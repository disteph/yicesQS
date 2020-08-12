open Containers
open Sexplib
open Type
open Yices2_high
open Yices2_ext_bindings
open Yices2_SMT2
open Command_options

let print i fs = Format.((if !verbosity >= i then fprintf else ifprintf) stdout) fs

module LazyList = struct

  type 'a t = 'a node Lazy.t
  and 'a node = [`Nil | `Cons of 'a * 'a t]

  let empty = lazy `Nil
  let return a = lazy (`Cons(a,empty))

  let rec length l = match Lazy.force l with
    | `Nil -> 0
    | `Cons(_,l) -> length l+1

  let rec fold : ('b Lazy.t -> 'a -> 'b) -> 'b Lazy.t -> 'a t -> 'b Lazy.t
    = fun f seed l -> lazy (match Lazy.force l with
      | `Nil -> Lazy.force seed
      | `Cons(head,tail) -> f (fold f seed tail) head)

  let map (type a b) (f : a -> b) (l : a t) =
    fold (fun nexts element -> `Cons(f element, nexts)) empty l

  let append (type a) (s1 : a t) (s2 : a t) : a t =
    fold (fun nexts element -> `Cons(element, nexts)) s2 s1

  let bind (type a b) (l : a t) (f : a -> b t) : b t =
    fold (fun nexts element -> Lazy.force (append (f element) nexts)) empty l

  let flatten (type a) (l : a t t) : a t = bind l (fun x -> x)
    
  let rec extract n l =
    if n <= 0 then []
    else
      match Lazy.force l with
      | `Nil -> []
      | `Cons(head,tail) -> head::(extract (n-1) tail)
  
end

module OptionMonad = struct
  include Option
  let bind = ( >>= )
end

open MTerm(OptionMonad)

let term_width y = Type.bvsize(Term.type_of_term y)

(*************************)
(* Free Variable testing *)
(*************************)
    
module HPairs = Hashtbl.Make(struct
    type t = Term.t * Term.t [@@deriving eq]
    let hash = Hash.pair Term.hash Term.hash
  end)

let free_table = HPairs.create 500

let fv x t =
  let rec aux t =
    match HPairs.find_opt free_table (x,t) with
    | Some b -> b
    | None ->
      let answer =
        if Term.equal t x then None
        else
          let Term a = Term.reveal t in
          match a with
          | A0 _ -> Some t
          | _    ->
            match map aux a with
            | Some _ -> Some t
            | None as a -> a
      in
      HPairs.add free_table (x,t) answer;
      answer
  in
  match aux t with
  | Some _ -> false
  | None -> true


(******************************************************)
(* Analysing bv-arrays as concats of extracts or bits *)
(******************************************************)

module BoolStruct = struct

  type 'a t =
    | Leaf of 'a
    | And of 'a t list
    | Or  of 'a t list
    | Not of 'a t
  [@@deriving eq, show]

  let rec compare compare_leaf t1 t2 = match t1, t2 with
    | Leaf t1, Leaf t2 -> compare_leaf t1 t2
    | And l1, And l2
    | Or l1, Or l2 -> List.compare (compare compare_leaf) l1 l2
    | Not t1, Not t2 -> compare compare_leaf t1 t2
    | Leaf _, _ -> -1
    | _, Leaf _ -> 1
    | Not _, _  -> -1
    | _, Not _  -> 1
    | Or _, _   -> -1
    | _, Or _   -> -1

  let rec map f = function
    | Leaf a -> Leaf (f a)
    | And l -> And(List.map (map f) l)
    | Or l  -> Or(List.map (map f) l)
    | Not a  -> Not(map f a)
end

module Slice : sig
  type t = private {
    extractee : Yices2_ext_bindings.Term.t;
    indices : (int * int) option;
  }
  val build   : ?indices:(int*int) -> Term.t -> t
  val pp      : t Format.printer
  val to_term : t -> Term.t
  val width   : t -> int
  val fv      : Term.t -> t -> bool
end = struct

  type t = { extractee : Term.t;
             indices   : (int * int) option }
  [@@deriving show]

  let build ?indices extractee =
    assert(Term.is_bitvector extractee);
    match indices with
    | Some(lo,hi) when not(Int.equal lo 0 && Int.equal hi (term_width extractee)) ->
      {extractee; indices}
    | _ -> { extractee; indices = None }

  let to_term {extractee; indices} =
    match indices with
    | None -> extractee
    | Some(lo,hi) -> 
    Term.BV.bvextract extractee lo (hi-1)

  let width { extractee; indices } = match indices with
    | None -> term_width extractee
    | Some(lo, hi) -> hi - lo

  let fv x {extractee} = fv x extractee
end

module SliceBlock = struct
  open BoolStruct

  type bit = (Term.t * int) BoolStruct.t [@@deriving show, ord]
  type t = Slice.t BoolStruct.t [@@deriving show]

  let rec to_term = function
    | Leaf slice -> Slice.to_term slice
    | And l  -> Term.BV.bvand (List.map to_term l)
    | Or l   -> Term.BV.bvor  (List.map to_term l)
    | Not a  -> Term.BV.bvnot (to_term a)

  let rec width = function
    | Leaf slice -> Slice.width slice
    | And(a::_)
    | Or (a::_)
    | Not a -> width a
    | _ -> assert false

  let rec fv x = function
    | Leaf slice -> Slice.fv x slice
    | And l | Or l -> List.exists (fv x) l
    | Not a -> fv x a

  let rec nnf polarity = function
    | Leaf _ as l -> if polarity then l else Not l
    | And l ->
      let l = List.map (nnf polarity) l in
      if polarity then And l else Or l
    | Or l ->
      let l = List.map (nnf polarity) l in
      if polarity then Or l else And l
    | Not a -> nnf (not polarity) a
  
end

(* Terms extended with primitive constructs for bvand bvor bvneg *)

module ExtTerm = struct

  type 'a bs   = BS
  type 'a base = Base

  type (_,_) ext =
    | T      : 'a           -> ([`term]     base,'a) ext
    | Bits   : Term.t list  -> ([`bits]  bs base, _) ext 
    | Slice  : SliceBlock.t -> ([`slice] bs base, _) ext 
    | Concat : block list   -> ([`concat],_) ext
  and 'a raw = ('a,Term.t) ext
  and t     = ExtTerm : _ raw -> t
  and block = Block   : _ bs base raw -> block

  let return a = ExtTerm(T a)

  let rec pp_ext : type a b. b Format.printer -> (a,b) ext Format.printer =
    fun pp_b fmt -> function
    | T a -> pp_b fmt a
    | Bits  block -> List.pp Term.pp fmt block
    | Slice block -> BoolStruct.pp Slice.pp fmt block
    | Concat l -> List.pp pp_block fmt l
  and pp_raw : type a. a raw Format.printer = fun fmt a -> pp_ext Term.pp fmt a
  and pp fmt (ExtTerm a) = pp_raw fmt a
  and pp_block fmt (Block a) = pp_raw fmt a

  let rec to_term : type a. a raw -> Term.t = function
    | T t -> t
    | Bits  block -> Term.BV.bvarray block
    | Slice block -> SliceBlock.to_term block
    | Concat l    -> Term.BV.bvconcat (List.rev_map (fun (Block b) -> to_term b) l)

  type 'a yraw = ('a,Types.yterm) ext
  and yt = YExtTerm : 'a yraw -> yt

  let build : type a b. (a, b Types.termstruct) ext -> a raw = function
    | T a         -> T(Term.build a)
    | Bits bits   -> Bits bits
    | Slice slice -> Slice slice
    | Concat l    -> Concat l

  let rec width : type a. (a,Term.t) ext -> int = function
    | T a      -> term_width a
    | Bits l   -> List.length l
    | Slice slice -> SliceBlock.width slice
    | Concat l -> List.fold_left (fun sofar (Block block) -> sofar + width block) 0 l

  let term_fv = fv
  let rec fv : type a. Term.t -> (a,Term.t) ext -> bool = fun x -> function
    | T a      -> term_fv x a
    | Bits a   -> List.exists (term_fv x) a
    | Slice slice -> SliceBlock.fv x slice
    | Concat l    -> List.exists (fun (Block b) -> fv x b) l

  let typeof : type a. (a,Term.t) ext -> Type.t = function
    | T a -> Term.type_of_term a
    | other -> width other |> Type.bv

end

let bvarray bits =
  let open Types in
  let open Option in
  print 6 "@[<2>bvarray scans the array@,@[<v>%a@]@]@,"
    (List.pp Term.pp) bits;
  (* Check if bit is t[i] *)
  let rec analyse bit =
    let open BoolStruct in
    match Term.reveal bit with
    | Term(Projection(`YICES_BIT_TERM, i, t)) -> return (Leaf(t, i))
    | Term(A1(`YICES_NOT_TERM, bit)) ->
      let+ t = analyse bit in
      Not t 
    | Term(Astar(`YICES_OR_TERM, l)) ->
      let rec aux accu = function
        | [] -> return accu
        | head::tail ->
          let* t = analyse head in
          aux (t::accu) tail
      in
      let+ t = aux [] l in
      Or(List.fast_sort SliceBlock.compare_bit t)
    | _ -> None
  in
  let open ExtTerm in
  let init_slice bit = function
    | Some bstruct ->
      let aux (extractee,i) = Slice.build extractee ~indices:(i, i+1) in
      Block(Slice(BoolStruct.map aux bstruct))
    | None -> Block(Bits [bit])
  in
  let close_slice = function
    | Block(Slice slice) -> Block(Slice(SliceBlock.nnf true slice))
    | Block(Bits l)      -> Block(Bits(List.rev l))
  in
  let rec test slice bit =
    print 6 "@[Testing %a against %a@]@," SliceBlock.pp slice SliceBlock.pp_bit bit;
    let open BoolStruct in
    match slice, bit with
    | Leaf Slice.{extractee; indices = Some(lo, hi) }, Leaf(t, i)
      when hi = i && Term.equal t extractee ->
      Option.return (Leaf(Slice.build extractee ~indices:(lo, hi+1)))
    | And l_slice, And l_bit ->
      let+ slice = aux [] (l_slice, l_bit) in
      And slice
    | Or l_slice, Or l_bit ->
      let+ slice = aux [] (l_slice, l_bit) in
      Or slice
    | Not slice, Not bit ->
      let+ slice = test slice bit in
      Not slice
    | _ ->
      print 6 "@[Not matching: %a and %a@]@," SliceBlock.pp slice SliceBlock.pp_bit bit;
      None
  and aux accu = function
    | [], [] -> Option.return (List.rev accu)
    | (head_slice::tail_slice), (head_bit::tail_bit) ->
      let* slice = test head_slice head_bit in
      aux (slice::accu) (tail_slice, tail_bit)
    | [], _::_ | _::_, [] -> None
  in
  let open ExtTerm in
  let rec aux ?slice accu bits = match slice, accu, bits with
    | Some slice, _, [] ->
      print 6 "@[Closing last slice@]@,";
      (close_slice slice)::accu (* we have finished, closing last slice *)
    | Some slice, _, bit::tail -> (* we had started and we have a new bit to look at *)
      print 6 "@[We had started and we have a new bit to look at: %a@]@,"
        Term.pp bit;
      let slice, accu = match slice, analyse bit with
        | Block(Slice s), (Some b as sbit) ->
          begin
            print 6 "@[Had a slice, now getting new bit %a@]@," SliceBlock.pp_bit b;
            match test s b with
            | Some s ->
              print 6 "@[In continuity@]@,";
              Block(Slice s), accu
            | None ->
              print 6 "@[Not in continuity@]@,";
              init_slice bit sbit, (close_slice slice)::accu
          end
        | Block(Bits l), None ->
          print 6 "@[analyse bit says None@]@,";
          Block(Bits(bit::l)), accu
        | _, sbit ->
          print 6 "@[other@]@,";
          init_slice bit sbit, (close_slice slice)::accu
      in
      aux ~slice accu tail
    | None, [], bit::tail -> (* initialisation *)
      let slice = analyse bit |> init_slice bit in
      aux ~slice [] tail
    | None, _, []   (* No current slice but no bit to treat *)
    | None, _::_, _ (* No current slice but we have already accumulated slices *)
      -> assert false
  in
  let r = aux [] bits |> List.rev in
  print 6 "@[<2>and produces@,@[<v>%a@]@]@,"
    ExtTerm.pp_raw ExtTerm.(Concat r);
  r



(****************************************************************)
(* Conditional inverses as in the Niemetz et al. CAV'2018 paper *)
(****************************************************************)


(*********************)
(* Inverse functions *)
(*********************)



(* Solves (P[x] = t) in x, for bv-polynomial P expressed as list l,
   inspired by Table 4 of CAV'2018.
   It produces a list of pairs (e_i, t_i) such that
   * x is free in e_i
   * e_i is either a monomial variable of P, or a monomial (cst*e_i') of P with cst not 1 or -1)
   * (e_i = t_i) is equivalent to (P[x] = t) *)

let getInversePoly (x : Term.t) (t : Term.t) (l : (bool list * Term.t option) list) =

  let rebuild treated to_treat =
    let l = List.rev_append treated to_treat in
    match l with
    | [] -> t
    | _ -> Term.BV.(bvsub t (Term.build(Types.BV_Sum l)))
  in

  (* First, we collect the coefficient of x in P (1 or -1),
     together with the rest of the polynomial when we have removed x's monomial.
     We fold the following function over the polynomial expressed as l. *)

  let rec aux treated = function
    | [] -> []
    | (bl,Some e_i) as monomial::to_treat when fv x e_i ->
      let next = aux (monomial::treated) to_treat in
      let t'   = rebuild treated to_treat in
      let open ExtTerm in
      begin match bl with
        | true::tail when List.for_all (fun b -> b) tail ->  (* coeff is -1 *)
          (ExtTerm(T e_i), Term.BV.bvneg t') :: next
        | true::tail when List.for_all (fun b -> not b) tail -> (* coeff is 1 *)
          (ExtTerm(T e_i), t') :: next
        | _ ->
          let coeff = Term.BV.bvconst_from_list bl in
          let monom_term = Term.BV.bvproduct [coeff; e_i] in 
          (ExtTerm(T monom_term), t')::next
      end
    | monomial ::to_treat -> aux (monomial::treated) to_treat

  in
  aux [] l

(* Solves concat(...,e_i,...) = t) in x
   It produces a list of pairs (e_i, t_i) such that
   * x is free in e_i
   * e_i is not a BV_ARRAY, and in particular not an extract
   * (e_i = t_i) is implied by concat(...,e_i,...) = t *)

let getInverseConcat (x : Term.t) (t : Term.t) (concat : ExtTerm.block list) =
  let open ExtTerm in
  let rec aux start_index = function
    | [] -> [] (* x did not appear in a nice place *)

    | Block(Bits l):: tail ->
      aux (start_index + List.length l) tail

    | Block(Slice bstruct) :: tail ->
      let width = SliceBlock.width bstruct in
      let next = aux (start_index + width) tail in
      if SliceBlock.fv x bstruct
      then
        let t' = Term.BV.bvextract t start_index (start_index + width - 1) in
        (ExtTerm(Slice bstruct), t') :: next
      else
        next
  in
  aux 0 concat


(****************************)
(* Invertibility conditions *)
(****************************)

type pred = [ `YICES_BV_GE_ATOM
            | `YICES_BV_SGE_ATOM
            | `YICES_EQ_TERM ]

exception NotImplemented

let mins ~width = true :: List.init (width - 1) (fun _ -> false)
                  |> List.rev
                  |> Term.BV.bvconst_from_list
let maxs ~width = false :: List.init (width - 1) (fun _ -> true)
                  |> List.rev
                  |> Term.BV.bvconst_from_list

(* Tables 2, 3, 5, 6, 7, 8 *)

let getIC : type a. Term.t
  -> pred -> uneval: a ExtTerm.raw -> eval:Term.t -> uneval_left:bool -> polarity:bool -> Term.t
  = fun
    (var : Term.t)
    (cons : pred)
    ~uneval
    ~eval
    ~uneval_left
    ~polarity ->
  let open Types in
  let open Term in
  let open BV in
  if not(Term.is_bitvector eval) then raise NotImplemented;
  let width    = ExtTerm.width uneval in
  let zero     = bvconst_zero ~width in
  let zero_not = bvnot zero in
  let filter (coeff, monom) =
    match monom with
    | Some monom when equal monom var ->
      let coeff = bvconst_from_list coeff in
      Term.equal coeff (bvconst_one ~width)
      || Term.equal coeff (bvconst_int ~width (-1)) 
    | _ -> true
  in
  let conjuncts_disjuncts l =
    let open BoolStruct in
    let open Slice in
    let aux sofar = function
      | Leaf{extractee; indices = None} when Term.equal extractee var -> sofar
      | a -> (SliceBlock.to_term a)::sofar
    in
    List.fold_left aux [] l
  in
  (* let concat_collect l =
   *   let open BoolStruct in
   *   let open Slice in
   *   let open ExtTerm in
   *   let to_term = function
   *     | [] -> None
   *     | l  -> Some(to_term(Concat l))
   *   in
   *   let rec aux sofar = function
   *     | Block(Slice(Leaf{extractee; indices = None}))::tail when Term.equal extractee var ->
   *       to_term(List.rev sofar), to_term tail
   *     | head::tail -> aux (head::sofar) tail
   *     | [] -> assert false
   *   in
   *   aux [] l
   * in *)
  print 6 "@[<2>getIC on %s%a with uneval = %a (%s) and eval = %a (%s)@]@,"
    (if polarity then "" else "the negation of ")
    Types.pp_term_constructor (match cons with
        | `YICES_BV_GE_ATOM  -> `YICES_BV_GE_ATOM
        | `YICES_BV_SGE_ATOM -> `YICES_BV_SGE_ATOM
        | `YICES_EQ_TERM -> `YICES_EQ_TERM)
    ExtTerm.pp_raw uneval
    (if uneval_left then "left" else "right")
    Term.pp eval
    (if uneval_left then "right" else "left");

  let t = eval in
  match cons with

  | `YICES_EQ_TERM -> (* Table 2 *)
    begin
      match uneval with
      | ExtTerm.T e ->
        let Term l = reveal e in 
        begin
          match l with
          | _ when equal var e ->  (* Not actually given in the paper, just obvious *)
            assert(not polarity);
            Term.true0()

          | BV_Sum [coeff, Some monom] when equal var monom ->
            let s = bvconst_from_list coeff in
            if polarity
            then (bvand [bvor [bvneg s; s]; t]) === t
            else (s =/= zero) ||| (t =/= zero)

          | Product(true, prod) ->
            let aux sofar ((p,exp) as a) =
              if equal p var then
                if Unsigned.UInt.to_int exp = 1 then sofar else raise NotImplemented
              else
                a::sofar
            in
            let s = build (Product (true, List.fold_left aux [] prod)) in
            if polarity
            then (bvand [bvor [bvneg s; s]; t]) === t
            else (s =/= zero) ||| (t =/= zero)

          | A2(`YICES_BV_REM, x, s) when equal var x ->
            if polarity
            then bvsge (bvnot (bvneg s)) t
            else (s =/= bvconst_one ~width) ||| (t =/= zero)

          | A2(`YICES_BV_REM, s, x) when equal var x ->
            if polarity
            then bvsge (bvsum [t; t; bvneg s]) t
            else (s =/= zero) ||| (t =/= zero)

          | A2(`YICES_BV_DIV, x, s) when equal var x ->
            if polarity
            then (bvdiv (bvmul s t) s) === t
            else (s =/= zero) ||| (t =/= zero_not)

          | A2(`YICES_BV_DIV, s, x) when equal var x ->
            if polarity
            then (bvdiv s (bvmul s t)) === t
            else
            if width = 1 then bvand [s; t] === zero
            else true0()

          | A2(`YICES_BV_LSHR, x, s) when equal var x ->
            if polarity
            then (bvlshr (bvshl t s) s === t)
            else
              let w = bvconst_int ~width width in
              t =/= zero ||| (bvlt s w)

          | A2(`YICES_BV_LSHR, s, x) when equal var x ->
            if polarity
            then
              let rec aux i accu =
                if i = -1 then accu
                else
                  let atom = (bvlshr s (bvconst_int ~width i) === t) in
                  aux (i-1) (atom :: accu)
              in
              orN (aux width [])
            else
              (s =/= zero) ||| (t =/= zero)

          | A2(`YICES_BV_ASHR, x, s) when equal var x ->
            if polarity
            then
              let w = bvconst_int ~width width in
              ((bvlt s w) ==> (bvashr (bvshl t s) s === t))
              &&&
              ((bvge s w) ==> (( t === zero_not) ||| (t === zero)))
            else true0()

          | A2(`YICES_BV_ASHR, s, x) when equal var x ->
            if polarity
            then
              let rec aux i accu =
                if i = -1 then accu
                else
                  let atom = (bvashr s (bvconst_int ~width i) === t) in
                  aux (i-1) (atom :: accu)
              in
              orN (aux width [])
            else
              ((t =/= zero)     ||| (s =/= zero))
              &&&
              ((t =/= zero_not) ||| (s =/= zero_not))

          | A2(`YICES_BV_SHL, x, s) when equal var x ->
            if polarity
            then (bvshl (bvlshr t s) s) === t
            else (t =/= zero) ||| (bvlt s (bvconst_int ~width width))

          | A2(`YICES_BV_SHL, s, x) when Term.equal var x ->
            if polarity
            then
              let rec aux i accu =
                if i = -1 then accu
                else
                  let atom = (bvshl s (bvconst_int ~width i) === t) in
                  aux (i-1) (atom :: accu)
              in
              orN (aux width [])
            else
              (s =/= zero) ||| (t =/= zero)

          | A2(`YICES_BV_SMOD, _, _)
          | A2(`YICES_BV_SDIV, _, _)
          | A2(`YICES_BV_SREM, _, _)
          | Astar(`YICES_OR_TERM, _) (* Rare: only if bvor not detected *)
            -> raise NotImplemented

          | A2(`YICES_BV_GE_ATOM, _, _)
          | A2(`YICES_EQ_TERM, _, _)
          | A2(`YICES_BV_SGE_ATOM, _, _)
            -> assert false
          | _ -> raise NotImplemented
        end

      | ExtTerm.Slice(Leaf{ extractee; indices }) -> (* Not in tables, but obvious *)
        true0()

      | ExtTerm.Slice(And l) ->
        let s = conjuncts_disjuncts l in
        if polarity
        then (bvand (t::s)) === t
        else
          (bvand s =/= zero) ||| (t =/= zero)

      | ExtTerm.Slice(Or l) ->
        let s = conjuncts_disjuncts l in
        if polarity
        then (bvor (t::s)) === t
        else
          (bvor s =/= zero_not) ||| (t =/= zero_not)

      | ExtTerm.Slice(Not l) -> assert false (* Should not have led to epsilon-terms *)

      | ExtTerm.Concat l ->
        if polarity
        then assert false (* Should not have led to epsilon-terms *)
        else true0()

      | ExtTerm.Bits _ -> assert false (* We should have abandoned ship by now *)

    end
    
  | `YICES_BV_GE_ATOM ->
    begin
      let cond() = (* Table 5 *)
        if polarity
        then Term.true0()   (* Column 6 *)
        else if uneval_left
        then t =/= zero     (* Column 2 *)
        else t =/= zero_not (* Column 3 *)
      in
      match uneval with
      | ExtTerm.T e ->
        let Term l = reveal e in 
        begin
          match l with

          (* Table 5 cases *)
          | _ when equal var e                  -> cond()
          | BV_Sum l when List.for_all filter l -> cond()

          (* Tables 3 and 6 *)
          | BV_Sum [coeff, Some monom] when equal var monom ->
            let s = bvconst_from_list coeff in
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge (bvor [bvneg s; s]) t
              else true0()
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero
            else bvlt t (bvor [bvneg s; s])

          | Product(true, prod) ->
            let aux sofar ((p,exp) as a) =
              if equal p var then
                if Unsigned.UInt.to_int exp = 1 then sofar else raise NotImplemented
              else
                a::sofar
            in
            let s = build (Product (true, List.fold_left aux [] prod)) in
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge (bvor [bvneg s; s]) t
              else true0()
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero
            else bvlt t (bvor [bvneg s; s])

          | A2(`YICES_BV_REM, x, s) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge (bvnot (bvneg s)) t
              else true0()
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero
            else bvlt t (bvnot (bvneg s))

          | A2(`YICES_BV_REM, s, x) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge (bvand [bvsum [t; t; bvneg s] ; s]) t ||| (bvlt t s)
              else true0()
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero
            else bvlt t s

          | A2(`YICES_BV_DIV, x, s) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvand [ bvdiv (bvmul s t) t ; s] === s
              else true0()
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then (bvlt zero s) &&& (bvlt zero t)
            else bvgt (bvdiv zero_not s) t

          | A2(`YICES_BV_DIV, s, x) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then true0()
              else bvlt zero (bvor [ bvneg s ; t])
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then (bvlt zero (bvnot(bvand [bvneg t ; s]))) &&& (bvlt zero t)
            else bvlt t zero_not

          (* | No easy representation of x & s = t in yices *)

          | Astar(`YICES_OR_TERM, l) ->
            let aux sofar a =
              if equal a var then sofar
              else a::sofar
            in
            let s = List.fold_left aux [] l in
            let s = build (Astar(`YICES_OR_TERM, s)) in
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then true0()
              else bvge t s
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then bvlt s t
            else bvlt t zero_not

          | A2(`YICES_BV_LSHR, x, s) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then (bvlshr (bvshl t s) s === t)
              else true0()
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero
            else bvlt t (bvlshr (bvnot s) s)

          | A2(`YICES_BV_LSHR, s, x) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge s t
              else true0()
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero
            else bvlt t s

          | A2(`YICES_BV_ASHR, x, s) when equal var x ->
            if polarity
            then (* Table 6 *)
              true0()
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero
            else bvlt t zero_not

          | A2(`YICES_BV_ASHR, s, x) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge s (bvnot s) ||| bvge s t
              else bvlt s (mins ~width) ||| bvge t s
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then (bvlt s t ||| bvsge s zero) &&& (t =/= zero)
            else (bvslt s (bvlshr s (bvnot t))) ||| (bvlt t s)

          | A2(`YICES_BV_SHL, x, s) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge (bvshl zero_not s) t
              else true0()
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero
            else bvlt t (bvshl zero_not s)

          | A2(`YICES_BV_SHL, s, x) when Term.equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then
                let rec aux i accu =
                  if i = -1 then accu
                  else
                    let atom = bvge (bvshl s (bvconst_int ~width i)) t in
                    aux (i-1) (atom :: accu)
                in
                orN (aux width [])
              else true0()
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero
            else
              let rec aux i accu =
                if i = -1 then accu
                else
                  let atom = bvgt (bvshl s (bvconst_int ~width i)) t in
                  aux (i-1) (atom :: accu)
              in
              orN (aux width [])

          | A2(`YICES_BV_SMOD, x, s)
          | A2(`YICES_BV_SDIV, x, s)
          | A2(`YICES_BV_SREM, x, s)
            -> raise NotImplemented

          | A2(`YICES_BV_GE_ATOM, _, _)
          | A2(`YICES_EQ_TERM, _, _)
          | A2(`YICES_BV_SGE_ATOM, _, _)
            -> assert false
          | _ -> raise NotImplemented (* assert false *)

        end

      | ExtTerm.Slice(Not _)     (* Table 5 *)
      | ExtTerm.Slice(Leaf _) -> (* Should be added to Table 5 *)
        cond()

      | ExtTerm.Slice(And l) ->
        if polarity
        then (* Table 6 *)
          if uneval_left (* uneval >= eval *)
          then
            let s = conjuncts_disjuncts l |> bvand in
            bvge s t
          else true0()
        else (* Table 3 *)
        if uneval_left (* uneval < eval *)
        then t =/= zero
        else
          let s = conjuncts_disjuncts l |> bvand in
          bvlt t s

      | ExtTerm.Slice(Or l) ->
        if polarity
        then (* Table 6 *)
          if uneval_left (* uneval >= eval *)
          then
            true0()
          else 
            let s = conjuncts_disjuncts l |> bvor in
            bvge t s
        else (* Table 3 *)
        if uneval_left (* uneval < eval *)
        then
          let s = conjuncts_disjuncts l |> bvor in
          bvlt s t
        else
          t =/= zero_not

      | ExtTerm.Concat l -> raise NotImplemented;
        
      | ExtTerm.Bits _ -> assert false (* We should have abandoned ship by now *)
    end

  | `YICES_BV_SGE_ATOM ->
    let cond() = (* Table 5 *)
      if polarity
      then Term.true0() (* Column 6 *)
      else if uneval_left
      then t =/= mins width (* Column 4 *)
      else t =/= maxs width (* Column 5 *)
    in
    match uneval with
    | ExtTerm.T e ->
      let Term l = reveal e in 
      begin
        match l with

        (* Table 5 cases *)
        | _ when equal var e -> cond()
        | BV_Sum l when List.for_all filter l ->  cond()

        (* Tables 7 and 8 *)
        | _ -> raise NotImplemented
      end
    | ExtTerm.Slice(Not _)     (* Table 5 *)
    | ExtTerm.Slice(Leaf _) -> (* Should be added to Table 5 *)
      cond()
    | ExtTerm.Slice _  -> raise NotImplemented
    | ExtTerm.Concat _ -> raise NotImplemented
    | ExtTerm.Bits _ -> assert false (* We should have abandoned ship by now *)


(**************************)
(* Building substitutions *)
(**************************)

module Monad = struct

  (* This monad is meant to create variants of a term-carrying type 
     where at most 1 term has been substituted by a fresh variable. *)

  (* A variant is generated by 1 modification *)
  type modif = { variable : Term.t; standing4 : ExtTerm.t }
  type 'a variant = 'a * modif

  (* The monad type is a (lazy) list of variants *)
  type 'a t = {
    original : 'a;
    variants : 'a variant LazyList.t
  }

  (* Return: no variant *)
  let return a = {
    original = a;
    variants = LazyList.empty
  }

  (* Bind: lazily compute the variants of the argument arg,
     apply the function to the original argument,
     authorising it to introduce variants,
     as well as to all of the arguments' variants,
     not authorising the function to perform and more modifications *)

  let bind (type a b) (arg: a t) (f : a -> b t) : b t =
    let f_original = f arg.original in
    let aux (nexts : b variant LazyList.t) ((a, modif) : a variant) : b variant LazyList.node =
      `Cons(((f a).original, modif), nexts)
    in
    { original = f_original.original;
      variants = LazyList.fold aux f_original.variants arg.variants }

  let (let*) = bind
  let (let+) a f = bind a (fun r -> return(f r))
end

module Variants = struct
  open MTerm(Monad)
  open ExtTerm
  open Monad

  let term_map = map

  let rec mapList : type a b. (a -> b Monad.t) -> a list -> b list Monad.t =
    fun f -> function
    | [] -> return []
    | head::tail ->
      let* h = f head in
      let+ t = mapList f tail in
      h::t

  open BoolStruct 

  let slice_map
      (fterm : Term.t -> Term.t Monad.t)
      (fother : SliceBlock.t -> SliceBlock.t Monad.t)
      slice =
    match slice with
    | Leaf Slice.{ extractee; indices } -> 
      let+ extractee = fterm extractee in
      Leaf(Slice.build extractee ?indices)
    | And l -> let+ l = mapList fother l in And l
    | Or l  -> let+ l = mapList fother l in Or l
    | Not a -> let+ a = fother a in Not a

  type _ modified =
    | SameType  : 'a     -> 'a modified
    | FreshTerm : Term.t -> _ bs base raw modified

  type update = { apply : 'a. 'a base raw -> 'a base raw modified Monad.t }

  let map : type a b. update -> (b,a Types.termstruct) ExtTerm.ext -> (b,a Types.termstruct) ExtTerm.ext Monad.t = fun f -> function

    | T a      ->
      let aux (t : Term.t) = let+ SameType(T t) = f.apply(T t) in t in
      let+ a = term_map aux a in
      T a

    | Slice slice    ->
      let fterm t  = let+ SameType(T r) = f.apply(T t) in r in
      let fother t =
        let+ r = f.apply(Slice t) in
        match r with
        | SameType(Slice slice) -> slice
        | FreshTerm extractee   -> Leaf(Slice.build extractee)
      in
      let+ slice  = slice_map fterm fother slice in
      Slice slice

    | Bits _ as bits -> return bits (* We compute no variants there *)

    | Concat l       ->
      let aux (Block block) =
        let+ r = f.apply block in
        match r with
        | SameType r          -> Block r
        | FreshTerm extractee -> Block(Slice(Leaf(Slice.build extractee)))
      in
      let+ blocks = mapList aux l in Concat blocks
end

type subst = {
  body : Term.t;
  epsilons : Term.t list
}

let pp_subst x fmt { body; epsilons } =
  Format.fprintf fmt "{%a <- %a} with %a" Term.pp x Term.pp body (List.pp Term.pp) epsilons

module Substs = struct

  type not_great =
    | Epsilon of subst
    | NonLinear of Term.t list
  
  type substs =
    | Eliminate of Term.t  (* substitution eliminates variable AND
                              faithfully represents literal from whence it came *)
    | NotGreat of not_great

  let pp_substs x fmt = function
    | Eliminate s ->
      Format.fprintf fmt "Elim %a" Term.pp s
    | NotGreat(Epsilon subst) ->
      Format.fprintf fmt "Epsilon %a" (pp_subst x) subst
    | NotGreat(NonLinear []) ->
      Format.fprintf fmt "Nothing"
    | NotGreat(NonLinear l) ->
      Format.fprintf fmt "NonLinear %a" (List.pp Term.pp) l

  type t = not_great -> substs

  let (||>) (a : t) f solutions =
    match a solutions with
    | Eliminate _  as result -> result
    | NotGreat not_great -> f not_great
  
  let ident not_great   = NotGreat not_great
  let nil = function
    | NonLinear _ as l -> NotGreat l
    | Epsilon _        -> NotGreat(NonLinear [])

end
open Substs

(* Fig 1 *)

let make_lit (cons : pred) ~uneval ~eval ~uneval_left ~polarity =
  let lhs, rhs = if uneval_left then uneval, eval else eval, uneval in
  let atom = Term.build Types.(A2(cons,lhs,rhs)) in
  if polarity then atom else Term.not1 atom

let rec solve
    (x : Term.t)
    (cons : pred)
    ~uneval
    ~eval
    ~uneval_left
    ~polarity
    (epsilons : Term.t list)
  (* The specs of the epsilon terms we have created in the recursive solve descent *)
  : Substs.not_great -> Substs.substs
  =
  print 6 "@[<2>solve with var = %a, uneval = %a and eval = %a@]@,"
    Term.pp x
    ExtTerm.pp uneval
    Term.pp eval;
  let open ExtTerm in
  let solve a = solve_aux x cons a eval ~uneval_left ~polarity epsilons in
  match uneval with
  | ExtTerm(Bits _ as bits)   -> solve bits
  | ExtTerm(Slice _ as slice) -> solve slice
  | ExtTerm(Concat _ as l)    -> solve l
  | ExtTerm(T e as uneval) when Term.equal e x ->
    begin (* Particular case when the 1st argument is x itself - end of recursion *)
      try
        print 6 "@[<2>uneval is the variable@]@,";
        let subst = 
          match cons with
          | `YICES_EQ_TERM when polarity -> { body = eval; epsilons }
          | _ ->
            let phi = getIC x cons ~uneval ~eval ~uneval_left ~polarity in
            let typ = Term.type_of_term x in
            let y   = Term.new_uninterpreted typ in
            let b   = make_lit cons ~uneval:y ~eval ~uneval_left ~polarity in
            { body = y; epsilons = Term.(phi ==> b)::epsilons }
        in
        let open Substs in
        match subst.epsilons, not(term_fv x eval) with
        | [], true  -> (fun _ -> Substs.Eliminate subst.body) (* No epsilon, no occurrence! *)
        | [], false -> (function
            | Epsilon _   -> Substs.NotGreat(NonLinear [subst.body]) 
            | NonLinear l -> Substs.NotGreat(NonLinear (subst.body::l)))
        | _::_, true -> (function (* Epsilon, no occurrence... maybe? *)
            | NonLinear [] -> Substs.NotGreat(Epsilon subst) (* OK if no other solution *)
            | solutions    -> Substs.nil solutions) (* Not OK otherwise *)
        | _::_, false      -> Substs.nil (* Epsilon with occurrence -> trash *)
      with NotImplemented  -> Substs.nil
    end
  | ExtTerm(T e) -> (* General case *)
    match Term.reveal e with
    | Term(Astar(`YICES_BV_ARRAY, bits)) -> (* In case of a BV_ARRAY, we preprocess *)
      begin match bvarray bits with
        | [Block(Bits _ as bits)]   -> solve bits
        | [Block(Slice _ as slice)] -> solve slice
        | l                         -> solve(Concat l)
      end
    | Term a -> solve(T a) (* Otherwise we let solve_aux analyse the term structure *)

and solve_aux : type a b. Term.t -> pred -> (b,a Types.termstruct) ExtTerm.ext -> Term.t ->
  uneval_left:bool -> polarity:bool -> Term.t list -> Substs.not_great -> Substs.substs
  = fun (x : Term.t)
    (cons : pred)
    a
    (t : Term.t)
    ~uneval_left
    ~polarity
    (epsilons : Term.t list) ->
    print 6 "@[<2>uneval is not the variable@]@,";
    (* The recursive call is parameterised by e_i and t *)
    let treat e_i t' = solve x cons ~uneval:e_i ~eval:t' ~uneval_left ~polarity epsilons in
    (* treat_nl manages the recursive calls on the non-linear problems we have *)
    let rec treat_nl = function
      | []             -> Substs.ident
      | (e_i,t')::tail -> treat e_i t' ||> treat_nl tail
    in
    let rec recurs_call accu = function
      | []              -> treat_nl accu
      | (e_i, t')::tail ->
        if fv x t'
        then recurs_call ((e_i, t')::accu) tail (* Non-linear case goes in accumulator *)
        else treat e_i t' ||> recurs_call accu tail
        (* Linear case treated immediately doesn't go further if it comes back with Eliminate *)
    in
    let test_poly = function
      | _::_::_ | [_, None] | [] -> true
      | [coeff, Some var] ->
        match coeff with
          | true::tail when List.for_all (fun b -> b) tail -> true  (* coeff is -1 *)
          | true::tail when List.for_all (fun b -> not b) tail -> true (* coeff is 1 *)
          | _ -> false
    in
    let open Types in
    let open ExtTerm in
    match cons, a with (* We analyse the top-level predicate and its 1st argument e *)

    | _, Slice(Leaf{ extractee; indices = None }) ->
      [ExtTerm(T extractee), t] |> recurs_call []

    | `YICES_EQ_TERM, Slice(Not a) ->
      [ExtTerm(Slice a), Term.BV.bvnot t] |> recurs_call []

    | `YICES_EQ_TERM, Concat blocks when polarity ->
       getInverseConcat x t blocks |> recurs_call []

    | `YICES_EQ_TERM, T(BV_Sum l) when test_poly l ->
      getInversePoly x t l |> recurs_call []

    | _ ->
      let open ExtTerm in
      let apply : type a. a base raw -> a base raw Variants.modified Monad.t = fun e_i ->
        print 6 "@[<2>apply on e_i = %a@]@," ExtTerm.pp_raw e_i;
        let variants = lazy(
          if ExtTerm.fv x e_i
          then
            begin
              print 6 "@[<2>Detecting possible modif@]@,";
              let typ     = ExtTerm.typeof e_i in
              let x'      = Term.new_uninterpreted typ in
              let open Variants in
              let modified : a base raw modified =
                match e_i with
                | T _     -> SameType(T x')
                | Slice _ -> FreshTerm x'
                | Bits _  -> FreshTerm x'
              in
              let variant = modified,
                            Monad.{ variable = x' ; standing4 = ExtTerm e_i }
              in
              `Cons(variant, LazyList.empty)
            end
          else `Nil)
        in
      Monad.{ original = SameType e_i; variants }
    in
    let variants = Variants.map { apply } a in
    let treat dx'_raw Monad.{ variable = x' ; standing4 = e_i } = try
        print 6 "@[<2>treat on var %a standing for head %a@]@," Term.pp x' ExtTerm.pp e_i;
        let dx' = ExtTerm.build dx'_raw in
        print 6 "@[<2>with dx' being %a@]@," ExtTerm.pp (ExtTerm dx');
        let phi = getIC x' cons ~uneval:dx' ~eval:t ~uneval_left ~polarity in
        print 6 "@[<2>getIC gave us %a@]@," Term.pp phi;
        let typ = Term.type_of_term x' in
        let y   = Term.new_uninterpreted typ in
        let dy  = Term.subst_term [x',y] (ExtTerm.to_term dx') in
        let b   = make_lit cons ~uneval:dy ~eval:t ~uneval_left ~polarity in
        solve x `YICES_EQ_TERM ~uneval:e_i ~eval:y ~uneval_left:true ~polarity:true
          (Term.(phi ==> b)::epsilons)
      with NotImplemented ->
        print 6 "Not implemented@,";
         Substs.nil
    in
    let aux nexts (dx'_raw, modif) = treat dx'_raw modif in
    let variants = LazyList.fold aux (lazy Substs.ident) variants.variants in
    Lazy.force variants


let solve_atom
    (x : Term.t)
    (atom : [`a2] Types.composite Types.termstruct)
    (polarity : bool)
    epsilons  (* The specs of the epsilon terms we have created in the recursive solve descent *)
  =
  let open ExtTerm in
  let Types.A2(cons,e,t) = atom in
  print 6 "@[<2>solve_atom %a with lhs = %a and rhs = %a@]@,"
    Term.pp x
    Term.pp e
    Term.pp t;
  match cons with
  | `YICES_EQ_TERM | `YICES_BV_GE_ATOM | `YICES_BV_SGE_ATOM as cons ->
    if term_fv x t
    then if term_fv x e
      then match cons with
        | `YICES_EQ_TERM when Term.is_bitvector t || Term.is_arithmetic t ->
          print 6 "@[<2>Present on both sides, and is bv or arith@]@,";
          let uneval, eval =
            if Term.is_bitvector t
            then Term.BV.bvsub t e, Term.BV.bvconst_zero ~width:(term_width t)
            else Term.Arith.sub t e, Term.Arith.zero()
          in
          solve x `YICES_EQ_TERM ~uneval:(return uneval) ~eval ~uneval_left:true ~polarity epsilons
        | _ ->
          print 6 "@[<2>Present on both sides, and is not bv or arith@]@,";
          solve x cons ~uneval:(return e) ~eval:t ~uneval_left:true ~polarity epsilons
          ||> solve x cons ~uneval:(return t) ~eval:e ~uneval_left:false ~polarity epsilons
      else
        (print 6 "@[<2>Present on rhs only@]@,";
         solve x cons ~uneval:(return t) ~eval:e ~uneval_left:false ~polarity epsilons)
    else
      (print 6 "@[<2>Present on lhs only@]@,";
       solve x cons ~uneval:(return e) ~eval:t ~uneval_left:true ~polarity epsilons)
  | _ -> assert false


let solve_lit x lit substs =
  let open Term in
  let open Types in
  let aux b t =
    if Term.equal x t then
      let body = if b then Term.true0() else Term.false0() in
      Substs.Eliminate body
    else
      match reveal t with
      | Term(A2 _ as atom) when fv x t ->
        print 5 "@[<v2>solve_lit looks at@,%a@," Term.pp lit;
        let r = solve_atom x atom b [] substs in
        print 5 "@[<2>which turns into %a@]@]@," (Substs.pp_substs x) r;
        r
      | _ -> Substs.nil substs
  in
  match reveal lit with
  | Term(A1(`YICES_NOT_TERM, t')) -> aux false t'
  | _ -> aux true lit

let solve_list conjuncts old_epsilons x : Term.t list * Term.t list =
  print 5 "@[<hv2>solve_list solves %a from@,%a@,@[<v>"
    Term.pp x
    (List.pp Term.pp) conjuncts;
  let rec aux treated accu = function
    | [] ->
      begin match accu with
        | Epsilon {body; epsilons} ->
          print 5 "@[<2>solve_list substitutes %a by %a@]@," Term.pp x Term.pp body;
          (* let aux conjunct =
           *   let new_conjunct = Term.subst_term [x,body] conjunct in
           *   if not (Term.equal conjunct new_conjunct)
           *   then
           *     print 5 "@[<2>Turning conjunct %a into %a@]@," Term.pp conjunct Term.pp new_conjunct
           * in
           * List.iter aux conjuncts; *)
          Term.subst_terms [x,body] conjuncts,
          epsilons @ Term.subst_terms [x,body] old_epsilons
        | _ ->
          (* print 5 "@[<2>solve_list does not substitute@]@,"; *)
          conjuncts, old_epsilons
      end
      
    | lit::tail ->
      match solve_lit x lit accu with

      | Eliminate body ->
        print 5 "@[<2>solve_list substitutes %a by %a@]@," Term.pp x Term.pp body;
        (* let aux conjunct =
         *   let new_conjunct = Term.subst_term [x,body] conjunct in
         *   if not (Term.equal conjunct new_conjunct)
         *   then
         *     print 5 "@[<2>Turning conjunct %a into %a@]@," Term.pp conjunct Term.pp new_conjunct
         * in
         * List.iter aux conjuncts; *)
        Term.subst_terms [x,body] conjuncts, Term.subst_terms [x,body] old_epsilons

      | NotGreat(Epsilon _ )
        when List.exists (fv x) treated
          || List.exists (fv x) tail
          || List.exists (fv x) old_epsilons  ->
        aux (lit::treated) accu tail

      | NotGreat subst ->
        aux (lit::treated) subst tail
  in
  let result = aux [] (NonLinear []) conjuncts in
  print 5 "@]@]@,";
  result


let solve_all vars t =
  let open Term in
  let open Types in
  let rec aux t = match reveal t with
    | Term(Astar(`YICES_OR_TERM,l)) ->
      l |> List.map aux |> List.flatten
    | _ -> [t]
  in
  let conjuncts =
    match reveal t with
    | Term(A1(`YICES_NOT_TERM, t)) ->
      aux t |> List.map Term.not1 |> List.sort_uniq ~cmp:Term.compare
    | _ -> [t]
  in
  print 3 "@[<2>IC analyses %a@]@," Term.pp t;
  let rec aux conjuncts epsilons = function
    | [] -> conjuncts, epsilons
    | x::vars ->
      let conjuncts, epsilons = solve_list conjuncts epsilons x in
      aux conjuncts epsilons vars
  in
  let conjuncts, epsilons = aux conjuncts [] vars in
  print 3 "@[<2>IC finished@]@,";
  Term.andN conjuncts, epsilons
