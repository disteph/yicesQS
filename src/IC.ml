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
    | `Cons(_,l) -> length l

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

let width y = Type.bvsize(Term.type_of_term y)

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

  let rec map f = function
    | Leaf a -> Leaf (f a)
    | And l -> And(List.map (map f) l)
    | Or l  -> Or(List.map (map f) l)
    | Not a  -> Not(map f a)
end

module Slice = struct

  type t = { extractee : Term.t;
             lo        : int;
             hi        : int }
  [@@deriving show]

  let to_term {extractee; lo; hi} =
    Term.BV.bvextract extractee lo (hi-1)

  let width {lo; hi} = hi - lo

  let fv x {extractee} = fv x extractee
end

module Block = struct
  open BoolStruct
  open Slice

  type slice = Slice.t BoolStruct.t [@@deriving show]

  let rec slice_to_term = function
    | Leaf slice -> Slice.to_term slice
    | And l  -> Term.BV.bvand (List.map slice_to_term l)
    | Or l   -> Term.BV.bvor  (List.map slice_to_term l)
    | Not a  -> Term.BV.bvnot (slice_to_term a)

  let rec slice_width = function
    | Leaf slice -> Slice.width slice
    | And(a::_)
    | Or (a::_)
    | Not a -> slice_width a
    | _ -> assert false

  let rec slice_fv x = function
    | Leaf slice -> Slice.fv x slice
    | And l | Or l -> List.exists (slice_fv x) l
    | Not a -> slice_fv x a

  type t =
    | Bits of Term.t list
    | Slice of slice
  [@@deriving show]

  let to_term = function
    | Bits bits -> Term.BV.bvarray bits
    | Slice slice -> slice_to_term slice

  let width = function
    | Bits l -> List.length l
    | Slice s -> slice_width s

  let fv x = function
    | Bits l  -> assert false
    | Slice s -> slice_fv x s
end

(* Terms extended with primitive constructs for bvand bvor bvneg *)

module ExtTerm = struct
  type 'a ext =
    | T of 'a
    | Block of Block.t
    | Concat of t list
  and t = Term.t ext [@@deriving show]

  let rec to_term = function
    | T t -> t
    | Block block -> Block.to_term block
    | Concat l -> Term.BV.bvconcat (List.map to_term l)

  type yt = Types.yterm ext

  let reveal : t -> yt = function
    | T a      -> T(Term.reveal a)
    | Block a  -> Block a
    | Concat l -> Concat l

  let rec build = function
    | T a      -> T(Term.build a)
    | Block block -> Block block
    | Concat l -> Concat l

  let term_width = width
  let rec width = function
    | T a      -> term_width a
    | Block a  -> Block.width a
    | Concat l -> List.fold_left (fun sofar block -> sofar + width block) 0 l

  let term_fv = fv
  let rec fv x = function
    | T a -> term_fv x a
    | Block a -> Block.fv x a
    | Concat l -> List.exists (fv x) l

  let typeof = function
    | T a -> Term.type_of_term a
    | other -> width other |> Type.bv

end

let bvarray bits =
  let open Types in
  let open Option in

  (* Check if bit is t[i] *)
  let rec analyse bit =
    let open BoolStruct in
    match Term.reveal bit with
    | Term(Projection(`YICES_BIT_TERM, i, t)) -> return (Leaf(i, t))
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
      Or t
    | _ -> None
  in
  let open Block in
  let init_slice bit = function
    | Some bstruct ->
      let aux (i,extractee) = Slice.{ extractee; lo = i; hi = i+1 } in
      Slice(BoolStruct.map aux bstruct)
    | None -> Bits [bit]
  in
  let close_slice = function
    | Slice _ as slice -> slice
    | Bits l -> Bits(List.rev l)
  in
  let rec test slice bit =
    let open BoolStruct in
    match slice, bit with
    | Leaf Slice.{extractee; lo; hi}, Leaf(i,t) when hi = i && Term.equal t extractee ->
      return (Leaf Slice.{extractee; lo; hi = hi+1})
    | And l_slice, And l_bit ->
      let+ slice = aux [] (l_slice, l_bit) in
      And slice
    | Or l_slice, Or l_bit ->
      let+ slice = aux [] (l_slice, l_bit) in
      Or slice
    | Not slice, Not bit ->
      let+ slice = test slice bit in
      Not slice
    | _ -> None
  and aux accu = function
    | [], [] -> return accu
    | (head_slice::tail_slice), (head_bit::tail_bit) ->
      let* slice = test head_slice head_bit in
      aux (slice::accu) (tail_slice, tail_bit)
    | [], _::_ | _::_, [] -> None
  in
  let open ExtTerm in
  let rec aux ?slice accu bits = match slice, accu, bits with
    | Some slice, _, [] -> (Block (close_slice slice))::accu (* we have finished, closing last slice *)
    | Some slice, _, bit::tail -> (* we had started and we have a new bit to look at *)
      let slice, accu = match slice, analyse bit with
        | Slice s, (Some b as sbit) ->
          begin
            match test s b with
            | Some s -> Slice s, accu
            | None -> init_slice bit sbit, (Block (close_slice slice))::accu
          end
        | Bits l, None -> Bits(bit::l), accu
        | _, sbit -> init_slice bit sbit, (Block (close_slice slice))::accu
      in
      aux ~slice accu tail
    | None, [], bit::tail -> (* initialisation *)
      let slice = analyse bit |> init_slice bit in
      aux ~slice [] tail
    | None, _, []   (* No current slice but no bit to treat *)
    | None, _::_, _ (* No current slice but we have already accumulated slices *)
      -> assert false
  in
  aux [] bits |> List.rev


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
      begin match bl with
        | true::tail when List.for_all (fun b -> b) tail ->  (* coeff is -1 *)
          (ExtTerm.T e_i, Term.BV.bvneg t') :: next
        | true::tail when List.for_all (fun b -> not b) tail -> (* coeff is 1 *)
          (ExtTerm.T e_i, t') :: next
        | _ ->
          let coeff = Term.BV.bvconst_from_list bl in
          let monom_term = Term.BV.bvproduct [coeff; e_i] in 
          (ExtTerm.T monom_term, t')::next
      end
    | monomial ::to_treat -> aux (monomial::treated) to_treat

  in
  aux [] l

(* Solves concat(...,e_i,...) = t) in x
   It produces a list of pairs (e_i, t_i) such that
   * x is free in e_i
   * e_i is not a BV_ARRAY, and in particular not an extract
   * (e_i = t_i) is implied by concat(...,e_i,...) = t *)

let getInverseConcat (x : Term.t) (t : Term.t) (concat : ExtTerm.t list) =
  let open Block in
  let open ExtTerm in
  let rec aux start_index = function
    | [] -> [] (* x did not appear in a nice place *)

    | Block(Bits l):: tail ->
      aux (start_index + List.length l) tail

    | Block(Slice bstruct) :: tail ->
      let width = slice_width bstruct in
      let next = aux (start_index + width) tail in
      if slice_fv x bstruct
      then
        let t' = Term.BV.bvextract t start_index (start_index + width - 1) in
        (Block(Slice bstruct), t') :: next
      else
        next
    | T _ :: _ | Concat _ :: _ -> assert false
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

let getIC
    (var : Term.t)
    (cons : pred)
    ~uneval
    ~eval
    ~uneval_left
    ~polarity : Term.t =
  let open Types in
  let open Term in
  let open BV in
  if not(Term.is_bitvector eval) then raise NotImplemented;
  let width = ExtTerm.width uneval in
  let zero  = bvconst_zero ~width in
  let zero_not = bvnot zero in
  let filter (coeff, monom) =
    match monom with
    | Some monom when equal monom var ->
      let coeff = bvconst_from_list coeff in
      Term.equal coeff (bvconst_one ~width)
      || Term.equal coeff (bvconst_int ~width (-1)) 
    | _ -> true
  in
  let t = eval in
  match uneval with
  | ExtTerm.T e ->
    let Term l = reveal e in 
    print 4 "@[<2>getIC on %s%a with uneval = %a (%s) and eval = %a (%s)@]@,"
      (if polarity then "" else "the negation of ")
      Types.pp_term_constructor (match cons with
          | `YICES_BV_GE_ATOM  -> `YICES_BV_GE_ATOM
          | `YICES_BV_SGE_ATOM -> `YICES_BV_SGE_ATOM
          | `YICES_EQ_TERM -> `YICES_EQ_TERM)
      Term.pp e
      (if uneval_left then "left" else "right")
      Term.pp eval
      (if uneval_left then "right" else "left");
    begin
      match cons with
      | `YICES_EQ_TERM -> (* Table 2 *)
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

          (* | No easy representation of x & s = t in yices *)

          | Astar(`YICES_OR_TERM, l) ->
            let aux sofar a =
              if equal a var then sofar
              else a::sofar
            in
            let s = List.fold_left aux [] l in
            if polarity
            then (bvor (t::s)) === t
            else
              let s = build (Astar(`YICES_OR_TERM, s)) in
              (s =/= zero_not) ||| (t =/= zero_not)

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

          | A2(`YICES_BV_SMOD, x, s)
          | A2(`YICES_BV_SDIV, x, s)
          | A2(`YICES_BV_SREM, x, s)
            -> raise NotImplemented

          | A2(`YICES_BV_GE_ATOM, _, _)
          | A2(`YICES_EQ_TERM, _, _)
          | A2(`YICES_BV_SGE_ATOM, _, _)
            -> assert false
          | _ -> raise NotImplemented
        end

      | `YICES_BV_GE_ATOM ->
        let cond() =
          if polarity
          then Term.true0()
          else if uneval_left
          then t =/= zero
          else t =/= zero_not
        in
        begin
          match l with

          (* Table 5 cases *)
          | _ when equal var e             -> cond()
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

      | `YICES_BV_SGE_ATOM ->
        let cond() =
          if polarity
          then Term.true0()
          else if uneval_left
          then t =/= mins ~width
          else t =/= maxs ~width
        in
        begin
          match l with
          (* Table 5 cases *)
          | _ when equal var e -> cond()
          | BV_Sum l when List.for_all filter l ->  cond()
          (* Tables 7 and 8 *)
          | _ -> raise NotImplemented
        end
    end
  | ExtTerm.Block _ -> raise NotImplemented
  | ExtTerm.Concat _ -> raise NotImplemented


(**************************)
(* Building substitutions *)
(**************************)

module Monad = struct

  (* This monad is meant to create variants of a term-carrying type 
     where at most 1 term has been substituted by a fresh variable.
     If there are n terms packed in the original data, we should have (n+1) variants
     (as we include the original data) *)

  (* A variant is generated by 1 optional modification *)
  type modif = Term.t * ExtTerm.t
  type 'a variant = 'a * modif 
  (* A list of variants *)
  type 'a variants = {
    original : 'a;
    variants : 'a variant LazyList.t
  }

  (* Monad type: tell me if a modification was already performed,
     and I will update the list of variants *)
  type 'a t = 'a variants

  (* Return: I'll just add the unmodified data *)
  let return a = {
    original = a;
    variants = LazyList.empty
  }

  (* Bind: update the variants using the argument arg,
     then go over each of them and apply f;
     in each case a,
     either a is the original data (no modification) and f can do up to 1 modification,
     or a is modified, and f is not allowed to make further modifications *)

  let bind (type a b) (arg: a t) (f : a -> b t) : b t =
    let f_original = f arg.original in
    let aux (nexts : b variant LazyList.t) ((a, modif) : a variant) : b variant LazyList.node =
      `Cons(((f a).original, modif), nexts)
    in
    { original = f_original.original;
      variants = LazyList.fold aux f_original.variants arg.variants }

  let (let*) (type a b) (a : a t) (f : a->b) : b t = bind a (fun r -> return(f r))
  let (let+) = bind
end

module Variants = struct
  open MTerm(Monad)
  open ExtTerm
  open Monad

  let rec mapList : type a b. (a -> b Monad.t) -> a list -> b list Monad.t =
    fun f -> function
    | [] -> return []
    | head::tail ->
      let+ h = f head in
      let* t = mapList f tail in
      h::t

  let rec slice_map (f : ExtTerm.t -> ExtTerm.t Monad.t) slice =
    let open BoolStruct in
    match slice with
    | Leaf Slice.{extractee; lo; hi} -> 
      let* extractee = f(T extractee) in (* Should produce variants of the form (T _) *)
      let extractee  = ExtTerm.to_term extractee in (* Hence to_term should be (T t) -> t *)
      Leaf Slice.{extractee; lo; hi}
    | And l -> let* l = mapList (slice_map f) l in And l
    | Or l  -> let* l = mapList (slice_map f) l in Or l
    | Not a -> let* a = slice_map f a in Not a

  let term_map = map

  let rec map (f : ExtTerm.t -> ExtTerm.t Monad.t) = function
    | T a ->
      let aux f t =
        let* t = f(T t) in (* Should produce variants of the form (T _) *)
        ExtTerm.to_term t  (* Hence to_term should be (T t) -> t *)
      in
      let* a = term_map (aux f) a in T a
    | Block(Slice slice) -> 
      let open Block in
      let* slice = slice_map f slice in
      Block(Slice slice)
    | Block(Bits _) as bits -> return bits
    | Concat l ->
      let open Block in
      let* blocks = mapList f l in Concat blocks
end

type subst = {
  body : Term.t;
  epsilons : Term.t list
}

let pp_subst x fmt { body; epsilons } =
  Format.fprintf fmt "{%a <- %a} with %a" Term.pp x Term.pp body (List.pp Term.pp) epsilons

module Substs = struct

  type substs =
    | Eliminate of subst  (* substitution eliminates variable AND
                             faithfully represents literal from whence it came *)
    | NonLinear of subst list

  let pp_substs x fmt = function
    | Eliminate s ->
      Format.fprintf fmt "Elim %a" (pp_subst x) s
    | NonLinear [] ->
      Format.fprintf fmt "Nothing"
    | NonLinear l ->
      Format.fprintf fmt "NonLinear %a" (List.pp (pp_subst x)) l

  type t = subst list -> substs

  let (||>) (a : t) f solutions =
    match a solutions with
    | Eliminate body as result -> result
    | NonLinear result         -> f result
  
  let nil solutions = NonLinear solutions 
  let eliminate subst _ = Eliminate subst 
  let nonlinear subst solutions = NonLinear(subst :: solutions) 

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
  : subst list -> Substs.substs
  =
  print 4 "@[<2>solve with var = %a, uneval = %a and eval = %a@]@,"
    Term.pp x
    ExtTerm.pp uneval
    Term.pp eval;
  match uneval with
  | ExtTerm.T e when Term.equal e x ->
    begin
      (* Particular case when the 1st argument is x itself - end of recursion *)
      try
        print 4 "@[<2>uneval is the variable@]@,";
        let subst = 
          match cons with
          | `YICES_EQ_TERM when polarity -> { body = eval; epsilons }
          | _ ->
            let phi = getIC x cons ~uneval ~eval ~uneval_left ~polarity in
            let typ = Term.type_of_term x in
            let y = Term.new_uninterpreted typ in
            let b = make_lit cons ~uneval:y ~eval ~uneval_left ~polarity in
            { body = y; epsilons = Term.(phi ==> b)::epsilons }
        in
        if not(fv x eval)
        then Substs.eliminate subst
        else Substs.nonlinear subst
      with NotImplemented -> Substs.nil
    end
  | ExtTerm.T e ->
    let Term a = Term.reveal e in
    solve_aux x cons (ExtTerm.T a) eval ~uneval_left ~polarity epsilons
  | ExtTerm.Block block ->
    solve_aux x cons (ExtTerm.Block block) eval ~uneval_left ~polarity epsilons
  | ExtTerm.Concat l ->
    solve_aux x cons (ExtTerm.Concat l) eval ~uneval_left ~polarity epsilons

and solve_aux : type a. Term.t -> pred -> a Types.termstruct ExtTerm.ext -> Term.t ->
  uneval_left:bool -> polarity:bool -> Term.t list -> subst list -> Substs.substs
  = fun (x : Term.t)
    (cons : pred)
    a
    (t : Term.t)
    ~uneval_left
    ~polarity
    (epsilons : Term.t list) ->
    print 4 "@[<2>uneval is not the variable@]@,";
    (* The recursive call is parameterised by e_i and t *)
    let treat e_i t' = solve x cons ~uneval:e_i ~eval:t' ~uneval_left ~polarity epsilons in
    let rec treat_nl = function
      | []             -> fun solutions -> solutions
      | (e_i,t')::tail ->
        let cont f solutions =
          match treat e_i t' solutions with
          | Eliminate subst     -> f (subst :: solutions)
          | NonLinear solutions -> f solutions
        in
        treat_nl tail |> cont
    in
    let rec recurs_call accu = function
      | []              -> fun solutions -> NonLinear(treat_nl accu solutions)
      | (e_i, t')::tail ->
        if fv x t'
        then recurs_call accu tail (* Non-linear case goes in accumulator *)
        (* then recurs_call ((e_i, t')::accu) tail (\* Non-linear case goes in accumulator *\) *)
        else treat e_i t' ||> recurs_call accu tail
        (* Linear case treated immediately doesn't go further if it comes back with Linear subst *)
    in
    let test_poly = function
      | [coeff, Some var] ->
        begin match coeff with
          | true::tail when List.for_all (fun b -> b) tail -> true  (* coeff is -1 *)
          | true::tail when List.for_all (fun b -> not b) tail -> true (* coeff is 1 *)
          | _ -> false
        end
      | _ -> true
    in
    let open Types in
    let open ExtTerm in
    let a = match a with
      | T (Astar(`YICES_BV_ARRAY, bits)) ->
        begin match bvarray bits with
          | [s] -> s
          | l   -> Concat l
        end
      | a -> a
    in
    match cons, a with (* We analyse the top-level predicate and its 1st argument e *)

    | `YICES_EQ_TERM, Concat blocks ->
       getInverseConcat x t blocks |> recurs_call []

    | `YICES_EQ_TERM, T(BV_Sum l) when test_poly l ->
      getInversePoly x t l |> recurs_call []

    | _ ->
      let aux (e_i : ExtTerm.t) =
        print 4 "@[<2>aux on e_i = %a@]@," ExtTerm.pp e_i;
        let variants = lazy(
          if ExtTerm.fv x e_i
        then
          begin
            print 4 "@[<2>Detecting possible modif@]@,";
            let typ = ExtTerm.typeof e_i in
            let x'  = Term.new_uninterpreted typ in
            let variant = ExtTerm.T x', (x', e_i) in
            `Cons(variant, LazyList.empty)
          end
        else `Nil)
      in
      Monad.{ original = e_i; variants }
    in
    let variants = Variants.map aux a in
    let treat dx'_raw (x', e_i) solutions = try
        print 4 "@[<2>aux on head = %a@]@," ExtTerm.pp e_i;
        let dx' = ExtTerm.build dx'_raw in
        print 4 "@[<2>dx' built as %a@]@," ExtTerm.pp dx';
        let phi = getIC x' cons ~uneval:dx' ~eval:t ~uneval_left ~polarity in
        print 4 "@[<2>getIC gave us %a@]@," Term.pp phi;
        let typ = Term.type_of_term x' in
        let y   = Term.new_variable typ in
        let dy  = Term.subst_term [x',y] (ExtTerm.to_term dx') in
        let b   = make_lit cons ~uneval:dy ~eval:t ~uneval_left ~polarity in
        solve x `YICES_EQ_TERM ~uneval:e_i ~eval:y ~uneval_left:true ~polarity:true
          (Term.(phi ==> b)::epsilons) solutions
      with NotImplemented ->
        print 4 "Not implemented@,";
        NonLinear solutions
    in
    let aux nexts (dx'_raw, modif) solutions =
      match treat dx'_raw modif solutions with
      | NonLinear _ as result -> result
      | Eliminate _ as result -> result
    in
    let variants = LazyList.fold aux (lazy (fun substs -> NonLinear substs)) variants.variants in
    Lazy.force variants


let solve_atom
    (x : Term.t)
    (atom : [`a2] Types.composite Types.termstruct)
    (polarity : bool)
    epsilons  (* The specs of the epsilon terms we have created in the recursive solve descent *)
  =
  let Types.A2(cons,e,t) = atom in
  print 4 "@[<2>solve_atom %a with lhs = %a and rhs = %a@]@,"
    Term.pp x
    Term.pp e
    Term.pp t;
  match cons with
  | `YICES_EQ_TERM | `YICES_BV_GE_ATOM | `YICES_BV_SGE_ATOM as cons ->
    if fv x t
    then if fv x e
      then match cons with
        | `YICES_EQ_TERM when Term.is_bitvector t || Term.is_arithmetic t ->
          print 6 "@[<2>Present on both sides, and is bv or arith@]@,";
          let uneval, eval =
            if Term.is_bitvector t
            then Term.BV.bvsub t e, Term.BV.bvconst_zero ~width:(width t)
            else Term.Arith.sub t e, Term.Arith.zero()
          in
          solve x `YICES_EQ_TERM ~uneval:(T uneval) ~eval ~uneval_left:true ~polarity epsilons
        | _ ->
          print 6 "@[<2>Present on both sides, and is not bv or arith@]@,";
          solve x cons ~uneval:(T e) ~eval:t ~uneval_left:true ~polarity epsilons
          ||> solve x cons ~uneval:(T t) ~eval:e ~uneval_left:false ~polarity epsilons
      else
        (print 6 "@[<2>Present on rhs only@]@,";
         solve x cons ~uneval:(T t) ~eval:e ~uneval_left:false ~polarity epsilons)
    else
      (print 6 "@[<2>Present on lhs only@]@,";
       solve x cons ~uneval:(T e) ~eval:t ~uneval_left:true ~polarity epsilons)
  | _ -> assert false


let solve_lit x lit substs =
  let open Term in
  let open Types in
  print 1 "@[<v2>solve_lit looks at@,%a@," Term.pp lit;
  let aux b t =
    let r =
      if Term.equal x t then
        let body = if b then Term.true0() else Term.false0() in
        Substs.eliminate {body; epsilons = []} substs
      else
        match reveal t with
        | Term(A2 _ as atom) when fv x t -> solve_atom x atom b [] substs
        | _ -> Substs.nil substs
    in
    print 1 "@[<2>which turns into %a@]@]@," (Substs.pp_substs x) r;
    r
  in
  match reveal lit with
  | Term(A1(`YICES_NOT_TERM, t')) -> aux false t'
  | _ -> aux true lit


let solve_list conjuncts old_epsilons x : Term.t list * Term.t list * bool =
  print 3 "@[<hv2>solve_list solves %a from@,%a@,@[<v>"
    Term.pp x
    (List.pp Term.pp) conjuncts;
  let rec aux treated accu = function
    | [] ->
      begin match accu with
        | [Some not_faithful, {body; epsilons}] ->
          print 5 "@[<2>solve_list substitutes %a by %a@]@," Term.pp x Term.pp body;
          Term.subst_terms [x,body] conjuncts,
          epsilons @ Term.subst_terms [x,body] old_epsilons,
          not_faithful()
        | _ ->
          print 5 "@[<2>solve_list does not substitute@]@,";
          conjuncts, old_epsilons, true
      end
      
    | lit::tail ->
      match solve_lit x lit [] with

      | Eliminate { body; epsilons = [] } ->
        print 5 "@[<2>solve_list substitutes %a by %a@]@," Term.pp x Term.pp body;
        Term.subst_terms [x,body] conjuncts, Term.subst_terms [x,body] old_epsilons, false

      | Eliminate subst  ->
        let not_faithful() =
          List.exists (fv x) treated
          || List.exists (fv x) tail
          || List.exists (fv x) old_epsilons
        in

        aux (lit::treated) ((Some not_faithful, subst)::accu) tail

      | NonLinear substs ->
        let rec aux2 accu = function
          | [] -> accu
          | subst::substs -> aux2 ((None, subst)::accu) substs
        in
        aux (lit::treated) (aux2 accu substs) tail
  in
  let result = aux [] [] conjuncts in
  print 3 "@]@]@,";
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
    | Term(A1(`YICES_NOT_TERM, t)) -> aux t |> List.map Term.not1
    | _ -> [t]
  in
  print 3 "@[<2>IC analyses %a@]@," Term.pp t;
  let rec aux conjuncts epsilons = function
    | [] -> conjuncts, epsilons
    | x::vars ->
      print 3 "@[<2>solve_all_aux@]@,";
      match solve_list conjuncts epsilons x with
      | _, _, true                 -> aux conjuncts epsilons vars
      | conjuncts, epsilons, false -> aux conjuncts epsilons vars
  in
  let conjuncts, epsilons = aux conjuncts [] vars in
  print 3 "@[<2>IC finished@]@,";
  Term.andN conjuncts, epsilons
