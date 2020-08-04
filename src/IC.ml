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
  let singleton a = lazy (`Cons(a,empty))

  let rec map f l = lazy (match Lazy.force l with
      | `Nil -> `Nil
      | `Cons(head,tail) -> `Cons(f head, map f tail))

  let rec append s1 s2 = lazy(
    match Lazy.force s1 with
    | `Nil -> Lazy.force s2
    | `Cons(head, tail ) -> `Cons(head, append tail s2))

  let rec flatten l = lazy (match l with
      | [] -> `Nil
      | head::tail -> Lazy.force (append head (flatten tail)))
    
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
  let (let*) = bind
end

open MTerm(OptionMonad)

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

type concat =
  | Bits of Term.t list
  | Extract of { extractee : Term.t; lo : int; hi: int; polarity: bool }

let bvarray bits =
  let open Types in

  (* Check if bit is t[i] *)
  let analyse bit =
    match Term.reveal bit with
    | Term(Projection(`YICES_BIT_TERM, i, t)) -> Some(i, t)
    | _ -> None
  in
  (* Check if bit is t[i] or (not t[i]) *)
  let analyse bit =
    match Term.reveal bit with
    | Term(A1(`YICES_NOT_TERM, bit)) -> analyse bit |> Option.map (fun (i,t) -> i,t,false) 
    | _ -> analyse bit |> Option.map (fun (i,t) -> i,t,true)
  in
  let init_slice bit = function
    | Some(i, extractee, polarity) -> Extract{ extractee; lo = i; hi = i+1; polarity }
    | None -> Bits [bit]
  in
  let close_slice = function
    | Extract _ as slice -> slice
    | Bits l -> Bits(List.rev l)
  in
  let rec aux ?slice accu bits = match slice, accu, bits with
    | Some slice, _, [] -> (close_slice slice)::accu (* we have finished, closing last slice *)
    | Some slice, _, bit::tail -> (* we had started and we have a new bit to look at *)
      let slice, accu = match slice, analyse bit with
        | Extract{ extractee; lo; hi; polarity }, Some(i, t', polarity')
          when Term.equal extractee t' && hi = i && Bool.equal polarity polarity' ->
          Extract{ extractee; lo; hi = hi+1; polarity }, accu
        | Bits l, None -> Bits(bit::l), accu
        | _, _ -> analyse bit |> init_slice bit, (close_slice slice)::accu
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

let width y = Type.bvsize(Term.type_of_term y)

(* Solves (P[x] = t) in x, for bv-polynomial P expressed as list l,
   Works if x only appears in P as monomial x or -x, otherwise raises exception
   Table 4 of CAV'2018 *)

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
    | [] -> [] (* could not find a monomial with variable x and coefficient 1 or -1 *)
    | (bl,Some e_i) as monomial::to_treat when fv x e_i ->
      begin match bl with
        | true::tail when List.for_all (fun b -> b) tail ->  (* coeff is -1 *)
          let t' = Term.BV.bvneg(rebuild treated to_treat) in
          (e_i,t') :: (aux (monomial::treated) to_treat)
        | true::tail when List.for_all (fun b -> not b) tail -> (* coeff is 1 *)
          let t' = rebuild treated to_treat in
          (e_i, t') :: (aux (monomial::treated) to_treat)
        | _ -> aux (monomial::treated) to_treat
      end
    | monomial ::to_treat -> aux (monomial::treated) to_treat

  in
  aux [] l

(* Solves concat(...,e_i,...) = t) in x *)

let getInverseConcat (x : Term.t) (t : Term.t) (bits : Term.t list) =
  let concat = bvarray bits in
  let rec aux start_index = function
    | [] -> [] (* x did not appear in a nice place *)

    | Bits l:: tail ->
      aux (start_index + List.length l) tail

    | Extract{ extractee; lo; hi; polarity }::tail
      when lo = 0 && hi = width extractee && fv x extractee ->
      let t'  = Term.BV.bvextract t start_index (start_index + hi - 1) in
      let t'  = if polarity then t' else Term.BV.bvnot t' in
      (extractee, t') ::  (aux (start_index + hi - lo) tail)

    | Extract{ lo; hi }::tail ->
      aux (start_index + hi - lo) tail
      
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
  let width = width uneval in
  let zero  = bvconst_zero ~width in
  let zero_neg = bvneg zero in
    let filter (coeff, monom) =
      match monom with
      | Some monom when equal monom var ->
        let coeff = bvconst_from_list coeff in
        Term.equal coeff (bvconst_one ~width)
        || Term.equal coeff (bvconst_int ~width (-1)) 
      | _ -> true
    in
  let t = uneval in
  let Term l = reveal uneval in
  match cons with
  | `YICES_EQ_TERM ->
    begin
      match l with
      | _ when equal var uneval ->
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
        else (s =/= zero) ||| (t =/= zero_neg)

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
          (s =/= zero_neg) ||| (t =/= zero_neg)

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
          ((bvge s w) ==> (( t === zero_neg) ||| (t === zero)))
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
          ((t =/= zero_neg) ||| (s =/= zero_neg))

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
      | _ -> assert false
    end

  | `YICES_BV_GE_ATOM ->
    let cond() =
      if polarity
      then Term.true0()
      else if uneval_left
      then t =/= zero
      else t =/= zero_neg
    in
    begin
      match l with
      (* hard to characterise when l is bvneg *)
      | _ when equal var uneval -> cond()
      (* | BV_Sum l when List.for_all filter l ->  cond() *)
      | _ -> raise NotImplemented
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
      (* hard to characterise when l is bvneg *)
      (* | _ when equal var uneval -> cond() *)
      (* | BV_Sum l when List.for_all filter l ->  cond() *)
      | _ -> raise NotImplemented
    end



(**************************)
(* Building substitutions *)
(**************************)

module Monad = struct
  type modif = (Term.t * Term.t) option
  type 'a variants = ('a * modif) list
  type 'a t = modif -> 'a variants -> 'a variants
  let return a _ variants = (a, None)::variants
  let bind (type  a b) (a: a t) (f : a -> b t) modif variants =
    let aux (sofar : b variants) (a,modif) = f a modif sofar in
    List.fold_left aux variants (a modif [])
end

module Variants = MTerm(Monad)

type subst = {
  body : Term.t;
  epsilons : Term.t list
}

let pp_subst x fmt { body; epsilons } =
  Format.fprintf fmt "{%a <- %a} with %a" Term.pp x Term.pp body (List.pp Term.pp) epsilons

module Substs = struct

  type substs =
    | Eliminate of subst
    | NonLinear of subst list

  let pp_substs x fmt = function
    | Eliminate s ->
      Format.fprintf fmt "Elim %a" (pp_subst x) s
    | NonLinear [] ->
      Format.fprintf fmt "Nothing"
    | NonLinear l ->
      Format.fprintf fmt "NonLinear %a" (List.pp (pp_subst x)) l

  type t = subst list -> substs

  let (let*) (a : t) f solutions =
    match a solutions with
    | Eliminate _ as result -> result
    | NonLinear result -> f result
  let (||>) = (let*)
  
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
    epsilons  (* The specs of the epsilon terms we have created in the recursive solve descent *)
  : subst list -> Substs.substs
  =
  print 4 "@[<2>solve with var = %a, uneval = %a and eval = %a@]@,"
    Term.pp x
    Term.pp uneval
    Term.pp eval;
  let e,t = uneval, eval in
  if Term.equal e x then (* Particular case when the 1st argument is x itself - end of recursion *)
    try
      print 4 "@[<2>uneval is the variable@]@,";
      let subst = 
        match cons with
        | `YICES_EQ_TERM when polarity -> { body = t; epsilons }
        | _ ->
          let phi = getIC x cons ~uneval ~eval ~uneval_left ~polarity in
          let typ = Term.type_of_term x in
          let y = Term.new_uninterpreted typ in
          let b = make_lit cons ~uneval:y ~eval:t ~uneval_left ~polarity in
          { body = y; epsilons = Term.(phi ==> b)::epsilons }
      in
      if not(fv x t)
      then Substs.eliminate subst
      else Substs.nonlinear subst
    with NotImplemented -> Substs.nil
  else
    begin
    print 4 "@[<2>uneval is not the variable@]@,";
    (* The recursive call is parameterised by e_i and t *)
    let treat e_i t' = solve x cons ~uneval:e_i ~eval:t' ~uneval_left ~polarity epsilons in
    let rec treat_nl = function
      | []             -> fun solutions -> solutions
      | (e_i,t')::tail ->
        let cont f solutions =
            match treat e_i t' solutions with
            | Eliminate result    -> f (result :: solutions)
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
    let Term a = Term.reveal e in
    match cons, a with (* We analyse the top-level predicate and its 1st argument e *)
    | `YICES_EQ_TERM, Types.(BV_Sum l) ->
      getInversePoly x t l |> recurs_call []
    | `YICES_EQ_TERM, Types.(Astar(`YICES_BV_ARRAY, bits)) ->
      getInverseConcat x t bits |> recurs_call []
    | _ ->
      let aux e_i modif variants =
        let variants = (e_i,None) :: variants in
        match modif with
        | None when fv x e_i ->
            let typ = Term.type_of_term e_i in
            let x'  = Term.new_uninterpreted typ in
            (x',Some(x', e_i)) :: variants
        | _ -> variants
      in
      let variants = Variants.map aux a None [] in
      let treat = function
        | dx'_raw, None -> Substs.nil
        | dx'_raw, Some(x', e_i) -> try
            let dx' = Term.build dx'_raw in
            let phi = getIC x' cons ~uneval:dx' ~eval:t ~uneval_left ~polarity in
            let typ = Term.type_of_term x' in
            let y   = Term.new_variable typ in
            let dy  = Term.subst_term [x',y] dx' in
            let b   = make_lit cons ~uneval:dy ~eval:t ~uneval_left ~polarity in
            solve x `YICES_EQ_TERM ~uneval:e_i ~eval:y ~uneval_left:true ~polarity:true
              (Term.(phi ==> b)::epsilons)
          with NotImplemented -> Substs.nil
      in
      let rec aux = function
        | []         -> Substs.nil
        | head::tail -> treat head ||> aux tail
      in
      aux variants
  end

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
          solve x `YICES_EQ_TERM ~uneval ~eval ~uneval_left:true ~polarity epsilons
        | _ ->
          print 6 "@[<2>Present on both sides, and is not bv or arith@]@,";
          solve x cons ~uneval:e ~eval:t ~uneval_left:true ~polarity epsilons
          ||> solve x cons ~uneval:t ~eval:e ~uneval_left:false ~polarity epsilons
      else
        (print 6 "@[<2>Present on rhs only@]@,";
         solve x cons ~uneval:t ~eval:e ~uneval_left:false ~polarity epsilons)
    else
      (print 6 "@[<2>Present on lhs only@]@,";
       solve x cons ~uneval:e ~eval:t ~uneval_left:true ~polarity epsilons)
  | _ -> assert false


let solve_lit x lit =
  let open Term in
  let open Types in
  let aux b t =
    if Term.equal x t then
      let body = if b then Term.true0() else Term.false0() in
      Substs.eliminate { body; epsilons = [] }
    else
      match reveal t with
      | Term(A2 _ as atom) when fv x t ->
        let r = solve_atom x atom b [] in
        print 1 "@[<2>solve_lit turns %a into %a@]@," Term.pp lit (Substs.pp_substs x) (r []);
        r
      | _ -> Substs.nil
  in
  match reveal lit with
  | Term(A1(`YICES_NOT_TERM, t')) -> aux false t'
  | _ -> aux true lit


let solve_list ((l,epsilons) as le) x =
  let rec aux = function
    | [] -> Substs.nil
    | lit::tail -> solve_lit x lit ||> aux tail
  in
  let substitute {body ; epsilons } (l,old_epsilons) =
    print 5 "@[<2>solve_list substitutes %a by %a@]@," Term.pp x Term.pp body;
    Term.subst_terms [x,body] l, Term.subst_terms [x,body] old_epsilons @ epsilons
  in
  let results = aux l [] in
  print 3 "@[<2>solve_list solves %a from %a, giving %a@]@,"
    Term.pp x
    (List.pp Term.pp) l
    (Substs.pp_substs x) results;
  match results with
  | Eliminate subst -> substitute subst le 
  | NonLinear _ -> le
  (* | NonLinear(subst::_) -> substitute subst le *)


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
  let l,epsilons = List.fold_left solve_list (conjuncts,[]) vars in
  Term.andN l, epsilons
