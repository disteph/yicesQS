open! Containers
open Yices2.Ext
open WithNoErrorHandling
open Utils

module OptionMonad = struct
  include Option
  let bind = ( >>= )
end

open MTerm(OptionMonad)


(* Build 10...0 of length width *)   
let mins ~width = true :: List.init (width - 1) (fun _ -> false)
                  |> List.rev
                  |> Term.BV.bvconst_from_list

(* Build 01...1 of length width *)   
let maxs ~width = false :: List.init (width - 1) (fun _ -> true)
                  |> List.rev
                  |> Term.BV.bvconst_from_list


(****************************************************************)
(* Conditional inverses as in the Niemetz et al. CAV'2018 paper *)
(* References are to the long version at                        *)
(* https://arxiv.org/pdf/1804.05025.pdf                         *)
(****************************************************************)


(*********************)
(* Inverse functions *)
(*********************)


(* Whether bv constant (list of bools) is -1 *)
let is_minus_one = function
  | true::tail when List.for_all (fun b -> b) tail -> true
  | _ -> false

(* Whether bv constant (list of bools) is 1 *)
let is_one = function
  | true::tail when List.for_all (fun b -> not b) tail -> true
  | _ -> false

(* Solves (P[x] = t) in x, for bv-polynomial P expressed as list l of monomials,
   inspired by Table 4 of CAV'2018.
   It produces a list of pairs (e_i, t_i) such that
   * x is free in e_i
   * e_i is either a monomial variable of P, or a monomial (cst*e_i') of P with cst not 1 or -1)
   * (e_i = t_i) is equivalent to (P[x] = t) *)

let getInversePoly
      (x : Term.t)
      (t : Term.t)
      (l : (bool list * Term.t option) list) (* Monomials: bool list is the constant *)
    : (ExtTerm.t * Term.t) list =

  (* Computes (t - \BigSum (treated @ to_treat)), the right-hand side t_i *)
  let rebuild treated to_treat =
    let l = List.rev_append treated to_treat in
    match l with
    | [] -> t
    | _ -> Term.BV.(bvsub t (Term.build(Types.BV_Sum l)))
  in

  (* We produce a pair (e_i, t_i) for every monomial in P that features x.
     We fold the following function over the polynomial P expressed as list l of monomials.*)

  let rec aux treated = function
    | [] -> []
    | (bl, Some e_i) as monomial::to_treat when Term.is_free ~var:x e_i ->
       (* x appears in the monomial *)
       (* We do the recursive call  *)
       let next = aux (monomial::treated) to_treat in
       (* Everything else than the monomial goes to the RHS *)
       let t_i  = rebuild treated to_treat in
       if is_minus_one bl     (* We output the pair (e_i, -t_i) *)
       then (ExtTerm.(ExtTerm(T e_i)), Term.BV.bvneg t_i) :: next
       else
         if is_one bl         (* We output the pair (e_i, t_i) *)
         then (ExtTerm.(ExtTerm(T e_i)), t_i) :: next
         else (* We output the pair (monomial, t_i) *)
           let coeff      = Term.BV.bvconst_from_list bl in
           let monom_term = Term.BV.bvproduct [coeff; e_i] in 
           (ExtTerm.(ExtTerm(T monom_term)), t_i) :: next

    | monomial ::to_treat -> (* x doesn't appear in the monomial: we accumulate *)
       aux (monomial::treated) to_treat

  in
  aux [] l

let reduce_sign_ext (ExtTerm.Block{ block; sign_ext; zero_ext } as b) =
  let open ExtTerm in
  if sign_ext = 0 then b
  else
    let width = width block in
    let block = to_term block in
    let min   = mins ~width in (* block and min should have same width *)
    let term1 = Term.BV.(zero_extend (bvadd block min) sign_ext) in
    let term2 = Term.BV.(zero_extend              min  sign_ext) in
    let term  = Term.BV.bvsub term1 term2 in
    Block{ block = Slice(BoolStruct.Leaf(Slice.build term)); sign_ext = 0; zero_ext }

(* Solves concat(...,e_i,...) = t) in x
   It produces a list of pairs (e_i, t_i) such that
   * x is free in e_i
   * e_i is not a BV_ARRAY, and in particular not an extract
   * (e_i = t_i) is implied by concat(...,e_i,...) = t *)

let getInverseConcat (x : Term.t) (t : Term.t) (concat : _ ExtTerm.block list)
    : (ExtTerm.t * Term.t) list =
  let open ExtTerm in
  let rec aux start_index = function
    | [] -> [] (* x did not appear in a nice place *)

    | Block{block = Bits _; _} as b :: tail ->
      print 6 "@[<2>getInverseConcat finds block of bits %a@]@," ExtTerm.pp b;
      aux (start_index + ExtTerm.width b) tail

    | Block{ block = Slice _ as block; sign_ext; zero_ext } as b :: tail ->
      let width = ExtTerm.width b in
      print 6 "@[<2>getInverseConcat finds block of slice %a@]@," ExtTerm.pp b;
      if ExtTerm.is_free ~var:x b
      then
        begin
          print 6 "@[<2>%a appears in it@]@," Term.pp x;
          if sign_ext = 0
          then
            (print 6 "@[<2>No sign extension@]@,";
             let width = width - zero_ext in
             let t' = Term.BV.bvextract t start_index (start_index + width - 1) in
             (ExtTerm.(ExtTerm block), t') :: aux (start_index + width) tail )
          else
            (print 6 "@[<2>Sign extension of length %i@]@," sign_ext;
             let b = reduce_sign_ext b in
             aux start_index (b::tail))
        end
      else
        begin
          print 6 "@[<2>%a doesn't appear in it@]@," Term.pp x;
          aux (start_index + width) tail
        end
  in
  aux 0 concat


(****************************)
(* Invertibility conditions *)
(****************************)

type pred = [ `YICES_BV_GE_ATOM
            | `YICES_BV_SGE_ATOM
            | `YICES_EQ_TERM
            | `YICES_ARITH_GE_ATOM ]

exception NotImplemented

(* Tables 2, 3, 5, 6, 7, 8 *)

let getIC : type a. Term.t -> pred -> uneval: a ExtTerm.termstruct -> eval:Term.t ->
  uneval_left:bool -> polarity:bool -> Term.t * (Term.t option)
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
      | a -> (ExtTerm.to_term(Slice a))::sofar
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
        | `YICES_EQ_TERM -> `YICES_EQ_TERM
        | `YICES_ARITH_GE_ATOM -> `YICES_ARITH_GE_ATOM)
    ExtTerm.pp uneval
    (if uneval_left then "left" else "right")
    Term.pp eval
    (if uneval_left then "right" else "left");

  let t = eval in
  match cons with

  | `YICES_ARITH_GE_ATOM -> raise NotImplemented
  
  | `YICES_EQ_TERM -> (* Table 2 *)
    begin
      match uneval with
      | ExtTerm.TermStruct l ->
        begin
          match l with
          | A0(_,e) when equal var e ->  (* Not actually given in the paper, just obvious *)
            assert(not polarity);
            Term.true0(), if polarity then Some t else None

          | BV_Sum [coeff, Some monom] when equal var monom ->
            let s = bvconst_from_list coeff in
            if polarity
            then (bvand [bvor [bvneg s; s]; t]) === t, None
            else (s =/= zero) ||| (t =/= zero), Some(bvshl (maxs ~width) t)

          | Product(true, prod) ->
            let aux sofar ((p,exp) as a) =
              if equal p var then
                if Unsigned.UInt.to_int exp = 1 then sofar else raise NotImplemented
              else
                a::sofar
            in
            let s = build (Product (true, List.fold_left aux [] prod)) in
            if polarity
            then (bvand [bvor [bvneg s; s]; t]) === t, None
            else (s =/= zero) ||| (t =/= zero), Some(bvshl (maxs ~width) t)

          | A2(`YICES_BV_REM, x, s) when equal var x ->
            if polarity
            then bvsge (bvnot (bvneg s)) t, Some t
            else (s =/= bvconst_one ~width) ||| (t =/= zero), Some(bvneg(bvnot t))

          | A2(`YICES_BV_REM, s, x) when equal var x ->
            if polarity
            then bvsge (bvsum [t; t; bvneg s]) t, Some(bvsub s t)
            else (s =/= zero) ||| (t =/= zero), Some t

          | A2(`YICES_BV_DIV, x, s) when equal var x ->
            if polarity
            then (bvdiv (bvmul s t) s) === t, Some(bvmul s t)
            else (s =/= zero) ||| (t =/= zero_not), Some(bvlshr s t)

          | A2(`YICES_BV_DIV, s, x) when equal var x ->
            if polarity
            then (bvdiv s (bvmul s t)) === t, None
            else
            (if width = 1 then bvand [s; t] === zero
             else true0()), Some(bvand [t; mins ~width]) 

          | A2(`YICES_BV_LSHR, x, s) when equal var x ->
            if polarity
            then (bvlshr (bvshl t s) s === t), Some(bvshl t s)
            else
              let w = bvconst_int ~width width in
              t =/= zero ||| (bvlt s w), Some(bvshl (mins ~width) t)

          | A2(`YICES_BV_LSHR, s, x) when equal var x ->
            if polarity
            then
              let rec aux i accu =
                if i = -1 then accu
                else
                  let atom = (bvlshr s (bvconst_int ~width i) === t) in
                  aux (i-1) (atom :: accu)
              in
              orN (aux width []), None
            else
              (s =/= zero) ||| (t =/= zero), Some(bvneg t)

          | A2(`YICES_BV_ASHR, x, s) when equal var x ->
            if polarity
            then
              let w = bvconst_int ~width width in
              ((bvlt s w) ==> (bvashr (bvshl t s) s === t))
              &&&
              ((bvge s w) ==> (( t === zero_not) ||| (t === zero))),
              None
            else true0(), Some(bvnot t)

          | A2(`YICES_BV_ASHR, s, x) when equal var x ->
            if polarity
            then
              let rec aux i accu =
                if i = -1 then accu
                else
                  let atom = (bvashr s (bvconst_int ~width i) === t) in
                  aux (i-1) (atom :: accu)
              in
              orN (aux width []), None
            else
              ((t =/= zero)     ||| (s =/= zero))
              &&&
              ((t =/= zero_not) ||| (s =/= zero_not)),
              Some(bvlshr t (bvsub s t))

          | A2(`YICES_BV_SHL, x, s) when equal var x ->
            if polarity
            then (bvshl (bvlshr t s) s) === t, Some(bvlshr t s)
            else (t =/= zero) ||| (bvlt s (bvconst_int ~width width)),
                 Some(bvshl (mins ~width) t)

          | A2(`YICES_BV_SHL, s, x) when Term.equal var x ->
            if polarity
            then
              let rec aux i accu =
                if i = -1 then accu
                else
                  let atom = (bvshl s (bvconst_int ~width i) === t) in
                  aux (i-1) (atom :: accu)
              in
              orN (aux width []), None
            else
              (s =/= zero) ||| (t =/= zero), Some t

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

      | ExtTerm.Slice(Leaf{ extractee = _; indices = _ }) -> (* Not in tables, but obvious *)
        true0(), None

      | ExtTerm.Slice(And l) ->
        let s = conjuncts_disjuncts l in
        if polarity
        then (bvand (t::s)) === t, Some t
        else
          (bvand s =/= zero) ||| (t =/= zero), Some(bvnot t)

      | ExtTerm.Slice(Or l) ->
        let s = conjuncts_disjuncts l in
        if polarity
        then (bvor (t::s)) === t, Some t
        else
          (bvor s =/= zero_not) ||| (t =/= zero_not), Some(bvnot t)

      | ExtTerm.Slice(Not _l) -> assert false (* Should not have led to epsilon-terms *)

      | ExtTerm.Concat _l ->
        if polarity
        then assert false (* Should not have led to epsilon-terms *)
        else true0(), None

      | ExtTerm.Block _ -> assert false (* We should have abandoned ship by now *)
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
      | ExtTerm.TermStruct l ->
        begin
          match l with

          (* Table 5 cases *)
          | A0(_,e) when equal var e            -> cond(), None
          | BV_Sum l when List.for_all filter l -> cond(), None

          (* Tables 3 and 6 *)
          | BV_Sum [coeff, Some monom] when equal var monom ->
            let s = bvconst_from_list coeff in
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge (bvor [bvneg s; s]) t, None
              else true0(), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero, None
            else bvlt t (bvor [bvneg s; s]), None

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
              then bvge (bvor [bvneg s; s]) t, None
              else true0(), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero, None
            else bvlt t (bvor [bvneg s; s]), None

          | A2(`YICES_BV_REM, x, s) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge (bvnot (bvneg s)) t, None
              else true0(), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero, None
            else bvlt t (bvnot (bvneg s)), None

          | A2(`YICES_BV_REM, s, x) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge (bvand [bvsum [t; t; bvneg s] ; s]) t ||| (bvlt t s), None
              else true0(), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero, None
            else bvlt t s, None

          | A2(`YICES_BV_DIV, x, s) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvand [ bvdiv (bvmul s t) t ; s] === s, None
              else true0(), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then (bvlt zero s) &&& (bvlt zero t), None
            else bvgt (bvdiv zero_not s) t, None

          | A2(`YICES_BV_DIV, s, x) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then true0(), None
              else bvlt zero (bvor [ bvneg s ; t]), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then (bvlt zero (bvnot(bvand [bvneg t ; s]))) &&& (bvlt zero t), None
            else bvlt t zero_not, None

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
              then true0(), None
              else bvge t s, None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then bvlt s t, None
            else bvlt t zero_not, None

          | A2(`YICES_BV_LSHR, x, s) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then (bvlshr (bvshl t s) s === t), None
              else true0(), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero, None
            else bvlt t (bvlshr (bvnot s) s), None

          | A2(`YICES_BV_LSHR, s, x) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge s t, None
              else true0(), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero, None
            else bvlt t s, None

          | A2(`YICES_BV_ASHR, x, _s) when equal var x ->
            if polarity
            then (* Table 6 *)
              true0(), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero, None
            else bvlt t zero_not, None

          | A2(`YICES_BV_ASHR, s, x) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge s (bvnot s) ||| bvge s t, None
              else bvlt s (mins ~width) ||| bvge t s, None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then (bvlt s t ||| bvsge s zero) &&& (t =/= zero), None
            else (bvslt s (bvlshr s (bvnot t))) ||| (bvlt t s), None

          | A2(`YICES_BV_SHL, x, s) when equal var x ->
            if polarity
            then (* Table 6 *)
              if uneval_left (* uneval >= eval *)
              then bvge (bvshl zero_not s) t, None
              else true0(), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero, None
            else bvlt t (bvshl zero_not s), None

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
                orN (aux width []), None
              else true0(), None
            else (* Table 3 *)
            if uneval_left (* uneval < eval *)
            then t =/= zero, None
            else
              let rec aux i accu =
                if i = -1 then accu
                else
                  let atom = bvgt (bvshl s (bvconst_int ~width i)) t in
                  aux (i-1) (atom :: accu)
              in
              orN (aux width []), None

          | A2(`YICES_BV_SMOD, _x, _s)
          | A2(`YICES_BV_SDIV, _x, _s)
          | A2(`YICES_BV_SREM, _x, _s)
            -> raise NotImplemented

          | A2(`YICES_BV_GE_ATOM, _, _)
          | A2(`YICES_EQ_TERM, _, _)
          | A2(`YICES_BV_SGE_ATOM, _, _)
            -> assert false
          | _ -> raise NotImplemented (* assert false *)

        end

      | ExtTerm.Slice(Not _)     (* Table 5 *)
      | ExtTerm.Slice(Leaf _) -> (* Should be added to Table 5 *)
        cond(), None

      | ExtTerm.Slice(And l) ->
        if polarity
        then (* Table 6 *)
          if uneval_left (* uneval >= eval *)
          then
            let s = conjuncts_disjuncts l |> bvand in
            bvge s t, None
          else true0(), None
        else (* Table 3 *)
        if uneval_left (* uneval < eval *)
        then t =/= zero, None
        else
          let s = conjuncts_disjuncts l |> bvand in
          bvlt t s, None

      | ExtTerm.Slice(Or l) ->
        if polarity
        then (* Table 6 *)
          if uneval_left (* uneval >= eval *)
          then
            true0(), None
          else 
            let s = conjuncts_disjuncts l |> bvor in
            bvge t s, None
        else (* Table 3 *)
        if uneval_left (* uneval < eval *)
        then
          let s = conjuncts_disjuncts l |> bvor in
          bvlt s t, None
        else
          t =/= zero_not, None

      | ExtTerm.Concat _l -> raise NotImplemented;
        
      | ExtTerm.Block _ -> assert false (* We should have abandoned ship by now *)
      | ExtTerm.Bits _ -> assert false (* We should have abandoned ship by now *)
    end

  | `YICES_BV_SGE_ATOM ->
    let cond() = (* Table 5 *)
      if polarity
      then Term.true0() (* Column 6 *)
      else if uneval_left
      then t =/= mins ~width (* Column 4 *)
      else t =/= maxs ~width (* Column 5 *)
    in
    match uneval with
    | ExtTerm.TermStruct l ->
      begin
        match l with

        (* Table 5 cases *)
        | A0(_,e)  when equal var e -> cond(), None
        | BV_Sum l when List.for_all filter l ->  cond(), None


        (* Tables 7 and 8 *)
        | BV_Sum [coeff, Some monom] when equal var monom ->
          let s = bvconst_from_list coeff in
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then bvsge (bvand[bvor [bvneg s; s]; maxs ~width]) t, None
            else (s =/= zero) ||| bvsge t s, None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt (bvand [ bvnot(bvneg t) ; (bvor [ bvneg s ; s ]) ]) t, None
          else bvslt t (bvsub t (bvor [s; t; bvneg s])), None

        | Product(true, prod) ->
          let aux sofar ((p,exp) as a) =
            if equal p var then
              if Unsigned.UInt.to_int exp = 1 then sofar else raise NotImplemented
            else
              a::sofar
          in
          let s = build (Product (true, List.fold_left aux [] prod)) in
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then bvsge (bvand[bvor [bvneg s; s]; maxs ~width]) t, None
            else (s =/= zero) ||| bvsge t s, None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt (bvand [ bvnot(bvneg t) ; (bvor [ bvneg s ; s ]) ]) t, None
          else bvslt t (bvsub t (bvor [s; t; bvneg s])) , None

        | A2(`YICES_BV_REM, x, s) when equal var x ->
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then (bvslt t s) ||| (bvsge zero s), None
            else bvslt zero_not (bvand [bvneg s ; t]), None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt (bvnot t) (bvor [bvneg s; bvneg t]), None
          else (bvsgt s zero ==> bvslt t (bvnot(bvneg s)))
               &&& (bvsle s zero ==> (t =/= maxs ~width))
               &&& ((t =/= zero) ||| (s =/= bvconst_one ~width)), None

        | A2(`YICES_BV_REM, s, x) when equal var x ->
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then (bvsge s zero ==> bvsge s t)
                 &&& ((bvslt s zero &&& bvsge t zero) ==> bvgt (bvsub s t) t), None
            else bvlt t (mins ~width) ||| bvsge t s, None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt s t ||| bvslt zero t, None
          else
            let one = bvconst_one ~width in
            (bvsge s zero ==> bvsgt s t)
            &&& (bvslt s zero ==> bvsgt (bvlshr (bvsub s one) one) t), None

        | A2(`YICES_BV_DIV, x, s) when equal var x ->
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then bvsge (bvdiv zero_not s) t ||| bvsge (bvdiv (maxs ~width) s) t, None
            else (bvdiv (bvmul s t) s === t) |||
                 (bvsle t zero ==> bvslt (bvdiv (mins ~width) s) t), None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvsle t zero ==> bvslt (bvdiv (mins ~width) s) t, None
          else bvsgt (bvdiv zero_not s) t ||| bvsgt (bvdiv (maxs ~width) s) t, None

        | A2(`YICES_BV_DIV, s, x) when equal var x ->
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then (bvsge s zero ==> bvsge s t) &&&
                 (bvslt s zero  ==> bvsge (bvlshr s (bvconst_one ~width)) t), None
            else bvsge t zero_not ||| bvsge t s, None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt s t ||| bvsge t zero, None
          else
          if width = 1
          then bvsgt s t, None
          else (bvsge s zero ==> bvsgt s t) &&&
               (bvslt s zero  ==> bvsgt (bvlshr s (bvconst_one ~width)) t), None

        | Astar(`YICES_OR_TERM, l) ->
          let aux sofar a =
            if equal a var then sofar
            else a::sofar
          in
          let s = List.fold_left aux [] l in
          let s = build (Astar(`YICES_OR_TERM, s)) in
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then bvsge s (bvand [s; t]), None
            else bvsge t (bvor [s; mins ~width]), None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt (bvor [bvnot(bvsub s t); s]) t, None
          else bvslt t (bvor [s; maxs ~width]), None

        | A2(`YICES_BV_LSHR, x, s) when equal var x ->
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then (s =/= zero) ==> bvsge (bvlshr zero_not s) t, None
            else bvsge t (bvlshr t s), None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt (bvlshr (bvnot(bvneg t)) s) t, None
          else bvslt t (bvlshr (bvshl (maxs ~width) s) s), None

        | A2(`YICES_BV_LSHR, s, x) when equal var x ->
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then (bvslt s zero ==> bvsge (bvlshr s (bvconst_one ~width)) t) &&&
                 (bvsge s zero ==> bvsge s t), None
            else bvlt t (mins ~width) ||| bvsge t s, None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt s t ||| bvslt zero t, None
          else (bvslt s zero ==> bvsgt (bvlshr s (bvconst_one ~width)) t) &&&
               (bvsge s zero ==> bvsgt s t), None

        | A2(`YICES_BV_ASHR, x, s) when equal var x ->
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then bvsge (bvlshr (maxs ~width) s) t, None
            else bvsge t (bvnot (bvlshr (maxs ~width) s)), None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt (bvashr (mins ~width) s) t, None
          else bvslt t (bvlshr (maxs ~width) s), None

        | A2(`YICES_BV_ASHR, s, x) when equal var x ->
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then bvge t (bvnot t) ||| bvsge s t, None
            else bvsge t zero ||| bvsge t s, None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt s t ||| bvslt zero t, None
          else bvslt t (bvand [s; maxs ~width]) &&& bvslt t (bvor [s; maxs ~width]), None

        | A2(`YICES_BV_SHL, x, s) when equal var x ->
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then
              let maxs = maxs ~width in
              bvsge (bvand [bvshl maxs s; maxs]) t, None
            else bvlt (bvlshr t (bvlshr t s)) (mins ~width), None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then bvslt (bvshl (bvlshr (mins ~width) s) s) t, None
          else
            let maxs = maxs ~width in
            bvslt t (bvand [bvshl maxs s; maxs]), None

        | A2(`YICES_BV_SHL, s, x) when Term.equal var x ->
          if polarity
          then (* Table 8 *)
            if uneval_left (* uneval >= eval *)
            then
              let rec aux i accu =
                if i = -1 then accu
                else
                  let atom = bvsge (bvshl s (bvconst_int ~width i)) t in
                  aux (i-1) (atom :: accu)
              in
              orN (aux width []), None
            else bvlt (bvlshr t s) (mins ~width), None
          else (* Table 7 *)
          if uneval_left (* uneval < eval *)
          then
            let mins = mins ~width in
            bvlt (bvshl mins s) (bvadd t mins), None
          else
            let rec aux i accu =
              if i = -1 then accu
              else
                let atom = bvsgt (bvshl s (bvconst_int ~width i)) t in
                aux (i-1) (atom :: accu)
            in
            orN (aux width []), None

        | A2(`YICES_BV_SMOD, _x, _s)
        | A2(`YICES_BV_SDIV, _x, _s)
        | A2(`YICES_BV_SREM, _x, _s)
          -> raise NotImplemented

        | A2(`YICES_BV_GE_ATOM, _, _)
        | A2(`YICES_EQ_TERM, _, _)
        | A2(`YICES_BV_SGE_ATOM, _, _)
          -> assert false
        | _ -> raise NotImplemented (* assert false *)


      end
    | ExtTerm.Slice(Not _)     (* Table 5 *)
    | ExtTerm.Slice(Leaf _) -> (* Should be added to Table 5 *)
      cond(), None

    | ExtTerm.Slice(And l) ->
      let s = conjuncts_disjuncts l |> bvor in
      if polarity
      then (* Table 8 *)
        if uneval_left (* uneval >= eval *)
        then (bvand [s; t] === t) ||| bvslt t (bvand [bvsub t s; s]), None
        else bvge s (bvand [t; mins ~width]), None
      else (* Table 7 *)
      if uneval_left (* uneval < eval *)
      then bvslt (bvand [bvnot(bvneg t); s]) t, None
      else bvslt t (bvand [s; maxs ~width]), None

    | ExtTerm.Slice(Or l) ->
      let s = conjuncts_disjuncts l |> bvor in
      if polarity
      then (* Table 8 *)
        if uneval_left (* uneval >= eval *)
        then bvsge s (bvand [s; t]), None
        else bvsge t (bvor [s; mins ~width]), None
      else (* Table 7 *)
      if uneval_left (* uneval < eval *)
      then bvslt (bvor [bvnot(bvsub s t); s]) t, None
      else bvslt t (bvor [s; maxs ~width]), None

    | ExtTerm.Concat _ -> raise NotImplemented
    | ExtTerm.Block _ -> assert false (* We should have abandoned ship by now *)
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

  (* let (let*\) = bind *)
  (* let (let+) a f = bind a (fun r -> return(f r)) *)

end

module Variants = ExtTerm.MTerm(Monad)

type subst = {
  body       : Term.t;      (* Term by which variable will be substituted *)
  conditions : Term.t list; (* The invertibility conditions *)
  epsilon    : bool         (* Whether this substitution involves any epsilon-term / fresh var *)
}

let pp_subst x fmt { body; conditions; epsilon = _ } =
  Format.fprintf fmt "{%a <- %a} with %a" Term.pp x Term.pp body (List.pp Term.pp) conditions

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

let rec solve :
          type a.
               Term.t ->
               pred ->
               uneval: a ExtTerm.closed ->
               eval:Term.t ->
               uneval_left:bool ->
               polarity:bool ->
               Term.t list ->
               bool ->
               Substs.not_great ->
               Substs.substs =
  fun
    (x : Term.t)               (* The variable to be eliminated *)
    (cons : pred)              (* The atom's predicate symbol *)
    ~uneval                    (* A side of the atom where x occurs *)
    ~eval                      (* The other side of the atom *)
    ~uneval_left               (* Whether the uneval side is the left-hand side of the atom *)
    ~polarity                  (* Whether the atom is negated *)
    (conditions : Term.t list) (* Invertibility conditions accumulated in recursive descent *)
    (epsilon    : bool)        (* Whether we have generated epsilon terms / new variables *)
  ->
  print 6 "@[<2>solve with var = %a, uneval = %a and eval = %a@]@,"
    Term.pp x
    ExtTerm.pp uneval
    Term.pp eval;
  let solve a = solve_aux x cons a ~eval ~uneval_left ~polarity conditions epsilon in
  let open ExtTerm in
  match uneval with
  | Bits _ as bits                   -> solve bits
  | Slice _ as slice                 -> solve slice
  | Concat _ as l                    -> solve l
  | Block{block; sign_ext; zero_ext} -> solve (Block{block; sign_ext; zero_ext})
  | T e when not(Term.equal e x)     -> let YExtTerm a = of_term e in solve a
  | T e -> (* Particular case when the 1st argument is x itself - end of recursion *)
    try
      print 6 "@[<2>uneval is the variable@]@,";
      let subst = 
        match cons with
        | `YICES_EQ_TERM when polarity -> { body = eval; conditions; epsilon }
        | _ ->
          let Term a = Term.reveal e in
          let phi, ci = getIC x cons ~uneval:(TermStruct a) ~eval ~uneval_left ~polarity in
          let y, epsilon = match ci with
            | Some y -> y, false
            | None -> let typ = Term.type_of_term x in Term.new_uninterpreted typ, true
          in
          let b   = make_lit cons ~uneval:y ~eval ~uneval_left ~polarity in
          { body = y; conditions = Term.(phi ==> b)::conditions; epsilon }
      in
      let open Substs in
      match subst.conditions, not(Term.is_free ~var:x eval) with
      | [], true  -> (fun _ -> Substs.Eliminate subst.body) (* No epsilon, no occurrence! *)
      | [], false -> (function
          | Epsilon _   -> Substs.NotGreat(NonLinear [subst.body]) 
          | NonLinear l -> Substs.NotGreat(NonLinear (subst.body::l)))
      | _::_, true -> (function (* Epsilon, no occurrence... maybe? *)
          | NonLinear [] -> Substs.NotGreat(Epsilon subst) (* OK if no other solution *)
          | solutions    -> Substs.nil solutions) (* Not OK otherwise *)
      | _::_, false      -> Substs.nil (* Epsilon with occurrence -> trash *)
    with NotImplemented  -> Substs.nil

and solve_aux : type a. Term.t -> pred -> a ExtTerm.termstruct -> eval:Term.t ->
  uneval_left:bool -> polarity:bool -> Term.t list -> bool -> Substs.not_great -> Substs.substs
  = fun (x : Term.t)
    (cons : pred)
    a
    ~eval:t
    ~uneval_left
    ~polarity
    (conditions : Term.t list)
    (epsilon    : bool) ->
    print 6 "@[<2>uneval is not the variable@]@,";
    let open ExtTerm in
    (* The recursive call is parameterised by e_i and t *)
    let treat (ExtTerm e_i) t' =
      solve x cons ~uneval:e_i ~eval:t' ~uneval_left ~polarity conditions epsilon
    in
    (* treat_nl manages the recursive calls on the non-linear problems we have *)
    let rec treat_nl = function
      | []             -> Substs.ident
      | (e_i,t')::tail -> treat e_i t' ||> treat_nl tail
    in
    let rec recurs_call accu = function
      | []              -> treat_nl accu
      | (e_i, t')::tail ->
        if Term.is_free ~var:x t'
        then recurs_call ((e_i, t')::accu) tail (* Non-linear case goes in accumulator *)
        else treat e_i t' ||> recurs_call accu tail
        (* Linear case treated immediately doesn't go further if it comes back with Eliminate *)
    in
    (* The following function tests if a bvsum l is a monomial whose coeff is 1 or -1 *)
    let test_poly = function
      | _::_::_ | [_, None] | [] -> true
      | [coeff, Some _var] ->
        match coeff with
          | true::tail when List.for_all (fun b -> b) tail -> true  (* coeff is -1 *)
          | true::tail when List.for_all (fun b -> not b) tail -> true (* coeff is 1 *)
          | _ -> false
    in
    let open Types in
    let open ExtTerm in
    match cons, a with (* We analyse the top-level predicate and its 1st argument e *)

    | _, Slice(Leaf{ extractee; indices = None }) ->
      treat (ExtTerm(T extractee)) t

    | _, (Block{ sign_ext; _ } as block) when sign_ext > 0 ->
      let Block{ block; sign_ext; zero_ext } = reduce_sign_ext block in
      treat (ExtTerm(Block{ block; sign_ext; zero_ext })) t

    | _, Block{ block; sign_ext = 0; zero_ext = 0 } ->
      treat (ExtTerm block) t

    | `YICES_EQ_TERM, Slice(Not a) ->
      treat (ExtTerm(Slice a)) (Term.BV.bvnot t)

    | `YICES_EQ_TERM, Concat blocks when polarity ->
      getInverseConcat x t blocks |> recurs_call []

    | `YICES_EQ_TERM, TermStruct(BV_Sum l) when test_poly l ->
      getInversePoly x t l |> recurs_call []

    | _ ->
      let open ExtTerm in
      let a : a termstruct = match a with
        | Concat blocks ->
          let aux block =
            if ExtTerm.is_free ~var:x block then reduce_sign_ext block
            else block
          in
          Concat(List.map aux blocks)
        | _ -> a
      in
      let fresh_var e_i =
        let typ = ExtTerm.typeof e_i in
        Term.new_uninterpreted typ
      in
      let apply : type a. a closed -> a closed Monad.t = fun e_i ->
        print 6 "@[<2>apply on e_i = %a@]@," ExtTerm.pp e_i;
        let variant x' modified =
          print 6 "@[<2>can modify@]@,";
          `Cons((modified,
                 Monad.{ variable = x' ; standing4 = ExtTerm e_i }), LazyList.empty)
        in
        let return_slice  x' = Slice(BoolStruct.Leaf(Slice.build x')) in
        let return_block  x' = return_slice x' |> return_block in
        let return_concat x' = return_block x' |> fun x -> Concat [x] in
        let variants : a closed Monad.variant LazyList.t = lazy(
          match e_i with
          | T _      when is_free ~var:x e_i -> let x' = fresh_var e_i in variant x' (T x')
          | Slice _  when is_free ~var:x e_i -> let x' = fresh_var e_i in variant x' (return_slice x')
          | Block _  when is_free ~var:x e_i -> let x' = fresh_var e_i in variant x' (return_block x')
          | Concat _ when is_free ~var:x e_i -> let x' = fresh_var e_i in variant x' (return_concat x')
          | Bits _
          | T _ | Slice _ | Block _ | Concat _ -> `Nil
        )
        in
        Monad.{ original = e_i; variants }
    in
    let variants = match a with
      | Bits _ -> Monad.return a (* We do not look for variants within bits *)
      | _      -> Variants.map { apply } a
    in
    let treat dx' Monad.{ variable = x' ; standing4 = ExtTerm e_i } = try
        print 6 "@[<2>treat on var %a standing for head %a@]@," Term.pp x' ExtTerm.pp e_i;
        print 6 "@[<2>with dx' being %a@]@," ExtTerm.pp dx';
        let phi, ci = getIC x' cons ~uneval:dx' ~eval:t ~uneval_left ~polarity in
        print 6 "@[<2>getIC gave us %a@]@," Term.pp phi;
        let y, epsilon = match ci with
          | Some y -> y, epsilon
          | None -> x', true
        in
        let dy  = Term.subst_term [x',y] (ExtTerm.to_term dx') in
        let b   = make_lit cons ~uneval:dy ~eval:t ~uneval_left ~polarity in
        solve x `YICES_EQ_TERM ~uneval:e_i ~eval:y ~uneval_left:true ~polarity:true
          (Term.(phi ==> b)::conditions) epsilon
      with NotImplemented ->
        print 6 "Not implemented@,";
         Substs.nil
    in
    let aux _nexts (dx'_raw, modif) = treat dx'_raw modif in
    let variants = LazyList.fold aux (lazy Substs.ident) variants.variants in
    Lazy.force variants


let solve_atom
    (x : Term.t)
    (atom : [`a2] Types.composite Types.termstruct)
    (polarity : bool)
  =
  let Types.A2(cons,e,t) = atom in
  print 6 "@[<2>solve_atom %a with lhs = %a and rhs = %a@]@,"
    Term.pp x
    Term.pp e
    Term.pp t;
  match cons with
  | `YICES_EQ_TERM | `YICES_ARITH_GE_ATOM | `YICES_BV_GE_ATOM | `YICES_BV_SGE_ATOM as cons
    ->
     if Term.is_free ~var:x t
     then
       if Term.is_free ~var:x e
       then
         match cons with
         | `YICES_EQ_TERM when Term.is_bitvector t || Term.is_arithmetic t ->
            print 6 "@[<2>Present on both sides, and is bv or arith@]@,";
            let uneval, eval =
              if Term.is_bitvector t
              then Term.BV.bvsub t e, Term.BV.bvconst_zero ~width:(Term.width_of_term t)
              else Term.Arith.sub t e, Term.Arith.zero()
            in
            solve x `YICES_EQ_TERM
              ~uneval:(ExtTerm.T uneval) ~eval ~uneval_left:true ~polarity
              [] false
         | _ ->
            print 6 "@[<2>Present on both sides, and is not bv or arith@]@,";
            solve x cons ~uneval:(ExtTerm.T e) ~eval:t ~uneval_left:true ~polarity
              [] false
            ||>
              solve x cons ~uneval:(ExtTerm.T t) ~eval:e ~uneval_left:false ~polarity
                [] false
       else
         (print 6 "@[<2>Present on rhs only@]@,";
          solve x cons ~uneval:(ExtTerm.T t) ~eval:e ~uneval_left:false ~polarity [] false)
     else
       (print 6 "@[<2>Present on lhs only@]@,";
        solve x cons ~uneval:(ExtTerm.T e) ~eval:t ~uneval_left:true ~polarity [] false)
  | _ ->
     Format.(fprintf stdout) "wrong predicate in solve_atom: %a" Term.pp (Term.build atom);
     assert false


let solve_lit x lit substs =
  let open Term in
  let open Types in
  let aux b t =
    if Term.equal x t then
      let body = if b then Term.true0() else Term.false0() in
      Substs.Eliminate body
    else
      match reveal t with
      | Term(A2 _ as atom) when is_free ~var:x t ->
        print 5 "@[<v2>solve_lit looks at@,%a@," Term.pp lit;
        let r = solve_atom x atom b substs in
        print 5 "@[<2>which turns into %a@]@]@," (Substs.pp_substs x) r;
        r
      | _ -> Substs.nil substs
  in
  match reveal lit with
  | Term(A1(`YICES_NOT_TERM, t')) -> aux false t'
  | _ -> aux true lit

(* type accu
 * 
 * let solve_list conjuncts old_conditions x value : (Term.t list * Term.t list) CLL.t =
 *   print 5 "@[<hv2>solve_list solves %a (with value %a) from@,%a@,@[<v>"
 *     Term.pp x
 *     Term.pp value
 *     (List.pp Term.pp) conjuncts;
 *   let rec aux treated accu = function
 *     | [] ->
 *       begin match accu with
 *         | Epsilon {body; conditions; _} ->
 *           CLL.return (
 *             Term.subst_terms [x,body] conjuncts,
 *             conditions @ Term.subst_terms [x,body] old_conditions)
 *         | _ ->
 *           CLL.return (
 *             conjuncts, old_conditions)
 *       end
 *       
 *     | lit::tail ->
 * 
 *       match solve_lit x lit accu with
 * 
 *       | Eliminate body ->
 *         print 5 "@[<2>solve_list substitutes %a by %a@]@," Term.pp x Term.pp body;
 *         CLL.return (
 *           Term.subst_terms [x,body] conjuncts,
 *           Term.subst_terms [x,body] old_conditions)
 * 
 *       | NotGreat(Epsilon _ )
 *         when List.exists (Term.is_free ~var:x) treated
 *           || List.exists (Term.is_free ~var:x) tail
 *           || List.exists (Term.is_free ~var:x) old_conditions  ->
 *         aux (lit::treated) accu tail
 * 
 *       | NotGreat substs ->
 *         aux (lit::treated) substs tail
 *   in
 *   let result = aux [] (NonLinear []) conjuncts in
 *   print 5 "@]@]@,";
 *   result *)


let solve_list conjuncts var old_epsilons : Term.t list WithEpsilons.t =
  print 5 "@[<hv2>solve_list solves %a from@,%a@,@[<v>"
    Term.pp var
    (List.pp Term.pp) conjuncts;
  let rec aux treated accu = function
    | [] ->
      begin match accu with
        | Epsilon {body; conditions; epsilon = _ } ->
          print 5 "@[<2>solve_list substitutes %a by %a@]@," Term.pp var Term.pp body;
          (* let aux conjunct =
           *   let new_conjunct = Term.subst_term [var,body] conjunct in
           *   if not (Term.equal conjunct new_conjunct)
           *   then
           *     print 5 "@[<2>Turning conjunct %a into %a@]@," Term.pp conjunct Term.pp new_conjunct
           * in
           * List.iter aux conjuncts; *)
          WithEpsilons.{
              main = Term.subst_terms [var,body] conjuncts;
              epsilons = conditions @ Term.subst_terms [var,body] old_epsilons }
        | _ ->
          (* print 5 "@[<2>solve_list does not substitute@]@,"; *)
          WithEpsilons.{
              main     = conjuncts;
              epsilons = old_epsilons }
      end
      
    | lit::tail ->
      match solve_lit var lit accu with

      | Eliminate body ->
        print 5 "@[<2>solve_list substitutes %a by %a@]@," Term.pp var Term.pp body;
        WithEpsilons.{
            main     = Term.subst_terms [var,body] conjuncts;
            epsilons = Term.subst_terms [var,body] old_epsilons }

      | NotGreat(Epsilon _ )
        when List.exists (Term.is_free ~var) treated
          || List.exists (Term.is_free ~var) tail
          || List.exists (Term.is_free ~var) old_epsilons ->
        aux (lit::treated) accu tail (* Same accu as before looking at lit; i.e. we ignore the lit *)

      | NotGreat subst ->
        aux (lit::treated) subst tail (* The accumulator has probably been updated my solve_lit *)
  in
  let result = aux [] (NonLinear []) conjuncts in
  print 5 "@]@]@,";
  result

let elim_existentials vars t =
  let open WithEpsilonsMonad in
  let conjuncts = get_conjuncts t in
  print 3 "@[<2>IC analyses %a@]@," Term.pp t;
  let+ conjuncts =
    ListWithEpsilons.fold solve_list (WithEpsilonsMonad.return conjuncts) vars
  in
  print 3 "@[<2>IC finished@]@,";
  return(Term.andN conjuncts)

let elim_existentials_init vars t = elim_existentials vars t []

let rec weaken_existential var formula =
  let open WithEpsilonsMonad in
  match get_disjuncts formula with
  | (_::_::_) as disjuncts ->
     fun epsilons ->
     let rec aux sofar = function
       | [] ->
          Term.orN sofar |> return
       | disjunct::tail ->
          let+ residual_disjunct = weaken_existential var disjunct in 
          if Term.is_free ~var residual_disjunct
          then fun _ -> WithEpsilons.{ main = Term.true0(); epsilons }
          else
            aux (residual_disjunct::sofar) tail
     in
     aux [] disjuncts epsilons
     
  | _ ->
     let conjuncts = get_conjuncts formula in
     let+ new_conjuncts = solve_list conjuncts var in
     let aux sofar conjunct =
       match get_disjuncts conjunct with
       | (_::_::_) ->
          let+ new_disjunction = weaken_existential var conjunct in
          return(new_disjunction::sofar)
       | _ ->
          if Term.is_free ~var conjunct then return sofar
          else return(conjunct::sofar)
     in
     let+ newnew_conjuncts = ListWithEpsilons.fold aux (return []) new_conjuncts in
     return(Term.andN newnew_conjuncts)
     
let weaken_existentials vars tolearn =
  ListWithEpsilons.fold
    (fun tolearn var -> weaken_existential var tolearn)
    (WithEpsilonsMonad.return tolearn)
    vars

let weaken_existentials_init vars tolearn = weaken_existentials vars tolearn []
