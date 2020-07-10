open Containers
open Sexplib
open Type
open Yices2_high
open Yices2_ext_bindings
open Yices2_SMT2
open Command_options

let print i fs = Format.((if !verbosity >= i then fprintf else ifprintf) stdout) fs

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

type pred = [ `YICES_BV_GE_ATOM
            | `YICES_BV_SGE_ATOM
            | `YICES_EQ_TERM ]

exception NotImplemented

let getIC (var : Term.t) (lit : [`a2] Types.composite Types.termstruct) (polarity : bool) : Term.t =
  raise NotImplemented

exception NotApplicable

(* Solves concat(...,x,...) = t) in x *)

let getInverseConcat (x : Term.t) (t : Term.t) (bits : Term.t list) =
  let concat = bvarray bits in
  let not_free_bit = function
    | Extract{ extractee } -> not(fv x extractee)
    | Bits l -> List.for_all (fun t -> not(fv x t)) l
  in
  let width y = Type.bvsize(Term.type_of_term y) in
  let rec aux start_index = function
    | [] -> None (* x did not appear in a nice place *)

    | Bits l:: tail                      when List.for_all (fun t -> not(fv x t)) l ->
      aux (start_index + List.length l) tail

    | Extract{ extractee; lo; hi }::tail when not(fv x extractee) ->
      aux (start_index + hi - lo) tail

    | Extract{ extractee; lo; hi; polarity }::tail
      when lo = 0 && hi = width extractee - 1 && List.for_all not_free_bit tail ->
      let t'  = Term.BV.bvextract t start_index (hi + 1) in
      Some(extractee, t')

    | _ -> None
  in
  aux 0 concat

(* Solves (P[x] = t) in x, for bv-polynomial P expressed as list l,
   Works if x only appears in P as monomial x or -x, otherwise raises exception *)

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
    | [] -> None (* could not find a monomial with variable x and coefficient 1 or -1 *)
    | (bl,Some e_i) as monomial::to_treat when fv x e_i ->
      begin match bl with
        | true::tail when List.for_all (fun b -> b) tail ->  (* coeff is -1 *)
          Some(e_i, Term.BV.bvneg(rebuild treated to_treat))
        | true::tail when List.for_all (fun b -> not b) tail -> (* coeff is 1 *)
          Some(e_i, rebuild treated to_treat)
        | _ -> aux (monomial::treated) to_treat
      end
    | monomial ::to_treat -> aux (monomial::treated) to_treat

  in
  aux [] l

module Monad = struct
  type 'a t = 'a * (Term.t * Term.t * bool) option
  let return a = a, None
  let bind (a,o) f = match f a, o with
    | r, None -> r
    | (a', Some _), Some(x',e_i,_) -> a', Some(x',e_i,false)
    | (a', None),   Some v -> a', Some v
end

open MTerm(Monad)

(* Fig 1 *)

let rec solve
    (x : Term.t)
    (atom : [`a2] Types.composite Types.termstruct)
    (polarity : bool)
    (epsilons : (Term.t * Term.t) list)
  =
  let Types.A2(cons,e,t) = atom in
  if fv x t
  then if fv x e then None
    else solve x Types.(A2(cons,t,e)) polarity epsilons
  else
  if Term.equal e x then
    match cons with
    | `YICES_EQ_TERM when polarity -> Some(Result.Ok t, epsilons)
    | _ ->
      let phi = getIC x atom polarity in
      let typ = Term.type_of_term x in
      let y = Term.new_variable typ in
      let b = Term.build Types.(A2(cons,y,t)) in
      let b = if polarity then b else Term.not1 b in
      Some(Result.Error y, (y,Term.(phi ==> b))::epsilons)
  else
    let recurs_call = function
      | None                     -> None (* Failed to invert (e.g., poly coeff is not 1 or -1) *)
      | Some(_, t') when fv x t' -> None (* More than 1 occurrence of x *)
      | Some(e_i, t')            -> solve x Types.(A2(cons, e_i, t')) polarity epsilons
    in
    let Term a = Term.reveal e in
    match cons, a with
    | `YICES_EQ_TERM, Types.(BV_Sum l) ->
      getInversePoly x t l |> recurs_call
    | `YICES_EQ_TERM, Types.(Astar(`YICES_BV_ARRAY, bits)) ->
      getInverseConcat x t bits |> recurs_call
    | _ ->
      let aux e_i =
        if fv x e_i then
          let typ = Term.type_of_term e_i in
          let x'  = Term.new_uninterpreted typ in
          x', Some(x', e_i, true)
        else
          e_i, None
      in
      match map aux a with
      | _, None                      (* Variable doesn't occur *)
      | _, Some(_, _, false) -> None (* Variable occurs more than once *)
      | dx'_raw, Some(x', e_i, true) ->
        let dx' = Term.build dx'_raw in
        let phi = getIC x' Types.(A2(cons,dx',t)) polarity in
        let typ = Term.type_of_term x' in
        let y   = Term.new_variable typ in
        let dy  = Term.subst_term [x',y] dx' in
        let b   = Term.build Types.(A2(cons,dy,t)) in
        let b   = if polarity then b else Term.not1 b in
        solve x Types.(A2(`YICES_EQ_TERM, e_i, y)) true ((y,Term.(phi ==> b))::epsilons)

let solve_lit x lit =
  let open Term in
  let open Types in
  let aux b t = 
    match reveal t with
    | Term(A2 _ as atom) when fv x t ->
      solve x atom b []
    | _ -> None
  in
  match reveal lit with
  | Term(A1(`YICES_NOT_TERM, t')) -> aux false t'
  | _ -> aux true lit
    
let solve_list x l =
  let rec aux accu = function
    | [] -> None
    | lit::tail -> try
        match solve_lit x lit with
        | Some(Result.Ok t, []) ->
          print 1 "@[<2>IC eliminated %a as %a@]@," Term.pp x Term.pp t;
          let rest = List.rev_append accu tail in
          Some(Term.subst_terms [x,t] rest)
        | _ -> aux (lit::accu) tail 
      with
      | NotImplemented -> aux (lit::accu) tail
  in
  aux [] l

let solve_all vars t =
  let conjuncts = 
    let open Term in
    let open Types in
    match reveal t with
    | Term(A1(`YICES_NOT_TERM, t')) ->
      begin
        match reveal t with
        | Term(Astar(`YICES_OR_TERM,l)) -> l
        | _ -> [t]
      end
    | _ -> [t]
  in
  let aux (l,remains) x =
    match solve_list x l with
    | Some l -> l, remains
    | None -> l,(x::remains)
  in
  let l,remains = List.fold_left aux (conjuncts,[]) vars
  in Term.andN l, remains
