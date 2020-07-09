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
end

open MTerm(OptionMonad)

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

type pred = [ `YICES_BV_GE_ATOM
            | `YICES_BV_SGE_ATOM
            | `YICES_EQ_TERM ]


exception NotImplemented

let getIC (var : Term.t) (lit : [`a2] Types.composite Types.termstruct) (polarity : bool) : Term.t =
  raise NotImplemented

exception NotApplicable

(* Solves (P[x] = t) in x, for bv-polynomial P expressed as list l,
   Works if x only appears in P as monomial x or -x, otherwise raises exception *)

let getInverse (x : Term.t) (l : (bool list * Term.t option) list) (t : Term.t) : Term.t =

  (* First, we collect the coefficient of x in P (1 or -1),
     together with the rest of the polynomial when we have removed x's monomial.
     We fold the following function over the polynomial expressed as l. *)

  let aux (sofar,l) (bl,var) =
    let b = match var with
      | Some var when fv x var ->
        if not (Term.equal x var)
        then raise NotApplicable (* monomial features x but monomial variable is not x *)
        else true
      | _ -> false
    in
    if b then
      match sofar, bl with
      | None, true::tail when List.for_all (fun b -> b) tail -> Some true, l (* coeff is -1 *)
      | None, true::tail when List.for_all (fun b -> not b) tail -> Some false, l (* coeff is 1 *)
      | _ -> raise NotApplicable
    else
      sofar, (bl, var)::l
  in
  match List.fold_left aux (None,[]) l with
  | Some coeff, rest ->
    let rest = Term.build(Types.BV_Sum rest) in
    if coeff then Term.BV.bvneg rest else rest
  | _ -> raise NotApplicable (* x did not appear in polynomial *)
  


module Monad = struct
  type 'a t = 'a * (Term.t * Term.t) option
  let return a = a, None
  let bind (a,o) f = match f a, o with
    | r, None -> r
    | (r, None), Some v -> r, Some v
    | _ -> raise NotApplicable
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
  if fv x t && not(fv x e)
  then solve x Types.(A2(cons,t,e)) polarity epsilons
  else
  if Term.equal e x then
    match cons with
    | `YICES_EQ_TERM when polarity -> Result.Ok t, epsilons
    | _ ->
      let phi = getIC x atom polarity in
      let typ = Term.type_of_term x in
      let y = Term.new_variable typ in
      let b = Term.build Types.(A2(cons,y,t)) in
      let b = if polarity then b else Term.not1 b in
      Result.Error y, (y,Term.(phi ==> b))::epsilons
  else
    let aux e_i =
      if fv x e_i then
        let typ = Term.type_of_term e_i in
        let x' = Term.new_variable typ in
        x', Some(x', e_i)
      else
        e_i, None
    in
    let Term a = Term.reveal e in
    let dx'_raw, dx', x', e_i =
      match map aux a with
      | dx', Some(x',e_i) -> dx', Term.build dx', x', e_i
      | _ -> raise NotApplicable
    in
    match cons, dx'_raw with
    | `YICES_EQ_TERM, Types.(BV_Sum l) ->
      let t' = getInverse x' l t in
      solve x Types.(A2(cons, e_i, t')) polarity epsilons
    | _ ->
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
    | Term(A2 _ as atom) -> solve x atom b []
    | _ -> raise NotApplicable
  in
  match reveal lit with
  | Term(A1(`YICES_NOT_TERM, t')) -> aux false t'
  | _ -> aux true lit
    
let solve_list x l =
  let rec aux accu = function
    | [] -> None
    | lit::tail -> try
        begin match solve_lit x lit with
          | Result.Ok t, [] ->
            print 1 "@[<2>IC eliminated %a as %a@]@," Term.pp x Term.pp t;
            let rest = List.rev_append accu tail in
            Some(Term.subst_terms [x,t] rest)
          | _ -> aux (lit::accu) tail 
        end
      with
      | NotApplicable | NotImplemented -> aux (lit::accu) tail
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
