[%%import "debug.mlh"]

open Containers

open Sexplib
open Type
open Yices2.Ext
open WithNoErrorHandling

open Utils

type logic = [ `NRA | `NIA | `LRA | `LIA | `BV | `Other ]
   
module type T = sig
  include Game.T
  val logic             : logic
  val qf_logic          : string
  val context           : Context.t (* Main context for the solver *)
  [%%if debug_mode]
  val epsilons_context  : Context.t (* context with only epsilon term constraints at level 0 *)
[%%endif]
(* val learnt : Term.t list ref *)
end

type t = (module T)

let pp fmt (module T:T) =
  Format.fprintf fmt "@[<v>\
                      @[%a@]\
                      @]"
    Game.pp (module T)

let pp_log_raw fmt ((module T:T),log) =
  let open T in
  let intro sofar t =
    let typ = Term.type_of_term t in
    let sexp = List[Atom "declare-fun"; Term.to_sexp t; List[]; Type.to_sexp typ] in
    sexp::sofar
  in
  let log = List.fold_left intro log top_level.newvars in
  let log = List.fold_left intro log top_level.rigid in
  let sl     = List[Atom "set-logic";  Atom qf_logic] in
  let option = List[Atom "set-option"; Atom ":produce-unsat-model-interpolants"; Atom "true"] in
  Format.fprintf fmt "@[<v>%a@]" (List.pp ~pp_sep:pp_space pp_sexp) (option::sl::log)

let create ~logic config (module G : Game.T) =
  let qf_logic =
    if String.length logic > 3 && String.equal (String.sub logic 0 3) "QF_"
    then logic
    else "QF_"^logic
  in
  let logic = match logic with
    | "NRA" | "QF_NRA" -> `NRA
    | "NIA" | "QF_NIA" -> `NIA
    | "LRA" | "QF_LRA" -> `LRA
    | "LIA" | "QF_LIA" -> `LIA
    | "BV"  | "QF_BV"  -> `BV
    | _     -> print_endline("Unknown logic: "^logic); `BV 
  in
  (module struct
     include G
     let logic = logic
     let qf_logic = qf_logic
[%%if debug_mode]
     let epsilons_context = Context.malloc ~config ()
[%%endif]
     let context          = Context.malloc ~config ()
     let () = Context.assert_formula context ground
     let () = Context.assert_formulas context (Seq.to_list existentials)
     let () = Context.assert_formulas context (Seq.to_list universals)
                                      (* let learnt = ref [] *)
   end : T)

[%%if debug_mode]
let epsilon_assert (module S : T) = Context.assert_formulas S.epsilons_context
[%%else]
let epsilon_assert _ _ = ()
[%%endif]

let learn (module S : T) lemmas =
  (* learnt := List.append lemma !S.learnt; *)
  print 4 "@[<2>Learning %a@]@," (List.pp Term.pp) lemmas;
  Context.assert_formulas S.context lemmas

let record_epsilons ((module S : T) as state) epsilons =
  print 3 "@[<v2>Recording epsilons @[<v2>  %a@]@]@,"
    (List.pp Term.pp) epsilons;
  epsilon_assert state epsilons;
  learn state epsilons

let free (module G : T) =
  Context.free G.context;
  Level.free G.top_level
    
