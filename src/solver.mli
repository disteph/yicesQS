open! Containers
open Yices2.Ext
open Yices2.SMT2.WithNoErrorHandling.Ext

module Support : sig
  type t =
    | Empty
    | S of { trigger : Term.t;
             variables : Term.t list; } [@@deriving show]
  val list : t -> Term.t list
end

(* Output for the next function.
   When calling 
     solve game base_support model
   base_support is the support of model,
   and game may involve uninterpreted constants outside base_support
   - If the call outputs Unsat f, it means:
   here is a formula f whose uninterpreted constants are in base_support,
   that is satisfied by model, and that is inconsistent with game.
   - If the call outputs Sat l, it means:
   each formula f in the list of formulae f has its uninterpreted constants in base_support,
   is satisfied by model, and implies game.
*)

type answer =
  | Unsat of Term.t
  | Sat of Term.t list
[@@deriving show { with_path = false }]

exception BadInterpolant of SolverState.t * Level.t * Term.t
exception BadUnder       of SolverState.t * Level.t * Term.t
exception FromYicesException of SolverState.t * Level.t * Types.error_report * string
exception WrongAnswer    of SolverState.t * answer

(* val solve : SolverState.t -> Level.t -> Model.t -> Support.t -> answer*SolverState.t *)

val treat : string -> SolverState.t list
