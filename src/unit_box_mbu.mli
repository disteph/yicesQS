open! Containers

open Ext

type skip_reason =
  | Disabled
  | NoIntegerEliminables
  | LinearIntegerExplanation
  | TooManyEliminables of int
  | FormulaTooLarge of int
  | UnsupportedConstruct of string
  | MissingModelValue of Term.t
  | IllTypedLiftedFormula of Term.t

type build_result = {
  rigid_vars : Term.t list;
  intro_vars : Term.t list;
  body : Term.t;
  back_subst : (Term.t * Term.t) list;
  temp_vars : Term.t list;
}

val pp_skip_reason : skip_reason Format.printer

val build :
  SModel.t ->
  true_of_model:Term.t ->
  rigid_vars:Term.t list ->
  newvars:Term.t list ->
  (build_result, skip_reason) result
