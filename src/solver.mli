[%%import "debug.mlh"]

open Containers
open Yices2.Ext_bindings

module Level : sig
  type t = {
    id : int;
    ground : Term.t;
    rigid : Term.t list;
    newvars : Term.t list;
    foralls : forall list;
  }
  and forall = {
    name : Term.t;
    selector : Term.t;
    selector_context : Context.t;
    sublevel : t;
  }
  val pp         : t Format.printer
  val pp_forall  : forall List.printer
  val pp_foralls : forall list Format.printer
  val free        : t -> unit
  val free_forall : forall -> unit
end

module Game : sig
  module type T =
    sig
      val ground : Term.t
      val existentials : Term.t list
      val universals : Term.t list
      val top_level : Level.t
    end
  type t = (module T)
  type game = t
  val pp : t Format.printer
  type state = {
    newvars : Term.t list;
    foralls : Level.forall list;
    existentials : Term.t list;
    universals : Term.t list;
  }
  module StateMonad :
    sig
      type 'a t = state -> 'a * state
      val return   : 'a -> 'a t
      val bind     : 'a t -> ('a -> 'b t) -> 'b t
      val ( let+ ) : 'a t -> ('a -> 'b t) -> 'b t
    end
  module MList :
    sig
      val fold :
        ('a -> 'b -> 'a StateMonad.t) ->
        'a StateMonad.t -> 'b list -> 'a StateMonad.t
      val map : ('a -> 'b StateMonad.t) -> 'a list -> 'b list StateMonad.t
    end
  val map :
    (Types.term_t -> Types.term_t StateMonad.t) ->
    'a Types.termstruct ->
    'a Types.termstruct StateMonad.t
  val var_add : Term.t -> 'a -> state -> 'a * state
  val bound_counter : int ref
  val fresh_bound : unit -> string
  val fresh :
    Term.t list ->
    Yices2.Low.Types.term_t list ->
    Yices2.Low.Types.term_t ->
    Term.t * Term.t list *
    Term.t list
  exception CannotTreat of Term.t
  val counter : int ref
  val process :
    Config.t ->
    rigidintro:Term.t list ->
    rigid:Term.t list ->
    intro:Term.t list -> Yices2.Low.Types.term_t -> game
end

module SolverState : sig
  module type T =
    sig
      val ground : Term.t
      val top_level : Level.t
      val universals : Term.t list
      val existentials : Term.t list
      val context : Context.t
[%%if debug_mode]
      val epsilons_context : Context.t
[%%endif]
    end
  type t = (module T)
  val pp : t Format.printer
  val pp_log_raw : (t * Sexplib.Sexp.t list) Format.printer
  val pp_log     : t Format.printer
  val create : Config.t -> (module Game.T) -> t
  val epsilon_assert : t -> Term.t list -> unit
  val learn : t -> Term.t List.t -> unit
  val record_epsilons : t -> Term.t List.t -> unit
  val free : t -> unit
end

module Support : sig
  type t =
    | Empty
    | S of { trigger : Term.t;
             variables : Term.t list; } [@@deriving show]
  val list : t -> Term.t list
end

(* Supported models *)
module SModel : sig

  type t = { support : Term.t list;
             model   : Model.t }

  val pp : t Format.printer
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

val solve : SolverState.t -> Level.t -> Model.t -> Support.t -> answer

val treat : string -> SolverState.t list
