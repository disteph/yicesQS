open! Containers

open Yices2.SMT2.WithNoErrorHandling.Ext

type t = {
    id : int;
    ground  : Term.t;
    rigid   : Term.t list; (* Eigenvariables that will systematically be set by ancestor games *)
    newvars : Term.t list; (* Eigenvariables to be set by this game, disjoint from above *)
    (* If uninterpreted constant u abstracts away formula (\forall x1...xn neg A), then *)
    foralls : forall list; (* ... (\forall x1..x2 neg A) is turned into an adversarial
                                    game g and (u,g) goes into that list;
                                    these games are the children game of the current game *)
  }
and forall = {
    name : Term.t;
    selector : Term.t;
    selector_context : Context.t;
    sublevel : t
  }

val pp         : t Format.printer
val pp_forall  : forall Format.printer
val pp_foralls : forall list Format.printer

val free : t -> unit

(* val free_forall : forall -> unit *)
