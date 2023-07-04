open! Containers

open Yices2.Ext.WithNoErrorHandling

type t = {
    id : int;
    ground  : Term.t;      (* Called Look-ahead Formula (LF) in the 2023 QSMA paper *)
    rigid   : Term.t list; (* Eigenvariables that will systematically be set by ancestor games *)
    newvars : Term.t list; (* Eigenvariables to be set by this game, disjoint from above *)
    (* If uninterpreted constant u abstracts away formula (\forall x1...xn neg A), then *)
    foralls : forall Seq.t; (* ... (\forall x1..x2 neg A) is turned into an adversarial
                                    game/level g and (g + some meta-info) goes into that list;
                                    these games are the children game of the current game *)
  }
(* The notion of subgame/sublevel with meta-information *)
and forall = {
    name : Term.t;     (* A Boolean proxy variable that stands for (\forall x1..x2 neg A) *)
    selector : Term.t; (* making that selector true enforces the constraints at that level *)
    selector_context : Context.t; (* not the main Yices context for QSMA *)
    sublevel : t
  }

val pp         : t Format.printer
val pp_forall  : forall Format.printer
val pp_foralls : forall Seq.t Format.printer

val free : t -> unit

(* val free_forall : forall -> unit *)
