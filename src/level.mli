open! Containers

open Ext

type t = {
    id : int;
    ground  : Term.t;      (* Look-ahead formula LF(n) (Def. 8). *)
    rigid   : Term.t list; (* Rigid(n) variables (Def. 1/3), fixed by ancestors. *)
    newvars : Term.t list; (* Local variables Var(n) \ Rigid(n) (Def. 1/3). *)
    (* If a proxy variable abstracts a forall formula, we create a child sublevel. *)
    foralls : forall Seq.t; (* Children nodes b with proxy b.p (Def. 1/2). *)
  }
(* The notion of subgame/sublevel with meta-information *)
and forall = {
    name : Term.t;     (* Boolean proxy b.p for the quantified subformula (Def. 1/2). *)
    selector : Term.t; (* Internal selector used to assert LF(b) (Def. 8). *)
    selector_context : Context.t; (* Separate context used for selector-based SMA. *)
    sublevel : t
  }

val pp         : t Format.printer
val pp_forall  : forall Format.printer
val pp_foralls : forall Seq.t Format.printer

val free : t -> unit

(* val free_forall : forall -> unit *)
