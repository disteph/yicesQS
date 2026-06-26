open Containers
open Ext

module type T = sig
  val ground : Term.t (* root.F with proxies (Def. 2), part of LF(root) (Def. 8). *)
  val existentials : Term.t Seq.t (* Conjuncts encoding p => LF(child) (Def. 8). *)
  val universals : Term.t Seq.t (* Selector constraints enforcing LF(child) (Def. 8). *)
  val top_level : Level.t
end

type t = (module T)

val pp : t Format.printer

exception CannotTreat of Term.t

val process : Config.t -> global_vars:Term.t list -> Term.t -> t

val process_level :
  Config.t ->
  rigid:Term.t list ->
  intro:Term.t list ->
  Term.t ->
  t
