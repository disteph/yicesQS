open Containers
open Yices2.Ext_bindings

module type T = sig
  val ground : Term.t
  val existentials : Term.t list
  val universals : Term.t list
  val top_level : Level.t
end

type t = (module T)

val pp : t Format.printer

exception CannotTreat of Term.t

val process : Config.t -> global_vars:Term.t list -> Term.t -> t
