open Containers
open Yices2.Ext.WithNoErrorHandling

module type T = sig
  val ground : Term.t
  val existentials : Term.t Seq.t
  val universals : Term.t Seq.t
  val top_level : Level.t
end

type t = (module T)

val pp : t Format.printer

exception CannotTreat of Term.t

val process : Config.t -> global_vars:Term.t list -> Term.t -> t
