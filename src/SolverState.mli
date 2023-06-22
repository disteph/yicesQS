[%%import "debug.mlh"]

open Containers
open Yices2.Ext.WithNoErrorHandling
open Utils

module type T = sig
    include Game.T
    val logic    : logic
    val qf_logic : string
    val context  : Context.t
[%%if debug_mode]
    val epsilons_context : Context.t
[%%endif]
  end

type t = (module T)

val pp : t Format.printer
val pp_log_raw : (t * Sexplib.Sexp.t list) Format.printer
(* val pp_log     : t Format.printer *)
val create          : logic:logic -> qf_logic:string -> Config.t -> (module Game.T) -> t
val epsilon_assert  : t -> Term.t list -> unit
val learn           : t -> Term.t List.t -> unit
val record_epsilons : t -> Term.t List.t -> unit
val free            : t -> unit
