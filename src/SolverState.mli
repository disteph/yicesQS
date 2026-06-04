[%%import "debug.mlh"]

open Containers
open Ext

type logic = [ `NRA | `NIA | `LRA | `LIA | `BV | `Other ]

module type T = sig
    include Game.T
    val logic    : logic
    val qf_logic : string
    val context  : Context.t (* SMA/MBO context for LF(root) (Def. 8). *)
[%%if debug_mode]
    val epsilons_context : Context.t (* Debug-only MBU epsilon checks (Def. 4). *)
[%%endif]
  end

type t = (module T)

val qf_logic_of_logic : string -> string
val pp : t Format.printer
val pp_log_raw : (t * Sexplib.Sexp.t list) Format.printer
(* val pp_log     : t Format.printer *)
val create     : logic:string -> Config.t -> (module Game.T) -> t
val stop            : t -> unit
val epsilon_assert  : t -> Term.t list -> unit
val learn           : t -> Term.t List.t -> unit
val record_epsilons : t -> Term.t List.t -> unit
val free            : t -> unit
