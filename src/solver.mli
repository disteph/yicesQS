[%%import "debug.mlh"]

open Containers
open Yices2.Ext_bindings

(* exception BadInterpolant of SolverState.t * Level.t * Term.t
 * exception BadUnder       of SolverState.t * Level.t * Term.t
 * exception FromYicesException of SolverState.t * Level.t * Types.error_report * string
 * exception WrongAnswer    of SolverState.t * answer *)

val treat : string -> unit
