[%%import "debug.mlh"]

(* Binding configuration: choose Yices error handling for SMA/MBO calls
   (Sec. 4 functions) used throughout the OptiQSMA implementation. *)

open Yices2.Ext

module Types = Types

[%%if debug_mode]

module ErrorHandling = ExceptionsErrorHandling
include WithExceptionsErrorHandling

[%%else]

module ErrorHandling = NoErrorHandling
include WithNoErrorHandling

[%%endif]
