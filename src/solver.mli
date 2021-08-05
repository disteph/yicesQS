[%%import "debug.mlh"]

open Containers
open Yices2.Ext_bindings

exception FromYicesException of Types.error_report * string

val treat : string -> unit
