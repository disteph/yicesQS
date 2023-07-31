[%%import "debug.mlh"]

open Yices2.Ext

module Types = Types

[%%if debug_mode]

module ErrorHandling = ExceptionsErrorHandling
include WithExceptionsErrorHandling

[%%else]

module ErrorHandling = NoErrorHandling
include WithNoErrorHandling

[%%endif]
