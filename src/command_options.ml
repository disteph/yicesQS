[%%import "debug.mlh"]

open Containers

let verbosity = ref 0
let filedump : string option ref  = ref None
let underapprox = ref 1

[%%if debug_mode]
let print i fs = Format.((if !verbosity >= i then fprintf else ifprintf) stdout) fs
[%%else]
let print _ fs = Format.(ifprintf stdout) fs
[%%endif]

