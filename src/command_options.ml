[%%import "debug.mlh"]

open Containers

[%%if debug_mode]
let print tag i fs = Tracing.print Format.stdout tag i fs
[%%else]
let print tag i fs = Tracing.iprint Format.stdout tag i fs
[%%endif]

