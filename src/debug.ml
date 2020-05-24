open Containers
    
[%%import "debug.mlh"]

[%%if debug_mode]
let print fs = Format.(fprintf stdout) fs
[%%else]
let print fs = Format.(ifprintf stdout) fs
[%%endif]
