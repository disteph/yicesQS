[%%import "debug.mlh"]

open Containers

open Ext
       
[%%if debug_mode]
open Command_options
let print i fs = Format.((if !verbosity >= i then fprintf else ifprintf) stdout) fs
[%%else]
let print _ fs = Format.(ifprintf stdout) fs
[%%endif]

let pp_space fmt () = Format.fprintf fmt " @,"

module CLL = CLazyList.Make(struct include Int let zero = 0 end)

module WithEpsilons = struct
  
  type 'a t = {
      main     : 'a;
      epsilons : Term.t list
    }

  let return main = { main; epsilons = [] }

end
