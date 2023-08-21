[%%import "debug.mlh"]

open Containers

open Ext

[%%if debug_mode]
let print trace = Tracing.print Format.stdout trace
[%%else]
(* let print trace = Tracing.iprint Format.stdout trace *)
let print _trace _i fs = Format.ifprintf Format.stdout fs
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
