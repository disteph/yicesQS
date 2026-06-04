open! Containers

let verbosity = ref 0
let timeout : float option ref = ref None
let underapprox = ref 1
let bv_invert = ref true
type mode = [`CDCLT of [`Eq | `Ineq] | `MCSAT ]
let ysolver : mode option ref = ref None
let yseed = ref 0
let switch_after = ref 5.0
let events : (float * mode option * int) list ref = ref []
let delegate : string option ref = ref None

let create_pool mode delay n =
  for i = 0 to n-1 do
    events := (delay, mode, i+1)::!events (* After delay seconds, switch to mode with seed i *)
  done
