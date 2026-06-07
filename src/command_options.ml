open! Containers

let verbosity = ref 0
let timeout : float option ref = ref None
let underapprox = ref 1
let bv_invert = ref true
type mode = [`CDCLT of [`Eq | `Ineq] | `MCSAT ]
let ysolver : mode option ref = ref None
let yseed = ref 0
let switch_after = ref 5.0
let delegate : string option ref = ref None
let wide_projection : int option ref = ref None

type slice_config = {
  mode: mode option;
  seed: int;
  delegate: string option;
  wide_projection: int option;
  underapprox: int;
  bv_invert: bool;
}

let make_slice_config ?(mode = !ysolver) ?(seed = !yseed) () = {
  mode;
  seed;
  delegate = !delegate;
  wide_projection = !wide_projection;
  underapprox = !underapprox;
  bv_invert = !bv_invert;
}

let apply_slice_config config =
  ysolver := config.mode;
  yseed := config.seed;
  delegate := config.delegate;
  wide_projection := config.wide_projection;
  underapprox := config.underapprox;
  bv_invert := config.bv_invert

let events : (float * slice_config) list ref = ref []

let create_pool mode delay n =
  for i = 0 to n-1 do
    events := (delay, make_slice_config ~mode ~seed:(i+1) ()) :: !events
  done
