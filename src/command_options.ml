open! Containers

let verbosity = ref 0
let timeout : float option ref = ref None
let underapprox = ref 20
let bv_invert = ref true
type mode = [`CDCLT of [`Eq | `Ineq] | `MCSAT ]
let ysolver : mode option ref = ref None
let yseed = ref 0
let switch_after = ref 5.0
let delegate : string option ref = ref None
let wide_projection : int option ref = ref None
let nia_unit_box_mbu = ref true
let nia_unit_box_max_elims = ref 4
let nia_unit_box_max_nodes = ref 5000
let nia_unit_box_timeout = ref 5.0

type slice_config = {
  mode: mode option;
  seed: int;
  delegate: string option;
  wide_projection: int option;
  underapprox: int;
  bv_invert: bool;
  nia_unit_box_mbu: bool;
  nia_unit_box_max_elims: int;
  nia_unit_box_max_nodes: int;
  nia_unit_box_timeout: float;
}

let make_slice_config ?(mode = !ysolver) ?(seed = !yseed) ?(delegate = !delegate) () = {
  mode;
  seed;
  delegate;
  wide_projection = !wide_projection;
  underapprox = !underapprox;
  bv_invert = !bv_invert;
  nia_unit_box_mbu = !nia_unit_box_mbu;
  nia_unit_box_max_elims = !nia_unit_box_max_elims;
  nia_unit_box_max_nodes = !nia_unit_box_max_nodes;
  nia_unit_box_timeout = !nia_unit_box_timeout;
}

let apply_slice_config config =
  ysolver := config.mode;
  yseed := config.seed;
  delegate := config.delegate;
  wide_projection := config.wide_projection;
  underapprox := config.underapprox;
  bv_invert := config.bv_invert;
  nia_unit_box_mbu := config.nia_unit_box_mbu;
  nia_unit_box_max_elims := config.nia_unit_box_max_elims;
  nia_unit_box_max_nodes := config.nia_unit_box_max_nodes;
  nia_unit_box_timeout := config.nia_unit_box_timeout

let events : (float * slice_config) list ref = ref []

let create_pool ?delegate mode delay n =
  for i = 0 to n-1 do
    events := (delay, make_slice_config ~mode ~seed:(i+1) ?delegate ()) :: !events
  done
