open! Containers

let verbosity = ref 0
let underapprox = ref 1
let bv_invert = ref true
let ysolver : [`CDCLT | `MCSAT ] option ref = ref None
let cdclT_mcsat = ref 0.0
