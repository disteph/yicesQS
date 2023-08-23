open! Containers

let verbosity = ref 0
let underapprox = ref 1
let rounds = ref 1
let ysolver : [`CDCLT | `MCSAT ] option ref = ref None
