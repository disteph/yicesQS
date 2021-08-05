open Containers
open Yices2.High
open Yices2.Ext_bindings
open Yices2.SMT2

open Solver
open Command_options

open Arg

let args = ref []
let description = "FBF on DIMACS"

let options = [
  ("-verb",     Int(fun i -> verbosity := i), "Verbosity level (default is 0)");
];;

Arg.parse options (fun a->args := a::!args) description;;

match !args with
| [filename] ->
     Format.(fprintf stdout) "@[<v>";
     treat filename;
     Format.(fprintf stdout) "@]%!";
| [] -> failwith "Too few arguments in the command"
| _ -> failwith "Too many arguments in the command";;


