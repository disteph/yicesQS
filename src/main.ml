open Containers
open Yices2.High
open Yices2.Ext_bindings
open Yices2.SMT2

open Solver
open Command_options

let () = assert(Global.has_mcsat())

let if_filedump f = 
  match !filedump with
  | None -> ()
  | Some prefix -> f prefix
  
(** Copy the input file input.smt2 to file (!filedump)/subdir/input.smt2 *)
let copy_input filename subdir prefix =
  let newfile = Filename.(filename |> basename |> concat subdir |> concat prefix) in
  CCIO.(
    with_in filename
      (fun ic ->
        let chunks = read_chunks_gen ic in
        with_out ~flags:[Open_binary; Open_creat] newfile
          (fun oc ->
            write_gen oc chunks
          )
      )
  )

(* let print_log filename subdir ?(suffix="trace") state log prefix =
 *   let newfile = Filename.(filename |> remove_extension |> basename) in
 *   let newfile = newfile^"."^suffix^".smt2" in
 *   let newfile = Filename.(newfile |> concat subdir |> concat prefix) in
 *   Format.(fprintf stdout) "%s@,%!" ("Writing "^suffix^" to "^newfile);
 *   Format.to_file newfile "@[<v>%a@]" SolverState.pp_log_raw (state,log)
 * 
 * (\** Export the trace of the interactive use of Yices as an SMTLib2 file.
 *     Running Yices on it should roughly emulate what happened through the API.
 *     Emphasis on "roughly". In
 *       print_trace "input.smt2" "subdir" state
 *     writes the trace in file (!filedump)/subdir/input.trace.smt2 *\)
 * let print_trace filename subdir ((module S : SolverState.T) as state) prefix =
 *   print_log filename subdir state (Context.to_sexp S.context) prefix
 * 
 * (\** Same as above but with an assertion instead of the whole trace *\)
 * let print_trace_with_assert filename subdir ?suffix ((module S : SolverState.T) as state) assertion prefix =
 *   let rec aux = function
 *     | [check_with_model;_] -> [check_with_model]
 *     | _::tail -> aux tail
 *     | _ -> assert false
 *   in
 *   let log = Context.to_sexp S.context |> aux in
 *   let log = Action.(AssertFormula assertion |> to_sexp log) in 
 *   print_log filename subdir ?suffix state log prefix
 * 
 * let copyNtrace filename subdir state prefix =
 *   copy_input  filename subdir prefix;
 *   print_trace filename subdir state prefix *)

open Arg

let args = ref []
let description = "QE in Yices"

let options = [
  ("-verb",     Int(fun i -> verbosity := i), "Verbosity level (default is 0)");
  ("-under",    Int(fun u -> underapprox := u), "Desired number of underapproximations in SAT answers (default is 1)");
  ("-filedump", String(fun s -> filedump := Some s), "Dump file in case of error: if so, give path prefix (default is no file dump)");
];;

Arg.parse options (fun a->args := a::!args) description;;

match !args with
| [filename] ->
  (try
     Format.(fprintf stdout) "@[<v>";
     let () = treat filename in
     Format.(fprintf stdout) "@]%!";
     (* let subdir = "good" in
      * copy_input filename subdir |> if_filedump;
      * let traces prefix =
      *   List.iter (fun state -> print_trace filename subdir state prefix) (List.rev states)
      * in
      * traces |> if_filedump; *)
   with

   (* | WrongAnswer(state, answer) as exc ->
    *   copyNtrace filename "wrong" state |> if_filedump;
    *   Format.(fprintf stdout) "@[Wrong answer!: %a@]@]%!" pp_answer answer;
    *   raise exc
    * 
    * | FromYicesException(state, level, report, bcktrace) as exc ->
    *   copyNtrace filename "yices_exc" state |> if_filedump;
    *   Format.(fprintf stdout) "@[Yices error at level %i: @[%s@]@]@,"
    *     level.id
    *     (ErrorPrint.string());
    *   Format.(fprintf stdout) "@[Error report:@,@[<v2>  %a@]@,"
    *     Types.pp_error_report report;
    *   Format.(fprintf stdout) "@[Backtrace is:@,@[%s@]@]@]%!" bcktrace;
    *   raise exc *)

   | Yices_SMT2_exception s as exc ->
     copy_input filename "SMT_exc" |> if_filedump;
     Format.(fprintf stdout) "@[SMT2 error: %s@]@," s;
     Format.(fprintf stdout) "Backtrace is:@,@[%s@]@]%!" (Printexc.get_backtrace());
     raise exc

   | ExceptionsErrorHandling.YicesException(_,report) as exc ->
      let bcktrace = Printexc.get_backtrace() in
      Format.(fprintf stdout) "@[Yices error: @[%s@]@]@," (ErrorPrint.string());
      Format.(fprintf stdout) "@[Error report:@,@[<v2>  %a@]@,"
        Types.pp_error_report report;
      Format.(fprintf stdout) "@[Backtrace is:@,@[%s@]@]@]%!" bcktrace;
      raise exc

  )
| [] -> failwith "Too few arguments in the command"
| _ -> failwith "Too many arguments in the command";;


