open Containers
open Yices2.High
open Yices2.Ext_bindings
open Yices2.SMT2

open Solver
open Command_options

let () = assert(Global.has_mcsat())
  
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

open Arg

let args = ref []
let description = "QE in Yices"

let options = Tracing.options;;

Arg.parse options (fun a->args := a::!args) description;;

match !args with
| [filename] ->
   Tracing.compile();
  (try
     Format.(fprintf stdout) "@[<v>";
     let () = treat filename in
     Format.(fprintf stdout) "@]%!";
   with

   | Yices_SMT2_exception s as exc ->
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


