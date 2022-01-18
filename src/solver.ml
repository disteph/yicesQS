[%%import "debug.mlh"]

open Containers
open Sexplib
open Type
open Yices2
open Yices2.Ext_bindings
open Yices2.SMT2

open Command_options

let pp_space fmt () = Format.fprintf fmt " @,"

type subst = (Term.t * Term.t) list

let timer_in_yices = Timer.create "Yices timer" 
let timer_in_mcsat = Timer.create "MCSAT timer"
let timer_other = Timer.create "other"
           
module DblCtx = struct

  type t = {
      cdclT : Context.t;
      cdclT_purify : (Term.t * Term.t) list ref;
      mcsat : Context.t
    }

  let malloc () =
    let cfg_cdclT = Config.malloc () in
    let cfg_mcsat = Config.malloc () in
    Config.set cfg_cdclT ~name:"solver-type" ~value:"dpllt";
    Config.set cfg_mcsat ~name:"solver-type" ~value:"mcsat";
    Config.set cfg_cdclT ~name:"mode" ~value:"multi-checks";
    Config.set cfg_mcsat ~name:"mode" ~value:"multi-checks";
    (* Config.set cfg_mcsat ~name:"mode" ~value:"push-pop"; *)
    Config.set cfg_mcsat ~name:"model-interpolation" ~value:"true";
    let r = { cdclT = Context.malloc ~config:cfg_cdclT ();
              cdclT_purify = ref [];
              mcsat = Context.malloc ~config:cfg_mcsat (); }
    in
    Config.free cfg_cdclT;
    Config.free cfg_mcsat;
    r

  let is_cdclT t =
    let is_nonlinear = function
      | _::_::_ -> true
      | [ _, exp ] when not Unsigned.UInt.(equal one exp) -> true
      | _ -> false
    in
    let Term x = Term.reveal t in
    match x with
    | Product(false,l) when is_nonlinear l -> false
    | _ -> true

  let is_mcsat _ = true
                 
  let cmp (a, _) (b, _) = Term.compare a b

  let assert_formula t formula =
    let cdclT_formula, cdclT_purify =
      Purification.Term.purify is_cdclT formula !(t.cdclT_purify)
    in
    Context.assert_formula t.cdclT cdclT_formula;
    t.cdclT_purify := List.sort_uniq ~cmp cdclT_purify

  let rec check ?param t =
    Timer.transfer timer_other timer_in_yices;
    print "check" 1 "@,@[CDCL(T) check %a@]" Context.pp t.cdclT;
    let status = Context.check ?param t.cdclT in
    Timer.transfer timer_in_yices timer_other;
    match status with
    | `STATUS_UNSAT -> `STATUS_UNSAT, None
    | `STATUS_SAT ->
       begin
         let model = Context.get_model t.cdclT in
         let assertions = Assertions.assertions (Context.assertions t.cdclT) in
         let implicant  = Model.implicant_for_formulas model assertions in
         let implicant  = Term.subst_terms !(t.cdclT_purify) implicant in
         let rec aux (assumptions, accu) = function
           | [] -> assumptions, accu
           | implicant_item::tail ->
              let mcsat_formula, accu =
                Purification.Term.purify is_mcsat implicant_item accu
              in
              aux (mcsat_formula::assumptions, accu) tail
         in
         let assumptions, mcsat_purify = aux ([],[]) implicant in

         Timer.transfer timer_other timer_in_mcsat;
         print "check" 1 "@,@[MCSAT check %a@]" (List.pp Term.pp) assumptions;
         let status = Context.check_with_assumptions t.mcsat assumptions in
         Timer.transfer timer_in_mcsat timer_other;

         match status with
         | `STATUS_SAT   ->
            let model_mcsat = Context.get_model t.mcsat in
            `STATUS_SAT, Some model_mcsat

         | `STATUS_UNSAT ->
            let core = Context.get_unsat_core t.mcsat |> Term.subst_terms mcsat_purify in
            assert_formula t Term.(not1(andN core));
            check ?param t

         | _ -> High.ExceptionsErrorHandling.raise_bindings_error
             (Format.sprintf "MCSAT %a, with report %a"
                Types.pp_smt_status status
                Types.pp_error_report (High.Error.report()))
       end
    | _ -> High.ExceptionsErrorHandling.raise_bindings_error
             (Format.sprintf "CDCL(T) %a, with report %a"
                Types.pp_smt_status status
                Types.pp_error_report (High.Error.report()))

end


let treat filename =
  print "treat" 1 "HELLO";
  let sexps = SMT2.load_file filename in
  let set_logic logic _ = print "treat" 3 "@[Setting logic to %s@]@," logic in
  let session    = Session.create ~set_logic 0 in
  let support    = ref [] in
  let expected   = ref None in
  let context    = DblCtx.malloc() in
  let treat sexp =
    match sexp with
    | List(Atom head::args) ->
      print "treat" 1 "@[<2>Traversing sexp@ %a@]@," pp_sexp sexp;
      begin
        match head, args, !(session.env) with
        | "set-info",   [Atom ":status"; Atom "sat"], _ ->
           expected := Some true

        | "set-info",   [Atom ":status"; Atom "unsat"], _ ->
           expected := Some false

        | "set-option", _, _ ->
           ()

        | "declare-fun", [Atom name; List []; typ], Some env
        | "declare-const", [Atom name; typ], Some env ->
          let ytype = ParseType.parse env.types typ |> Cont.get in
          let yvar = Term.new_uninterpreted ~name ytype in
          support := yvar :: !support;
          (* print 2 "@[<2>  declared fun/cst is %a@]@," Term.pp yvar; *)
          Variables.permanently_add env.variables name yvar

        | "assert", [formula], Some env ->
          let formula = ParseTerm.parse env formula |> Cont.get in
          (* print 2 "@[<2>Asserting formula@,%a@]@," Term.pp formula; *)
          (match env.model with
           | Some model -> Model.free model
           | None -> ());
          DblCtx.assert_formula context formula

        | "check-sat", [], _ ->
           print "treat" 1 "@[<v>";
           Timer.start timer_other;
           let status, model = DblCtx.check context in
           Timer.stop timer_other;
           print "treat" 1 "@]@,";
           Format.(fprintf stdout) "@[%a, expecting %a@]@,"
             Types.pp_smt_status status
             (Option.pp Types.pp_smt_status)
             (Option.map (fun b -> if b then `STATUS_SAT else `STATUS_UNSAT) !expected);
           Format.(fprintf stdout) "@[Time in Yices = %f, time in MCSAT = %f, time elsewhere = %f@]@,"
             (Timer.read timer_in_yices)
             (Timer.read timer_in_mcsat)
             (Timer.read timer_other);
           let () =
             match model with
             | None -> ()
             | Some model ->
                Format.(fprintf stdout) "@,@[model@]@,@[<v>%a@]@," (SModel.pp ()) (SModel.make model)
           in
           (* SolverState.free initial_state; *)
           print "treat" 3 "@[Context freed@]@,";

        | "exit", [], _ ->
          print "treat" 1 "@[Exiting@]@,"; ()
          (* Session.exit session *)

        | _ -> ParseInstruction.parse session sexp

      end
    | _ -> ParseInstruction.parse session sexp
  in
  List.iter treat sexps;
  print "treat" 1 "@[Exited gracefully@]@,"
