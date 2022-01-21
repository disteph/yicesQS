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

let epsilon   = ref None

module DblCtx = struct

  type t = {
      cdclT   : Context.t;
      cdclT_assertions : Term.t list ref;
      cdclT_assertionsH : unit HTerms.t;
      cdclT_purify : subst ref;
      mcsat   : Context.t;
      epsilon : (Term.t * Term.t) option; (* epsilon term and value *)
      rat2alg : subst ref;
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

    let cdclT = Context.malloc ~config:cfg_cdclT () in
    let mcsat = Context.malloc ~config:cfg_mcsat () in

    let epsilon =
      match !epsilon with
      | None -> None
      | Some f ->
         let epsilon = Term.new_uninterpreted ~name:"epsilon" (Type.real()) in
         let epsilon_v = Term.Arith.parse_float f in
         (* let epsilon_pos = Term.Arith.(lt (zero()) epsilon) in *)
         (* let epsilon_leq = Term.Arith.(leq epsilon epsilon_v) in *)
         (* let constraints = [ epsilon_pos; epsilon_leq ] in *)
         let constraints = [ Term.(epsilon === epsilon_v) ] in
         (* Context.assert_formulas cdclT constraints; *)
         Context.assert_formulas mcsat constraints;
         Some(epsilon, epsilon_v)
    in
    let r = { cdclT;
              cdclT_assertions  = ref [];
              cdclT_assertionsH = HTerms.create 100;
              cdclT_purify = ref [];
              mcsat;
              epsilon;
              rat2alg = ref [] }
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
      Purification.Term.purify is_cdclT formula []
    in
    assert(not(HTerms.mem t.cdclT_assertionsH cdclT_formula));
    t.cdclT_assertions := cdclT_formula :: !(t.cdclT_assertions);
    HTerms.replace t.cdclT_assertionsH cdclT_formula ();
    (* Context.assert_formula t.cdclT cdclT_formula; *)
    (* Context.assert_formula t.mcsat cdclT_formula; *)
    t.cdclT_purify := List.rev_append cdclT_purify !(t.cdclT_purify);
    Context.assert_formulas t.mcsat (List.map (fun (x,y) -> Term.eq x y) cdclT_purify)

  let alg2rat = HTerms.create 100
  let rat2alg = HTerms.create 100
  let reset() = HTerms.reset alg2rat; HTerms.reset rat2alg

  let is_approx = HTerms.mem rat2alg

  let alg2rat ctx k =
    if is_approx k then k
    else
      let f x =
        let typ = Term.type_of_term x in
        let x_Q = Term.new_uninterpreted ~name:(Format.sprintf "%a_Q" Term.pp x) typ in
        HTerms.add rat2alg x_Q x;
        let diff_term = Term.Arith.(x -- x_Q) in
        let () = 
          match ctx.epsilon with
          | None -> ()
          | Some(epsilon,_) ->
             let bounding = Term.Arith.([leq (neg epsilon) diff_term;
                                         leq diff_term epsilon])
             in
             Context.assert_formulas ctx.mcsat bounding
        in
        ctx.rat2alg := (x_Q, x)::!(ctx.rat2alg);
        x_Q
      in
      HTerms.get_or_add alg2rat ~f ~k

  (* let rat2alg = HTerms.find rat2alg *)
              
  let rec check ?param t =

    (* Check CDCL(T) context *)

    Timer.transfer timer_other timer_in_yices;
    print "check" 1 "@,@[<v>@[CDCL(T) check@]@, @[<v>%a@]@]" (List.pp Term.pp) !(t.cdclT_assertions);
    let status = Context.check_with_assumptions ?param t.cdclT !(t.cdclT_assertions) in
    Timer.transfer timer_in_yices timer_other;
    match status with

    | `STATUS_UNSAT -> `STATUS_UNSAT, None

    | `STATUS_SAT ->
       begin
         let cdclT_model = Context.get_model t.cdclT in
         let assertions = !(t.cdclT_assertions) in

         (* Support: those terms, + values they get in cdclT_model, satisfy the cdclT ctx *)
         let support = Model.model_terms_support cdclT_model assertions in

         print "check" 1 "@,@[<v>@[CDCL(T) model is@]@, @[<v>%a@]@]"
           (SModel.pp ()) (SModel.make ~support cdclT_model); 


         let smodel_to_extend, subst = (* We're going to ask MCSAT to extend this model *)
           match t.epsilon with
           | Some(epsilon, _) -> (* The user requested that MCSAT tries to build a model close to the CDCL(T) one *)
              let aux (model, support) support_term =
                (* CDCL(T) should not know of approximation variables or epsilon *)
                assert(not(is_approx support_term));
                assert(not(Term.equal epsilon support_term));
                (* we substitute approximation variables for input variables of sort real *)
                let term_in_model =
                  if Term.is_real support_term then alg2rat t support_term else support_term
                in
                let val_in_model = Model.get_value_as_term cdclT_model support_term in
                (term_in_model, val_in_model)::model, term_in_model::support             
              in
              let model_to_extend, support = List.fold_left aux ([],[]) support in
              SModel.make ~support (Model.from_map model_to_extend),
              !(t.rat2alg)

           | None -> 
              let smodel_to_extend, constraints =
                Model.implicant_for_formulas cdclT_model assertions
                |> SModel.from_assumptions
              in
              Context.assert_formulas t.mcsat constraints;
              smodel_to_extend,
              List.rev_map (fun x -> x, Purification.Term.get_body x) smodel_to_extend.support
         in

         (* Now we search for full model, which extends smodel_to_extend *)

         let rec search_model () =

           Timer.transfer timer_other timer_in_mcsat;
           print "check" 1 "@,@[<v>@[MCSAT check@]@, @[<v>%a@]@,@[modulo model@]@, @[<v>%a@]@]"
             Context.pp t.mcsat
             (SModel.pp ()) smodel_to_extend;
           let status = Context.check_with_smodel t.mcsat smodel_to_extend in
           Timer.transfer timer_in_mcsat timer_other;

           match status with
           | `STATUS_SAT   ->

              let mcsat_model      = Context.get_model t.mcsat in
              print "check" 1 "@,@[<v>@[SAT with model@]@, @[<v>%a@]@]" Model.pp mcsat_model;
              
              let mcsat_assertions = Assertions.assertions (Context.assertions t.mcsat) in
              (* Support: those terms, + values they get in mcsat_model, satisfy the mcsat ctx *)
              let support = Model.model_terms_support mcsat_model mcsat_assertions in

              let aux assumptions support_term =
                if Term.is_real support_term
                   && not(is_approx support_term)
                   && (match t.epsilon with
                       | Some(eps,_) when Term.equal eps support_term -> false
                       | _ -> true)
                then
                  begin
                    let val_in_model = Model.get_value mcsat_model support_term in
                    let v = Model.reveal mcsat_model val_in_model in
                    match v with
                    | `Rational q ->
                       Term.Arith.(leq support_term (mpq q))
                       :: Term.Arith.(geq support_term (mpq q))
                       :: assumptions
                    | `Algebraic { a; b; a_open; b_open ; _ } ->
                       let lb, ub, lb_open, ub_open =
                         if Q.compare a b < 0 then a, b, a_open, b_open
                         else b, a, b_open, a_open
                       in
                       let open Term in
                       let open Arith in
                       let assumption_lb = (if lb_open then lt else leq) (mpq lb) support_term in
                       let assumption_ub = (if ub_open then lt else leq) support_term (mpq ub) in
                       assumption_lb :: assumption_ub :: assumptions
                    | _ -> failwith "Val bad type"
                  end
                else assumptions
              in

              let assumptions = List.fold_left aux !(t.cdclT_assertions) support in

              begin
                Timer.transfer timer_other timer_in_yices;
                print "check" 1 "@,@[<v>@[CDCL(T) check@]@, @[<v>%a@]@,with assumptions@, @[<v>%a@]@]"
                  Context.pp t.cdclT
                  (List.pp Term.pp) assumptions;
                let status = Context.check_with_assumptions ?param t.cdclT assumptions in
                Timer.transfer timer_in_yices timer_other;
                match status with
                | `STATUS_UNSAT ->
                   let lemma = Context.get_unsat_core t.cdclT
                               |> List.filter (HTerms.mem t.cdclT_assertionsH)
                               (* |> List.map Term.not1 *)
                               |> Term.orN
                   in
                   print "check" 1 "@,@[<v>@[Found UNSAT, with lemma@]@, @[<v>%a@]@]"
                     Term.pp lemma;
                   Context.assert_formula t.mcsat lemma;
                   search_model()

                | `STATUS_SAT ->
                   print "check" 1 "@,@[Found SAT, proceeding to final check@]";
                   let rec final_check = function
                     | [] ->
                        print "check" 1 "@,@[DONE!@]";
                        `STATUS_SAT, Some mcsat_model
                     | assertion::assertions ->
                        if Model.get_bool_value mcsat_model assertion
                        then
                          begin
                            print "check" 1 "@,@[<v>@[This constraint is not satisfied@]@, @[<v>%a@]@]"
                              Term.pp assertion;
                            final_check assertions
                          end
                        else
                          begin
                            print "check" 1 "@,@[<v>@[This constraint is not satisfied@]@, @[<v>%a@]@]"
                              Term.pp assertion;
                            Context.assert_formula t.mcsat assertion;
                            search_model()
                          end
                   in
                   final_check assertions

                | _ -> High.ExceptionsErrorHandling.raise_bindings_error
                         (Format.sprintf "CDCLT/inner %a, with report %a"
                            Types.pp_smt_status status
                            Types.pp_error_report (High.Error.report()))
              end

           | `STATUS_UNSAT ->

              let interpolant = Context.get_model_interpolant t.mcsat in
              print "check" 1 "@,@[<v>@[UNSAT with interpolant@]@, @[<v>%a@]@]"
                Term.pp interpolant;
              let interpolant = Term.subst_term subst interpolant in
              print "check" 1 "@,@[<v>@[after substitution:@]@, @[<v>%a@]@]"
                Term.pp interpolant;
              assert(not (Model.get_bool_value cdclT_model interpolant));
              assert_formula t interpolant;
              check ?param t

           | _ -> High.ExceptionsErrorHandling.raise_bindings_error
                    (Format.sprintf "MCSAT %a, with report %a"
                       Types.pp_smt_status status
                       Types.pp_error_report (High.Error.report()))
         in
         search_model()
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
  let context    = DblCtx.malloc () in
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
           Format.(fprintf stdout) "@,@,@[%a, expecting %a@]@,"
             Types.pp_smt_status status
             (Option.pp Types.pp_smt_status)
             (Option.map (fun b -> if b then `STATUS_SAT else `STATUS_UNSAT) !expected);
           Format.(fprintf stdout) "@,@[Time in Yices = %f, time in MCSAT = %f, time elsewhere = %f@]@,"
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
  DblCtx.reset();
  print "treat" 1 "@[Exited gracefully@]@,"
