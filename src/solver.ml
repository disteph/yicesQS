[%%import "debug.mlh"]

open Containers

open Sexplib
open Type
open Yices2.Ext
open Ext

module SMT2 = Yices2.SMT2.Make(Ext)
open SMT2

open Command_options
open Utils

module Support = struct
  
  type t =
    | Empty
    | S of {
        trigger : Term.t;
        variables : Term.t list
      } [@@deriving show]

  let list = function
    | Empty -> []
    | S{ trigger; variables } -> trigger::variables
end

type answer =
  | Unsat of Term.t
  | Sat of Term.t list
[@@deriving show { with_path = false }]

exception BadInterpolant     of SolverState.t * Level.t * Term.t
exception BadUnder           of SolverState.t * Level.t * Term.t
exception FromYicesException of SolverState.t * Level.t * Types.error_report * string
exception WrongAnswer        of SolverState.t * answer

[%%if debug_mode]

let check state level model support reason =
  let (module S:SolverState.T) = state in
  print "check" 3 "@[<v2>Checking that our model %a@,satisfies reason %a@]@,"
    (SModel.pp()) (SModel{ model; support })
    Term.pp reason;
  Context.push S.epsilons_context;
  Context.assert_formula S.epsilons_context (Term.not1 reason);
  match Context.check S.epsilons_context ~smodel:(SModel.make model ~support) with
  | `STATUS_SAT   ->
    print "check" 3 "@[<v2>It does not satisfy it@]@,";
    raise (BadUnder(state, level, reason))
  | `STATUS_UNSAT ->
    print "check" 3 "@[<v2>It does satisfy it@]@,";
    Context.pop S.epsilons_context
  | _ -> assert false

let check_interpolant state level model interpolant context =
  if (Model.get_bool_value model interpolant)
  then raise (BadInterpolant(state, level, interpolant));
  if Term.(equal interpolant (false0()))
     && not(Types.equal_smt_status (Context.check context) `STATUS_UNSAT)
  then raise (BadInterpolant(state, level, interpolant));

[%%else]

let check _state _level _model _support _reason = ()

let check_interpolant _state _level _model _interpolant _context = ()

[%%endif]

type treat_sat_result =
  | ModelWorked of Term.t list
  | ModelFailed

let rec solve ?(compute_over=true) state level model support learnt : answer * SolverState.t * Term.t =
  try
    let (module S:SolverState.T) = state in
    let open S in
    print "solve" 1 "@[<v2>Solving game:@,%a@,@[<2>from model@ %a@]@]@,"
      Level.pp level
      (SModel.pp()) (SModel{ model; support = Support.list support });
    print "solve" 1 "@]%!@[<v>";

    print "solve" 4 "@[Trying to solve over-approximations@]@,";
    let status =
      match support with
      | Empty -> print "solve" 0 ".%i%!" level.id; Context.check context
      | S _   -> print "solve" 0 ".%i" level.id; Context.check context
                                ~smodel:(SModel.make model ~support:(Support.list support))
    in
    match status with

    | `STATUS_UNSAT ->
      let interpolant = match support with
        | S _ when compute_over ->
           print "disabled" 0 "@[Overapproximation@]@,";
           let interpolant = Context.get_model_interpolant context in
           check_interpolant state level model interpolant context;
           Term.(not1 interpolant)
        | _ -> print "disabled" 0 "@[No overapproximation@]@,"; Term.true0()
      in
      let answer = Unsat interpolant in
      print "solve" 3 "@[<2>Level %i answer on that model is@ @[%a@]@]"
        level.id pp_answer answer;
      answer, state, Term.andN learnt

    | `STATUS_SAT ->
      let SModel{ model; _ } = Context.get_model context ~keep_subst:true in
      print "model" 0 "@[Found model of over-approx @,@[<v 2>  %a@]@]@,%!"
        (SModel.pp())
        (SModel{support = List.append level.newvars (Support.list support); model });
      post_process ~compute_over state level model support learnt

    | x -> Types.show_smt_status x |> print_endline; failwith "not good status"

  with
    Yices2.High.ExceptionsErrorHandling.YicesException(_,report) ->
    raise (FromYicesException(state, level,report, Printexc.get_backtrace()))

and post_process ~compute_over state level model support learnt =
  print "indent" 1 "@[<v 1> ";
  let result, learnt = treat_sat state level model support learnt in
  print "indent" 1 "@]@,";
  match result with
  | ModelWorked underapprox ->
     if List.is_empty underapprox
     then print "disabled" 0 "@[No underapproximation@]@,"
     else print "disabled" 0 "@[Underapproximation@]@,";
     Sat underapprox, state, Term.andN learnt
  | ModelFailed -> (solve[@tailcall]) ~compute_over state level model support learnt

and treat_sat state level model support learnt : treat_sat_result * Term.t list =
  let (module S:SolverState.T) = state in

  let compute_under =
    match support with
    | Empty -> false
    | S _   -> true
  in
  (* Now we look at each forall formula that we have to satisfy, one by one *)
  let rec aux model cumulated_support reasons4success (learnt : Term.t list) foralls =
    match foralls() with

    (* We have satisfied all forall formulae; our model is good! *)
    | Seq.Nil ->
       if compute_under
       then
      let reasons4success = Level.(level.ground)::reasons4success in
      (* We first aggregate the reasons why our model worked *)
      (* Any model satisfying true_of_model would have been a good model *)
      let true_of_model = Term.andN reasons4success in
      print "solve" 4 "@[<2>true of model is@ @[<v>%a@]@]@," Term.pp true_of_model;
      (* Now compute several projections of the reason on the rigid variables *)
      let seq =
        print "solve" 1 "@,Sent for generalization:@, %a@," Term.pp true_of_model;
        (* print 0 "@,%a" (List.pp Term.pp) Level.(level.newvars); *)
        QF_API.generalize_model
          ~logic:S.logic
          model
          ~true_of_model
          ~rigid_vars:Level.(level.rigid)
          ~newvars:   Level.(level.newvars)
      in
      let rec extract
                (accu : Term.t list)
                (epsilons : Term.t list)
                (n:int)
                (l : Term.t WithEpsilons.t CLL.t) : Term.t list WithEpsilons.t =
        if n <= 0 then { main = accu; epsilons }
        else
          match Lazy.force l with
          | `Nil -> { main = accu; epsilons }
          | `Cons(({ main = head; epsilons = epsilons_local }, _), tail) -> 
            match epsilons_local, epsilons with
            | [], epsilons
            | epsilons, [] -> extract (head::accu) epsilons (n-1) tail
            | _::_, _::_   -> extract accu epsilons (n-1) tail
      in
      let WithEpsilons.{ main = underapprox; epsilons } = extract [] [] !underapprox seq in
      print "solve" 1 "@,After generalization@, %a@," (List.pp Term.pp) underapprox;
      SolverState.record_epsilons state epsilons;
      print "solve" 3 "@[<v2>Level %i model works, with %i reason(s)@,@[<v2>  %a@]@]@,"
        level.id
        (List.length underapprox)
        (List.pp Term.pp) underapprox;
      ModelWorked underapprox, learnt
       else
      ModelWorked [], learnt

    (* Here we have a forall formula o that is false in the model;
       the reason why we don't have to look at it is that o is false in the model. *)
    | Seq.Cons(o, opponents) when not (Model.get_bool_value model Level.(o.name)) ->
      print "solve" 4 "@[Level %i does not need to be looked at as %a is false@]@,"
        o.sublevel.id
        Term.pp o.name;
      aux model
        (o.name::cumulated_support)
        (Term.not1 o.name::reasons4success)
        learnt
        (Seq.append o.sublevel.foralls opponents)

    (* Here we have a forall formula o that is true in the model;
       we have to make a recursive call to play the corresponding sub-game *)
    | Seq.Cons(o, opponents) ->
      print "solve" 4 "@[Level %i needs to be looked at as %a is true@]@,"
        o.sublevel.id
        Term.pp o.name;

      let open Level in

      (* To the recursive call, we will feed values for the following variables *)
      let recurs_support = Support.S{ trigger = o.selector; variables = o.sublevel.rigid } in

      (* Now we produce the model to feed the recursive call and perform the call.
         We get back the status of the call and the model that we fed to it *)
      let (recurs_status, _, recurs_learnt), _recurs_model =
      (* let recurs_status = *)
        (* if Model.get_bool_value model o.selector
         * then (\* The selector for this subformula is already true *\)
         *   (print "solve" 4 "@[Model already makes %a true, we stick to the same model@]@,"
         *      Term.pp o.selector;
         *    post_process state o.sublevel model recurs_support, model)
         * else *)
        (* We extend the model by setting the selector to true *)
        let status =
          Context.check o.selector_context
            ~smodel:(SModel.make model ~support:o.sublevel.rigid)
        in
        (* This should always work *)
        assert(Types.equal_smt_status status `STATUS_SAT);
        (* This is the extended model *)
        let SModel{ model = recurs_model ; _} =
          Context.get_model o.selector_context ~keep_subst:true
        in
        solve ~compute_over:compute_under state o.sublevel recurs_model recurs_support [], recurs_model

      in

      let learnt =
        match S.logic with
        | `BV ->
           let WithEpsilons.{ main; epsilons } =
             IC.weaken_existentials_init o.sublevel.newvars recurs_learnt
           in
           SolverState.record_epsilons state epsilons;
           SolverState.learn state [main];
           main::learnt
             
        | _ -> learnt
      in

      (* elim_trigger eliminates the trigger variable from the explanations given by the
         recursive call *)
      let elim_trigger reason = Term.subst_term [o.selector,Term.true0()] reason in
      match recurs_status with
      | Unsat reason ->
        begin
          print "solve" 1 "@,";
          print "solve" 4 "@[<v2>Back to level %i, we see from level %i answer Unsat with reason@,@[%a@]@]@,"
            level.id
            o.sublevel.id
            Term.pp reason;
          if compute_under then
          (* We first eliminate the trigger from the reason... *)
          let reason = elim_trigger reason in
          print "solve" 4 "@[Reason's projection is %a@]@," Term.pp reason;
          (* ...and check that our current model indeed satisfies it (debug mode). *)
          check state level model o.sublevel.rigid reason;
          (* next moves on to the next opponent;
             with a cumulated support and a model that may updated with what we've learnt. *)
          let next cumulated_support model =
            (* we add the reason and continue with the next opponents *)
            aux model cumulated_support (reason::reasons4success) learnt opponents
          in
          match opponents with
          | _ -> next cumulated_support model (* This was the last opponent. *)
          (* | _ -> *)
          (*   (\* If there is another opponent coming, we may want to update our current model *)
          (*      according to the lemmas we've learnt from the recursive call *)
          (*      and that our current model may be violating. *\) *)
          (*   (\* We first augment the cumulated support with those variables that matter for *)
          (*      reason to hold *\) *)
          (*   let var_that_matter = Model.model_term_support model reason in *)
          (*   (\* Then we add them to the cumulative support *\) *)
          (*   let cumulated_support = *)
          (*     List.sorted_merge_uniq ~cmp:Term.compare var_that_matter cumulated_support *)
          (*   in *)
          (*   print "solve" 4 "@[Now checking whether our model %a violates anything we have learnt@]@," *)
          (*     (SModel.pp ()) (SModel{ model; support = cumulated_support }); *)
          (*   match Context.check context ~smodel:(SModel.make model ~support:cumulated_support) with *)
          (*   | `STATUS_SAT  -> *)
          (*      let SModel{ model; _ } =  *)
          (*        Context.get_model context ~keep_subst:true *)
          (*      in *)
          (*      next cumulated_support model *)
          (*   | `STATUS_UNSAT ->  *)
          (*     print 4 "@[We learned something that defeats this model@]@,"; *)
          (*     None *)
                      (*   | _             -> assert false *)
          else
            failwith "FIXME"
        end

      | Sat reasons4failure ->
        print "solve" 4 "@[<v2>Back to level %i, we see from level %i answer Sat with reasons@,@[%a@]@]@,"
          level.id
          o.sublevel.id
          (List.pp Term.pp) reasons4failure;
        assert(List.length reasons4failure > 0);
        let aux sofar reason =
          let reason = elim_trigger reason in
          check state level model o.sublevel.rigid reason;
          let lemma = Term.(o.name ==> not1 reason) in
          SolverState.learn state [lemma];
          lemma::sofar
        in
        let learnt = List.fold_left aux learnt reasons4failure in
        ModelFailed, learnt
  in
  let cumulated_support = match support with
    (* If our own support is not empty, the first element is our own trigger:
       we keep it as well as the values passed to the recursive call but its own trigger *)
    | S{ trigger; _ } -> [trigger]
    | Empty -> [] (* otherwise we just keep those values *)
  in
  aux model cumulated_support [] learnt level.foralls

[%%if debug_mode]
let return state answer expected =
  match answer, expected with
  | Unsat _, None -> "unsat?"
  | Sat _, None -> "sat?"
  | Unsat _, Some false -> "unsat!"
  | Sat _, Some true -> "sat!"
  | Unsat _, Some true 
    | Sat _, Some false -> raise (WrongAnswer(state, answer))
[%%else]
let return _state answer _expected =
  match answer with
  | Unsat _ -> "unsat"
  | Sat _ -> "sat"
[%%endif]


[%%if debug_mode]
let setmode config = Config.set config ~name:"mode" ~value:"push-pop"
[%%else]
let setmode config = Config.set config ~name:"mode" ~value:"multi-checks"
[%%endif]

let treat filename =
  let sexps = SMT2.load_file filename in
  let session    = Session.create 0 in
  let config     = ref None in
  let logic      = ref `Other in
  let qf_logic   = ref "" in
  let support    = ref [] in
  let expected   = ref None in
  let assertions = ref [] in
  let states     = ref [] in
  let treat sexp =
    match sexp with
    | List(Atom head::args) ->
      print "treat" 1 "@[<2>Traversing sexp@ %a@]@," pp_sexp sexp;
      begin
        match head, args with
        | "set-info",   [Atom ":status"; Atom "sat"] ->
          expected := Some true

        | "set-info",   [Atom ":status"; Atom "unsat"] ->
          expected := Some false

        | "set-option", _ ->
           ()

        | "declare-fun", [Atom name; List []; typ]
        | "declare-const", [Atom name; typ] ->
          let ytype = ParseType.parse session.types typ |> Yices2.SMT2.Cont.get in
          let yvar = Term.new_uninterpreted ~name ytype in
          support := yvar :: !support;
          (* print "treat" 2 "@[<2>  declared fun/cst is %a@]@," Term.pp yvar; *)
          Variables.permanently_add session.variables name yvar

        | "assert", [formula] ->
           let formula = ParseTerm.parse session formula |> Yices2.SMT2.Cont.get in
           (* print 2 "@[<2>Asserting formula@,%a@]@," Term.pp formula; *)
           (match !(session.model) with
            | Some(SModel{ model; _ }) -> Model.free model
            | None -> ());
           assertions := formula::!assertions

        
        | "set-logic",  [Atom l]            ->
           let cfg = Config.malloc () in
           print "treat" 3 "@[Setting logic to %s@]@," l;
           let mcsat =
             match !Command_options.ysolver with
             | Some `MCSAT -> true
             | Some `CDCLT -> false
             | None -> not(String.equal "BV" l)
           in
           if mcsat
           then
             begin 
               Config.set cfg ~name:"solver-type" ~value:"mcsat";
               Config.set cfg ~name:"model-interpolation" ~value:"true"
             end;
           setmode cfg;
           config := Some cfg;
           begin
             match l with
             | "BV" ->  logic := `BV; qf_logic := "QF_BV"
             | "NIA" -> logic := `NIA; qf_logic := "QF_NIA"
             | "NRA" -> logic := `NRA; qf_logic := "QF_NRA"
             | "LIA" -> logic := `LIA; qf_logic := "QF_LIA"
             | "LRA" -> logic := `LRA; qf_logic := "QF_LRA"
             | _ -> logic := `Other; qf_logic := "all"
           end
        | "check-sat", [] ->
           begin
             match !config with
             | None ->
                raise (Yices2.SMT2.Yices_SMT2_exception "You need to have (set-logic ...) before (check-sat)")
             | Some config ->
           let formula = Term.(andN !assertions) in
           print "treat" 2 "@[<v 2>@[Computing game@]@,";
           let WithEpsilons.{ main = game; epsilons } =
             Game.process config ~logic:!logic ~global_vars:!support formula
           in
           print "treat" 3 "@[<v 1>Computed game is:@,@[%a@]@]@," Game.pp game;
           print "treat" 2 "@]@,";
           let state = SolverState.create ~logic:!logic ~qf_logic:!qf_logic config game in
           SolverState.epsilon_assert state epsilons;
           print "treat" 1 "@[<v>";
           let (module G) = game in
           let answer, state, _learnt =
             solve ~compute_over:false state G.top_level (Model.from_map []) Support.Empty []
           in
           print "treat" 1 "@]@,";
           let str = return state answer !expected in
           Format.(fprintf stdout) "@[%s@]@," str;
           states := state::!states;
           (* SolverState.free initial_state; *)
           print "treat" 3 "@[Game freed@]@,"
           end

        | "exit", [] ->
           print "treat" 1 "@[Exiting@]@,"; ()
        (* Session.exit session *)

        | _ -> ParseInstruction.parse session sexp

      end
    | _ -> ParseInstruction.parse session sexp
  in
  List.iter treat sexps;
  print "treat" 1 "@[Exited gracefully@]@,";
  !states
