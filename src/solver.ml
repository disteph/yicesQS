[%%import "debug.mlh"]

(* Implements OptiQSMA from the journal paper (Alg. 3/4) on a QSMA-tree
   (Def. 1) with per-node formula n.psi (Def. 2). The solver checks
   satisfaction with look-ahead |=la (Def. 11) using look-ahead formulas
   LF(n) (Def. 8), and alternates model-based over-approximation (Def. 5/MBO)
   and under-approximation (Def. 4/MBU). *)

open Containers

open Sexplib
open Type
open Yices2.Ext
open Ext

module SMT2 = Yices2.SMT2.Make(Ext)
open SMT2
module YicesHigh = Yices2.High.Make(Yices2.High.NoErrorHandling)

open Command_options
open Utils

module Support = struct
  (* A support pins the current assignment to Rigid(n) (Def. 1/3) when
     calling SMA/Context.check. The trigger is the internal selector used
     to enforce LF(sublevel) (Def. 8) when recursing; variables are the
     rigid variables of that subgame. *)
  
  type t =
    | Empty
    | S of {
        trigger : Term.t;
        variables : Term.t list
      } [@@deriving show]

  (* list t: flatten a support into the list of terms to keep fixed. *)
  let list = function
    | Empty -> []
    | S{ trigger; variables } -> trigger::variables
end

type answer =
  | Unsat of Term.t
  | Sat of Term.t list
[@@deriving show { with_path = false }]

(* Debug-only consistency checks. *)
exception BadInterpolant     of SolverState.t * Level.t * Term.t
exception BadUnder           of SolverState.t * Level.t * Term.t
exception FromYicesException of SolverState.t * Level.t * Types.error_report * string
exception WrongAnswer        of SolverState.t * answer

[%%if debug_mode]

(* check state level smodel support reason:
   - state: current solver state (contexts/config/logic)
   - level: level whose model we are checking
   - smodel: model returned by Yices
   - support: terms whose values are fixed in the check
   - reason: formula that should be true in model
   Debug helper to validate U (Def. 4) returned by MBU. *)
let check state level smodel support reason =
  let (module S:SolverState.T) = state in
  print "check" 3 "@[<v2>Checking that our model %a@,satisfies reason %a@]@,"
    (SModel.pp()) (SModel.with_support support smodel)
    Term.pp reason;
  Context.push S.epsilons_context;
  Context.assert_formula S.epsilons_context (Term.not1 reason);
  match Context.check S.epsilons_context ~smodel:(SModel.with_support support smodel) with
  | `STATUS_SAT   ->
    print "check" 3 "@[<v2>It does not satisfy it@]@,";
    raise (BadUnder(state, level, reason))
  | `STATUS_UNSAT ->
    print "check" 3 "@[<v2>It does satisfy it@]@,";
    Context.pop S.epsilons_context
  | _ -> assert false

(* check_interpolant state level smodel interpolant context:
   - interpolant must be false in model and must be a valid interpolant
   when it is the constant false. Debug helper for O (Def. 5). *)
let check_interpolant state level smodel interpolant context =
  if (SModel.formula_true_in_model smodel interpolant)
  then raise (BadInterpolant(state, level, interpolant));
  if Term.(equal interpolant (false0()))
     && not(Types.equal_smt_status (Context.check context) `STATUS_UNSAT)
  then raise (BadInterpolant(state, level, interpolant));

[%%else]

let check _state _level _smodel _support _reason = ()

let check_interpolant _state _level _smodel _interpolant _context = ()

[%%endif]

let timer = Timer.create "timer"
exception Interrupted
let count = ref 0

let () = Global.init()
let current_param = ref None
let as_inequalities = ref false
let cancel_flag = Atomic.make false

let param_from_seed i logic mode =
  let p = Param.malloc () in
  Param.set p ~name:"random-seed" ~value:(string_of_int i);
  (match SolverState.qf_logic_of_logic logic, mode with
   | ("QF_NIA" | "QF_LIA"), `MCSAT ->
       Param.set p ~name:"mcsat-l2o" ~value:"true"
   | _ -> ());
  p

let is_qf_bv_logic = String.equal "QF_BV"

(* solve ?compute_over state level smodel support:
   - compute_over: if true, compute a model interpolant on UNSAT
   - state: solver state (contexts, logic, counters)
   - level: current game level to solve
   - smodel: model from parent level (or empty model at top)
   - support: terms fixed in model when checking the level
   Implements optiSubtreeIsSolved (Alg. 4) for node level, with support
   = Rigid(level) (Def. 1/3). Returns SAT(U) or UNSAT(O) as in Alg. 4. *)
let rec solve ?(compute_over=true) state level smodel support : answer*SolverState.t =
  if Atomic.get cancel_flag then raise Interrupted;
  let (module S:SolverState.T) = state in
  print "base" 1 "@[<v2>Counter is %i@]@,\n%!" !count;
  let open S in
  try
    print "solve" 1 "@[<v2>Solving game:@,%a@,@[<2>from model@ %a@]@]@,"
      Level.pp level
      (SModel.pp()) (SModel.with_support (Support.list support) smodel);

    print "solve" 4 "@[Trying to solve over-approximations@]@,";
    let status =
      match support with
      | Empty -> print "solve" 0 ".%i%!" level.id; Context.check ~param:(Option.get_exn_or "No parameter" !current_param) context
      | S _   -> print "solve" 0 ".%i" level.id; Context.check context
                                ~as_inequalities:!as_inequalities
                                ~param:(Option.get_exn_or "No parameter" !current_param)
                                ~smodel:(SModel.with_support (Support.list support) smodel)
    in
    match status with

    | `STATUS_UNSAT ->
      (* Over-approximation: use model interpolant (MBO) for O (Def. 5),
         mirroring Alg. 4 line 6. *)
      let interpolant = match support with
        | S _ when compute_over ->
           print "disabled" 0 "@[Overapproximation@]@,";
           let interpolant = Context.get_model_interpolant context in
           check_interpolant state level smodel interpolant context;
           Term.(not1 interpolant)
        | _ -> print "disabled" 0 "@[No overapproximation@]@,"; Term.true0()
      in
      let answer = Unsat interpolant in
      print "solve" 3 "@[<2>Level %i answer on that model is@ @[%a@]@]"
        level.id pp_answer answer;
      answer, state

    | `STATUS_SAT ->
      (* SMA found an extension M' satisfying the current LF(level) context
         (Def. 8). We now check |=la (Def. 11) against forall subgames. *)
      let smodel = Context.get_model context ~keep_subst:true in
      print "model" 0 "@[Found model of over-approx @,@[<v 2>  %a@]@]@,%!"
        (SModel.pp())
        (SModel.with_support (List.append level.newvars (Support.list support)) smodel);

      post_process ~compute_over state level smodel support

    | `STATUS_ERROR ->
      let report = Error.report () in
      raise (FromYicesException(state, level, report, Printexc.get_backtrace()))

    | `STATUS_INTERRUPTED -> raise Interrupted

    | x -> Types.show_smt_status x |> print_endline; failwith "not good status"

  with
    (* Wrap Yices errors with level/state context for debugging. *)
    ExceptionsErrorHandling.YicesException(_,report) ->
    raise (FromYicesException(state, level,report, Printexc.get_backtrace()))

(* post_process ~compute_over state level smodel support:
   - compute_over: same flag passed to solve
   - state: solver state
   - level: current level
   - smodel: model returned by Context.get_model for this level
   - support: current support
   If the model is good, return SAT(U) with under-approx reasons (Def. 4/Alg. 4
   line 10). Otherwise, retry solve with the current model. *)
and post_process ~compute_over state level smodel support =
  print "indent" 0 "@[<v 1> ";
  let result = treat_sat state level smodel support in
  print "indent" 0 "@]@,%!";
  match result with
  | Some underapprox ->
     if List.is_empty underapprox
     then print "disabled" 0 "@[No underapproximation@]@,"
     else print "disabled" 0 "@[Underapproximation@]@,";
     Sat underapprox, state

  | None -> (solve[@tailcall]) ~compute_over state level smodel support

(* treat_sat state level smodel support:
   - state: solver state
   - level: current game level
   - smodel: candidate model for this level
   - support: which terms are fixed from above
   Implements solutionForallDescendants (Alg. 4) using FAN/NAN
   (Defs. 9/10). Returns Some under-approx reasons if the model satisfies
   all foralls (i.e., |=la holds), otherwise None to force a retry. *)
and treat_sat state level smodel support =
  let (module S:SolverState.T) = state in

  (* Under-approximation (Def. 4) is only meaningful if we came with a
     non-empty support, i.e., at non-top levels. *)
  let compute_under =
    match support with
    | Empty -> false
    | S _   -> true
  in
  (* Now we look at each forall formula that we have to satisfy, one by one *)
  (* aux smodel cumulated_support reasons foralls:
     - smodel: current candidate model
     - cumulated_support: terms fixed so far (incl. triggers)
     - reasons: accumulated reasons why foralls are satisfied
     - foralls: remaining forall opponents to check
     Traverses the current level's forall opponents (Def. 1/2) and
     mimics FAN/NAN filtering (Defs. 9/10). *)
  let rec aux smodel cumulated_support reasons foralls =
    match foralls() with

    (* We have satisfied all forall formulae; our model is good. *)
    | Seq.Nil ->
       if compute_under
       then
         let reasons = Level.(level.ground)::reasons in
         (* We first aggregate the reasons why our model worked *)
         (* Any model satisfying true_of_model would have been a good model *)
         let true_of_model = Term.andN reasons in
         print "solve" 4 "@[<2>true of model is@ @[<v>%a@]@]@," Term.pp true_of_model;
         (* Compute MBU (Def. 4) projections on rigid variables. *)
         let seq =
           print "solve" 1 "@,Sent for generalization:@, %a@," Term.pp true_of_model;
           (* print "solve" 0 "@,%a" (List.pp Term.pp) Level.(level.newvars); *)
           QF_API.generalize_model
             ~logic:S.logic
             smodel
             ~true_of_model
             ~rigid_vars:Level.(level.rigid)
             ~newvars:   Level.(level.newvars)
         in
         (* extract chooses up to !underapprox projected reasons and collects epsilons. *)
         let rec extract
                   (accu     : Term.t list)
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
         Some underapprox
       else
         Some[]

    (* Here we have a forall formula o that is false in the model;
       the reason why we don't have to look at it is that o is false in the model. *)
    | Seq.Cons(o, opponents) when not (SModel.formula_true_in_model smodel Level.(o.name)) ->
      print "solve" 4 "@[Level %i does not need to be looked at as %a is false@]@,"
        o.sublevel.id
        Term.pp o.name;
      (* o.name is the proxy b.p from Def. 1/2 (possibly polarity-flipped by
         preprocessing). If it is false, LF(level) forces LF(o.sublevel) (Def. 8),
         so we keep checking descendant foralls without recursion. *)
      aux smodel
        (o.name::cumulated_support)
        (Term.not1 o.name::reasons)
        (Seq.append o.sublevel.foralls opponents)

    (* Here we have a forall formula o that is true in the model;
       we have to make a recursive call to play the corresponding sub-game *)
    | Seq.Cons(o, opponents) ->
      print "solve" 4 "@[Level %i needs to be looked at as %a is true@]@,"
        o.sublevel.id
        Term.pp o.name;

      let open Level in

      (* To the recursive call, we will feed values for the following variables *)
      (* The recursive support includes only Rigid(o.sublevel) (Def. 1/3) and
         the selector used to assert LF(o.sublevel) (Def. 8). Derived terms
         are not passed (see the div-by-zero ping-pong example). *)
      let recurs_support = Support.S{ trigger = o.selector; variables = o.sublevel.rigid } in

      (* Now we produce the model to feed the recursive call and perform the call.
         We get back the status of the call *)
        let recurs_status =
        (* We extend the model by setting the selector to true *)
        let status =
          Context.check o.selector_context
            ~smodel:(SModel.with_support o.sublevel.rigid smodel)
        in
        (* This should always work *)
        assert(Types.equal_smt_status status `STATUS_SAT);
        (* This is the extended model *)
        let recurs_smodel =
          Context.get_model o.selector_context ~keep_subst:true
        in
        solve ~compute_over:compute_under state o.sublevel recurs_smodel recurs_support

      in
      (* elim_trigger eliminates the trigger variable from the explanations given by the
         recursive call *)
      let elim_trigger reason = Term.subst_term [o.selector,Term.true0()] reason in
      match recurs_status |> fst with
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
            (* ...and check that our current model indeed satisfies it. *)
            check state level smodel o.sublevel.rigid reason;
            (* next moves on to the next opponent;
               with a cumulated support and a model that may updated with what we've learnt. *)
            let next cumulated_support smodel =
              (* we add the reason and continue with the next opponents *)
              aux smodel cumulated_support (reason::reasons) opponents
            in
            match opponents with
            | _ -> next cumulated_support smodel (* This was the last opponent. *)
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
          (*   print "solve" 4 *)
          (*     "@[Now checking whether our model %a violates anything we have learnt@]@," *)
          (*     (SModel.pp ()) (SModel{ model; support = cumulated_support }); *)
          (*   match *)
          (*     Context.check context ~smodel:(SModel.make model ~support:cumulated_support) *)
          (*   with *)
          (*   | `STATUS_SAT  -> *)
          (*      let SModel{ model; _ } = Context.get_model context ~keep_subst:true in *)
          (*      next cumulated_support model *)
          (*   | `STATUS_UNSAT ->  *)
          (*     print "solve" 4 "@[We learned something that defeats this model@]@,"; *)
          (*     None *)
          (*   | _             -> assert false *)
          else
            aux smodel cumulated_support reasons opponents
        end
      | Sat reasons ->
        print "solve" 4 "@[<v2>Back to level %i, we see from level %i answer Sat with reasons@,@[%a@]@]@,"
          level.id
          o.sublevel.id
          (List.pp Term.pp) reasons;
        assert(List.length reasons > 0);
        (* The sublevel found a SAT model for the negated subformula; update
           our context as in Alg. 4 line 16 (b.U <- b.U or U). *)
        let aux reason =
          let reason = elim_trigger reason in
          check state level smodel o.sublevel.rigid reason;
          let lemma = Term.(o.name ==> not1 reason) in
          SolverState.learn state [lemma]
        in
        List.iter aux reasons;
        None
  in
  let cumulated_support = match support with
    (* If our own support is not empty, the first element is our own trigger:
       we keep it as well as the values passed to the recursive call but its own trigger *)
    | S{ trigger; _ } -> [trigger]
    | Empty -> [] (* otherwise we just keep those values *)
  in
  aux smodel cumulated_support [] level.foralls

[%%if debug_mode]
(* return state answer expected:
   - state/answer: result of solve
   - expected: SMT-LIB :status (if present)
   Debug mode distinguishes sat?/sat! and checks against expected. *)
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
(* In debug mode we need push/pop for consistency checks. *)
let setmode config = Config.set config ~name:"mode" ~value:"push-pop"
[%%else]
(* In release mode, multi-checks is faster and sufficient. *)
let setmode config = Config.set config ~name:"mode" ~value:"multi-checks"
[%%endif]

let create_events logic =
  let auto_portfolio, timeout =
    match !timeout, !events with
    | Some timeout, [] -> true, timeout
    | _ -> false, 0.
  in
  let small_switch = 5. /. 1200. *. timeout in
  let default () =
    match SolverState.qf_logic_of_logic logic with
    | "QF_NRA" | "QF_NIA" ->
      if auto_portfolio then begin
        wide_projection := Some 0;
        events := (24.5 /. 1200. *. timeout,
                   make_slice_config ~mode:(Some `MCSAT) ~seed:0 ()) :: !events;
        create_pool (Some `MCSAT) small_switch 20
      end;
      `MCSAT
    | "QF_LRA" ->
      if auto_portfolio then
        create_pool (Some `MCSAT) (timeout /. 4.) 3;
      `MCSAT
    | "QF_LIA" ->
      if auto_portfolio then
        create_pool (Some (`CDCLT `Ineq)) (timeout /. 6.) 5;
      `CDCLT `Ineq
    | "QF_BV" ->
      if auto_portfolio then begin
        events := (24.5 /. 1200. *. timeout,
                   make_slice_config ~mode:(Some (`CDCLT `Eq)) ~seed:0 ()) :: !events;
        create_pool (Some (`CDCLT `Eq)) small_switch 10;
        events := (700. /. 1200. *. timeout,
                   make_slice_config ~mode:(Some `MCSAT) ~seed:0 ()) :: !events;
        create_pool (Some `MCSAT) small_switch 10
      end;
      `CDCLT `Eq
    | _ -> `MCSAT
  in
  Option.get_lazy default !ysolver

(* set_config ~logic mode:
   - mode: whether to use MCSAT or CDCL(T)
   Creates a Yices config with the right solver and interpolation settings.
   Delegate selection is configured on reusable QF_BV contexts. *)
let set_config ~logic mode =
  let cfg = Config.malloc () in
  begin
    match mode with
    | `MCSAT ->
      Config.set cfg ~name:"solver-type" ~value:"mcsat";
      Config.set cfg ~name:"model-interpolation" ~value:"true"
    | `CDCLT _ ->
      match !Command_options.delegate with
      | Some delegate when is_qf_bv_logic (SolverState.qf_logic_of_logic logic) ->
         Config.default ~logic:"QF_BV" cfg;
         Config.set cfg ~name:"sat-delegate" ~value:delegate
      | _ -> ()
  end;
  setmode cfg;
  cfg

open Eio.Std

let run_with_timeout ~timeout_sec ~stop f =
  Eio_main.run @@ fun env ->
    let clock = Eio.Stdenv.clock env in
    let domain_mgr = Eio.Stdenv.domain_mgr env in
    let result_promise, resolve = Promise.create () in
    Switch.run (fun sw ->
      Fiber.fork ~sw (fun () ->
        let result =
          try Ok (Eio.Domain_manager.run domain_mgr f)
          with Interrupted -> Error `Timeout
        in
        Promise.resolve resolve result);
      match Eio.Time.with_timeout clock timeout_sec (fun () ->
        Promise.await result_promise)
      with
      | Ok result -> Some result
      | Error `Timeout ->
          stop();
          let _ = Promise.await result_promise in
          None)

(* treat filename:
   - filename: SMT-LIB2 file to parse and solve
   Parses commands, builds a game for the current assertions, runs solve,
   and handles get-model/get-value via session.model. *)
let treat filename =
  let sexps = SMT2.load_file filename in
  let session    = Session.create 0 in
  let config     = ref None in
  let logic      = ref "" in
  let mode       = ref `MCSAT in
  let support    = ref [] in
  let expected   = ref None in
  let assertions = ref [] in
  let states     = ref [] in
  (* treat sexp:
     - sexp: top-level SMT-LIB2 command
     Handles a subset of commands directly and defers the rest to SMT2 parser. *)
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
          (* support tracks declared variables so get-model prints them in order. *)
          support := yvar :: !support;
          (* print "treat" 2 "@[<2>  declared fun/cst is %a@]@," Term.pp yvar; *)
          Variables.permanently_add session.variables name yvar

        | "assert", [formula] ->
          let formula = ParseTerm.parse session formula |> Yices2.SMT2.Cont.get in
          session.model := None;
          assertions := formula::!assertions

        | "set-logic",  [Atom l]            ->
           print "treat" 3 "@[Setting logic to %s@]@," l;
           logic  := l;
           mode := create_events l;
           config := Some(set_config ~logic:l !mode)

        | "check-sat", [] ->
           begin
             match !config with
             | None ->
                raise (Yices2.SMT2.Yices_SMT2_exception "You need to have (set-logic ...) before (check-sat)")
             | Some config ->
                let formula = Term.(andN !assertions) in
                (* Build the QSMA-tree (Def. 1) and solve from the empty model. *)
                print "treat" 2 "@[<v 2>@[Computing game@]@,";
                let (module G) as game =
                  Game.process config ~global_vars:!support formula
                in
                print "treat" 3 "@[<v 1>Computed game is:@,@[%a@]@]@," Game.pp game;
                print "treat" 2 "@]@,";
                print "treat" 1 "@[<v>";
                Timer.start timer;
                events := List.rev !events;
                current_param := Some (param_from_seed !yseed !logic !mode);
                as_inequalities := (match !mode with `CDCLT `Ineq -> true | _ -> false);
                let rec check_sat config =
                    let state = SolverState.create ~logic:!logic config game in
                    let f () =
                      solve ~compute_over:false state G.top_level (SModel.empty()) Support.Empty
                    in
                    match !events with
                    | [] -> f ()
                    | (timeout_sec, config) :: rest ->
                      let stop () =
                        SolverState.stop state;
                        Atomic.set cancel_flag true
                      in
                      match run_with_timeout ~timeout_sec ~stop f with
                      | Some answer -> answer
                      | None ->
                        apply_slice_config config;
                        let newmode = Option.get_or ~default:!mode config.mode in
                        mode := newmode;
                        print "counter" 1 "@[<v>SWITCH TO %s with random seed %i@]@,"
                          (match newmode with `MCSAT -> "MCSAT" | `CDCLT _ -> "CDCLT")
                          config.seed;
                        current_param := Some (param_from_seed config.seed !logic newmode);
                        as_inequalities := (match newmode with `CDCLT `Ineq -> true | _ -> false);
                        events := rest;
                        Atomic.set cancel_flag false;
                        check_sat (set_config ~logic:!logic newmode)
                in
                let answer, state = check_sat config in
                print "treat" 1 "@]@,";
                let str = return state answer !expected in
                Format.(fprintf stdout) "@[%s@]@," str;
                states := state::!states;
                (* SolverState.free initial_state; *)
                print "treat" 3 "@[Game freed@]@,";
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
