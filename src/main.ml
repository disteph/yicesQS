open Containers
open Sexplib
open Type
open Yices2_high
open Yices2_ext_bindings
open Yices2_SMT2
open Command_options
open IC

let print i fs = Format.((if !verbosity >= i then fprintf else ifprintf) stdout) fs

let ppl ~prompt pl fmt l = match l with
  | [] -> ()
  | _::_ -> Format.fprintf fmt "@,@[<v 2>%s %i formula(e)@,%a@]"
              prompt
              (List.length l)
              (List.pp pl) l

let pp_term fmt t = t |> Term.to_sexp |> pp_sexp fmt

type subst = (Term.t * Term.t) list

module HType = Hashtbl.Make(Type)
module HTerm = Hashtbl.Make(Term)

module Level = struct

  type t = {
    id : int;
    ground  : Term.t;
    rigid   : Term.t list; (* Eigenvariables that will systematically be set by ancestor games *)
    newvars : Term.t list; (* Eigenvariables to be set by this game, disjoint from above *)
    (* If uninterpreted constant u abstracts away formula (\forall x1...xn neg A), then *)
    foralls : forall list; (* ... (\forall x1..x2 neg A) is turned into an adversarial
                                    game g and (u,g) goes into that list;
                                    these games are the children game of the current game *)
  }
  and forall = {
      name : Term.t;
      selector : Term.t;
      selector_context : Context.t;
      sublevel : t
    }


  let rec pp fmt {id; rigid; newvars; foralls}
    = Format.fprintf fmt "@[<v>\
                          Level id: %i@,\
                          %i ancestors' variables: @[<hov>%a@]@,\
                          %i free variables: @[<hov>%a@]\
                          %a@]"
      id
      (List.length rigid)
      (List.pp ~sep:" " pp_term) rigid
      (List.length newvars)
      (List.pp ~sep:" " pp_term) newvars
      pp_foralls foralls
  and pp_forall fmt {name; selector; sublevel} =
    Format.fprintf fmt "@[<v 2>%a opens sub-level@,%a@]"
      pp_term name
      pp sublevel
  and pp_foralls fmt = function
    | [] -> ()
    | foralls -> Format.fprintf fmt "@,@[<v2>%i ∀-formula(e) / sub-level(s):@,%a@]"
                   (List.length foralls) (List.pp ~sep:"" pp_forall) foralls

  let rec free level =
    List.iter free_forall level.foralls
  and free_forall {selector_context; sublevel} =
    Context.free selector_context;
    free sublevel
    
end

module Game = struct

  module type T = sig
    val ground    : Term.t (* Ground abstraction of the game, as a quantifier-free formula *)
    val existentials : Term.t list
    val universals   : Term.t list
    val top_level : Level.t
  end

  type t = (module T)
  type game = t     

  let pp fmt (module T:T) =
    let open T in
    Format.fprintf fmt "@[<v>\
                        @[<2>Ground:@ %a@]@,\
                        @[<2>Existentials:@ @[<v>%a@]@]@,\
                        @[<v 2>Levels:@,%a@]\
                        @]"
      pp_term ground
      (List.pp ~sep:"" pp_term) existentials
      Level.pp top_level

  (* The encoding of a formula into a game is done with a state monad,
     where the state is this *)

  type state = {
    newvars : Term.t list;
    foralls : Level.forall list;
    existentials : Term.t list;
    universals   : Term.t list
  }

  (* The state monad *)

  module StateMonad = struct
    type 'a t = state -> 'a * state
    let return a s = a,s
    let bind a f s = let a,s = a s in f a s
    let (let+) = bind 
  end
  open StateMonad

  (* Monadic fold and map *)
  module MList = MList(StateMonad)
  include MTerm(StateMonad)

  let var_add newvar a state =
    let newvars = newvar::state.newvars in
    a, { state with newvars }

  let bound_counter = ref 1

  let fresh_bound () : string =
    let name = "y!"^string_of_int !bound_counter in
    incr bound_counter;
    name

  let fresh rigid bound body : Term.t * Term.t list * Term.t list =
    let aux (subst, rigid, newvars) v =
      let typ = Term.type_of_term v in
      let name = fresh_bound() in
      let newvar = Term.new_uninterpreted ~name typ in
      ((v,newvar)::subst), (newvar::rigid), (newvar::newvars)
    in
    let subst, rigid, newvars = List.fold_left aux ([], rigid, []) bound in
    Term.subst_term subst body, rigid, newvars

  exception CannotTreat of Term.t

  let counter = ref 0

  let foralls_rev = HTerm.create 10

  (* rigidintro = rigid + intro *)
  let rec process config ~rigidintro ~rigid ~intro body : game =

    let rec aux t : Term.t StateMonad.t =
      let Term a = Term.reveal t in
      match a with
      | Bindings { c = `YICES_FORALL_TERM;
                   vars;
                   body }
        ->
        if false
        then
          return(HTerm.find foralls_rev t) (* returns placeholder previously generated *)
        else
          begin
            (* Creating a selector for the forall formula *)
            incr counter;
            let freshcount = string_of_int !counter in
            let name  = "trig"^freshcount in
            let selector = Term.new_uninterpreted ~name (Type.bool()) in
            (* Creating a name for the forall formula *)
            let name  = "name"^freshcount in
            let name  = Term.new_uninterpreted ~name (Type.bool()) in
            HTerm.add foralls_rev t name;
            let substituted, rigidintro_sub, intro_sub = fresh rigidintro vars body in
            let (module SubGame) =
              process config
                ~rigidintro:rigidintro_sub
                ~rigid:rigidintro
                ~intro:intro_sub
                (Term.not1 substituted) in
            let selector_context = Context.malloc ~config () in
            Context.assert_formula selector_context selector;
            let newforall =
              Level.{ name; selector; selector_context; sublevel = SubGame.top_level }
            in
            let existential = Term.(name ||| SubGame.ground) in
            let universal   = Term.(selector === SubGame.ground) in
            fun state ->
              print 5 "@[<2>Abstracting as %a formula @,%a@]@," pp_term name pp_term t;
              let newvars = List.append SubGame.top_level.newvars (name::selector::state.newvars) in
              let foralls = List.append SubGame.top_level.foralls (newforall::state.foralls) in
              let existentials = List.append SubGame.existentials (existential::state.existentials) in
              let universals   = List.append SubGame.universals   (universal::state.universals) in
              name, { newvars; foralls; existentials; universals }
          end
      | Bindings { c = `YICES_LAMBDA_TERM } -> raise(CannotTreat t)
      | A0 _ -> return t
      | _ ->
        let+ x = map aux a in return(Term.build x)
    in
    print 5 "@[<2>Traversing term@,%a@]@," pp_term body;
    let id = !counter in
    let state = { newvars = intro; foralls = []; existentials = []; universals = []; } in
    let ground, { newvars; foralls; existentials; universals } = aux body state in
    let foralls = List.rev foralls in
    (module struct
      let top_level = Level.{id; ground = Term.(ground &&& andN existentials); rigid; newvars; foralls;}
      let ground = ground
      let existentials = existentials
      let universals = universals
    end)
end

module SolverState = struct

  module type T = sig
    include Game.T
    val universals   : Term.t list
    val existentials : Term.t list
    val context           : Context.t (* Main context for the solver *)
    val epsilons_context  : Context.t (* context with only epsilon term constraints at level 0 *)
    (* val learnt : Term.t list ref *)
  end

  type t = (module T)

  let pp fmt (module T:T) =
    let open T in
    Format.fprintf fmt "@[<v>\
                        @[%a@]\
                        @]"
      Game.pp (module T)

  let pp_log_raw fmt ((module T:T),log) =
    let open T in
    let intro sofar t =
      let typ = Term.type_of_term t in
      let sexp = List[Atom "declare-fun"; Term.to_sexp t; List[]; Type.to_sexp typ] in
      sexp::sofar
    in
    let log = List.fold_left intro log top_level.newvars in
    let log = List.fold_left intro log top_level.rigid in
    let sl     = List[Atom "set-logic";  Atom "QF_BV"] in
    let option = List[Atom "set-option"; Atom ":produce-unsat-model-interpolants"; Atom "true"] in
    Format.fprintf fmt "@[<v>%a@]" (List.pp ~sep:"" pp_sexp) (option::sl::log)

  let pp_log fmt ((module T:T) as state) =
    let open T in
    let log = Context.to_sexp context in
    pp_log_raw fmt (state,log)
    
  let create config (module G : Game.T) = (module struct
    include G
    let epsilons_context = Context.malloc ~config ()
    let context          = Context.malloc ~config ()
    let () = Context.assert_formula context ground
    let () = Context.assert_formulas context existentials
    let () = Context.assert_formulas context universals
    (* let learnt = ref [] *)
  end : T)

  let learn (module S : T) lemmas =
    (* learnt := List.append lemma !S.learnt; *)
    print 4 "@[<2>Learning %a@]@," (List.pp pp_term) lemmas;
    Context.assert_formulas S.context lemmas

  let record_epsilons ((module S : T) as state) epsilons =
    print 3 "@[<v2>Recording epsilons @[<v2>  %a@]@]@,"
      (List.pp Term.pp) epsilons;
    (* Context.assert_formulas S.epsilons_context epsilons; *)
    learn state epsilons

  let free (module G : T) =
    Context.free G.context;
    Level.free G.top_level
  
end

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

(* Supported models *)
module SModel = struct

  type t = {
    support : Term.t list;
    model   : Model.t
  }

  let pp fmt {support;model} =
    let aux fmt u =
      let v = Model.get_value_as_term model u in
      Format.fprintf fmt "@[%a := %a@]" pp_term u pp_term v
    in
    match support with
    | [] -> Format.fprintf fmt "[]"
    | support -> Format.fprintf fmt "@[<v>%a@]" (List.pp ~sep:"" aux) support

end


(* Output for the next function.
   When calling 
     solve game base_support model
   base_support is the support of model,
   and game may involve uninterpreted constants outside base_support
   - If the call outputs Unsat f, it means:
   here is a formula f whose uninterpreted constants are in base_support,
   that is satisfied by model, and that is inconsistent with game.
   - If the call outputs Sat l, it means:
   each formula f in the list of formulae f has its uninterpreted constants in base_support,
   is satisfied by model, and implies game.
*)

type answer =
  | Unsat of Term.t
  | Sat of Term.t list
[@@deriving show { with_path = false }]

exception BadInterpolant of SolverState.t * Level.t * Term.t
exception BadUnder of SolverState.t * Level.t * Term.t
exception FromYicesException of SolverState.t * Level.t * Types.error_report
exception WrongAnswer of SolverState.t * answer

module THash = Hashtbl.Make'(Term)
    
let build_table model oldvar newvar =
  let tbl = THash.create (List.length newvar * 10) in
  let treat_new var =
    let value = Model.get_value_as_term model var in
    match THash.find_opt tbl value with
    | Some _ -> ()
    | None   -> THash.add tbl value []
  in
  List.iter treat_new newvar;
  let treat_old var =
    let value = Model.get_value_as_term model var in
    match THash.find_opt tbl value with
    | Some l -> THash.replace tbl value (var::l)
    | None   -> ()
  in
  List.iter treat_old oldvar;
  tbl

let generalize_model model formula_orig oldvar newvar : (Term.t * Term.t list) LazyList.t =
  let formula, epsilons = IC.solve_all newvar formula_orig in
  print 3 "@[<v2>Formula sent to IC is %a@]@," pp_term formula_orig;
  print 3 "@[<v2>Formula returned by IC is %a@]@," pp_term formula;
  (* let epsilons = [] in *)
  let tbl = build_table model oldvar newvar in
  let rec aux1 list : subst LazyList.t = match list with
    | []      -> LazyList.return []
    | (var, value, terms)::other_vars ->
      print 3 "@[<v2>Trying to eliminate variable %a, with value %a and matching variables %a@]@,"
        pp_term var
        pp_term value
        (List.pp pp_term) terms;
      let rest = aux1 other_vars in
      let rec aux2 = function
        | []    -> LazyList.map (fun subst -> (var,value)::subst) rest
        | t::tl -> LazyList.append (LazyList.map (fun subst -> (var,t)::subst) rest) (aux2 tl) 
      in
      aux2 terms
  in
  let aux var =
    let value = Model.get_value_as_term model var in
    var, value, THash.find tbl value
  in
  let substs = newvar |> List.map aux |> aux1 in
  let aux subst =
    Term.subst_term subst formula,
    Term.subst_terms subst epsilons
  in
  LazyList.map aux substs

(* let check state level model support reason =
 *   let (module S:SolverState.T) = state in
 *   print 3 "@[<v2>Checking that our model %a@,satisfies reason %a@]@,"
 *     SModel.pp { model; support }
 *     pp_term reason;
 *   Context.push S.epsilons_context;
 *   Context.assert_formula S.epsilons_context (Term.not1 reason);
 *   match Context.check_with_model S.epsilons_context model support with
 *   | `STATUS_SAT   ->
 *     print 3 "@[<v2>It does not satisfy it@]@,";
 *     raise (BadUnder(state, level, reason))
 *   | `STATUS_UNSAT ->
 *     print 3 "@[<v2>It does satisfy it@]@,";
 *     Context.pop S.epsilons_context
 *   | _ -> assert false *)

let rec solve state level model support : answer = try
    let (module S:SolverState.T) = state in
    let open S in
    print 1 "@[<v2>Solving game:@,%a@,@[<2>from model@ %a@]@]@,"
      Level.pp level
      SModel.pp { model; support = Support.list support };

    print 4 "@[Trying to solve over-approximations@]@,";
    let status = match support with
      | Empty -> Context.check context
      | S _   -> Context.check_with_model context model (Support.list support)
    in
    match status with

    | `STATUS_UNSAT ->
      let interpolant = match support with
        | Empty -> Term.false0()
        | S _   -> Context.get_model_interpolant context
      in
      if (Model.get_bool_value model interpolant)
      then raise (BadInterpolant(state, level, interpolant));
      if Term.(equal interpolant (false0()))
      && not(Types.equal_smt_status (Context.check context) `STATUS_UNSAT)
      then raise (BadInterpolant(state, level, interpolant));
      let answer = Unsat Term.(not1 interpolant) in
      print 3 "@[<2>Level %i answer on that model is@ @[%a@]@]" level.id pp_answer answer;
      answer

    | `STATUS_SAT ->
      let model = Context.get_model context ~keep_subst:true in
      print 4 "@[Found model of over-approx @,@[<v 2>  %a@]@]@,"
        SModel.pp SModel.{support = List.append level.newvars (Support.list support); model };
      post_process state level model support
    | x -> Types.show_smt_status x |> print_endline; failwith "not good status"

  with
    ExceptionsErrorHandling.YicesException(_,report) ->
    raise (FromYicesException(state, level,report))

and post_process state level model support =
  print 1 "@[<v 1> ";
  let result = treat_sat state level model support in
  print 1 "@]@,";
  match result with
  | Some underapprox -> Sat underapprox
  | None -> solve state level model support

and treat_sat state level model support =
  let (module S:SolverState.T) = state in
  let open S in

  (* Now we look at each forall formula that we have to satisfy, one by one *)
  let rec aux model cumulated_support reasons = function

    (* We have satisfied all forall formulae; our model is good! *)
    | [] ->
      let reasons = Level.(level.ground)::reasons in
      (* We first aggregate the reasons why our model worked *)
      (* Any model satisfying true_of_model would have been a good model *)
      let true_of_model = Term.andN reasons in
      print 4 "@[<2>true of model is@ @[<v>%a@]@]@," pp_term true_of_model;
      (* Now compute several projections of the reason on the rigid variables *)
      let seq =
        generalize_model model true_of_model Level.(level.rigid) Level.(level.newvars)
      in
      let rec extract (accu : Term.t list) (epsilons : Term.t list) n l : Term.t list * Term.t list =
        if n <= 0 then accu, epsilons
        else
          match Lazy.force l with
          | `Nil -> accu, epsilons
          | `Cons((head, epsilons_local), tail) -> 
            match epsilons_local, epsilons with
            | [], epsilons
            | epsilons, [] -> extract (head::accu) epsilons (n-1) tail
            | _::_, _::_   -> extract accu epsilons (n-1) tail
      in
      let underapprox, epsilons = extract [] [] !underapprox seq in
      SolverState.record_epsilons state epsilons;
      print 3 "@[<v2>Level %i model works, with reason@,@[<v2>  %a@]@]@,"
        level.id
        (List.pp pp_term)
        underapprox;
      Some underapprox

    (* Here we have a forall formula o that is false in the model;
       the reason why we don't have to look at it is that o is false in the model. *)
    | o :: opponents when not (Model.get_bool_value model Level.(o.name)) ->
      print 4 "@[Level %i does not need to be looked at as %a is false@]@,"
        o.sublevel.id
        pp_term o.name;
      aux model (o.name::cumulated_support) (Term.not1 o.name::reasons) opponents

    (* Here we have a forall formula o that is true in the model;
       we have to make a recursive call to play the corresponding sub-game *)
    | o :: opponents ->
      print 4 "@[Level %i needs to be looked at as %a is true@]@,"
        o.sublevel.id
        pp_term o.name;

      let open Level in

      (* To the recursive call, we will feed values for the following variables *)
      let recurs_support = Support.S{ trigger = o.selector; variables = o.sublevel.rigid } in

      (* Now we produce the model to feed the recursive call and perform the call.
         We get back the status of the call and the model that we fed to it *)
      let recurs_status, recurs_model =
        if Model.get_bool_value model o.selector
        then (* The selector for this subformula is already true *)
          (print 4 "@[Model already makes %a true, we stick to the same model@]@,"
             pp_term o.selector;
           post_process state o.sublevel model recurs_support, model)
        else
        (* We extend the model by setting the selector to true *)
        let status =
          Context.check_with_model o.selector_context model o.sublevel.rigid
        in
        (* This should always work *)
        assert(Types.equal_smt_status status `STATUS_SAT);
        (* This is the extended model *)
        let recurs_model = Context.get_model o.selector_context ~keep_subst:true in
        solve state o.sublevel recurs_model recurs_support, recurs_model

      in
      (* elim_trigger eliminates the trigger variable from the explanations given by the
         recursive call *)
      let elim_trigger reason = Term.subst_term [o.selector,Term.true0()] reason in
      match recurs_status with
      | Unsat reason ->
        begin
          print 1 "@,";
          print 4 "@[<v2>Back to level %i, we see from level %i answer Unsat with reason@,@[%a@]@]@,"
            level.id
            o.sublevel.id
            pp_term reason;
          (* We first eliminate the trigger from the reason... *)
          let reason = elim_trigger reason in
          print 4 "@[Reason's projection is %a@]@," pp_term reason;
          (* ...and check that our current model indeed satisfies it. *)
          (* check state level model o.sublevel.rigid reason; *)
          (* next moves on to the next opponent;
             with a cumulated support and a model that may updated with what we've learnt. *)
          let next cumulated_support model =
            (* we add the reason and continue with the next opponents *)
            aux model cumulated_support (reason::reasons) opponents
          in
          match opponents with
          | _ -> next cumulated_support model (* This was the last opponent. *)
          | _::_ ->
            (* If there is another opponent coming, we may want to update our current model
               according to the lemmas we've learnt from the recursive call
               and that our current model may be violating. *)
            (* We first augment the cumulated support with those variables that matter for
               reason to hold *)
            let var_that_matter = Model.model_term_support model reason in
            (* Then we add them to the cumulative support *)
            let cumulated_support =
              List.sorted_merge_uniq ~cmp:Term.compare var_that_matter cumulated_support
            in
            print 4 "@[Now checking whether our model %a violates anything we have learnt@]@,"
              SModel.pp { model; support = cumulated_support };
            match Context.check_with_model context model cumulated_support with
            | `STATUS_SAT  ->
              Context.get_model context ~keep_subst:true |> next cumulated_support
            | `STATUS_UNSAT -> 
              print 4 "@[We learned something that defeats this model@]@,";
              None
            | _             -> assert false
        end
      | Sat reasons ->
        print 4 "@[<v2>Back to level %i, we see from level %i answer Sat with reasons@,@[%a@]@]@,"
          level.id
          o.sublevel.id
          (List.pp pp_term) reasons;
        assert(List.length reasons > 0);
        let aux reason =
          let reason = elim_trigger reason in
          (* check state level model o.sublevel.rigid reason; *)
          let lemma = Term.(o.name ==> not1 reason) in
          SolverState.learn state [lemma]
        in
        List.iter aux reasons;
        None
  in
  let cumulated_support = match support with
    (* If our own support is not empty, the first element is our own trigger:
       we keep it as well as the values passed to the recursive call but its own trigger *)
    | S{ trigger } -> [trigger]
    | Empty -> [] (* otherwise we just keep those values *)
  in
  aux model cumulated_support [] level.foralls


let () = assert(Global.has_mcsat())

let treat filename =
  let sexps = SMT2.load_file filename in
  let set_logic logic config =
    print 3 "@[Setting logic to %s@]@," logic;
    Config.set config ~name:"solver-type" ~value:"mcsat";
    Config.set config ~name:"mode" ~value:"multi-checks"
  in
  let session = Session.create ~set_logic 0 in
  let support       = ref [] in
  let expected      = ref None in
  let assertions    = ref [] in
  let treat sexp =
    match sexp with
    | List(Atom head::args) ->
      print 1 "@[<2>Traversing sexp@ %a@]@," pp_sexp sexp;
      begin
        match head, args, !(session.env) with
        | "set-info",   [Atom ":status"; Atom "sat"],   _ ->
          expected := Some true

        | "set-info",   [Atom ":status"; Atom "unsat"],   _ ->
          expected := Some false

        | "declare-fun", [Atom name; List []; typ], Some env
        | "declare-const", [Atom name; typ], Some env ->
          let ytype = ParseType.parse env.types typ |> Cont.get in
          let yvar = Term.new_uninterpreted ~name ytype in
          support := yvar :: !support;
          (* print 2 "@[<2>  declared fun/cst is %a@]@," pp_term yvar; *)
          Variables.permanently_add env.variables name yvar

        | "assert", [formula], Some env ->
          let formula = ParseTerm.parse env formula |> Cont.get in
          (* print 2 "@[<2>Asserting formula@,%a@]@," pp_term formula; *)
          (match env.model with
           | Some model -> Model.free model
           | None -> ());
          assertions := formula::!assertions

        | "check-sat", [], Some env ->
          let formula = Term.(andN !assertions) in
          print 2 "@[<v 2>@[Computing game@]@,";
          let (module G) as game = Game.process session.config
              ~rigidintro:!support
              ~rigid:[]
              ~intro:!support
              formula
          in
          print 3 "@[<v 1>Computed game is:@,@[%a@]@]@," Game.pp game;
          print 2 "@]@,";
          let initial_state = SolverState.create session.config game in
          print 1 "@[<v>";
          let answer = solve initial_state G.top_level (Model.from_map []) Support.Empty in
          print 1 "@]@,";
          let str = match answer, !expected with
            | Unsat _, None -> "unsat?"
            | Sat _, None -> "sat?"
            | Unsat _, Some false -> "unsat!"
            | Sat _, Some true -> "sat!"
            | Unsat _, Some true 
            | Sat _, Some false -> raise (WrongAnswer(initial_state, answer))
          in
          Format.(fprintf stdout) "@[%s@]@," str;
          (* SolverState.free initial_state; *)
          print 3 "@[Game freed@]@,";

        | "exit", [], _ ->
          print 1 "@[Exiting@]@,"; ()
          (* Session.exit session *)

        | _ -> ParseInstruction.parse session sexp

      end
    | _ -> ParseInstruction.parse session sexp
  in
  List.iter treat sexps;
  print 1 "@[Exited gracefully@]@,"

let print_file filename destination state =
  match !filedump with
  | None -> ()
  | Some prefix ->
    let newfile = Filename.(filename |> remove_extension |> basename) in
    let newfile = newfile^".trace.smt2" in
    let newfile = Filename.(newfile |> concat destination |> concat prefix) in
    Format.(fprintf stdout) "%s@,%!" ("Writing log to "^newfile);
    Format.to_file newfile "@[<v>%a@]" SolverState.pp_log state

let copy_file filename destination =
  match !filedump with
  | None -> ()
  | Some prefix ->
    let newfile = Filename.(filename |> basename |> concat destination |> concat prefix) in
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
     treat filename;
     Format.(fprintf stdout) "@]%!";
   with
   | BadInterpolant((module S : SolverState.T) as state, level, interpolant) as exc ->
     let destination = "bad_interpolant" in
     print_file filename destination state;
     copy_file filename destination;
     begin
       match !filedump with
       | None -> ()
       | Some prefix ->
         let newfile = Filename.(filename |> remove_extension |> basename) in
         let newfile = newfile^".interpolant_check.smt2" in
         let newfile = Filename.(newfile |> concat destination |> concat prefix) in
         Format.(fprintf stdout) "%s@,%!" ("Writing interpolant-check to "^newfile);
         let rec aux = function
           | [check_with_model;_] -> [check_with_model]
           | _::tail -> aux tail
           | _ -> assert false
         in
         let log = Context.to_sexp S.context |> aux in
         let log = Action.(AssertFormula interpolant |> to_sexp log) in 
         Format.to_file newfile "@[<v>%a@]" SolverState.pp_log_raw (state,log)
     end;
     Format.(fprintf stdout) "Interpolant:@,%a@," pp_term interpolant;
     Format.(fprintf stdout) "@]%!";
     raise exc

   | BadUnder((module S : SolverState.T) as state, level, under) as exc ->
     let destination = "bad_under" in
     print_file filename destination state;
     copy_file filename destination;
     begin
       match !filedump with
       | None -> ()
       | Some prefix ->
         let newfile = Filename.(filename |> remove_extension |> basename) in
         let newfile = newfile^".under_check.smt2" in
         let newfile = Filename.(newfile |> concat destination |> concat prefix) in
         Format.(fprintf stdout) "%s@,%!" ("Writing under-check to "^newfile);
         let rec aux = function
           | [check_with_model;_] -> [check_with_model]
           | _::tail -> aux tail
           | _ -> assert false
         in
         let log = Context.to_sexp S.context |> aux in
         let log = Action.(AssertFormula under |> to_sexp log) in 
         Format.to_file newfile "@[<v>%a@]" SolverState.pp_log_raw (state,log)
     end;
     Format.(fprintf stdout) "Under:@,%a@," pp_term under;
     Format.(fprintf stdout) "@]%!";
     raise exc

   | WrongAnswer(state, answer) as exc ->
     print_file filename "wrong" state;
     copy_file filename "wrong";
     Format.(fprintf stdout) "@[Wrong answer!: %a@]@," pp_answer answer;
     Format.(fprintf stdout) "@]%!";
     raise exc

   | FromYicesException(state, level, report) as exc ->
     print_file filename "yices_exc" state;
     copy_file filename "yices_exc";
     Format.(fprintf stdout) "@[Yices error at level %i: @[%s@]@]@,"
       level.Level.id
       (ErrorPrint.string());
     Format.(fprintf stdout) "@[Error report:@,@[<v2>  %a@]@]@,"
       Types.pp_error_report report;
     Format.(fprintf stdout) "@]%!";
     raise exc

   | Yices_SMT2_exception s as exc ->
     copy_file filename "SMT_exc";
     Format.(fprintf stdout) "@[SMT2 error: %s@]@," s;
     Format.(fprintf stdout) "@]%!";
     raise exc

  )
| [] -> failwith "Too few arguments in the command"
| _ -> failwith "Too many arguments in the command";;


