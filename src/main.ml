open Containers
open Sexplib
open Type
open Yices2_high
open Yices2_ext_bindings
open Yices2_SMT2

let verbosity = ref 0
let filedump  = ref None

let print i fs = Format.((if !verbosity >= i then fprintf else ifprintf) stdout) fs

let ppl ~prompt pl fmt l = match l with
  | [] -> ()
  | _::_ -> Format.fprintf fmt "@,@[<v 2>%s %i formula(e)@,%a@]"
              prompt
              (List.length l)
              (List.pp pl) l

let pp_term fmt t = t |> Term.to_sexp |> pp_sexp fmt

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
    Format.fprintf fmt "@[<v 2>%a (with selector %a) opens sub-level@,%a@]"
      pp_term name
      pp_term selector
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
    val namings   : (Term.t * Term.t * Term.t) list
    val top_level : Level.t
  end

  type t = (module T)
  type game = t     

  let pp fmt (module T:T) =
    let open T in
    let pp_naming fmt (u,trigger,formula) =
      Format.fprintf fmt "@[<2>%a (with selector %a) standing for@ %a@]"
        pp_term u
        pp_term trigger
        pp_term formula
    in
    Format.fprintf fmt "@[<v>\
                        @[<2>Ground:@ %a@]@,\
                        @[<2>Namings:@ @[<v>%a@]@]@,\
                        @[<v 2>Levels:@,%a@]\
                        @]"
      pp_term ground
      (List.pp ~sep:"" pp_naming) namings
      Level.pp top_level

  (* The encoding of a formula into a game is done with a state monad,
     where the state is this *)

  type state = {
    newvars : Term.t list;
    foralls : Level.forall list;
    namings : (Term.t * Term.t * Term.t) list
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

  type subst = (Term.t * Term.t) list

  let var_add newvar a state =
    let newvars = newvar::state.newvars in
    a, { state with newvars }

  let bound_counter = ref 0

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

  (* let fresh1 vars body =
   *   let h = HType.create 10 in
   *   let aux subst v =
   *     let typ = Term.type_of_term v in
   *     if HType.mem h typ
   *     then return ((v, HType.find h typ)::subst)
   *     else
   *       begin
   *         let name = fresh_bound() in
   *         let newvar = Term.new_uninterpreted ~name typ in
   *         HType.add h typ newvar;
   *         var_add newvar ((v,newvar)::subst)
   *       end
   *   in
   *   let+ subst = MList.fold aux (return []) vars in
   *   return (Term.subst_term subst body) *)


  exception CannotTreat of Term.t

  let counter = ref 0

  let fa_counter = ref 0

  let fresh_placeholder () =
    let name = "forall_name"^string_of_int !fa_counter in
    incr fa_counter;
    name

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
        if HTerm.mem foralls_rev t
        then
          return(HTerm.find foralls_rev t) (* returns placeholder previously generated *)
        else
          begin
            (* Creating a selector for the forall formula *)
            let name     = fresh_placeholder() in
            let selector = Term.new_uninterpreted ~name (Type.bool()) in
            (* Creating a name for the forall formula *)
            let name     = fresh_placeholder() in
            let name     = Term.new_uninterpreted ~name (Type.bool()) in
            HTerm.add foralls_rev t name;
            (* We instantiate the forall formula ,
               instantiating all bound variables by the same uninterpreted term (per type)
               this is used to produce a "lucky" instance of the formula *)
            (* let+ substituted1 = fresh1 vars body in *)
            (* let+ lucky_instance = aux substituted1 in *)
            (* let t'   = Term.(uninterpreted &&& lucky_instance) in *)
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
            let newnaming = name, selector, SubGame.ground in
            fun state ->
              print 4 "@[<2>Abstracting as %a formula @,%a@]@," pp_term name pp_term t;
              let newvars = name      ::(List.append SubGame.top_level.newvars state.newvars) in
              let foralls = newforall ::(List.append SubGame.top_level.foralls state.foralls) in
              let namings = newnaming ::(List.append SubGame.namings state.namings) in
              name, { newvars; foralls; namings }
          end
      | Bindings { c = `YICES_LAMBDA_TERM } -> raise(CannotTreat t)
      | A0 _ -> return t
      | _ ->
        let+ x = map aux a in return(Term.build x)
    in
    print 5 "@[<2>Traversing term@,%a@]@," pp_term body;
    let id = !counter in
    incr counter;
    let state = { newvars = intro; foralls = []; namings = [] } in
    let ground, { newvars; foralls; namings } = aux body state in
    (module struct
      let top_level =
        let existentials = List.map (fun (u,_,f) -> Term.(u ||| f)) namings in
        let ground = Term.(ground &&& andN existentials) in 
        Level.{id; ground; rigid; newvars; foralls;}
      let ground = ground
      let namings = namings
    end)
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
    | _ -> Format.fprintf fmt "@[<v>%a@]" (List.pp ~sep:"" aux) support

end

module SolverState = struct

  module type T = sig
    include Game.T
    val universals   : Term.t list
    val existentials : Term.t list
    val over  : Term.t list ref (* Models of the game satify ground /\ /\over *)
    val under : Term.t list ref (* Models of ground /\ \/under satisfy the game *)
    val context_over  : Context.t
    val context_under : Context.t
  end

  type t = (module T)

  let pp fmt (module T:T) =
    let open T in
    Format.fprintf fmt "@[<v>\
                        @[%a@]\
                        %a\
                        %a\
                        @]"
      Game.pp (module T)
      (ppl ~prompt:"Over-approximation (\"Learnt\"): conjunction of" pp_term) !over
      (ppl ~prompt:"Under-approximation: disjunction of" pp_term) !under

  let pp_log x fmt (module T:T) =
    let open T in
    let log = match x with
      | `over -> Context.to_sexp context_over
      | `under -> Context.to_sexp context_under
    in
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

  let create config (module G : Game.T) = (module struct
    include G
    let existentials = List.map (fun (u,_,form) -> Term.(u ||| form)) namings
    let universals = List.map (fun (_,trigger,form) -> Term.(trigger ==> form)) namings
    let over   = ref []
    let under  = ref []
    let context_over = Context.malloc ~config ()
    let context_under = Context.malloc ~config ()
    let () = Context.assert_formula context_over ground
    let () = Context.assert_formula context_under ground
    let () = Context.assert_formulas context_over existentials
    let () = Context.assert_formulas context_under existentials
    let () = Context.assert_formulas context_over universals
    let () = Context.assert_formulas context_under universals
  end : T)

  let free (module G : T) =
    Context.free G.context_over;
    Context.free G.context_under;
    Level.free G.top_level
  
end

(* Output for the next function.
   When calling 
     solve game base_support model
   base_support is the support of model,
   and game may involve uninterpreted constants outside base_support
   - If the call outputs Unsat f, it means:
   here is a formula f whose uninterpreted constants are in base_support,
   that is satisfied by model, and that is inconsistent with game.
   - If the call outputs Sat f, it means:
   here is a formula f whose uninterpreted constants are in base_support,
   that is satisfied by model, and that implies game.
*)

type answer =
  | Unsat of Term.t
  | Sat of Term.t
[@@deriving show { with_path = false }]

exception BadInterpolant of SolverState.t * Level.t * Term.t
exception FromYicesException of SolverState.t * Level.t * Types.error_report

let sat_answer (module S:SolverState.T) level model reason =
  let open S in
  print 4 "@[<2>true of model is@ @[<v>%a@]@]@," pp_term reason;
  let true_of_model = Term.(Level.(level.ground) &&& reason) in
  let gen_model =
    Model.generalize_model model true_of_model Level.(level.newvars) `YICES_GEN_DEFAULT
  in
  let answer = Term.(andN gen_model) in
  print 3 "@[<2>Level %i answer on that model is SAT because@ @[%a@]@]" level.Level.id pp_term answer;
  answer


let rec solve state ?selector level model = try
    let (module S:SolverState.T) = state in
    let open S in
    print 1 "@[<v2>Solving game:@,%a@,@[<2>from model@ %a@]@]@," Level.pp level SModel.pp model;
    
    print 4 "@[Trying to solve over-approximations@]@,";
    let status = match model.support with
      | [] -> Context.check context_over
      | _ -> Context.check_with_model context_over model.model model.support
    in
    match status with
    | `STATUS_UNSAT ->
      let interpolant = match model.support with
        | [] -> Term.false0()
        | _ -> Context.get_model_interpolant context_over
      in
      if (Model.get_bool_value model.model interpolant)
      then raise (BadInterpolant(state, level, interpolant));
      let answer = Unsat Term.(not1 interpolant) in
      print 3 "@[<2>Level %i answer on that model is@ @[%a@]@]" level.id pp_answer answer;
      answer

    | `STATUS_SAT ->
      let newmodel = Context.get_model context_over ~keep_subst:true in
      print 4 "@[Found model of over-approx @,@[<v 2>  %a@]@]@,"
        SModel.pp
        SModel.{support = List.append level.rigid level.newvars; model = newmodel }
      ;
      let rec aux reasons = function
        | [] ->
          print 1 "@]@,";
          let reason = Term.andN reasons in
          print 4 "@[Collected reason is %a@]@," pp_term reason;
          if not(List.is_empty reasons) then under := reason::!under;
          Sat(sat_answer state level newmodel reason)
        | o :: opponents when not (Model.get_bool_value newmodel Level.(o.name)) ->
          print 4 "@[Level %i does not need to be looked at as %a is false@]@,"
            o.sublevel.id
            pp_term o.name;
          aux (Term.not1 o.name::reasons) opponents
        | o :: opponents ->
          print 4 "@[Level %i needs to be looked at as %a is true@]@,"
            o.sublevel.id
            pp_term o.name;
          let status =
            Context.check_with_model o.selector_context newmodel o.sublevel.rigid
          in
          assert(Types.equal_smt_status status `STATUS_SAT);
          let newmodel = Context.get_model o.selector_context ~keep_subst:true in
          let support  = o.selector :: o.sublevel.rigid in
          let newmodel = SModel.{ support; model = newmodel } in
          let recurs   = solve state ~selector:o.selector o.sublevel newmodel in
          match recurs with
          | Unsat reason ->
            print 1 "@,";
            let gen_model =
              Model.generalize_model newmodel.model reason [o.name;o.selector] `YICES_GEN_DEFAULT
            in
            aux (List.append gen_model reasons) opponents
          | Sat reason ->
            let gen_model =
              Model.generalize_model newmodel.model reason [o.name] `YICES_GEN_DEFAULT
            in
            let learnt = Term.(o.name ==> not1 (andN gen_model)) in
            let learnt = match selector with
              | Some s -> Term.(s ==> learnt)
              | None -> learnt
            in
            Context.assert_formula context_over learnt;
            print 1 "@]@,";
            print 4 "@[<2>Learnt clause:@,%a@]@," pp_term learnt;
            over := learnt::!over;
            solve state ?selector level model
      in
      print 1 "@[<v 1> ";
      let result = aux [] level.foralls in
      result
    | x -> Types.show_smt_status x |> print_endline; failwith "not good status"
  with
    ExceptionsErrorHandling.YicesException(_,report) ->
    raise (FromYicesException(state, level,report))

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
          let _status    = Context.check env.context in
          let emptymodel = Context.get_model env.context ~keep_subst:true in
          let emptymodel = SModel.{ support = []; model = emptymodel } in
          let initial_state = SolverState.create session.config game in
          print 1 "@[<v>";
          let answer = solve initial_state G.top_level emptymodel in
          print 1 "@]@,";
          let str = match answer, !expected with
            | Unsat _, None -> "unsat?"
            | Sat _, None -> "sat?"
            | Unsat _, Some true -> "unsat!!!!!!!"
            | Sat _, Some false -> "sat!!!!!!!"
            | Unsat _, Some false -> "unsat!"
            | Sat _, Some true -> "sat!"
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


let print_file filename destination x state =
  match !filedump with
  | None -> ()
  | Some prefix ->
    let newfile = Filename.(filename |> remove_extension |> basename) in
    let newfile = match x with
      | `over  -> newfile^".over.smt2"
      | `under -> newfile^".under.smt2"
    in
    let newfile = Filename.(newfile |> concat destination |> concat prefix) in
    Format.(fprintf stdout) "%s@,%!" ("Writing log to "^newfile);
    Format.to_file newfile "@[<v>%a@]" (SolverState.pp_log x) state

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
   | BadInterpolant(state, level, interpolant) as exc ->
     print_file filename "bad_interpolant" `over state;
     copy_file filename "bad_interpolant";
     Format.(fprintf stdout) "Interpolant at level %i:@,%a@," level.Level.id Term.pp interpolant;
     Format.(fprintf stdout) "@]%!";
     raise exc

   | FromYicesException(state, level, report) as exc ->
     print_file filename "yices_exc" `over state;
     print_file filename "yices_exc" `under state;
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


