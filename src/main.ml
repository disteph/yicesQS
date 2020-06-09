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

module Game = struct  
  type t = {
    id : int;
    rigid   : Term.t list; (* Eigenvariables that will systematically be set by ancestor games *)
    newvars : Term.t list; (* Eigenvariables to be set by this game, disjoint from above *)
    ground  : Term.t;      (* Ground abstraction of the game, as a quantifier-free formula *)
    over    : Term.t list ref; (* Models of the game satify ground /\ /\over *)
    under   : Term.t list ref; (* Models of ground /\ \/under satisfy the game *)
    (* If uninterpreted constant u abstracts away formula (\forall x1...xn A), then *)
    foralls : (Term.t * t) list; (* ... (\forall x1..x2 A) is turned into an adversarial game g
                                      and (u,g) goes into that list;
                                      these games are the children game of the current game *)
    context_over  : Context.t; (* A Yices context that tries to satisfy ground /\ /\over *)
    context_under : Context.t; (* A Yices context that tries to satisfy ground /\ \/under *)
  }

  type game = t
  
  let rec pp fmt {id; rigid; newvars; ground; under; over; foralls}
    = Format.fprintf fmt "@[<v>@[Game id: %i@]@,\
                          @[Ancestors' variables %i: %a@]@,\
                          @[Free variables %i: %a@]@,\
                          @[Ground: %a@]\
                          %a\
                          %a\
                          %a@]"
      id
      (List.length rigid)
      (List.pp pp_term) rigid
      (List.length newvars)
      (List.pp pp_term) newvars
      pp_term ground
      (ppl ~prompt:"Over-approximation (\"Learnt\"): conjunction of" pp_term) !over
      (ppl ~prompt:"Under-approximation: disjunction of" pp_term) !under
      (ppl ~prompt:"Foralls:" pp_forall) foralls
  and pp_forall fmt (u,game) =
    Format.fprintf fmt "@[<v 2>%a standing for@,%a@]" pp_term u pp game

  let pp_log x fmt game =
    let log = match x with
      | `over -> Context.to_sexp game.context_over
      | `under -> Context.to_sexp game.context_under
    in
    let intro sofar t =
      let typ = Term.type_of_term t in
      let sexp = List[Atom "declare-fun"; Term.to_sexp t; List[]; Type.to_sexp typ] in
      sexp::sofar
    in
    let log = List.fold_left intro log game.newvars in
    let log = List.fold_left intro log game.rigid in
    let sl = List[Atom "set-logic"; Atom "QF_BV"] in
    let option = List[Atom "set-option"; Atom ":produce-unsat-model-interpolants"; Atom "true"] in
    Format.fprintf fmt "@[<v>%a@]" (List.pp ~sep:"" pp_sexp) (option::sl::log)

  let free {context_over; context_under } =
    Context.free context_over;
    Context.free context_under
  
  let free game =
    let aux (_,g) = free g in
    List.iter aux game.foralls;
    free game

  let rec search_sub_game i game = 
    if game.id = i then Some game
    else
      let rec aux = function
        | [] -> None
        | (_,sgame)::tail ->
          match search_sub_game i sgame with
          | Some _ as x -> x
          | None -> aux tail
      in
      aux game.foralls
  
  (* The encoding of a formula into a game is done with a state monad,
     where the state is this *)

  type state = {
    newvars : Term.t list;
    foralls : (Term.t * t) list;
    existentials : Term.t list;
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
    let name = "forall_placeholder"^string_of_int !fa_counter in
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
            (* We create a name for the forall formula *)
            let name = fresh_placeholder() in
            let uninterpreted = Term.new_uninterpreted ~name (Type.bool()) in
            (* We instantiate the forall formula ,
               instantiating all bound variables by the same uninterpreted term (per type)
               this is used to produce a "lucky" instance of the formula *)
            (* let+ substituted1 = fresh1 vars body in *)
            (* let+ lucky_instance = aux substituted1 in *)
            (* let t'   = Term.(uninterpreted &&& lucky_instance) in *)
            let substituted, rigidintro_sub, intro_sub = fresh rigidintro vars body in
            let subgame = process config ~rigidintro:rigidintro_sub ~rigid:rigidintro ~intro:intro_sub (Term.not1 substituted) in
            let t'      = uninterpreted in
            HTerm.add foralls_rev t t';
            fun state ->
              print 4 "@[Abstracting @[%a@], which becomes @[%a@]@]@," pp_term t pp_term t';
              let newvars = uninterpreted           ::(List.append subgame.newvars state.newvars) in
              let foralls = (uninterpreted, subgame)::(List.append subgame.foralls state.foralls) in
              let existentials = Term.(subgame.ground ||| uninterpreted)::state.existentials in
              t', { newvars; foralls; existentials }
          end
      | Bindings { c = `YICES_LAMBDA_TERM } -> raise(CannotTreat t)
      | A0 _ -> return t
      | _ ->
        let+ x = map aux a in return(Term.build x)
    in
    print 5 "@[Traversing term @[%a@]@]@," pp_term body;
    let id = !counter in
    incr counter;
    let state = { newvars = intro; foralls = []; existentials = [] } in
    let ground, { newvars; foralls; existentials } = aux body state in
    let over   = ref [] in
    let under  = ref [] in
    let context_over = Context.malloc ~config () in
    Context.assert_formula context_over ground;
    Context.assert_formulas context_over existentials;
    let context_under = Context.malloc ~config () in
    Context.assert_formula context_under ground;
    Context.assert_formulas context_under existentials;
    let ground  = Term.(ground &&& andN existentials) in
    { id; rigid; newvars; ground; over; under; foralls; context_over; context_under }

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
    | [] -> Format.fprintf fmt " []"
    | _::_ -> Format.fprintf fmt "@,@[<v>%a@]" (List.pp aux) support

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

exception BadInterpolant of Game.t * Term.t
exception FromYicesException of Game.t * Types.error_report

let sat_answer x game reason =
  let open Game in
  let model = match x with
    | `over  -> Context.get_model game.context_over ~keep_subst:true
    | `under -> Context.get_model game.context_under ~keep_subst:true
  in
  let true_of_model = Term.(reason &&& game.ground) in
  print 4 "@[true of model is @[<v>   %a@]@]" pp_term true_of_model;
  let gen_model =
    Model.generalize_model model true_of_model game.newvars `YICES_GEN_DEFAULT
  in
  let answer = Term.(andN gen_model) in
  print 3 "@[Game %i answer on that model is SAT because %a@]" game.id Term.pp answer;
  answer


let rec solve game model = try
    print 1 "@[<v 3>@[Solving game:@]@,%a@,from model%a@]@," Game.pp game SModel.pp model;

    print 4 "@[Trying to solve over-approximations@]@,";
    match Context.check_with_model game.context_over model.model model.support with
    | `STATUS_UNSAT ->
      let interpolant = Context.get_model_interpolant game.context_over in
      if (Model.get_bool_value model.model interpolant)
      then raise (BadInterpolant(game, interpolant));
      let answer = Unsat Term.(not1 interpolant) in
      print 3 "@[Game %i answer on that model is %a@]" game.id pp_answer answer;
      answer

    | `STATUS_SAT ->
      let newmodel = Context.get_model game.context_over ~keep_subst:true in
      print 4 "@[Found model of over-approx @[<v 2>  %a@]@]@,"
        SModel.pp
        SModel.{support = List.append game.rigid game.newvars; model = newmodel }
      ;

      print 4 "@[Trying to solve under-approximations@]@,";
      let rec under_solve = function
        | [] -> None
        | under_i::tail ->
          Context.push game.context_under;
          Context.assert_formula game.context_under under_i;
          match Context.check_with_model game.context_under model.model model.support with
          | `STATUS_UNSAT -> Context.pop game.context_under; under_solve tail 
          | `STATUS_SAT   ->
            let term = sat_answer `under game under_i in
            Context.pop game.context_under;
            Some term
          | x -> Types.show_smt_status x |> print_endline; failwith "not good status"
      in
      begin
        match under_solve !(game.under) with
        | Some term -> Sat term
        | None ->
          print 4 "@[Solving over- and under-approximations was not interesting; looking at subgames.@]@,";
          let rec aux reasons = function
            | [] ->
              let reason = Term.andN reasons in
              if not(List.is_empty reasons) then game.under := reason::!(game.under);
              Sat(sat_answer `over game reason)
            | (u,_)::opponents when not (Model.get_bool_value newmodel u)
              -> aux (Term.not1 u::reasons) opponents
            | (u,opponent)::opponents ->
              print 1 "@[<v 1> ";
              let recurs = solve opponent { support = opponent.rigid; model = newmodel} in
              print 1 "@]@,";
              match recurs with
              | Unsat reason -> aux (reason::reasons) opponents
              | Sat reason ->
                let learnt = Term.(u ==> not1 reason) in
                Context.assert_formula game.context_over learnt;
                Context.assert_formula game.context_under learnt; (* Not necessary; useful? *)
                game.over := learnt::!(game.over);
                solve game model
          in
          aux [] game.foralls
      end
    | x -> Types.show_smt_status x |> print_endline; failwith "not good status"
  with
    ExceptionsErrorHandling.YicesException(_,report) ->
    raise (FromYicesException(game,report))

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
      print 1 "@[Traversing sexp @[%a@]@]@," Sexplib.Sexp.pp sexp;
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
          print 2 "@[<v>declared fun/cst is %a@]@," pp_term yvar;
          Variables.permanently_add env.variables name yvar

        | "assert", [formula], Some env ->
          let formula = ParseTerm.parse env formula |> Cont.get in
          print 2 "@[Asserting formula @[<1>%a@]@]@," pp_term formula;
          (match env.model with
           | Some model -> Model.free model
           | None -> ());
          assertions := formula::!assertions

        | "check-sat", [], Some env ->
          let formula = Term.(andN !assertions) in
          print 2 "@[<v 2>@[Computing game@]@,";
          let game = Game.process session.config
              ~rigidintro:!support
              ~rigid:[]
              ~intro:!support
              formula
          in
          print 3 "@[<v 1>@[Computed game is:@]@,@[%a@]@]@,%!" Game.pp game;
          print 2 "@]@,";
          let _status = Context.check env.context in
          let emptymodel = Context.get_model env.context ~keep_subst:true in
          let emptymodel = SModel.{ support = []; model = emptymodel } in
          print 1 "@[<v>";
          let answer = solve game emptymodel in
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
          Game.free game;
          print 3 "@[Game freed@]@,";

        | "exit", [], _ ->
          print 1 "@[Exiting@]@,";
          Session.exit session

        | _ -> ParseInstruction.parse session sexp

      end
    | _ -> ParseInstruction.parse session sexp
  in
  List.iter treat sexps;
  print 1 "@[Exited gracefully@]@,"


let print_file filename destination x game =
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
    Format.to_file newfile "@[<v>%a@]" (Game.pp_log x) game

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
   | BadInterpolant(game, interpolant) as exc ->
     print_file filename "bad_interpolant" `over game;
     copy_file filename "bad_interpolant";
     Format.(fprintf stdout) "Interpolant:@,%a@," Term.pp interpolant;
     Format.(fprintf stdout) "@]%!";
     raise exc

   | FromYicesException(game, report) as exc ->
     print_file filename "yices_exc" `over game;
     print_file filename "yices_exc" `under game;
     copy_file filename "yices_exc";
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


