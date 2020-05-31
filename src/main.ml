open Containers
open Yices2_high
open Sexplib.Type
open Yices2_SMT2
open Bindings

open Debug


let verbosity = ref 0

let print i fs = Format.((if !verbosity >= i then fprintf else ifprintf) stdout) fs

let ppl ~prompt pl fmt l = match l with
  | [] -> ()
  | _::_ -> Format.fprintf fmt "@,@[<v 2>%s %i formula(e)@,%a@]"
              prompt
              (List.length l)
              (List.pp pl) l

module HType = Hashtbl.Make(Type)
module HTerm = Hashtbl.Make(Term)

module Game = struct  
  type t = {
    id : int;
    context : Context.t;   (* A Yices context that tries to satisfy this game *)
    support : Term.t list; (* All uninterpreted constants involved in this game *)
    newvars : Term.t list; (* Subset of the above that were not involved in the parent game *)
    ground  : Term.t;      (* Ground abstraction of the game, as a quantifier-free formula *)
    learnt  : Term.t list ref; (* ground formulas learnt from the foralls *)
    (* If uninterpreted constant u abstracts away formula (\forall x1...xn A), then *)
    existentials : Term.t list; (* ...ground formula (A{x1\u1...xn\un} => u) goes into that list,
                                   for new uninterpreted constants u1...un *)
    foralls : (Term.t * t) list (* ... (\forall x1..x2 A) is turned into an adversarial game g
                                      and (u,g) goes into that list;
                                      these games are the children game of the current game *)
  }

  let rec pp fmt {id; ground; support; learnt; existentials; foralls}
    = Format.fprintf fmt "@[<v>@[Game id: %i@]@,\
                          @[Variables %i: %a@]@,\
                          @[Ground: %a@]\
                          %a\
                          %a\
                          %a@]"
      id
      (List.length support)
      (List.pp Term.pp) support
      Term.pp ground
      (ppl ~prompt:"Existentials:" Term.pp) existentials
      (ppl ~prompt:"Learnt:" Term.pp) !learnt
      (ppl ~prompt:"Foralls:" pp_forall) foralls
  and pp_forall fmt (u,game) =
    Format.fprintf fmt "@[<v 2>%a standing for@,%a@]" Term.pp u pp game
    
  let rec free {context; foralls} =
    let aux (_,g) = free g in
    List.iter aux foralls;
    Context.free context

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
  
  (* The following datastructure is used to record
     that uninterpreted constant u abstracts away formula (\forall x1...xn A):
     { uninterpreted = u; vars = x1...xn; body = A } *)
  type forall = {
    uninterpreted : Term.t;
    vars : Term.t list;
    body : Term.t
  }

  (* The encoding of a formula into a game is done with a state monad,
     where the state is this*)

  type state = {
    support : Term.t list;
    newvars : Term.t list;
    existentials: Term.t list;
    foralls : forall list
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
    let support = newvar::state.support in
    let newvars = newvar::state.newvars in
    a, { state with support; newvars }

  let bound_counter = ref 0

  let fresh_bound () =
    let name = "y!"^string_of_int !bound_counter in
    incr bound_counter;
    name

  let fresh vars body =
    let aux subst v =
      let typ = Term.type_of_term v in
      let name = fresh_bound() in
      let newvar = Term.new_uninterpreted ~name typ in
      var_add newvar ((v,newvar)::subst)
    in
    let+ subst = MList.fold aux (return []) vars in
    return (Term.subst_term subst body)

  let fresh1 vars body =
    let h = HType.create 10 in
    let aux subst v =
      let typ = Term.type_of_term v in
      if HType.mem h typ
      then return ((v, HType.find h typ)::subst)
      else
        begin
          let name = fresh_bound() in
          let newvar = Term.new_uninterpreted ~name typ in
          HType.add h typ newvar;
          var_add newvar ((v,newvar)::subst)
        end
    in
    let+ subst = MList.fold aux (return []) vars in
    return (Term.subst_term subst body)


  exception CannotTreat of Term.t

  let counter = ref 0

  let fa_counter = ref 0

  let fresh_placeholder () =
    let name = "forall_placeholder"^string_of_int !fa_counter in
    incr fa_counter;
    name

  let rec process config player ~support ~bound t =
    print 5 "@[Traversing term @[%a@]@]@," Term.pp t;
    let id = if player then 2*(!counter) else (2*(!counter))+1 in
    incr counter;
    let tmp =
      let foralls_rev = HTerm.create 10 in
      let rec aux t =
        let Term a = Term.reveal t in
        match a with
        | Bindings { c = `YICES_FORALL_TERM;
                     vars;
                     body }
          ->
          if HTerm.mem foralls_rev t
          then
            return(HTerm.find foralls_rev t)
          else
            begin
              (* We create a name for the forall formula *)
              let name = fresh_placeholder() in
              let uninterpreted = Term.new_uninterpreted ~name (Type.bool()) in
              (* We instantiate the forall formula in 2 ways *)
              (* once instantiating all bound variables by the same uninterpreted term (per type) *)
              (* let+ substituted1 = fresh1 vars body in *)
              (* once instantiating all bound variables by distinct eigenvariables *)
              let+ substituted  = fresh vars body in
              (* (\* the former version is used to produce a "lucky" instance of the formula *\)
               * let+ lucky_instance = aux substituted1 in *)
              (* the latter version is used to produce a "lucky" instance of the formula *)
              let+ existential = aux substituted in
              (* let t'           = Term.(uninterpreted &&& lucky_instance) in *)
              let t'           = uninterpreted in
              HTerm.add foralls_rev t t';
              fun state ->
                print 4 "@[Abstracting @[%a@], which becomes @[%a@]@]@," Term.pp t Term.pp t';
                let support      = uninterpreted::state.support in
                let newvars      = uninterpreted::state.newvars in
                let existentials = Term.(existential ==> uninterpreted)::state.existentials in
                let foralls      = { uninterpreted; vars; body }::state.foralls in
                t', { support; newvars; existentials; foralls }
            end
        | Bindings { c = `YICES_LAMBDA_TERM } -> raise(CannotTreat t)
        | A0 _ -> return t
        | _ ->
          let+ x = map aux a in return(Term.build x)
      in
      (* creating meta-variables for the bound variables we are given *)
      let+ t = fresh bound t in
      aux t
    in
    let state = { support; newvars = []; existentials = []; foralls = [] } in
    let ground, { support; newvars; existentials; foralls } = tmp state in
    let treat { uninterpreted; vars; body } =
      uninterpreted, process config (not player) ~support ~bound:vars (Term.not1 body)
    in
    let foralls = List.map treat foralls in
    let context = Context.malloc ~config () in
    Context.assert_formula context ground;
    Context.assert_formulas context existentials;
    { id; context; support; newvars; ground; learnt = ref []; existentials; foralls }

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
      Format.fprintf fmt "@[%a := %a@]" Term.pp u Term.pp v
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

let rec solve
    (Game.{ context; support; newvars; ground; existentials; foralls } as game)
    model
  =
  print 3 "@[<v 3>@[Solving game:@]@,%a@,from model%a@]@," Game.pp game SModel.pp model;
  match Context.check_with_model context model.model model.support with
  |  `STATUS_UNSAT ->
    let answer = Unsat Term.(not1 (Context.get_model_interpolant context)) in
    print 3 "@[Game %i answer on that model is %a@]" game.id pp_answer answer;
    answer
  |  `STATUS_SAT ->
    let newmodel = Context.get_model context ~keep_subst:true in
    print 4 "@[<v 1>Found model of ground+existentials+learnt:%a@]@," SModel.pp SModel.{ support; model = newmodel};
    let rec aux reasons = function
      | [] ->
        let true_of_model = ground::(List.rev_append existentials reasons) in
        let gen_model =
          Model.generalize_model_list newmodel true_of_model newvars `YICES_GEN_BY_PROJ
        in
        let answer = Sat Term.(andN gen_model) in
        print 3 "@[Game %i answer on that model is %a@]" game.id pp_answer answer;
        answer
      | (u,_)::opponents when not (Model.get_bool_value newmodel u)
        -> aux reasons opponents
      | (u,opponent)::opponents ->
        print 1 "@[<v 1> ";
        let recurs = solve opponent { support; model = newmodel} in
        print 1 "@]@,";
        match recurs with
        | Unsat reason -> aux (reason::reasons) opponents
        | Sat reason ->
          let learnt = Term.(u ==> not1 reason) in
          (* print "@[Learning %a@]@," Term.pp learnt; *)
          Context.assert_formula context learnt;
          game.learnt := learnt::!(game.learnt);
          solve game model
    in
    aux [] foralls
  | x -> Types.show_smt_status x |> print_endline; failwith "not good status"

let () = assert(Global.has_mcsat())

let treat filename =
  let sexps = SMT2.load_file filename in
  let session = Session.create ~verbosity:0 in
  let support = ref [] in
  let expected = ref None in
  let assertions = ref [] in
  let treat sexp =
    match sexp with
    | List(Atom head::args) ->
      print 1 "@[Traversing sexp @[%a@]@]@," Sexplib.Sexp.pp sexp;
      begin match head, args, !(session.env) with
        | "set-info",   [Atom ":status"; Atom "sat"],   _ ->
          expected := Some true

        | "set-info",   [Atom ":status"; Atom "unsat"],   _ ->
          expected := Some false

        | "set-logic",   [Atom logic],   None ->
          print 3 "@[Setting logic to %s@]@," logic;
          Config.set session.config ~name:"solver-type" ~value:"mcsat";
          Config.set session.config ~name:"mode" ~value:"multi-checks";
          Session.init_env ~configure:() session ~logic

        | "declare-fun", [Atom name; List []; typ], _
        | "declare-const", [Atom name; typ], _ ->
          let ytype = ParseType.parse session.types typ |> Cont.get in
          let yvar = Term.new_uninterpreted ~name ytype in
          support := yvar :: !support;
          print 2 "@[<v>declared fun/cst is %a@]@," Term.pp yvar;
          Variables.permanently_add session.variables name yvar

        | "assert", [formula], Some env ->
          let formula = ParseTerm.parse session formula |> Cont.get in
          print 2 "@[Asserting formula @[<1>%a@]@]@," Term.pp formula;
          (match env.model with
           | Some model -> Model.free model
           | None -> ());
          assertions := formula::!assertions

        | "check-sat", [], Some env ->
          let formula = Term.(andN !assertions) in
          print 2 "@[<v 2>@[Computing game@]@,";
          let game = Game.process session.config true ~support:!support ~bound:[] formula in
          print 3 "@[<v 1>@[Computed game is:@]@,@[%a@]@]@," Game.pp game;
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

open Arg

let args = ref []
let description = "QE in Yices"

let options = [
  ("-verb", Int(fun i -> verbosity := i), "Verbosity level (default is 0)");
];;

Arg.parse options (fun a->args := a::!args) description;;

match !args with
| [filename] ->
  (try
     Format.(fprintf stdout) "@[<v>";
     treat filename;
     Format.(fprintf stdout) "@]%!";
  with
    ExceptionsErrorHandling.YicesException(_,report) as exc
    ->
    Format.(fprintf stderr) "@[<v>%a@]%!" Types.pp_error_report report;
    raise exc
 )
| [] -> failwith "Too few arguments in the command"
| _ -> failwith "Too many arguments in the command";;


