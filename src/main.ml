open Containers
open Yices2_high

let print fs = Format.(fprintf stdout) fs

module EH1 = Make(ExceptionsErrorHandling)
open EH1

module Term = struct
  include Term
  let pp fmt t = t |> PP.term_string |> Format.fprintf fmt "%s"
end

module HType = Hashtbl.Make(Type)
module HTerm = Hashtbl.Make(Term)

module Game = struct  
  type t = {
    context : Context.t;   (* A Yices context that tries to satisfy this game *)
    support : Term.t list; (* All uninterpreted constants involved in this game *)
    newvars : Term.t list; (* Subset of the above that were not involved in the parent game *)
    ground  : Term.t;      (* Ground abstraction of the game, as a quantifier-free formula *)
    (* If uninterpreted constant u abstracts away formula (\forall x1...xn A), then *)
    existentials : Term.t list; (* ...ground formula (A{x1\u1...xn\un} => u) goes into that list,
                                   for new uninterpreted constants u1...un *)
    foralls : (Term.t * t) list (* ... (\forall x1..x2 A) is turned into an adversarial game g
                                      and (u,g) goes into that list;
                                      these games are the children game of the current game *)
  }

  let ppl s pl fmt l = match l with
    | [] -> ()
    | _::_ -> Format.fprintf fmt "@,@[<v 2>%s:@ @[%a@]@]" s (List.pp pl) l

  let rec pp fmt {ground; support; existentials; foralls}
    = Format.fprintf fmt "@[<v>@[Exists %a@]@,@[Ground: %a@]%a%a@]"
      (List.pp Term.pp) support
      Term.pp ground
      (ppl "Existentials" Term.pp) existentials
      (ppl "Foralls" pp') foralls
  and pp' fmt (u,game) =
    Format.fprintf fmt "@,@[<v 2>%a standing for@,%a@]" Term.pp u pp game

  let rec free {context; foralls} =
    let aux (_,g) = free g in
    List.iter aux foralls;
    Context.free context

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

  let fresh vars body =
    let aux subst v =
      let typ = Term.type_of_term v in
      let newvar = Term.new_uninterpreted_term typ in
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
          let newvar = Term.new_uninterpreted_term typ in
          HType.add h typ newvar;
          var_add newvar ((v,newvar)::subst)
        end
    in
    let+ subst = MList.fold aux (return []) vars in
    return (Term.subst_term subst body)


  exception CannotTreat of Term.t

  let rec process config ~support ~bound t =
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
            let uninterpreted = Term.new_uninterpreted_term (Type.bool()) in
            (* We instantiate the forall formula in 2 ways *)
            (* once instantiating all bound variables by the same uninterpreted term (per type) *)
            let+ substituted1 = fresh1 vars body in
            (* once instantiating all bound variables by distinct eigenvariables *)
            let+ substituted  = fresh vars body in
            (* the former version is used to produce a "lucky" instance of the formula *)
            let+ lucky_instance = aux substituted1 in
            (* the latter version is used to produce a "lucky" instance of the formula *)
            let+ existential = aux substituted in
            let t'           = Term.(uninterpreted &&& lucky_instance) in
            HTerm.add foralls_rev t t';
            fun state ->
              print "@[Abstracting @[%a@], which becomes @[%a@]@]@," Term.pp t Term.pp t';
              let existentials = Term.(existential ==> uninterpreted)::state.existentials in
              let foralls      = { uninterpreted; vars; body }::state.foralls in
              t', { state with existentials; foralls }
          end
      | Bindings { c = `YICES_LAMBDA_TERM } -> raise(CannotTreat t)
      | A0 _ -> return t
      | _ ->
        (* let aa = PP.term_string t in
         * print_endline aa; *)
        let+ x = map aux a in return(Term.build x)
    in
    (* creating meta-variables for the bound variables we are given *)
    let+ t = fresh bound t in
    aux t
  in
  let state = { support; newvars = []; existentials = []; foralls = [] } in
  let ground, { support; newvars; existentials; foralls } = tmp state in
  let treat { uninterpreted; vars; body } =
    uninterpreted, process config ~support ~bound:vars (Term.not1 body)
  in
  let foralls = List.map treat foralls in
  let context = Context.malloc config in
  Context.assert_formula context ground;
  Context.assert_formulas context existentials;
  { context; support; newvars; ground; existentials; foralls }

end



type model = {
  support : Term.t list;
  model   : Model.t
}

let pp_model fmt {support;model} =
  let aux fmt u =
    let v = Model.get_value_as_term model u in
    Format.fprintf fmt "@[%a := %a@]" Term.pp u Term.pp v
  in
  List.pp aux fmt support

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
[@@deriving show]

let rec solve
    (Game.{ context; support; newvars; ground; existentials; foralls } as game)
    model
  =
  print "@[<v 3>@[Solving game:@]@,%a@,from model@,%a@]@," Game.pp game pp_model model;
  match Context.check_with_model context model.model model.support with
  |  `STATUS_UNSAT ->
    let answer = Unsat Term.(not1 (Context.get_model_interpolant context)) in
    print "@[My answer is %a@]" pp_answer answer;
    answer
  |  `STATUS_SAT ->
    let newmodel = Context.get_model context ~keep_subst:true in
    print "@[<v 1>Model of ground+existentials is:@,%a@]@," pp_model { support; model = newmodel};
    let rec aux reasons = function
      | [] ->
        let true_of_model = ground::(List.rev_append existentials reasons) in
        let gen_model =
          Model.generalize_model_list newmodel true_of_model newvars `YICES_GEN_BY_PROJ
        in
        let answer = Sat Term.(andN gen_model) in
        print "@[My answer is %a@]" pp_answer answer;
        answer
      | (u,_)::opponents when not (Model.get_bool_value newmodel u)
        -> aux reasons opponents
      | (_,opponent)::opponents ->
        print "@[<v 1> ";
        let recurs = solve opponent { support; model = newmodel} in
        print "@]@,";
        match recurs with
        | Unsat reason -> aux (reason::reasons) opponents
        | Sat reason ->
          let learnt = Term.(not1 reason) in
          print "@[Learning %a@]@," Term.pp learnt;
          Context.assert_formula context learnt;
          solve game model
    in
    aux [] foralls
  | x -> Types.show_smt_status x |> print_endline; failwith "not good status"

open Yices2_SMT2
open Sexplib.Type

let () = assert(Global.has_mcsat())

let treat filename =
  let sexps = SMT2.load_file filename in
  let session = Session.create ~verbosity:3 in
  Config.set session.config ~name:"solver-type" ~value:"mcsat";
  Config.set session.config ~name:"mode" ~value:"multi-checks";
  let context = Context.malloc session.config in
  let param = Param.malloc () in
  let env = Session.{
    logic = "QF_BV";
    context;
    assertions = [];
    param;
    model = None
  }
  in
  session.env := Some env;
  let support = ref [] in
  let treat sexp =
    match sexp with
    | List(Atom head::args) ->
      begin match head, args, !(session.env) with
        | "declare-fun", [Atom var; List []; typ], _
        | "declare-const", [Atom var; typ], _ ->
          let ytype = ParseType.parse session.types typ |> Cont.get in
          let yvar = Term.new_uninterpreted_term ytype in
          support := yvar :: !support;
          Variables.permanently_add session.variables var yvar
        | "assert", [formula], Some real_env ->
          let formula = ParseTerm.parse session formula |> Cont.get in
          (match real_env.model with
           | Some model -> Model.free model
           | None -> ());
          print "@[Asserting formula @[<1>%a@]@]@," Term.pp formula;
          session.env := Some { real_env with assertions = formula::real_env.assertions;
                                              model = None}
        | "check-sat", [], Some env ->
          let formula = Term.(andN env.assertions) in
          let game = Game.process session.config ~support:!support ~bound:[] formula in
          print "@[<v 1>@[Computed game is:@]@,@[%a@]@]@," Game.pp game;
          print "@[Checking environment: %a@]@," Types.pp_smt_status (Context.check env.context);
          let emptymodel = Context.get_model env.context ~keep_subst:true in
          print "@[<v 1>@[emptymodel is:@]@ %s@]@," (PP.model_string emptymodel);
          print "@[support is: %a@]@,%!" (List.pp Term.pp) game.support;
          print "@[<v>";
          let answer = solve game { support = []; model = emptymodel } in
          print "@]@,";
          print "%a@," pp_answer answer;
          print "@[Error is: %s@]@,%!" (ErrorPrint.string())
        | _ -> ParseInstruction.parse session sexp
      end
    | _ -> ParseInstruction.parse session sexp
  in
  List.iter treat sexps;
  print "@[Exited gracefully@]%!"

open Arg

let args = ref []
let description = "QE in Yices";;

Arg.parse [] (fun a->args := a::!args) description;;

match !args with
| [filename] ->
  (try
     print "@[<v>";
     treat filename;
     print "@]";
  with
    ExceptionsErrorHandling.YicesException _ as exc
    -> ErrorPrint.string () |> print_endline; raise exc)
| [] -> failwith "Too few arguments in the command"
| _ -> failwith "Too many arguments in the command";;


