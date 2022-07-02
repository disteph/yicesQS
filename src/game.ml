open Containers

open Yices2.High
open Yices2.Ext_bindings

open Utils

module type T = sig
  val ground    : Term.t (* Ground abstraction of the game, as a quantifier-free formula *)
  val existentials : Term.t list
  val universals   : Term.t list
  val top_level : Level.t
end

type t = (module T)

let pp fmt (module T:T) =
  let open T in
  Format.fprintf fmt "@[<v>\
                      @[<2>Ground:@ %a@]@,\
                      @[<2>Existentials:@ @[<v>%a@]@]@,\
                      @[<v 2>Levels:@,%a@]\
                      @]"
    Term.pp ground
    (List.pp ~pp_sep:pp_space Term.pp) existentials
    Level.pp top_level

(* The encoding of a formula into a game is done with a state monad,
     where the state is this *)

type state = {
    newvars : Term.t list;
    foralls : Level.forall list;
    existentials : Term.t list;
    universals   : Term.t list;
    epsilons     : Term.t list
  }

(* The state monad *)
module StateMonad = StateMonad(struct type t = state end)

(* Monadic fold and map *)
module MList = MList(StateMonad)
include MTerm(StateMonad)

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

let foralls_rev = HTerms.create 10

(* rigidintro = rigid + intro *)
let rec process config ~logic ~rigidintro ~rigid ~intro body : t WithEpsilonsMonad.t =
  let open StateMonad in

  let rec aux t : Term.t StateMonad.t =
    let Term a = Term.reveal t in
    match a with
    | Bindings { c = `YICES_FORALL_TERM;
                 vars;
                 body }
      ->
       if false
       then
         return(HTerms.find foralls_rev t) (* returns placeholder previously generated *)
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
           HTerms.add foralls_rev t name;
           let substituted, rigidintro_sub, intro_sub = fresh rigidintro vars body in
           fun state ->
           let WithEpsilons.{ main = (module SubGame); epsilons } =
             process config
               ~logic
               ~rigidintro:rigidintro_sub
               ~rigid:rigidintro
               ~intro:intro_sub
               (Term.not1 substituted)
               state.epsilons
           in
           let selector_context = Context.malloc ~config () in
           Context.assert_formula selector_context selector;
           let newforall =
             Level.{ name; selector; selector_context; sublevel = SubGame.top_level }
           in
           let existential = Term.(name ||| SubGame.ground) in
           let universal   = Term.(selector === SubGame.ground) in
           print 5 "@[<2>Abstracting as %a formula @,%a@]@," Term.pp name Term.pp t;

           let WithEpsilons.{ main = projection; epsilons } =
             let open WithEpsilons in
             match logic with
             | `BV ->
                ListWithEpsilons.map
                  (IC.weaken_existentials intro_sub)
                  (SubGame.existentials @ SubGame.universals)
                  epsilons
             | _ -> return []
           in
           
           let newvars = SubGame.top_level.newvars @ (name::selector::state.newvars) in
           let foralls = SubGame.top_level.foralls @ (newforall::state.foralls) in
           let existentials = SubGame.existentials @ (existential::state.existentials) in
           let universals   =
             projection @ SubGame.universals   @ (universal::state.universals) in
           name, { newvars; foralls; existentials; universals; epsilons }
         end
    | Bindings { c = `YICES_LAMBDA_TERM; _ } -> raise(CannotTreat t)
    | A0 _ -> return t
    | _ ->
       let+ x = map aux a in return(Term.build x)
  in
  print 5 "@[<v2>Traversing term@,%a@]@," Term.pp body;
  let id = !counter in
  fun epsilons ->
  let state = { newvars = intro;
                foralls = [];
                existentials = [];
                universals = [];
                epsilons }
  in
  let ground, { newvars; foralls; existentials; universals; epsilons } = aux body state in
  let foralls = List.rev foralls in
  WithEpsilons.{
      main =
        (module struct
           let top_level =
             Level.{id; ground = Term.(ground &&& andN existentials); rigid; newvars; foralls;}
           let ground = ground
           let existentials = existentials
           let universals = universals
         end);
      epsilons }

let process config ~logic ~global_vars body : t WithEpsilons.t =
  process config ~logic ~rigidintro:global_vars ~rigid:[] ~intro:global_vars body []
