open Containers

open Yices2.High
open Ext

open Utils

(* Build the QSMA-tree (Def. 1) and look-ahead formulas LF(n) (Def. 8)
   used by OptiQSMA (Alg. 3/4). *)

module type T = sig
  val ground    : Term.t (* root.F with proxies (Def. 2), part of LF(root) (Def. 8). *)
  val existentials : Term.t Seq.t (* Conjuncts encoding p => LF(child) (Def. 8). *)
  val universals   : Term.t Seq.t (* Selector constraints enforcing LF(child) (Def. 8). *)
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
    (List.pp ~pp_sep:pp_space Term.pp) (Seq.to_list existentials)
    Level.pp top_level

(* The encoding of a formula into a QSMA-tree uses a state monad. *)

type state = {
    newvars : Term.t list;
    foralls : Level.forall list;
    existentials : Term.t Seq.t;
    universals   : Term.t Seq.t
  }

(* The state monad *)

module StateMonad = struct
  type 'a t = state -> 'a * state
  let return a s = a,s
  let bind a f s = let a,s = a s in f a s
  let (let+) = bind 
end

(* Monadic fold and map *)
module MList = Yices2.Common.MList(StateMonad)
include MTerm(StateMonad)

(* Create fresh names for turning bound variables into eigenvariables
   (they become rigid variables for descendant nodes, Def. 1/3). *)
let bound_counter = ref 1

let fresh_bound () : string =
  let name = "y!"^string_of_int !bound_counter in
  incr bound_counter;
  name

(* Given a Yices forall term, with bound variables and body,
   - create fresh eigenvariables newvars for each bound variable
   - substitute these eigenvariables for the bound variables in the body
   - accumulate the new eigenvariables in the accumulator passed as argument
   - return the substituted body, the accumulator, the new eigenvariables
 *)
let fresh ~accu bound body : Term.t * Term.t list * Term.t list =
  let aux (subst, accu, newvars) v =
    let typ = Term.type_of_term v in
    let name = fresh_bound() in
    let newvar = Term.new_uninterpreted ~name typ in
    ((v,newvar)::subst), (newvar::accu), (newvar::newvars)
  in
  let subst, rigid, newvars = List.fold_left aux ([], accu, []) bound in
  Term.subst_term subst body, rigid, newvars

exception CannotTreat of Term.t

let counter = ref 0

(* Ideally, if we see the same forall subformula several times,
   we should only turn it into a game once and re-use the same game at every occurrence.
   To detect this, we need a map from forall terms to games *)
let foralls_rev = Types.HTerms.create 10

(* Core procedure for encoding a formula (exists intro. body) into a game.
   - config is the Yices config
   - intros and body are describing the existential formula we're encoding
   - rigid are the variables that will be set by the ancestor games (Rigid(n))
   - rigidintro = rigid + intro; for some reason this is useful
   and we want to avoid the cost of concatenation everytime we need it.
 *)
let rec process config ~rigidintro ~rigid ~intro body : t =
  let open StateMonad in

  (* This auxiliary function descends into the term structure of body
     and turns forall subformulas into proxy variables (Def. 1/2). *)
  let rec aux t : Term.t StateMonad.t =
    let Term a = Term.reveal t in
    match a with
    | Bindings { c = `YICES_FORALL_TERM;
                 vars;
                 body }
      ->
       if false (* This is the place where we should reuse the same game
                   if we see a forall formula several times.
                   Currently we're not doing it because in practice
                   that happens very rarely
                   and we are saving some CPU cycles for the SMT-comp *)
       then
         return(Types.HTerms.find foralls_rev t) (* returns game previously generated *)
       else
         begin
           (* Creating a selector for the forall formula (used to enforce LF). *)
           incr counter;
           let freshcount = string_of_int !counter in
           let name  = "trig"^freshcount in
           let selector = Term.new_uninterpreted ~name (Type.bool()) in
           (* Creating a proxy name b.p for the forall formula (Def. 1/2). *)
           let name  = "name"^freshcount in
           let name  = Term.new_uninterpreted ~name (Type.bool()) in
           (* Types.HTerms.add foralls_rev t name; *)
           (* We replace bound variables by eigenvariables (Rigid for descendants). *)
           let substituted, rigidintro_sub, intro_sub = fresh ~accu:rigidintro vars body in
           (* Recursively create the QSMA-subtree for the negated body. *)
           let (module SubGame) =
             process config
               ~rigidintro:rigidintro_sub
               ~rigid:rigidintro
               ~intro:intro_sub
               (Term.not1 substituted) (* Negation because process works on existentials *)
           in
           let selector_context = Context.malloc ~config () in
           Context.assert_formula selector_context selector;
           let newforall =
             Level.{ name; selector; selector_context; sublevel = SubGame.top_level }
           in
           (* name stands for the forall formula; SubGame.ground is LF(b).
              and SubGame.ground should hold if the existential formula is true;
              hence, the implication (not name) => SubGame.ground should always hold.
              This is the LF(n) shape of Def. 8 (via p => LF(b)). *)
           let existential = Term.(name ||| SubGame.ground) in
           (* The selector is just a way to assert LF(b) in a separate context.
              Technically we just need (selector ==> SubGame.ground),
              but experiments show slightly better results with ===; who knows why... *)
           let universal   = Term.(selector === SubGame.ground) in
           fun state ->
           print "process" 5 "@[<2>Abstracting as %a formula @,%a@]@," Term.pp name Term.pp t;
           let newvars = SubGame.top_level.newvars @ (name::selector::state.newvars) in
           let foralls = newforall::state.foralls in
           let existentials =
             Seq.(append SubGame.existentials (cons existential state.existentials))
           in
           let universals   =
             Seq.(append SubGame.universals (cons universal state.universals))
           in
           name, { newvars; foralls; existentials; universals }
         end
    | Bindings { c = `YICES_LAMBDA_TERM; _ } -> raise(CannotTreat t)
    | A0 _ -> return t
    | _ ->
       let+ x = map aux a in return(Term.build x)
  in
  print "process" 5 "@[<v2>Traversing term@,%a@]@," Term.pp body;
  let id = !counter in
  let state = { newvars = intro;
                foralls      = [];
                existentials = Seq.nil;
                universals   = Seq.nil; }
  in
  let ground, { newvars; foralls; existentials; universals } = aux body state in
  (module struct
     let top_level =
       Level.{id;
              ground = Term.(ground &&& andN (Seq.to_list existentials));
              rigid;
              newvars;
              foralls = Seq.of_list foralls }
     let ground = ground
     let existentials = existentials
     let universals = universals
   end)

let process config ~global_vars body : t =
  process config ~rigidintro:global_vars ~rigid:[] ~intro:global_vars body
