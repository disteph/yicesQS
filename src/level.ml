open Containers
open Yices2.Ext_bindings

open Utils

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


let rec pp fmt {id; rigid; newvars; foralls; ground = _}
  = Format.fprintf fmt "@[<v>\
                        Level id: %i@,\
                        %i ancestors' variables: @[<hov>%a@]@,\
                        %i free variables: @[<hov>%a@]\
                        %a@]"
      id
      (List.length rigid)
      (List.pp ~pp_sep:pp_space Term.pp) rigid
      (List.length newvars)
      (List.pp ~pp_sep:pp_space Term.pp) newvars
      pp_foralls foralls
and pp_forall fmt {name; selector = _; sublevel; selector_context = _} =
  Format.fprintf fmt "@[<v 2>%a opens sub-level@,%a@]"
    Term.pp name
    pp sublevel
and pp_foralls fmt = function
  | [] -> ()
  | foralls -> Format.fprintf fmt "@,@[<v2>%i ∀-formula(e) / sub-level(s):@,%a@]"
                 (List.length foralls) (List.pp ~pp_sep:pp_space pp_forall) foralls

let rec free level =
  List.iter free_forall level.foralls
and free_forall {selector_context; sublevel; _} =
  Context.free selector_context;
  free sublevel
