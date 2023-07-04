open Containers
open Yices2.Ext.WithNoErrorHandling

open Utils

type t = { (* See comments in mli *)
    id : int;
    ground  : Term.t;
    rigid   : Term.t list;
    newvars : Term.t list;
    foralls : forall Seq.t;
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
and pp_foralls fmt foralls =
  match foralls() with
  | Seq.Nil -> ()
  | _ -> Format.fprintf fmt "@,@[<v2>%i ∀-formula(e) / sub-level(s):@,%a@]"
           (Seq.length foralls)
           (List.pp ~pp_sep:pp_space pp_forall)
           (Seq.to_list foralls)


let rec free level =
  Seq.iter free_forall level.foralls
and free_forall {selector_context; sublevel; _} =
  Context.free selector_context;
  free sublevel
