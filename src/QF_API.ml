open! Containers

open Ext
open Utils

module HTerms = Types.HTerms

(* Implements the model-based under-approximation function MBU (Def. 4),
   returned as formulas U for OptiQSMA (Alg. 4, line 10). *)

(* build_table smodel oldvar newvar:
   - smodel: current assignment used to read variable values
   - oldvar: rigid variables that can be used as substitutions
   - newvar: variables to eliminate (we only care about their values)
   Returns a table mapping each value taken by a newvar to the list of oldvar
   that share that value in the model. *)
let build_table smodel oldvar newvar =
  let tbl = HTerms.create (List.length newvar * 10) in
  (* treat_new var: record the value of a variable to eliminate as a table key. *)
  let treat_new var =
    let value = SModel.get_value_as_term smodel var |> Option.get_exn_or "no term value" in
    match HTerms.find_opt tbl value with
    | Some _ -> ()
    | None   -> HTerms.add tbl value []
  in
  List.iter treat_new newvar;
  (* treat_old var: if a rigid variable has a value already in the table,
     add the variable to the bucket for that value. *)
  let treat_old var =
    let value = SModel.get_value_as_term smodel var |> Option.get_exn_or "no term value" in
    match HTerms.find_opt tbl value with
    | Some l -> HTerms.replace tbl value (var::l)
    | None   -> ()
  in
  List.iter treat_old oldvar;
  tbl

(* A substitution list plus epsilon constraints accumulated during elimination. *)
type subst = (Term.t * Term.t) list WithEpsilons.t

(* generalize_model smodel ~true_of_model ~rigid_vars ~newvars:
   - smodel: model satisfying true_of_model
   - true_of_model: quantifier-free formula that holds in model
   - rigid_vars: variables that must remain in the result
   - newvars: variables to eliminate
   Returns a lazy list of generalized formulas U (Def. 4), each with
   optional epsilon constraints. *)
let generalize_model smodel ~true_of_model ~rigid_vars ~newvars =

  (* Then we build a table:
     for each value that the variables to eliminate take in the model,
     what are the rigid variables that have that value? *)
  let tbl = build_table smodel rigid_vars newvars in

  let open CLL in
  (* aux1 takes the list of variables t eliminate.
     The output is a costed lazy list of substitutions. *)
  (* aux1 list:
     - list: variables to eliminate
     Produces a lazy list of substitutions for those variables. *)
  let rec aux1 list : subst CLL.t = match list with
    | []              -> [] |> WithEpsilons.return |> CLL.return
    | var::other_vars -> (* var is a variable to eliminate *)
      let value = SModel.get_value_as_term smodel var |> Option.get_exn_or "no term value" in (* its value in the model *)
      let terms = HTerms.find tbl value in (* list of rigid variables that have that value *)
      let value =
        match Term.reveal value with
        (* | Term App(f, [arg]) when Term.equal f (Model.epsilon_real()) -> *)
        (*    begin *)
        (*      let Term arg = Term.reveal arg in *)
        (*      match arg with *)
        (*      | Bindings{c = `YICES_LAMBDA_TERM; vars = [yvar]; body } -> *)
        (*         let main = Term.new_uninterpreted (Type.real()) in *)
        (*         let epsilon = Term.subst_term [yvar, var] body in *)
        (*         WithEpsilons.{ main; epsilons = [epsilon] } *)
        (*      | _ -> failwith "should not be" *)
        (*    end *)
        | _ -> WithEpsilons.return value
      in
      print "generalize_model" 3 "@[<v2>Trying to eliminate variable %a, with value %a and matching variables %a@]@,"
        Term.pp var
        Term.pp value.main
        (List.pp Term.pp) terms;
      (* We recursively compute the costed lazy list of substitutions for all other variables. *)
      let@ WithEpsilons.{ main = subst; epsilons = epsilons_rec } = aux1 other_vars in
      (* subst symbolically represents (any) one of these substitutions;
         We need to extend it with a substitution for var.
         We turn all of the rigid variables that have the same value as var
         into a costed lazy list with no cost between elements. *)
      (* aux2 list:
         - list: candidate rigid variables with the same value as var
         Converts that list to a lazy list of substitution candidates. *)
      let rec aux2 : Term.t list -> Term.t WithEpsilons.t CLL.t = function
        | []   -> LazyList.empty
        | t::l -> lazy(`Cons((WithEpsilons.return t,0), aux2 l))
                      (* | []             -> WLL.return value *)
                      (* | [t]            -> lazy(`Cons((t,100), WLL.return value)) *)
                      (* | t::(_::_ as l) -> lazy(`Cons((t,0), aux2 l)) *)
      in
      (* ...and we add as the head of the lazy list the value that var has, as a term.
       Substituting var by that constant term will be done first,
       with a cost of 100 to access the substitutions by rigid variables. *)
      let@ WithEpsilons.{ main = t; epsilons } = lazy(`Cons((value,100), aux2 terms)) in
      (* t represents any one of the terms susbtituting var
         (the rigid variables with same value, the value itself as a term) *)
      WithEpsilons.{ main= (var, t)::subst; epsilons = epsilons @ epsilons_rec }
      |> CLL.return
  in
  let@ WithEpsilons.{ main = subst; epsilons } = aux1 newvars in
  CLL.return WithEpsilons.{
      main     = Term.subst_term subst true_of_model.main;
      epsilons = epsilons @ Term.subst_terms subst true_of_model.epsilons
    }

(* denum_elim smodel t:
   - smodel: used to evaluate denominators
   - t: term to rewrite
   Rewrites rational division into multiplication by the inverse of the
   model-evaluated denominator. If the denominator is 0, it raises
   Division_by_zero so callers can fall back to a safer path. *)
let rec denum_elim smodel t =
  match Term.reveal t with
  | Term(A0 _) -> t
  | Term(A2(`YICES_RDIV, num, denum)) ->
     let num = denum_elim smodel num in
     let denum = SModel.get_value_as_term smodel denum |> Option.get_exn_or "no term value" |> Term.rational_const_value in
     if Q.(equal denum zero) then raise Division_by_zero
     else
       let cst = denum |> Q.inv |> Term.Arith.mpq in
       Term.Arith.mul cst num
  | Term b -> Term.(build(map (denum_elim smodel) b))

(* generalize_model ~logic smodel ~true_of_model ~rigid_vars ~newvars:
   - logic: target theory; selects the generalization strategy
   - smodel: model satisfying true_of_model
   - true_of_model: quantifier-free formula to generalize
   - rigid_vars: variables to keep
   - newvars: variables to eliminate
   Implements MBU (Def. 4) using projection, invertibility conditions,
   or substitution depending on the theory. *)
let generalize_model ~logic smodel ~true_of_model ~rigid_vars ~newvars
    : Term.t WithEpsilons.t CLL.t =
  match logic with
  | `NRA
  | `LRA
  (* | `NIA
   * | `LIA *)
    ->
     begin
       try
         (* For LRA/NRA, try Yices projection after eliminating risky divisions. *)
         let true_of_model = denum_elim smodel true_of_model in
         SModel.generalize_model smodel true_of_model newvars `YICES_GEN_BY_PROJ
         |> Term.andN |> fun x -> CLL.return(WithEpsilons.return x)
       with _ ->
         (* Fall back to substitution-based generalization on failure. *)
         generalize_model smodel
           ~true_of_model:(WithEpsilons.return true_of_model) ~rigid_vars ~newvars
     end
  | `BV when !Command_options.bv_invert ->
     (* For BV, optionally apply invertibility conditions before substitution. *)
     (* First, we try to eliminate as many variables as we can by invertibility conditions *)
     let ic = IC.solve_all newvars true_of_model in
     print "generalize_model" 3 "@[<v2>Formula sent to IC is %a@]@," Term.pp true_of_model;
     print "generalize_model" 3 "@[<v2>Formula returned by IC is %a@]@," Term.pp WithEpsilons.(ic.main);
     generalize_model smodel ~true_of_model:ic ~rigid_vars ~newvars
     
  | _ ->
     (* Default: substitution-based generalization for other logics. *)
     generalize_model smodel
       ~true_of_model:(WithEpsilons.return true_of_model) ~rigid_vars ~newvars
