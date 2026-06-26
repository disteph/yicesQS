open! Containers

open Ext

type skip_reason =
  | Disabled
  | NoIntegerEliminables
  | LinearIntegerExplanation
  | TooManyEliminables of int
  | FormulaTooLarge of int
  | UnsupportedConstruct of string
  | MissingModelValue of Term.t
  | IllTypedLiftedFormula of Term.t

type build_result = {
  rigid_vars : Term.t list;
  intro_vars : Term.t list;
  body : Term.t;
  back_subst : (Term.t * Term.t) list;
  temp_vars : Term.t list;
}

let pp_skip_reason fmt = function
  | Disabled ->
    Format.fprintf fmt "disabled"
  | NoIntegerEliminables ->
    Format.fprintf fmt "no integer eliminables"
  | LinearIntegerExplanation ->
    Format.fprintf fmt "linear integer explanation"
  | TooManyEliminables n ->
    Format.fprintf fmt "too many integer eliminables (%d)" n
  | FormulaTooLarge n ->
    Format.fprintf fmt "formula too large (%d nodes)" n
  | UnsupportedConstruct name ->
    Format.fprintf fmt "unsupported construct %s" name
  | MissingModelValue t ->
    Format.fprintf fmt "missing model value for %a" Term.pp t
  | IllTypedLiftedFormula t ->
    Format.fprintf fmt "ill-typed lifted formula near %a" Term.pp t

let ( let* ) r f = match r with
  | Ok x -> f x
  | Error _ as e -> e

let rec map_result f = function
  | [] -> Ok []
  | x::xs ->
    let* y = f x in
    let* ys = map_result f xs in
    Ok (y::ys)

let find_subst subst t =
  List.find_map
    (fun (x, y) -> if Term.equal x t then Some y else None)
    subst

let unsupported name = Error (UnsupportedConstruct name)

let counter = ref 0

let fresh_name prefix =
  incr counter;
  prefix ^ string_of_int !counter

let model_value_subst smodel vars =
  let aux var =
    match SModel.get_value_as_term smodel var with
    | Some value -> Ok (var, value)
    | None -> Error (MissingModelValue var)
  in
  map_result aux vars

let children_of_termstruct : type a. a Types.termstruct -> Term.t list = function
  | A0 _ -> []
  | A1 (_, t) -> [t]
  | A2 (_, t, u) -> [t; u]
  | ITE (c, t, u) -> [c; t; u]
  | Astar (_, terms) -> terms
  | Bindings { vars; body; _ } -> body::vars
  | App (f, args) -> f::args
  | Update { array; index; value } -> array::value::index
  | Projection (_, _, t) -> [t]
  | BV_Sum components ->
    List.filter_map snd components
  | FF_Sum components
  | Sum components ->
    List.filter_map snd components
  | Product (_, factors) ->
    List.map fst factors

let node_count t =
  let rec aux t =
    let Term s = Term.reveal t in
    1 + (children_of_termstruct s |> List.map aux |> List.fold_left (+) 0)
  in
  aux t

let model_implicant smodel true_of_model =
  try
    match SModel.implicant_for_formula smodel true_of_model with
    | [] -> true_of_model
    | cube -> Term.andN cube
  with _ ->
    true_of_model

type arith_shape =
  | Const
  | Linear
  | Nonlinear

(* Conservative classifier for the QF-LIA fragment inside an NIA explanation.
   It accepts only integer-typed arithmetic and fails closed on real arithmetic
   or any constructor that would need rewriting to prove linearity. Examples:
   -1 times x is linear, x times y is not, and real constants are rejected. *)
let join_linear lhs rhs =
  match lhs, rhs with
  | Nonlinear, _
  | _, Nonlinear ->
    Nonlinear
  | Linear, _
  | _, Linear ->
    Linear
  | Const, Const ->
    Const

let arith_shape_lia shape =
  match shape with
  | Const
  | Linear -> true
  | Nonlinear -> false

let rec arith_shape t =
  if not (Term.is_int t) then
    Nonlinear
  else
    let Term s = Term.reveal t in
    match s with
    | A0 (`YICES_ARITH_CONSTANT, _) ->
      Const
    | A0 (`YICES_UNINTERPRETED_TERM, _)
    | A0 (`YICES_VARIABLE, _) ->
      Linear
    | Sum components ->
      let component_shape (_, term) =
        match term with
        | None -> Const
        | Some term -> arith_shape term
      in
      components
      |> List.map component_shape
      |> List.fold_left join_linear Const
    | Product (false, factors) ->
      product_shape factors
    | A0 (`YICES_BOOL_CONSTANT, _)
    | A0 (`YICES_ARITH_FF_CONSTANT, _)
    | A0 (`YICES_FF_CONSTANT, _)
    | A0 (`YICES_BV_CONSTANT, _)
    | A0 (`YICES_SCALAR_CONSTANT, _)
    | A1 _
    | A2 _
    | ITE _
    | Astar _
    | Bindings _
    | App _
    | Update _
    | Projection _
    | BV_Sum _
    | FF_Sum _
    | Product (true, _) ->
      Nonlinear

and product_shape factors =
  let factor_shape (term, exponent) =
    let exponent = Unsigned.UInt.to_int exponent in
    match arith_shape term with
    | Nonlinear ->
      Nonlinear
    | Const ->
      Const
    | Linear ->
      if exponent = 1 then Linear else Nonlinear
  in
  let rec count_linear count = function
    | [] ->
      if count <= 1 then
        (if count = 0 then Const else Linear)
      else
        Nonlinear
    | factor::factors ->
      match factor_shape factor with
      | Nonlinear ->
        Nonlinear
      | Const ->
        count_linear count factors
      | Linear ->
        count_linear (count + 1) factors
  in
  count_linear 0 factors

let arith_lia t =
  arith_shape_lia (arith_shape t)

let rec bool_lia t =
  if not (Term.is_bool t) then
    false
  else
    let Term s = Term.reveal t in
    match s with
    | A0 (`YICES_BOOL_CONSTANT, _)
    | A0 (`YICES_UNINTERPRETED_TERM, _)
    | A0 (`YICES_VARIABLE, _) ->
      true
    | A1 (`YICES_NOT_TERM, t1) ->
      bool_lia t1
    | A2 (`YICES_EQ_TERM, lhs, rhs) ->
      if Term.is_arithmetic lhs && Term.is_arithmetic rhs then
        arith_lia lhs && arith_lia rhs
      else if Term.is_bool lhs && Term.is_bool rhs then
        bool_lia lhs && bool_lia rhs
      else
        false
    | A2 (`YICES_ARITH_GE_ATOM, lhs, rhs) ->
      arith_lia lhs && arith_lia rhs
    | Astar (`YICES_OR_TERM, terms)
    | Astar (`YICES_XOR_TERM, terms) ->
      List.for_all bool_lia terms
    | Astar (`YICES_DISTINCT_TERM, terms) ->
      if List.for_all Term.is_bool terms then
        List.for_all bool_lia terms
      else if List.for_all Term.is_arithmetic terms then
        List.for_all arith_lia terms
      else
        false
    | A0 (`YICES_ARITH_CONSTANT, _)
    | A0 (`YICES_ARITH_FF_CONSTANT, _)
    | A0 (`YICES_FF_CONSTANT, _)
    | A0 (`YICES_BV_CONSTANT, _)
    | A0 (`YICES_SCALAR_CONSTANT, _)
    | A1 _
    | A2 _
    | ITE _
    | Astar _
    | Bindings _
    | App _
    | Update _
    | Projection _
    | BV_Sum _
    | FF_Sum _
    | Sum _
    | Product _ ->
      false

let is_lia_formula = bool_lia

let require_bool t =
  if Term.is_bool t then Ok t else Error (IllTypedLiftedFormula t)

let require_arith t =
  if Term.is_arithmetic t then Ok t else Error (IllTypedLiftedFormula t)

let build_or terms =
  let* terms = map_result require_bool terms in
  Ok (Term.orN terms)

let build_xor terms =
  let* terms = map_result require_bool terms in
  Ok (Term.xorN terms)

let build_distinct terms =
  try Ok (Term.distinct terms) with _ -> Error (IllTypedLiftedFormula (Term.andN []))

let build_eq original lhs rhs =
  try
    if Term.is_arithmetic lhs && Term.is_arithmetic rhs then
      Ok (Term.Arith.arith_eq lhs rhs)
    else
      Ok (Term.eq lhs rhs)
  with _ ->
    Error (IllTypedLiftedFormula original)

let build_ge original lhs rhs =
  let* lhs = require_arith lhs in
  let* rhs = require_arith rhs in
  try Ok (Term.Arith.geq lhs rhs) with _ -> Error (IllTypedLiftedFormula original)

let build_sum original components =
  let lift_component (coeff, term) =
    match term with
    | None -> Ok (Term.Arith.mpq coeff)
    | Some term ->
      let* term = require_arith term in
      let coeff = Term.Arith.mpq coeff in
      try Ok (Term.Arith.mul coeff term)
      with _ -> Error (IllTypedLiftedFormula original)
  in
  let* terms = map_result lift_component components in
  try
    Ok (match terms with
        | [] -> Term.Arith.int 0
        | _ -> Term.Arith.sum terms)
  with _ -> Error (IllTypedLiftedFormula original)

let build_product original factors =
  let expand_factor (term, exponent) =
    let* term = require_arith term in
    let exponent = Unsigned.UInt.to_int exponent in
    try Ok (Term.Arith.power term exponent)
    with _ -> Error (IllTypedLiftedFormula original)
  in
  let* terms = map_result expand_factor factors in
  try
    Ok (match terms with
        | [] -> Term.Arith.int 1
        | _ -> Term.Arith.product terms)
  with _ -> Error (IllTypedLiftedFormula original)

let rec lift ~subst t =
  match find_subst subst t with
  | Some replacement -> Ok replacement
  | None ->
    let Term s = Term.reveal t in
    match s with
    | A0 (`YICES_UNINTERPRETED_TERM, _) ->
      if Term.is_int t then unsupported "unmapped-int-variable"
      else if Term.is_bool t || Term.is_arithmetic t then Ok t
      else unsupported "uninterpreted-term"
    | A0 (`YICES_VARIABLE, _) ->
      unsupported "unmapped-variable"
    | A0 (`YICES_BOOL_CONSTANT, _)
    | A0 (`YICES_ARITH_CONSTANT, _) ->
      Ok t
    | A0 (`YICES_ARITH_FF_CONSTANT, _)
    | A0 (`YICES_FF_CONSTANT, _)
    | A0 (`YICES_BV_CONSTANT, _)
    | A0 (`YICES_SCALAR_CONSTANT, _) ->
      unsupported "constant"

    | A1 (`YICES_NOT_TERM, t1) ->
      let* t1 = lift ~subst t1 in
      let* t1 = require_bool t1 in
      Ok (Term.not1 t1)
    | A1 (`YICES_ABS, _) -> unsupported "abs"
    | A1 (`YICES_CEIL, _) -> unsupported "ceil"
    | A1 (`YICES_FLOOR, _) -> unsupported "floor"
    | A1 (`YICES_IS_INT_ATOM, _) -> unsupported "is-int"

    | A2 (`YICES_EQ_TERM, lhs, rhs) ->
      let* lhs = lift ~subst lhs in
      let* rhs = lift ~subst rhs in
      build_eq t lhs rhs
    | A2 (`YICES_ARITH_GE_ATOM, lhs, rhs) ->
      let* lhs = lift ~subst lhs in
      let* rhs = lift ~subst rhs in
      build_ge t lhs rhs
    | A2 (`YICES_RDIV, _, _) -> unsupported "real-division"
    | A2 (`YICES_IDIV, _, _) -> unsupported "integer-division"
    | A2 (`YICES_IMOD, _, _) -> unsupported "mod"
    | A2 (`YICES_DIVIDES_ATOM, _, _) -> unsupported "divides"
    | A2 (`YICES_ARITH_ROOT_ATOM, _, _) -> unsupported "arith-root"
    | A2 (`YICES_BV_ASHR, _, _)
    | A2 (`YICES_BV_DIV, _, _)
    | A2 (`YICES_BV_GE_ATOM, _, _)
    | A2 (`YICES_BV_LSHR, _, _)
    | A2 (`YICES_BV_REM, _, _)
    | A2 (`YICES_BV_SDIV, _, _)
    | A2 (`YICES_BV_SGE_ATOM, _, _)
    | A2 (`YICES_BV_SHL, _, _)
    | A2 (`YICES_BV_SMOD, _, _)
    | A2 (`YICES_BV_SREM, _, _) ->
      unsupported "bitvector"

    | ITE _ -> unsupported "ite"

    | Astar (`YICES_OR_TERM, terms) ->
      let* terms = map_result (lift ~subst) terms in
      build_or terms
    | Astar (`YICES_XOR_TERM, terms) ->
      let* terms = map_result (lift ~subst) terms in
      build_xor terms
    | Astar (`YICES_DISTINCT_TERM, terms) ->
      let* terms = map_result (lift ~subst) terms in
      build_distinct terms
    | Astar (`YICES_TUPLE_TERM, _) -> unsupported "tuple"
    | Astar (`YICES_BV_ARRAY, _) -> unsupported "bitvector-array"

    | Bindings _ -> unsupported "quantifier-or-lambda"
    | App _ -> unsupported "application"
    | Update _ -> unsupported "array-update"
    | Projection _ -> unsupported "projection"
    | BV_Sum _ -> unsupported "bitvector-sum"
    | FF_Sum _ -> unsupported "finite-field-sum"
    | Sum components ->
      let lift_component (coeff, term) =
        match term with
        | None -> Ok (coeff, None)
        | Some term ->
          let* term = lift ~subst term in
          Ok (coeff, Some term)
      in
      let* components = map_result lift_component components in
      build_sum t components
    | Product (true, _) ->
      unsupported "bitvector-product"
    | Product (false, factors) ->
      let lift_factor (term, exponent) =
        let* term = lift ~subst term in
        Ok (term, exponent)
      in
      let* factors = map_result lift_factor factors in
      build_product t factors

let make_box int_elims =
  let real = Type.real () in
  let one = Term.Arith.int 1 in
  let make_var prefix _ =
    Term.new_uninterpreted ~name:(fresh_name prefix) real
  in
  let y_vars = List.map (make_var "ub!y!") int_elims in
  let r_vars = List.map (fun _ -> Term.new_variable real) int_elims in
  let bounds =
    List.map2
      (fun y r ->
        Term.(Term.Arith.leq y r &&&
              Term.Arith.lt r (Term.Arith.add y one)))
      y_vars
      r_vars
  in
  y_vars, r_vars, Term.andN bounds

let rigid_proxy_map true_of_model rigid_vars =
  let real = Type.real () in
  rigid_vars
  |> List.filter Term.is_int
  |> List.filter (fun var -> Term.is_free ~var true_of_model)
  |> List.map (fun var ->
      let proxy = Term.new_uninterpreted ~name:(fresh_name "ub!z!") real in
      var, proxy)

let non_int_rigids true_of_model rigid_vars =
  rigid_vars
  |> List.filter (fun var -> not (Term.is_int var))
  |> List.filter (fun var -> Term.is_free ~var true_of_model)

(* Soundness hinge: this builder only creates a sibling NRA obligation from a
   model implicant. Integer eliminables are universally ranged over real unit
   boxes, non-integer eliminables are frozen to their model values, and integer
   rigids are replaced by real proxies. Solver.check later accepts a reason
   only after substituting those proxies back and rejecting any formula that
   still mentions temporary box/proxy variables. *)
let build smodel ~true_of_model ~rigid_vars ~newvars =
  if not !Command_options.nia_unit_box_mbu then
    Error Disabled
  else
    let int_elims, other_elims = List.partition Term.is_int newvars in
    match int_elims with
    | [] -> Error NoIntegerEliminables
    | _ ->
      let true_of_model = model_implicant smodel true_of_model in
      let occurs var = Term.is_free ~var true_of_model in
      let int_elims = List.filter occurs int_elims in
      let other_elims = List.filter occurs other_elims in
      match int_elims with
      | [] -> Error NoIntegerEliminables
      | _ ->
        if is_lia_formula true_of_model then
          Error LinearIntegerExplanation
        else
          let n_elims = List.length int_elims in
          if n_elims > !Command_options.nia_unit_box_max_elims then
            Error (TooManyEliminables n_elims)
          else
            let nodes = node_count true_of_model in
            if nodes > !Command_options.nia_unit_box_max_nodes then
              Error (FormulaTooLarge nodes)
            else
              let* other_subst = model_value_subst smodel other_elims in
              let true_of_model = Term.subst_term other_subst true_of_model in
              let y_vars, r_vars, box = make_box int_elims in
              let int_elim_subst = List.combine int_elims r_vars in
              let int_rigid_subst = rigid_proxy_map true_of_model rigid_vars in
              let subst = int_elim_subst @ int_rigid_subst in
              let* lifted_body = lift ~subst true_of_model in
              let* lifted_body = require_bool lifted_body in
              let body = Term.(box ==> lifted_body) in
              let body = Term.forall r_vars body in
              let rigid_proxies = List.map snd int_rigid_subst in
              let kept_rigids = non_int_rigids true_of_model rigid_vars in
              let back_subst =
                List.map (fun (old_var, proxy) -> proxy, old_var) int_rigid_subst
              in
              Ok {
                rigid_vars = rigid_proxies @ kept_rigids;
                intro_vars = y_vars;
                body;
                back_subst;
                temp_vars = rigid_proxies @ y_vars;
              }
