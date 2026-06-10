# Plan: Division Handling in `projection_preprocess`

## Purpose

Improve `QF_API.projection_preprocess` so arithmetic model projection can handle real division more generally.

The current implementation is sound but too narrow. For a term of the form:

```smt2
(/ num den)
```

it evaluates `den` in the current model, rewrites the term to:

```smt2
(* (/ 1 model(den)) num)
```

and adds the guard:

```smt2
(= den model(den))
```

This freezes the denominator to its model value. That preserves implication, but it can destroy useful generality before Yices projection gets a chance to eliminate variables.

The new approach should avoid freezing symbolic real denominators when the surrounding formula is an arithmetic atom. Instead, it should clear denominators at the atom level, adding only the sign constraints needed to make the rewrite sound.

## High-Level Design

Split preprocessing into two conceptual passes.

1. A construct-elimination pass:
   - Eliminates constructs that Yices projection does not accept.
   - Preserves existing model-selected behavior for `ite`.
   - Preserves existing handling for `abs`, `floor`, `ceil`, integer division, and modulus.
   - Rewrites real division by constant nonzero denominators directly.
   - Leaves symbolic real division untouched when the logic permits nonlinear arithmetic.

2. A division-clearing pass:
   - Walks Boolean structure.
   - Finds arithmetic atoms.
   - Normalizes both sides of each arithmetic atom into a symbolic fraction.
   - Multiplies through by a denominator whose sign is known from the model.
   - Adds a symbolic sign guard, such as `D > 0` or `D < 0`, rather than `D = model(D)`.
   - Flips inequality direction when the selected denominator is negative.
   - Leaves an atom unchanged if it cannot be cleared locally.

This keeps the current fallback structure: if preprocessing fails or produces a form that projection rejects, callers can still fall back to substitution-based generalization.

The second pass should be best-effort. It should improve atoms it understands, but it should not force formula-wide substitution just because one atom contains an unsupported construct or a denominator that is zero in the current model. Leaving such an atom unchanged is sound, and wide projection may still find an implicant that does not depend on it.

## Logic-Specific Behavior

### `LRA`

True linear real arithmetic should not contain symbolic division. Any acceptable real division in `LRA` should have a rational constant denominator.

Behavior:

- Rewrite `(/ t c)` to `(* (/ 1 c) t)` when `c` is a nonzero rational constant.
- If `c` is rational zero inside an arithmetic atom, the preferred best-effort behavior is to leave that atom unchanged and let projection try to omit it.
- If the implementation does not have an atom-local path for `LRA`, rational-zero denominators may still fail preprocessing and use the existing fallback.
- If `RDIV` has a nonconstant denominator, treat it as outside the intended `LRA` fragment and fail preprocessing so the existing fallback path is used.
- Do not clear symbolic denominators in `LRA`, because doing so can introduce products and leave linear arithmetic.

Example:

```smt2
(<= (/ (+ x 1) 3) y)
```

becomes:

```smt2
(<= (* (/ 1 3) (+ x 1)) y)
```

No guard is needed because the denominator is syntactically the nonzero constant `3`.

### `NRA`

Nonlinear real arithmetic can accept products introduced by clearing denominators.

Behavior:

- Rewrite constant-denominator real division immediately, as in `LRA`.
- Leave symbolic-denominator `RDIV` terms in place during the construct-elimination pass.
- In the second pass, clear symbolic denominators inside arithmetic atoms.
- Add sign guards selected from the model.

Example:

```smt2
(<= (/ x y) z)
```

If `model(y) > 0`, rewrite to:

```smt2
(and
  (> y 0)
  (<= x (* z y)))
```

If `model(y) < 0`, rewrite to:

```smt2
(and
  (< y 0)
  (>= x (* z y)))
```

### `LIA` and `NIA`

Integer division and modulus are not rational division. They should not be handled by the real-fraction clearing algorithm.

Behavior:

- Keep the current special cases for `IDIV` and `IMOD`.
- Preserve the existing fallback behavior for unsupported integer division/modulus cases.
- Do not apply real denominator clearing to `IDIV` or `IMOD`.
- If real division occurs in an integer logic through mixed arithmetic, only constant nonzero real denominators should be rewritten directly. Symbolic real denominators should fail preprocessing unless there is a clear mixed-real `NRA` context.

## Required API Changes

The current function:

```ocaml
val projection_preprocess : SModel.t -> Term.t -> Term.t
```

does not know the target logic. Make it logic-aware:

```ocaml
val projection_preprocess : logic:SolverState.logic -> SModel.t -> Term.t -> Term.t
```

This matches the type already exposed by `QF_API.generalize_model` in `src/QF_API.mli`.
If keeping `projection_preprocess` private inside `QF_API.ml`, the function can use the
same concrete polymorphic variant shape directly:

```ocaml
val projection_preprocess :
  logic:[ `NRA | `NIA | `LRA | `LIA | `BV | `Other ] ->
  SModel.t ->
  Term.t ->
  Term.t
```

Then update the call site in `generalize_model`:

```ocaml
let true_of_model' = projection_preprocess ~logic smodel true_of_model
```

If exposing the full logic type in `QF_API.mli` is inconvenient, introduce a small local mode:

```ocaml
type projection_preprocess_mode =
  | Linear_real
  | Nonlinear_real
  | Integer
  | Other
```

and map the existing `logic` value to that mode at the call site.

## Data Structures

Introduce an internal representation for arithmetic fractions:

```ocaml
type frac = {
  num : Term.t;
  den : Term.t;
  guards : Term.t list;
}
```

Meaning:

```text
frac represents num / den under guards
```

The `den` field must be division-free after fraction construction. The `guards` field contains conditions needed to preserve the meaning of divisions encountered while constructing the fraction.

The simplest implementation can maintain `guards` separately from `frac`:

```ocaml
type frac = Term.t * Term.t
```

and return:

```ocaml
(frac * Term.t list) option
```

The `None` case means the current atom cannot be safely normalized and should be left unchanged. The record form is more readable and less error-prone if the implementation keeps guards inside `frac`.

## Helper Predicates

Add helpers for constant rational detection:

```ocaml
val rational_const_opt : Term.t -> Q.t option
```

Expected behavior:

- Return `Some q` if the term is syntactically a rational constant.
- Return `None` otherwise.
- Do not ask the model for this check.

Use this for direct constant-denominator rewrites. Model evaluation is only for choosing a sign branch for symbolic denominators and for existing model-based construct elimination.

Add helpers for sign selection:

```ocaml
val model_sign : SModel.t -> Term.t -> [ `Pos | `Neg | `Zero ]
```

Behavior:

- Evaluate the term in the model.
- Return `Zero` if the value is rational zero.
- Return `Pos` if the value is greater than zero.
- Return `Neg` if the value is less than zero.

In pass 2, a zero denominator should cause the current atom rewrite attempt to be abandoned, not a formula-wide preprocessing failure. In pass 1, keep the existing conservative behavior unless a later implementation deliberately makes real division handling fully atom-local.

## Pass 1: Construct Elimination

Rename or split the current function:

```ocaml
projection_preprocess_aux
```

into a first-pass function:

```ocaml
projection_eliminate_constructs :
  mode:projection_preprocess_mode ->
  SModel.t ->
  Term.t ->
  Term.t list ->
  Term.t * Term.t list
```

This pass should keep the current guard-threading style.

### Real Division in Pass 1

Current behavior:

```ocaml
| Term(A2(`YICES_RDIV, num, denum)) ->
   ...
   Term.Arith.mul cst num,
   Term.eq denum (rational_term denum_value) :: guards
```

Replace it with:

1. Recurse into numerator and denominator.
2. If denominator is syntactically a nonzero rational constant, rewrite to multiplication by its inverse.
3. If denominator is syntactically zero:
   - In `Nonlinear_real`, rebuild `RDIV` with rewritten children and leave the containing atom for pass 2.
   - In `Linear_real`, `Integer`, or `Other`, fail preprocessing unless the implementation has an atom-local best-effort path for that mode.
4. If denominator is nonconstant:
   - In `Nonlinear_real`, rebuild `RDIV` with rewritten children and leave it for pass 2.
   - In `Linear_real`, `Integer`, or `Other`, raise an exception that triggers fallback.

Important: do not add `den = model(den)` for real division in the new path.

### Integer Division and Modulus in Pass 1

Keep the current conservative behavior:

- For `IDIV`:
  - Raise on model-zero denominator.
  - Preserve the simplifications for denominator model value `1` and `-1` when valid.
  - Otherwise replace with the model value and guard operands to their model values.

- For `IMOD`:
  - Raise on model-zero denominator.
  - Preserve simplification to zero for denominator model value `1` or `-1`.
  - Otherwise replace with the model value and guard operands to their model values.

This can be improved later, but it should stay separate from real division clearing.

### `abs`

Keep current model-selected rewriting:

```text
abs(arg) = arg    under arg >= 0
abs(arg) = -arg   under arg <= 0
```

This is useful because it avoids leaving unsupported `abs` in terms sent to projection.

### `floor` and `ceil`

Keep current interval-guard rewriting:

```text
floor(arg) = k    under k <= arg < k + 1
ceil(arg) = k     under k - 1 < arg <= k
```

where `k` is selected from the model.

### `ite`

Keep current model-selected branch behavior:

- Recurse into the condition.
- Recurse only into the branch selected by the model.
- Add either the rewritten condition or its negation as a guard.

This avoids imposing guards from dead branches, especially guards from dead branch denominators.

## Pass 2: Division Clearing

Add a second pass:

```ocaml
clear_real_divisions_in_atoms :
  SModel.t ->
  Term.t ->
  Term.t list ->
  Term.t * Term.t list
```

This pass walks Boolean structure and rewrites arithmetic atoms.

It should be used only in `Nonlinear_real` mode. For `Linear_real`, pass 1 should already have removed all legal real division.

Important: Pass 2 must be applied to both:

- the main formula returned by pass 1; and
- every guard accumulated by pass 1.

Pass-1 guards are ordinary formulas and may still contain symbolic `RDIV`. For example, guards introduced for `abs`, `floor`, `ceil`, selected `ite` conditions, or conservative integer-division fallback can mention rewritten subterms that still contain real division in `Nonlinear_real` mode. Pass 2 should attempt to denominator-clear these guards before final assembly; if a guard atom cannot be cleared, keep that atom unchanged and continue.

### Boolean Traversal

The pass should recurse through Boolean connectives:

- `and`
- `or`
- `not`
- implication, if represented explicitly
- equality over Booleans, if represented explicitly
- any other Boolean application supported by `GuardMTerm.map`

For non-Boolean arithmetic terms outside atoms, leave them unchanged unless they are part of an arithmetic atom.

The safest initial version can reuse the generic `MTerm.map` style and add special cases for arithmetic atoms before the generic case.

If an arithmetic atom cannot be rewritten, keep that atom in its original form and continue traversing the rest of the formula. Do not let one unresolved atom prevent other atoms from being denominator-cleared.

### Arithmetic Atom Detection

Detect atoms with arithmetic sides:

- Equality between arithmetic terms:
  - `YICES_EQ_TERM` where both sides are arithmetic.
- Arithmetic inequalities:
  - `YICES_ARITH_GE_ATOM`, representing `lhs >= rhs`.

The Yices high-level term representation uses `YICES_ARITH_GE_ATOM` as the arithmetic comparison atom. There are no separate `LT`, `LE`, or `GT` atom constructors. The helper constructors encode them in terms of `GE` and Boolean negation:

- `Term.Arith.geq a b` reveals as ``A2(`YICES_ARITH_GE_ATOM, a, b)``.
- `Term.Arith.leq a b` should reveal as ``A2(`YICES_ARITH_GE_ATOM, b, a)``.
- `Term.Arith.lt a b` is represented as `not (a >= b)`.
- `Term.Arith.gt a b` is represented as `not (b >= a)`.

Before implementing Pass 2, confirm this with a small representation spike that builds and reveals:

```ocaml
Term.Arith.lt
Term.Arith.leq
Term.Arith.geq
Term.Arith.gt
Term.eq
```

The current code already uses these helpers:

```ocaml
Term.Arith.lt
Term.Arith.leq
Term.Arith.geq
Term.eq
```

so the spike should print or inspect the exact `Term.reveal` forms in this repository.

Important: `YICES_EQ_TERM` is also used for non-arithmetic equality. Only rewrite equality atoms when both sides satisfy `Term.is_arithmetic`.

### Fraction Normalization

Implement:

```ocaml
fraction_of_arith :
  SModel.t ->
  Term.t ->
  frac option
```

For a term `t`, return `Some frac` when the term can be normalized, where `frac` represents `num / den` and guards such that:

```text
guards imply t = num / den
```

and `den` is division-free.

Return `None` when the term cannot be normalized without making an unsupported assumption. The caller must then leave the whole arithmetic atom unchanged and discard any guards generated while attempting to normalize it.

The conceptual algebra is ordinary fraction algebra, but the implementation must match the actual Yices term representation. Arithmetic is normalized into:

- `Sum of (Q.t * Term.t option) list`, representing a linear combination of constants and scaled terms.
- `Product of bool * (Term.t * uint) list`, representing a product of powers. In the bindings, the boolean is true for bitvector power products and false for arithmetic power products, so arithmetic normalization should expect `Product(false, factors)`.
- ``A2(`YICES_RDIV, a, b)``, representing real division that survived construction.

There are no dedicated binary addition, binary multiplication, subtraction, or unary negation constructors. Those operations usually reveal as `Sum` or `Product`.

Before implementing this function, confirm how symbolic `RDIV` is embedded by revealing a term such as:

```smt2
(<= (/ x y) z)
```

The expected shape is either a direct ``A2(`YICES_RDIV, x, y)`` in an arithmetic position, or an `RDIV` term used as a base inside a `Sum` or `Product`. The exact shape determines which recursive cases need to peel into term bases.

Rules:

#### Constants, Variables, and Unsupported Arithmetic Leaves

For any division-free arithmetic term treated as atomic:

```text
t -> t / 1
```

No guards.

This includes variables, rational constants, and arithmetic applications that are not explicitly normalized in the first implementation.

#### `Sum`

For:

```ocaml
Sum terms
```

where each element is:

```ocaml
(coeff, None)
(coeff, Some base)
```

interpret the list as:

```text
sum_i coeff_i * base_i
```

with `None` standing for the constant term `1`.

Convert each monomial to a fraction:

```text
coeff * base -> (coeff * base_num) / base_den
coeff        -> coeff / 1
```

Then fold the ordinary fraction-addition rule over the list:

```text
(an / ad) + (bn / bd) = (an * bd + bn * ad) / (ad * bd)
```

This covers addition, subtraction, unary negation, and rational scaling. For example, a bare `-x` is represented as a `Sum` entry with coefficient `-1`.

If the `Sum` list is empty, return `0 / 1`.

#### `Product`

For:

```ocaml
Product (false, factors)
```

where each factor is:

```ocaml
(base, exponent)
```

interpret the product as:

```text
product_i base_i ^ exponent_i
```

Convert each `base` recursively to a fraction and fold multiplication:

```text
(an / ad) * (bn / bd) = (an * bn) / (ad * bd)
```

For an exponent greater than one, multiply the same base fraction repeatedly, or add a small helper:

```ocaml
frac_pow : frac -> int -> frac
```

Convert the binding's unsigned exponent to an OCaml `int` for small helper loops, following the existing local style that uses `Unsigned.UInt.to_int`.

If the arithmetic product is empty, return `1 / 1`.

If `Product(true, factors)` appears, it is a bitvector product and should not be handled by arithmetic fraction normalization.

#### Real Division

For:

```text
(/ a b)
```

where:

```text
a -> an / ad
b -> bn / bd
```

the result is:

```text
(an * bd) / (ad * bn)
```

The denominator includes `bn`, so add a sign guard for `bn`.

Use the model to choose:

```text
bn > 0
```

or:

```text
bn < 0
```

If `model(bn) = 0`, return `None` for the current fraction-normalization attempt. The atom rewriter should leave the original atom unchanged and add no guards from the failed attempt.

Do not add a sign guard for `bd` here only because it appears in the denominator of `b`; the recursive fraction for `b` must already have added the guards needed to make `b` well-defined. However, the final atom-clearing step will add a sign guard for the final common denominator used to multiply through.

Guard generation inside `fraction_of_arith` must be transactional: guards discovered while trying to normalize an atom are committed only if the whole atom is successfully rewritten. If any recursive subterm returns `None`, discard those tentative guards.

#### Direct Binary Fallback

If the representation spike shows any direct arithmetic composite forms other than `Sum`, `Product`, and `RDIV`, add cases for them only after confirming their revealed constructors. Do not write speculative cases for nonexistent `ADD`, `SUB`, `MUL`, or `NEG` constructors.

For any unsupported arithmetic node:

```text
t -> t / 1
```

is acceptable only if `t` is known to be division-free and acceptable to projection.

If `t` may contain `RDIV`, function applications, tuples, tuple projection, updates, lambda/application constructs, or any other term form that the fraction normalizer cannot safely inspect, return `None`. The atom rewriter should then keep the original atom unchanged. This preserves a chance that wide projection can choose an implicant that does not mention the unresolved atom.

#### Conceptual Binary Rules

The following identities are the algebra implemented by the `Sum` and `Product` cases:

- Addition:

```text
(an / ad) + (bn / bd) = (an * bd + bn * ad) / (ad * bd)
```

- Subtraction:

```text
(an / ad) - (bn / bd) = (an * bd - bn * ad) / (ad * bd)
```

- Negation:

```text
-(an / ad) = (-an) / ad
```

- Multiplication:

```text
(an / ad) * (bn / bd) = (an * bn) / (ad * bd)
```

These are documentation for the `Sum`/`Product` implementation, not separate constructor cases.

#### Optional Simplification

Add lightweight simplification helpers to control term growth:

```ocaml
arith_mul : Term.t -> Term.t -> Term.t
arith_add : Term.t -> Term.t -> Term.t
arith_sub : Term.t -> Term.t -> Term.t
```

They should simplify only obvious identities:

- `0 * t = 0`
- `1 * t = t`
- `t * 1 = t`
- `0 + t = t`
- `t + 0 = t`
- `t - 0 = t`
- `-0 = 0`

Avoid aggressive algebraic simplification in the first implementation. Correctness matters more than compactness, and Yices may already simplify terms internally.

## Atom Rewriting

The implementation should rewrite the two arithmetic atom shapes that actually appear in the Yices high-level representation:

- ``A2(`YICES_EQ_TERM, lhs, rhs)`` when both sides are arithmetic.
- ``A2(`YICES_ARITH_GE_ATOM, lhs, rhs)``, representing `lhs >= rhs`.

Strict inequalities are represented by Boolean negation around a `GE` atom, so the Boolean traversal must also special-case:

```ocaml
A1(`YICES_NOT_TERM, ge_atom)
```

For any arithmetic comparison, compute:

```text
lhs - rhs -> N / D
```

Then rewrite according to the atom kind.

Use the model to evaluate `D`:

- If `model(D) > 0`, add guard `D > 0`.
- If `model(D) < 0`, add guard `D < 0`.
- If `model(D) = 0`, abandon the rewrite for this atom and keep the original atom unchanged.

The final guard on `D` allows multiplication by `D` while preserving the selected sign branch.

The atom rewrite should have an explicit result type, for example:

```ocaml
type atom_rewrite =
  | Rewritten of Term.t * Term.t list
  | Unchanged
```

Use `Unchanged` when fraction normalization returns `None`, when a denominator evaluates to zero, or when the atom contains constructs the second pass does not understand. In the `Unchanged` case, add no denominator guards from the failed attempt.

### Equality

For:

```text
lhs = rhs
```

with:

```text
lhs - rhs = N / D
```

rewrite to:

```text
N = 0
```

and add the final sign guard for `D`.

Strictly, equality only needs `D != 0`, but the sign guard is acceptable and model-local. It also keeps guard construction uniform.

### Disequality

Disequality is expected to appear as `not (= lhs rhs)`. When the Boolean traversal sees `not` over an arithmetic equality, rewrite the inner equality and then negate the rewritten equality:

```text
not (N = 0)
```

with the same denominator sign guards.

There is no separate direct disequality atom expected in the Yices high-level representation.

### Non-strict `GE`

For the actual atom:

```text
lhs >= rhs
```

with:

```text
lhs - rhs = N / D
```

if `model(D) > 0`, rewrite to:

```text
N >= 0
```

if `model(D) < 0`, rewrite to:

```text
N <= 0
```

Other non-strict comparisons are encoded through argument order. For example, `lhs <= rhs` should arrive as `rhs >= lhs`, so the same `GE` rewrite applies.

### Strict Inequality via `not GE`

For a strict comparison represented as:

```text
not (lhs >= rhs)
```

with:

```text
lhs - rhs = N / D
```

if `model(D) > 0`, rewrite to:

```text
not (N >= 0)
```

if `model(D) < 0`, rewrite to:

```text
not (N <= 0)
```

The implementation may build these as the corresponding strict helper calls:

- `N < 0` when `model(D) > 0`.
- `N > 0` when `model(D) < 0`.

This is semantically the same, but the code should remember that the revealed representation will likely be `not GE` again.

### Greater-Than Forms

`lhs > rhs` is expected to arrive as `not (rhs >= lhs)`. No separate `GT` atom case is needed.

## Guard Management

There are two guard sources:

1. Construct-elimination guards from pass 1:
   - `abs` branch guards.
   - `floor` and `ceil` interval guards.
   - selected `ite` condition guards.
   - conservative `IDIV` and `IMOD` value guards.

2. Division-clearing guards from pass 2:
   - divisor sign guards inside nested `RDIV`.
   - final common denominator sign guards for each arithmetic atom.

Pass 2 must process pass-1 guards before final assembly. The intended sequencing is:

```ocaml
let main1, guards1 = projection_eliminate_constructs ... true_of_model [] in
let main2, guards2 = clear_real_divisions_in_atoms smodel main1 [] in
let process_guard (processed_guards, extra_guards) guard =
  let guard', extra_guards = clear_real_divisions_in_atoms smodel guard extra_guards in
  guard' :: processed_guards, extra_guards
in
let guards1', guards3 = List.fold_left process_guard ([], guards2) guards1 in
Term.andN (main2 :: List.rev_append guards1' guards3)
```

The exact OCaml shape can differ, but the invariant must not: no pass-1 guard may bypass Pass 2.

All processed guards should be conjoined at the top:

```ocaml
Term.andN (rewritten_formula :: guards)
```

Do not place guards only next to a subformula unless the Boolean context is carefully handled. Top-level conjunction is consistent with current `projection_preprocess`, which constructs a model-based under-approximation of the formula.

The model must satisfy every generated guard. This is important because the resulting formula is sent to model projection using the same model.

## Soundness Condition

The preprocessing result does not need to be equivalent to the input globally. It needs to be a model-preserving under-approximation:

```text
preprocessed_formula => original_formula
```

and:

```text
model satisfies preprocessed_formula
```

For real division clearing, this is achieved by:

- Adding guards that make every denominator nonzero.
- Choosing sign guards that match the model.
- Flipping inequalities exactly when multiplying by a negative denominator.
- Leaving any atom unchanged when these conditions cannot be established locally.

For equalities, `D != 0` is enough for equivalence of:

```text
N / D = 0
```

and:

```text
N = 0
```

Using `D > 0` or `D < 0` is stronger but still model-preserving and less restrictive than freezing `D` to a concrete rational value.

For unchanged atoms, soundness is immediate: the preprocessed formula still contains the same atom from pass 1. The only tradeoff is completeness of the projection attempt. Yices may reject the remaining construct, or wide projection may find an implicant that avoids it.

## Failure Behavior

Pass 2 should not fail preprocessing for local atom-level problems. The following cases should leave the current atom unchanged and continue:

- A denominator in the current atom evaluates to zero in the current model.
- The atom contains real division but cannot be normalized safely.
- The atom contains function application, tuples, tuple projection, updates, bindings, or another construct the fraction normalizer does not inspect.
- The atom has an arithmetic shape that is not one of the supported `EQ`, `GE`, `not EQ`, or `not GE` forms.

This is sound because an unchanged atom still means exactly what it meant in the pass-1 formula. It is also useful because wide projection may find a model-preserving implicant that simply omits that atom.

The following cases may still fail preprocessing and let the existing caller fall back to substitution:

- `LRA` contains nonconstant real division and the implementation chooses not to attempt best-effort projection on such formulas.
- Pass 1 reaches an unsupported construct where it cannot preserve the original term.
- Final term construction fails or Yices rejects the preprocessed formula during projection.

The implementation can keep using exceptions for pass-1 failures. For pass-2 local failures, prefer an explicit `Unchanged` result over exceptions. If exceptions are convenient internally, catch them inside the atom rewriter and convert them to `Unchanged` before returning to the Boolean traversal.

For true fatal unsupported cases, introduce a local exception:

```ocaml
exception Projection_preprocess_unsupported
```

or reuse a simple failure if the current caller catches all exceptions. A named exception is preferable because it makes debug output and future narrowing easier.

## Implementation Steps

### Step 1: Make Preprocessing Logic-Aware

- Update `projection_preprocess` to accept `~logic` or a local preprocessing mode.
- Update the call site in `generalize_model`.
- Keep behavior unchanged initially by mapping all arithmetic logics to the current implementation.
- Build after this mechanical change.

### Step 2: Split Pass 1 from Final Assembly

- Rename the current recursive body to `projection_eliminate_constructs`.
- Keep the same guard-threading behavior.
- Preserve all existing cases.
- Have `projection_preprocess` call pass 1 and conjoin guards as before.
- Build and run existing regression tests.

### Step 3: Change `RDIV` Handling in Pass 1

- Add syntactic rational-constant detection.
- Rewrite `RDIV` with nonzero constant denominator to multiplication by the reciprocal.
- In `Nonlinear_real`, leave syntactic zero denominator `RDIV` for pass 2 so the containing atom can be left unchanged.
- In non-NRA modes, keep conservative fallback behavior for syntactic zero denominator unless an atom-local best-effort path is added there too.
- In `Nonlinear_real`, rebuild nonconstant `RDIV` for pass 2.
- In `Linear_real`, fail preprocessing on nonconstant `RDIV`.
- Remove the old `den = model(den)` guard for `RDIV`.
- Add focused tests for constant denominator behavior.

### Step 3.5: Spike the Revealed Term Representation

Before implementing fraction normalization, build small arithmetic terms and inspect `Term.reveal`.

Confirm:

- How `(/ x y)` is represented when `y` is symbolic.
- Whether `(/ x y)` appears directly as ``A2(`YICES_RDIV, x, y)`` or as a base inside `Sum`/`Product`.
- How `x / y <= z` reveals after construction.
- How `Term.Arith.lt`, `leq`, `geq`, and `gt` reveal.
- How `Term.not1` over arithmetic atoms reveals.

This spike should determine the exact pattern matches in `fraction_of_arith` and the Boolean traversal. Do it before writing the core recursive normalization code.

### Step 4: Add Fraction Normalization

- Implement the `frac` type.
- Implement `fraction_of_arith`.
- Cover constants, variables, `Sum`, `Product`, and `RDIV`.
- Treat addition, subtraction, negation, and rational scaling through the `Sum` case.
- Treat multiplication and powers through the `Product` case.
- Add helper constructors for arithmetic identity simplification.
- Add helper to evaluate a term sign in the model.
- Build after this step even before integrating atom rewriting.

### Step 5: Add Atom Rewriting

- Implement `rewrite_arith_atom`.
- Give it an explicit `Rewritten`/`Unchanged` result.
- Support the actual arithmetic atom constructors:
  - ``A2(`YICES_EQ_TERM, lhs, rhs)`` where both sides are arithmetic.
  - ``A2(`YICES_ARITH_GE_ATOM, lhs, rhs)``.
- In Boolean traversal, support `not` over arithmetic equality and `not` over arithmetic `GE`.
- For each supported atom:
  - Compute `lhs - rhs`.
  - Normalize to `N / D`.
  - Add final denominator sign guard.
  - Produce a division-free atom.
- Ensure strict inequalities remain strict.
- Ensure non-strict inequalities remain non-strict.
- Ensure inequality direction flips when `model(D) < 0`.
- Return `Unchanged` instead of raising when an atom contains unsupported constructs or a denominator whose model value is zero.
- Commit generated guards only when the atom is successfully rewritten.

### Step 6: Add Pass 2 Boolean Traversal

- Implement `clear_real_divisions_in_atoms`.
- Recurse over Boolean structure.
- Apply `rewrite_arith_atom` before generic traversal.
- Apply pass 2 to the pass-1 main formula and to every pass-1 guard.
- Conjoin generated guards at the top.
- Use pass 2 only for `Nonlinear_real`.
- After pass 2, optionally record whether any `YICES_RDIV` remains in the final conjunction. Remaining `RDIV` is allowed only inside atoms that were deliberately left unchanged.

### Step 7: Preserve Fallback Behavior

- Keep the existing `try ... with _ -> substitution ()` in `generalize_model`.
- Prefer catching only preprocessing/projection-related exceptions later, but do not change that behavior as part of this feature unless needed.
- Add debug prints under an existing debug channel if helpful:
  - original atom
  - rewritten atom
  - generated denominator guards

### Step 8: Add Regression Tests

Add small `.smt2` regressions that exercise:

1. Constant denominator in `LRA`:
   - `(/ x 3)` is rewritten without a guard freezing `3`.

2. Symbolic denominator in `NRA`, positive model sign:
   - `x / y <= z`
   - expected guard: `y > 0`
   - expected rewritten inequality: `x <= z * y`

3. Symbolic denominator in `NRA`, negative model sign:
   - `x / y <= z`
   - expected guard: `y < 0`
   - expected rewritten inequality: `x >= z * y`

4. Equality with symbolic denominator:
   - `x / y = z`
   - expected rewrite: `x - z * y = 0`, with sign guard on `y`.

5. Multiple denominators:
   - `x / y + a / b <= c`
   - expected guards on `y`, `b`, and the final common denominator.

6. Nested real division:
   - `x / (y / z) <= w`
   - expected guards sufficient to ensure both `z` and `y` are nonzero.

7. Dead-branch division:
   - `ite` where the unselected branch contains division by zero.
   - should not raise.

8. Selected-branch division by zero:
   - pass 2 should leave the affected atom unchanged.
   - preprocessing should continue and still give wide projection a chance to omit that atom.
   - if Yices projection rejects the final formula, the existing outer fallback still applies.

9. `LRA` symbolic denominator:
   - should fail preprocessing and fall back rather than create nonlinear products.

10. Unsupported construct inside an arithmetic atom:
    - include a function application or tuple-related term inside an atom with `RDIV`.
    - pass 2 should leave that atom unchanged and continue rewriting other atoms.

11. Existing integer division and modulus cases:
    - ensure behavior does not regress.

### Step 9: Compare Projection Quality

Use existing wide projection and arithmetic regressions to compare:

- Number of cases where preprocessing succeeds.
- Number of cases where projection succeeds.
- Size of projected cubes.
- Runtime impact.
- Whether fewer substitutions are needed after failed projection.

The important qualitative check is that denominators are no longer frozen to exact rational model values in `NRA`.

## Examples

### Example 1: Simple Positive Denominator

Input:

```smt2
(<= (/ x y) 5)
```

Model:

```text
y = 2
```

Rewrite:

```smt2
(and
  (> y 0)
  (<= x (* 5 y)))
```

### Example 2: Simple Negative Denominator

Input:

```smt2
(<= (/ x y) 5)
```

Model:

```text
y = -2
```

Rewrite:

```smt2
(and
  (< y 0)
  (>= x (* 5 y)))
```

### Example 3: Both Sides Have Denominators

Input:

```smt2
(< (/ x y) (/ a b))
```

Equivalent difference:

```text
x / y - a / b = (x*b - a*y) / (y*b)
```

If:

```text
model(y*b) > 0
```

rewrite:

```smt2
(and
  sign guards needed for y and b
  (> (* y b) 0)
  (< (- (* x b) (* a y)) 0))
```

If:

```text
model(y*b) < 0
```

rewrite:

```smt2
(and
  sign guards needed for y and b
  (< (* y b) 0)
  (> (- (* x b) (* a y)) 0))
```

### Example 4: Equality

Input:

```smt2
(= (/ (+ x 1) y) z)
```

Difference:

```text
((x + 1) - z*y) / y
```

If:

```text
model(y) > 0
```

rewrite:

```smt2
(and
  (> y 0)
  (= (- (+ x 1) (* z y)) 0))
```

Using `y > 0` is stronger than `y != 0`, but it is model-preserving and avoids freezing `y`.

## Risks and Mitigations

### Term Growth

Clearing denominators can duplicate denominator terms and grow expressions quickly.

Mitigation:

- Use simple identity simplifications.
- Keep products factored where possible.
- Do not expand multiplication over addition.
- Consider sharing with `let` only if the term API and projection path support it well.

### Term Representation Mismatch

The conceptual algebra uses addition, subtraction, negation, and multiplication, but the Yices high-level representation normalizes arithmetic into `Sum` and `Product`. Implementing against nonexistent binary arithmetic constructors would miss the real cases.

Mitigation:

- Run the representation spike before implementing `fraction_of_arith`.
- Pattern-match `Sum`, `Product`, and ``A2(`YICES_RDIV, _, _)`` first.
- Treat the binary algebra rules as identities implemented through `Sum`/`Product`, not as separate expected constructors.

### Incorrect Inequality Direction

The main soundness risk is failing to flip inequalities when multiplying by a negative denominator.

Mitigation:

- Centralize sign selection in one helper.
- Centralize comparison rewriting in one function.
- Add tests for positive and negative denominator models for `GE` and `not GE`, since other comparison helpers are encoded through those forms.

### Missing Divisor Guards

Nested divisions can lose nonzero requirements if only the final common denominator is guarded.

Mitigation:

- For successfully rewritten atoms, `fraction_of_arith` must add guards for every divisor introduced by `RDIV`.
- For successfully rewritten atoms, atom rewriting must also add a final sign guard for the denominator used to clear the atom.
- If any required divisor guard cannot be generated because the denominator evaluates to zero, leave the atom unchanged and discard tentative guards.

### Unresolved Atoms

Some atoms may still contain constructs that pass 2 does not understand, such as function applications, tuples, tuple destructors, updates, bindings, or other non-arithmetic structure. Some atoms may also contain divisions whose denominators evaluate to zero in the current model.

Mitigation:

- Treat pass 2 as best-effort per atom.
- Leave unresolved atoms unchanged.
- Continue rewriting other atoms in the same formula or guard.
- Let wide projection attempt to find an implicant that does not depend on unresolved atoms.
- Keep the existing outer fallback for cases where Yices projection rejects the remaining formula.

### Applying NRA Rewrites in LRA

Clearing symbolic denominators in `LRA` can create nonlinear terms.

Mitigation:

- Make preprocessing logic-aware.
- Permit symbolic denominator clearing only in `Nonlinear_real`.
- Fail preprocessing on nonconstant denominator `RDIV` in `Linear_real`.

### Boolean Contexts

Adding all guards at the top creates an under-approximation. This is consistent with current preprocessing, but it is stronger than a locally guarded equivalence inside disjunctions.

Mitigation:

- Keep the model-based under-approximation invariant explicit.
- Test formulas with disjunctions and negations.
- Ensure the current model satisfies all generated guards.

## Acceptance Criteria

The feature is ready when:

- `projection_preprocess` is logic-aware.
- Constant-denominator real division is rewritten without equality guards.
- Symbolic real division in `NRA` is cleared at arithmetic atoms with sign guards.
- Atoms that cannot be safely cleared are left unchanged rather than causing immediate formula-wide fallback.
- Symbolic real division in `LRA` does not produce nonlinear rewrites.
- Fraction normalization handles the actual `Sum` and `Product` revealed forms.
- Atom rewriting handles arithmetic `YICES_EQ_TERM`, arithmetic `YICES_ARITH_GE_ATOM`, and their negated Boolean forms.
- Existing `abs`, `floor`, `ceil`, `ite`, `IDIV`, and `IMOD` behavior is preserved.
- Successfully rewritten atoms contain no `RDIV`; any remaining `RDIV` appears only inside atoms deliberately left unchanged.
- The current model satisfies every generated guard.
- Regression tests cover positive, negative, zero, nested, and dead-branch denominator cases.
- Regression tests cover unsupported constructs inside atoms and verify pass 2 keeps traversing other atoms.
- Existing regression tests pass.

## Suggested Implementation Order

1. Make the API logic-aware.
2. Preserve current behavior through a mechanical refactor.
3. Rewrite constant denominator `RDIV` directly.
4. Spike `Term.reveal` shapes for symbolic `RDIV`, comparisons, and negation.
5. Add `Sum`/`Product`-based fraction normalization helpers.
6. Add atom-level denominator clearing for `NRA`.
7. Add focused regression tests.
8. Run broad arithmetic regressions and compare behavior.
