# Copy/paste prompt: P11 polarity

You are the P11 worker for the first parallel Chapter 6 batch in the
`lean_rockafellar` repository. Formalize the polar-cone development in
Rockafellar--Wets 6.21--6.24. Work only in the assigned new file, leave no
unproved declarations, and commit the result.

## Starting state and branch

Use an isolated checkout and create
`chapter6-p11-polarity` from exactly:

```text
b2eb4ea92faefd721b93eba48422a6c204d61fc9
```

```text
git switch -c chapter6-p11-polarity b2eb4ea
git rev-parse HEAD
git status --short
```

Do not reset an existing branch. Stop if `HEAD` is not the full hash above or
if the starting worktree is dirty.

## Exclusive ownership

Create and edit only:

```text
RockafellarWets/Chapter6/Polarity.lean
```

Do not edit `README.md`, `CHAPTER6_COVERAGE.md`, any ledger,
`RockafellarWets/Chapter6.lean`, `RockafellarWets.lean`, any lake file,
anything under `parallel_tasks/`, any existing source, or another prompt-owned
file. Do not add umbrella imports or depend on an unmerged P1--P14 module.

Place every new declaration in `namespace RW`.

## Objective and canonical definition

Formalize formula 6(14), Corollary 6.21, Exercise 6.22, and Examples 6.23--6.24
on book pages 215--217 (PDF pages 223--225). P11 owns the canonical Chapter 6
name and sign convention:

```lean
def polarCone (K : Set E) : Set E :=
  {v | ∀ w ∈ K, ⟪v, w⟫_ℝ ≤ 0}
```

Do not substitute Mathlib's nonnegative `ProperCone.innerDual` for this public
definition. Prove a private or public bridge to it and reuse its infrastructure.

Required 6.21 deliverables:

- a membership simp theorem, `0` membership, antitonicity, and the stated
  monotonicity of bipolars;
- `polarCone K` is a closed convex cone;
- polarity ignores convex-conic closure;
- the bipolar identity
  `polarCone (polarCone K) = closure (conicHull K)`;
- hence `K⁺⁺ = K` for every closed convex cone, and involutivity/injectivity
  on that class.

Required 6.22 deliverables, in finite dimensions:

```lean
w ∈ interior K ↔
  ∀ v ∈ polarCone K, v ≠ 0 → ⟪v, w⟫_ℝ < 0

(interior K).Nonempty ↔ IsPointed (polarCone K)
```

State these with the book's `Convex ℝ K` and `IsCone K` hypotheses. Also
formalize the printed replacement clause when `K = polarCone K₀` for a
closed cone `K₀`, if it is not already an immediate corollary of the same
theorem. Include the elementary polar pairs printed after 6.22: zero/univ and
a nonzero ray/homogeneous halfspace. A generic finite-product orthant theorem
is optional; do not block the core result on it.

Required 6.23 deliverable: for a real inner-product submodule `M`, identify the
polar of its carrier with the carrier of `Mᗮ` (orthogonal complement), and
deduce the double-orthogonal identity `Mᗮᗮ = M` in finite dimensions. Do not
use `Mᵛ`, which denotes a different dual construction in this environment.

Required 6.24 deliverables: for convex `C` and `x ∈ C`, prove both directions
of polarity between `normalCone C x` and `tangentCone C x`, preferably as two
set equalities, and prove

```lean
IsPointed (normalCone C x) ↔ (interior C).Nonempty
```

Do not weaken the polarity result to one inclusion.

## Existing APIs and proof route

Start by inspecting:

- `RockafellarWets/Chapter3/GeneratedCones.lean`, especially `conicHull`,
  `ProperCone.innerDual_conicHull`, and the already-proved
  `innerDual_innerDual_eq_closure_conicHull`;
- `RockafellarWets/Chapter3/PointedCones.lean` for `IsPointed` lemmas;
- `RockafellarWets/Chapter6/ConvexSets.lean` for
  `normalCone_eq_of_convex`, `tangentCone_eq_closure_radialCone`, and
  `interior_tangentCone_of_convex`;
- Mathlib's `Submodule.orthogonal`, closure, interior, and finite-dimensional
  separation APIs.

The shortest 6.21 proof is a sign-conversion to `ProperCone.innerDual` followed
by `innerDual_innerDual_eq_closure_conicHull`; normalize inner-product order
with `real_inner_comm`. For 6.24, rewrite the existing 6.9 formulas and use the
bipolar theorem rather than introducing a parallel tangent or normal notion.
The 6.22 strict inequality is the main risk: use finite-dimensional separation
and the existing pointed-cone criteria rather than assuming closedness not
printed in the book.

## Exclusions

Do not formalize supporting-halfspace envelopes (P10), regular tangents (P12),
product formulas, Farkas' lemma, polyhedral polarity, smooth manifolds, or the
generic continuity result. Do not change Chapter 3's `innerDual` convention.

## Verification and commit

Run:

```text
lake env lean RockafellarWets/Chapter6/Polarity.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/Polarity.lean
git diff --check
git status --short
```

The search must be empty, and status must name only the assigned file. No
`sorry`, `admit`, new axiom, disabled linter, or placeholder result is allowed.
Then commit:

```text
git add RockafellarWets/Chapter6/Polarity.lean
git commit -m "Formalize Chapter 6 polar cone correspondence"
```

Report the commit hash, exact theorem inventory, checks run, and any precisely
justified adaptation of a printed clause.
