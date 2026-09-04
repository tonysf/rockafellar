# P04 — Tangent and normal cones to closed intervals

## Objective

Formalize the one-dimensional interval component of Rockafellar–Wets Example 6.10: at a point of a closed real interval, the tangent cone is determined by whether the point is a left endpoint, right endpoint, interior point, or the interval is a singleton; the regular and limiting normal cones have the opposite sign pattern and coincide.

This worker owns the interval building block only. Finite products and the full box theorem will be integrated separately.

## Git setup

- Exact base commit: `b2eb4ea92faefd721b93eba48422a6c204d61fc9` (`b2eb4ea`).
- Required branch name: `chapter6-p04-interval-cones`.
- Start from exactly that commit. Do not merge, rebase, or cherry-pick another batch branch.
- Before editing, confirm that `git rev-parse HEAD` is the exact base above. If it is not, stop and report the blocker.

## Exclusive file ownership

You own exactly one implementation file:

- `RockafellarWets/Chapter6/IntervalCones.lean`

Create that file if it does not exist. Do not edit any other file. In particular, do not edit:

- `README.md`;
- `CHAPTER6_COVERAGE.md` or any other coverage ledger;
- `RockafellarWets/Chapter6.lean`, `RockafellarWets.lean`, or another umbrella import;
- existing Chapter 6 implementation files;
- any file under `parallel_tasks/`, including this prompt, the batch index, or the shared contract;
- files owned by P01, P02, or P03.

## Mathematical deliverables

Work in namespace `RW`, for subsets of `ℝ`. Import `RockafellarWets.Chapter6.ConvexSets` and reuse Theorem 6.9 rather than reproving the general convex normal formula.

### 1. Bounded nondegenerate intervals

For `a < b`, prove the endpoint and interior tangent formulas:

```lean
tangentCone (Set.Icc a b) a = Set.Ici 0
tangentCone (Set.Icc a b) b = Set.Iic 0

-- for a < x < b
tangentCone (Set.Icc a b) x = Set.univ
```

Prove the corresponding exact formulas for both normal notions:

```lean
regularNormalCone (Set.Icc a b) a = Set.Iic 0
normalCone        (Set.Icc a b) a = Set.Iic 0

regularNormalCone (Set.Icc a b) b = Set.Ici 0
normalCone        (Set.Icc a b) b = Set.Ici 0

-- for a < x < b
regularNormalCone (Set.Icc a b) x = {0}
normalCone        (Set.Icc a b) x = {0}
```

Use separate well-named theorems, or a single case theorem plus these statements as corollaries. The endpoint hypotheses must distinguish a genuine one-sided endpoint from a singleton interval.

### 2. Degenerate bounded interval

Prove the fourth case of Example 6.10 through `Icc a a`-specific public
corollaries:

```lean
tangentCone (Set.Icc a a) a = {0}
regularNormalCone (Set.Icc a a) a = Set.univ
normalCone (Set.Icc a a) a = Set.univ
```

P14 owns the canonical generic singleton formulas and theorem names. You may
use a `private` scalar singleton helper internally, but do not publish generic
theorems named like `tangentCone_singleton`, `normalCone_singleton`, or
`regularNormalCone_singleton`.

### 3. Unbounded closed intervals and the whole line

Cover the remaining closed intervals allowed by the book:

```lean
tangentCone (Set.Ici a) a = Set.Ici 0
regularNormalCone (Set.Ici a) a = Set.Iic 0
normalCone (Set.Ici a) a = Set.Iic 0

tangentCone (Set.Iic b) b = Set.Iic 0
regularNormalCone (Set.Iic b) b = Set.Ici 0
normalCone (Set.Iic b) b = Set.Ici 0
```

For `a < x`, show the cones of `Ici a` at `x` are `univ`, `{0}`, `{0}`; state the symmetric result for `x < b` in `Iic b`.

P14 owns the public generic whole-space formulas. If a whole-space calculation
is useful internally, keep it private and P04-specific. The later box assembly
will obtain the unconstrained-coordinate case from P14.

### 4. Regularity and geometric derivability

Record that every point of each closed interval treated above is geometrically derivable and Clarke regular. At minimum provide the bounded-interval statements:

```lean
theorem isGeometricallyDerivable_Icc (hx : x ∈ Set.Icc a b) :
    IsGeometricallyDerivable (Set.Icc a b) x

theorem isClarkeRegularAt_Icc (hx : x ∈ Set.Icc a b) :
    IsClarkeRegularAt (Set.Icc a b) x
```

Derive these from convexity and closedness using `convex_Icc`, `isClosed_Icc`,
`isGeometricallyDerivable_of_convex`, and `isClarkeRegularAt_of_convex`.
Analogous named results for `Ici` and `Iic` are encouraged when short. Any
singleton or whole-line corollary in this file must remain private or have an
unmistakably P04/result-specific name; P14 owns the public generic API.

## Proof guidance and relevant APIs

- `RockafellarWets/Chapter6/ConvexSets.lean`
  - `radialCone`
  - `tangentCone_eq_closure_radialCone`
  - `isGeometricallyDerivable_of_convex`
  - `regularNormalCone_eq_of_convex`
  - `normalCone_eq_regularNormalCone_of_convex`
  - `normalCone_eq_of_convex`
  - `isClarkeRegularAt_of_convex`
- `convex_Icc`, `convex_Ici`, `convex_Iic`, `convex_univ`, and `convex_singleton`
- `isClosed_Icc`, `isClosed_Ici`, `isClosed_Iic`, `isClosed_univ`, and `isClosed_singleton`
- Real inner products simplify to multiplication; useful lemmas and tactics include `real_inner_self_eq_norm_sq`, `simp`, `norm_num`, `positivity`, `linarith`, and `nlinarith`.
- Standard interval lemmas include `Set.mem_Icc`, `Set.mem_Ici`, `Set.mem_Iic`, `Set.Icc_self`, `Set.left_mem_Icc`, `Set.right_mem_Icc`, and the closure formulas for `Ioi` and `Iio` when computing radial-cone closures.

For tangent cones, a direct sequence proof is acceptable, but the preferred route is to compute `radialCone` and use the convex-set theorem. For normal cones, use the convex normal characterization and then the equality of regular and limiting normals.

## Exclusions

- Do not formalize finite Cartesian products or boxes in `ℝⁿ`; P05 owns the
  reusable binary `WithLp 2` product infrastructure.
- Do not define a new bespoke interval datatype unless absolutely necessary; standard sets `Icc`, `Ici`, `Iic`, singleton, and `univ` are the intended interface.
- Do not work on Exercises 6.7–6.9 or later multiplier results.
- Do not edit existing convex-set results.
- Do not import another P01–P14 worker's not-yet-integrated module.
- Do not leave `sorry`, `admit`, `axiom`, disabled linters, or placeholder declarations.

## Verification

Run at minimum:

```bash
lake env lean RockafellarWets/Chapter6/IntervalCones.lean
git diff --check
```

The assigned file must compile from a clean checkout of base commit `b2eb4ea` plus your one new file. Search it for `sorry`, `admit`, `axiom`, disabled linters, and placeholders. Do not add an umbrella import merely to test it.

## Required commit

Commit only the owned file on branch `chapter6-p04-interval-cones` with commit message:

```text
Prove tangent and normal formulas for intervals
```

In your final report, include the commit hash, theorem inventory, exact verification commands and outcomes, and any exact adaptation of a printed statement.
