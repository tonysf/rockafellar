# Copy/paste prompt: P12 regular tangents

You are the P12 worker for the first parallel Chapter 6 batch in the
`lean_rockafellar` repository. Formalize Definition 6.25 and every clause of
Theorem 6.26. This is a high-risk foundational task: keep the definition
filter-native, expose its sequential reading, and commit only a complete,
proved module.

## Starting state and branch

Use an isolated checkout. Create `chapter6-p12-regular-tangents` from exactly:

```text
b2eb4ea92faefd721b93eba48422a6c204d61fc9
```

```text
git switch -c chapter6-p12-regular-tangents b2eb4ea
git rev-parse HEAD
git status --short
```

Do not reset or overwrite an existing branch. Stop if the hash differs or the
starting worktree is dirty.

## Exclusive ownership

Create and edit only:

```text
RockafellarWets/Chapter6/RegularTangents.lean
```

Do not edit any existing file, `README.md`, `CHAPTER6_COVERAGE.md`, any other
ledger, either umbrella import, lake configuration, anything in
`parallel_tasks/`, or another worker's file. Do not import a not-yet-integrated
P1--P14 module.

Place every new declaration in `namespace RW`.

## Objective and definition

Definition 6.25 and Theorem 6.26 are on book pages 217--218 (PDF pages
225--226). Define the regular tangent cone `T̂_C(x)` by formula 6(15), the
joint inner limit of `(C - x') / τ` as `x' →_C x` and `τ ↓ 0`. A suitable
shape is:

```lean
def regularTangentCone (C : Set E) (x : E) : Set E :=
  innerSetLimitAlong
    ((nhdsWithin x C) ×ˢ (nhdsWithin 0 (Set.Ioi (0 : ℝ))))
    (fun p : E × ℝ ↦ blowUp C p.1 p.2)
```

Use the product-filter notation `×ˢ`; `Filter.prod` is not an identifier at
the pinned base commit. Retain the simultaneous two-parameter inner limit. Do
not define the public object only by an opaque sequence predicate.

Required deliverables:

- a `mem_regularTangentCone` theorem giving the neighborhood/filter reading;
- the exact sequential reading printed in 6.25: for every `τν ↓ 0` and
  every `x̄ν →_C x`, select `xν ∈ C` such that
  `(xν - x̄ν) / τν → w`; prove both directions, using first
  countability rather than silently taking it as the definition;
- `0 ∈ regularTangentCone C x`, cone closure under nonnegative scaling,
  closedness, and convexity for `x ∈ C`;
- every regular tangent is derivable, hence
  `regularTangentCone C x ⊆ derivableCone C x` and
  `regularTangentCone C x ⊆ tangentCone C x`;
- the locally closed characterization in 6.26: if
  `IsLocallyClosedAt C x`, then membership is equivalent to saying that for
  every sequence `xν →_C x` there are
  `wν ∈ tangentCone C (xν)` with `wν → w`;
- formula 6(16), preferably exactly

```lean
regularTangentCone C x =
  svInnerLimitWithin (tangentCone C) C x
```

  under `x ∈ C` and `IsLocallyClosedAt C x`.

Use `⊆`, not strict inclusion: the book's glyph in this context means subset.
Do not claim equality with `tangentCone` without a separate regularity
hypothesis; that is a later result.

## Existing APIs and proof route

Inspect and reuse:

- `RockafellarWets/Chapter6/TangentCones.lean`: `blowUp`, `tangentCone`,
  `derivableCone`, their inner/outer-limit formulas, closedness/cone lemmas,
  and `derivableCone_subset_tangentCone`;
- `RockafellarWets/Chapter6/NormalCones.lean`: `IsLocallyClosedAt`;
- `RockafellarWets/Chapter5/SetLimitsAlong.lean`:
  `mem_innerSetLimitAlong`, `isClosed_innerSetLimitAlong`, filter monotonicity,
  and congruence;
- `RockafellarWets/Chapter5/SequentialLimits.lean`, especially the sequential
  characterizations of `svInnerLimitWithin`;
- `RockafellarWets/Chapter5/Semicontinuity.lean` for
  `svInnerLimitWithin`.

Follow the printed proof structure. Closedness is immediate from the inner
limit. Derivability comes from the constant base sequence `x̄ν = x`.
For convexity, first prove the cone property and then show closure under
addition by a two-stage selection: realize `w₀` relative to the arbitrary
base points and then realize `w₁` relative to the selected intermediate
points. For 6(16), localize to a closed neighborhood supplied by
`IsLocallyClosedAt`, prove the closed-set case, and transport back using
eventual equality/locality. Do not assume P14's unmerged locality lemmas.

## Exclusions

Do not formalize Theorems 6.27--6.31, Clarke-regularity equivalences, polarity,
recession directions, product rules, or change-of-coordinate rules. Do not
alter `tangentCone`, `derivableCone`, or any Chapter 5 set-limit definition.

## Verification and commit

Run all of:

```text
lake env lean RockafellarWets/Chapter6/RegularTangents.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/RegularTangents.lean
git diff --check
git status --short
```

The search must return no matches and status must list only the assigned file.
No `sorry`, `admit`, axiom, linter suppression, or placeholder is permitted.
Commit the completed file:

```text
git add RockafellarWets/Chapter6/RegularTangents.lean
git commit -m "Formalize Chapter 6 regular tangent cones"
```

Report the commit hash, theorem inventory, verification output, and the exact
filter used for the joint limit.
