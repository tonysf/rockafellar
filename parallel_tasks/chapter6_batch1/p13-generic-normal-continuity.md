# Copy/paste prompt: P13 generic normal continuity

You are the P13 worker for the first parallel Chapter 6 batch in the
`lean_rockafellar` repository. Audit and formalize Proposition 6.49 using the
already-proved generic continuity theorem from Chapter 5. The printed
arbitrary-set wording must be checked against this repository's convention
that `normalCone C x = ∅` off `C`; do not hide a necessary hypothesis.

## Starting state and branch

Use an isolated checkout and create
`chapter6-p13-generic-normal-continuity` from exactly:

```text
b2eb4ea92faefd721b93eba48422a6c204d61fc9
```

```text
git switch -c chapter6-p13-generic-normal-continuity b2eb4ea
git rev-parse HEAD
git status --short
```

Never reset an existing branch. Stop if the full hash differs or the starting
worktree is dirty.

## Exclusive ownership

Create and edit only:

```text
RockafellarWets/Chapter6/GenericNormalContinuity.lean
```

Do not edit existing source, `README.md`, `CHAPTER6_COVERAGE.md`, any ledger,
`RockafellarWets/Chapter6.lean`, `RockafellarWets.lean`, lake configuration,
anything in `parallel_tasks/`, or another prompt-owned file. Do not import any
unmerged P1--P14 module.

Place every new declaration in `namespace RW`.

## Objective and statement audit

Proposition 6.49 is on book page 232 (PDF page 240). It says that points of
the boundary of `C` where `normalCone C` is not continuous relative to that boundary
form a meager subset, hence continuity points are dense.

Mathlib calls the topological boundary `frontier C`; use `frontier`, not an
invented `boundary` identifier, in every Lean declaration.

First inspect the definitions and prove the strongest statement justified by
the repository APIs. The minimum required, faithful closed-set theorem shapes
are:

```lean
theorem isMeagre_not_svContinuousWithinAt_normalCone_frontier
    [FiniteDimensional ℝ E] {C : Set E} (hC : IsClosed C) :
    IsMeagre
      {x : frontier C |
        ¬ SvContinuousWithinAt (normalCone C) (frontier C) (x : E)}

theorem dense_svContinuousWithinAt_normalCone_frontier
    [FiniteDimensional ℝ E] {C : Set E} (hC : IsClosed C) :
    Dense
      {x : frontier C |
        SvContinuousWithinAt (normalCone C) (frontier C) (x : E)}
```

Also expose the semicontinuity restriction used by the proof, for example:

```lean
SvOscOn (normalCone C) (frontier C)
```

under `IsClosed C`.

Then audit the exact arbitrary-set wording. If it is provable under the Lean
definitions, add the hypothesis-free versions and derive the closed versions.
If it is not, retain the closed-set theorems and explain the mismatch precisely
in the module docstring. In particular test the dense nonclosed-set obstruction:
off `C` the mapping is empty, while on a dense set its normal values may be
nonempty, so outer semicontinuity on the whole boundary does not follow from
`svOscOn_normalCone C`. Do not assert the printed generality merely because it
appears in the book. A corrected formulation relative to `C ∩ frontier C`
may be included if it is both meaningful and proved, but it does not replace
the required closed-set result.

The density corollary is required, not optional. State meagerness in the
subtype `frontier C`, matching Chapter 5's convention.

## Existing APIs and proof route

Use only base-commit modules, especially:

- `RockafellarWets/Chapter5/GenericContinuity.lean`:
  `isMeagre_not_svContinuousWithinAt_of_svOscOn`;
- `RockafellarWets/Chapter5/Semicontinuity.lean` and
  `SemicontinuityCriteria.lean` for restriction/monotonicity lemmas;
- `RockafellarWets/Chapter6/NormalCones.lean`:
  `svOscOn_normalCone`, `svOscWithinAt_normalCone`, and the empty-off-set
  convention;
- Mathlib's facts that `frontier C` is closed, a closed subset of a complete
  finite-dimensional space is Baire, and the complement of a meager set is
  dense in a Baire space.

For closed `C`, use `frontier C ⊆ C` and restrict
`svOscOn_normalCone C` to the boundary. Apply the Chapter 5 theorem directly.
For density, work in the boundary subtype and use its Baire-space instance;
do not silently equate ambient and subtype meagerness.

## Exclusions

Do not formalize other results from 6.27--6.48, generic continuity for arbitrary
set-valued maps, new definitions of continuity, or a new normal-cone notion.
Do not change Chapter 5 to make this corollary easier.

## Verification and commit

Run:

```text
lake env lean RockafellarWets/Chapter6/GenericNormalContinuity.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/GenericNormalContinuity.lean
git diff --check
git status --short
```

The search must be empty and status must name only the assigned file. Do not
use `sorry`, `admit`, new axioms, linter suppression, or placeholder theorems.
Commit:

```text
git add RockafellarWets/Chapter6/GenericNormalContinuity.lean
git commit -m "Formalize generic continuity of normal cones"
```

Report the commit hash, exact hypotheses of every public theorem, audit
conclusion for the printed arbitrary-set clause, and verification results.
