# Copy/paste prompt: P16 limiting-normal change of coordinates

You are the P16 worker for the second parallel Chapter 6 batch in the
`lean_rockafellar` repository. Complete the limiting-normal clause of
Rockafellar--Wets Exercise 6.7. Work only in the assigned new Lean file, prove
every declaration, and commit it.

## Starting state and branch

Use an isolated checkout and create
`chapter6-p16-limiting-normal-change-coordinates` from exactly:

```text
9fa1c19eab36f7fc79845f679d35b87344366e0b
```

Before editing, run:

```text
git rev-parse HEAD
git status --short
```

`HEAD` must be the exact hash above and the worktree must be clean. Do not
merge, rebase, or cherry-pick another worker branch. Do not reset or overwrite
an existing branch; stop and report a blocker if the starting state differs.

## Exclusive ownership

Create and edit only:

```text
RockafellarWets/Chapter6/LimitingNormalChangeOfCoordinates.lean
```

Do not edit any existing source file, `README.md`, `CHAPTER6_COVERAGE.md`, any
other ledger, `RockafellarWets/Chapter6.lean`, `RockafellarWets.lean`, lake
configuration, or anything under `parallel_tasks/`. Do not edit files owned by
P17 or P18. Place every declaration in `namespace RW`.

## Exact printed scope

Exercise 6.7 in `rockafellar_wets.pdf` (printed pp. 202--203) takes
`C = G⁻¹(D) ⊆ ℝⁿ`, with `G : ℝⁿ → ℝᵐ` continuously differentiable and
`DG(x)` of full rank `m`, and prints three formulas. The tangent and regular
normal formulas are already proved. This task owns exactly the remaining
limiting-normal formula

```text
N_{G⁻¹(D)}(x) = DG(x)* N_D(G(x)).
```

The use of a `C¹` hypothesis is substantive here: limiting normals are limits
of regular normals at moving base points, so both the derivative and its
adjoint must vary continuously. A single `HasStrictFDerivAt` at `x` is not an
adequate replacement for the printed smoothness assumption.

## Main theorem

Import the integrated P1--P3 infrastructure and prove a theorem with this
shape (minor binder or universe rearrangements are fine):

```lean
theorem normalCone_preimage_of_surjective
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {G : E → F} {x : E}
    (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x))
    (D : Set F) :
    normalCone (G ⁻¹' D) x =
      ContinuousLinearMap.adjoint (fderiv ℝ G x) '' normalCone D (G x)
```

Only the multiplier space `F` needs finite dimensionality for compactness; do
not impose finite dimensionality on `E` unless Lean forces it. This is a
strict generalization of the book's finite-dimensional statement. If a
cleaner implementation first proves a helper with an explicit derivative
`G'` and `HasFDerivAt G G' x`, expose the theorem above as the canonical public
result. Preserve the empty-off-set convention automatically; do not add
`G x ∈ D`, closedness of `D`, or Clarke regularity assumptions.

## Required proof architecture

The proof must handle the two inclusions independently and expose genuinely
reusable intermediate lemmas when doing so makes the sequence bookkeeping
clear.

### Target normal to preimage normal

For `v ∈ normalCone D (G x)`:

1. unpack Definition 6.3 into `yₙ → G x` and
   `vₙ ∈ regularNormalCone D (yₙ)` with `vₙ → v`;
2. obtain the local section from
   `HasStrictFDerivAt.exists_local_rightInverse_of_surjective`, using
   `hG.hasStrictFDerivAt one_ne_zero`;
3. lift a tail of `yₙ` to `xₙ → x` with `G (xₙ) = yₙ`, using
   `HasStrictFDerivAt.lift_through_local_rightInverse` (or the packaged
   `exists_local_lift_of_surjective`);
4. use `hG.eventually` to ensure `G` is `C¹`, hence differentiable, at every
   retained `xₙ`;
5. apply `adjoint_image_regularNormalCone_subset_preimage` at each `xₙ` to
   obtain
   `adjoint (fderiv ℝ G (xₙ)) vₙ ∈ regularNormalCone (G ⁻¹' D) xₙ`;
6. use `hG.continuousAt_fderiv one_ne_zero`, continuity/isometry of
   `ContinuousLinearMap.adjoint`, and continuity of evaluation to prove these
   vectors tend to `adjoint (fderiv ℝ G x) v`;
7. assemble the limiting-normal witness with `mem_normalCone_of_forall`.

It is fine to discard a finite prefix once, but reindex all sequences
consistently and retain the required strict-monotone/tendsto facts.

### Preimage normal to target normal

For `w ∈ normalCone (G ⁻¹' D) x`:

1. unpack witnesses `xₙ → x` and
   `wₙ ∈ regularNormalCone (G ⁻¹' D) xₙ`, `wₙ → w`;
2. use `exists_continuousAt_rightInverse_of_surjective` at
   `A = fderiv ℝ G x`, then compose its eventual identity with continuity of
   `fderiv` to obtain right inverses `Rₙ` for all derivatives on a common tail;
3. derive surjectivity of each `fderiv ℝ G (xₙ)` from
   `(fderiv ℝ G (xₙ)).comp Rₙ = id`;
4. apply `regularNormalCone_preimage_of_surjective` at each retained `xₙ`
   to choose multipliers
   `vₙ ∈ regularNormalCone D (G (xₙ))` satisfying
   `adjoint (fderiv ℝ G (xₙ)) vₙ = wₙ`;
5. prove `vₙ` is bounded. Use
   `norm_le_rightInverse_norm_mul_adjoint`; continuity of the chosen
   right-inverse family makes `‖Rₙ‖` eventually bounded, and convergence of
   `wₙ` makes `‖wₙ‖` eventually bounded;
6. use finite dimensionality of `F` (`isCompact_closedBall` or
   `tendsto_subseq_of_bounded`) to select a convergent subsequence
   `vφₙ → v`;
7. combine continuity of `G` with the retained regular-normal memberships to
   show `v ∈ normalCone D (G x)`;
8. pass the adjoint identities to the limit using continuity of `fderiv` and
   `adjoint`, and conclude
   `w = adjoint (fderiv ℝ G x) v` by uniqueness of limits.

Do not silently appeal to weak compactness in an infinite-dimensional
multiplier space. The strong convergent subsequence is exactly why the theorem
has `[FiniteDimensional ℝ F]`.

## Relevant existing APIs

- `RockafellarWets/Chapter6/NormalCones.lean`
  - `normalCone`, `mem_normalCone_of_forall`
  - `regularNormalCone_subset_normalCone`
  - `mem_normalCone_of_tendsto`
- `RockafellarWets/Chapter6/RegularNormalChangeOfCoordinates.lean`
  - `adjoint_image_regularNormalCone_subset_preimage`
  - `regularNormalCone_preimage_of_surjective`
- `RockafellarWets/Chapter6/ContinuousRightInverses.lean`
  - `exists_continuousLinearMap_rightInverse`
  - `exists_continuousAt_rightInverse_of_surjective`
  - `norm_le_rightInverse_norm_mul_adjoint`
- `RockafellarWets/Chapter6/LocalSubmersion.lean`
  - `HasStrictFDerivAt.exists_local_rightInverse_of_surjective`
  - `HasStrictFDerivAt.lift_through_local_rightInverse`
  - `HasStrictFDerivAt.exists_local_lift_of_surjective`
- Mathlib:
  - `ContDiffAt.eventually`, `ContDiffAt.hasStrictFDerivAt`
  - `ContDiffAt.continuousAt_fderiv`
  - the linear-isometry continuity of `ContinuousLinearMap.adjoint`
  - `IsCompact.tendsto_subseq`, `isCompact_closedBall`,
    `tendsto_subseq_of_bounded`
  - `Tendsto.clm_apply`/continuous evaluation, or an equivalent explicit
    operator-norm estimate.

Check exact names and argument order in this pinned Mathlib version instead of
guessing. Small private tail/reindexing and boundedness lemmas are encouraged.

## Exclusions

- Do not reprove or rename the tangent or regular-normal clauses of 6.7.
- Do not formalize smooth manifolds (6.8); that is a later task.
- Do not assume `D` is closed, convex, locally closed, or Clarke regular.
- Do not replace the equality by either inclusion or by a polarity statement.
- Do not weaken `C¹` to differentiability only at `x`.
- Do not publish a competing generic right-inverse or locality API.
- Do not use `sorry`, `admit`, `axiom`, linter suppression, placeholder
  declarations, or unsafe shortcuts.

## Verification and commit

Run:

```text
lake env lean RockafellarWets/Chapter6/LimitingNormalChangeOfCoordinates.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/LimitingNormalChangeOfCoordinates.lean
git diff --check
git status --short
```

The search must have no matches and status must list only the assigned file.
Do not add an umbrella import merely to test it. Commit only that file:

```text
git add RockafellarWets/Chapter6/LimitingNormalChangeOfCoordinates.lean
git commit -m "Prove limiting-normal change of coordinates"
```

Report the commit hash, theorem inventory, exact typeclass assumptions, all
verification commands and outcomes, and any exact adaptation of the requested
theorem shape.
