# P02 — Local submersion section from a surjective strict derivative

## Objective

Prove a reusable local submersion theorem for maps between real Hilbert spaces: if `G` has a surjective strict derivative at `x`, then near `G x` it has a continuous local right inverse through `x`, with a continuous-linear strict derivative for that local section.

This task must be self-contained at the common base commit. Do not import or assume P01's unmerged file.

## Git setup

- Exact base commit: `b2eb4ea92faefd721b93eba48422a6c204d61fc9` (`b2eb4ea`).
- Required branch name: `chapter6-p02-local-submersion`.
- Start from exactly that commit. Do not merge, rebase, or cherry-pick another batch branch.
- Before editing, confirm that `git rev-parse HEAD` is the exact base above. If it is not, stop and report the blocker.

## Exclusive file ownership

You own exactly one implementation file:

- `RockafellarWets/Chapter6/LocalSubmersion.lean`

Create that file if it does not exist. Do not edit any other file. In particular, do not edit:

- `README.md`;
- `CHAPTER6_COVERAGE.md` or any other coverage ledger;
- `RockafellarWets/Chapter6.lean`, `RockafellarWets.lean`, or another umbrella import;
- `RockafellarWets/Chapter6/ChangeOfCoordinates.lean`;
- any file under `parallel_tasks/`, including this prompt, the batch index, or the shared contract;
- files owned by P01, P03, or P04.

## Mathematical deliverables

Work in namespace `RW` with real Hilbert spaces:

```lean
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
```

### 1. Local right inverse through the base point

The main theorem must have the following semantic shape; theorem naming and conjunction ordering may be adjusted for a clean API:

```lean
theorem HasStrictFDerivAt.exists_local_rightInverse_of_surjective
    {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x)
    (hsurj : Function.Surjective G') :
    ∃ (R : F →L[ℝ] E) (s : F → E),
      G'.comp R = ContinuousLinearMap.id ℝ F ∧
      HasStrictFDerivAt s R (G x) ∧
      s (G x) = x ∧
      ∀ᶠ y in 𝓝 (G x), G (s y) = y
```

The derivative identity and `s (G x) = x` are required. The right-inverse identity must hold on a full neighborhood of `G x`, not only along a selected sequence.

### 2. Neighborhood form

Provide a named corollary unpacking the eventual statement into actual neighborhoods. Its semantic content should be:

```lean
∃ U ∈ 𝓝 x, ∃ V ∈ 𝓝 (G x),
  Set.MapsTo s V U ∧ Set.EqOn (G ∘ s) id V
```

It is acceptable for `U`, `V`, and `s` to occur in the conclusion of the main theorem instead, provided the derivative and base-point clauses remain available.

### 3. Filter or sequence lifting corollary

Add a small reusable corollary recording that values tending to `G x` can be lifted through the local section to values tending to `x`, eventually with exact image. An acceptable filter-level shape is:

```lean
Tendsto ys l (𝓝 (G x)) →
Tendsto (s ∘ ys) l (𝓝 x) ∧
∀ᶠ n in l, G (s (ys n)) = ys n
```

A sequence-specialized theorem over `atTop` is also acceptable.

## Intended construction

Reuse the augmentation idea already present in `tangentCone_preimage_of_surjective`, but keep all new declarations in your owned file:

1. Let `N = ker G'` and let `P : E →L[ℝ] N` be the orthogonal projection.
2. Show `Q = G'.prod P : E →L[ℝ] F × N` is bijective and package it as `Psi : E ≃L[ℝ] F × N`.
3. Define `Phi z = (G z, P z)` and obtain its local inverse from the inverse function theorem.
4. Feed the local inverse the slice `y ↦ (y, P x)` to obtain `s : F → E`.
5. Compute the derivative `R`, prove `G'.comp R = id`, and derive the eventual right-inverse and base-point identities.

Using `WithLp 2` is allowed but not required here: the theorem needs normed-space inverse-function machinery, not adjoints. The ordinary product target is sufficient and has the topology/norm equivalence needed by the existing proof.

P01 owns the canonical public theorem about a fixed or continuously varying
right inverse of a continuous linear map. Because this branch cannot import
P01 yet, keep any purely linear right-inverse helper used by the construction
`private` or unmistakably P02-local. The public API of this file should concern
the nonlinear local section and its derivative, not duplicate P01's API.

## Relevant existing files and APIs

- `RockafellarWets/Chapter6/ChangeOfCoordinates.lean`
  - `tangentCone_preimage_of_surjective` contains the complete projection/augmentation proof pattern.
  - `tangentCone_preimage` shows how the local inverse API is currently used.
- `ContinuousLinearMap.isClosed_ker`
- `IsClosed.completeSpace_coe`
- `Submodule.orthogonalProjection`
- `ContinuousLinearEquiv.ofBijective`
- `ContinuousLinearEquiv.coe_ofBijective`
- `HasStrictFDerivAt.prodMk`
- `HasStrictFDerivAt.comp`
- `HasStrictFDerivAt.localInverse`
- `HasStrictFDerivAt.to_localInverse`
- `HasStrictFDerivAt.localInverse_apply_image`
- `HasStrictFDerivAt.eventually_left_inverse`
- `HasStrictFDerivAt.eventually_right_inverse`
- `Filter.eventually_iff_exists_mem`
- `ContinuousAt.tendsto` and `Tendsto.comp`

Import existing base files only. In particular, do not import `RockafellarWets.Chapter6.ContinuousRightInverses`: that file does not exist at the common base and belongs to another worker.

## Exclusions

- Do not edit or refactor the existing tangent-cone proof.
- Do not prove tangent-cone or normal-cone transformation formulas.
- Do not attempt the limiting-normal clause of Exercise 6.7.
- Do not add finite-dimensional hypotheses; the orthogonal projection handles the kernel complement in Hilbert spaces.
- Do not leave `sorry`, `admit`, `axiom`, disabled linters, or placeholder declarations.

## Verification

Run at minimum:

```bash
lake env lean RockafellarWets/Chapter6/LocalSubmersion.lean
git diff --check
```

The assigned file must compile from a clean checkout of base commit `b2eb4ea` plus your one new file. Search it for `sorry`, `admit`, `axiom`, disabled linters, and placeholders. Do not add an umbrella import merely to test it.

## Required commit

Commit only the owned file on branch `chapter6-p02-local-submersion` with commit message:

```text
Prove a local submersion section theorem
```

In your final report, include the commit hash, theorem inventory, exact verification commands and outcomes, and any exact adaptation of the requested theorem shapes.
