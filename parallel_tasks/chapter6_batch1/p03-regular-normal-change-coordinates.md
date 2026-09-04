# P03 — Regular-normal change of coordinates for Exercise 6.7

## Objective

Prove the regular-normal formula in Chapter 6, Exercise 6.7, for a preimage under a map with surjective strict derivative:

```text
N̂_{G⁻¹(D)}(x) = G'(x)* N̂_D(G(x)).
```

The proof must use the existing kernel-projection augmentation with an `L²` product target, `WithLp 2 (F × ker G')`, so that the augmented target is an inner product space and the augmented derivative has an adjoint.

This task is self-contained at the common base. Do not assume P01 or P02 has been merged.

## Git setup

- Exact base commit: `b2eb4ea92faefd721b93eba48422a6c204d61fc9` (`b2eb4ea`).
- Required branch name: `chapter6-p03-regular-normal-change-coordinates`.
- Start from exactly that commit. Do not merge, rebase, or cherry-pick another batch branch.
- Before editing, confirm that `git rev-parse HEAD` is the exact base above. If it is not, stop and report the blocker.

## Exclusive file ownership

You own exactly one implementation file:

- `RockafellarWets/Chapter6/RegularNormalChangeOfCoordinates.lean`

Create that file if it does not exist. Do not edit any other file. In particular, do not edit:

- `RockafellarWets/Chapter6/ChangeOfCoordinates.lean`;
- `RockafellarWets/Chapter6/NormalCones.lean`;
- `README.md`;
- `CHAPTER6_COVERAGE.md` or any other coverage ledger;
- `RockafellarWets/Chapter6.lean`, `RockafellarWets.lean`, or another umbrella import;
- any file under `parallel_tasks/`, including this prompt, the batch index, or the shared contract;
- files owned by P01, P02, or P04.

## Main theorem

Work in namespace `RW` under the same infinite-dimensional real Hilbert hypotheses as the existing tangent formula. Deliver a theorem with this shape:

```lean
theorem regularNormalCone_preimage_of_surjective
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x)
    (hsurj : Function.Surjective G')
    (D : Set F) :
    regularNormalCone (G ⁻¹' D) x =
      ContinuousLinearMap.adjoint G' '' regularNormalCone D (G x)
```

Do not add a `FiniteDimensional` hypothesis. Do not replace the conclusion by a polarity statement or a mere inclusion.

## Required reusable lemmas

The final proof should expose, with sensible names and docstrings, the following reusable layers.

### 1. Private locality helper for regular normals

```lean
private theorem regularNormalCone_inter_nhds_p03
    {C U : Set E} {x : E} (hU : U ∈ 𝓝 x) :
    regularNormalCone (C ∩ U) x = regularNormalCone C x
```

Use `nhdsWithin_inter_of_mem'`; this lemma should not require completeness.
P14 owns the eventual canonical public locality theorem, so this helper must
remain `private` (or have an unmistakably P03-local private name) to avoid a
duplicate declaration when the branches are integrated.

### 2. One-way differentiable pullback

For `hH : HasFDerivAt H H' a`, prove

```lean
ContinuousLinearMap.adjoint H' '' regularNormalCone S (H a) ⊆
  regularNormalCone (H ⁻¹' S) a
```

Prove it directly from Definition 6.3. The intended ingredients are `hH.isLittleO.def`, transport of the eventual regular-normal inequality through `ContinuousWithinAt.tendsto_nhdsWithin`, `ContinuousLinearMap.adjoint_inner_left`, `H'.le_opNorm`, and Cauchy–Schwarz. This direction only needs ordinary Fréchet differentiability.

### 3. Equality under a local diffeomorphism

For `Phi' : E ≃L[ℝ] K` and a strict derivative, prove

```lean
regularNormalCone (Phi ⁻¹' S) x =
  ContinuousLinearMap.adjoint (Phi' : E →L[ℝ] K) ''
    regularNormalCone S (Phi x)
```

Apply the previous inclusion to `Phi` and to `hPhi.localInverse`. Use `hPhi.eventually_right_inverse` plus regular-normal locality to identify the inverse image set with `S` near `Phi x`. Do not assume that an arbitrary continuous linear equivalence is an isometry; cancel the two adjoints by the fundamental inner-product identity or `adjoint_comp`.

### 4. Regular normals to an `L²` cylinder

Define the cylinder over `D` in the augmented target, for example:

```lean
def l2Cylinder (D : Set F) : Set (WithLp 2 (F × N)) :=
  {z | z.fst ∈ D}
```

Prove the exact formula

```lean
regularNormalCone (l2Cylinder D) (WithLp.toLp 2 (u, b)) =
  WithLp.toLp 2 '' (regularNormalCone D u ×ˢ ({0} : Set N))
```

For the reverse/free-coordinate direction, explicit tangent directions `toLp 2 (0, w)` and their negatives may be combined with `inner_nonpos_of_mem_regularNormalCone`. For the forward direction use `WithLp.prod_inner_apply`, `WithLp.norm_fst_le`, and `mem_regularNormalCone_iff`.

### 5. `WithLp 2` augmentation

Reuse the algebra of `tangentCone_preimage_of_surjective`, but send the product through

```lean
(WithLp.prodContinuousLinearEquiv 2 ℝ F N).symm
```

The required structure is:

1. `N = LinearMap.ker (G' : E →ₗ[ℝ] F)`;
2. `P : E →L[ℝ] N = N.orthogonalProjection`;
3. first construct the existing bijection `Psi0 : E ≃L[ℝ] F × N` from `G'.prod P`;
4. set `Psi = Psi0.trans (WithLp.prodContinuousLinearEquiv 2 ℝ F N).symm`;
5. define `Phi z = WithLp.toLp 2 (G z, P z)` and prove its strict derivative is `Psi`;
6. establish the key adjoint computation

```lean
ContinuousLinearMap.adjoint (Psi : E →L[ℝ] WithLp 2 (F × N))
    (WithLp.toLp 2 (v, 0)) =
  ContinuousLinearMap.adjoint G' v
```

Prove the last identity by `ext_inner_right`, `adjoint_inner_left`, and `WithLp.prod_inner_apply`.

## Relevant existing files and Mathlib APIs

- `RockafellarWets/Chapter6/NormalCones.lean`
  - `regularNormalCone`, `mem_regularNormalCone`, `mem_regularNormalCone_iff`
  - `inner_nonpos_of_mem_regularNormalCone`
- `RockafellarWets/Chapter6/ChangeOfCoordinates.lean`
  - `tangentCone_preimage`
  - `tangentCone_preimage_of_surjective`, whose augmentation should be mirrored rather than edited
- Explicit imports will likely include:
  - `Mathlib.Analysis.InnerProductSpace.ProdL2`
  - `Mathlib.Analysis.InnerProductSpace.Adjoint`
- `WithLp.prodContinuousLinearEquiv`
- `WithLp.prod_inner_apply`
- `WithLp.norm_fst_le`
- `WithLp.norm_toLp_fst`
- `WithLp.toLp_fst`, `WithLp.toLp_snd`, `WithLp.toLp_sub`
- `ContinuousLinearMap.adjoint`, `adjoint_inner_left`, `adjoint_inner_right`, `adjoint_comp`, `adjoint_adjoint`
- `HasStrictFDerivAt.to_localInverse`, `eventually_right_inverse`, and `localInverse_apply_image`
- `ContinuousLinearEquiv.ofBijective` and `coe_ofBijective`

## Exclusions

- Do not prove the limiting `normalCone` formula. Its moving-base-point multiplier control is a separate task.
- Do not alter the existing tangent-cone theorem or duplicate it as a new result.
- Do not use the finite-dimensional tangent-polarity converse as a shortcut.
- Do not edit coverage prose or claim all of Exercise 6.7 is complete.
- Do not import P01 or P02 files; they are absent at the common base.
- Do not leave `sorry`, `admit`, `axiom`, disabled linters, or placeholder declarations.

## Verification

Run at minimum:

```bash
lake env lean RockafellarWets/Chapter6/RegularNormalChangeOfCoordinates.lean
git diff --check
```

The assigned file must compile from a clean checkout of base commit `b2eb4ea` plus your one new file. Search it for `sorry`, `admit`, `axiom`, disabled linters, and placeholders. Do not add an umbrella import merely to test it.

## Required commit

Commit only the owned file on branch `chapter6-p03-regular-normal-change-coordinates` with commit message:

```text
Prove regular-normal change of coordinates
```

In your final report, include the commit hash, theorem inventory, exact verification commands and outcomes, and any exact adaptation of the requested theorem shapes.
