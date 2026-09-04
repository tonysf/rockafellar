# P01 — Continuous right inverses for surjective Hilbert-space operators

## Objective

Build the reusable linear-operator infrastructure needed later for submersions and multiplier limits: a surjective continuous linear map between real Hilbert spaces has a continuous linear right inverse, and right inverses can be chosen continuously for all operators sufficiently close to a fixed surjective operator.

This is a self-contained worker task. Do not assume that any other Chapter 6 batch branch has been merged.

## Git setup

- Exact base commit: `b2eb4ea92faefd721b93eba48422a6c204d61fc9` (`b2eb4ea`).
- Required branch name: `chapter6-p01-continuous-right-inverses`.
- Start from exactly that commit. Do not merge, rebase, or cherry-pick another batch branch.
- Before editing, confirm that `git rev-parse HEAD` is the exact base above. If it is not, stop and report the blocker.

## Exclusive file ownership

You own exactly one implementation file:

- `RockafellarWets/Chapter6/ContinuousRightInverses.lean`

Create that file if it does not exist. Do not edit any other file. In particular, do not edit:

- `README.md`;
- `CHAPTER6_COVERAGE.md` or any other coverage ledger;
- `RockafellarWets/Chapter6.lean`, `RockafellarWets.lean`, or another umbrella import;
- any file under `parallel_tasks/`, including this prompt, the batch index, or the shared contract;
- files owned by P02, P03, or P04.

## Mathematical deliverables

Work in namespace `RW`. Use real Hilbert spaces, with completeness hypotheses wherever Mathlib's adjoint, orthogonal-projection, or inverse APIs require them.

### 1. A fixed continuous linear right inverse

Prove that a surjective continuous linear map admits a continuous linear right inverse. The principal theorem should have this semantic shape; names and harmless argument ordering may be improved:

```lean
theorem exists_continuousLinearMap_rightInverse
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    ∃ R : F →L[ℝ] E, A.comp R = ContinuousLinearMap.id ℝ F
```

Also expose a convenient chosen right inverse, or a theorem giving the pointwise identity `∀ y, A (R y) = y`. The construction must be genuinely continuous linear; a merely set-theoretic or nonlinear section does not satisfy this task.

### 2. Adjoint lower bound from a right inverse

Prove the estimate that makes multiplier sequences controllable. For `A.comp R = id`, provide a theorem equivalent to

```lean
‖y‖ ≤ ‖R‖ * ‖ContinuousLinearMap.adjoint A y‖
```

for every `y : F`. It is acceptable to package this as the existence of a positive constant bounding `A†` below, but retain a direct theorem involving a chosen `R` as well. The proof should come from taking adjoints of `A.comp R = id`, not from finite-dimensional compactness.

### 3. A locally continuous choice for nearby operators

For a fixed surjective `A`, construct a choice of right inverse depending continuously on a nearby operator. Supply a theorem with the following semantic content:

```lean
theorem exists_continuousAt_rightInverse_of_surjective
    (A : E →L[ℝ] F) (hA : Function.Surjective A) :
    ∃ chooseR : (E →L[ℝ] F) → (F →L[ℝ] E),
      ContinuousAt chooseR A ∧
      A.comp (chooseR A) = ContinuousLinearMap.id ℝ F ∧
      ∀ᶠ B in 𝓝 A,
        B.comp (chooseR B) = ContinuousLinearMap.id ℝ F
```

An equivalent formulation using an explicit neighborhood `U ∈ 𝓝 A` and continuity on `U`, or a subtype of the open set of suitable operators, is acceptable. It must state both continuity at `A` and exact right-inverse identities near `A`; mere local surjectivity is insufficient.

A standard construction is:

1. choose a fixed right inverse `R₀` of `A`;
2. observe that `A.comp R₀ = id`;
3. for `B` near `A`, invert the endomorphism `B.comp R₀` of `F`;
4. set `R(B) = R₀.comp ((B.comp R₀).inverse)`.

You may use another equivalent construction if it produces the same API.

## Relevant existing code and Mathlib APIs

- `RockafellarWets/Chapter6/ChangeOfCoordinates.lean`, especially `tangentCone_preimage_of_surjective`, contains the kernel/orthogonal-projection argument showing that an augmented operator is bijective. Reuse the idea, but do not edit that file.
- `ContinuousLinearMap.isClosed_ker`
- `IsClosed.completeSpace_coe`
- `Submodule.orthogonalProjection`
- `Submodule.orthogonalProjection_mem_subspace_eq_self`
- `ContinuousLinearEquiv.ofBijective`
- `ContinuousLinearEquiv.coe_ofBijective`
- `ContinuousLinearEquiv.isOpen` and `ContinuousLinearEquiv.nhds`
- `ContinuousLinearMap.inverse` and `ContinuousLinearMap.IsInvertible`
- `NormedRing.inverse_continuousAt`
- `ContinuousLinearMap.adjoint`, `adjoint_inner_left`, `adjoint_comp`, and `adjoint_id`
- Likely explicit imports include `Mathlib.Analysis.InnerProductSpace.Adjoint` and the operator files defining openness/inversion of bounded linear equivalences.

Prefer a proof valid in infinite-dimensional real Hilbert spaces. Do not add `FiniteDimensional` merely to choose a complement: the closed kernel has an orthogonal complement.

## Exclusions

- Do not prove a nonlinear inverse/submersion theorem.
- Do not define or transform tangent cones, regular normal cones, or limiting normal cones.
- Do not implement Exercise 6.7 itself.
- Do not modify existing Chapter 6 files to consume this API.
- Do not leave `sorry`, `admit`, `axiom`, disabled linters, or placeholder declarations.

## Verification

Run at minimum:

```bash
lake env lean RockafellarWets/Chapter6/ContinuousRightInverses.lean
git diff --check
```

The assigned file must compile from a clean checkout of base commit `b2eb4ea` plus your one new file. Search the file for `sorry`, `admit`, `axiom`, disabled linters, and placeholders. Do not add an umbrella import merely to test it.

## Required commit

Commit only the owned file on branch `chapter6-p01-continuous-right-inverses` with commit message:

```text
Add continuous right inverses for surjective operators
```

In your final report, include the commit hash, theorem inventory, exact verification commands and outcomes, and any exact adaptation of the requested theorem shapes.
