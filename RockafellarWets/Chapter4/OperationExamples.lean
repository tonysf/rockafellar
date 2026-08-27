/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Operation-convergence regression examples

Focused boundary cases for Theorems 4.26--4.33.
-/

import RockafellarWets.Chapter4.ConvexHullTotalConvergence
import RockafellarWets.Chapter4.ConvexIntersections
import RockafellarWets.Chapter4.FiniteSumConvergence
import RockafellarWets.Chapter4.OrthogonalProjections
import RockafellarWets.Chapter4.UnionConvergence

open Bornology Filter Function Metric Set Topology
open scoped BigOperators Pointwise

namespace RW

section OperationExamples

/-- The constant singleton sequence is eventually bounded. -/
private theorem eventuallyBounded_singleton_zero :
    EventuallyBounded (fun _ : ℕ ↦ ({0} : Set ℝ)) := by
  refine ⟨0, 0, ?_⟩
  intro n _hn x hx
  simp only [mem_singleton_iff] at hx
  subst x
  simp

/-- **Theorem 4.26 regression:** even a constant map preserves convergence
on an eventually bounded sequence. -/
theorem image_constant_singleton_regression :
    PKConverges
      (fun _ ↦ (fun _x : ℝ ↦ (0 : ℝ)) '' ({0} : Set ℝ))
      ((fun _x : ℝ ↦ (0 : ℝ)) '' ({0} : Set ℝ)) := by
  apply PKConverges.image_of_eventuallyBounded
    (pkConverges_const_of_isClosed (D := ({0} : Set ℝ)) isClosed_singleton)
    continuous_const eventuallyBounded_singleton_zero

/-- Total convergence of the constant zero singleton, reused below. -/
private theorem totalConverges_singleton_zero :
    TotalConverges (fun _ : ℕ ↦ ({0} : Set ℝ)) ({0} : Set ℝ) := by
  apply totalConverges_of_uniformly_bounded
    (pkConverges_const_of_isClosed (D := ({0} : Set ℝ)) isClosed_singleton)
    (singleton_nonempty 0) isBounded_singleton
  exact fun _ ↦ Subset.rfl

/-- **Theorem 4.27 regression:** the zero linear map is permitted when the
limiting horizon cone is trivial. -/
theorem linearImage_zero_singleton_regression :
    TotalConverges
      (fun _ ↦ (0 : ℝ →ₗ[ℝ] ℝ) '' ({0} : Set ℝ))
      ((0 : ℝ →ₗ[ℝ] ℝ) '' ({0} : Set ℝ)) := by
  apply totalConverges_singleton_zero.linear_image (0 : ℝ →ₗ[ℝ] ℝ)
  intro v hv _hvmap
  have hzero : horizonCone ({0} : Set ℝ) = ({0} : Set ℝ) :=
    (isBounded_iff_horizonCone_eq_singleton_zero).mp isBounded_singleton
  rw [hzero] at hv
  simpa only [mem_singleton_iff] using hv

/-- An unbounded horizontal ray in `ℝ²`. -/
private def horizontalRay : Set (ℝ × ℝ) :=
  Set.Ici 0 ×ˢ ({0} : Set ℝ)

private theorem horizontalRay_isClosed : IsClosed horizontalRay :=
  isClosed_Ici.prod isClosed_singleton

private theorem horizontalRay_isCone : IsCone horizontalRay := by
  constructor
  · exact ⟨by simp, by simp⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩ c hc
    constructor
    · change 0 ≤ c * x
      exact mul_nonneg hc.le hx
    · simp only [mem_singleton_iff] at hy ⊢
      subst y
      simp

private theorem totalConverges_horizontalRay :
    TotalConverges (fun _ : ℕ ↦ horizontalRay) horizontalRay := by
  apply totalConverges_of_isCone
    (pkConverges_const_of_isClosed horizontalRay_isClosed)
    ⟨0, horizontalRay_isCone.1⟩
  exact fun _ ↦ horizontalRay_isCone

/-- **Theorem 4.27 regression:** first-coordinate projection is globally
noninjective, but its kernel meets the horizontal ray's horizon only at zero. -/
theorem noninjective_projection_horizontalRay_regression :
    TotalConverges
        (fun _ ↦ (LinearMap.fst ℝ ℝ ℝ) ''
          (show Set (ℝ × ℝ) from horizontalRay))
        ((LinearMap.fst ℝ ℝ ℝ) '' horizontalRay) ∧
      ¬ Function.Injective (LinearMap.fst ℝ ℝ ℝ) := by
  constructor
  · apply totalConverges_horizontalRay.linear_image (LinearMap.fst ℝ ℝ ℝ)
    intro v hv hvfst
    rw [horizonCone_eq_self_of_isClosed_isCone
      horizontalRay_isClosed horizontalRay_isCone] at hv
    rcases v with ⟨x, y⟩
    simp only [LinearMap.fst_apply] at hvfst
    simp only [horizontalRay, mem_prod, mem_Ici, mem_singleton_iff] at hv
    subst x
    rcases hv with ⟨_hx, hy⟩
    subst y
    rfl
  · intro hinj
    have hpair : ((0, 0) : ℝ × ℝ) = (0, 1) := hinj (by simp)
    norm_num at hpair

/-- **Theorem 4.28 regression:** arbitrary orthogonal projections preserve
the constant zero singleton. -/
theorem starProjection_singleton_regression (M : Submodule ℝ ℝ) :
    PKConverges
      (fun _ ↦ M.starProjection '' ({0} : Set ℝ))
      (M.starProjection '' ({0} : Set ℝ)) := by
  apply PKConverges.starProjection_of_convex
    (pkConverges_const_of_isClosed (D := ({0} : Set ℝ)) isClosed_singleton)
    (singleton_nonempty 0) (fun _ ↦ convex_singleton 0) M
  have hzero : horizonCone ({0} : Set ℝ) = ({0} : Set ℝ) :=
    (isBounded_iff_horizonCone_eq_singleton_zero).mp isBounded_singleton
  rw [hzero]
  ext x
  simp

/-- The two singleton factors used for the product and sum regressions. -/
private def zeroFactors : Fin 2 → Set ℝ := fun _ ↦ {0}

private theorem totalConverges_zeroFactors (i : Fin 2) :
    TotalConverges (fun _ : ℕ ↦ zeroFactors i) (zeroFactors i) := by
  simpa only [zeroFactors] using totalConverges_singleton_zero

private theorem zeroFactors_horizon_product :
    horizonCone (dependentSetProduct zeroFactors) =
      dependentSetProduct (fun i ↦ horizonCone (zeroFactors i)) := by
  simpa only [dependentSetProduct] using
    (horizonCone_pi_eq_pi_horizonCone_of_convex_nonempty zeroFactors
      (fun _ ↦ convex_singleton 0) (fun _ ↦ singleton_nonempty 0))

/-- **Exercise 4.29(a,d) regression:** finite products and finite sums of
constant zero singletons converge totally. -/
theorem finiteProduct_and_sum_regression :
    TotalConverges
        (fun n ↦ dependentSetProduct
          (fun i : Fin 2 ↦ (fun _ : ℕ ↦ zeroFactors i) n))
        (dependentSetProduct zeroFactors) ∧
      TotalConverges
        (fun n ↦ finiteSetSum
          (fun i : Fin 2 ↦ (fun _ : ℕ ↦ zeroFactors i) n))
        (finiteSetSum zeroFactors) := by
  have hcomponents : ∀ i : Fin 2,
      TotalConverges (fun _ : ℕ ↦ zeroFactors i) (zeroFactors i) :=
    totalConverges_zeroFactors
  constructor
  · exact totalConverges_dependentSetProduct hcomponents
      zeroFactors_horizon_product
  · apply totalConverges_finiteSetSum hcomponents zeroFactors_horizon_product
    intro u hu _hsum
    funext i
    have hui := hu i
    have hzero : horizonCone (zeroFactors i) = ({0} : Set ℝ) :=
      (isBounded_iff_horizonCone_eq_singleton_zero).mp isBounded_singleton
    rw [hzero] at hui
    simpa only [mem_singleton_iff, Pi.zero_apply] using hui

/-- **Proposition 4.30(b,c) regression:** convexification of the constant
zero singleton converges both ordinarily and totally. -/
theorem convexHull_singleton_regression :
    PKConverges
        (fun _ ↦ _root_.convexHull ℝ ({0} : Set ℝ))
        (_root_.convexHull ℝ ({0} : Set ℝ)) ∧
      TotalConverges
        (fun _ ↦ _root_.convexHull ℝ ({0} : Set ℝ))
        (closure (_root_.convexHull ℝ ({0} : Set ℝ))) := by
  constructor
  · apply PKConverges.convexHull_of_uniformly_bounded
      (pkConverges_const_of_isClosed (D := ({0} : Set ℝ)) isClosed_singleton)
      isBounded_singleton
    exact fun _ ↦ Subset.rfl
  · apply totalConverges_singleton_zero.convexHull (singleton_nonempty 0)
    rw [(isBounded_iff_horizonCone_eq_singleton_zero).mp isBounded_singleton]
    intro n z hz _hsum i
    simpa only [mem_singleton_iff] using hz i

/-- **Exercise 4.31 regression:** a finite union of constant singleton
sequences converges totally. -/
theorem finiteUnion_singleton_regression :
    TotalConverges
      (fun n ↦ ⋃ i : Fin 2, (fun _ : ℕ ↦ zeroFactors i) n)
      (⋃ i : Fin 2, zeroFactors i) := by
  exact totalConverges_iUnion totalConverges_zeroFactors

private theorem cannotBeSeparated_univ :
    CannotBeSeparated (univ : Set ℝ) univ := by
  have hsub : (univ : Set ℝ) - univ = univ := by
    apply Set.Subset.antisymm (fun x _hx ↦ mem_univ x)
    intro x _hx
    exact Set.mem_sub.2 ⟨x, mem_univ x, 0, mem_univ 0, sub_zero x⟩
  rw [CannotBeSeparated, hsub, interior_univ]
  exact mem_univ 0

/-- **Theorem 4.32(c) regression:** pairwise intersection at the full-space
boundary case. -/
theorem pairIntersection_univ_regression :
    PKConverges (fun _ : ℕ ↦ (univ : Set ℝ) ∩ univ)
      ((univ : Set ℝ) ∩ univ) := by
  apply PKConverges.inter_of_cannotBeSeparated
    (pkConverges_const_of_isClosed (D := (univ : Set ℝ)) isClosed_univ)
    (pkConverges_const_of_isClosed (D := (univ : Set ℝ)) isClosed_univ)
    (fun _ ↦ convex_univ) (fun _ ↦ convex_univ) cannotBeSeparated_univ

/-- **Exercise 4.33 regression:** a finite intersection of constant full
spaces converges under the exact nonseparation hypothesis. -/
theorem finiteIntersection_univ_regression :
    PKConverges
      (fun _ : ℕ ↦ ⋂ _i : Fin 2, (univ : Set ℝ))
      (⋂ _i : Fin 2, (univ : Set ℝ)) := by
  apply pkConverges_iInter_fin_of_cannotBeSeparated
  · exact fun _ ↦
      pkConverges_const_of_isClosed (D := (univ : Set ℝ)) isClosed_univ
  · exact fun _ _ ↦ convex_univ
  · intro i
    simpa using cannotBeSeparated_univ

end OperationExamples

end RW
