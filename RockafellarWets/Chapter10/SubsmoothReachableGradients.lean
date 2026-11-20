/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: reachable gradients of subsmooth functions

The formulas of **Theorem 10.31** in terms of
`∇̄f(x̄) = {v | ∃ x^ν →_D x̄ with ∇f(x^ν) → v}`, `D` the set of points of `O` where `f` is
differentiable (`reachableGradients f {y | y ∈ O ∧ DifferentiableAt ℝ f y} x̄`, Theorem 9.61),
for `f` lower-`C¹` on the open set `O`:

* `lip f(x̄) = max_{v ∈ ∇̄f(x̄)} |v|` (`IsLowerCOn.lipschitzModulus_eq_reachable`);
* `df(x̄)(w) = max_{v ∈ ∇̄f(x̄)} ⟪v, w⟫` (`IsLowerCOn.subderivative_eq_reachable`);
* `∂f(x̄) = con ∇̄f(x̄) = con {∇f_t(x̄) | t ∈ T(x̄)}`
  (`IsLowerCOn.convexHull_reachableGradients_eq_subdifferential`, together with
  `LowerRepresentation.subdifferential_eq_convexHull`);
* `-∂(-f)(x̄) = ∇̄f(x̄) ⊂ {∇f_t(x̄) | t ∈ T(x̄)}` (`IsLowerCOn.neg_subdifferential_neg_eq_reachable`,
  `LowerRepresentation.reachableGradients_subset_gradSet`).

These combine the strict continuity and regularity from 10.31
(`IsLowerCOn.strictlyContinuous_regular`) with Theorem 9.61 and Exercise 9.21.
-/

import RockafellarWets.Chapter10.SubsmoothFunctions
import RockafellarWets.Chapter9.ClarkeReachableGradients

open Filter Function Metric Set Topology MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {k : ℕ∞} {f : E → ℝ} {O : Set E}

private theorem null_diff_self (O : Set E) :
    volume ({y ∈ O | DifferentiableAt ℝ f y} \ {y | y ∈ O ∧ DifferentiableAt ℝ f y}) = 0 := by
  simp

/-- **Theorem 10.31**: `∂f(x̄) = con ∇̄f(x̄)`. -/
theorem IsLowerCOn.convexHull_reachableGradients_eq_subdifferential (hf : IsLowerCOn k f O)
    (hk : 1 ≤ k) (hO : IsOpen O) {x : E} (hx : x ∈ O) :
    convexHull ℝ (reachableGradients f {y | y ∈ O ∧ DifferentiableAt ℝ f y} x) =
      subdifferential (fun y ↦ (f y : EReal)) x :=
  convexHull_reachableGradients_eq_subdifferential_of_regular hO
    (fun _ hy ↦ hf.strictlyContinuousAt hk hy) (fun _ hy ↦ hy.2) (null_diff_self O) hx
    (hf.strictlyContinuous_regular hk x hx).2

/-- **Theorem 10.31**: `df(x̄)(w) = max_{v ∈ ∇̄f(x̄)} ⟪v, w⟫`. -/
theorem IsLowerCOn.subderivative_eq_reachable (hf : IsLowerCOn k f O) (hk : 1 ≤ k)
    (hO : IsOpen O) {x : E} (hx : x ∈ O) (w : E) :
    ∃ v ∈ reachableGradients f {y | y ∈ O ∧ DifferentiableAt ℝ f y} x,
      subderivative (fun y ↦ (f y : EReal)) x w = (⟪v, w⟫_ℝ : EReal) ∧
      ∀ z ∈ reachableGradients f {y | y ∈ O ∧ DifferentiableAt ℝ f y} x, ⟪z, w⟫_ℝ ≤ ⟪v, w⟫_ℝ := by
  obtain ⟨v, hv, hval, hmax⟩ := exists_max_reachableGradient_regularSubderivative hO
    (fun _ hy ↦ hf.strictlyContinuousAt hk hy) (fun _ hy ↦ hy.2) (null_diff_self O) hx w
  have hreg := (hf.strictlyContinuous_regular hk x hx).2
  refine ⟨v, hv, ?_, hmax⟩
  rw [congrFun (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.1 hreg).2 w]
  exact hval

/-- **Theorem 10.31**: `lip f(x̄) = max_{v ∈ ∇̄f(x̄)} |v|`. -/
theorem IsLowerCOn.lipschitzModulus_eq_reachable (hf : IsLowerCOn k f O) (hk : 1 ≤ k)
    (hO : IsOpen O) {x : E} (hx : x ∈ O) :
    ∃ v ∈ reachableGradients f {y | y ∈ O ∧ DifferentiableAt ℝ f y} x,
      lipschitzModulus f x = (‖v‖₊ : ℝ≥0∞) ∧
      ∀ z ∈ reachableGradients f {y | y ∈ O ∧ DifferentiableAt ℝ f y} x, ‖z‖ ≤ ‖v‖ := by
  set D := {y | y ∈ O ∧ DifferentiableAt ℝ f y} with hD
  obtain ⟨hsc, -⟩ := hf.strictlyContinuous_regular hk x hx
  have hf' : (fun y ↦ ((f y : EReal)).toReal) = f := funext fun y ↦ EReal.toReal_coe _
  have hcl : x ∈ closure D := subset_closure_differentiableAt_of_strictlyContinuousOn volume hO
    (fun _ hy ↦ hf.strictlyContinuousAt hk hy) hx
  obtain ⟨hne, hcpt⟩ := reachableGradients_nonempty_compact (hf.strictlyContinuousAt hk hx) hcl
  obtain ⟨v, hv, hvmax⟩ := hcpt.exists_isMaxOn hne continuous_norm.continuousOn
  rw [isMaxOn_iff] at hvmax
  have hsub := hf.convexHull_reachableGradients_eq_subdifferential hk hO hx
  obtain ⟨u, hu, hlip, hmax⟩ := hsc.exists_subgradient_norm_eq_modulus
  rw [hf'] at hlip
  refine ⟨v, hv, ?_, hvmax⟩
  have h1 : ‖u‖ ≤ ‖v‖ := by
    rw [← hsub] at hu
    have hball : reachableGradients f D x ⊆ closedBall 0 ‖v‖ := fun z hz ↦ by
      rw [mem_closedBall_zero_iff]
      exact hvmax z hz
    have h := convexHull_min hball (convex_closedBall 0 _) hu
    rwa [mem_closedBall_zero_iff] at h
  have h2 : ‖v‖ ≤ ‖u‖ := hmax v (by rw [← hsub]; exact subset_convexHull ℝ _ hv)
  rw [hlip]
  congr 1
  ext
  simp only [coe_nnnorm]
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Theorem 10.31** (with Exercise 9.21): `-∂(-f)(x̄) = ∇̄f(x̄)`. -/
theorem IsLowerCOn.neg_subdifferential_neg_eq_reachable (hf : IsLowerCOn k f O) (hk : 1 ≤ k)
    (hO : IsOpen O) {x : E} (hx : x ∈ O) :
    -subdifferential (fun y ↦ -((f y : ℝ) : EReal)) x =
      reachableGradients f {y | y ∈ O ∧ DifferentiableAt ℝ f y} x := by
  have hf' : (fun y ↦ ((f y : EReal)).toReal) = f := funext fun y ↦ EReal.toReal_coe _
  have h := neg_subdifferential_neg_eq hO (hf.strictlyContinuous_regular hk) hx
  simp only [hf'] at h
  rw [h]
  ext v
  simp only [mem_setOf_eq]
  rw [reachableGradients, mem_clusterValuesWithin_iff]
  constructor
  · rintro ⟨xs, hxs, hdiff, hgrad⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hxs.eventually (hO.mem_nhds hx))
    exact ⟨fun n ↦ xs (n + N), fun n ↦ ⟨hN _ (Nat.le_add_left N n), hdiff _⟩,
      hxs.comp (tendsto_add_atTop_nat N), hgrad.comp (tendsto_add_atTop_nat N)⟩
  · rintro ⟨xs, hD, hxs, hgrad⟩
    exact ⟨xs, hxs, fun n ↦ (hD n).2, hgrad⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Theorem 10.31**: `∇̄f(x̄) ⊂ {∇f_t(x̄) | t ∈ T(x̄)}` for any local representation. -/
theorem LowerRepresentation.reachableGradients_subset_gradSet {V : Set E}
    (R : LowerRepresentation k f V) (hk : 1 ≤ k) (hV : IsOpen V) (hVO : V ⊆ O)
    (hf : IsLowerCOn k f O) (hO : IsOpen O) {x : E} (hx : x ∈ V) :
    reachableGradients f {y | y ∈ O ∧ DifferentiableAt ℝ f y} x ⊆ R.gradSet x := by
  rw [← hf.neg_subdifferential_neg_eq_reachable hk hO (hVO hx)]
  exact R.neg_subdifferential_neg_subset hk hV hx

end RW
