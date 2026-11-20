/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Clarke subgradients from reachable gradients

Theorem 9.61, including arbitrary negligible exclusions from the set of
differentiability points.
-/

import RockafellarWets.Chapter9.ReachableGradientSupport
import RockafellarWets.Chapter9.LineDerivativeBounds
import RockafellarWets.Chapter8.SubdifferentialRegularityCriterion

open Filter Metric Set Topology MeasureTheory
open scoped NNReal InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Theorem 9.61**, the support formula, with arbitrary null-set
exclusions from the differentiability set. -/
theorem regularSubderivative_eq_support_reachableGradients
    {f : E → ℝ} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ y ∈ O, StrictlyContinuousAt f y) (hD : ∀ y ∈ D, DifferentiableAt ℝ f y)
    (hnull : volume ({y ∈ O | DifferentiableAt ℝ f y} \ D) = 0)
    {x : E} (hx : x ∈ O) :
    regularSubderivative (fun y ↦ (f y : EReal)) x = supportFunction (reachableGradients f D x) := by
  apply regularSubderivative_eq_support_reachableGradients_of_le (hf x hx) hD
  intro w
  have hxD := subset_closure_differentiability_set_of_null_complement volume hO hf hnull hx
  obtain ⟨v,hv,hval,hmax⟩ := exists_max_inner_reachableGradients (hf x hx) hxD w
  rw [hval]
  by_contra hn
  obtain ⟨c,hvc,hc⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hvc' : ⟪v,w⟫_ℝ < c := EReal.coe_lt_coe_iff.mp hvc
  obtain ⟨r,hr,_,k,hL,hgrad⟩ := exists_lipschitz_ball_ae_inner_gradient_lt
    volume hO hf hD hnull hx (fun z hz ↦ (hmax z hz).trans_lt hvc')
  have hae : ∀ᵐ y ∂(volume : Measure E), y ∈ ball x r →
      ∃ L : E →L[ℝ] ℝ, HasFDerivAt f L y ∧ L w ≤ c := by
    filter_upwards [hgrad] with y hy hyB
    obtain ⟨hd,hbound⟩ := hy hyB
    exact ⟨fderiv ℝ f y,hd.hasFDerivAt,by simpa only [inner_gradient_left hd] using hbound.le⟩
  have hle : regularSubderivative (fun y ↦ (f y : EReal)) x w ≤ (c : EReal) := by
    apply regularSubderivative_le_of_eventual_increment_bound (hf x hx)
    have hy : Tendsto (Prod.fst : E × ℝ → E) (𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 x) := tendsto_fst
    have ht : Tendsto (Prod.snd : E × ℝ → ℝ) (𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) (𝓝[>] 0) := tendsto_snd
    have hpath : Tendsto (fun p : E × ℝ ↦ p.1 + p.2 • w)
        (𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 x) := by
      simpa only [zero_smul,add_zero] using
        hy.add ((ht.mono_right nhdsWithin_le_nhds).smul tendsto_const_nhds)
    filter_upwards [hy.eventually (ball_mem_nhds x hr),hpath.eventually (ball_mem_nhds x hr),
      ht.eventually self_mem_nhdsWithin] with p hp hp' hpos
    simpa only [mul_comm] using sub_le_mul_of_ae_fderiv_le hL hae (le_of_lt hpos) hp hp'
  exact hc.not_ge hle

/-- **Theorem 9.61**, the attained maximum formula. -/
theorem exists_max_reachableGradient_regularSubderivative
    {f : E → ℝ} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ y ∈ O, StrictlyContinuousAt f y) (hD : ∀ y ∈ D, DifferentiableAt ℝ f y)
    (hnull : volume ({y ∈ O | DifferentiableAt ℝ f y} \ D) = 0)
    {x : E} (hx : x ∈ O) (w : E) :
    ∃ v ∈ reachableGradients f D x,
      regularSubderivative (fun y ↦ (f y : EReal)) x w = (⟪v,w⟫_ℝ : EReal) ∧
      ∀ z ∈ reachableGradients f D x, ⟪z,w⟫_ℝ ≤ ⟪v,w⟫_ℝ := by
  rw [regularSubderivative_eq_support_reachableGradients hO hf hD hnull hx]
  exact exists_max_inner_reachableGradients (hf x hx)
    (subset_closure_differentiability_set_of_null_complement volume hO hf hnull hx) w

/-- **Theorem 9.61**, the nonempty compact reachable-gradient set and both
convex-hull representations, including the null-set exclusion refinement. -/
theorem clarke_reachableGradient_representation
    {f : E → ℝ} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ y ∈ O, StrictlyContinuousAt f y) (hD : ∀ y ∈ D, DifferentiableAt ℝ f y)
    (hnull : volume ({y ∈ O | DifferentiableAt ℝ f y} \ D) = 0)
    {x : E} (hx : x ∈ O) :
    (reachableGradients f D x).Nonempty ∧ IsCompact (reachableGradients f D x) ∧
      reachableGradients f D x ⊆ subdifferential (fun y ↦ (f y : EReal)) x ∧
      convexHull ℝ (reachableGradients f D x) =
        convexHull ℝ (subdifferential (fun y ↦ (f y : EReal)) x) ∧
      convexHull ℝ (reachableGradients f D x) = clarkeSubdifferential (fun y ↦ (f y : EReal)) x := by
  have hxD := subset_closure_differentiability_set_of_null_complement volume hO hf hnull hx
  obtain ⟨hne,hcomp⟩ := reachableGradients_nonempty_compact (hf x hx) hxD
  exact ⟨hne,hcomp,reachableGradients_subset_subdifferential (hf x hx).continuousAt hD,
    convexHull_reachableGradients_eq_of_support_eq (hf x hx) hxD
      (regularSubderivative_eq_support_reachableGradients hO hf hD hnull hx)⟩

/-- **Theorem 9.61**, at regular points the limiting subdifferential itself
is the convex hull of reachable gradients. -/
theorem convexHull_reachableGradients_eq_subdifferential_of_regular
    {f : E → ℝ} {O D : Set E} (hO : IsOpen O)
    (hf : ∀ y ∈ O, StrictlyContinuousAt f y) (hD : ∀ y ∈ D, DifferentiableAt ℝ f y)
    (hnull : volume ({y ∈ O | DifferentiableAt ℝ f y} \ D) = 0)
    {x : E} (hx : x ∈ O) (hreg : IsSubdifferentiallyRegularAt (fun y ↦ (f y : EReal)) x) :
    convexHull ℝ (reachableGradients f D x) = subdifferential (fun y ↦ (f y : EReal)) x := by
  have hh := (clarke_reachableGradient_representation hO hf hD hnull hx).2.2.2.1
  rw [hreg.subdifferential_eq_regularSubdifferential] at hh ⊢
  exact hh.trans (subdifferential_properties (f := fun y ↦ (f y : EReal))
    (x := x) rfl).2.1.convexHull_eq

end RW
