/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Compact quadratic penalties for constrained normals

The analytic step in Theorem 6.14: minimizing a quadratic constraint penalty
on a compact product yields feasible limiting points and nearby regular
normals to both factors. The multiplier normalization is performed separately.
-/

import RockafellarWets.Chapter6.SmoothGradientWitness
import RockafellarWets.Chapter6.Optimality
import RockafellarWets.Chapter6.ElementaryCones
import Mathlib.Analysis.InnerProductSpace.Adjoint

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section CompactPenalty

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Compact quadratic-penalty minimizers have a subsequence converging to
the unique constrained maximizer. Only continuity is needed here. -/
theorem exists_penalty_minimizers_tendsto
    {X : Set E} {D : Set F} (hX : IsCompact X) (hD : IsCompact D)
    {f : E → F} (hf : Continuous f) {h : E → ℝ} (hh : Continuous h)
    {x : E} (hx : x ∈ X) (hfx : f x ∈ D)
    (hmax : IsMaxOn h (X ∩ f ⁻¹' D) x)
    (hunique : ∀ y ∈ X ∩ f ⁻¹' D, h y = h x → y = x) :
    ∃ (τ : ℕ → ℝ) (xs : ℕ → E) (us : ℕ → F),
      (∀ n, 0 < τ n) ∧ Tendsto τ atTop (𝓝 0) ∧
      (∀ n, xs n ∈ X) ∧ (∀ n, us n ∈ D) ∧
      Tendsto xs atTop (𝓝 x) ∧ Tendsto us atTop (𝓝 (f x)) ∧
      ∀ n, IsMinOn (fun p : E × F ↦
        ‖f p.1 - p.2‖ ^ 2 / 2 - τ n * h p.1) (X ×ˢ D) (xs n, us n) := by
  let τ : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hτpos : ∀ n, 0 < τ n := by intro n; dsimp [τ]; positivity
  have hτto : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmin : ∀ n, ∃ p ∈ X ×ˢ D, IsMinOn
      (fun p : E × F ↦ ‖f p.1 - p.2‖ ^ 2 / 2 - τ n * h p.1) (X ×ˢ D) p := by
    intro n
    apply (hX.prod hD).exists_isMinOn ⟨(x, f x), hx, hfx⟩
    exact (((hf.comp continuous_fst).sub continuous_snd).norm.pow 2 |>.div_const 2
      |>.sub (continuous_const.mul (hh.comp continuous_fst))).continuousOn
  choose p hp hpm using hmin
  obtain ⟨q, hq, φ, hφ, hpto⟩ := (hX.prod hD).tendsto_subseq hp
  have hφτ := hτto.comp hφ.tendsto_atTop
  have hpx := hpto.fst_nhds
  have hpu := hpto.snd_nhds
  have hineq : ∀ n, ‖f (p (φ n)).1 - (p (φ n)).2‖ ^ 2 / 2 ≤
      τ (φ n) * (h (p (φ n)).1 - h x) := by
    intro n
    have hm := hpm (φ n) (show (x, f x) ∈ X ×ˢ D from ⟨hx, hfx⟩)
    dsimp at hm
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_div, zero_sub] at hm
    linarith
  have hres : f q.1 = q.2 := by
    have hlim := le_of_tendsto_of_tendsto
      (((hf.tendsto q.1).comp hpx).sub hpu |>.norm.pow 2 |>.div_const 2)
      (hφτ.mul (((hh.tendsto q.1).comp hpx).sub tendsto_const_nhds))
      (Eventually.of_forall hineq)
    simp only [zero_mul] at hlim
    have hz : ‖f q.1 - q.2‖ = 0 := by nlinarith [sq_nonneg ‖f q.1 - q.2‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hge : h x ≤ h q.1 := by
    apply ge_of_tendsto ((hh.tendsto q.1).comp hpx)
    apply Eventually.of_forall
    intro n
    change h x ≤ h (p (φ n)).1
    have hi := hineq n
    have hn := hτpos (φ n)
    nlinarith [sq_nonneg ‖f (p (φ n)).1 - (p (φ n)).2‖]
  have hqmem : q.1 ∈ X ∩ f ⁻¹' D := ⟨hq.1, by simpa only [mem_preimage, hres] using hq.2⟩
  have hqx : q.1 = x := hunique q.1 hqmem (le_antisymm (hmax hqmem) hge)
  have hqu : q.2 = f x := by rw [← hres, hqx]
  refine ⟨τ ∘ φ, fun n ↦ (p (φ n)).1, fun n ↦ (p (φ n)).2,
    fun n ↦ hτpos (φ n), hφτ, fun n ↦ (hp (φ n)).1,
    fun n ↦ (hp (φ n)).2, ?_, ?_, fun n ↦ hpm (φ n)⟩
  · simpa only [hqx] using hpx
  · simpa only [hqu] using hpu

end CompactPenalty

section PenaltyNormals

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- First-order conditions for a quadratic penalty on a product set. -/
theorem penalty_minimizer_regular_normals
    {X : Set E} {D : Set F} {f : E → F} {A : E →L[ℝ] F}
    {h : E → ℝ} {g x : E} {u : F} {τ : ℝ}
    (hx : x ∈ X) (hu : u ∈ D) (hf : HasFDerivAt f A x)
    (hh : HasGradientAt h g x)
    (hmin : IsMinOn (fun p : E × F ↦ ‖f p.1 - p.2‖ ^ 2 / 2 - τ * h p.1)
      (X ×ˢ D) (x, u)) :
    τ • g - A.adjoint (f x - u) ∈ regularNormalCone X x ∧
      f x - u ∈ regularNormalCone D u := by
  have hxgrad : HasGradientAt (fun y ↦ ‖f y - u‖ ^ 2 / 2 - τ * h y)
      (A.adjoint (f x - u) - τ • g) x := by
    apply hasGradientAt_iff_hasFDerivAt.2
    convert ((hf.sub_const u).norm_sq.mul_const (1 / 2)).sub
      (hh.hasFDerivAt.const_mul τ) using 1
    · ext w
      simp [div_eq_mul_inv]
    · ext w
      simp [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]
  have hugrad : HasGradientAt (fun v ↦ ‖f x - v‖ ^ 2 / 2 - τ * h x)
      (u - f x) u := by
    apply hasGradientAt_iff_hasFDerivAt.2
    convert (((hasFDerivAt_id u).const_sub (f x)).norm_sq.mul_const (1 / 2)).sub_const
      (τ * h x) using 1
    · ext w
      simp [div_eq_mul_inv]
    · ext w
      simp [InnerProductSpace.toDual_apply_apply]
  constructor
  · have hm : IsMinOn (fun y ↦ ‖f y - u‖ ^ 2 / 2 - τ * h y) X x :=
      fun y hy ↦ hmin (show (y, u) ∈ X ×ˢ D from ⟨hy, hu⟩)
    simpa only [neg_sub] using
      IsLocalMinOn.neg_gradient_mem_regularNormalCone hx hm.localize hxgrad
  · have hm : IsMinOn (fun v ↦ ‖f x - v‖ ^ 2 / 2 - τ * h x) D u :=
      fun v hv ↦ hmin (show (x, v) ∈ X ×ˢ D from ⟨hx, hv⟩)
    simpa only [neg_sub] using
      IsLocalMinOn.neg_gradient_mem_regularNormalCone hu hm.localize hugrad

end PenaltyNormals

end RW
