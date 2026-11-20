/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lower Lipschitz estimates and local invertibility
-/

import RockafellarWets.Chapter9.InverseLocalizations

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A positive lower Lipschitz estimate on an input neighborhood is exactly
an upper Lipschitz estimate on the inverse graph near its base point. -/
theorem exists_localGraphLipschitzBound_inverse_iff {f : E → F} {x : E}
    (hf : ContinuousAt f x) :
    (∃ k : ℝ≥0, LocalGraphLipschitzBound (svGraph (svInv (fun a ↦ {f a}))) (f x,x) k) ↔
      ∃ c : ℝ, 0 < c ∧ ∃ U ∈ 𝓝 x, ∀ a ∈ U, ∀ b ∈ U,
        c * dist a b ≤ dist (f a) (f b) := by
  constructor
  · rintro ⟨k,δ,hδ,hbound⟩
    let U := ball x δ ∩ f ⁻¹' ball (f x) δ
    have hU : U ∈ 𝓝 x := inter_mem (ball_mem_nhds x hδ) (hf (ball_mem_nhds (f x) hδ))
    have hK : 0 < (k:ℝ)+1 := by positivity
    refine ⟨((k:ℝ)+1)⁻¹,inv_pos.mpr hK,U,hU,?_⟩
    intro a ha b hb
    have hg {a : E} (ha : a ∈ U) :
        (f a,a) ∈ svGraph (svInv (fun a ↦ {f a})) ∩ ball (f x,x) δ := by
      refine ⟨mem_singleton _,?_⟩
      rw [← ball_prod_same]
      exact ⟨ha.2,ha.1⟩
    have h := hbound _ (hg ha) _ (hg hb)
    rw [inv_mul_le_iff₀ hK]
    change dist a b ≤ ((k:ℝ)+1)*dist (f a) (f b)
    have hd := dist_nonneg (x := f a) (y := f b)
    dsimp only at h
    nlinarith
  · rintro ⟨c,hc,U,hU,hbound⟩
    obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨⟨c⁻¹,(inv_pos.mpr hc).le⟩,δ,hδ,?_⟩
    intro p hp q hq
    have hpball := hp.2
    have hqball := hq.2
    rw [← ball_prod_same] at hpball hqball
    have hpEq : p.1 = f p.2 := hp.1
    have hqEq : q.1 = f q.2 := hq.1
    have h := hbound p.2 (hδU hpball.2) q.2 (hδU hqball.2)
    change dist p.2 q.2 ≤ c⁻¹ * dist p.1 q.1
    rw [le_inv_mul_iff₀ hc,hpEq,hqEq]
    exact h

section Square
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The positive lower slope criterion following **Corollary 9.55**,
in its equivalent neighborhood-estimate form. -/
theorem hasLipschitzInverseLocalization_iff_lower_bound {f : P → P} {x : P} {O : Set P}
    (hO : IsOpen O) (hx : x ∈ O) (hf : ContinuousOn f O) :
    HasLipschitzSingleValuedLocalization (svInv (fun a ↦ {f a})) (f x) x ↔
      ∃ c : ℝ, 0 < c ∧ ∃ U ∈ 𝓝 x, ∀ a ∈ U, ∀ b ∈ U,
        c * dist a b ≤ dist (f a) (f b) := by
  rw [hasLipschitzInverseLocalization_iff_strictKernel_zero hO hx hf,
    ← strictGraphicalDerivative_svInv]
  rw [strictGraphicalDerivative_zero_iff_localGraphLipschitz (show x ∈ svInv (fun a ↦ {f a}) (f x) from mem_singleton _)]
  exact exists_localGraphLipschitzBound_inverse_iff (hf.continuousAt (hO.mem_nhds hx))

end Square
end RW
