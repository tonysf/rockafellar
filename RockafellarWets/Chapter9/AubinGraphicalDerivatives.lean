/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Transport of graphical derivative directions
-/

import RockafellarWets.Chapter9.AubinProperty
import RockafellarWets.Chapter9.SetValuedLipschitz
import RockafellarWets.Chapter8.ProtoDifferentiability
import RockafellarWets.Chapter8.SubderivativeFormulas
import RockafellarWets.Chapter3.SetOperations

open Filter Metric Set Topology
open scoped NNReal ENNReal Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : E → Set F} {x a b : E} {u v : F} {k : ℝ≥0}

/-- A fixed input direction gives a subset of the graphical outer limit
for any mapping, without a continuity hypothesis. -/
theorem quotient_outer_fixed_subset_graphicalDerivative (S : E → Set F) (x : E) (u : F) (b : E) :
    outerSetLimitAlong (𝓝[>] (0:ℝ)) (fun t ↦ mappingDifferenceQuotient S x u t b) ⊆
      graphicalDerivative S x u b := by
  intro z hz
  obtain ⟨t,q,ht,hq,hq₀⟩ := mem_outerSetLimitAlong_iff_exists_seq.mp hz
  change (b,z) ∈ svGraph (graphicalDerivative S x u)
  rw [svGraph_graphicalDerivative_eq_outerLimit,mem_outerSetLimitAlong_iff_exists_seq]
  exact ⟨t,fun n ↦ (b,q n),ht,hq,tendsto_const_nhds.prodMk_nhds hq₀⟩

/-- The local Aubin estimate rescales to estimates for arbitrary convergent
input and output directions along the difference quotients. -/
theorem AubinEstimate.eventually_transport_quotients (h : AubinEstimate S univ x u k)
    {t : ℕ → ℝ} {A B : ℕ → E} {Z : ℕ → F} (ht : Tendsto t atTop (𝓝[>] 0))
    (hA : Tendsto A atTop (𝓝 a)) (hB : Tendsto B atTop (𝓝 b)) (hZ : Tendsto Z atTop (𝓝 v))
    (hM : ∀ᶠ n in atTop, Z n ∈ mappingDifferenceQuotient S x u (t n) (A n)) :
    ∀ᶠ n in atTop, ∃ z ∈ mappingDifferenceQuotient S x u (t n) (B n),
      dist (Z n) z ≤ k*dist (A n) (B n) := by
  obtain ⟨V,hV,W,hW,H⟩ := h
  have h₀ := tendsto_nhdsWithin_iff.mp ht
  have h1 : Tendsto (fun n ↦ x + t n • A n) atTop (𝓝 x) := by simpa using tendsto_const_nhds.add (h₀.1.smul hA)
  have h2 : Tendsto (fun n ↦ x + t n • B n) atTop (𝓝 x) := by simpa using tendsto_const_nhds.add (h₀.1.smul hB)
  have h3 : Tendsto (fun n ↦ u + t n • Z n) atTop (𝓝 u) := by simpa using tendsto_const_nhds.add (h₀.1.smul hZ)
  filter_upwards [h₀.2,h1.eventually hV,h2.eventually hV,h3.eventually hW,hM] with n hn h1n h2n h3n hMn
  have hp : 0 < t n := hn
  obtain ⟨z,hz,hd⟩ := H _ ⟨trivial,h1n⟩ _ ⟨trivial,h2n⟩ _ ⟨(mem_mappingDifferenceQuotient_iff hp.ne').mp hMn,h3n⟩
  refine ⟨(t n)⁻¹ • (z-u),⟨z,hz,rfl⟩,?_⟩
  have he : (t n)⁻¹ • ((u + t n • Z n)-z) = Z n - (t n)⁻¹ • (z-u) := by
    rw [show u+t n • Z n-z = t n • Z n-(z-u) by abel,smul_sub,inv_smul_smul₀ hp.ne']
  simp only [dist_eq_norm,add_sub_add_left_eq_sub,← smul_sub,norm_smul_of_nonneg hp.le] at hd
  rw [dist_eq_norm,← he,norm_smul_of_nonneg (inv_pos.mpr hp).le,inv_mul_le_iff₀ hp,dist_eq_norm]
  linarith only [hd,mul_left_comm (k:ℝ) (t n) ‖A n-B n‖]

/-- **Exercise 9.49(a).** Every graphical derivative output at one input
transports to a fixed-direction quotient limit at another input, with
the original Lipschitz bound. -/
theorem AubinEstimate.exists_fixed_quotient_limit [ProperSpace F] (h : AubinEstimate S univ x u k)
    (hv : v ∈ graphicalDerivative S x u a) (b : E) :
    ∃ z ∈ outerSetLimitAlong (𝓝[>] (0:ℝ)) (fun t ↦ mappingDifferenceQuotient S x u t b),
      dist v z ≤ k*dist a b := by
  change (a,v) ∈ svGraph (graphicalDerivative S x u) at hv
  rw [svGraph_graphicalDerivative_eq_outerLimit,mem_outerSetLimitAlong_iff_exists_seq] at hv
  obtain ⟨t,q,ht,hq,hq₀⟩ := hv
  have hA := (continuous_fst.tendsto _).comp hq₀
  have hZ := (continuous_snd.tendsto _).comp hq₀
  have H := h.eventually_transport_quotients ht hA (tendsto_const_nhds (x := b)) hZ (.of_forall hq)
  obtain ⟨N,hN⟩ := eventually_atTop.mp H
  let ψ (n : ℕ) := n+N
  have hψ : Tendsto ψ atTop atTop := tendsto_add_atTop_nat N
  choose s hs hd using fun n ↦ hN (ψ n) (by dsimp [ψ]; omega)
  have hdlim := (tendsto_const_nhds (x := (k:ℝ))).mul ((hA.comp hψ).dist (tendsto_const_nhds (x := b)))
  obtain ⟨R,hR⟩ := (isBounded_range_of_tendsto _ hdlim).exists_norm_le
  obtain ⟨M,hM⟩ := (isBounded_range_of_tendsto _ (hZ.comp hψ)).exists_norm_le
  have hsB (n : ℕ) : s n ∈ closedBall 0 (M+R) := by
    rw [mem_closedBall_zero_iff]
    have hr := hR _ (mem_range_self n)
    have hm := hM _ (mem_range_self n)
    have hh := dist_triangle (s n) (q (ψ n)).2 0
    rw [dist_zero_right,dist_zero_right,dist_comm (s n)] at hh
    change ‖(k:ℝ)*dist (q (ψ n)).1 b‖ ≤ R at hr
    have hr' : (k:ℝ)*dist (q (ψ n)).1 b ≤ R := (le_abs_self _).trans hr
    change ‖(q (ψ n)).2‖ ≤ M at hm
    exact hh.trans ((add_le_add ((hd n).trans hr') hm).trans_eq (add_comm ..))
  obtain ⟨z,_,φ,hφ,hz⟩ := (isCompact_closedBall _ _).tendsto_subseq hsB
  refine ⟨z,mem_outerSetLimitAlong_iff_exists_seq.mpr ⟨t ∘ ψ ∘ φ,s ∘ φ,
    ht.comp (hψ.comp hφ.tendsto_atTop),fun n ↦ hs (φ n),hz⟩,?_⟩
  exact le_of_tendsto_of_tendsto (((hZ.comp hψ).comp hφ.tendsto_atTop).dist hz)
    (hdlim.comp hφ.tendsto_atTop) (.of_forall fun n ↦ hd (φ n))

theorem AubinEstimate.graphicalDerivative_transport [ProperSpace F] (h : AubinEstimate S univ x u k)
    (hv : v ∈ graphicalDerivative S x u a) (b : E) :
    ∃ z ∈ graphicalDerivative S x u b, dist v z ≤ k*dist a b := by
  obtain ⟨z,hz,hd⟩ := h.exists_fixed_quotient_limit hv b
  exact ⟨z,quotient_outer_fixed_subset_graphicalDerivative S x u b hz,hd⟩

theorem AubinEstimate.graphicalDerivative_eq_outer_fixed [ProperSpace F] (h : AubinEstimate S univ x u k) (b : E) :
    graphicalDerivative S x u b = outerSetLimitAlong (𝓝[>] (0:ℝ)) (fun t ↦ mappingDifferenceQuotient S x u t b) := by
  apply Subset.antisymm _ (quotient_outer_fixed_subset_graphicalDerivative ..)
  intro z hz
  obtain ⟨z',hz',he⟩ := h.exists_fixed_quotient_limit hz b
  simpa using (show z = z' from dist_le_zero.mp (by simpa using he)) ▸ hz'

theorem AubinEstimate.exists_graphicalDerivative_norm_le [ProperSpace F] (h : AubinEstimate S univ x u k)
    (hu : u ∈ S x) (b : E) : ∃ z ∈ graphicalDerivative S x u b, ‖z‖ ≤ k*‖b‖ := by
  obtain ⟨z,hz,hd⟩ := h.graphicalDerivative_transport (a := 0) (v := 0)
    ((isCone_tangentCone (show WithLp.toLp 2 (x,u) ∈ euclideanSvGraph S from hu)).1) b
  exact ⟨z,hz,by simpa using hd⟩

end RW
