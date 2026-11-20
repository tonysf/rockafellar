/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Inverse transport, metric estimates, and linear openness
-/

import RockafellarWets.Chapter9.ExtendedAubinProperty
import RockafellarWets.Chapter9.SetValuedLipschitz
import RockafellarWets.Chapter5.SemicontinuityCriteria

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [MetricSpace E] [MetricSpace F]
    {S : E → Set F} {A U : Set F} {V : Set E} {k l : ℝ≥0}

/-- The fiber inclusion in 9(25a), with separate source and target sets. -/
def InverseTransportEstimate (S : E → Set F) (A U : Set F) (V : Set E) (k : ℝ≥0) : Prop :=
  ∀ a ∈ A, ∀ b ∈ U, ∀ x ∈ V, a ∈ S x → ∃ y, b ∈ S y ∧ dist x y ≤ k * dist a b

/-- The distance inequality 9(25b). Distances to empty fibers are infinite. -/
def InverseMetricEstimate (S : E → Set F) (A U : Set F) (V : Set E) (k : ℝ≥0) : Prop :=
  ∀ x ∈ V, ∀ b ∈ U, infEDist x (svInv S b) ≤ (k : ℝ≥0∞) * infEDist b (S x ∩ A)

/-- The pointwise form of 9(25c), equivalent to the stated image inclusion. -/
def InverseOpenEstimate (S : E → Set F) (A U : Set F) (V : Set E) (k : ℝ≥0) : Prop :=
  ∀ x ∈ V, ∀ r : ℝ, 0 < r → ∀ a ∈ S x ∩ A, ∀ b ∈ U, dist a b ≤ r →
    ∃ y, b ∈ S y ∧ dist x y ≤ k * r

/-- The closed-graph and range hypotheses in Proposition 9.46 ensure the
nonempty closed inverse fibers needed to attain distance bounds. -/
theorem nonemptyClosedValuedOn_inverse_of_osc (hS : SvOsc S) (hU : U ⊆ svRange S) :
    NonemptyClosedValuedOn (svInv S) U := by
  intro u hu
  exact ⟨hU hu,((isClosed_svGraph_iff_svOsc).mpr hS).preimage
    (continuous_id.prodMk continuous_const)⟩

/-- A transport bound controls the infimum of the distances in the source
fiber. Positivity handles an empty source fiber. -/
theorem InverseTransportEstimate.metricEstimate (h : InverseTransportEstimate S A U V k) (hk : 0 < k) :
    InverseMetricEstimate S A U V k := by
  intro x hx b hb
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  conv_rhs => rw [infEDist,ENNReal.mul_iInf_of_ne hk0 ENNReal.coe_ne_top]
  apply le_iInf
  intro a
  rw [ENNReal.mul_iInf_of_ne hk0 ENNReal.coe_ne_top]
  apply le_iInf
  rintro ⟨ha,hA⟩
  obtain ⟨y,hy,hd⟩ := h a hA b hb x hx ha
  apply (infEDist_le_edist_of_mem (show y ∈ svInv S b from hy)).trans
  have h := ENNReal.ofReal_le_ofReal hd
  simpa [edist_dist,ENNReal.ofReal_mul,dist_comm] using h

/-- A larger constant converts a distance bound into an attained transport
bound, even for nonclosed fibers. -/
theorem InverseMetricEstimate.transportEstimate_of_lt (h : InverseMetricEstimate S A U V k) (hkl : k < l) :
    InverseTransportEstimate S A U V l := by
  intro a ha b hb x hx hax
  by_cases he : a = b
  · subst a
    exact ⟨x,hax,by simp⟩
  have hd : 0 < dist a b := dist_pos.mpr he
  have hlpos : 0 < (l : ℝ) := lt_of_le_of_lt k.2 hkl
  have hbnd := (h x hx b hb).trans
    (mul_le_mul' le_rfl (infEDist_le_edist_of_mem (show a ∈ S x ∩ A from ⟨hax,ha⟩)))
  have hsmall : infEDist x (svInv S b) < ENNReal.ofReal (l * dist a b) := by
    apply hbnd.trans_lt
    have hr := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < (l:ℝ)*dist a b)).mpr
      (mul_lt_mul_of_pos_right (show (k:ℝ) < l from hkl) hd)
    simpa [edist_dist,ENNReal.ofReal_mul,dist_comm] using hr
  obtain ⟨y,hy,hd'⟩ := infEDist_lt_iff.mp hsmall
  exact ⟨y,hy,(ENNReal.ofReal_lt_ofReal_iff'.mp (by simpa only [edist_dist] using hd')).1.le⟩

/-- Closed nonempty inverse fibers allow the same constant in the distance
and transport estimates. -/
theorem InverseMetricEstimate.transportEstimate [ProperSpace E]
    (h : InverseMetricEstimate S A U V k) (hS : NonemptyClosedValuedOn (svInv S) U) :
    InverseTransportEstimate S A U V k := by
  intro a ha b hb x hx hax
  apply (exists_mem_dist_le_iff_infEDist_le (hS b hb).1 (hS b hb).2 x (by positivity)).mpr
  have hd := (h x hx b hb).trans
    (mul_le_mul' le_rfl (infEDist_le_edist_of_mem (show a ∈ S x ∩ A from ⟨hax,ha⟩)))
  simpa [edist_dist,ENNReal.ofReal_mul,dist_comm] using hd

theorem inverseTransportEstimate_iff_openEstimate :
    InverseTransportEstimate S A U V k ↔ InverseOpenEstimate S A U V k := by
  constructor
  · intro h x hx r hr a ha b hb hd
    obtain ⟨y,hy,hxy⟩ := h a ha.2 b hb x hx ha.1
    exact ⟨y,hy,hxy.trans (mul_le_mul_of_nonneg_left hd k.2)⟩
  · intro h a ha b hb x hx hax
    by_cases he : a = b
    · subst a
      exact ⟨x,hax,by simp⟩
    · exact h x hx (dist a b) (dist_pos.mpr he) a ⟨hax,ha⟩ b hb le_rfl

/-- **Proposition 9.46**, the three estimates with a positive fixed constant. -/
theorem inverseTransportEstimate_iff_metricEstimate [ProperSpace E]
    (hS : NonemptyClosedValuedOn (svInv S) U) (hk : 0 < k) :
    InverseTransportEstimate S A U V k ↔ InverseMetricEstimate S A U V k :=
  ⟨fun h ↦ h.metricEstimate hk, fun h ↦ h.transportEstimate hS⟩

/-- **Proposition 9.46(a–c)**, the global inverse Lipschitz statement. -/
theorem svLipschitzOnWith_inverse_iff_metricEstimate [ProperSpace E]
    (hS : NonemptyClosedValuedOn (svInv S) U) (hk : 0 < k) :
    SvLipschitzOnWith k (svInv S) U ↔ InverseMetricEstimate S U U univ k := by
  rw [svLipschitzOnWith_iff_transport hS,← inverseTransportEstimate_iff_metricEstimate hS hk]
  exact ⟨fun h a ha b hb x _ hx ↦ h a ha b hb x hx,fun h a ha b hb x hx ↦ h a ha b hb x trivial hx⟩

/-- The transport/openness equivalence admits a zero constant. -/
theorem svLipschitzOnWith_inverse_iff_openEstimate [ProperSpace E]
    (hS : NonemptyClosedValuedOn (svInv S) U) :
    SvLipschitzOnWith k (svInv S) U ↔ InverseOpenEstimate S U U univ k := by
  rw [← inverseTransportEstimate_iff_openEstimate,svLipschitzOnWith_iff_transport hS]
  exact ⟨fun h a ha b hb x _ hx ↦ h a ha b hb x hx,fun h a ha b hb x hx ↦ h a ha b hb x trivial hx⟩

private def singletonGraphMapping (x : ℝ) : Set ℝ := if x = 0 then {0} else ∅

/-- The printed fixed-constant equivalence in 9.46 needs a positive constant
when distances to empty fibers use the standard convention `0 * ∞ = 0`.
The graph consisting of the single point `(0,0)` has a zero-Lipschitz inverse
on its range, while its metric estimate fails outside its domain. -/
theorem zero_inverseMetricEstimate_counterexample :
    ∃ S : ℝ → Set ℝ, IsClosed (svGraph S) ∧
      SvLipschitzOnWith 0 (svInv S) {0} ∧
      InverseOpenEstimate S {0} {0} univ 0 ∧
      ¬ InverseMetricEstimate S {0} {0} univ 0 := by
  have hg : svGraph singletonGraphMapping = {(0,0)} := by
    ext ⟨x,u⟩
    simp only [svGraph,mem_setOf_eq,singletonGraphMapping,mem_singleton_iff,Prod.mk.injEq]
    split_ifs with hx <;> simp_all
  have hi : svInv singletonGraphMapping 0 = {0} := by
    ext x
    simp [svInv,singletonGraphMapping]
  have hc : NonemptyClosedValuedOn (svInv singletonGraphMapping) {0} := by
    rintro u rfl
    rw [hi]
    exact ⟨singleton_nonempty _,isClosed_singleton⟩
  have hL : SvLipschitzOnWith 0 (svInv singletonGraphMapping) {0} := by
    refine ⟨hc,?_⟩
    rintro a rfl b rfl
    simp
  refine ⟨singletonGraphMapping,hg ▸ isClosed_singleton,hL,
    (svLipschitzOnWith_inverse_iff_openEstimate hc).mp hL,?_⟩
  intro hm
  have h := hm 1 trivial 0 (mem_singleton _)
  rw [hi] at h
  norm_num [infEDist_singleton,edist_dist] at h

end RW
