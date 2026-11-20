/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semidifferentiability from proto-differentiability and the Aubin property
-/

import RockafellarWets.Chapter9.AubinGraphicalDerivatives
import RockafellarWets.Chapter9.AubinLocalization
import RockafellarWets.Chapter8.MappingSemiderivatives

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : E → Set F} {x : E} {u : F} {k : ℝ≥0}

/-- **Proposition 9.50(a)**: the Aubin transport estimate corrects the input
directions of proto-derivative recovery sequences to any prescribed convergent
directions. This gives the joint set limit defining the semiderivative. -/
theorem AubinEstimate.hasMappingSemiderivative (h : AubinEstimate S univ x u k)
    (hp : IsProtoDifferentiableAt S x u) :
    HasMappingSemiderivative S x u (graphicalDerivative S x u) := by
  apply hasMappingSemiderivative_iff_continuousConvergence.mpr
  intro t ht w
  apply svConvergesContinuouslyAt_iff_forall_seq.mpr
  intro B hB
  have hi : graphicalDerivative S x u w ⊆
      innerSetLimit (fun n ↦ mappingDifferenceQuotient S x u (t n) (B n)) := by
    intro v hv
    have hpg := pkConvergesAlong_iff_forall_seq.mp hp t ht
    obtain ⟨q,hq,hq₀⟩ := mem_innerSetLimit_iff_exists_seq.mp
      (hpg.1.ge (show (w,v) ∈ svGraph (graphicalDerivative S x u) from hv))
    have hA := (continuous_fst.tendsto _).comp hq₀
    have hZ := (continuous_snd.tendsto _).comp hq₀
    have hT := h.eventually_transport_quotients ht hA hB hZ hq
    have herr : Tendsto (fun n ↦ (k:ℝ)*dist (q n).1 (B n)) atTop (𝓝 0) := by
      simpa only [dist_self,mul_zero] using (tendsto_const_nhds (x := (k:ℝ))).mul (hA.dist hB)
    apply mem_innerSetLimit_iff_eventually_ball.mpr
    intro ε hε
    filter_upwards [hT,hZ.eventually (ball_mem_nhds _ (half_pos hε)),
      herr.eventually (gt_mem_nhds (half_pos hε))] with n hTn hZn hEn
    obtain ⟨z,hz,hd⟩ := hTn
    refine ⟨z,hz,?_⟩
    change dist (q n).2 v < ε/2 at hZn
    change dist z v < ε
    have hd' : dist z (q n).2 ≤ k*dist (q n).1 (B n) := by simpa only [dist_comm] using hd
    exact (dist_triangle z (q n).2 v).trans_lt (by linarith)
  have ho : outerSetLimit (fun n ↦ mappingDifferenceQuotient S x u (t n) (B n)) ⊆
      graphicalDerivative S x u w := by
    intro v hv
    obtain ⟨φ,z,hφ,hz,hz₀⟩ := mem_outerSetLimit_iff_exists_subsequence.mp hv
    change (w,v) ∈ svGraph (graphicalDerivative S x u)
    rw [svGraph_graphicalDerivative_eq_outerLimit,mem_outerSetLimitAlong_iff_exists_seq]
    exact ⟨t ∘ φ,fun n ↦ (B (φ n),z n),ht.comp hφ.tendsto_atTop,hz,
      (hB.comp hφ.tendsto_atTop).prodMk_nhds hz₀⟩
  have hio := innerSetLimit_subset_outerSetLimit (fun n ↦ mappingDifferenceQuotient S x u (t n) (B n))
  exact ⟨Subset.antisymm (hio.trans ho) hi,Subset.antisymm ho (hi.trans hio)⟩

/-- **Proposition 9.50(a)** in terms of the named Aubin property. -/
theorem HasAubinPropertyAt.hasMappingSemiderivative (h : HasAubinPropertyAt S x u)
    (hp : IsProtoDifferentiableAt S x u) :
    HasMappingSemiderivative S x u (graphicalDerivative S x u) := by
  obtain ⟨k,hk⟩ := h.2.2.2
  exact hk.hasMappingSemiderivative hp

/-- Under the Aubin property, proto-differentiability and semidifferentiability
are equivalent. -/
theorem hasMappingSemiderivative_iff_proto_of_aubin [FiniteDimensional ℝ F]
    (h : HasAubinPropertyAt S x u) :
    HasMappingSemiderivative S x u (graphicalDerivative S x u) ↔ IsProtoDifferentiableAt S x u :=
  ⟨fun hs ↦ hs.protoDerivative.1,h.hasMappingSemiderivative⟩

section Regular

variable {P Q : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [FiniteDimensional ℝ Q]
    {R : P → Set Q} {a : P} {b : Q}

/-- The final assertion of **Proposition 9.50(a)**: strict continuity and
graphical regularity imply semidifferentiability. -/
theorem SvStrictlyContinuousAt.hasMappingSemiderivative_of_regular
    (h : SvStrictlyContinuousAt R a) (hb : b ∈ R a) (hr : IsGraphicallyRegularAt R a b) :
    HasMappingSemiderivative R a b (graphicalDerivative R a b) := by
  obtain ⟨k,hk⟩ := h.exists_aubinEstimate b
  exact hk.hasMappingSemiderivative (hr.isProtoDifferentiableAt hb)

end Regular

end RW
