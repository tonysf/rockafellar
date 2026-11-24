/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Horizon cones and horizon functions of measurable mappings

Exercise 14.21(a) and Exercise 14.54(a) of Rockafellar–Wets.  The horizon cone
`C^∞ = {0} ∪ asymptoticCone ℝ C` (with `∅^∞ = {0}`) is the outer limit of the scalings `λC`,
`λ ↘ 0`, realized here over positive rationals:
`asymptoticCone ℝ C = ⋂ₘ cl ⋃_{0 < q < 1/(m+1)} q C`.
-/

import RockafellarWets.Chapter14.IntegrandExamples
import RockafellarWets.Chapter3.HorizonFunctions

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Pointwise Classical

noncomputable section

namespace RW

section Formula

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem asymptoticCone_eq_iInter_closure_rat_smul (C : Set E) :
    asymptoticCone ℝ C = ⋂ m : ℕ, _root_.closure (⋃ q : ℚ,
      ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)), (q : ℝ) • C) := by
  ext v
  rw [mem_asymptoticCone_iff, AffineSpace.asymptoticNhds_eq_smul, Filter.frequently_iff,
    mem_iInter]
  constructor
  · intro h m
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hU : Ioi ((m : ℝ) + 1) • ball v (ε / 2) ∈ atTop (α := ℝ) • 𝓝 v :=
      Filter.mem_smul.2 ⟨_, Ioi_mem_atTop _, _, ball_mem_nhds v (half_pos hε), subset_rfl⟩
    obtain ⟨_, ⟨s, hs, w, hw, rfl⟩, hpC⟩ := h hU
    have hs' : (m : ℝ) + 1 < s := hs
    have hspos : 0 < s := lt_of_le_of_lt (by positivity) hs'
    set p := s • w with hpdef
    -- rational approximation of `1/s`
    have hgap : 0 < 1 / ((m : ℝ) + 1) - 1 / s := by
      rw [sub_pos]
      exact one_div_lt_one_div_of_lt (by positivity) hs'
    obtain ⟨δ, hδpos, hδ1, hδ2, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / s ∧
        δ < 1 / ((m : ℝ) + 1) - 1 / s ∧ δ * ‖p‖ < ε / 2 := by
      refine ⟨min (min (1 / s / 2) ((1 / ((m : ℝ) + 1) - 1 / s) / 2)) (ε / 4 / (‖p‖ + 1)),
        lt_min (lt_min (div_pos (one_div_pos.2 hspos) two_pos) (by linarith))
          (div_pos (by linarith) (by positivity)), ?_, ?_, ?_⟩
      · exact (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith [one_div_pos.2 hspos]))
      · exact (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (by linarith))
      · calc min (min (1 / s / 2) ((1 / ((m : ℝ) + 1) - 1 / s) / 2)) (ε / 4 / (‖p‖ + 1)) * ‖p‖
            ≤ ε / 4 / (‖p‖ + 1) * ‖p‖ := by gcongr; exact min_le_right _ _
          _ ≤ ε / 4 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [norm_nonneg p]
          _ < ε / 2 := by linarith
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show 1 / s - δ < 1 / s + δ by linarith)
    have hq0 : (0 : ℝ) < q := by linarith
    have hqm : (q : ℝ) < 1 / ((m : ℝ) + 1) := by linarith
    refine ⟨(q : ℝ) • p, mem_iUnion₂.2 ⟨q, ⟨by exact_mod_cast hq0, hqm⟩, smul_mem_smul_set hpC⟩, ?_⟩
    have hw' : (1 / s) • p = w := by
      rw [hpdef, smul_smul, one_div, inv_mul_cancel₀ hspos.ne', one_smul]
    have h1 : dist ((q : ℝ) • p) w ≤ |(q : ℝ) - 1 / s| * ‖p‖ := by
      rw [← hw', dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
    have h2 : |(q : ℝ) - 1 / s| < δ := by
      rw [abs_lt]
      constructor <;> linarith
    have h3 : dist w v < ε / 2 := hw
    rw [dist_comm]
    calc dist ((q : ℝ) • p) v ≤ dist ((q : ℝ) • p) w + dist w v := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
          have : |(q : ℝ) - 1 / s| * ‖p‖ ≤ δ * ‖p‖ :=
            mul_le_mul_of_nonneg_right h2.le (norm_nonneg _)
          linarith
      _ = ε := by ring
  · intro h U hU
    obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_smul.1 hU
    obtain ⟨R, hR⟩ := mem_atTop_sets.1 hA
    obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.1 hB
    obtain ⟨m, hm⟩ := exists_nat_gt (max R 1)
    have hcl := h m
    rw [Metric.mem_closure_iff] at hcl
    obtain ⟨z, hz, hzv⟩ := hcl ε hε
    obtain ⟨q, ⟨hq0, hqm⟩, c, hc, rfl⟩ := mem_iUnion₂.1 hz
    have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
    refine ⟨c, hAB ⟨(q : ℝ)⁻¹, hR _ ?_, (q : ℝ) • c, hεB ?_, ?_⟩, hc⟩
    · have h1 : (q : ℝ) < 1 / ((m : ℝ) + 1) := hqm
      have h2 : 1 / ((m : ℝ) + 1) < 1 / R ∨ R ≤ 0 := by
        rcases le_or_gt R 0 with hR0 | hR0
        · exact Or.inr hR0
        · left
          exact one_div_lt_one_div_of_lt hR0 (by linarith [le_max_left R 1])
      rcases h2 with h2 | h2
      · have hRpos : 0 < R := by
          by_contra hneg
          push_neg at hneg
          have := one_div_nonpos.2 hneg
          linarith [one_div_pos.2 (show (0 : ℝ) < (m : ℝ) + 1 by positivity)]
        rw [ge_iff_le, le_inv_comm₀ hRpos hq0']
        simp only [one_div] at h1 h2
        linarith
      · exact le_trans h2 (inv_nonneg.2 hq0'.le)
    · rw [mem_ball, dist_comm]
      exact hzv
    · simp only [smul_smul, inv_mul_cancel₀ hq0'.ne', one_smul]

theorem horizonCone_eq_insert_iInter (C : Set E) :
    horizonCone C = insert 0 (⋂ m : ℕ, _root_.closure (⋃ q : ℚ,
      ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)), (q : ℝ) • C)) := by
  rw [horizonCone, asymptoticCone_eq_iInter_closure_rat_smul]

end Formula

section Exercise1421

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Exercise 14.21(a) (horizon cones)**: for any measurable `S`, the horizon cone mapping
`t ↦ S(t)^∞` is closed-valued and measurable. -/
theorem SvMeasurable.horizonCone {S : T → Set E} (hS : SvMeasurable S) :
    (∀ t, IsClosed (RW.horizonCone (S t))) ∧ SvMeasurable (fun t ↦ RW.horizonCone (S t)) := by
  have hm : SvMeasurable (fun t ↦ ⋂ m : ℕ, _root_.closure (⋃ q : ℚ,
      ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)), (q : ℝ) • S t)) := by
    refine SvMeasurable.iInter (fun m ↦ (SvMeasurable.iUnion fun q ↦ ?_).closure)
      (fun _ _ ↦ isClosed_closure)
    by_cases hq : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)
    · have : (fun t ↦ ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)), (q : ℝ) • S t) =
          fun t ↦ (q : ℝ) • S t := funext fun t ↦ iSup_pos hq
      rw [this]
      exact hS.image (continuous_const_smul (q : ℝ))
    · have : (fun t ↦ ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)), (q : ℝ) • S t) =
          fun _ ↦ ∅ := funext fun t ↦ iSup_neg hq
      rw [this]
      exact svMeasurable_const ∅
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [horizonCone_eq_insert_iInter, insert_eq]
    exact isClosed_singleton.union (isClosed_iInter fun _ ↦ isClosed_closure)
  · have heq : (fun t ↦ RW.horizonCone (S t)) = fun t ↦ {(0 : E)} ∪ ⋂ m : ℕ,
        _root_.closure (⋃ q : ℚ, ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)), (q : ℝ) • S t) :=
      funext fun t ↦ by rw [horizonCone_eq_insert_iInter, insert_eq]
    rw [heq]
    exact (svMeasurable_const _).union hm

end Exercise1421

section Exercise1454

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem horizonFunction_of_epigraph_empty {g : E → EReal} (h : epigraph g = ∅) :
    RW.horizonFunction g = indicatorVA {0} := by
  have hH : horizonCone (epigraph g) = {0} := by rw [h, horizonCone_empty]
  funext w
  unfold RW.horizonFunction
  rw [hH]
  by_cases hw : w = 0
  · subst hw
    rw [indicatorVA_apply_mem (mem_singleton 0)]
    refine le_antisymm (iInf_le_of_le ⟨0, by simp⟩ le_rfl) (le_iInf fun b ↦ ?_)
    have hb : (b : ℝ) = 0 := by
      have := b.2
      simp only [mem_singleton_iff, Prod.mk_eq_zero] at this
      exact this.2
    rw [hb]
    exact le_rfl
  · rw [indicatorVA_apply_not_mem (by simpa using hw)]
    have : IsEmpty {a : ℝ // ((w, a) : E × ℝ) ∈ ({0} : Set (E × ℝ))} := ⟨fun b ↦ by
      have := b.2
      simp only [mem_singleton_iff, Prod.mk_eq_zero] at this
      exact hw this.1⟩
    exact iInf_of_empty _

/-- **Exercise 14.54(a) (horizon integrands)**: for a normal integrand `f`, the horizon functions
`h(t, ·) = f(t, ·)^∞` form a normal integrand (`epi h(t, ·) = (epi f(t, ·))^∞`, and `h(t, ·) = δ_{0}`
when `f(t, ·) ≡ ∞`). -/
theorem IsNormalIntegrand.horizonFunction {f : T → E → EReal} (hf : IsNormalIntegrand f) :
    IsNormalIntegrand (fun t ↦ RW.horizonFunction (f t)) := by
  obtain ⟨hHc, hHm⟩ := hf.2.horizonCone
  have hzero : epigraph (indicatorVA ({0} : Set E)) = ({0} : Set E) ×ˢ Ici (0 : ℝ) :=
    epigraph_indicatorVA _
  have hepi : ∀ t, epigraph (RW.horizonFunction (f t)) =
      if t ∈ svDom (epiMapping f) then RW.horizonCone (epiMapping f t)
      else ({0} : Set E) ×ˢ Ici (0 : ℝ) := by
    intro t
    split_ifs with h
    · exact epigraph_horizonFunction_eq_horizonCone_epigraph h
    · have hempty : epigraph (f t) = ∅ := not_nonempty_iff_eq_empty.1 h
      rw [horizonFunction_of_epigraph_empty hempty, hzero]
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [hepi t]
    split_ifs
    · exact hHc t
    · exact isClosed_singleton.prod isClosed_Ici
  · rw [show epiMapping (fun t ↦ RW.horizonFunction (f t)) = _ from funext hepi]
    convert SvMeasurable.ite hf.2.measurableSet_svDom hHm
      (svMeasurable_const (({0} : Set E) ×ˢ Ici (0 : ℝ))) using 2 with t

end Exercise1454

end RW
