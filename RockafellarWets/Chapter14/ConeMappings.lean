/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Tangent and normal cone mappings

Theorem 14.26 of Rockafellar–Wets.  The graph of `N_{S(t)}` is the closure of the union of the
sets `{(x, v) | x ∈ P_{S(t)}(x + v/(ν+1))}` (proximal normals, Exercise 6.18(a)); normal cones
along a measurable selection are slices of it (14.14); tangent cones are outer limits of
rational blow-ups `q⁻¹(S(t) - x(t))`; the regular cones follow by polarity (6.28).
-/

import RockafellarWets.Chapter14.HullsAndPolars
import RockafellarWets.Chapter14.MeasurableLimits
import RockafellarWets.Chapter6.NormalApproximation
import RockafellarWets.Chapter6.TangentNormalPolarity

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace RW

section Projections

variable {E : Type*} [NormedAddCommGroup E]

/-- Nearest points stay nearest along the segment towards the projected point. -/
theorem mem_projMapping_of_le {C : Set E} {x v : E} {τ τ' : ℝ} (hτ' : 0 ≤ τ') (hle : τ' ≤ τ)
    [Module ℝ E] [NormSMulClass ℝ E] (h : x ∈ projMapping C (x + τ • v)) :
    x ∈ projMapping C (x + τ' • v) := by
  refine ⟨h.1, fun c hc ↦ ?_⟩
  have h1 := h.2 c hc
  simp only [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs] at h1 ⊢
  have hτ : 0 ≤ τ := hτ'.trans hle
  rw [abs_of_nonneg hτ] at h1
  rw [abs_of_nonneg hτ']
  calc τ' * ‖v‖ = τ * ‖v‖ - (τ - τ') * ‖v‖ := by ring
    _ ≤ ‖c - (x + τ • v)‖ - ‖(x + τ • v) - (x + τ' • v)‖ := by
        gcongr
        · rw [show (x + τ • v) - (x + τ' • v) = (τ - τ') • v by
            rw [add_sub_add_left_eq_sub, sub_smul], norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (by linarith)]
    _ ≤ ‖c - (x + τ' • v)‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub c (x + τ' • v) (x + τ • v)
        have h2 := norm_sub_rev (x + τ • v) (x + τ' • v)
        linarith

end Projections

section Theorem1426

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem svGraph_proximalNormalCone_eq_iUnion (C : Set E) :
    svGraph (proximalNormalCone C) = ⋃ n : ℕ,
      {p : E × E | (p.1 + (1 / ((n : ℝ) + 1)) • p.2, p.1) ∈ svGraph (projMapping C)} := by
  ext ⟨x, v⟩
  simp only [mem_svGraph, mem_proximalNormalCone, mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hτ
    exact ⟨n, mem_projMapping_of_le (by positivity) hn.le hx⟩
  · rintro ⟨n, hn⟩
    exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- For closed `C`, `gph N_C` is the closure of the graph of the proximal normal cone
(Exercise 6.18(a)). -/
theorem svGraph_normalCone_eq_closure {C : Set E} (hC : IsClosed C) :
    svGraph (normalCone C) = _root_.closure (svGraph (proximalNormalCone C)) := by
  apply Subset.antisymm
  · rintro ⟨x, v⟩ hv
    obtain ⟨xs, vs, hxs, hvs, hxt, hvt⟩ :=
      exists_seq_mem_proximalNormalCone_tendsto_of_mem_normalCone hC hv
    exact mem_closure_of_tendsto (hxt.prodMk_nhds hvt) (Eventually.of_forall fun n ↦ hvs n)
  · intro p hp
    obtain ⟨q, hq, hqt⟩ := mem_closure_iff_seq_limit.1 hp
    have hxs : ∀ n, (q n).1 ∈ C := fun n ↦ (hq n).choose_spec.2.1
    refine ⟨hC.mem_of_tendsto (hqt.fst_nhds) (Eventually.of_forall hxs), fun n ↦ (q n).1,
      fun n ↦ (q n).2, hxs, hqt.fst_nhds, fun n ↦ proximalNormalCone_subset_regularNormalCone (hq n),
      hqt.snd_nhds⟩

/-- The graph of the normal cone mapping of a closed-valued measurable `S` is closed-valued
and measurable (Theorem 14.26, last assertion). -/
theorem svMeasurable_svGraph_normalCone {S : T → Set E} (hS : SvMeasurable S)
    (hSc : ∀ t, IsClosed (S t)) :
    (∀ t, IsClosed (svGraph (normalCone (S t)))) ∧
      SvMeasurable (fun t ↦ svGraph (normalCone (S t))) := by
  obtain ⟨⟨hPc, hPm⟩, -⟩ := projection_mappings_measurable hS hSc
  have hGn : ∀ n : ℕ, SvMeasurable (fun t ↦ {p : E × E |
      (p.1 + (1 / ((n : ℝ) + 1)) • p.2, p.1) ∈ svGraph (projMapping (S t))}) := by
    intro n
    set Φ : T → E × E → E × E := fun _ p ↦ (p.1 + (1 / ((n : ℝ) + 1)) • p.2, p.1)
    have hΦ : IsCaratheodory Φ := ⟨fun _ ↦ measurable_const,
      fun _ ↦ (continuous_fst.add (continuous_snd.const_smul _)).prodMk continuous_fst⟩
    exact (hΦ.svMeasurable_preimage hPm hPc).2
  have heq : (fun t ↦ svGraph (normalCone (S t))) = fun t ↦ _root_.closure (⋃ n : ℕ,
      {p : E × E | (p.1 + (1 / ((n : ℝ) + 1)) • p.2, p.1) ∈ svGraph (projMapping (S t))}) :=
    funext fun t ↦ by rw [svGraph_normalCone_eq_closure (hSc t), svGraph_proximalNormalCone_eq_iUnion]
  refine ⟨fun t ↦ by rw [svGraph_normalCone_eq_closure (hSc t)]; exact isClosed_closure, ?_⟩
  rw [heq]
  exact (SvMeasurable.iUnion hGn).closure

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The tangent cone as an outer limit of rational blow-ups. -/
theorem tangentCone_eq_iInter_closure_rat_blowUp (C : Set E) (x : E) :
    tangentCone C x = ⋂ m : ℕ, _root_.closure (⋃ q : ℚ, ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)),
      (fun y ↦ (q : ℝ)⁻¹ • (y - x)) '' C) := by
  apply Subset.antisymm
  · rintro w ⟨xs, τs, hxs, hxt, hτpos, hτt, hwt⟩
    refine mem_iInter.2 fun m ↦ ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hev1 : ∀ᶠ n in atTop, τs n < 1 / ((m : ℝ) + 1) :=
      hτt.eventually (gt_mem_nhds (by positivity))
    have hev2 : ∀ᶠ n in atTop, dist ((τs n)⁻¹ • (xs n - x)) w < ε / 2 :=
      (Metric.tendsto_nhds.1 hwt) (ε / 2) (half_pos hε)
    obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
    -- approximate `τs n` by a rational `q`
    set y := xs n - x
    have hcont : ContinuousAt (fun s : ℝ ↦ s⁻¹ • y) (τs n) :=
      (continuousAt_inv₀ (hτpos n).ne').smul continuousAt_const
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (half_pos hε)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max (τs n - δ) 0 < τs n from
      max_lt (by linarith) (hτpos n))
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_right _ _) hq1
    have hqd : dist (q : ℝ) (τs n) < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_left (τs n - δ) 0]
    refine ⟨(q : ℝ)⁻¹ • y, mem_iUnion₂.2 ⟨q, ⟨by exact_mod_cast hq0, by linarith⟩, xs n, hxs n,
      rfl⟩, ?_⟩
    have h1 := hδε hqd
    rw [dist_comm]
    calc dist ((q : ℝ)⁻¹ • y) w ≤ dist ((q : ℝ)⁻¹ • y) ((τs n)⁻¹ • y) + dist ((τs n)⁻¹ • y) w :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 hn2
      _ = ε := by ring
  · intro w hw
    have hpick : ∀ m : ℕ, ∃ q : ℚ, ∃ y ∈ C, 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1) ∧
        dist ((q : ℝ)⁻¹ • (y - x)) w < 1 / ((m : ℝ) + 1) := by
      intro m
      have := mem_iInter.1 hw m
      rw [Metric.mem_closure_iff] at this
      obtain ⟨z, hz, hzw⟩ := this (1 / ((m : ℝ) + 1)) (by positivity)
      obtain ⟨q, ⟨hq0, hq1⟩, y, hy, rfl⟩ := mem_iUnion₂.1 hz
      exact ⟨q, y, hy, hq0, hq1, by rw [dist_comm]; exact hzw⟩
    choose q y hy hq0 hq1 hdist using hpick
    have hqt : Tendsto (fun m ↦ (q m : ℝ)) atTop (𝓝 0) :=
      squeeze_zero (fun m ↦ (by exact_mod_cast (hq0 m).le)) (fun m ↦ (hq1 m).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hwt : Tendsto (fun m ↦ (q m : ℝ)⁻¹ • (y m - x)) atTop (𝓝 w) :=
      tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) (fun m ↦ (hdist m).le)
        tendsto_one_div_add_atTop_nhds_zero_nat)
    refine mem_tangentCone_of_forall hy (fun m ↦ by exact_mod_cast hq0 m) hqt hwt

/-- **Theorem 14.26 (tangent and normal cone mappings)**: for a closed-valued measurable `S` and a
measurable selection `x(t) ∈ S(t)`, the mappings `t ↦ T_{S(t)}(x(t))`, `T̂_{S(t)}(x(t))`,
`N_{S(t)}(x(t))`, `N̂_{S(t)}(x(t))` and `t ↦ gph N_{S(t)}` are closed-valued and measurable. -/
theorem tangent_and_normal_cone_mappings {S : T → Set E} (hS : SvMeasurable S)
    (hSc : ∀ t, IsClosed (S t)) {x : T → E} (hx : Measurable x) (hxS : ∀ t, x t ∈ S t) :
    ((∀ t, IsClosed (tangentCone (S t) (x t))) ∧
        SvMeasurable (fun t ↦ tangentCone (S t) (x t))) ∧
      ((∀ t, IsClosed (regularTangentCone (S t) (x t))) ∧
        SvMeasurable (fun t ↦ regularTangentCone (S t) (x t))) ∧
      ((∀ t, IsClosed (normalCone (S t) (x t))) ∧
        SvMeasurable (fun t ↦ normalCone (S t) (x t))) ∧
      ((∀ t, IsClosed (regularNormalCone (S t) (x t))) ∧
        SvMeasurable (fun t ↦ regularNormalCone (S t) (x t))) ∧
      ((∀ t, IsClosed (svGraph (normalCone (S t)))) ∧
        SvMeasurable (fun t ↦ svGraph (normalCone (S t)))) := by
  obtain ⟨hGc, hGm⟩ := svMeasurable_svGraph_normalCone hS hSc
  -- tangent cones
  have hT : (∀ t, IsClosed (tangentCone (S t) (x t))) ∧
      SvMeasurable (fun t ↦ tangentCone (S t) (x t)) := by
    have hblow : ∀ q : ℚ, SvMeasurable (fun t ↦ (fun y ↦ (q : ℝ)⁻¹ • (y - x t)) '' S t) := by
      intro q
      have hΦ : IsCaratheodory (fun t (y : E) ↦ (q : ℝ)⁻¹ • (y - x t)) :=
        ⟨fun y ↦ (measurable_const.sub hx).const_smul _,
          fun t ↦ (continuous_id.sub continuous_const).const_smul _⟩
      exact hΦ.svMeasurable_image hS hSc
    have heq : (fun t ↦ tangentCone (S t) (x t)) = fun t ↦ ⋂ m : ℕ, _root_.closure (⋃ q : ℚ,
        ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)), (fun y ↦ (q : ℝ)⁻¹ • (y - x t)) '' S t) :=
      funext fun t ↦ tangentCone_eq_iInter_closure_rat_blowUp _ _
    refine ⟨fun t ↦ ?_, ?_⟩
    · rw [tangentCone_eq_iInter_closure_rat_blowUp]
      exact isClosed_iInter fun _ ↦ isClosed_closure
    · rw [heq]
      refine SvMeasurable.iInter (fun m ↦ (SvMeasurable.iUnion fun q ↦ ?_).closure)
        (fun _ _ ↦ isClosed_closure)
      by_cases hq : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)
      · have : (fun t ↦ ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)),
            (fun y ↦ (q : ℝ)⁻¹ • (y - x t)) '' S t) =
            fun t ↦ (fun y ↦ (q : ℝ)⁻¹ • (y - x t)) '' S t := funext fun t ↦ iSup_pos hq
        rw [this]
        exact hblow q
      · have : (fun t ↦ ⋃ (_ : 0 < q ∧ (q : ℝ) < 1 / ((m : ℝ) + 1)),
            (fun y ↦ (q : ℝ)⁻¹ • (y - x t)) '' S t) = fun _ ↦ ∅ := funext fun t ↦ iSup_neg hq
        rw [this]
        exact svMeasurable_const ∅
  -- normal cones
  have hosc : ∀ t, SvOsc (normalCone (S t)) := fun t ↦ isClosed_svGraph_iff_svOsc.1 (hGc t)
  obtain ⟨hNc, hNm⟩ := composition_with_measurable_functions hosc hGm hx
  refine ⟨hT, ⟨fun t ↦ ?_, ?_⟩, ⟨hNc, hNm⟩, ⟨fun t ↦ ?_, ?_⟩, hGc, hGm⟩
  · rw [regularTangentCone_eq_polarCone_normalCone (hxS t) (RW.IsClosed.isLocallyClosedAt (hSc t) _)]
    exact isClosed_polarCone _
  · have heq : (fun t ↦ regularTangentCone (S t) (x t)) =
        fun t ↦ polarCone (normalCone (S t) (x t)) :=
      funext fun t ↦ regularTangentCone_eq_polarCone_normalCone (hxS t)
        (RW.IsClosed.isLocallyClosedAt (hSc t) _)
    rw [heq]
    exact hNm.polarCone
  · rw [regularNormalCone_eq_polarCone_tangentCone (hxS t)]
    exact isClosed_polarCone _
  · have heq : (fun t ↦ regularNormalCone (S t) (x t)) =
        fun t ↦ polarCone (tangentCone (S t) (x t)) :=
      funext fun t ↦ regularNormalCone_eq_polarCone_tangentCone (hxS t)
    rw [heq]
    exact hT.2.polarCone

end Theorem1426

end RW
