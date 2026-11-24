/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Continuity properties of normal integrands

Theorem 14.42 and Corollary 14.43 (Scorza-Dragoni property) of Rockafellar–Wets, in the setting of
Theorem 14.10 (`LusinMeasurability`): a Borel set `T₀` of a finite-dimensional space `E`, `A = L(T)`
expressed through null-measurability for a measure `μ` finite on compact sets and inner regular by
compact sets (Lebesgue measure).  An integrand `f : T₀ × G → ℝ̄` is extended to `E × G` arbitrarily
(the conditions only involve `T₀`); it is a normal integrand for `L(T)` when its epigraphical
mapping is `L(T)`-measurable, and epi-continuity of `t ↦ f(t, ·)` relative to `T_ε` is continuity of
the epigraphical mapping relative to `T_ε`.
-/

import RockafellarWets.Chapter14.LusinMeasurability
import RockafellarWets.Chapter14.NormalIntegrands

open Set Filter Topology Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace RW

section Graphs

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- A closed graph over `K` gives outer semicontinuity relative to `K`. -/
theorem svOscOn_of_isClosed_svGraph_inter {S : E → Set F} {K : Set E}
    (h : IsClosed (svGraph S ∩ (K ×ˢ univ))) : SvOscOn S K := by
  intro x _
  rw [svOscWithinAt_iff]
  intro u hu
  have hnot : (x, u) ∉ svGraph S ∩ (K ×ˢ univ) := fun h' ↦ hu h'.1
  obtain ⟨V, hV, W, hW, hsub⟩ := mem_nhds_prod_iff.1 (h.isOpen_compl.mem_nhds hnot)
  refine ⟨W, hW, V, hV, eq_empty_iff_forall_notMem.2 ?_⟩
  rintro y ⟨⟨hyK, hyV⟩, v, hvS, hvW⟩
  exact hsub (mk_mem_prod hyV hvW) ⟨hvS, hyK, mem_univ _⟩

variable {G : Type*} [TopologicalSpace G]

/-- The graph of the epigraphical mapping over a closed `K` is closed exactly when the integrand is
lsc relative to `K × G`. -/
theorem isClosed_svGraph_epiMapping_inter_iff [MeasurableSpace E] {f : E → G → EReal}
    {K : Set E} (hK : IsClosed K) :
    IsClosed (svGraph (epiMapping f) ∩ (K ×ˢ univ)) ↔
      LowerSemicontinuousOn (Function.uncurry f) (K ×ˢ univ) := by
  set Γ := svGraph (epiMapping f) ∩ (K ×ˢ (univ : Set (G × ℝ)))
  have hmemΓ : ∀ (t : E) (x : G) (a : ℝ), (t, (x, a)) ∈ Γ ↔ t ∈ K ∧ f t x ≤ (a : EReal) := by
    intro t x a
    simp only [Γ, mem_inter_iff, mem_svGraph, mem_prod, mem_univ, and_true, epiMapping,
      mem_epigraph_iff]
    exact and_comm
  constructor
  · intro hΓ
    rw [lowerSemicontinuousOn_iff_preimage_Iic]
    have hreal : ∀ r : ℝ, IsClosed {p : E × G | (p.1, (p.2, r)) ∈ Γ} :=
      fun r ↦ hΓ.preimage (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
    have hset : ∀ r : ℝ, (K ×ˢ (univ : Set G)) ∩ Function.uncurry f ⁻¹' Iic (r : EReal) =
        (K ×ˢ univ) ∩ {p : E × G | (p.1, (p.2, r)) ∈ Γ} := by
      intro r
      ext ⟨t, x⟩
      simp only [mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage, mem_Iic,
        Function.uncurry_apply_pair, mem_setOf_eq, hmemΓ]
      tauto
    intro b
    induction b using EReal.rec with
    | bot =>
      refine ⟨⋂ n : ℕ, {p : E × G | (p.1, (p.2, -(n : ℝ))) ∈ Γ},
        isClosed_iInter fun n ↦ hreal _, ?_⟩
      ext ⟨t, x⟩
      simp only [mem_inter_iff, mem_prod, mem_univ, and_true, mem_preimage, mem_Iic,
        Function.uncurry_apply_pair, mem_iInter, mem_setOf_eq, hmemΓ, le_bot_iff]
      constructor
      · rintro ⟨htK, hf⟩
        exact ⟨htK, fun n ↦ ⟨htK, by rw [hf]; exact bot_le⟩⟩
      · rintro ⟨htK, hf⟩
        refine ⟨htK, ?_⟩
        induction h : f t x using EReal.rec with
        | bot => rfl
        | top =>
          have := (hf 0).2
          rw [h] at this
          exact absurd this (by simp)
        | coe a =>
          obtain ⟨n, hn⟩ := exists_nat_gt (-a)
          have := (hf n).2
          rw [h, EReal.coe_le_coe_iff] at this
          linarith
    | top => exact ⟨univ, isClosed_univ, by simp⟩
    | coe r => exact ⟨_, hreal r, hset r⟩
  · intro hf
    have hC := (lowerSemicontinuousOn_iff_isClosed_epigraph (hK.prod isClosed_univ)).1 hf
    have : Γ = (fun q : E × (G × ℝ) ↦ ((q.1, q.2.1), ((q.2.2 : ℝ) : EReal))) ⁻¹'
        {p : (E × G) × EReal | p.1 ∈ K ×ˢ (univ : Set G) ∧ Function.uncurry f p.1 ≤ p.2} := by
      ext ⟨t, x, a⟩
      simp only [mem_preimage, mem_setOf_eq, mem_prod, mem_univ, and_true,
        Function.uncurry_apply_pair, hmemΓ]
    rw [this]
    exact hC.preimage ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_coe_real_ereal.comp (continuous_snd.comp continuous_snd)))

/-- For closed `K`, the epigraphical mapping is osc relative to `K` exactly when `f` is lsc relative
to `K × G`. -/
theorem svOscOn_epiMapping_iff [MeasurableSpace E] {f : E → G → EReal} {K : Set E}
    (hK : IsClosed K) :
    SvOscOn (epiMapping f) K ↔ LowerSemicontinuousOn (Function.uncurry f) (K ×ˢ univ) := by
  rw [← isClosed_svGraph_epiMapping_inter_iff hK]
  exact ⟨fun h ↦ h.isClosed_svGraph_inter hK, svOscOn_of_isClosed_svGraph_inter⟩

end Graphs

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]

section Theorem1442

/-- **Theorem 14.42 (continuity properties of normal integrands).** For `f : T₀ × G → ℝ̄` with
`f(t, ·)` lsc, each of the following is equivalent to `f` being an `L(T)`-normal integrand:
(a) for every `ε > 0` there is a closed `T_ε ⊆ T₀`, `μ(T₀ \ T_ε) < ε`, relative to which
`t ↦ f(t, ·)` is epi-continuous; (b) the same with `f` lsc relative to `T_ε × G`; (c) `f(t, ·) = g(t, ·)`
on a measurable `T' ⊆ T₀` of full measure for a Borel `g` with `g(t, ·)` lsc.  When `μ(T₀) < ∞`, the
sets `T_ε` can be taken compact. -/
theorem continuity_properties_of_normal_integrands (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] {T₀ : Set E} (hT₀ : MeasurableSet T₀) {f : E → G → EReal}
    (hf : ∀ t, LowerSemicontinuous (f t)) :
    List.TFAE [SvNullMeasurableOn μ T₀ (epiMapping f),
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ K ⊆ T₀, IsClosed K ∧ μ (T₀ \ K) < ε ∧
        SvContinuousOn (epiMapping f) K,
      ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ K ⊆ T₀, IsClosed K ∧ μ (T₀ \ K) < ε ∧
        LowerSemicontinuousOn (Function.uncurry f) (K ×ˢ univ),
      ∃ g : E → G → EReal, Measurable (Function.uncurry g) ∧ (∀ t, LowerSemicontinuous (g t)) ∧
        ∃ T' ⊆ T₀, NullMeasurableSet T' μ ∧ μ (T₀ \ T') = 0 ∧ ∀ t ∈ T', f t = g t] ∧
    (μ T₀ ≠ ∞ → SvNullMeasurableOn μ T₀ (epiMapping f) → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ K ⊆ T₀, IsCompact K ∧ μ (T₀ \ K) < ε ∧ SvContinuousOn (epiMapping f) K ∧
        LowerSemicontinuousOn (Function.uncurry f) (K ×ˢ univ)) := by
  have hSc : ∀ t, IsClosed (epiMapping f t) := fun t ↦
    (lsc_iff_epigraph_closed_ereal _).1 (hf t)
  obtain ⟨hT, hcpt⟩ := measurability_versus_continuity μ hT₀ hSc
  have h12 := hT.out 0 1
  have h13 := hT.out 0 2
  have h14 := hT.out 0 3
  refine ⟨?_, fun hfin hm ε hε ↦ ?_⟩
  swap
  · obtain ⟨K, hKT, hKc, hKμ, hK, hKo⟩ := hcpt hfin hm ε hε
    exact ⟨K, hKT, hKc, hKμ, hK, (svOscOn_epiMapping_iff hKc.isClosed).1 hKo⟩
  tfae_have 1 ↔ 2 := h12
  tfae_have 1 ↔ 3 := by
    rw [h13]
    refine forall₂_congr fun ε _ ↦ exists_congr fun K ↦ ?_
    constructor
    · rintro ⟨hKT, hKc, hKμ, hK⟩
      exact ⟨hKT, hKc, hKμ, (svOscOn_epiMapping_iff hKc).1 hK⟩
    · rintro ⟨hKT, hKc, hKμ, hK⟩
      exact ⟨hKT, hKc, hKμ, (svOscOn_epiMapping_iff hKc).2 hK⟩
  tfae_have 3 → 4 := by
    intro h
    choose K hKT hKc hKμ hK using fun n : ℕ ↦ h ((n : ℝ≥0∞) + 1)⁻¹ (by simp)
    classical
    set T' := ⋃ n, K n
    refine ⟨fun t x ↦ if t ∈ T' then f t x else ⊤, ?_, fun t ↦ ?_, T', iUnion_subset hKT,
      (MeasurableSet.iUnion fun n ↦ (hKc n).measurableSet).nullMeasurableSet, ?_,
      fun t ht ↦ funext fun x ↦ (if_pos ht).symm⟩
    · refine measurable_ereal_of_le_coe fun α ↦ ?_
      have heq : {p : E × G | Function.uncurry (fun t x ↦ if t ∈ T' then f t x else ⊤) p ≤ α} =
          ⋃ n, (K n ×ˢ univ) ∩ Function.uncurry f ⁻¹' Iic (α : EReal) := by
        ext ⟨t, x⟩
        simp only [mem_setOf_eq, Function.uncurry_apply_pair, mem_iUnion, mem_inter_iff,
          mem_prod, mem_univ, and_true, mem_preimage, mem_Iic]
        constructor
        · intro hp
          by_cases ht : t ∈ T'
          · rw [if_pos ht] at hp
            obtain ⟨n, hn⟩ := mem_iUnion.1 ht
            exact ⟨n, hn, hp⟩
          · rw [if_neg ht] at hp
            exact absurd hp (by simp)
        · rintro ⟨n, hn, hp⟩
          rw [if_pos (mem_iUnion.2 ⟨n, hn⟩)]
          exact hp
      rw [heq]
      refine MeasurableSet.iUnion fun n ↦ ?_
      obtain ⟨v, hv, hveq⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 (hK n) (α : EReal)
      rw [hveq]
      exact ((hKc n).prod isClosed_univ).measurableSet.inter hv.measurableSet
    · by_cases ht : t ∈ T'
      · simp only [ht, if_true]
        exact hf t
      · simp only [ht, if_false]
        exact lowerSemicontinuous_const
    · refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun n ↦ ?_)
        (zero_le _)
      calc μ (T₀ \ T') ≤ μ (T₀ \ K n) := measure_mono (diff_subset_diff_right
            (subset_iUnion K n))
        _ ≤ ((n : ℝ≥0∞) + 1)⁻¹ := (hKμ n).le
        _ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
  tfae_have 4 → 1 := by
    rintro ⟨g, hgm, hgl, T', hT'T, hT', hT'μ, hfg⟩
    refine h14.2 ⟨epiMapping g, fun t ↦ (lsc_iff_epigraph_closed_ereal _).1 (hgl t), ?_, T',
      hT'T, hT', hT'μ, fun t ht ↦ by simp only [epiMapping, hfg t ht]⟩
    have : svGraph (epiMapping g) ∩ (T₀ ×ˢ univ) =
        {q : E × (G × ℝ) | Function.uncurry g (q.1, q.2.1) ≤ ((q.2.2 : ℝ) : EReal)} ∩
          (T₀ ×ˢ univ) := by
      ext ⟨t, x, a⟩
      simp only [mem_inter_iff, mem_svGraph, epiMapping, mem_epigraph_iff, mem_setOf_eq,
        Function.uncurry_apply_pair]
    rw [this]
    exact (measurableSet_le (hgm.comp (measurable_fst.prodMk measurable_snd.fst))
      (measurable_coe_real_ereal.comp measurable_snd.snd)).inter
      (hT₀.prod MeasurableSet.univ)
  tfae_finish

end Theorem1442

section Corollary1443

/-- **Corollary 14.43 (Scorza-Dragoni property).** For a Carathéodory integrand `f : T₀ × G → ℝ`
(`L(T)`-measurable in `t`, continuous in `x`) and any `ε > 0` there is a closed `T_ε ⊆ T₀` with
`μ(T₀ \ T_ε) < ε` such that `f` is continuous relative to `T_ε × G`. -/
theorem scorza_dragoni_property (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] {T₀ : Set E} (hT₀ : MeasurableSet T₀) {f : E → G → ℝ}
    (hcont : ∀ t, Continuous (f t))
    (hmeas : ∀ x : G, ∀ B : Set ℝ, MeasurableSet B →
      NullMeasurableSet (T₀ ∩ (fun t ↦ f t x) ⁻¹' B) μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ T₀, IsClosed K ∧ μ (T₀ \ K) < ε ∧ ContinuousOn (Function.uncurry f) (K ×ˢ univ) := by
  -- both `f` and `-f`, as extended-real integrands, are `L(T)`-normal
  have hnormal : ∀ φ : E → G → ℝ, (∀ t, Continuous (φ t)) →
      (∀ x : G, ∀ B : Set ℝ, MeasurableSet B →
        NullMeasurableSet (T₀ ∩ (fun t ↦ φ t x) ⁻¹' B) μ) →
      SvNullMeasurableOn μ T₀ (epiMapping fun t x ↦ ((φ t x : ℝ) : EReal)) := by
    intro φ hφc hφm O hO
    set D := TopologicalSpace.denseSeq G
    have hD := TopologicalSpace.denseRange_denseSeq G
    have heq : T₀ ∩ svPreimage (epiMapping fun t x ↦ ((φ t x : ℝ) : EReal)) O =
        ⋃ p : ℕ × ℚ, ⋃ (_ : (D p.1, ((p.2 : ℚ) : ℝ)) ∈ O),
          T₀ ∩ (fun t ↦ φ t (D p.1)) ⁻¹' Iio (p.2 : ℝ) := by
      ext t
      simp only [mem_inter_iff, svPreimage, mem_setOf_eq, epiMapping, mem_iUnion, mem_preimage,
        mem_Iio, exists_prop]
      constructor
      · rintro ⟨htT, ⟨x, a⟩, hxa, hO'⟩
        rw [mem_epigraph_iff, EReal.coe_le_coe_iff] at hxa
        obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO _ hO'
        obtain ⟨η, hη, hηφ⟩ := Metric.continuous_iff.1 (hφc t) x (δ / 2) (by positivity)
        obtain ⟨i, hi⟩ := hD.exists_dist_lt x (lt_min hη hδ : 0 < min η δ)
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show a + δ / 2 < a + δ by linarith)
        refine ⟨(i, q), hball ?_, htT, ?_⟩
        · rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq]
          refine ⟨by rw [dist_comm]; exact hi.trans_le (min_le_right _ _), ?_⟩
          rw [abs_lt]
          constructor <;> linarith
        · have h1 := hηφ (D i) (by rw [dist_comm]; exact hi.trans_le (min_le_left _ _))
          rw [Real.dist_eq, abs_lt] at h1
          linarith
      · rintro ⟨p, hpO, htT, hlt⟩
        refine ⟨htT, (D p.1, (p.2 : ℝ)), ?_, hpO⟩
        rw [mem_epigraph_iff, EReal.coe_le_coe_iff]
        exact hlt.le
    rw [heq]
    exact NullMeasurableSet.iUnion fun p ↦ NullMeasurableSet.iUnion fun _ ↦
      hφm _ _ measurableSet_Iio
  have hf1 := hnormal f hcont hmeas
  have hf2 := hnormal (fun t x ↦ -f t x) (fun t ↦ (hcont t).neg) fun x B hB ↦ by
    have : (fun t ↦ -f t x) ⁻¹' B = (fun t ↦ f t x) ⁻¹' ((fun y : ℝ ↦ -y) ⁻¹' B) := rfl
    rw [this]
    exact hmeas x _ (measurable_neg hB)
  have hlsc : ∀ φ : E → G → ℝ, (∀ t, Continuous (φ t)) →
      ∀ t, LowerSemicontinuous fun x ↦ ((φ t x : ℝ) : EReal) := fun φ hφ t ↦
    (continuous_coe_real_ereal.comp (hφ t)).lowerSemicontinuous
  have hb1 := ((continuity_properties_of_normal_integrands μ hT₀ (hlsc f hcont)).1.out 0 2).1 hf1
  have hb2 := ((continuity_properties_of_normal_integrands μ hT₀
    (hlsc (fun t x ↦ -f t x) fun t ↦ (hcont t).neg)).1.out 0 2).1 hf2
  have hε2 : ε / 2 ≠ 0 := by simp [hε]
  obtain ⟨K₁, hK₁T, hK₁c, hK₁μ, hK₁⟩ := hb1 _ hε2
  obtain ⟨K₂, hK₂T, hK₂c, hK₂μ, hK₂⟩ := hb2 _ hε2
  refine ⟨K₁ ∩ K₂, inter_subset_left.trans hK₁T, hK₁c.inter hK₂c, ?_, ?_⟩
  · calc μ (T₀ \ (K₁ ∩ K₂)) ≤ μ (T₀ \ K₁) + μ (T₀ \ K₂) := by
          rw [diff_inter]
          exact measure_union_le _ _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hK₁μ hK₂μ
      _ = ε := ENNReal.add_halves ε
  · rw [continuousOn_iff_lower_upperSemicontinuousOn]
    refine ⟨fun p hp y hy ↦ ?_, fun p hp y hy ↦ ?_⟩
    · have h := (hK₁.mono (prod_mono inter_subset_left subset_rfl)) p hp (y : EReal)
        (EReal.coe_lt_coe_iff.2 hy)
      exact h.mono fun q hq ↦ EReal.coe_lt_coe_iff.1 hq
    · have hy' : f p.1 p.2 < y := hy
      have hlt : -y < -f p.1 p.2 := by linarith
      have h := (hK₂.mono (prod_mono inter_subset_right subset_rfl)) p hp ((-y : ℝ) : EReal)
        (EReal.coe_lt_coe_iff.2 hlt)
      refine h.mono fun q hq ↦ ?_
      have hq' : -y < -f q.1 q.2 := EReal.coe_lt_coe_iff.1 hq
      show f q.1 q.2 < y
      linarith

end Corollary1443

end RW
