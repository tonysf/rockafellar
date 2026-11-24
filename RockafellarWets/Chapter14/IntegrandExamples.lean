/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Examples of normal integrands, level sets and optimal values

Examples 14.29–14.32, Proposition 14.33, Corollary 14.34 (joint measurability criterion; the
converse under completeness for an s-finite measure, as in the corrected Theorem 14.8),
Theorem 14.36 (measurability in constraint systems) and Theorem 14.37 (measurability of optimal
values and solutions) of Rockafellar–Wets.
-/

import RockafellarWets.Chapter14.NormalIntegrands

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Classical

noncomputable section

namespace RW

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Example1429

/-- **Example 14.29**: a Carathéodory integrand (finite, measurable in `t`, continuous in `x`) is
a normal integrand. -/
theorem IsCaratheodory.isNormalIntegrand {f : T → E → ℝ} (hf : IsCaratheodory f) :
    IsNormalIntegrand (fun t x ↦ (f t x : EReal)) := by
  set F : T → E × ℝ → ℝ := fun t p ↦ f t p.1 - p.2
  have hF : IsCaratheodory F := by
    refine ⟨fun p ↦ (hf.1 p.1).sub measurable_const, fun t ↦ ?_⟩
    exact ((hf.2 t).comp continuous_fst).sub continuous_snd
  have hepi : ∀ t, epigraph (fun x ↦ (f t x : EReal)) = {p : E × ℝ | F t p ∈ Iic 0} := by
    intro t
    ext ⟨x, α⟩
    simp only [epigraph, mem_setOf_eq, ge_iff_le, EReal.coe_le_coe_iff, mem_Iic, F, sub_nonpos]
  obtain ⟨hc, hm⟩ := hF.svMeasurable_preimage (S := fun _ ↦ Iic (0 : ℝ)) (svMeasurable_const _)
    (fun _ ↦ isClosed_Iic)
  refine ⟨fun t ↦ by rw [hepi t]; exact hc t, ?_⟩
  have : epiMapping (fun t x ↦ (f t x : EReal)) = fun t ↦ {p : E × ℝ | F t p ∈ Iic 0} :=
    funext hepi
  rw [this]
  exact hm

omit [MeasurableSpace T] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
theorem upperSemicontinuous_of_lowerSemicontinuous_neg {g : E → EReal}
    (h : LowerSemicontinuous fun x ↦ -g x) : UpperSemicontinuous g := by
  intro x y hy
  have := h x (-y) (EReal.neg_lt_neg_iff.2 hy)
  filter_upwards [this] with x' hx'
  exact EReal.neg_lt_neg_iff.1 hx'

/-- **Example 14.29 (Carathéodory integrands)**: `f` is (the extended-real embedding of) a
Carathéodory integrand if and only if both `f` and `-f` are proper normal integrands. -/
theorem caratheodory_integrands [Nonempty E] {f : T → E → EReal} :
    (∃ g : T → E → ℝ, IsCaratheodory g ∧ f = fun t x ↦ (g t x : EReal)) ↔
      IsNormalIntegrand f ∧ IsNormalIntegrand (fun t x ↦ -f t x) ∧ (∀ t, IsProper (f t)) ∧
        ∀ t, IsProper (fun x ↦ -f t x) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hng : IsCaratheodory fun t x ↦ -g t x :=
      ⟨fun x ↦ (hg.1 x).neg, fun t ↦ (hg.2 t).neg⟩
    refine ⟨hg.isNormalIntegrand, ?_, fun t ↦ ?_, fun t ↦ ?_⟩
    · have := hng.isNormalIntegrand
      simpa only [EReal.coe_neg] using this
    · obtain ⟨x⟩ := ‹Nonempty E›
      exact ⟨⟨x, EReal.coe_lt_top _⟩, fun x ↦ EReal.bot_lt_coe _⟩
    · obtain ⟨x⟩ := ‹Nonempty E›
      refine ⟨⟨x, ?_⟩, fun x ↦ ?_⟩
      · show -((g t x : ℝ) : EReal) < ⊤
        rw [← EReal.coe_neg]; exact EReal.coe_lt_top _
      · show -((g t x : ℝ) : EReal) > ⊥
        rw [← EReal.coe_neg]; exact EReal.bot_lt_coe _
  · rintro ⟨hf, hnf, hp, hnp⟩
    have hbot : ∀ t x, f t x ≠ ⊥ := fun t x ↦ ((hp t).2 x).ne'
    have htop : ∀ t x, f t x ≠ ⊤ := fun t x h ↦ by
      have : -f t x > ⊥ := (hnp t).2 x
      rw [h, EReal.neg_top] at this
      exact lt_irrefl _ this
    refine ⟨fun t x ↦ (f t x).toReal, ⟨fun x ↦ (hf.measurable_apply x).ereal_toReal,
      fun t ↦ ?_⟩, ?_⟩
    · have hcont : Continuous (f t) := continuous_iff_lower_upperSemicontinuous.2
        ⟨hf.lowerSemicontinuous t,
          upperSemicontinuous_of_lowerSemicontinuous_neg (hnf.lowerSemicontinuous t)⟩
      exact EReal.continuousOn_toReal.comp_continuous hcont fun x ↦ by
        simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨hbot t x, htop t x⟩
    · funext t x
      exact (EReal.coe_toReal (htop t x) (hbot t x)).symm

end Example1429

section Examples1430to1432

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Example 14.30 (autonomous integrands)**: `f(t, x) ≡ g(x)` with `g` lsc is normal. -/
theorem isNormalIntegrand_const {g : E → EReal} (hg : LowerSemicontinuous g) :
    IsNormalIntegrand (fun _ : T ↦ g) :=
  ⟨fun _ ↦ (lsc_iff_epigraph_closed_ereal g).1 hg, svMeasurable_const _⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Example 14.31 (joint lower semicontinuity)**: on a topological parameter space whose
σ-field contains the Borel sets (e.g. a Borel set `T ⊂ ℝᵈ`), a jointly lsc `f` is a normal
integrand. -/
theorem isNormalIntegrand_of_lowerSemicontinuous [TopologicalSpace T] [OpensMeasurableSpace T]
    {f : T → E → EReal} (hf : LowerSemicontinuous (Function.uncurry f)) :
    IsNormalIntegrand f := by
  have hclosed : IsClosed (svGraph (epiMapping f)) := by
    have hepi := (lsc_iff_epigraph_closed_ereal _).1 hf
    have : svGraph (epiMapping f) =
        (fun p : T × (E × ℝ) ↦ ((p.1, p.2.1), p.2.2)) ⁻¹' epigraph (Function.uncurry f) := by
      ext ⟨t, x, α⟩
      rfl
    rw [this]
    exact hepi.preimage ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd))
  have hosc : SvOsc (epiMapping f) := isClosed_svGraph_iff_svOsc.1 hclosed
  refine ⟨fun t ↦ ?_, hosc.svMeasurable⟩
  have : epigraph (f t) = (fun u ↦ (t, u)) ⁻¹' svGraph (epiMapping f) := rfl
  rw [this]
  exact hclosed.preimage (Continuous.prodMk_right t)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Example 14.32 (indicator integrands)**: `δ_C` is a normal integrand if and only if `C` is
closed-valued and measurable. -/
theorem isNormalIntegrand_indicatorVA_iff {C : T → Set E} :
    IsNormalIntegrand (fun t ↦ indicatorVA (C t)) ↔ (∀ t, IsClosed (C t)) ∧ SvMeasurable C := by
  have hepi : epiMapping (fun t ↦ indicatorVA (C t)) = fun t ↦ C t ×ˢ Ici (0 : ℝ) :=
    funext fun t ↦ epigraph_indicatorVA (C t)
  constructor
  · rintro ⟨hc, hm⟩
    refine ⟨fun t ↦ ?_, fun O hO ↦ ?_⟩
    · have h1 := hc t
      rw [epigraph_indicatorVA] at h1
      have : C t = (fun x ↦ ((x, 0) : E × ℝ)) ⁻¹' (C t ×ˢ Ici (0 : ℝ)) := by
        ext x
        simp
      rw [this]
      exact h1.preimage (Continuous.prodMk_left 0)
    · have : svPreimage C O = svPreimage (epiMapping fun t ↦ indicatorVA (C t)) (O ×ˢ univ) := by
        rw [hepi]
        ext t
        simp only [mem_svPreimage]
        constructor
        · rintro ⟨x, hx, hxO⟩
          exact ⟨(x, 0), ⟨hx, self_mem_Ici⟩, hxO, mem_univ _⟩
        · rintro ⟨⟨x, α⟩, ⟨hx, -⟩, hxO, -⟩
          exact ⟨x, hx, hxO⟩
      rw [this]
      exact hm _ (hO.prod isOpen_univ)
  · rintro ⟨hc, hm⟩
    refine ⟨fun t ↦ by rw [epigraph_indicatorVA]; exact (hc t).prod isClosed_Ici, ?_⟩
    rw [hepi]
    exact hm.prod (svMeasurable_const _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Example 14.32**, second part: for a normal integrand `f₀` and closed-valued measurable `C`,
the function `f = f₀` on `C(t)`, `∞` off `C(t)`, is a normal integrand with
`D_f(t) = D_{f₀}(t) ∩ C(t)`. -/
theorem IsNormalIntegrand.restrict {f₀ : T → E → EReal} (hf₀ : IsNormalIntegrand f₀)
    {C : T → Set E} (hC : SvMeasurable C) (hCc : ∀ t, IsClosed (C t)) :
    IsNormalIntegrand (fun t x ↦ if x ∈ C t then f₀ t x else ⊤) ∧
      ∀ t, domMapping (fun t x ↦ if x ∈ C t then f₀ t x else ⊤) t = domMapping f₀ t ∩ C t := by
  have hepi : ∀ t, epigraph (fun x ↦ if x ∈ C t then f₀ t x else ⊤) =
      epigraph (f₀ t) ∩ (C t ×ˢ univ) := by
    intro t
    ext ⟨x, α⟩
    by_cases hx : x ∈ C t <;> simp [epigraph, hx]
  refine ⟨⟨fun t ↦ by rw [hepi t]; exact (hf₀.1 t).inter ((hCc t).prod isClosed_univ), ?_⟩,
    fun t ↦ ?_⟩
  · have : epiMapping (fun t x ↦ if x ∈ C t then f₀ t x else ⊤) =
        fun t ↦ epiMapping f₀ t ∩ (C t ×ˢ univ) := funext hepi
    rw [this]
    exact hf₀.2.inter (hC.prod (svMeasurable_const _)) hf₀.1 fun t ↦ (hCc t).prod isClosed_univ
  · ext x
    by_cases hx : x ∈ C t <;> simp [domMapping, effectiveDomain, hx]

omit [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- **Example 14.32**, Carathéodory case: `D_f(t) = C(t)`. -/
theorem IsCaratheodory.restrict_domMapping {f₀ : T → E → ℝ} (C : T → Set E) (t : T) :
    domMapping (fun t x ↦ if x ∈ C t then (f₀ t x : EReal) else ⊤) t = C t := by
  ext x
  by_cases hx : x ∈ C t <;> simp [domMapping, effectiveDomain, hx]

end Examples1430to1432

section Proposition1433

/-- The mapping `t ↦ (-∞, α(t)]` of a measurable real function is closed-valued and
measurable. -/
theorem svMeasurable_Iic_of_measurable {α : T → ℝ} (hα : Measurable α) :
    SvMeasurable (fun t ↦ Iic (α t)) := by
  set Φ : T → ℝ → ℝ := fun t β ↦ β - α t
  have hΦ : IsCaratheodory Φ :=
    ⟨fun β ↦ measurable_const.sub hα, fun t ↦ continuous_id.sub continuous_const⟩
  have h := (hΦ.svMeasurable_preimage (S := fun _ ↦ Iic (0 : ℝ)) (svMeasurable_const _)
    (fun _ ↦ isClosed_Iic)).2
  have : (fun t ↦ {β | Φ t β ∈ Iic (0 : ℝ)}) = fun t ↦ Iic (α t) := by
    funext t
    ext β
    simp [Φ]
  rwa [this] at h

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Proposition 14.33**, second part: for a normal integrand and a measurable real `α(t)`,
the mapping `t ↦ {x | f(t, x) ≤ α(t)}` is closed-valued and measurable. -/
theorem IsNormalIntegrand.levelSet_measurable {f : T → E → EReal} (hf : IsNormalIntegrand f)
    {α : T → ℝ} (hα : Measurable α) :
    (∀ t, IsClosed {x | f t x ≤ α t}) ∧ SvMeasurable (fun t ↦ {x | f t x ≤ α t}) := by
  have hc : ∀ t, IsClosed {x | f t x ≤ α t} := fun t ↦
    (hf.lowerSemicontinuous t).isClosed_preimage _
  refine ⟨hc, svMeasurable_of_measurableSet_svPreimage_isCompact fun K hK ↦ ?_⟩
  have hR : SvMeasurable (fun t ↦ K ×ˢ Iic (α t)) :=
    (svMeasurable_const K).prod (svMeasurable_Iic_of_measurable hα)
  have hQ := hf.2.inter hR hf.1 (fun t ↦ hK.isClosed.prod isClosed_Iic)
  have : svPreimage (fun t ↦ {x | f t x ≤ α t}) K =
      svDom (fun t ↦ epiMapping f t ∩ (K ×ˢ Iic (α t))) := by
    ext t
    simp only [mem_svPreimage, mem_svDom]
    constructor
    · rintro ⟨x, hx, hxK⟩
      exact ⟨(x, α t), (show ((α t : ℝ) : EReal) ≥ f t x from hx), hxK, self_mem_Iic⟩
    · rintro ⟨⟨x, β⟩, hxβ, hxK, hβ⟩
      have hβ' : β ≤ α t := hβ
      exact ⟨x, (show f t x ≤ β from hxβ).trans (EReal.coe_le_coe_iff.2 hβ'), hxK⟩
  rw [this]
  exact hQ.measurableSet_svDom

omit [MeasurableSpace T] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- Closed real sublevel sets make an extended-real function lsc. -/
theorem lowerSemicontinuous_of_isClosed_levelSet {g : E → EReal}
    (h : ∀ α : ℝ, IsClosed {x | g x ≤ α}) : LowerSemicontinuous g := by
  refine lowerSemicontinuous_iff_isClosed_preimage.2 fun y ↦ ?_
  induction y with
  | bot =>
    have : g ⁻¹' Iic ⊥ = ⋂ n : ℕ, {x | g x ≤ ((-(n : ℝ) : ℝ) : EReal)} := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_iInter, mem_setOf_eq]
      constructor
      · intro hx n
        exact hx.trans bot_le
      · intro hx
        rw [ereal_eq_bot_of_forall_le_neg_nat hx]
    rw [this]
    exact isClosed_iInter fun n ↦ h _
  | coe a => exact h a
  | top =>
    have : g ⁻¹' Iic ⊤ = univ := by ext x; simp
    rw [this]
    exact isClosed_univ

omit [MeasurableSpace T] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- The epigraph of an lsc function is the closure of the union of the rational slabs
`lev_{≤q} g × [q, ∞)`. -/
theorem epigraph_eq_closure_iUnion_levelSet {g : E → EReal} (hg : LowerSemicontinuous g) :
    epigraph g = _root_.closure (⋃ q : ℚ, {x | g x ≤ (q : ℝ)} ×ˢ Ici ((q : ℝ))) := by
  apply Subset.antisymm
  · rintro ⟨x, β⟩ hxβ
    have hxβ' : g x ≤ β := hxβ
    have hq : ∀ n : ℕ, ∃ q : ℚ, β < q ∧ (q : ℝ) < β + 1 / ((n : ℝ) + 1) := fun n ↦
      exists_rat_btwn (by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity])
    choose q hq1 hq2 using hq
    have htend : Tendsto (fun n ↦ ((x, (q n : ℝ)) : E × ℝ)) atTop (𝓝 (x, β)) := by
      refine tendsto_const_nhds.prodMk_nhds ?_
      have h0 : Tendsto (fun n : ℕ ↦ β + 1 / ((n : ℝ) + 1)) atTop (𝓝 β) := by
        have := (tendsto_const_nhds (x := β)).add tendsto_one_div_add_atTop_nhds_zero_nat
        rwa [add_zero] at this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
        (fun n ↦ (hq1 n).le) (fun n ↦ (hq2 n).le)
    refine mem_closure_of_tendsto htend (Eventually.of_forall fun n ↦ ?_)
    refine mem_iUnion.2 ⟨q n, ?_, self_mem_Ici⟩
    exact hxβ'.trans (EReal.coe_le_coe_iff.2 (hq1 n).le)
  · refine closure_minimal ?_ ((lsc_iff_epigraph_closed_ereal g).1 hg)
    refine iUnion_subset fun q ↦ ?_
    rintro ⟨x, β⟩ ⟨hx, hβ⟩
    have hx' : g x ≤ ((q : ℝ) : EReal) := hx
    have hβ' : (q : ℝ) ≤ β := hβ
    exact (show g x ≤ β from hx'.trans (EReal.coe_le_coe_iff.2 hβ'))

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Proposition 14.33 (measurability of level-set mappings)**: `f` is a normal integrand if
and only if all level-set mappings `t ↦ lev_{≤α} f(t, ·)`, `α ∈ ℝ`, are closed-valued and
measurable; moreover `t ↦ {x | f(t, x) ≤ α(t)}` is closed-valued and measurable for every
measurable `α` (`IsNormalIntegrand.levelSet_measurable`). -/
theorem measurability_of_level_set_mappings {f : T → E → EReal} :
    IsNormalIntegrand f ↔ ∀ α : ℝ, (∀ t, IsClosed {x | f t x ≤ α}) ∧
      SvMeasurable (fun t ↦ {x | f t x ≤ α}) := by
  constructor
  · intro hf α
    exact hf.levelSet_measurable (α := fun _ ↦ α) measurable_const
  · intro h
    have hlsc : ∀ t, LowerSemicontinuous (f t) := fun t ↦
      lowerSemicontinuous_of_isClosed_levelSet fun α ↦ (h α).1 t
    refine ⟨fun t ↦ (lsc_iff_epigraph_closed_ereal _).1 (hlsc t), ?_⟩
    have heq : epiMapping f = fun t ↦
        _root_.closure (⋃ q : ℚ, {x | f t x ≤ (q : ℝ)} ×ˢ Ici ((q : ℝ))) :=
      funext fun t ↦ epigraph_eq_closure_iUnion_levelSet (hlsc t)
    rw [heq]
    exact (SvMeasurable.iUnion fun q : ℚ ↦ (h (q : ℝ)).2.prod (svMeasurable_const _)).closure

/-- **Corollary 14.34**, forward direction: a normal integrand is `A ⊗ B(E)`-measurable as a
function of `(t, x)` (and lsc in `x`). -/
theorem IsNormalIntegrand.measurable_uncurry {f : T → E → EReal} (hf : IsNormalIntegrand f) :
    Measurable (Function.uncurry f) := by
  refine measurable_ereal_of_le_coe fun α ↦ ?_
  have h := hf.levelSet_measurable (α := fun _ ↦ α) measurable_const
  have heq : {p : T × E | Function.uncurry f p ≤ α} = svGraph (fun t ↦ {x | f t x ≤ α}) := rfl
  rw [heq]
  exact h.2.measurableSet_svGraph h.1

/-- **Corollary 14.34**, converse (adapted, cf. Theorem 14.8): when the σ-field `A` is complete
for an s-finite (e.g. σ-finite) measure `μ`, an `A ⊗ B(E)`-measurable `f` with every `f(t, ·)` lsc
is a normal integrand. -/
theorem isNormalIntegrand_of_measurable_uncurry (μ : MeasureTheory.Measure T)
    [MeasureTheory.SFinite μ] [μ.IsComplete] {f : T → E → EReal}
    (hf : Measurable (Function.uncurry f)) (hlsc : ∀ t, LowerSemicontinuous (f t)) :
    IsNormalIntegrand f := by
  rw [measurability_of_level_set_mappings]
  intro α
  exact ⟨fun t ↦ (hlsc t).isClosed_preimage (α : EReal),
    svMeasurable_of_measurableSet_svGraph μ (hf measurableSet_Iic)⟩

/-- **Corollary 14.34 (joint measurability criterion)**, adapted: a normal integrand is
`A ⊗ B(E)`-measurable and lsc in `x`; conversely these properties characterize normal integrands
when `A` is complete for an s-finite (e.g. σ-finite) measure.  This covers the book's case
`T = ℝᵈ`, `A = L(ℝᵈ)` (`joint_measurability_criterion_lebesgue`).  On a standard Borel space no
measure is needed (`joint_measurability_criterion_standardBorel`). -/
theorem joint_measurability_criterion {f : T → E → EReal} :
    (IsNormalIntegrand f → Measurable (Function.uncurry f) ∧ ∀ t, LowerSemicontinuous (f t)) ∧
    ∀ (μ : MeasureTheory.Measure T) [MeasureTheory.SFinite μ] [μ.IsComplete],
      (IsNormalIntegrand f ↔
        Measurable (Function.uncurry f) ∧ ∀ t, LowerSemicontinuous (f t)) := by
  have hfwd : IsNormalIntegrand f →
      Measurable (Function.uncurry f) ∧ ∀ t, LowerSemicontinuous (f t) :=
    fun hf ↦ ⟨hf.measurable_uncurry, hf.lowerSemicontinuous⟩
  exact ⟨hfwd, fun μ _ _ ↦ ⟨hfwd, fun h ↦ isNormalIntegrand_of_measurable_uncurry μ h.1 h.2⟩⟩

end Proposition1433


section Theorem1436

/-- The equality constraint `t ↦ {x | g(t, x) = β(t)}` of a Carathéodory function is
closed-valued and measurable. -/
theorem IsCaratheodory.eqLevel_measurable {g : T → E → ℝ} (hg : IsCaratheodory g) {β : T → ℝ}
    (hβ : Measurable β) :
    (∀ t, IsClosed {x | g t x = β t}) ∧ SvMeasurable (fun t ↦ {x | g t x = β t}) := by
  set Φ : T → E → ℝ := fun t x ↦ g t x - β t
  have hΦ : IsCaratheodory Φ :=
    ⟨fun x ↦ (hg.1 x).sub hβ, fun t ↦ (hg.2 t).sub continuous_const⟩
  obtain ⟨hc, hm⟩ := hΦ.svMeasurable_preimage (S := fun _ ↦ ({0} : Set ℝ))
    (svMeasurable_const _) (fun _ ↦ isClosed_singleton)
  have heq : (fun t ↦ {x | Φ t x ∈ ({0} : Set ℝ)}) = fun t ↦ {x | g t x = β t} := by
    funext t
    ext x
    simp [Φ, sub_eq_zero]
  rw [heq] at hm
  refine ⟨fun t ↦ ?_, hm⟩
  have := hc t
  simp only [Φ, mem_singleton_iff, sub_eq_zero] at this
  exact this

/-- **Theorem 14.36 (measurability in constraint systems)**: the feasible set
`C(t) = {x ∈ X(t) | fᵢ(t, x) ≤ αᵢ(t) (i ∈ I₁), gⱼ(t, x) = βⱼ(t) (j ∈ I₂)}` with normal `fᵢ`,
Carathéodory `gⱼ`, countable `I₁`, `I₂` and measurable `αᵢ`, `βⱼ` is closed-valued and
measurable; `{t | C(t) ≠ ∅}` is measurable and admits a measurable selection of `C`. -/
theorem measurability_in_constraint_systems [Nonempty E] {I₁ I₂ : Type*} [Countable I₁]
    [Countable I₂] {X : T → Set E} (hX : SvMeasurable X) (hXc : ∀ t, IsClosed (X t))
    {f : I₁ → T → E → EReal} (hf : ∀ i, IsNormalIntegrand (f i))
    {g : I₂ → T → E → ℝ} (hg : ∀ j, IsCaratheodory (g j))
    {α : I₁ → T → ℝ} (hα : ∀ i, Measurable (α i)) {β : I₂ → T → ℝ} (hβ : ∀ j, Measurable (β j)) :
    (∀ t, IsClosed {x | x ∈ X t ∧ (∀ i, f i t x ≤ α i t) ∧ ∀ j, g j t x = β j t}) ∧
      SvMeasurable (fun t ↦ {x | x ∈ X t ∧ (∀ i, f i t x ≤ α i t) ∧ ∀ j, g j t x = β j t}) ∧
      MeasurableSet {t | ∃ x, x ∈ X t ∧ (∀ i, f i t x ≤ α i t) ∧ ∀ j, g j t x = β j t} ∧
      ∃ x : T → E, Measurable x ∧ ∀ t, (∃ y, y ∈ X t ∧ (∀ i, f i t y ≤ α i t) ∧
        ∀ j, g j t y = β j t) → x t ∈ X t ∧ (∀ i, f i t (x t) ≤ α i t) ∧
          ∀ j, g j t (x t) = β j t := by
  have hL1 := fun i ↦ (hf i).levelSet_measurable (hα i)
  have hL2 := fun j ↦ (hg j).eqLevel_measurable (hβ j)
  have hset : ∀ t, {x | x ∈ X t ∧ (∀ i, f i t x ≤ α i t) ∧ ∀ j, g j t x = β j t} =
      X t ∩ ((⋂ i, {x | f i t x ≤ α i t}) ∩ ⋂ j, {x | g j t x = β j t}) := by
    intro t
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
  have hc1 : ∀ t, IsClosed (⋂ i, {x | f i t x ≤ α i t}) := fun t ↦
    isClosed_iInter fun i ↦ (hL1 i).1 t
  have hc2 : ∀ t, IsClosed (⋂ j, {x | g j t x = β j t}) := fun t ↦
    isClosed_iInter fun j ↦ (hL2 j).1 t
  have hc : ∀ t, IsClosed {x | x ∈ X t ∧ (∀ i, f i t x ≤ α i t) ∧ ∀ j, g j t x = β j t} :=
    fun t ↦ by rw [hset t]; exact (hXc t).inter ((hc1 t).inter (hc2 t))
  have hm : SvMeasurable
      (fun t ↦ {x | x ∈ X t ∧ (∀ i, f i t x ≤ α i t) ∧ ∀ j, g j t x = β j t}) := by
    rw [funext hset]
    exact hX.inter ((SvMeasurable.iInter (fun i ↦ (hL1 i).2) fun i ↦ (hL1 i).1).inter
      (SvMeasurable.iInter (fun j ↦ (hL2 j).2) fun j ↦ (hL2 j).1) hc1 hc2) hXc
      (fun t ↦ (hc1 t).inter (hc2 t))
  refine ⟨hc, hm, hm.measurableSet_svDom, ?_⟩
  obtain ⟨x, hxm, hx⟩ := hm.exists_measurable_selection hc
  exact ⟨x, hxm, fun t hy ↦ hx t hy⟩

end Theorem1436


section Theorem1437

omit [MeasurableSpace E] [BorelSpace E] in
/-- Proposition 14.33 with an extended-real measurable level `α(t)` (needed for 14.37, where
`α = inf f(t, ·)` may be infinite). -/
theorem IsNormalIntegrand.levelSet_measurable_ereal {f : T → E → EReal}
    (hf : IsNormalIntegrand f) {α : T → EReal} (hα : Measurable α) :
    (∀ t, IsClosed {x | f t x ≤ α t}) ∧ SvMeasurable (fun t ↦ {x | f t x ≤ α t}) := by
  refine ⟨fun t ↦ (hf.lowerSemicontinuous t).isClosed_preimage _, ?_⟩
  have hbot : SvMeasurable (fun t ↦ ⋂ n : ℕ, {x | f t x ≤ ((-(n : ℝ) : ℝ) : EReal)}) :=
    SvMeasurable.iInter (fun n ↦ (hf.levelSet_measurable (α := fun _ ↦ -(n : ℝ))
      measurable_const).2) fun n ↦ (hf.levelSet_measurable (α := fun _ ↦ -(n : ℝ))
        measurable_const).1
  have hreal := (hf.levelSet_measurable (α := fun t ↦ (α t).toReal) hα.ereal_toReal).2
  have hAtop : MeasurableSet {t | α t = ⊤} := hα (measurableSet_singleton ⊤)
  have hAbot : MeasurableSet {t | α t = ⊥} := hα (measurableSet_singleton ⊥)
  have key := SvMeasurable.ite hAtop (svMeasurable_const (univ : Set E))
    (SvMeasurable.ite hAbot hbot hreal)
  convert key using 1
  funext t
  split_ifs with h1 h2
  · have h1' : α t = ⊤ := h1
    ext x
    simp [h1']
  · have h2' : α t = ⊥ := h2
    ext x
    simp only [mem_setOf_eq, h2', le_bot_iff, mem_iInter]
    constructor
    · intro hx n
      rw [hx]
      exact bot_le
    · intro hx
      exact ereal_eq_bot_of_forall_le_neg_nat hx
  · have htop : α t ≠ ⊤ := h1
    have hbot' : α t ≠ ⊥ := h2
    ext x
    simp only [mem_setOf_eq]
    rw [EReal.coe_toReal htop hbot']

omit [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem argmin_eq_ite (g : E → EReal) :
    argmin g = if (⨅ x, g x) < ⊤ then {x | g x ≤ ⨅ y, g y} else ∅ := by
  split_ifs with h
  · rw [argmin_eq_setOf_eq_iInf h]
    ext x
    simp only [mem_setOf_eq]
    exact ⟨fun hx ↦ hx.le, fun hx ↦ le_antisymm hx (iInf_le _ x)⟩
  · ext x
    simp only [mem_argmin_iff, mem_empty_iff_false, iff_false, not_and]
    exact fun _ ↦ h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The optimal value `t ↦ inf f(t, ·)` of a normal integrand is measurable. -/
theorem IsNormalIntegrand.measurable_iInf {f : T → E → EReal} (hf : IsNormalIntegrand f) :
    Measurable fun t ↦ ⨅ x, f t x := by
  refine measurable_ereal_of_lt_coe fun β ↦ ?_
  have : {t | ⨅ x, f t x < β} = svPreimage (epiMapping f) (univ ×ˢ Iio β) := by
    ext t
    simp only [mem_setOf_eq, mem_svPreimage]
    constructor
    · intro h
      obtain ⟨x, hx⟩ := iInf_lt_iff.1 h
      obtain ⟨r, hr1, hr2⟩ := EReal.exists_between_coe_real hx
      exact ⟨(x, r), (show (r : EReal) ≥ f t x from hr1.le), mem_univ _,
        EReal.coe_lt_coe_iff.1 hr2⟩
    · rintro ⟨⟨x, r⟩, hxr, -, hr⟩
      have hxr' : f t x ≤ r := hxr
      have hr' : r < β := hr
      exact lt_of_le_of_lt ((iInf_le _ x).trans hxr') (EReal.coe_lt_coe_iff.2 hr')
  rw [this]
  exact hf.2 _ (isOpen_univ.prod isOpen_Iio)

/-- **Theorem 14.37 (measurability of optimal values and solutions)**: for a normal integrand,
`p(t) = inf f(t, ·)` is measurable and `P(t) = argmin f(t, ·)` is closed-valued and measurable;
hence `{t | argmin f(t, ·) ≠ ∅}` is measurable and minimizers can be selected measurably. -/
theorem measurability_of_optimal_values_and_solutions [Nonempty E] {f : T → E → EReal}
    (hf : IsNormalIntegrand f) :
    Measurable (fun t ↦ ⨅ x, f t x) ∧ (∀ t, IsClosed (argmin (f t))) ∧
      SvMeasurable (fun t ↦ argmin (f t)) ∧ MeasurableSet {t | (argmin (f t)).Nonempty} ∧
      ∃ x : T → E, Measurable x ∧ ∀ t, (argmin (f t)).Nonempty → x t ∈ argmin (f t) := by
  have hp := hf.measurable_iInf
  obtain ⟨hLc, hLm⟩ := hf.levelSet_measurable_ereal hp
  have hc : ∀ t, IsClosed (argmin (f t)) := fun t ↦ by
    rw [argmin_eq_ite]
    split_ifs
    · exact hLc t
    · exact isClosed_empty
  have hm : SvMeasurable (fun t ↦ argmin (f t)) := by
    have key := SvMeasurable.ite (hp (measurableSet_Iio (a := (⊤ : EReal)))) hLm
      (svMeasurable_const (∅ : Set E))
    convert key using 1
    funext t
    rw [argmin_eq_ite]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl
  obtain ⟨x, hxm, hx⟩ := hm.exists_measurable_selection hc
  exact ⟨hp, hc, hm, hm.measurableSet_svDom, x, hxm, hx⟩

end Theorem1437

end RW
