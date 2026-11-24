/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Moreau envelopes and proximal mappings of normal integrands

Exercise 14.38 of Rockafellar–Wets.  For a proper normal integrand with `f(t, ·)` prox-bounded
with threshold `λ_f(t)` and a measurable `λ(t) ∈ (0, λ_f(t))`:

* `e(t, x) = e_{λ(t)} f(t, ·)(x)` is finite and a Carathéodory integrand: continuity in `x` comes
  from Theorem 7.37 applied to the constant sequence, measurability in `t` from a Castaing
  representation of the epigraphical mapping (the infimum of the continuous function
  `(w, α) ↦ α + |w - x|²/(2λ)` over `epi f(t, ·)` equals its infimum over a dense subset);
* `P(t, ·) = P_{λ(t)} f(t, ·)` is osc (5.23(b)), and its graph is the level set `{h ≤ 0}` of the
  normal integrand `h(t, x, w) = f(t, w) + |w - x|²/(2λ(t)) - e(t, x)`;
* for convex `f(t, ·)`, `P` is a single-valued Carathéodory mapping (12.19);
* `e(t, x(t))` and `P(t, x(t))` depend measurably on `t` (14.14).
-/

import RockafellarWets.Chapter14.IntegrandSums
import RockafellarWets.Chapter7.MoreauEnvelopeLimits
import RockafellarWets.Chapter5.ProximalMappings
import RockafellarWets.Chapter12.ProximalMappingMonotonicity

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace RW

section Envelopes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem epiConverges_const_of_lowerSemicontinuous [NormedSpace ℝ E] {g : E → EReal} (hg : LowerSemicontinuous g) :
    EpiConverges (fun _ ↦ g) g := by
  have hc := (lsc_iff_epigraph_closed_ereal g).1 hg
  exact ⟨by rw [innerSetLimit_const, hc.closure_eq], by rw [outerSetLimit_const, hc.closure_eq]⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem eventualProxThreshold_const (g : E → EReal) :
    eventualProxThreshold (fun _ ↦ g) = proxThreshold g := by
  unfold eventualProxThreshold proxThreshold
  simp only [liminf_const]
  rfl

/-- Theorem 1.25 (envelope part), via Theorem 7.37: for `g` proper lsc and `0 < λ < λ_g`, the
Moreau envelope is finite and continuous. -/
theorem moreauEnvelopeEReal_finite_continuous {g : E → EReal} (hp : IsProper g)
    (hl : LowerSemicontinuous g) {lam : ℝ} (hlam : 0 < lam) (hthr : (lam : EReal) < proxThreshold g) :
    (∀ x, ∃ a : ℝ, moreauEnvelopeEReal g lam x = a) ∧ Continuous (moreauEnvelopeEReal g lam) := by
  have hconv := epiConverges_const_of_lowerSemicontinuous hl
  have hthr' : (lam : EReal) < eventualProxThreshold (fun _ ↦ g) := by
    rwa [eventualProxThreshold_const]
  have key : ∀ (xs : ℕ → E) (x : E), Tendsto xs atTop (𝓝 x) →
      (∃ a : ℝ, moreauEnvelopeEReal g lam x = a) ∧
        Tendsto (fun n ↦ moreauEnvelopeEReal g lam (xs n)) atTop (𝓝 (moreauEnvelopeEReal g lam x)) :=
    fun xs x hxs ↦ tendsto_moreauEnvelopeEReal_of_epiConverges hconv (fun _ ↦ hl) hp hxs
      tendsto_const_nhds hlam hthr'
  refine ⟨fun x ↦ (key (fun _ ↦ x) x tendsto_const_nhds).1, ?_⟩
  rw [continuous_iff_seqContinuous]
  intro xs x hxs
  exact (key xs x hxs).2

end Envelopes

section Exercise1438

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The infimum of `α + q(w)` over an epigraph equals its infimum over a dense subset. -/
theorem iInf_add_eq_iInf_of_dense {g : E → EReal} {z : ℕ → E × ℝ}
    (hz : epigraph g = _root_.closure (range z)) {q : E → ℝ} (hq : Continuous q) :
    (⨅ w, g w + (q w : EReal)) = ⨅ n, (((z n).2 + q (z n).1 : ℝ) : EReal) := by
  have hzmem : ∀ n, z n ∈ epigraph g := fun n ↦ hz ▸ subset_closure ⟨n, rfl⟩
  apply le_antisymm
  · refine le_iInf fun n ↦ (iInf_le _ (z n).1).trans ?_
    rw [EReal.coe_add]
    exact add_le_add (hzmem n) le_rfl
  · set M := ⨅ n, (((z n).2 + q (z n).1 : ℝ) : EReal)
    have hcl : ∀ p ∈ epigraph g, M ≤ ((p.2 + q p.1 : ℝ) : EReal) := by
      have hclosed : IsClosed {p : E × ℝ | M ≤ ((p.2 + q p.1 : ℝ) : EReal)} :=
        isClosed_le continuous_const (continuous_coe_real_ereal.comp
          (continuous_snd.add (hq.comp continuous_fst)))
      intro p hp
      rw [hz] at hp
      exact closure_minimal (by
        rintro _ ⟨n, rfl⟩
        exact iInf_le (fun n ↦ (((z n).2 + q (z n).1 : ℝ) : EReal)) n) hclosed hp
    refine le_iInf fun w ↦ ?_
    induction h : g w with
    | bot =>
      rw [EReal.bot_add, le_bot_iff, EReal.eq_bot_iff_forall_lt]
      intro y
      have := hcl (w, y - q w - 1) (by change g w ≤ _; rw [h]; exact bot_le)
      refine lt_of_le_of_lt this (EReal.coe_lt_coe_iff.2 ?_)
      simp only
      linarith
    | coe r =>
      have := hcl (w, r) (by change g w ≤ r; rw [h])
      rwa [EReal.coe_add] at this
    | top =>
      rw [EReal.top_add_coe]
      exact le_top


theorem ereal_add_coe_eq_iff {A : EReal} (hA : A ≠ ⊥) {q m : ℝ} (hle : (m : EReal) ≤ A + q) :
    (A + q = m ∧ (m : EReal) < ⊤) ↔ A + ((q - m : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := by
  induction A with
  | bot => exact absurd rfl hA
  | top =>
    rw [EReal.top_add_coe, EReal.top_add_coe]
    simp
  | coe a =>
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_eq_coe_iff, EReal.coe_le_coe_iff]
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hle
    constructor
    · rintro ⟨h, -⟩
      linarith
    · intro h
      exact ⟨by linarith, EReal.coe_lt_top m⟩

/-- **Exercise 14.38 (Moreau envelopes and proximal mappings)**. -/
theorem moreau_envelopes_and_proximal_mappings {f : T → E → EReal} (hf : IsNormalIntegrand f)
    (hp : ∀ t, IsProper (f t)) {lam : T → ℝ} (hlam : Measurable lam) (hpos : ∀ t, 0 < lam t)
    (hthr : ∀ t, (lam t : EReal) < proxThreshold (f t)) :
    (∀ t x, ∃ a : ℝ, moreauEnvelopeEReal (f t) (lam t) x = a) ∧
      IsCaratheodory (fun t x ↦ (moreauEnvelopeEReal (f t) (lam t) x).toReal) ∧
      (∀ t, SvOsc (proximalMappingEReal (f t) (lam t))) ∧
      ((∀ t, IsClosed (svGraph (proximalMappingEReal (f t) (lam t)))) ∧
        SvMeasurable (fun t ↦ svGraph (proximalMappingEReal (f t) (lam t)))) ∧
      ((∀ t, Convex ℝ (epigraph (f t))) → ∃ P : T → E → E, IsCaratheodory P ∧
        ∀ t x, proximalMappingEReal (f t) (lam t) x = {P t x}) ∧
      (∀ {x : T → E}, Measurable x →
        Measurable (fun t ↦ moreauEnvelopeEReal (f t) (lam t) (x t)) ∧
          SvMeasurable (fun t ↦ proximalMappingEReal (f t) (lam t) (x t))) := by
  have hl : ∀ t, LowerSemicontinuous (f t) := hf.lowerSemicontinuous
  have hfc := fun t ↦ moreauEnvelopeEReal_finite_continuous (hp t) (hl t) (hpos t) (hthr t)
  set e : T → E → ℝ := fun t x ↦ (moreauEnvelopeEReal (f t) (lam t) x).toReal with hedef
  have he : ∀ t x, moreauEnvelopeEReal (f t) (lam t) x = e t x := by
    intro t x
    obtain ⟨a, ha⟩ := (hfc t).1 x
    simp only [hedef, ha, EReal.toReal_coe]
  -- measurability in `t`
  obtain ⟨z, hz⟩ := hf.2.exists_castaingRepresentation hf.1
  have hdom : ∀ t, t ∈ svDom (epiMapping f) := by
    intro t
    obtain ⟨⟨w, hw⟩, -⟩ := hp t
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f t w < r := by
      induction h : f t w with
      | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
      | coe a => exact ⟨a + 1, EReal.coe_lt_coe_iff.2 (lt_add_one a)⟩
      | top => rw [h] at hw; exact absurd hw (lt_irrefl _)
    exact ⟨(w, r), hr.le⟩
  have hmeasx : ∀ x, Measurable fun t ↦ moreauEnvelopeEReal (f t) (lam t) x := by
    intro x
    have heq : (fun t ↦ moreauEnvelopeEReal (f t) (lam t) x) = fun t ↦
        ⨅ n, (((z n t).2 + (1 / (2 * lam t)) * ‖(z n t).1 - x‖ ^ 2 : ℝ) : EReal) := by
      funext t
      exact iInf_add_eq_iInf_of_dense (hz.2 t (hdom t))
        ((continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)))
    rw [heq]
    refine Measurable.iInf fun n ↦ Measurable.coe_real_ereal ?_
    exact (hz.1 n).snd.add ((measurable_const.div (measurable_const.mul hlam)).mul
      (((hz.1 n).fst.sub measurable_const).norm.pow_const 2))
  have hcar : IsCaratheodory e := by
    refine ⟨fun x ↦ (hmeasx x).ereal_toReal, fun t ↦ ?_⟩
    refine EReal.continuousOn_toReal.comp_continuous (hfc t).2 fun x ↦ ?_
    rw [he t x]
    simp
  -- osc and graph
  have hosc : ∀ t, SvOsc (proximalMappingEReal (f t) (lam t)) := fun t ↦ by
    rw [← proxMappingEReal_eq_proximalMappingEReal]
    exact svOsc_proxMappingEReal (hp t) (hl t) (lam t)
  set h : T → E × E → EReal := fun t p ↦
    f t p.2 + (((1 / (2 * lam t)) * ‖p.2 - p.1‖ ^ 2 - e t p.1 : ℝ) : EReal) with hhdef
  have hh : IsNormalIntegrand h := by
    have h1 : IsNormalIntegrand (fun t (p : E × E) ↦ f t p.2) :=
      hf.comp_caratheodory (F := fun (_ : T) (p : E × E) ↦ p.2)
        ⟨fun _ ↦ measurable_const, fun _ ↦ continuous_snd⟩
    have h2 : IsCaratheodory (fun t (p : E × E) ↦ (1 / (2 * lam t)) * ‖p.2 - p.1‖ ^ 2 - e t p.1) := by
      refine ⟨fun p ↦ ?_, fun t ↦ ?_⟩
      · exact ((measurable_const.div (measurable_const.mul hlam)).mul measurable_const).sub
          (hcar.1 p.1)
      · exact (continuous_const.mul ((continuous_snd.sub continuous_fst).norm.pow 2)).sub
          ((hcar.2 t).comp continuous_fst)
    exact h1.add h2.isNormalIntegrand (fun t p ↦ ((hp t).2 p.2).ne') (fun _ _ ↦ EReal.coe_ne_bot _)
  have hgraph : ∀ t, svGraph (proximalMappingEReal (f t) (lam t)) = {p : E × E | h t p ≤ ((0 : ℝ) : EReal)} := by
    intro t
    ext ⟨x, w⟩
    simp only [mem_svGraph, mem_proximalMappingEReal_iff, mem_setOf_eq, hhdef]
    rw [he t x]
    have hle : moreauEnvelopeEReal (f t) (lam t) x ≤ proximalObjectiveEReal (f t) (lam t) x w :=
      iInf_le _ w
    rw [he t x] at hle
    unfold proximalObjectiveEReal at hle ⊢
    exact ereal_add_coe_eq_iff ((hp t).2 w).ne' hle
  have hlev := hh.levelSet_measurable (α := fun _ ↦ (0 : ℝ)) measurable_const
  have hGc : ∀ t, IsClosed (svGraph (proximalMappingEReal (f t) (lam t))) := fun t ↦ by
    rw [hgraph t]
    exact hlev.1 t
  have hGm : SvMeasurable (fun t ↦ svGraph (proximalMappingEReal (f t) (lam t))) := by
    rw [funext hgraph]
    exact hlev.2
  refine ⟨fun t x ↦ (hfc t).1 x, hcar, hosc, ⟨hGc, hGm⟩, fun hconv ↦ ?_, fun {x} hx ↦ ?_⟩
  · have hsing : ∀ t x, proximalMappingEReal (f t) (lam t) x =
        {resolventMap (subdifferential (f t)) (lam t) x} := fun t x ↦
      proximalMappingEReal_eq_singleton_of_convex (hp t) (hl t) (hconv t) (hpos t) x
    refine ⟨fun t x ↦ resolventMap (subdifferential (f t)) (lam t) x, ⟨fun x ↦ ?_, fun t ↦ ?_⟩,
      hsing⟩
    · have hs := (composition_with_measurable_functions hosc hGm
        (measurable_const (a := x))).2
      have heq : (fun t ↦ proximalMappingEReal (f t) (lam t) x) =
          fun t ↦ {resolventMap (subdifferential (f t)) (lam t) x} := funext fun t ↦ hsing t x
      rw [heq] at hs
      exact svMeasurable_singleton_iff.1 hs
    · have hne := svNonexpansive_proximalMappingEReal_of_convex (hp t) (hconv t) (hpos t)
      refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ ?_).continuous
      have hx : resolventMap (subdifferential (f t)) (lam t) x ∈
          proximalMappingEReal (f t) (lam t) x := by rw [hsing t x]; rfl
      have hy : resolventMap (subdifferential (f t)) (lam t) y ∈
          proximalMappingEReal (f t) (lam t) y := by rw [hsing t y]; rfl
      have := hne hy hx
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      exact this
  · refine ⟨?_, (composition_with_measurable_functions hosc hGm hx).2⟩
    have hjoint : Measurable (Function.uncurry fun (y : E) (t : T) ↦ e t y) :=
      MeasureTheory.measurable_uncurry_of_continuous_of_measurable (fun t ↦ hcar.2 t)
        (fun y ↦ hcar.1 y)
    have h2 : Measurable ((Function.uncurry fun (y : E) (t : T) ↦ e t y) ∘ fun t ↦ (x t, t)) :=
      hjoint.comp (hx.prodMk measurable_id)
    have h3 : (fun t ↦ moreauEnvelopeEReal (f t) (lam t) (x t)) =
        fun t ↦ ((e t (x t) : ℝ) : EReal) := funext fun t ↦ he t (x t)
    rw [h3]
    exact h2.coe_real_ereal

end Exercise1438

end RW
