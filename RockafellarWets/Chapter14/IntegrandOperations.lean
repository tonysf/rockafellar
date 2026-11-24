/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Operations on integrands

Proposition 14.44(a)(b) (pointwise suprema and infima), Proposition 14.45(a)(c) (composition
with Carathéodory mappings and measurable parameters), Proposition 14.47 (inf-projection) and
Exercise 14.35 (closures of measurable integrands, under completeness for an s-finite measure) and
Proposition 14.53 (limits of integrands; epi-limits and closures of pointwise limits) of
Rockafellar–Wets.  The lsc regularization `cl_x` is the project's `epiClosure`.
-/

import RockafellarWets.Chapter14.IntegrandExamples
import RockafellarWets.Chapter7.EpiLimitProperties
import RockafellarWets.Chapter3.Parametric
import RockafellarWets.Chapter3.Pointwise

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace RW

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

section Proposition1444

/-- **Proposition 14.44(a)**: countable pointwise suprema of normal integrands are normal. -/
theorem IsNormalIntegrand.iSup {J : Type*} [Countable J] {f : J → T → E → EReal}
    (hf : ∀ j, IsNormalIntegrand (f j)) : IsNormalIntegrand (fun t x ↦ ⨆ j, f j t x) := by
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [epigraph_iSup]
    exact isClosed_iInter fun j ↦ (hf j).1 t
  · have : epiMapping (fun t x ↦ ⨆ j, f j t x) = fun t ↦ ⋂ j, epiMapping (f j) t :=
      funext fun t ↦ epigraph_iSup _
    rw [this]
    exact SvMeasurable.iInter (fun j ↦ (hf j).2) fun j ↦ (hf j).1

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Proposition 14.44(b)**: for countably many normal integrands, the lsc regularization
`cl_x (inf_j fⱼ)` of the pointwise infimum is a normal integrand. -/
theorem IsNormalIntegrand.epiClosure_iInf {J : Type*} [Countable J] {f : J → T → E → EReal}
    (hf : ∀ j, IsNormalIntegrand (f j)) :
    IsNormalIntegrand (fun t ↦ epiClosure (fun x ↦ ⨅ j, f j t x)) := by
  have hepi : ∀ t, epigraph (epiClosure (fun x ↦ ⨅ j, f j t x)) =
      _root_.closure (⋃ j, epigraph (f j t)) := fun t ↦ by
    rw [epigraph_epiClosure, closure_epigraph_iInf]
  refine ⟨fun t ↦ by rw [hepi t]; exact isClosed_closure, ?_⟩
  have : epiMapping (fun t ↦ epiClosure (fun x ↦ ⨅ j, f j t x)) =
      fun t ↦ _root_.closure (⋃ j, epiMapping (f j) t) := funext hepi
  rw [this]
  exact (SvMeasurable.iUnion fun j ↦ (hf j).2).closure

/-- **Proposition 14.44(b)**, lsc case: a countable pointwise infimum of normal integrands that is
lsc in `x` is a normal integrand. -/
theorem IsNormalIntegrand.iInf_of_lowerSemicontinuous {J : Type*} [Countable J]
    {f : J → T → E → EReal} (hf : ∀ j, IsNormalIntegrand (f j))
    (hlsc : ∀ t, LowerSemicontinuous fun x ↦ ⨅ j, f j t x) :
    IsNormalIntegrand (fun t x ↦ ⨅ j, f j t x) := by
  have h := IsNormalIntegrand.epiClosure_iInf hf
  have heq : (fun t ↦ epiClosure (fun x ↦ ⨅ j, f j t x)) = fun t x ↦ ⨅ j, f j t x :=
    funext fun t ↦ epiClosure_eq_of_lowerSemicontinuous (hlsc t)
  rwa [heq] at h

/-- **Proposition 14.44(b)**, finite case: a finite pointwise infimum of normal integrands is a
normal integrand. -/
theorem IsNormalIntegrand.iInf_of_finite {J : Type*} [Finite J] {f : J → T → E → EReal}
    (hf : ∀ j, IsNormalIntegrand (f j)) : IsNormalIntegrand (fun t x ↦ ⨅ j, f j t x) := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · simp only [iInf_of_empty]
    exact isNormalIntegrand_const lowerSemicontinuous_const
  exact IsNormalIntegrand.iInf_of_lowerSemicontinuous hf fun t ↦
    lowerSemicontinuous_iInf_of_finite fun j ↦ (hf j).lowerSemicontinuous t

end Proposition1444

section Proposition1445

variable [MeasurableSpace E] [BorelSpace E]

/-- **Proposition 14.45(a)**: `f(t, x) = g(t, F(t, x))` is normal for a normal integrand `g` and a
Carathéodory mapping `F`. -/
theorem IsNormalIntegrand.comp_caratheodory {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] {g : T → G → EReal}
    (hg : IsNormalIntegrand g) {F : T → E → G} (hF : IsCaratheodory F) :
    IsNormalIntegrand (fun t x ↦ g t (F t x)) := by
  set Φ : T → E × ℝ → G × ℝ := fun t p ↦ (F t p.1, p.2)
  have hΦ : IsCaratheodory Φ :=
    ⟨fun p ↦ (hF.1 p.1).prodMk measurable_const,
      fun t ↦ ((hF.2 t).comp continuous_fst).prodMk continuous_snd⟩
  obtain ⟨hc, hm⟩ := hΦ.svMeasurable_preimage hg.2 hg.1
  have hepi : ∀ t, epigraph (fun x ↦ g t (F t x)) = {p : E × ℝ | Φ t p ∈ epiMapping g t} :=
    fun t ↦ rfl
  refine ⟨fun t ↦ by rw [hepi t]; exact hc t, ?_⟩
  have : epiMapping (fun t x ↦ g t (F t x)) = fun t ↦ {p : E × ℝ | Φ t p ∈ epiMapping g t} :=
    funext hepi
  rw [this]
  exact hm

/-- **Proposition 14.45(c)**: `f(t, x) = g(t, x, u(t))` is normal for a normal integrand `g` and a
measurable `u`. -/
theorem IsNormalIntegrand.comp_measurable_param {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
    {g : T → E × G → EReal} (hg : IsNormalIntegrand g) {u : T → G} (hu : Measurable u) :
    IsNormalIntegrand (fun t x ↦ g t (x, u t)) :=
  hg.comp_caratheodory (F := fun t x ↦ (x, u t))
    ⟨fun x ↦ measurable_const.prodMk hu, fun t ↦ continuous_id.prodMk continuous_const⟩

end Proposition1445

section Proposition1447

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

omit [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ G] [FiniteDimensional ℝ G] in
theorem closure_epigraph_valueFunction_eq_image [TopologicalSpace E] (g : E × G → EReal) :
    _root_.closure (epigraph (valueFunction g)) =
      _root_.closure ((fun p : (E × G) × ℝ ↦ (p.1.2, p.2)) '' epigraph g) := by
  apply Subset.antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro ⟨u, α⟩ huα
    have huα' : valueFunction g u ≤ α := huα
    have hseq : ∀ n : ℕ, ((u, α + 1 / ((n : ℝ) + 1)) : G × ℝ) ∈
        (fun p : (E × G) × ℝ ↦ (p.1.2, p.2)) '' epigraph g := by
      intro n
      have hlt : valueFunction g u < ((α + 1 / ((n : ℝ) + 1) : ℝ) : EReal) :=
        lt_of_le_of_lt huα' (EReal.coe_lt_coe_iff.2 (by
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith))
      obtain ⟨x, hx⟩ := iInf_lt_iff.1 hlt
      exact ⟨((x, u), α + 1 / ((n : ℝ) + 1)), hx.le, rfl⟩
    have htend : Tendsto (fun n : ℕ ↦ ((u, α + 1 / ((n : ℝ) + 1)) : G × ℝ)) atTop
        (𝓝 (u, α)) := by
      refine tendsto_const_nhds.prodMk_nhds ?_
      have := (tendsto_const_nhds (x := α)).add tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [add_zero] at this
    exact mem_closure_of_tendsto htend (Eventually.of_forall hseq)
  · refine closure_mono ?_
    rintro _ ⟨⟨⟨x, u⟩, α⟩, hxα, rfl⟩
    exact (iInf_le (fun x' : E ↦ g (x', u)) x).trans hxα

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
/-- **Proposition 14.47 (inf-projection of integrands)**: for a normal integrand
`f : T × (ℝⁿ × ℝᵐ) → ℝ̄`, the lsc regularization `p̄(t, ·) = cl_u inf_x f(t, x, ·)` is always a
normal integrand. -/
theorem IsNormalIntegrand.epiClosure_valueFunction {f : T → E × G → EReal}
    (hf : IsNormalIntegrand f) : IsNormalIntegrand (fun t ↦ epiClosure (valueFunction (f t))) := by
  have hepi : ∀ t, epigraph (epiClosure (valueFunction (f t))) =
      _root_.closure ((fun p : (E × G) × ℝ ↦ (p.1.2, p.2)) '' epiMapping f t) := fun t ↦ by
    rw [epigraph_epiClosure, closure_epigraph_valueFunction_eq_image]
    rfl
  refine ⟨fun t ↦ by rw [hepi t]; exact isClosed_closure, ?_⟩
  have : epiMapping (fun t ↦ epiClosure (valueFunction (f t))) =
      fun t ↦ _root_.closure ((fun p : (E × G) × ℝ ↦ (p.1.2, p.2)) '' epiMapping f t) :=
    funext hepi
  rw [this]
  exact (hf.2.image ((continuous_snd.comp continuous_fst).prodMk continuous_snd)).closure

/-- **Proposition 14.47**: if the inf-projection `p(t, u) = inf_x f(t, x, u)` is lsc in `u`, it is
a normal integrand. -/
theorem IsNormalIntegrand.valueFunction_of_lowerSemicontinuous {f : T → E × G → EReal}
    (hf : IsNormalIntegrand f) (hlsc : ∀ t, LowerSemicontinuous (valueFunction (f t))) :
    IsNormalIntegrand (fun t ↦ valueFunction (f t)) := by
  have h := hf.epiClosure_valueFunction
  have heq : (fun t ↦ epiClosure (valueFunction (f t))) = fun t ↦ valueFunction (f t) :=
    funext fun t ↦ epiClosure_eq_of_lowerSemicontinuous (hlsc t)
  rwa [heq] at h

end Proposition1447

section Proposition1453

/-- **Proposition 14.53(a)**: if `f(t, ·)` is the lower epi-limit `e-lim inf fν(t, ·)` of normal
integrands, it is a normal integrand. -/
theorem IsNormalIntegrand.epiLowerLimit {f : ℕ → T → E → EReal}
    (hf : ∀ n, IsNormalIntegrand (f n)) :
    IsNormalIntegrand (fun t ↦ RW.epiLowerLimit (fun n ↦ f n t)) := by
  have hepi : epiMapping (fun t ↦ RW.epiLowerLimit (fun n ↦ f n t)) =
      RW.pointwiseOuterLimit (fun n ↦ epiMapping (f n)) :=
    funext fun t ↦ epigraph_epiLowerLimit _
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [epigraph_epiLowerLimit]
    exact isClosed_outerSetLimit _
  · rw [hepi]
    exact SvMeasurable.pointwiseOuterLimit fun n ↦ (hf n).2

/-- **Proposition 14.53(a)**: if `f(t, ·)` is the upper epi-limit `e-lim sup fν(t, ·)` of normal
integrands, it is a normal integrand. -/
theorem IsNormalIntegrand.epiUpperLimit {f : ℕ → T → E → EReal}
    (hf : ∀ n, IsNormalIntegrand (f n)) :
    IsNormalIntegrand (fun t ↦ RW.epiUpperLimit (fun n ↦ f n t)) := by
  have hepi : epiMapping (fun t ↦ RW.epiUpperLimit (fun n ↦ f n t)) =
      RW.pointwiseInnerLimit (fun n ↦ epiMapping (f n)) :=
    funext fun t ↦ epigraph_epiUpperLimit _
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [epigraph_epiUpperLimit]
    exact isClosed_innerSetLimit _
  · rw [hepi]
    exact SvMeasurable.pointwiseInnerLimit fun n ↦ (hf n).2

/-- **Proposition 14.53(a)**: epi-limits of normal integrands are normal integrands. -/
theorem IsNormalIntegrand.of_epiConverges {f : ℕ → T → E → EReal} {g : T → E → EReal}
    (hf : ∀ n, IsNormalIntegrand (f n)) (hg : ∀ t, EpiConverges (fun n ↦ f n t) (g t)) :
    IsNormalIntegrand g := by
  have hepi : epiMapping g = RW.pointwiseInnerLimit (fun n ↦ epiMapping (f n)) :=
    funext fun t ↦ ((hg t).inner_eq).symm
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [← (hg t).inner_eq]
    exact isClosed_innerSetLimit _
  · rw [hepi]
    exact SvMeasurable.pointwiseInnerLimit fun n ↦ (hf n).2

/-- **Proposition 14.53(b)**: `f(t, ·) = cl [p-lim sup fν(t, ·)]` is a normal integrand. -/
theorem IsNormalIntegrand.epiClosure_limsup {f : ℕ → T → E → EReal}
    (hf : ∀ n, IsNormalIntegrand (f n)) :
    IsNormalIntegrand (fun t ↦ epiClosure (fun x ↦ Filter.limsup (fun n ↦ f n t x) atTop)) := by
  have hsup : ∀ m, IsNormalIntegrand (fun t x ↦ ⨆ k, ⨆ (_ : m ≤ k), f k t x) := by
    intro m
    refine IsNormalIntegrand.iSup fun k ↦ ?_
    by_cases hk : m ≤ k
    · simp only [hk, iSup_pos]
      exact hf k
    · simp only [hk, iSup_false]
      exact isNormalIntegrand_const lowerSemicontinuous_const
  have h := IsNormalIntegrand.epiClosure_iInf hsup
  have heq : (fun t ↦ epiClosure (fun x ↦ ⨅ m, ⨆ k, ⨆ (_ : m ≤ k), f k t x)) =
      fun t ↦ epiClosure (fun x ↦ Filter.limsup (fun n ↦ f n t x) atTop) := by
    funext t
    congr 1
    funext x
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
  rwa [heq] at h

/-- **Exercise 14.35 (closures of measurable integrands)**, adapted: when the σ-field `A` is
complete for an s-finite (e.g. σ-finite) measure, `f(t, ·) = cl f₀(t, ·)` is a normal integrand
for every `A ⊗ B(E)`-measurable `f₀`.  (The printed hypothesis "complete for some measure" holds
for every σ-field, by the counting measure, and does not suffice: for `f₀ = δ_G` with `G` a Borel
set whose projection is not Borel, `dom f(t, ·) = cl G(t)` would make that projection measurable;
see `closure_integrand_counterexample` on the Baire space.) -/
theorem isNormalIntegrand_epiClosure_of_measurable [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure T) [MeasureTheory.SFinite μ] [μ.IsComplete] {f₀ : T → E → EReal}
    (hf₀ : Measurable (Function.uncurry f₀)) :
    IsNormalIntegrand (fun t ↦ epiClosure (f₀ t)) := by
  have hepi : ∀ t, epiMapping (fun t ↦ epiClosure (f₀ t)) t = _root_.closure (epiMapping f₀ t) :=
    fun t ↦ epigraph_epiClosure (f₀ t)
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [show epigraph (epiClosure (f₀ t)) = _ from hepi t]
    exact isClosed_closure
  · rw [show epiMapping (fun t ↦ epiClosure (f₀ t)) =
      fun t ↦ _root_.closure (epiMapping f₀ t) from funext hepi]
    refine SvMeasurable.closure (svMeasurable_of_measurableSet_svGraph μ ?_)
    have : svGraph (epiMapping f₀) =
        {p : T × (E × ℝ) | Function.uncurry f₀ (p.1, p.2.1) ≤ ((p.2.2 : ℝ) : EReal)} := by
      ext p
      rfl
    rw [this]
    exact measurableSet_le (hf₀.comp (measurable_fst.prodMk measurable_snd.fst))
      (measurable_coe_real_ereal.comp measurable_snd.snd)

/-- **Proposition 14.53(b)**, lim inf case (adapted: completeness for an s-finite measure):
`f(t, ·) = cl [p-lim inf fν(t, ·)]` is a normal integrand, via 14.34 and 14.35.  Under the printed
hypothesis "complete for some measure" it fails (`liminf_integrand_counterexample`). -/
theorem IsNormalIntegrand.epiClosure_liminf [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure T) [MeasureTheory.SFinite μ] [μ.IsComplete]
    {f : ℕ → T → E → EReal} (hf : ∀ n, IsNormalIntegrand (f n)) :
    IsNormalIntegrand (fun t ↦ epiClosure (fun x ↦ Filter.liminf (fun n ↦ f n t x) atTop)) := by
  have hmeas : Measurable (Function.uncurry fun t x ↦ Filter.liminf (fun n ↦ f n t x) atTop) :=
    Measurable.liminf (f := fun n p ↦ Function.uncurry (f n) p) fun n ↦ (hf n).measurable_uncurry
  exact isNormalIntegrand_epiClosure_of_measurable μ hmeas

end Proposition1453


section Proposition1447LevelBounded

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

omit [MeasurableSpace T] [FiniteDimensional ℝ G] in
/-- Theorem 1.17-type fact used in Proposition 14.47: if `g(x, u)` is lsc and level-bounded in `x`
locally uniformly in `u`, then `p(u) = inf_x g(x, u)` is lsc (no properness is needed). -/
theorem lowerSemicontinuous_valueFunction_of_levelBounded {g : E × G → EReal}
    (hl : LowerSemicontinuous g) (hb : IsLevelBoundedInXLocallyUniformly g) :
    LowerSemicontinuous (valueFunction g) := by
  refine lowerSemicontinuous_of_isClosed_levelSet fun α ↦ ?_
  refine isSeqClosed_iff_isClosed.1 fun u ubar hu hut ↦ ?_
  obtain ⟨ε, hε, hbdd⟩ := hb ubar (α + 1)
  have hx : ∀ n : ℕ, ∃ x, g (x, u n) < ((α + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
    intro n
    have h1 : valueFunction g (u n) ≤ α := hu n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h2 : (α : EReal) < ((α + 1 / ((n : ℝ) + 1) : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.2 (by linarith)
    exact iInf_lt_iff.1 (lt_of_le_of_lt h1 h2)
  choose x hx using hx
  have hmem : ∀ᶠ n in atTop, (x n, u n) ∈ localUniformSublevel g ubar ε (α + 1) := by
    filter_upwards [hut.eventually (closedBall_mem_nhds ubar hε)] with n hn
    refine ⟨⟨mem_univ _, hn⟩, ?_⟩
    change g (x n, u n) ≤ ((α + 1 : ℝ) : EReal)
    refine (hx n).le.trans (EReal.coe_le_coe_iff.2 ?_)
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have hxbdd : Bornology.IsBounded (Prod.fst '' localUniformSublevel g ubar ε (α + 1)) :=
    hbdd.image_fst
  obtain ⟨xbar, -, φ, hφ, hxφ⟩ := tendsto_subseq_of_frequently_bounded hxbdd
    (hmem.mono fun n hn ↦ ⟨_, hn, rfl⟩).frequently
  have huφ : Tendsto (u ∘ φ) atTop (𝓝 ubar) := hut.comp hφ.tendsto_atTop
  have hpair : Tendsto (fun k ↦ (x (φ k), u (φ k))) atTop (𝓝 (xbar, ubar)) := hxφ.prodMk_nhds huφ
  have hle : g (xbar, ubar) ≤ α := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real hgt
    have hev := hpair.eventually (hl (xbar, ubar) _ hy2)
    have hsmall : ∀ᶠ k in atTop, α + 1 / ((φ k : ℝ) + 1) < y := by
      have hr : Tendsto (fun k ↦ α + 1 / ((φ k : ℝ) + 1)) atTop (𝓝 α) := by
        have h0 : Tendsto (fun k ↦ 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
        have := (tendsto_const_nhds (x := α)).add h0
        rwa [add_zero] at this
      exact hr.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.1 hy1))
    obtain ⟨k, hk1, hk2⟩ := (hev.and hsmall).exists
    have := lt_trans hk1 (hx (φ k))
    exact absurd (EReal.coe_lt_coe_iff.1 this) (not_lt.2 hk2.le)
  exact (iInf_le (fun x' : E ↦ g (x', ubar)) xbar).trans hle

/-- **Proposition 14.47**, parenthetical case: if for each `t` the normal integrand `f(t, x, u)` is
level-bounded in `x` locally uniformly in `u`, the inf-projection `p` is a normal integrand. -/
theorem IsNormalIntegrand.valueFunction_of_levelBounded {f : T → E × G → EReal}
    (hf : IsNormalIntegrand f) (hb : ∀ t, IsLevelBoundedInXLocallyUniformly (f t)) :
    IsNormalIntegrand (fun t ↦ valueFunction (f t)) :=
  hf.valueFunction_of_lowerSemicontinuous fun t ↦
    lowerSemicontinuous_valueFunction_of_levelBounded (hf.lowerSemicontinuous t) (hb t)

end Proposition1447LevelBounded

end RW
