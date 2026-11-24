/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Integral functionals

Proposition 14.58 (integral functionals) and Definition 14.59 (decomposable spaces) of
Rockafellar–Wets, with the book's extended (upper) integral of an extended-real function:
`∫ α = ∫ max{α, 0} + ∫ min{α, 0}` with `∞ + (-∞) = ∞`, i.e. `upperIntegral μ α` is `∞` when
`∫ α⁺ = ∞` and `∫ α⁺ - ∫ α⁻` otherwise.
-/

import RockafellarWets.Chapter14.IntegrandOperations
import RockafellarWets.Chapter7.EpigraphAddition
import RockafellarWets.Chapter3.ERealInfimum
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity

open Set Filter Topology Metric TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace RW

section UpperIntegral

variable {T : Type*} [MeasurableSpace T]

/-- The book's (upper) integral of an extended-real function: `∞` when the positive part has
infinite integral, otherwise `∫ α⁺ - ∫ α⁻`. -/
def upperIntegral (μ : Measure T) (α : T → EReal) : EReal :=
  if ∫⁻ t, (α t).toENNReal ∂μ = ⊤ then ⊤
  else ((∫⁻ t, (α t).toENNReal ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ t, (-α t).toENNReal ∂μ : ℝ≥0∞) : EReal)

variable {μ : Measure T}

theorem upperIntegral_of_lintegral_ne_top {α : T → EReal} (h : ∫⁻ t, (α t).toENNReal ∂μ ≠ ⊤) :
    upperIntegral μ α = ((∫⁻ t, (α t).toENNReal ∂μ : ℝ≥0∞) : EReal) -
      ((∫⁻ t, (-α t).toENNReal ∂μ : ℝ≥0∞) : EReal) := by
  rw [upperIntegral, if_neg h]

theorem upperIntegral_lt_top_iff {α : T → EReal} :
    upperIntegral μ α < ⊤ ↔ ∫⁻ t, (α t).toENNReal ∂μ < ⊤ := by
  constructor
  · intro h
    by_contra h'
    rw [not_lt, top_le_iff] at h'
    rw [upperIntegral, if_pos h'] at h
    exact lt_irrefl _ h
  · intro h
    rw [upperIntegral_of_lintegral_ne_top h.ne, sub_eq_add_neg]
    refine EReal.add_lt_top (fun h' ↦ h.ne (EReal.coe_ennreal_eq_top_iff.1 h')) ?_
    exact ne_top_of_le_ne_top EReal.zero_ne_top
      (EReal.neg_le_neg_iff.1 (by simpa using EReal.coe_ennreal_nonneg _))

/-- The upper integral is monotone (almost everywhere). -/
theorem upperIntegral_mono_ae {α β : T → EReal} (h : ∀ᵐ t ∂μ, α t ≤ β t) :
    upperIntegral μ α ≤ upperIntegral μ β := by
  have hP : ∫⁻ t, (α t).toENNReal ∂μ ≤ ∫⁻ t, (β t).toENNReal ∂μ :=
    lintegral_mono_ae (h.mono fun t ht ↦ EReal.toENNReal_le_toENNReal ht)
  have hN : ∫⁻ t, (-β t).toENNReal ∂μ ≤ ∫⁻ t, (-α t).toENNReal ∂μ :=
    lintegral_mono_ae (h.mono fun t ht ↦ EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 ht))
  by_cases hβ : ∫⁻ t, (β t).toENNReal ∂μ = ⊤
  · have : upperIntegral μ β = ⊤ := by rw [upperIntegral, if_pos hβ]
    rw [this]
    exact le_top
  · have hα : ∫⁻ t, (α t).toENNReal ∂μ ≠ ⊤ := ne_top_of_le_ne_top hβ hP
    rw [upperIntegral_of_lintegral_ne_top hα, upperIntegral_of_lintegral_ne_top hβ]
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 hP)
      (EReal.coe_ennreal_le_coe_ennreal_iff.2 hN)

theorem upperIntegral_mono {α β : T → EReal} (h : ∀ t, α t ≤ β t) :
    upperIntegral μ α ≤ upperIntegral μ β :=
  upperIntegral_mono_ae (Eventually.of_forall h)

theorem upperIntegral_congr_ae {α β : T → EReal} (h : α =ᵐ[μ] β) :
    upperIntegral μ α = upperIntegral μ β :=
  le_antisymm (upperIntegral_mono_ae (h.mono fun _ ht ↦ ht.le))
    (upperIntegral_mono_ae (h.mono fun _ ht ↦ ht.ge))

end UpperIntegral

section Proposition1458

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The integral functional `I_f[x] = ∫ f(t, x(t)) μ(dt)` with the upper integral. -/
def integralFunctional (μ : Measure T) (f : T → E → EReal) (x : T → E) : EReal :=
  upperIntegral μ fun t ↦ f t (x t)

/-- **Proposition 14.58 (integral functionals)**: for a normal integrand and a measurable `x`,
`t ↦ f(t, x(t))` is measurable, so `I_f[x]` is well defined; and `I_f[x] < ∞` forces
`x(t) ∈ D_f(t)` for `μ`-almost every `t`. -/
theorem integral_functionals {μ : Measure T} {f : T → E → EReal} (hf : IsNormalIntegrand f)
    {x : T → E} (hx : Measurable x) :
    Measurable (fun t ↦ f t (x t)) ∧
      (integralFunctional μ f x < ⊤ → ∀ᵐ t ∂μ, x t ∈ domMapping f t) := by
  refine ⟨hf.measurable_comp hx, fun hI ↦ ?_⟩
  have hP := upperIntegral_lt_top_iff.1 hI
  have hae := ae_lt_top (hf.measurable_comp hx).ereal_toENNReal hP.ne
  filter_upwards [hae] with t ht
  exact lt_top_iff_ne_top.2 (EReal.toENNReal_ne_top_iff.1 ht.ne)

end Proposition1458

section Definition1459

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [MeasurableSpace E]

open scoped Classical in
/-- **Definition 14.59 (decomposable spaces)**: a space `X` of measurable functions `T → E` is
decomposable relative to `μ` if it contains `x₀` modified on any measurable `A` with
`μ(A) < ∞` by any bounded measurable function `x₁`. -/
def IsDecomposable (μ : Measure T) (X : Set (T → E)) : Prop :=
  (∀ x ∈ X, Measurable x) ∧ ∀ x₀ ∈ X, ∀ A : Set T, MeasurableSet A → μ A < ⊤ →
    ∀ x₁ : T → E, Measurable x₁ → (∃ C, ∀ t ∈ A, ‖x₁ t‖ ≤ C) → A.piecewise x₁ x₀ ∈ X

/-- The space `M(T, A; ℝⁿ)` of all measurable functions is decomposable. -/
theorem isDecomposable_measurable (μ : Measure T) :
    IsDecomposable μ {x : T → E | Measurable x} :=
  ⟨fun _ hx ↦ hx, fun _ hx₀ _ hA _ _ hx₁ _ ↦ Measurable.piecewise hA hx₁ hx₀⟩

end Definition1459


section Interchange

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure T}

theorem ereal_toENNReal_max_neg (a : EReal) {r : ℝ} (hr : 0 ≤ r) :
    (max a ((-r : ℝ) : EReal)).toENNReal = a.toENNReal := by
  rcases le_total 0 a with ha | ha
  · rw [max_eq_left (le_trans (EReal.coe_le_coe_iff.2 (by linarith)) ha)]
  · rw [EReal.toENNReal_of_nonpos ha, EReal.toENNReal_of_nonpos (max_le ha
      (EReal.coe_le_coe_iff.2 (by linarith) |>.trans_eq EReal.coe_zero))]

theorem ereal_neg_max (a b : EReal) : -max a b = min (-a) (-b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_right (EReal.neg_le_neg_iff.2 h)]
  · rw [max_eq_left h, min_eq_left (EReal.neg_le_neg_iff.2 h)]

theorem ereal_toENNReal_min (a b : EReal) :
    (min a b).toENNReal = min a.toENNReal b.toENNReal := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (EReal.toENNReal_le_toENNReal h)]
  · rw [min_eq_right h, min_eq_right (EReal.toENNReal_le_toENNReal h)]

theorem ereal_toENNReal_coe_nonneg {r : ℝ} (hr : 0 ≤ r) :
    ((r : ℝ) : EReal).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

/-- The heart of Theorem 14.60 and Exercise 14.61: for a σ-finite measure and a normal integrand,
whenever `∫ inf f(t, ·) < β` there is a measurable `x₁` with `I_f[x₁] < β` (a measurable
selection of the level sets `{x | f(t, x) ≤ max{p(t), -ν} + ψ(t)/(ν + 1)}`). -/
theorem exists_measurable_integralFunctional_lt [SigmaFinite μ] [Nonempty E]
    {f : T → E → EReal} (hf : IsNormalIntegrand f) {β : ℝ}
    (hβ : upperIntegral μ (fun t ↦ ⨅ x, f t x) < β) :
    ∃ x₁ : T → E, Measurable x₁ ∧ integralFunctional μ f x₁ < β := by
  set p : T → EReal := fun t ↦ ⨅ x, f t x with hpdef
  have hp : Measurable p := hf.measurable_iInf
  have hPp : ∫⁻ t, (p t).toENNReal ∂μ ≠ ⊤ :=
    (upperIntegral_lt_top_iff.1 (hβ.trans (EReal.coe_lt_top β))).ne
  obtain ⟨g, hgpos, hgm, hgint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ (ε := 1) one_ne_zero
  set ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hεdef
  have hε : ∀ n, 0 < ε n := fun n ↦ by positivity
  set α : ℕ → T → EReal := fun n t ↦
    max (p t) ((-(n : ℝ) : ℝ) : EReal) + ((ε n * (g t : ℝ) : ℝ) : EReal) with hαdef
  set Pp := ∫⁻ t, (p t).toENNReal ∂μ
  set Np := ∫⁻ t, (-p t).toENNReal ∂μ
  set G := ∫⁻ t, (g t : ℝ≥0∞) ∂μ
  set δ : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (ε n) * G
  set M : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ t, min ((-p t).toENNReal) (n : ℝ≥0∞) ∂μ
  have hgm' : Measurable fun t ↦ (g t : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hgm
  -- (i) positive parts
  have hP : ∀ n, ∫⁻ t, (α n t).toENNReal ∂μ ≤ Pp + δ n := by
    intro n
    have hpt : ∀ t, (α n t).toENNReal ≤ (p t).toENNReal + ENNReal.ofReal (ε n) * (g t : ℝ≥0∞) := by
      intro t
      refine EReal.toENNReal_add_le.trans (le_of_eq ?_)
      rw [ereal_toENNReal_max_neg _ (Nat.cast_nonneg n),
        ereal_toENNReal_coe_nonneg (by have := hε n; positivity),
        ENNReal.ofReal_mul (hε n).le, ENNReal.ofReal_coe_nnreal]
    calc ∫⁻ t, (α n t).toENNReal ∂μ
        ≤ ∫⁻ t, ((p t).toENNReal + ENNReal.ofReal (ε n) * (g t : ℝ≥0∞)) ∂μ := lintegral_mono hpt
      _ = Pp + δ n := by
        rw [lintegral_add_right _ (hgm'.const_mul _), lintegral_const_mul _ hgm']
  -- (ii) negative parts
  have hN : ∀ n, M n ≤ ∫⁻ t, (-α n t).toENNReal ∂μ + δ n := by
    intro n
    have hpt : ∀ t, min ((-p t).toENNReal) (n : ℝ≥0∞) ≤
        (-α n t).toENNReal + ENNReal.ofReal (ε n) * (g t : ℝ≥0∞) := by
      intro t
      have heq : min (-p t) ((n : ℝ) : EReal) =
          -α n t + ((ε n * (g t : ℝ) : ℝ) : EReal) := by
        have h0 : -α n t = min (-p t) ((n : ℝ) : EReal) - ((ε n * (g t : ℝ) : ℝ) : EReal) := by
          simp only [hαdef]
          rw [EReal.neg_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _)),
            ereal_neg_max, ← EReal.coe_neg, neg_neg]
        rw [h0, EReal.sub_add_cancel]
      have h1 : (min (-p t) ((n : ℝ) : EReal)).toENNReal =
          min ((-p t).toENNReal) (n : ℝ≥0∞) := by
        rw [ereal_toENNReal_min, ereal_toENNReal_coe_nonneg (Nat.cast_nonneg n),
          ENNReal.ofReal_natCast]
      rw [← h1, heq]
      refine EReal.toENNReal_add_le.trans (le_of_eq ?_)
      rw [ereal_toENNReal_coe_nonneg (by have := hε n; positivity),
        ENNReal.ofReal_mul (hε n).le, ENNReal.ofReal_coe_nnreal]
    calc M n ≤ ∫⁻ t, ((-α n t).toENNReal + ENNReal.ofReal (ε n) * (g t : ℝ≥0∞)) ∂μ :=
          lintegral_mono hpt
      _ = ∫⁻ t, (-α n t).toENNReal ∂μ + δ n := by
        rw [lintegral_add_right _ (hgm'.const_mul _), lintegral_const_mul _ hgm']
  -- (iii) limits
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr (lt_trans hgint ENNReal.one_lt_top).ne)
    simpa [δ] using h2
  have hM : Tendsto M atTop (𝓝 Np) := by
    have hmono : Monotone fun (n : ℕ) (t : T) ↦ min ((-p t).toENNReal) (n : ℝ≥0∞) := by
      intro m n hmn t
      show min _ (m : ℝ≥0∞) ≤ min _ (n : ℝ≥0∞)
      exact min_le_min le_rfl (Nat.cast_le.2 hmn)
    have hmeas : ∀ n : ℕ, Measurable fun t ↦ min ((-p t).toENNReal) (n : ℝ≥0∞) := fun n ↦
      hp.neg.ereal_toENNReal.min measurable_const
    have hsup : ∀ t, (⨆ n : ℕ, min ((-p t).toENNReal) (n : ℝ≥0∞)) = (-p t).toENNReal := by
      intro t
      refine le_antisymm (iSup_le fun n ↦ min_le_left _ _) ?_
      rcases eq_or_ne ((-p t).toENNReal) ⊤ with h | h
      · rw [h]
        simp only [top_le_iff, min_eq_right le_top]
        exact ENNReal.iSup_natCast
      · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h
        exact le_iSup_of_le n (le_min le_rfl hn.le)
    have := lintegral_iSup (μ := μ) hmeas hmono
    simp only [hsup] at this
    rw [show Np = ∫⁻ t, (-p t).toENNReal ∂μ from rfl, this]
    exact tendsto_atTop_iSup fun m n hmn ↦ lintegral_mono fun t ↦ hmono hmn t
  have hδfin : ∀ n, δ n ≠ ⊤ := fun n ↦
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lt_trans hgint ENNReal.one_lt_top).ne
  -- (iv) the bound tends to `∫ p`
  have hlim : Tendsto (fun n ↦ ((Pp + δ n : ℝ≥0∞) : EReal) - ((M n - δ n : ℝ≥0∞) : EReal))
      atTop (𝓝 ((Pp : EReal) - (Np : EReal))) := by
    have h1 : Tendsto (fun n ↦ Pp + δ n) atTop (𝓝 Pp) := by
      simpa using tendsto_const_nhds.add hδ
    have h2 : Tendsto (fun n ↦ M n - δ n) atTop (𝓝 Np) := by
      simpa using ENNReal.Tendsto.sub hM hδ (Or.inr ENNReal.zero_ne_top)
    have h1' := (continuous_coe_ennreal_ereal.tendsto _).comp h1
    have h2' := (continuous_neg.tendsto _).comp ((continuous_coe_ennreal_ereal.tendsto _).comp h2)
    have h3 := h1'.prodMk_nhds h2'
    have hcont : ContinuousAt (fun q : EReal × EReal ↦ q.1 + q.2) ((Pp : EReal), -(Np : EReal)) :=
      EReal.continuousAt_add (Or.inl fun h ↦ hPp (EReal.coe_ennreal_eq_top_iff.1 h))
        (Or.inl (EReal.coe_ennreal_ne_bot _))
    have := hcont.tendsto.comp h3
    simpa [Function.comp_def, sub_eq_add_neg] using this
  have hlt : (Pp : EReal) - (Np : EReal) < β := by
    rw [← upperIntegral_of_lintegral_ne_top hPp]
    exact hβ
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hlt)).exists
  have hIα : upperIntegral μ (α n) < β := by
    have hPn : ∫⁻ t, (α n t).toENNReal ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hPp, hδfin n⟩) (hP n)
    rw [upperIntegral_of_lintegral_ne_top hPn]
    refine lt_of_le_of_lt ?_ hn
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.2 (hP n))
      (EReal.coe_ennreal_le_coe_ennreal_iff.2 (tsub_le_iff_right.2 (hN n)))
  -- (v) a measurable selection of the level sets
  have hαm : Measurable (α n) :=
    (hp.max measurable_const).add (measurable_const.mul (measurable_coe_nnreal_real.comp hgm)).coe_real_ereal
  obtain ⟨hLc, hLm⟩ := hf.levelSet_measurable_ereal hαm
  have hne : ∀ t, t ∈ svDom (fun t ↦ {x | f t x ≤ α n t}) := by
    intro t
    obtain ⟨x₀⟩ := ‹Nonempty E›
    by_cases hpt : p t = ⊤
    · refine ⟨x₀, ?_⟩
      have hα : α n t = ⊤ := by
        simp only [hαdef, hpt, max_eq_left le_top]
        exact EReal.top_add_coe _
      simp [hα]
    · set m := max (p t) ((-(n : ℝ) : ℝ) : EReal) with hm
      have hmtop : m ≠ ⊤ := max_ne_top hpt (EReal.coe_ne_top _)
      have hmbot : m ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
      have hlt : p t < α n t := by
        have hpos : 0 < ε n * (g t : ℝ) := mul_pos (hε n) (by exact_mod_cast hgpos t)
        calc p t ≤ m := le_max_left _ _
          _ = ((m.toReal : ℝ) : EReal) := (EReal.coe_toReal hmtop hmbot).symm
          _ < ((m.toReal + ε n * (g t : ℝ) : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)
          _ = α n t := by
            simp only [hαdef]
            rw [EReal.coe_add, EReal.coe_toReal hmtop hmbot]
      obtain ⟨x, hx⟩ := iInf_lt_iff.1 hlt
      exact ⟨x, hx.le⟩
  obtain ⟨x₁, hx₁m, hx₁⟩ := hLm.exists_measurable_selection hLc
  exact ⟨x₁, hx₁m, lt_of_le_of_lt (upperIntegral_mono fun t ↦ hx₁ t (hne t)) hIα⟩


/-- The decomposition step of Theorem 14.60: modifying `x₀` (with `I_f[x₀] < ∞`) by `x₁` on
large sets of finite measure on which `x₁` is bounded brings `I_f` below any `β > I_f[x₁]`. -/
theorem exists_mem_integralFunctional_lt_of_decomposable [SigmaFinite μ] {f : T → E → EReal}
    (hf : IsNormalIntegrand f) {X : Set (T → E)} (hX : IsDecomposable μ X)
    {x₀ : T → E} (hx₀ : x₀ ∈ X) (hI₀ : integralFunctional μ f x₀ < ⊤)
    {x₁ : T → E} (hx₁ : Measurable x₁) {β : ℝ} (hI₁ : integralFunctional μ f x₁ < β) :
    ∃ x ∈ X, integralFunctional μ f x < β := by
  classical
  set g₀ : T → EReal := fun t ↦ f t (x₀ t) with hg₀def
  set g₁ : T → EReal := fun t ↦ f t (x₁ t) with hg₁def
  have hg₀ : Measurable g₀ := hf.measurable_comp (hX.1 x₀ hx₀)
  have hg₁ : Measurable g₁ := hf.measurable_comp hx₁
  set A : ℕ → Set T := fun ν ↦ spanningSets μ ν ∩ {t | ‖x₁ t‖ ≤ ν} with hAdef
  have hAm : ∀ ν, MeasurableSet (A ν) := fun ν ↦
    (measurableSet_spanningSets μ ν).inter (measurableSet_le hx₁.norm measurable_const)
  have hAmono : Monotone A := fun m n hmn ↦
    inter_subset_inter (monotone_spanningSets μ hmn) fun t (ht : ‖x₁ t‖ ≤ m) ↦
      show ‖x₁ t‖ ≤ n from le_trans ht (Nat.cast_le.2 hmn)
  have hAunion : ⋃ ν, A ν = univ := by
    refine eq_univ_of_forall fun t ↦ ?_
    obtain ⟨ν₁, hν₁⟩ := mem_iUnion.1 ((iUnion_spanningSets μ).symm ▸ mem_univ t :
      t ∈ ⋃ i, spanningSets μ i)
    obtain ⟨ν₂, hν₂⟩ := exists_nat_ge ‖x₁ t‖
    refine mem_iUnion.2 ⟨max ν₁ ν₂, monotone_spanningSets μ (le_max_left _ _) hν₁, ?_⟩
    show ‖x₁ t‖ ≤ ((max ν₁ ν₂ : ℕ) : ℝ)
    exact hν₂.trans (Nat.cast_le.2 (le_max_right _ _))
  have hAfin : ∀ ν, μ (A ν) < ⊤ := fun ν ↦
    (measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ ν)
  obtain ⟨xs, hxsdef⟩ : ∃ xs : ℕ → T → E, xs = fun ν ↦ (A ν).piecewise x₁ x₀ := ⟨_, rfl⟩
  have hxs : ∀ ν, xs ν ∈ X := fun ν ↦ by
    rw [hxsdef]
    convert hX.2 x₀ hx₀ (A ν) (hAm ν) (hAfin ν) x₁ hx₁ ⟨ν, fun t ht ↦ ht.2⟩ using 1
    funext t
    simp only [Set.piecewise]
    congr 1
  set P₀ := ∫⁻ t, (g₀ t).toENNReal ∂μ
  set P₁ := ∫⁻ t, (g₁ t).toENNReal ∂μ
  set N₁ := ∫⁻ t, (-g₁ t).toENNReal ∂μ
  have hP₀ : P₀ ≠ ⊤ := (upperIntegral_lt_top_iff.1 hI₀).ne
  have hP₁ : P₁ ≠ ⊤ := (upperIntegral_lt_top_iff.1 (hI₁.trans (EReal.coe_lt_top β))).ne
  have hsplit : ∀ ν, ∫⁻ t, (f t (xs ν t)).toENNReal ∂μ =
      (∫⁻ t in A ν, (g₁ t).toENNReal ∂μ) + ∫⁻ t in (A ν)ᶜ, (g₀ t).toENNReal ∂μ := by
    intro ν
    rw [← lintegral_add_compl _ (hAm ν)]
    congr 1
    · exact setLIntegral_congr_fun (hAm ν) fun t ht ↦ by
        simp only [hxsdef, Set.piecewise_eq_of_mem _ _ _ ht, hg₁def]
    · exact setLIntegral_congr_fun (hAm ν).compl fun t ht ↦ by
        simp only [hxsdef, Set.piecewise_eq_of_notMem _ _ _ ht, hg₀def]
  have hsplitN : ∀ ν, ∫⁻ t in A ν, (-g₁ t).toENNReal ∂μ ≤
      ∫⁻ t, (-f t (xs ν t)).toENNReal ∂μ := by
    intro ν
    calc ∫⁻ t in A ν, (-g₁ t).toENNReal ∂μ
        = ∫⁻ t in A ν, (-f t (xs ν t)).toENNReal ∂μ :=
          setLIntegral_congr_fun (hAm ν) fun t ht ↦ by
            simp only [hxsdef, Set.piecewise_eq_of_mem _ _ _ ht, hg₁def]
      _ ≤ ∫⁻ t, (-f t (xs ν t)).toENNReal ∂μ := setLIntegral_le_lintegral _ _
  have hup : ∀ h : T → ℝ≥0∞, Tendsto (fun ν ↦ ∫⁻ t in A ν, h t ∂μ) atTop
      (𝓝 (∫⁻ t, h t ∂μ)) := by
    intro h
    have := tendsto_measure_iUnion_atTop (μ := μ.withDensity h) hAmono
    rw [hAunion, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    convert this using 1
    funext ν
    simp only [Function.comp_apply]
    rw [withDensity_apply _ (hAm ν)]
  have hlim0 : Tendsto (fun ν ↦ ∫⁻ t in (A ν)ᶜ, (g₀ t).toENNReal ∂μ) atTop (𝓝 0) := by
    have hanti : Antitone fun ν ↦ (A ν)ᶜ := fun m n hmn ↦ compl_subset_compl.2 (hAmono hmn)
    have hfin : μ.withDensity (fun t ↦ (g₀ t).toENNReal) (A 0)ᶜ ≠ ⊤ := by
      rw [withDensity_apply _ (hAm 0).compl]
      exact ne_top_of_le_ne_top hP₀ (setLIntegral_le_lintegral _ _)
    have := tendsto_measure_iInter_atTop (μ := μ.withDensity fun t ↦ (g₀ t).toENNReal)
      (fun ν ↦ (hAm ν).compl.nullMeasurableSet) hanti ⟨0, hfin⟩
    rw [← compl_iUnion, hAunion, compl_univ, measure_empty] at this
    convert this using 1
    funext ν
    simp only [Function.comp_apply]
    rw [withDensity_apply _ (hAm ν).compl]
  have hlimB : Tendsto (fun ν ↦ ((∫⁻ t in A ν, (g₁ t).toENNReal ∂μ +
      ∫⁻ t in (A ν)ᶜ, (g₀ t).toENNReal ∂μ : ℝ≥0∞) : EReal) -
        ((∫⁻ t in A ν, (-g₁ t).toENNReal ∂μ : ℝ≥0∞) : EReal)) atTop
      (𝓝 ((P₁ : EReal) - (N₁ : EReal))) := by
    have h1 : Tendsto (fun ν ↦ ∫⁻ t in A ν, (g₁ t).toENNReal ∂μ +
        ∫⁻ t in (A ν)ᶜ, (g₀ t).toENNReal ∂μ) atTop (𝓝 P₁) := by
      simpa using (hup fun t ↦ (g₁ t).toENNReal).add hlim0
    have h1' := (continuous_coe_ennreal_ereal.tendsto _).comp h1
    have h2' := (continuous_neg.tendsto _).comp
      ((continuous_coe_ennreal_ereal.tendsto _).comp (hup fun t ↦ (-g₁ t).toENNReal))
    have h3 := h1'.prodMk_nhds h2'
    have hcont : ContinuousAt (fun q : EReal × EReal ↦ q.1 + q.2) ((P₁ : EReal), -(N₁ : EReal)) :=
      EReal.continuousAt_add (Or.inl fun h ↦ hP₁ (EReal.coe_ennreal_eq_top_iff.1 h))
        (Or.inl (EReal.coe_ennreal_ne_bot _))
    have := hcont.tendsto.comp h3
    simpa [Function.comp_def, sub_eq_add_neg] using this
  have hlt : (P₁ : EReal) - (N₁ : EReal) < β := by
    rw [← upperIntegral_of_lintegral_ne_top hP₁]
    exact hI₁
  obtain ⟨ν, hν⟩ := (hlimB.eventually (gt_mem_nhds hlt)).exists
  refine ⟨xs ν, hxs ν, ?_⟩
  have hPν : ∫⁻ t, (f t (xs ν t)).toENNReal ∂μ ≠ ⊤ := by
    rw [hsplit]
    exact ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top hP₁ (setLIntegral_le_lintegral _ _),
      ne_top_of_le_ne_top hP₀ (setLIntegral_le_lintegral _ _)⟩
  unfold integralFunctional
  rw [upperIntegral_of_lintegral_ne_top hPν, hsplit ν]
  exact lt_of_le_of_lt (EReal.sub_le_sub le_rfl
    (EReal.coe_ennreal_le_coe_ennreal_iff.2 (hsplitN ν))) hν

theorem ereal_eq_of_toENNReal_eq {x y : EReal} (h₁ : x.toENNReal = y.toENNReal)
    (h₂ : (-x).toENNReal = (-y).toENNReal) : x = y := by
  rcases lt_trichotomy 0 x with hx | rfl | hx
  · have hy : 0 < y := EReal.toENNReal_pos_iff.1 (h₁ ▸ EReal.toENNReal_pos_iff.2 hx)
    exact (EReal.toENNReal_eq_toENNReal hx.le hy.le).1 h₁
  · rw [EReal.toENNReal_zero, eq_comm, EReal.toENNReal_eq_zero_iff] at h₁
    rw [neg_zero, EReal.toENNReal_zero, eq_comm, EReal.toENNReal_eq_zero_iff] at h₂
    have h₂' : (0 : EReal) ≤ y := EReal.neg_le_neg_iff.1 (by simpa using h₂)
    exact (le_antisymm h₁ h₂').symm
  · have hx' : 0 < -x := EReal.neg_pos.2 hx
    have hy' : 0 < -y := EReal.toENNReal_pos_iff.1 (h₂ ▸ EReal.toENNReal_pos_iff.2 hx')
    have := (EReal.toENNReal_eq_toENNReal hx'.le hy'.le).1 h₂
    exact neg_injective this

/-- If `a ≤ b` and both have the same finite upper integral, then `a = b` almost everywhere. -/
theorem ae_eq_of_le_of_upperIntegral_eq {a b : T → EReal} (ha : Measurable a)
    (hb : Measurable b) (hab : ∀ t, a t ≤ b t) (heq : upperIntegral μ a = upperIntegral μ b)
    (hbot : upperIntegral μ a ≠ ⊥) (htop : upperIntegral μ b ≠ ⊤) : a =ᵐ[μ] b := by
  have hPle : ∫⁻ t, (a t).toENNReal ∂μ ≤ ∫⁻ t, (b t).toENNReal ∂μ :=
    lintegral_mono fun t ↦ EReal.toENNReal_le_toENNReal (hab t)
  have hNle : ∫⁻ t, (-b t).toENNReal ∂μ ≤ ∫⁻ t, (-a t).toENNReal ∂μ :=
    lintegral_mono fun t ↦ EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (hab t))
  have hPb : ∫⁻ t, (b t).toENNReal ∂μ ≠ ⊤ := (upperIntegral_lt_top_iff.1 (lt_top_iff_ne_top.2 htop)).ne
  have hPa : ∫⁻ t, (a t).toENNReal ∂μ ≠ ⊤ := ne_top_of_le_ne_top hPb hPle
  rw [upperIntegral_of_lintegral_ne_top hPa] at heq hbot
  rw [upperIntegral_of_lintegral_ne_top hPb] at heq
  have hNa : ∫⁻ t, (-a t).toENNReal ∂μ ≠ ⊤ := by
    intro h
    rw [h, EReal.coe_ennreal_top, EReal.sub_top] at hbot
    exact hbot rfl
  have hNb : ∫⁻ t, (-b t).toENNReal ∂μ ≠ ⊤ := ne_top_of_le_ne_top hNa hNle
  have hreal := congrArg EReal.toReal heq
  have ne_top : ∀ {z : ℝ≥0∞}, z ≠ ⊤ → (z : EReal) ≠ ⊤ := fun hz h ↦
    hz (EReal.coe_ennreal_eq_top_iff.1 h)
  rw [EReal.toReal_sub (ne_top hPa) (EReal.coe_ennreal_ne_bot _)
      (ne_top hNa) (EReal.coe_ennreal_ne_bot _),
    EReal.toReal_sub (ne_top hPb) (EReal.coe_ennreal_ne_bot _)
      (ne_top hNb) (EReal.coe_ennreal_ne_bot _)] at hreal
  simp only [EReal.toReal_coe_ennreal] at hreal
  have h1 := (ENNReal.toReal_le_toReal hPa hPb).2 hPle
  have h2 := (ENNReal.toReal_le_toReal hNb hNa).2 hNle
  have hPeq : ∫⁻ t, (b t).toENNReal ∂μ ≤ ∫⁻ t, (a t).toENNReal ∂μ :=
    (ENNReal.toReal_le_toReal hPb hPa).1 (by linarith)
  have hNeq : ∫⁻ t, (-a t).toENNReal ∂μ ≤ ∫⁻ t, (-b t).toENNReal ∂μ :=
    (ENNReal.toReal_le_toReal hNa hNb).1 (by linarith)
  have hpos := ae_eq_of_ae_le_of_lintegral_le (Eventually.of_forall fun t ↦
    EReal.toENNReal_le_toENNReal (hab t)) hPa hb.ereal_toENNReal.aemeasurable hPeq
  have hneg := ae_eq_of_ae_le_of_lintegral_le (Eventually.of_forall fun t ↦
    EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.2 (hab t))) hNb
    ha.neg.ereal_toENNReal.aemeasurable hNeq
  filter_upwards [hpos, hneg] with t h1 h2
  exact ereal_eq_of_toENNReal_eq h1 h2.symm


/-- The minimizer characterization shared by Theorem 14.60 and Exercise 14.61. -/
theorem argmin_characterization_of_interchange {f : T → E → EReal} (hf : IsNormalIntegrand f)
    {X : Set (T → E)} (hX : ∀ x ∈ X, Measurable x)
    (heq : (⨅ x ∈ X, integralFunctional μ f x) = upperIntegral μ (fun t ↦ ⨅ x, f t x))
    (hbot : upperIntegral μ (fun t ↦ ⨅ x, f t x) ≠ ⊥)
    (htop : upperIntegral μ (fun t ↦ ⨅ x, f t x) ≠ ⊤) {xbar : T → E} (hxbar : xbar ∈ X) :
    integralFunctional μ f xbar = (⨅ x ∈ X, integralFunctional μ f x) ↔
      ∀ᵐ t ∂μ, xbar t ∈ argmin (f t) := by
  set p : T → EReal := fun t ↦ ⨅ x, f t x with hpdef
  have hp : Measurable p := hf.measurable_iInf
  have hptop : ∀ᵐ t ∂μ, p t < ⊤ := by
    have hP := upperIntegral_lt_top_iff.1 (lt_top_iff_ne_top.2 htop)
    filter_upwards [ae_lt_top hp.ereal_toENNReal hP.ne] with t ht
    exact lt_top_iff_ne_top.2 (EReal.toENNReal_ne_top_iff.1 ht.ne)
  rw [heq]
  constructor
  · intro hI
    have htop' : upperIntegral μ (fun t ↦ f t (xbar t)) ≠ ⊤ := by
      change integralFunctional μ f xbar ≠ ⊤
      rw [hI]
      exact htop
    have hae := ae_eq_of_le_of_upperIntegral_eq hp (hf.measurable_comp (hX xbar hxbar))
      (fun t ↦ iInf_le _ (xbar t)) hI.symm hbot htop'
    filter_upwards [hae, hptop] with t h1 h2
    exact (mem_argmin_iff _ _).2 ⟨h1.symm, h2⟩
  · intro hae
    refine upperIntegral_congr_ae ?_
    filter_upwards [hae] with t ht
    exact ((mem_argmin_iff _ _).1 ht).1

/-- **Theorem 14.60 (interchange of minimization and integration)**: for a decomposable space `X`
of measurable functions, a σ-finite `μ` and a normal integrand `f` with `I_f ≢ ∞` on `X`,
`inf_{x ∈ X} ∫ f(t, x(t)) μ(dt) = ∫ inf_x f(t, x) μ(dt)`; and when this common value is not `-∞`,
`xbar ∈ X` minimizes `I_f` over `X` if and only if `xbar(t) ∈ argmin f(t, ·)` for `μ`-a.e. `t`. -/
theorem interchange_of_minimization_and_integration [SigmaFinite μ] [Nonempty E]
    {X : Set (T → E)} (hX : IsDecomposable μ X) {f : T → E → EReal} (hf : IsNormalIntegrand f)
    (hfin : ∃ x₀ ∈ X, integralFunctional μ f x₀ < ⊤) :
    (⨅ x ∈ X, integralFunctional μ f x) = upperIntegral μ (fun t ↦ ⨅ x, f t x) ∧
      (upperIntegral μ (fun t ↦ ⨅ x, f t x) ≠ ⊥ → ∀ xbar ∈ X,
        (integralFunctional μ f xbar = (⨅ x ∈ X, integralFunctional μ f x) ↔
          ∀ᵐ t ∂μ, xbar t ∈ argmin (f t))) := by
  obtain ⟨x₀, hx₀, hI₀⟩ := hfin
  have hge : ∀ x ∈ X, upperIntegral μ (fun t ↦ ⨅ x, f t x) ≤ integralFunctional μ f x :=
    fun x _ ↦ upperIntegral_mono fun t ↦ iInf_le _ (x t)
  have heq : (⨅ x ∈ X, integralFunctional μ f x) = upperIntegral μ (fun t ↦ ⨅ x, f t x) := by
    refine le_antisymm ?_ (le_iInf₂ hge)
    by_contra h
    push_neg at h
    obtain ⟨β, hβ1, hβ2⟩ := EReal.exists_between_coe_real h
    obtain ⟨x₁, hx₁, hI₁⟩ := exists_measurable_integralFunctional_lt hf hβ1
    obtain ⟨x, hxX, hIx⟩ := exists_mem_integralFunctional_lt_of_decomposable hf hX hx₀ hI₀ hx₁ hI₁
    exact absurd (lt_of_lt_of_le hβ2 ((iInf₂_le x hxX).trans_lt hIx).le) (lt_irrefl _)
  refine ⟨heq, fun hbot xbar hxbar ↦ ?_⟩
  have htop : upperIntegral μ (fun t ↦ ⨅ x, f t x) ≠ ⊤ :=
    (lt_of_le_of_lt (heq ▸ iInf₂_le x₀ hx₀) hI₀).ne
  exact argmin_characterization_of_interchange hf hX.1 heq hbot htop hxbar

/-- **Exercise 14.61 (simplified interchange criterion)**: for σ-finite `μ` and a normal integrand
`f`, the conclusions of Theorem 14.60 hold for every space `X` with `M_f ⊂ X ⊂ M(T, A; ℝⁿ)`,
where `M_f` consists of the measurable `x` with `I_f[x] < ∞` (the inf-formula needs no
assumption that `I_f ≢ ∞` on `X`). -/
theorem simplified_interchange_criterion [SigmaFinite μ] [Nonempty E] {f : T → E → EReal}
    (hf : IsNormalIntegrand f) {X : Set (T → E)}
    (hX₁ : ∀ x : T → E, Measurable x → integralFunctional μ f x < ⊤ → x ∈ X)
    (hX₂ : ∀ x ∈ X, Measurable x) :
    (⨅ x ∈ X, integralFunctional μ f x) = upperIntegral μ (fun t ↦ ⨅ x, f t x) ∧
      ((∃ x₀ ∈ X, integralFunctional μ f x₀ < ⊤) →
        upperIntegral μ (fun t ↦ ⨅ x, f t x) ≠ ⊥ → ∀ xbar ∈ X,
          (integralFunctional μ f xbar = (⨅ x ∈ X, integralFunctional μ f x) ↔
            ∀ᵐ t ∂μ, xbar t ∈ argmin (f t))) := by
  have hge : ∀ x ∈ X, upperIntegral μ (fun t ↦ ⨅ x, f t x) ≤ integralFunctional μ f x :=
    fun x _ ↦ upperIntegral_mono fun t ↦ iInf_le _ (x t)
  have heq : (⨅ x ∈ X, integralFunctional μ f x) = upperIntegral μ (fun t ↦ ⨅ x, f t x) := by
    refine le_antisymm ?_ (le_iInf₂ hge)
    by_contra h
    push_neg at h
    obtain ⟨β, hβ1, hβ2⟩ := EReal.exists_between_coe_real h
    obtain ⟨x₁, hx₁, hI₁⟩ := exists_measurable_integralFunctional_lt hf hβ1
    have hx₁X := hX₁ x₁ hx₁ (hI₁.trans (EReal.coe_lt_top β))
    exact absurd (lt_of_lt_of_le hβ2 ((iInf₂_le x₁ hx₁X).trans_lt hI₁).le) (lt_irrefl _)
  refine ⟨heq, fun ⟨x₀, hx₀, hI₀⟩ hbot xbar hxbar ↦ ?_⟩
  have htop : upperIntegral μ (fun t ↦ ⨅ x, f t x) ≠ ⊤ :=
    (lt_of_le_of_lt (heq ▸ iInf₂_le x₀ hx₀) hI₀).ne
  exact argmin_characterization_of_interchange hf hX₂ heq hbot htop hxbar

end Interchange


section Example1462

variable {T E G : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] {μ : Measure T}

theorem infAddition_iInf {ι : Sort*} (a : EReal) (b : ι → EReal) :
    infAddition a (⨅ i, b i) = ⨅ i, infAddition a (b i) := by
  by_cases htop : a = ⊤
  · simp [infAddition, htop]
  by_cases hbot : a = ⊥
  · subst hbot
    by_cases hall : ∀ i, b i = ⊤
    · have : (⨅ i, b i) = ⊤ := iInf_eq_top.2 hall
      simp [infAddition, this, hall]
    · push_neg at hall
      obtain ⟨i, hi⟩ := hall
      have hinf : (⨅ i, b i) ≠ ⊤ := ne_top_of_le_ne_top hi (iInf_le _ i)
      have h1 : infAddition ⊥ (⨅ i, b i) = ⊥ := by simp [infAddition, hinf]
      rw [h1, eq_comm, eq_bot_iff]
      refine (iInf_le _ i).trans ?_
      simp [infAddition, hi]
  · have hfin : ∀ c : EReal, infAddition a c = c + ((a.toReal : ℝ) : EReal) := by
      intro c
      rw [EReal.coe_toReal htop hbot, add_comm]
      by_cases hc : c = ⊤
      · simp [infAddition, hc, EReal.add_top_of_ne_bot hbot]
      · simp [infAddition, htop, hc]
    simp only [hfin]
    exact (erealAddRightOrderIso a.toReal).map_iInf b


omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G]
  [MeasurableSpace G] [BorelSpace G] in
theorem integralFunctional_pair (g : T → E × G → EReal) (x : T → E) (u : T → G) :
    integralFunctional μ g (fun t ↦ (x t, u t)) =
      integralFunctional μ (fun t v ↦ g t (x t, v)) u := rfl

/-- The inner interchange of Example 14.62 for a fixed `x`. -/
theorem iInf_infAddition_integralFunctional_pair [SigmaFinite μ] [Nonempty G]
    {g : T → E × G → EReal}
    (hg : IsNormalIntegrand g) {U : Set (T → G)} (hU : IsDecomposable μ U) (J : EReal)
    {x : T → E} (hx : Measurable x)
    (hH : J < ⊤ → integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x < ⊤ →
      ∃ u ∈ U, integralFunctional μ g (fun t ↦ (x t, u t)) < ⊤) :
    (⨅ u ∈ U, infAddition J (integralFunctional μ g (fun t ↦ (x t, u t)))) =
      infAddition J (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x) := by
  have hh : IsNormalIntegrand (fun t v ↦ g t (x t, v)) :=
    hg.comp_caratheodory (F := fun t v ↦ (x t, v))
      ⟨fun v ↦ hx.prodMk measurable_const, fun t ↦ continuous_const.prodMk continuous_id⟩
  by_cases hex : ∃ u₀ ∈ U, integralFunctional μ g (fun t ↦ (x t, u₀ t)) < ⊤
  · obtain ⟨u₀, hu₀, hI₀⟩ := hex
    have h := (interchange_of_minimization_and_integration hU hh ⟨u₀, hu₀, hI₀⟩).1
    have h' : (⨅ u ∈ U, integralFunctional μ g (fun t ↦ (x t, u t))) =
        integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x := h
    rw [← h']
    simp only [infAddition_iInf]
  · push_neg at hex
    have hall : ∀ u ∈ U, integralFunctional μ g (fun t ↦ (x t, u t)) = ⊤ := fun u hu ↦
      top_le_iff.1 (hex u hu)
    have hlhs : (⨅ u ∈ U, infAddition J (integralFunctional μ g (fun t ↦ (x t, u t)))) = ⊤ := by
      refine iInf₂_eq_top.2 fun u hu ↦ ?_
      simp [infAddition, hall u hu]
    rw [hlhs, eq_comm]
    by_cases hJ : J = ⊤
    · simp [infAddition, hJ]
    · have hI : integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x = ⊤ := by
        by_contra hne
        obtain ⟨u, hu, hlt⟩ := hH (lt_top_iff_ne_top.2 hJ) (lt_top_iff_ne_top.2 hne)
        exact absurd (hall u hu) hlt.ne
      simp [infAddition, hI]


theorem infAddition_mono_right (a : EReal) {b c : EReal} (h : b ≤ c) :
    infAddition a b ≤ infAddition a c := by
  unfold infAddition
  by_cases ha : a = ⊤
  · simp [ha]
  by_cases hc : c = ⊤
  · simp [hc]
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top hc h
  simp only [ha, hb, hc, or_self, if_false]
  exact add_le_add le_rfl h

theorem infAddition_finite_of_bot_lt_of_lt_top {a b : EReal} (h1 : ⊥ < infAddition a b)
    (h2 : infAddition a b < ⊤) : a ≠ ⊤ ∧ a ≠ ⊥ ∧ b ≠ ⊤ ∧ b ≠ ⊥ ∧ infAddition a b = a + b := by
  have ha : a ≠ ⊤ := fun h ↦ by simp [infAddition, h] at h2
  have hb : b ≠ ⊤ := fun h ↦ by simp [infAddition, h] at h2
  have hab : infAddition a b = a + b := by simp [infAddition, ha, hb]
  rw [hab] at h1
  exact ⟨ha, fun h ↦ by simp [h] at h1, hb, fun h ↦ by simp [h] at h1, hab⟩

/-- **Example 14.62 (reduced optimization)**, corrected.  For a σ-finite `μ`, a normal integrand
`g : T × (ℝⁿ × ℝᵐ) → ℝ̄` with `f(t, x) = inf_u g(t, x, u)` lsc in `x`, a decomposable `U`, any `X`
and any `J`, problem (P) `inf J[x] + I_g[x, u]` (inf-addition) equals (P') `inf J[x] + I_f[x]`,
and when this value is finite, `(x̄, ū)` solves (P) iff `x̄` solves (P') and
`ū(t) ∈ argmin g(t, x̄(t), ·)` a.e.  The extra hypothesis `hH` (for every `x ∈ X` with
`J[x] < ∞` and `I_f[x] < ∞` some `u ∈ U` has `I_g[x, u] < ∞`, automatic e.g. for
`U = M(T, A; ℝᵐ)`, see `reduced_optimization_measurable`) replaces the book's `inf(P) < ∞`, which
does not suffice: with `T = ℕ`, counting measure, `U = ℓ^∞`, `X = {0, 1}`, `J = 0`,
`g(t, x, u) = |u - xt| + |1 - x| 2^{-t-1}`, one has `inf(P) = 1` but `inf(P') = 0`
(`RW.reduced_optimization_counterexample` in `ReducedOptimizationCounterexample`). -/
theorem reduced_optimization [SigmaFinite μ] [Nonempty G] {g : T → E × G → EReal}
    (hg : IsNormalIntegrand g) (hflsc : ∀ t, LowerSemicontinuous fun y ↦ ⨅ v, g t (y, v))
    {X : Set (T → E)} (hX : ∀ x ∈ X, Measurable x) {U : Set (T → G)}
    (hU : IsDecomposable μ U) (J : (T → E) → EReal)
    (hH : ∀ x ∈ X, J x < ⊤ → integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x < ⊤ →
      ∃ u ∈ U, integralFunctional μ g (fun t ↦ (x t, u t)) < ⊤) :
    IsNormalIntegrand (fun t y ↦ ⨅ v, g t (y, v)) ∧
      (⨅ x ∈ X, ⨅ u ∈ U, infAddition (J x) (integralFunctional μ g (fun t ↦ (x t, u t)))) =
        (⨅ x ∈ X, infAddition (J x) (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x)) ∧
      (⊥ < (⨅ x ∈ X, infAddition (J x) (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x)) →
        (⨅ x ∈ X, infAddition (J x) (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x)) < ⊤ →
        ∀ xbar ∈ X, ∀ ubar ∈ U,
          (infAddition (J xbar) (integralFunctional μ g (fun t ↦ (xbar t, ubar t))) =
              (⨅ x ∈ X, ⨅ u ∈ U, infAddition (J x) (integralFunctional μ g (fun t ↦ (x t, u t)))) ↔
            infAddition (J xbar) (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) xbar) =
                (⨅ x ∈ X, infAddition (J x) (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x)) ∧
              ∀ᵐ t ∂μ, ubar t ∈ argmin (fun v ↦ g t (xbar t, v)))) := by
  set f : T → E → EReal := fun t y ↦ ⨅ v, g t (y, v) with hfdef
  have hf : IsNormalIntegrand f := by
    have hswap : IsNormalIntegrand (fun t (q : G × E) ↦ g t (q.2, q.1)) :=
      hg.comp_caratheodory (F := fun (_ : T) (q : G × E) ↦ (q.2, q.1))
        ⟨fun _ ↦ measurable_const, fun _ ↦ continuous_snd.prodMk continuous_fst⟩
    have h := hswap.valueFunction_of_lowerSemicontinuous (fun t ↦ hflsc t)
    exact h
  have heq : (⨅ x ∈ X, ⨅ u ∈ U, infAddition (J x) (integralFunctional μ g (fun t ↦ (x t, u t)))) =
      (⨅ x ∈ X, infAddition (J x) (integralFunctional μ f x)) :=
    iInf_congr fun x ↦ iInf_congr fun hx ↦
      iInf_infAddition_integralFunctional_pair hg hU (J x) (hX x hx) (hH x hx)
  refine ⟨hf, heq, fun hbot htop xbar hxbar ubar hubar ↦ ?_⟩
  rw [heq]
  have hFle : infAddition (J xbar) (integralFunctional μ f xbar) ≤
      infAddition (J xbar) (integralFunctional μ g (fun t ↦ (xbar t, ubar t))) :=
    infAddition_mono_right _ (upperIntegral_mono fun t ↦ iInf_le _ (ubar t))
  have hinfF : (⨅ x ∈ X, infAddition (J x) (integralFunctional μ f x)) ≤
      infAddition (J xbar) (integralFunctional μ f xbar) := iInf₂_le xbar hxbar
  constructor
  · intro hG
    have hFeq : infAddition (J xbar) (integralFunctional μ f xbar) =
        (⨅ x ∈ X, infAddition (J x) (integralFunctional μ f x)) :=
      le_antisymm (hFle.trans hG.le) hinfF
    refine ⟨hFeq, ?_⟩
    obtain ⟨hJt, hJb, hGt, -, hGsum⟩ := infAddition_finite_of_bot_lt_of_lt_top
      (hG ▸ hbot : ⊥ < infAddition (J xbar) (integralFunctional μ g (fun t ↦ (xbar t, ubar t))))
      (hG ▸ htop)
    obtain ⟨-, -, -, hFb, hFsum⟩ := infAddition_finite_of_bot_lt_of_lt_top
      (hFeq ▸ hbot : ⊥ < infAddition (J xbar) (integralFunctional μ f xbar)) (hFeq ▸ htop)
    have hIeq : integralFunctional μ g (fun t ↦ (xbar t, ubar t)) = integralFunctional μ f xbar := by
      have h1 : J xbar + integralFunctional μ g (fun t ↦ (xbar t, ubar t)) =
          J xbar + integralFunctional μ f xbar := by rw [← hGsum, ← hFsum, hG, hFeq]
      have hJ : J xbar = ((J xbar).toReal : EReal) := (EReal.coe_toReal hJt hJb).symm
      rw [hJ] at h1
      have := congrArg (fun z ↦ z - ((J xbar).toReal : EReal)) h1
      simpa only [add_comm ((J xbar).toReal : EReal), EReal.add_sub_cancel_right] using this
    have hh : IsNormalIntegrand (fun t v ↦ g t (xbar t, v)) :=
      hg.comp_caratheodory (F := fun t v ↦ (xbar t, v))
        ⟨fun v ↦ (hX xbar hxbar).prodMk measurable_const,
          fun t ↦ continuous_const.prodMk continuous_id⟩
    have hint := interchange_of_minimization_and_integration hU hh
      ⟨ubar, hubar, lt_top_iff_ne_top.2 hGt⟩
    have hcommon : upperIntegral μ (fun t ↦ ⨅ v, g t (xbar t, v)) = integralFunctional μ f xbar :=
      rfl
    refine (hint.2 (hcommon ▸ hFb) ubar hubar).1 ?_
    rw [hint.1, hcommon]
    exact hIeq
  · rintro ⟨hFeq, hae⟩
    have hIeq : integralFunctional μ g (fun t ↦ (xbar t, ubar t)) = integralFunctional μ f xbar := by
      refine upperIntegral_congr_ae ?_
      filter_upwards [hae] with t ht
      exact ((mem_argmin_iff _ _).1 ht).1
    rw [hIeq, hFeq]

/-- For `U = M(T, A; ℝᵐ)` the hypothesis `hH` of `reduced_optimization` is automatic: if
`I_f[x] < ∞` for a measurable `x`, then `I_g[x, u] < ∞` for some measurable `u`, by the selection
lemma of Theorem 14.60 applied to the normal integrand `h(t, u) = g(t, x(t), u)` (14.45(a)). -/
theorem exists_measurable_integralFunctional_pair_lt_top [SigmaFinite μ]
    {g : T → E × G → EReal} (hg : IsNormalIntegrand g) {x : T → E} (hx : Measurable x)
    (hI : integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x < ⊤) :
    ∃ u ∈ {u : T → G | Measurable u}, integralFunctional μ g (fun t ↦ (x t, u t)) < ⊤ := by
  have hh : IsNormalIntegrand (fun t v ↦ g t (x t, v)) :=
    hg.comp_caratheodory (F := fun t v ↦ (x t, v))
      ⟨fun v ↦ hx.prodMk measurable_const, fun t ↦ continuous_const.prodMk continuous_id⟩
  have hI' : upperIntegral μ (fun t ↦ ⨅ v, g t (x t, v)) < ⊤ := hI
  obtain ⟨β, hβ, -⟩ := EReal.lt_iff_exists_real_btwn.1 hI'
  obtain ⟨u, hu, hlt⟩ := exists_measurable_integralFunctional_lt hh hβ
  exact ⟨u, hu, hlt.trans (EReal.coe_lt_top β)⟩

/-- **Example 14.62 (reduced optimization)** for `U = M(T, A; ℝᵐ)`, where the printed statement
holds even without the proviso `inf(P) < ∞`: (P) and (P') have the same infimum, and when it is
finite the optimal pairs of (P) are the `(x̄, ū)` with `x̄` optimal for (P') and
`ū(t) ∈ argmin g(t, x̄(t), ·)` a.e.  The hypothesis `hH` of `reduced_optimization` holds by
`exists_measurable_integralFunctional_pair_lt_top`. -/
theorem reduced_optimization_measurable [SigmaFinite μ] {g : T → E × G → EReal}
    (hg : IsNormalIntegrand g) (hflsc : ∀ t, LowerSemicontinuous fun y ↦ ⨅ v, g t (y, v))
    {X : Set (T → E)} (hX : ∀ x ∈ X, Measurable x) (J : (T → E) → EReal) :
    IsNormalIntegrand (fun t y ↦ ⨅ v, g t (y, v)) ∧
      (⨅ x ∈ X, ⨅ u ∈ {u : T → G | Measurable u},
          infAddition (J x) (integralFunctional μ g (fun t ↦ (x t, u t)))) =
        (⨅ x ∈ X, infAddition (J x) (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x)) ∧
      (⊥ < (⨅ x ∈ X, infAddition (J x) (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x)) →
        (⨅ x ∈ X, infAddition (J x) (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x)) < ⊤ →
        ∀ xbar ∈ X, ∀ ubar ∈ {u : T → G | Measurable u},
          (infAddition (J xbar) (integralFunctional μ g (fun t ↦ (xbar t, ubar t))) =
              (⨅ x ∈ X, ⨅ u ∈ {u : T → G | Measurable u},
                infAddition (J x) (integralFunctional μ g (fun t ↦ (x t, u t)))) ↔
            infAddition (J xbar) (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) xbar) =
                (⨅ x ∈ X,
                  infAddition (J x) (integralFunctional μ (fun t y ↦ ⨅ v, g t (y, v)) x)) ∧
              ∀ᵐ t ∂μ, ubar t ∈ argmin (fun v ↦ g t (xbar t, v)))) :=
  reduced_optimization hg hflsc hX (isDecomposable_measurable μ) J
    (fun x hx _ hI ↦ exists_measurable_integralFunctional_pair_lt_top hg (hX x hx) hI)

end Example1462

end RW
