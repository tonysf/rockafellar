/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Sums and nonnegative multiples of normal integrands

Proposition 14.44(c)(d) (finite nonnegative combinations and separable sums) and
Corollary 14.46 (multiplication by nonnegative measurable scalars) of Rockafellar–Wets.

For 14.44(c) the summands are required never to take `-∞` (proper summands, as in 14.44(d) and
the book's 1.39(a), qualify, and so do summands `≡ ∞`): with the book's inf-addition convention
`∞ - ∞ = ∞`, a sum of normal integrands taking `-∞` need not even be lsc in `x`
(`sum_of_normal_integrands_counterexample`).  On functions that never take `-∞`,
the extended-real sum and products by nonnegative reals agree with the book's conventions
(including `0 · ∞ = 0`).
-/

import RockafellarWets.Chapter14.IntegrandOperations
import RockafellarWets.Chapter7.EpigraphAddition

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Classical

noncomputable section

namespace RW

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Corollary1446

theorem ereal_coe_pos_mul_le_coe_iff {c : ℝ} (hc : 0 < c) (a : EReal) (α : ℝ) :
    (c : EReal) * a ≤ (α : EReal) ↔ a ≤ ((α / c : ℝ) : EReal) := by
  induction a with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hc]
    simp
  | coe r =>
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, le_div_iff₀ hc, mul_comm]
  | top =>
    rw [EReal.coe_mul_top_of_pos hc]
    simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Corollary 14.46 (multiplication by nonnegative scalars)**: `λ(t) g(t, x)` is a normal
integrand for a normal integrand `g` and measurable `λ ≥ 0` (with `0 · ±∞ = 0`). -/
theorem IsNormalIntegrand.mul_measurable {g : T → E → EReal} (hg : IsNormalIntegrand g)
    {lam : T → ℝ} (hlam : Measurable lam) (hpos : ∀ t, 0 ≤ lam t) :
    IsNormalIntegrand (fun t x ↦ (lam t : EReal) * g t x) := by
  refine measurability_of_level_set_mappings.2 fun α ↦ ?_
  have hset : ∀ t, {x | (lam t : EReal) * g t x ≤ α} =
      if t ∈ {t | lam t = 0} then {_x : E | (0 : ℝ) ≤ α} else {x | g t x ≤ ((α / lam t : ℝ))} := by
    intro t
    split_ifs with h
    · have h' : lam t = 0 := h
      ext x
      simp [h']
    · have h' : 0 < lam t := lt_of_le_of_ne (hpos t) (Ne.symm h)
      ext x
      exact ereal_coe_pos_mul_le_coe_iff h' (g t x) α
  obtain ⟨hLc, hLm⟩ := hg.levelSet_measurable (α := fun t ↦ α / lam t)
    (measurable_const.div hlam)
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [hset t]
    split_ifs
    · exact isClosed_const
    · exact hLc t
  · rw [funext hset]
    exact SvMeasurable.ite (hlam (measurableSet_singleton 0)) (svMeasurable_const _) hLm

end Corollary1446

section Proposition1444

omit [MeasurableSpace T] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- Sums of lsc functions that never take `-∞` are lsc. -/
theorem lowerSemicontinuous_add_of_ne_bot {g₁ g₂ : E → EReal} (h₁ : LowerSemicontinuous g₁)
    (h₂ : LowerSemicontinuous g₂) (hb₂ : ∀ x, g₂ x ≠ ⊥) (hb₁ : ∀ x, g₁ x ≠ ⊥) :
    LowerSemicontinuous fun x ↦ g₁ x + g₂ x :=
  h₁.add' h₂ fun x ↦ EReal.continuousAt_add (Or.inr (hb₂ x)) (Or.inl (hb₁ x))

omit [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem epigraph_add_of_ne_bot {g₁ g₂ : E → EReal} (hb₁ : ∀ x, g₁ x ≠ ⊥) (hb₂ : ∀ x, g₂ x ≠ ⊥) :
    epigraph (fun x ↦ g₁ x + g₂ x) =
      (fun p : (E × ℝ) × (E × ℝ) ↦ (p.1.1, p.1.2 + p.2.2)) ''
        ((epigraph g₁ ×ˢ epigraph g₂) ∩ {p | p.1.1 = p.2.1}) := by
  ext ⟨x, α⟩
  constructor
  · intro h
    have h' : g₁ x + g₂ x ≤ α := h
    have ht₁ : g₁ x ≠ ⊤ := by
      intro ht
      rw [ht, EReal.top_add_of_ne_bot (hb₂ x)] at h'
      exact absurd h' (by simp)
    set a := (g₁ x).toReal
    have ha : g₁ x = a := (EReal.coe_toReal ht₁ (hb₁ x)).symm
    have ht₂ : g₂ x ≠ ⊤ := by
      intro ht
      rw [ha, ht, EReal.coe_add_top] at h'
      exact absurd h' (by simp)
    set b := (g₂ x).toReal
    have hb : g₂ x = b := (EReal.coe_toReal ht₂ (hb₂ x)).symm
    rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at h'
    refine ⟨((x, a), (x, α - a)), ⟨⟨(show (a : EReal) ≥ g₁ x from ha.le), ?_⟩, rfl⟩, ?_⟩
    · change g₂ x ≤ ((α - a : ℝ) : EReal)
      rw [hb, EReal.coe_le_coe_iff]
      linarith
    · simp
  · rintro ⟨⟨⟨y, r⟩, ⟨z, s⟩⟩, ⟨⟨hr, hs⟩, hyz⟩, heq⟩
    change y = z at hyz
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    subst hyz
    change g₁ y + g₂ y ≤ ((r + s : ℝ) : EReal)
    rw [EReal.coe_add]
    exact add_le_add (show g₁ y ≤ r from hr) (show g₂ y ≤ s from hs)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Proposition 14.44(c)**, binary sums: the sum of two normal integrands that never take
`-∞` is a normal integrand. -/
theorem IsNormalIntegrand.add {f g : T → E → EReal} (hf : IsNormalIntegrand f)
    (hg : IsNormalIntegrand g) (hfb : ∀ t x, f t x ≠ ⊥) (hgb : ∀ t x, g t x ≠ ⊥) :
    IsNormalIntegrand (fun t x ↦ f t x + g t x) := by
  refine ⟨fun t ↦ (lsc_iff_epigraph_closed_ereal _).1 (lowerSemicontinuous_add_of_ne_bot
    (hf.lowerSemicontinuous t) (hg.lowerSemicontinuous t) (hgb t) (hfb t)), ?_⟩
  have heq : epiMapping (fun t x ↦ f t x + g t x) = fun t ↦
      (fun p : (E × ℝ) × (E × ℝ) ↦ (p.1.1, p.1.2 + p.2.2)) ''
        ((epiMapping f t ×ˢ epiMapping g t) ∩ {p | p.1.1 = p.2.1}) :=
    funext fun t ↦ epigraph_add_of_ne_bot (hfb t) (hgb t)
  rw [heq]
  refine (SvMeasurable.inter (hf.2.prod hg.2) (svMeasurable_const _)
    (fun t ↦ (hf.1 t).prod (hg.1 t)) (fun _ ↦ isClosed_eq (continuous_fst.comp continuous_fst)
      (continuous_fst.comp continuous_snd))).image ?_
  exact (continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).add (continuous_snd.comp continuous_snd))

theorem ereal_coe_nonneg_mul_ne_bot {c : ℝ} (hc : 0 ≤ c) {a : EReal} (ha : a ≠ ⊥) :
    (c : EReal) * a ≠ ⊥ := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  · induction a with
    | bot => exact absurd rfl ha
    | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
    | top => rw [EReal.coe_mul_top_of_pos hc]; exact top_ne_bot

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Proposition 14.44(c)**: finite combinations `∑ λⱼ fⱼ` with `λⱼ ≥ 0` of normal integrands
that never take `-∞` (e.g. proper normal integrands) are normal integrands. -/
theorem IsNormalIntegrand.finsetSum_smul {J : Type*} (s : Finset J) {f : J → T → E → EReal}
    (hf : ∀ j, IsNormalIntegrand (f j)) (hb : ∀ j t x, f j t x ≠ ⊥) (lam : J → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) :
    IsNormalIntegrand (fun t x ↦ ∑ j ∈ s, (lam j : EReal) * f j t x) ∧
      ∀ t x, ∑ j ∈ s, (lam j : EReal) * f j t x ≠ ⊥ := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨isNormalIntegrand_const lowerSemicontinuous_const, fun _ _ ↦ EReal.zero_ne_bot⟩
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    have hterm : IsNormalIntegrand (fun t x ↦ (lam j : EReal) * f j t x) :=
      (hf j).mul_measurable (lam := fun _ ↦ lam j) measurable_const fun _ ↦ hlam j
    have htb : ∀ t x, (lam j : EReal) * f j t x ≠ ⊥ := fun t x ↦
      ereal_coe_nonneg_mul_ne_bot (hlam j) (hb j t x)
    exact ⟨hterm.add ih.1 htb ih.2, fun t x ↦ EReal.add_ne_bot_iff.2 ⟨htb t x, ih.2 t x⟩⟩

end Proposition1444

section SeparableSums

variable {J : Type*} [Fintype J] {G : J → Type*} [∀ j, NormedAddCommGroup (G j)]
  [∀ j, NormedSpace ℝ (G j)] [∀ j, FiniteDimensional ℝ (G j)] [∀ j, MeasurableSpace (G j)]
  [∀ j, BorelSpace (G j)]

/-- **Proposition 14.44(d)**: for proper normal integrands `fⱼ : T × ℝ^{nⱼ} → ℝ̄`, the separable
sum `f(t, x₁, …, x_r) = f₁(t, x₁) + ⋯ + f_r(t, x_r)` is a normal integrand. -/
theorem IsNormalIntegrand.separableSum {f : ∀ j, T → G j → EReal}
    (hf : ∀ j, IsNormalIntegrand (f j)) (hp : ∀ j t, IsProper (f j t)) :
    IsNormalIntegrand (fun t (x : ∀ j, G j) ↦ ∑ j, f j t (x j)) := by
  have hcomp : ∀ j, IsNormalIntegrand (fun t (x : ∀ j, G j) ↦ f j t (x j)) := fun j ↦
    (hf j).comp_caratheodory (F := fun (_ : T) (x : ∀ j, G j) ↦ x j) ⟨fun _ ↦ measurable_const,
      fun _ ↦ continuous_apply j⟩
  have h := IsNormalIntegrand.finsetSum_smul Finset.univ hcomp
    (fun j t (x : ∀ j, G j) ↦ ((hp j t).2 (x j)).ne') (fun _ ↦ 1) (fun _ ↦ zero_le_one)
  simpa only [EReal.coe_one, one_mul] using h.1

end SeparableSums

section Counterexample

/-- **Proposition 14.44(c)** needs summands that never take `-∞` (e.g. proper ones): with the
book's inf-addition (`∞ - ∞ = ∞`, `infAddition`), the sum of the autonomous normal integrands
`f₁ = -∞` on `(-∞, 0]`, `∞` on `(0, ∞)` and `f₂(x) = 1/|x|`, `f₂(0) = ∞` equals `-∞` on
`(-∞, 0)` and `∞` on `[0, ∞)`, which is not lsc, so it is not a normal integrand. -/
theorem sum_of_normal_integrands_counterexample :
    ∃ f₁ f₂ : Unit → ℝ → EReal, IsNormalIntegrand f₁ ∧ IsNormalIntegrand f₂ ∧
      ¬ IsNormalIntegrand (fun t x ↦ infAddition (f₁ t x) (f₂ t x)) := by
  set g₁ : ℝ → EReal := fun x ↦ if x ≤ 0 then ⊥ else ⊤ with hg₁
  set g₂ : ℝ → EReal := fun x ↦ if x = 0 then ⊤ else ((1 / |x| : ℝ) : EReal) with hg₂
  have hl₁ : LowerSemicontinuous g₁ := by
    refine lowerSemicontinuous_iff_isClosed_preimage.2 fun y ↦ ?_
    by_cases hy : y = ⊤
    · have : g₁ ⁻¹' Iic y = univ := by ext x; simp [hy]
      rw [this]
      exact isClosed_univ
    · have : g₁ ⁻¹' Iic y = Iic 0 := by
        ext x
        by_cases hx : x ≤ 0 <;> simp [hg₁, hx, hy]
      rw [this]
      exact isClosed_Iic
  have hl₂ : LowerSemicontinuous g₂ := by
    refine lowerSemicontinuous_iff_isClosed_preimage.2 fun y ↦ ?_
    induction y with
    | bot =>
      have : g₂ ⁻¹' Iic ⊥ = ∅ := by
        ext x
        by_cases hx : x = 0 <;> simp [hg₂, hx]
      rw [this]
      exact isClosed_empty
    | coe a =>
      by_cases ha : 0 < a
      · have : g₂ ⁻¹' Iic (a : EReal) = {x | 1 / a ≤ |x|} := by
          ext x
          by_cases hx : x = 0
          · simp only [hg₂, hx, if_true, mem_preimage, mem_Iic, top_le_iff, EReal.coe_ne_top,
              mem_setOf_eq, abs_zero, false_iff, not_le]
            exact one_div_pos.2 ha
          · simp only [hg₂, hx, if_false, mem_preimage, mem_Iic, EReal.coe_le_coe_iff,
              mem_setOf_eq]
            have habs : 0 < |x| := abs_pos.2 hx
            rw [div_le_iff₀ habs, div_le_iff₀ ha, mul_comm]
        rw [this]
        exact isClosed_le continuous_const continuous_abs
      · have : g₂ ⁻¹' Iic (a : EReal) = ∅ := by
          ext x
          by_cases hx : x = 0
          · simp [hg₂, hx]
          · simp only [hg₂, hx, if_false, mem_preimage, mem_Iic, EReal.coe_le_coe_iff,
              mem_empty_iff_false, iff_false, not_le]
            have : 0 < 1 / |x| := one_div_pos.2 (abs_pos.2 hx)
            linarith
        rw [this]
        exact isClosed_empty
    | top =>
      have : g₂ ⁻¹' Iic ⊤ = univ := by ext x; simp
      rw [this]
      exact isClosed_univ
  refine ⟨fun _ ↦ g₁, fun _ ↦ g₂, isNormalIntegrand_const hl₁, isNormalIntegrand_const hl₂, ?_⟩
  intro h
  have hlsc := h.lowerSemicontinuous ()
  have hclosed := hlsc.isClosed_preimage (0 : EReal)
  have hset : (fun x ↦ infAddition (g₁ x) (g₂ x)) ⁻¹' Iic 0 = Iio 0 := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_Iio]
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · have h1 : g₁ x = ⊥ := by simp [hg₁, hx.le]
      have h2 : g₂ x = ((1 / |x| : ℝ) : EReal) := by simp [hg₂, hx.ne]
      rw [h1, h2]
      simp [infAddition, hx]
    · simp [hg₂, infAddition]
    · have h1 : g₁ x = ⊤ := by simp [hg₁, not_le.2 hx]
      simp [h1, infAddition, not_lt.2 hx.le]
  rw [hset] at hclosed
  have h0 : (0 : ℝ) ∈ closure (Iio (0 : ℝ)) := by
    rw [closure_Iio' ⟨-1, by norm_num⟩]
    exact self_mem_Iic
  rw [hclosed.closure_eq] at h0
  exact lt_irrefl (0 : ℝ) (mem_Iio.1 h0)

end Counterexample


section PointwiseLimits

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Proposition 14.53(b)**: `f(t, ·) = cl [p-lim fν(t, ·)]` is a normal integrand when the
pointwise limit exists. -/
theorem IsNormalIntegrand.epiClosure_of_tendsto {f : ℕ → T → E → EReal} {h : T → E → EReal}
    (hf : ∀ n, IsNormalIntegrand (f n))
    (hlim : ∀ t x, Tendsto (fun n ↦ f n t x) atTop (𝓝 (h t x))) :
    IsNormalIntegrand (fun t ↦ epiClosure (h t)) := by
  have heq : (fun t ↦ epiClosure (h t)) =
      fun t ↦ epiClosure (fun x ↦ Filter.limsup (fun n ↦ f n t x) atTop) := by
    funext t
    congr 1
    funext x
    exact ((hlim t x).limsup_eq).symm
  rw [heq]
  exact IsNormalIntegrand.epiClosure_limsup hf

end PointwiseLimits

end RW
