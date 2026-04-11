/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3E: Epi-Addition

This file starts the epi-addition layer around Corollary 3.33:
- the `EReal` epi-sum is encoded as a parametric infimum;
- the associated integrand is proper and lsc under the corresponding
  assumptions on the summands;
- the direct consequences of Theorem 3.31 are packaged for the epi-sum under
  a horizon-positivity hypothesis on that integrand.
-/

import RockafellarWets.Chapter3.Parametric
import RockafellarWets.Chapter3.Coercivity

open Set Topology EReal Filter

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The linear map sending two epigraph points `(y,a)` and `(w,b)` to the
epigraph point `((w, y + w), a + b)` of the epi-sum integrand. -/
def epiSumLinearMap : ((E × ℝ) × (E × ℝ)) →ₗ[ℝ] ((E × E) × ℝ) where
  toFun p := ((p.2.1, p.1.1 + p.2.1), p.1.2 + p.2.2)
  map_add' p q := by
    ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' c p := by
    ext <;> simp [smul_add, mul_add]

@[simp] theorem epiSumLinearMap_apply (p : ((E × ℝ) × (E × ℝ))) :
    epiSumLinearMap p = ((p.2.1, p.1.1 + p.2.1), p.1.2 + p.2.2) := rfl

/-- Real epigraphs are stable under the epi-sum linear map as soon as both
functions are everywhere strictly above `⊥`. -/
theorem image_epiSumLinearMap_eq_epigraph
    {h₁ h₂ : E → EReal}
    (hbot₁ : ∀ x, h₁ x > ⊥) (hbot₂ : ∀ x, h₂ x > ⊥) :
    epiSumLinearMap '' (epigraph h₁ ×ˢ epigraph h₂) =
      epigraph (fun p : E × E => h₁ (p.2 - p.1) + h₂ p.1) := by
  ext z
  rcases z with ⟨⟨w, x⟩, γ⟩
  constructor
  · rintro ⟨p, hp, hpz⟩
    rcases p with ⟨⟨y, a⟩, ⟨u, b⟩⟩
    rcases hp with ⟨hy, hu⟩
    rw [← hpz]
    rw [mem_epigraph_iff] at hy hu ⊢
    simpa [epiSumLinearMap_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add hy hu
  · intro hz
    rw [mem_epigraph_iff] at hz
    let y : E := x - w
    have h₁bot : h₁ y > ⊥ := hbot₁ y
    have h₂bot : h₂ w > ⊥ := hbot₂ w
    have h₁top : h₁ y ≠ ⊤ := by
      intro htop
      have : (⊤ : EReal) ≤ (γ : EReal) := by
        simpa [y, htop, ne_of_gt h₂bot] using hz
      simpa using this
    have h₂top : h₂ w ≠ ⊤ := by
      intro htop
      have : (⊤ : EReal) ≤ (γ : EReal) := by
        simpa [y, htop, ne_of_gt h₁bot] using hz
      simpa using this
    let a : ℝ := (h₁ y).toReal
    have hy_epi : (y, a) ∈ epigraph h₁ := by
      rw [mem_epigraph_iff]
      simpa [a, EReal.coe_toReal h₁top (ne_of_gt h₁bot)] using (le_rfl : h₁ y ≤ h₁ y)
    have hsum_real :
        (h₁ y).toReal + (h₂ w).toReal ≤ γ := by
      have : ((((h₁ y).toReal + (h₂ w).toReal : ℝ) : EReal) ≤ (γ : EReal)) := by
        simpa [EReal.coe_add, EReal.coe_toReal h₁top (ne_of_gt h₁bot),
          EReal.coe_toReal h₂top (ne_of_gt h₂bot), y] using hz
      exact_mod_cast this
    have hw_epi : (w, γ - a) ∈ epigraph h₂ := by
      rw [mem_epigraph_iff]
      have : (h₂ w).toReal ≤ γ - a := by
        dsimp [a] at hsum_real ⊢
        linarith
      rw [← EReal.coe_toReal h₂top (ne_of_gt h₂bot)]
      exact_mod_cast this
    refine ⟨((y, a), (w, γ - a)), ⟨hy_epi, hw_epi⟩, ?_⟩
    ext <;> simp [epiSumLinearMap_apply, y, a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- The parametric integrand behind epi-addition:
`g(w, x) = f₁(x - w) + f₂(w)`. -/
def epiSumIntegrand (f₁ f₂ : E → EReal) : E × E → EReal :=
  fun p => f₁ (p.2 - p.1) + f₂ p.1

/-- The `EReal` epi-sum / infimal convolution:
`(f₁ ⊞ f₂)(x) = inf_w [f₁(x - w) + f₂(w)]`. -/
noncomputable def epiSum (f₁ f₂ : E → EReal) : E → EReal :=
  valueFunction (epiSumIntegrand f₁ f₂)

@[simp] theorem epiSum_apply (f₁ f₂ : E → EReal) (x : E) :
    epiSum f₁ f₂ x = ⨅ w : E, (f₁ (x - w) + f₂ w) := rfl

@[simp] theorem epiSumIntegrand_apply (f₁ f₂ : E → EReal) (w x : E) :
    epiSumIntegrand f₁ f₂ (w, x) = f₁ (x - w) + f₂ w := rfl

/-- Properness of the epi-sum integrand comes directly from properness of the
two summands. -/
theorem isProper_epiSumIntegrand {f₁ f₂ : E → EReal}
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    IsProper (epiSumIntegrand f₁ f₂) := by
  constructor
  · rcases hproper₁.1 with ⟨x₁, hx₁⟩
    rcases hproper₂.1 with ⟨x₂, hx₂⟩
    refine ⟨(x₂, x₁ + x₂), ?_⟩
    have hx₁_top : f₁ x₁ ≠ ⊤ := ne_of_lt hx₁
    have hx₂_top : f₂ x₂ ≠ ⊤ := ne_of_lt hx₂
    simpa [epiSumIntegrand, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (EReal.add_lt_top hx₁_top hx₂_top)
  · intro p
    exact (EReal.bot_lt_add_iff.mpr ⟨hproper₁.2 (p.2 - p.1), hproper₂.2 p.1⟩)

/-- Lower semicontinuity of the epi-sum integrand in the proper case. The
properness assumptions exclude the only bad continuity regime for `EReal`
addition. -/
theorem lowerSemicontinuous_epiSumIntegrand {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    LowerSemicontinuous (epiSumIntegrand f₁ f₂) := by
  have hsub : LowerSemicontinuous (fun p : E × E => f₁ (p.2 - p.1)) := by
    simpa [Function.comp] using
      hlsc₁.comp (continuous_snd.sub continuous_fst)
  have hfst : LowerSemicontinuous (fun p : E × E => f₂ p.1) := by
    simpa [Function.comp] using hlsc₂.comp continuous_fst
  refine LowerSemicontinuous.add' hsub hfst ?_
  intro p
  exact EReal.continuousAt_add
    (.inr (ne_of_gt (hproper₂.2 p.1)))
    (.inl (ne_of_gt (hproper₁.2 (p.2 - p.1))))

/-- The epigraph of the epi-sum is nonempty once the two summands are proper,
because the corresponding value-function epigraph is nonempty. -/
theorem epigraph_epiSum_nonempty_of_isProper {f₁ f₂ : E → EReal}
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    (epigraph (epiSum f₁ f₂)).Nonempty := by
  simpa [epiSum] using
    epigraph_valueFunction_nonempty_of_isProper
      (f := epiSumIntegrand f₁ f₂) (isProper_epiSumIntegrand hproper₁ hproper₂)

/-- A negative vertical direction at horizontal velocity `0` is impossible in
the horizon cone of the epigraph of a proper lsc convex function. -/
theorem zero_le_of_mem_horizonCone_epigraph_zero
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) {a : ℝ}
    (ha : ((0 : E), a) ∈ horizonCone (epigraph f)) :
    0 ≤ a := by
  rcases hproper.1 with ⟨x, hx⟩
  have hbot : f x ≠ ⊥ := ne_of_gt (hproper.2 x)
  have htop : f x ≠ ⊤ := ne_of_lt hx
  have hx_epi : (x, (f x).toReal) ∈ epigraph f := by
    rw [mem_epigraph_iff]
    simpa [EReal.coe_toReal htop hbot] using (le_rfl : f x ≤ f x)
  have hmem :
      (1 : ℝ) • ((0 : E), a) + (x, (f x).toReal) ∈ epigraph f :=
    smul_add_mem_of_mem_horizonCone (C := epigraph f) hconv
      (isClosed_epigraph_of_lsc_ereal f hlsc) hx_epi ha zero_le_one
  have hineq : f x ≤ (((f x).toReal + a : ℝ) : EReal) := by
    rw [mem_epigraph_iff] at hmem
    simpa [Prod.smul_mk, smul_eq_mul, EReal.coe_toReal htop hbot,
      add_assoc, add_left_comm, add_comm] using hmem
  have hreal : (f x).toReal ≤ (f x).toReal + a := by
    rw [← EReal.coe_toReal htop hbot] at hineq
    exact_mod_cast hineq
  linarith

/-- For a proper lsc convex function, the horizon function vanishes at `0`. -/
theorem horizonFunction_zero_eq_zero_of_convex
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) :
    horizonFunction f (0 : E) = 0 := by
  apply le_antisymm
  · simpa using
      horizonFunction_le_of_mem_horizonCone_epigraph
        (f := f) (w := 0) (a := 0) (zero_mem_horizonCone (epigraph f))
  · rw [horizonFunction]
    refine le_iInf ?_
    intro a
    exact_mod_cast
      zero_le_of_mem_horizonCone_epigraph_zero hconv hlsc hproper a.property

/-- A proper lsc convex function has no `⊥` values in its horizon function. -/
theorem bot_lt_horizonFunction_of_convex
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) (w : E) :
    ⊥ < horizonFunction f w := by
  by_contra h
  have hbot : horizonFunction f w = ⊥ := le_antisymm (le_of_not_gt h) bot_le
  have hneg :
      ∀ n : ℕ, ∃ a : {a : ℝ // (w, a) ∈ horizonCone (epigraph f)},
        (a : EReal) < ((-((n : ℝ) + 1) : ℝ) : EReal) := by
    intro n
    have hlt : horizonFunction f w < ((-((n : ℝ) + 1) : ℝ) : EReal) := by
      have : (⊥ : EReal) < ((-((n : ℝ) + 1) : ℝ) : EReal) := EReal.bot_lt_coe _
      simpa [hbot] using this
    let A : Type := {a : ℝ // (w, a) ∈ horizonCone (epigraph f)}
    have hA : Nonempty A := by
      by_contra hA
      letI : IsEmpty A := not_nonempty_iff.mp hA
      have htop : horizonFunction f w = ⊤ := by
        rw [horizonFunction]
        exact iInf_of_empty _
      have : (⊤ : EReal) < ((-((n : ℝ) + 1) : ℝ) : EReal) := by simpa [htop] using hlt
      exact (not_lt_of_ge le_top this).elim
    letI : Nonempty A := hA
    rw [horizonFunction] at hlt
    exact exists_lt_of_ciInf_lt hlt
  choose a ha using hneg
  have hseq_mem :
      ∀ n : ℕ,
        ((((n : ℝ) + 1)⁻¹) • w, (-1 : ℝ)) ∈ asymptoticCone ℝ (epigraph f) := by
    intro n
    have ha_real : (a n : ℝ) < -((n : ℝ) + 1) := by
      exact_mod_cast ha n
    have hmem_hcone : (w, (a n : ℝ)) ∈ horizonCone (epigraph f) := (a n).property
    have hmem_asym :
        (w, (a n : ℝ)) ∈ asymptoticCone ℝ (epigraph f) := by
      rcases (show (w, (a n : ℝ)) = 0 ∨
          (w, (a n : ℝ)) ∈ asymptoticCone ℝ (epigraph f) by
            simpa [horizonCone] using hmem_hcone) with hzero | hzero
      · exfalso
        have hneg0 : (a n : ℝ) < 0 := lt_trans ha_real (by linarith)
        have hEq : (a n : ℝ) = 0 := by simpa using congrArg Prod.snd hzero
        exact (lt_irrefl (0 : ℝ)) (by simpa [hEq] using hneg0)
      · exact hzero
    have hscaled :
        (((n : ℝ) + 1)⁻¹) • (w, (a n : ℝ)) ∈ asymptoticCone ℝ (epigraph f) := by
      exact (smul_mem_asymptoticCone_iff
        (s := epigraph f) (c := ((n : ℝ) + 1)⁻¹)
        (v := (w, (a n : ℝ))) (by positivity)).2 hmem_asym
    have hlt_scaled : (((n : ℝ) + 1)⁻¹) * (a n : ℝ) < -1 := by
      have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
      have := mul_lt_mul_of_pos_left ha_real hpos
      have hone : ((n : ℝ) + 1)⁻¹ * (-((n : ℝ) + 1)) = -1 := by
        field_simp
      exact this.trans_eq hone
    have hshift :
        ((((n : ℝ) + 1)⁻¹) • w, -1) ∈ asymptoticCone ℝ (epigraph f) := by
      have hbase :
          ((((n : ℝ) + 1)⁻¹) • w, (((n : ℝ) + 1)⁻¹) * (a n : ℝ)) ∈
            asymptoticCone ℝ (epigraph f) := by
        simpa [Prod.smul_mk, smul_eq_mul] using hscaled
      have hnonneg : 0 ≤ -1 - (((n : ℝ) + 1)⁻¹) * (a n : ℝ) := by
        linarith
      have := add_nonneg_mem_asymptoticCone_epigraph
        (f := f) (w := (((n : ℝ) + 1)⁻¹) • w)
        (a := (((n : ℝ) + 1)⁻¹) * (a n : ℝ))
        (d := -1 - (((n : ℝ) + 1)⁻¹) * (a n : ℝ)) hbase hnonneg
      simpa [add_assoc, add_left_comm, add_comm] using this
    exact hshift
  have hseq_tendsto :
      Tendsto (fun n : ℕ => ((((n : ℝ) + 1)⁻¹) • w, (-1 : ℝ)))
        atTop (𝓝 ((0 : E), (-1 : ℝ))) := by
    have hw :
        Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ) • w)
          atTop (𝓝 (0 : E)) := by
      simpa [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const w
    simpa [nhds_prod_eq] using hw.prodMk (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1)))
  have hmem_zero :
      ((0 : E), (-1 : ℝ)) ∈ asymptoticCone ℝ (epigraph f) :=
    (isClosed_asymptoticCone (k := ℝ) (s := epigraph f)).mem_of_tendsto
      hseq_tendsto (Filter.Eventually.of_forall hseq_mem)
  have hnonneg :=
    zero_le_of_mem_horizonCone_epigraph_zero hconv hlsc hproper
      (Set.mem_insert_of_mem 0 hmem_zero)
  linarith

/-- In the convex proper lsc case, the only horizon directions annihilated by
`epiSumLinearMap` are trivial. -/
private theorem epiSumLinearMap_hker [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    ∀ ⦃z : ((E × ℝ) × (E × ℝ))⦄,
      z ∈ horizonCone (epigraph f₁ ×ˢ epigraph f₂) →
      epiSumLinearMap z = 0 → z = 0 := by
  intro z hz hz0
  have hz' : z.1 ∈ horizonCone (epigraph f₁) ∧ z.2 ∈ horizonCone (epigraph f₂) :=
    horizonCone_prod_subset hz
  have hz20 : z.2.1 = 0 := by
    simpa [epiSumLinearMap_apply] using
      congrArg (fun p : ((E × E) × ℝ) => p.1.1) hz0
  have hsumx : z.1.1 + z.2.1 = 0 := by
    simpa [epiSumLinearMap_apply] using
      congrArg (fun p : ((E × E) × ℝ) => p.1.2) hz0
  have hz10 : z.1.1 = 0 := by
    simpa [hz20] using hsumx
  have hsuma : z.1.2 + z.2.2 = 0 := by
    simpa [epiSumLinearMap_apply] using congrArg Prod.snd hz0
  have h₁nonneg : 0 ≤ z.1.2 := by
    have hz1pair : ((z.1.1, z.1.2) : E × ℝ) ∈ horizonCone (epigraph f₁) := by
      simpa using hz'.1
    have : ((0 : E), z.1.2) ∈ horizonCone (epigraph f₁) := by
      simpa [hz10] using hz1pair
    exact zero_le_of_mem_horizonCone_epigraph_zero hconv₁ hlsc₁ hproper₁ this
  have h₂nonneg : 0 ≤ z.2.2 := by
    have hz2pair : ((z.2.1, z.2.2) : E × ℝ) ∈ horizonCone (epigraph f₂) := by
      simpa using hz'.2
    have : ((0 : E), z.2.2) ∈ horizonCone (epigraph f₂) := by
      simpa [hz20] using hz2pair
    exact zero_le_of_mem_horizonCone_epigraph_zero hconv₂ hlsc₂ hproper₂ this
  have hz12 : z.1.2 = 0 := by linarith
  have hz22 : z.2.2 = 0 := by linarith
  ext <;> simp [hz10, hz20, hz12, hz22]

/-- Convex epi-addition integrands have horizon function equal to the sum of
the transformed horizon functions of the summands. -/
theorem horizonFunction_epiSumIntegrand_eq_add [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂) :
    horizonFunction (epiSumIntegrand f₁ f₂) =
      fun p : E × E => horizonFunction f₁ (p.2 - p.1) + horizonFunction f₂ p.1 := by
  apply eq_of_epigraph_eq
  calc
    epigraph (horizonFunction (epiSumIntegrand f₁ f₂))
        = horizonCone (epigraph (epiSumIntegrand f₁ f₂)) := by
            exact epigraph_horizonFunction_eq_horizonCone_epigraph
              (epigraph_nonempty_of_isProper (isProper_epiSumIntegrand hproper₁ hproper₂))
    _ = horizonCone (epiSumLinearMap '' (epigraph f₁ ×ˢ epigraph f₂)) := by
          congr 1
          simpa [epiSumIntegrand] using
            (image_epiSumLinearMap_eq_epigraph hproper₁.2 hproper₂.2).symm
    _ = epiSumLinearMap '' horizonCone (epigraph f₁ ×ˢ epigraph f₂) := by
          symm
          exact linearImage_horizonCone_eq (L := epiSumLinearMap)
            (C := epigraph f₁ ×ˢ epigraph f₂)
            (epiSumLinearMap_hker hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂)
    _ = epiSumLinearMap '' (horizonCone (epigraph f₁) ×ˢ horizonCone (epigraph f₂)) := by
          rw [horizonCone_prod_eq_of_convex_nonempty hconv₁ hconv₂
            (epigraph_nonempty_of_isProper hproper₁)
            (epigraph_nonempty_of_isProper hproper₂)]
    _ = epiSumLinearMap '' (epigraph (horizonFunction f₁) ×ˢ epigraph (horizonFunction f₂)) := by
          rw [epigraph_horizonFunction_eq_horizonCone_epigraph
                (epigraph_nonempty_of_isProper hproper₁),
              epigraph_horizonFunction_eq_horizonCone_epigraph
                (epigraph_nonempty_of_isProper hproper₂)]
    _ = epigraph (fun p : E × E => horizonFunction f₁ (p.2 - p.1) + horizonFunction f₂ p.1) := by
          exact image_epiSumLinearMap_eq_epigraph
            (fun x => bot_lt_horizonFunction_of_convex hconv₁ hlsc₁ hproper₁ x)
            (fun x => bot_lt_horizonFunction_of_convex hconv₂ hlsc₂ hproper₂ x)

/-- The positivity condition in Corollary 3.33 yields the horizon-positivity
hypothesis required by Theorem 3.31 for the epi-sum integrand. -/
theorem horizonFunction_epiSumIntegrand_pos_of_pos [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (epiSumIntegrand f₁ f₂) (w, (0 : E)) := by
  intro w hw
  simpa [horizonFunction_epiSumIntegrand_eq_add hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂,
    sub_eq_add_neg, add_comm] using hpos hw

/-- Direct lsc consequence of Theorem 3.31 for epi-addition. -/
theorem lowerSemicontinuous_epiSum_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    LowerSemicontinuous (epiSum f₁ f₂) := by
  simpa [epiSum] using
    lowerSemicontinuous_valueFunction_of_horizonFunction_pos
      (f := epiSumIntegrand f₁ f₂)
      (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)
      (isProper_epiSumIntegrand hproper₁ hproper₂)
      hpos

/-- Convex epi-addition inherits lower semicontinuity from Corollary 3.33's
positivity hypothesis on the transformed horizon sum. -/
theorem lowerSemicontinuous_epiSum_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    LowerSemicontinuous (epiSum f₁ f₂) := by
  apply lowerSemicontinuous_epiSum_of_horizon_pos hlsc₁ hlsc₂ hproper₁ hproper₂
  exact horizonFunction_epiSumIntegrand_pos_of_pos
    hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂ hpos

/-- Direct horizon formula from Theorem 3.31 for epi-addition. -/
theorem horizonFunction_epiSum_eq_valueFunction_horizonIntegrand
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (epiSumIntegrand f₁ f₂) (w, (0 : E))) :
    horizonFunction (epiSum f₁ f₂) =
      valueFunction (horizonFunction (epiSumIntegrand f₁ f₂)) := by
  simpa [epiSum] using
    horizonFunction_valueFunction_eq_valueFunction_horizonFunction
      (f := epiSumIntegrand f₁ f₂)
      (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)
      (isProper_epiSumIntegrand hproper₁ hproper₂)
      hpos

/-- In the convex case, the horizon function commutes with epi-addition. -/
theorem horizonFunction_epiSum_eq_epiSum_horizonFunction
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w) :
    horizonFunction (epiSum f₁ f₂) =
      epiSum (horizonFunction f₁) (horizonFunction f₂) := by
  have hEq :=
    horizonFunction_epiSum_eq_valueFunction_horizonIntegrand
      hlsc₁ hlsc₂ hproper₁ hproper₂
      (horizonFunction_epiSumIntegrand_pos_of_pos
        hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂ hpos)
  simpa [epiSum,
    horizonFunction_epiSumIntegrand_eq_add hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂] using hEq

/-- Under the horizon-positivity condition on the epi-sum integrand, the
infimum in epi-addition is attained whenever it is finite. -/
theorem exists_eq_epiSum_of_finite_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (epiSumIntegrand f₁ f₂) (w, (0 : E)))
    {x : E} (hfin_top : epiSum f₁ f₂ x < ⊤) (hfin_bot : epiSum f₁ f₂ x > ⊥) :
    ∃ w : E, epiSum f₁ f₂ x = f₁ (x - w) + f₂ w := by
  have hLB : IsLevelBoundedInXLocallyUniformly (epiSumIntegrand f₁ f₂) :=
    isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos
  rcases exists_eq_valueFunction_of_finite_of_lsc_localUniform
      (f := epiSumIntegrand f₁ f₂)
      (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)
      hLB hfin_top hfin_bot with ⟨w, hw⟩
  exact ⟨w, by simpa [epiSum, epiSumIntegrand] using hw⟩

/-- Under Corollary 3.33's positivity hypothesis, the epi-sum infimum is
attained whenever it is finite. -/
theorem exists_eq_epiSum_of_finite_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w)
    {x : E} (hfin_top : epiSum f₁ f₂ x < ⊤) (hfin_bot : epiSum f₁ f₂ x > ⊥) :
    ∃ w : E, epiSum f₁ f₂ x = f₁ (x - w) + f₂ w := by
  exact exists_eq_epiSum_of_finite_of_horizon_pos
    hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSumIntegrand_pos_of_pos
      hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂ hpos)
    hfin_top hfin_bot

/-- The horizon formula from epi-addition also has the finite-attainment
consequence on the horizon level. -/
theorem exists_eq_horizon_epiSum_of_finite_of_horizon_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (epiSumIntegrand f₁ f₂) (w, (0 : E)))
    {x : E} (hfin_top : horizonFunction (epiSum f₁ f₂) x < ⊤)
    (hfin_bot : horizonFunction (epiSum f₁ f₂) x > ⊥) :
    ∃ w : E,
      horizonFunction (epiSum f₁ f₂) x =
        horizonFunction (epiSumIntegrand f₁ f₂) (w, x) := by
  simpa [epiSum] using
    exists_eq_horizonFunction_valueFunction_of_finite
      (f := epiSumIntegrand f₁ f₂)
      (lowerSemicontinuous_epiSumIntegrand hlsc₁ hlsc₂ hproper₁ hproper₂)
      (isProper_epiSumIntegrand hproper₁ hproper₂)
      hpos hfin_top hfin_bot

/-- Under Corollary 3.33's positivity hypothesis, the infimum formula on the
horizon level is attained whenever it is finite. -/
theorem exists_eq_horizon_epiSum_of_finite_of_pos
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w)
    {x : E} (hfin_top : horizonFunction (epiSum f₁ f₂) x < ⊤)
    (hfin_bot : horizonFunction (epiSum f₁ f₂) x > ⊥) :
    ∃ w : E,
      horizonFunction (epiSum f₁ f₂) x =
        horizonFunction (epiSumIntegrand f₁ f₂) (w, x) := by
  exact exists_eq_horizon_epiSum_of_finite_of_horizon_pos
    hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSumIntegrand_pos_of_pos
      hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂ hpos)
    hfin_top hfin_bot

/-- If the right summand is coercive, the horizon-positivity hypothesis in
Corollary 3.33 is automatic in the convex proper lsc case. -/
theorem horizonFunction_epiSum_pos_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction f₁ (-w) + horizonFunction f₂ w := by
  intro w hw
  have htop :
      horizonFunction f₂ w = ⊤ :=
    horizonFunction_eq_top_of_isCoercive
      hconv₂ hlsc₂ hproper₂ hcoercive₂ hw
  have hnebot :
      horizonFunction f₁ (-w) ≠ ⊥ := by
    have hlt : horizonFunction f₁ (-w) > ⊥ := by
      simpa using bot_lt_horizonFunction_of_convex hconv₁ hlsc₁ hproper₁ (-w)
    exact ne_of_gt hlt
  have hsum :
      horizonFunction f₁ (-w) + horizonFunction f₂ w = ⊤ := by
    rw [htop, EReal.add_top_of_ne_bot hnebot]
  simpa [hsum] using (show (0 : EReal) < (⊤ : EReal) by simp)

/-- The transformed horizon positivity from Corollary 3.33 yields the
integrand positivity hypothesis required by Theorem 3.31. -/
theorem horizonFunction_epiSumIntegrand_pos_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    ∀ ⦃w : E⦄, w ≠ 0 →
      0 < horizonFunction (epiSumIntegrand f₁ f₂) (w, (0 : E)) := by
  exact horizonFunction_epiSumIntegrand_pos_of_pos
    hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSum_pos_of_isCoercive
      hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂ hcoercive₂)

/-- If the right summand is coercive, epi-addition of the two horizon
functions collapses to the left horizon function. -/
theorem epiSum_horizonFunction_eq_left_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    epiSum (horizonFunction f₁) (horizonFunction f₂) = horizonFunction f₁ := by
  ext x
  rw [epiSum_apply]
  apply le_antisymm
  · have hzero :=
      iInf_le (fun w : E => horizonFunction f₁ (x - w) + horizonFunction f₂ w) (0 : E)
    simpa [horizonFunction_zero_eq_zero_of_convex hconv₂ hlsc₂ hproper₂] using hzero
  · refine le_iInf ?_
    intro w
    by_cases hw : w = 0
    · simpa [hw, horizonFunction_zero_eq_zero_of_convex hconv₂ hlsc₂ hproper₂]
    · have htop :
          horizonFunction f₂ w = ⊤ :=
        horizonFunction_eq_top_of_isCoercive
          hconv₂ hlsc₂ hproper₂ hcoercive₂ hw
      have hnebot :
          horizonFunction f₁ (x - w) ≠ ⊥ := by
        have hlt : horizonFunction f₁ (x - w) > ⊥ := by
          simpa using bot_lt_horizonFunction_of_convex hconv₁ hlsc₁ hproper₁ (x - w)
        exact ne_of_gt hlt
      rw [htop, EReal.add_top_of_ne_bot hnebot]
      exact le_top

/-- Corollary 3.33(b), convex lsc consequence: epi-addition with a coercive
right summand is lower semicontinuous. -/
theorem lowerSemicontinuous_epiSum_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    LowerSemicontinuous (epiSum f₁ f₂) := by
  apply lowerSemicontinuous_epiSum_of_horizon_pos hlsc₁ hlsc₂ hproper₁ hproper₂
  exact horizonFunction_epiSumIntegrand_pos_of_isCoercive
    hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂ hcoercive₂

/-- Corollary 3.33(b), convex equality case: the horizon function of the
epi-sum equals the left horizon function when the right summand is coercive. -/
theorem horizonFunction_epiSum_eq_left_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂) :
    horizonFunction (epiSum f₁ f₂) = horizonFunction f₁ := by
  calc
    horizonFunction (epiSum f₁ f₂)
        = epiSum (horizonFunction f₁) (horizonFunction f₂) := by
            exact horizonFunction_epiSum_eq_epiSum_horizonFunction
              hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂
              (horizonFunction_epiSum_pos_of_isCoercive
                hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂ hcoercive₂)
    _ = horizonFunction f₁ := by
          exact epiSum_horizonFunction_eq_left_of_isCoercive
            hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂ hcoercive₂

/-- Under coercivity of the right summand, the epi-sum infimum is attained
whenever it is finite. -/
theorem exists_eq_epiSum_of_finite_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂)
    {x : E} (hfin_top : epiSum f₁ f₂ x < ⊤) (hfin_bot : epiSum f₁ f₂ x > ⊥) :
    ∃ w : E, epiSum f₁ f₂ x = f₁ (x - w) + f₂ w := by
  exact exists_eq_epiSum_of_finite_of_horizon_pos
    hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSumIntegrand_pos_of_isCoercive
      hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂ hcoercive₂)
    hfin_top hfin_bot

/-- Under coercivity of the right summand, the finite horizon epi-sum formula
is attained. -/
theorem exists_eq_horizon_epiSum_of_finite_of_isCoercive
    [FiniteDimensional ℝ E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁)) (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₁ : LowerSemicontinuous f₁) (hlsc₂ : LowerSemicontinuous f₂)
    (hproper₁ : IsProper f₁) (hproper₂ : IsProper f₂)
    (hcoercive₂ : RW.IsCoercive f₂)
    {x : E} (hfin_top : horizonFunction (epiSum f₁ f₂) x < ⊤)
    (hfin_bot : horizonFunction (epiSum f₁ f₂) x > ⊥) :
    ∃ w : E,
      horizonFunction (epiSum f₁ f₂) x =
        horizonFunction (epiSumIntegrand f₁ f₂) (w, x) := by
  exact exists_eq_horizon_epiSum_of_finite_of_horizon_pos
    hlsc₁ hlsc₂ hproper₁ hproper₂
    (horizonFunction_epiSumIntegrand_pos_of_isCoercive
      hconv₁ hconv₂ hlsc₁ hlsc₂ hproper₁ hproper₂ hcoercive₂)
    hfin_top hfin_bot

end RW
