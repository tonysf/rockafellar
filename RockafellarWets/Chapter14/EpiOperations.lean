/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Epi-addition and epi-multiplication of normal integrands

Example 14.48 of Rockafellar–Wets.  Epi-addition uses the book's inf-addition (`infAddition`,
`∞ - ∞ = ∞`): `(g □ h)(x) = inf_w g(x - w) + h(w)`; the `m`-fold sum `f₁ □ ⋯ □ f_m` is the
iterated sum over a list, with the identity `δ_{0}` for the empty list, and
`epi cl(f₁ □ ⋯ □ f_m) = cl (epi f₁ + ⋯ + epi f_m + epi δ_{0})` (1.28).  Epi-multiplication is
`(λ ⋆ g)(x) = λ g(λ⁻¹x)` for `λ > 0`, and `0 ⋆ g = δ_{0}` (`≡ ∞` when `g ≡ ∞`), formula 1(14).
-/

import RockafellarWets.Chapter14.IntegrandSums

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Pointwise Classical

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Binary epi-addition with the book's inf-addition. -/
def infEpiSum (g h : E → EReal) (x : E) : EReal := ⨅ w, infAddition (g (x - w)) (h w)

/-- The `m`-fold epi-sum `f₁ □ ⋯ □ f_m` of a list, with `δ_{0}` for the empty list. -/
def iteratedEpiSum : List (E → EReal) → E → EReal
  | [] => indicatorVA {0}
  | g :: gs => infEpiSum g (iteratedEpiSum gs)

/-- The sum `epi f₁ + ⋯ + epi f_m + epi δ_{0}` of the epigraphs. -/
def epigraphSum : List (E → EReal) → Set (E × ℝ)
  | [] => epigraph (indicatorVA ({0} : Set E))
  | g :: gs => epigraph g + epigraphSum gs

theorem closure_add_closure_right {s t : Set (E × ℝ)} :
    _root_.closure (s + _root_.closure t) = _root_.closure (s + t) := by
  apply Subset.antisymm _ (closure_mono (add_subset_add_left subset_closure))
  refine closure_minimal ?_ isClosed_closure
  have hcont : Continuous fun p : (E × ℝ) × (E × ℝ) ↦ p.1 + p.2 := continuous_fst.add continuous_snd
  rintro _ ⟨a, ha, b, hb, rfl⟩
  have hmem : (a, b) ∈ _root_.closure (s ×ˢ t) := by
    rw [closure_prod_eq]
    exact ⟨subset_closure ha, hb⟩
  have := image_closure_subset_closure_image hcont ⟨(a, b), hmem, rfl⟩
  rwa [image_prod, image2_add] at this

/-- Formula 1.28 for inf-addition epi-sums: `cl epi (g □ h) = cl (epi g + epi h)`. -/
theorem closure_epigraph_infEpiSum (g h : E → EReal) :
    _root_.closure (epigraph (infEpiSum g h)) = _root_.closure (epigraph g + epigraph h) := by
  apply Subset.antisymm
  · refine closure_minimal ?_ isClosed_closure
    rintro ⟨x, β⟩ hxβ
    have hxβ' : infEpiSum g h x ≤ β := hxβ
    have hseq : ∀ n : ℕ, ((x, β + 1 / ((n : ℝ) + 1)) : E × ℝ) ∈ epigraph g + epigraph h := by
      intro n
      have hlt : infEpiSum g h x < ((β + 1 / ((n : ℝ) + 1) : ℝ) : EReal) :=
        lt_of_le_of_lt hxβ' (EReal.coe_lt_coe_iff.2 (by
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith))
      obtain ⟨w, hw⟩ := iInf_lt_iff.1 hlt
      obtain ⟨r, s, hr, hs, hrs⟩ := (infAddition_le_coe_iff _ _ _).1 hw.le
      refine ⟨(x - w, r), hr, (w, s), hs, ?_⟩
      simp only [Prod.mk_add_mk, sub_add_cancel, hrs]
    have htend : Tendsto (fun n : ℕ ↦ ((x, β + 1 / ((n : ℝ) + 1)) : E × ℝ)) atTop (𝓝 (x, β)) := by
      refine tendsto_const_nhds.prodMk_nhds ?_
      have := (tendsto_const_nhds (x := β)).add tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [add_zero] at this
    exact mem_closure_of_tendsto htend (Eventually.of_forall hseq)
  · refine closure_mono ?_
    rintro _ ⟨⟨x₁, a₁⟩, h₁, ⟨x₂, a₂⟩, h₂, rfl⟩
    change infEpiSum g h (x₁ + x₂) ≤ ((a₁ + a₂ : ℝ) : EReal)
    refine (iInf_le _ x₂).trans ?_
    rw [add_sub_cancel_right]
    exact (infAddition_le_coe_iff _ _ _).2 ⟨a₁, a₂, h₁, h₂, rfl⟩

theorem epigraph_epiClosure_iteratedEpiSum (gs : List (E → EReal)) :
    epigraph (epiClosure (iteratedEpiSum gs)) = _root_.closure (epigraphSum gs) := by
  induction gs with
  | nil =>
    simp only [iteratedEpiSum, epigraphSum]
    rw [epigraph_epiClosure]
  | cons g gs ih =>
    simp only [iteratedEpiSum, epigraphSum]
    rw [epigraph_epiClosure, closure_epigraph_infEpiSum, ← closure_add_closure_right,
      ← epigraph_epiClosure, ih, closure_add_closure_right]

/-- Epi-multiplication `λ ⋆ g`, formula 1(14). -/
def epiMultiplication (lam : ℝ) (g : E → EReal) : E → EReal :=
  if 0 < lam then fun x ↦ (lam : EReal) * g (lam⁻¹ • x)
  else if ∃ y, g y < ⊤ then indicatorVA {0} else fun _ ↦ ⊤

theorem epigraph_epiMultiplication_of_pos {lam : ℝ} (hlam : 0 < lam) (g : E → EReal) :
    epigraph (epiMultiplication lam g) = lam • epigraph g := by
  ext ⟨x, β⟩
  simp only [epiMultiplication, if_pos hlam]
  constructor
  · intro h
    have h' : (lam : EReal) * g (lam⁻¹ • x) ≤ β := h
    rw [ereal_coe_pos_mul_le_coe_iff hlam] at h'
    refine ⟨(lam⁻¹ • x, β / lam), h', ?_⟩
    simp only [Prod.smul_mk, smul_eq_mul, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul,
      Prod.mk.injEq, true_and]
    field_simp
  · rintro ⟨⟨y, γ⟩, hyγ, heq⟩
    simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    change (lam : EReal) * g (lam⁻¹ • lam • y) ≤ ((lam * γ : ℝ) : EReal)
    rw [ereal_coe_pos_mul_le_coe_iff hlam, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    have : lam * γ / lam = γ := by field_simp
    rw [this]
    exact hyγ

section Example1448

variable {T : Type*} [MeasurableSpace T] [FiniteDimensional ℝ E]

/-- **Example 14.48(a)**: `f(t, ·) = cl (f₁(t, ·) □ ⋯ □ f_m(t, ·))` is a normal integrand for
normal integrands `fᵢ`. -/
theorem IsNormalIntegrand.epiClosure_iteratedEpiSum (fs : List (T → E → EReal))
    (hfs : ∀ f ∈ fs, IsNormalIntegrand f) :
    IsNormalIntegrand (fun t ↦ epiClosure (iteratedEpiSum (fs.map fun f ↦ f t))) := by
  have hsum : SvMeasurable (fun t ↦ epigraphSum (fs.map fun f ↦ f t)) := by
    induction fs with
    | nil =>
      simp only [List.map_nil, epigraphSum]
      exact svMeasurable_const _
    | cons f fs ih =>
      simp only [List.map_cons, epigraphSum]
      exact (hfs f (List.mem_cons_self ..)).2.add
        (ih fun g hg ↦ hfs g (List.mem_cons_of_mem _ hg))
  refine ⟨fun t ↦ by rw [epigraph_epiClosure_iteratedEpiSum]; exact isClosed_closure, ?_⟩
  have heq : epiMapping (fun t ↦ epiClosure (iteratedEpiSum (fs.map fun f ↦ f t))) =
      fun t ↦ _root_.closure (epigraphSum (fs.map fun f ↦ f t)) :=
    funext fun t ↦ epigraph_epiClosure_iteratedEpiSum _
  rw [heq]
  exact hsum.closure

variable [MeasurableSpace E] [BorelSpace E]

/-- **Example 14.48(b)**: `f(t, ·) = λ(t) ⋆ g(t, ·)` is a normal integrand for a normal integrand
`g` and measurable `λ(t) ≥ 0`. -/
theorem IsNormalIntegrand.epiMultiplication {g : T → E → EReal} (hg : IsNormalIntegrand g)
    {lam : T → ℝ} (hlam : Measurable lam) (hpos : ∀ t, 0 ≤ lam t) :
    IsNormalIntegrand (fun t ↦ RW.epiMultiplication (lam t) (g t)) := by
  have hdom : MeasurableSet {t | ∃ y, g t y < ⊤} := by
    have : {t | ∃ y, g t y < ⊤} = svDom (epiMapping g) := by
      ext t
      simp only [mem_setOf_eq, mem_svDom]
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨r, hr⟩ : ∃ r : ℝ, g t y < r := by
          induction h : g t y with
          | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
          | coe a => exact ⟨a + 1, EReal.coe_lt_coe_iff.2 (lt_add_one a)⟩
          | top => rw [h] at hy; exact absurd hy (lt_irrefl _)
        exact ⟨(y, r), hr.le⟩
      · rintro ⟨⟨y, r⟩, hyr⟩
        exact ⟨y, lt_of_le_of_lt hyr (EReal.coe_lt_top r)⟩
    rw [this]
    exact hg.2.measurableSet_svDom
  have hpos_set : MeasurableSet {t | 0 < lam t} := measurableSet_lt measurable_const hlam
  have hscaled : SvMeasurable (fun t ↦ lam t • epiMapping g t) := by
    have hΦ : IsCaratheodory (fun t (p : E × ℝ) ↦ lam t • p) :=
      ⟨fun p ↦ hlam.smul_const p, fun t ↦ continuous_const_smul _⟩
    have h := hΦ.svMeasurable_image hg.2 hg.1
    exact h
  have hepi : ∀ t, epigraph (RW.epiMultiplication (lam t) (g t)) =
      if t ∈ {t | 0 < lam t} then lam t • epiMapping g t
      else if t ∈ {t | ∃ y, g t y < ⊤} then epigraph (indicatorVA ({0} : Set E)) else ∅ := by
    intro t
    split_ifs with h1 h2
    · rw [epigraph_epiMultiplication_of_pos h1]
      rfl
    · have h1' : ¬ 0 < lam t := h1
      simp only [RW.epiMultiplication, if_neg h1', if_pos (show ∃ y, g t y < ⊤ from h2)]
    · have h1' : ¬ 0 < lam t := h1
      simp only [RW.epiMultiplication, if_neg h1', if_neg (show ¬ ∃ y, g t y < ⊤ from h2)]
      ext p
      simp [epigraph]
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [hepi t]
    split_ifs with h1 h2
    · have h1' : 0 < lam t := h1
      exact (hg.1 t).smul_of_ne_zero h1'.ne'
    · rw [epigraph_indicatorVA]
      exact isClosed_singleton.prod isClosed_Ici
    · exact isClosed_empty
  · rw [show epiMapping (fun t ↦ RW.epiMultiplication (lam t) (g t)) = _ from funext hepi]
    convert SvMeasurable.ite hpos_set hscaled
      (SvMeasurable.ite hdom (svMeasurable_const (epigraph (indicatorVA ({0} : Set E))))
        (svMeasurable_const ∅)) using 2 with t

end Example1448

end RW
