/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 11: operations on piecewise linear-quadratic functions

**Proposition 11.32(c)**: the inf-projection `p(u) = inf_x f(x, u)` of a proper, convex,
piecewise linear-quadratic function is lower semicontinuous and convex, with polyhedral domain;
either it is proper and piecewise linear-quadratic, or it is `-∞` on its domain
(`IsPiecewiseLinearQuadratic.parametricValue_properties`).

Part (c) is about the inf-projection `parametricValue`. As in the book, a finite value
`p(ū)` is attained (11.16) at some `x̄`, and a subgradient `(0, ȳ) ∈ ∂f(x̄, ū)` (10.22(c)) gives
the affine minorant `p(ū) + ⟪ȳ, · - ū⟫` of `p`.  Hence `p` is proper and lower semicontinuous on
its closed domain, so `p = p**`, while `p* = f*(0, ·)` (11.23(c)) is piecewise linear-quadratic
by 11.14(b) and 10.22.  Parts (a) (`IsPiecewiseLinearQuadratic.epiSum_properties`) and (b)
(`IsPiecewiseLinearQuadratic.fiberInfimum_properties`) reduce to (c) through piecewise
linear-quadratic joint functions.
-/

import RockafellarWets.Chapter11.PiecewiseLinearQuadraticMinimum
import RockafellarWets.Chapter11.DualOperationClosures
import RockafellarWets.Chapter11.PrimalDualSolutions
import RockafellarWets.Chapter10.PLQFiniteCalculus
import RockafellarWets.Chapter7.EpiLimitProperties

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

section InfProjection

variable {f : WithLp 2 (E × F) → EReal} (hf : IsPiecewiseLinearQuadratic f) (hp : IsProper f)
  (hc : Convex ℝ (epigraph f))
include hf hp hc

omit hp in
theorem isPolyhedral_effectiveDomain_parametricValue_of_plq :
    IsPolyhedral (effectiveDomain (parametricValue f)) := by
  rw [effectiveDomain_parametricValue]
  exact (hf.isPolyhedral_effectiveDomain hc).linear_image (WithLp.sndL 2 ℝ E F).toLinearMap

/-- A finite value of the inf-projection is attained and supported by an affine minorant. -/
theorem exists_affine_minorant_parametricValue_of_plq {u₀ : F} {c : ℝ}
    (hu₀ : parametricValue f u₀ = c) :
    ∃ y₀ : F, ∀ u, ((c + ⟪y₀, u - u₀⟫_ℝ : ℝ) : EReal) ≤ parametricValue f u := by
  set φ : E → EReal := partialFunction f u₀ with hφ
  have hφplq : IsPiecewiseLinearQuadratic φ := hf.partialFunction u₀
  have hφc : Convex ℝ (epigraph φ) := by
    have h := convex_epigraph_compAffine hc partialEmbeddingDerivative
      (WithLp.toLp 2 ((0 : E), u₀))
    convert h using 3 with x
    simp only [hφ, partialFunction]
    congr 1
    apply WithLp.ofLp_injective
    simp [partialEmbeddingDerivative]
  have hφinf : (⨅ x, φ x) = c := hu₀
  have hφp : IsProper φ := by
    refine ⟨?_, fun x ↦ hp.2 _⟩
    obtain ⟨x, hx⟩ := iInf_lt_iff.1 (show (⨅ x, φ x) < ⊤ by rw [hφinf]; exact EReal.coe_lt_top c)
    exact ⟨x, hx⟩
  obtain ⟨x₀, hx₀⟩ := (hφplq.argmin_nonempty_and_isPolyhedral hφp hφc
    (by rw [hφinf]; exact EReal.coe_ne_bot c)).1
  have hfx : f (WithLp.toLp 2 (x₀, u₀)) = c := hx₀.1.trans hφinf
  have hxd : WithLp.toLp 2 (x₀, u₀) ∈ effectiveDomain f := by
    change f _ < ⊤
    rw [hfx]
    exact EReal.coe_lt_top c
  have h0 : (0 : E) ∈ subdifferential φ x₀ :=
    (mem_argmin_sub_inner_iff_subgradient hφp hφc 0 x₀).1 (by simpa using hx₀)
  rw [hφ, hf.subdifferential_partialFunction hc u₀ hxd] at h0
  obtain ⟨y₀, hy₀⟩ := h0
  have hsub := (mem_subdifferential_iff_of_convex hc hp hfx).1 hy₀
  refine ⟨y₀, fun u ↦ le_iInf fun x ↦ ?_⟩
  have h := hsub (WithLp.toLp 2 (x, u))
  convert h using 3
  rw [← WithLp.toLp_sub, WithLp.prod_inner_apply]
  simp

/-- **Proposition 11.32(c)**: the inf-projection of a proper, convex, piecewise linear-quadratic
function is convex and lower semicontinuous with polyhedral domain; it is either proper and
piecewise linear-quadratic, or identically `-∞` on its domain. -/
theorem IsPiecewiseLinearQuadratic.parametricValue_properties :
    Convex ℝ (epigraph (parametricValue f)) ∧ LowerSemicontinuous (parametricValue f) ∧
      IsPolyhedral (effectiveDomain (parametricValue f)) ∧
      ((IsProper (parametricValue f) ∧ IsPiecewiseLinearQuadratic (parametricValue f)) ∨
        ∀ u ∈ effectiveDomain (parametricValue f), parametricValue f u = ⊥) := by
  have hconv := convex_epigraph_parametricValue_of_convex hc
  have hpoly := isPolyhedral_effectiveDomain_parametricValue_of_plq hf hc
  have hclosed := hpoly.isClosed
  -- lower semicontinuity
  have hlsc : LowerSemicontinuous (parametricValue f) := by
    intro u y hy
    induction h : parametricValue f u using EReal.rec with
    | bot => rw [h] at hy; exact absurd hy (not_lt_bot)
    | top =>
      have hu : u ∉ effectiveDomain (parametricValue f) := by
        change ¬ parametricValue f u < ⊤
        rw [h]
        exact lt_irrefl _
      filter_upwards [hclosed.isOpen_compl.mem_nhds hu] with u' hu'
      have : parametricValue f u' = ⊤ := not_lt_top_iff.1 hu'
      rw [this]
      exact hy.trans_le (h ▸ le_rfl)
    | coe c =>
      rw [h] at hy
      obtain ⟨y₀, hy₀⟩ := exists_affine_minorant_parametricValue_of_plq hf hp hc h
      induction y using EReal.rec with
      | bot => exact Eventually.of_forall fun u' ↦ lt_of_lt_of_le (EReal.bot_lt_coe _) (hy₀ u')
      | top => exact absurd hy (not_top_lt)
      | coe y =>
        rw [gt_iff_lt, EReal.coe_lt_coe_iff] at hy
        have hcont : Continuous (fun u' : F ↦ c + ⟪y₀, u' - u⟫_ℝ) := by fun_prop
        have hev : ∀ᶠ u' in 𝓝 u, y < c + ⟪y₀, u' - u⟫_ℝ :=
          continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hy)
        filter_upwards [hev] with u' hu'
        exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hu') (hy₀ u')
  refine ⟨hconv, hlsc, hpoly, ?_⟩
  by_cases hfin : ∃ u₀, parametricValue f u₀ ≠ ⊥ ∧ parametricValue f u₀ ≠ ⊤
  · left
    obtain ⟨u₀, hb, ht⟩ := hfin
    have hu₀ : parametricValue f u₀ = ((parametricValue f u₀).toReal : EReal) :=
      (EReal.coe_toReal ht hb).symm
    obtain ⟨y₀, hy₀⟩ := exists_affine_minorant_parametricValue_of_plq hf hp hc hu₀
    have hpp : IsProper (parametricValue f) :=
      ⟨⟨u₀, lt_top_iff_ne_top.2 ht⟩, fun u ↦ lt_of_lt_of_le (EReal.bot_lt_coe _) (hy₀ u)⟩
    refine ⟨hpp, ?_⟩
    -- `p = p**` and `p* = f*(0, ·)`
    have hl := hf.lowerSemicontinuous
    have hfstar := hf.isPiecewiseLinearQuadratic_fenchelConjugate hp hl hc
    have hpstar : fenchelConjugate (parametricValue f) =
        fun v ↦ fenchelConjugate f (WithLp.toLp 2 ((0 : E), v)) := by
      funext v
      rw [fenchelConjugate_parametricValue]
    have hpstar_plq : IsPiecewiseLinearQuadratic (fenchelConjugate (parametricValue f)) := by
      rw [hpstar]
      have h := hfstar.compAffine
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ E F)) 0
      simpa using h
    have h2 := hpstar_plq.isPiecewiseLinearQuadratic_fenchelConjugate
      (isProper_fenchelConjugate hpp hlsc hconv) (lowerSemicontinuous_fenchelConjugate _)
      (convex_epigraph_fenchelConjugate _)
    rwa [fenchelConjugate_fenchelConjugate_eq hpp hlsc hconv] at h2
  · right
    push_neg at hfin
    intro u hu
    by_contra hb
    exact (ne_of_lt hu) (hfin u hb)

end InfProjection

/-! ### Images under linear maps and epi-sums -/

/-- The joint function `(x, u) ↦ f x + δ(A x = u)` whose inf-projection is `Af`. -/
noncomputable def fiberLift (A : E →L[ℝ] F) (f : E → EReal) (q : WithLp 2 (E × F)) : EReal :=
  f (WithLp.ofLp q).1 +
    indicatorVA {q : WithLp 2 (E × F) | A (WithLp.ofLp q).1 = (WithLp.ofLp q).2} q

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem parametricValue_fiberLift (A : E →L[ℝ] F) {f : E → EReal} (hp : IsProper f) :
    parametricValue (fiberLift A f) = fiberInfimum A f := by
  funext u
  apply le_antisymm
  · refine le_iInf fun x ↦ (iInf_le _ x.1).trans (le_of_eq ?_)
    simp [fiberLift, indicatorVA, x.2]
  · refine le_iInf fun x ↦ ?_
    show fiberInfimum A f u ≤ fiberLift A f (WithLp.toLp 2 (x, u))
    by_cases hx : A x = u
    · refine (iInf_le _ ⟨x, hx⟩).trans (le_of_eq ?_)
      simp [fiberLift, indicatorVA, hx]
    · have : fiberLift A f (WithLp.toLp 2 (x, u)) = ⊤ := by
        simp only [fiberLift, indicatorVA, mem_setOf_eq, hx, if_false]
        exact EReal.add_top_of_ne_bot (hp.2 x).ne'
      rw [this]
      exact le_top

/-- The continuous linear projection `(x, u) ↦ x` of the Euclidean product. -/
noncomputable def l2Fst (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] : WithLp 2 (E × F) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E F).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap

/-- The continuous linear projection `(x, u) ↦ u` of the Euclidean product. -/
noncomputable def l2Snd (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] : WithLp 2 (E × F) →L[ℝ] F :=
  (ContinuousLinearMap.snd ℝ E F).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] theorem l2Fst_apply (q : WithLp 2 (E × F)) : l2Fst E F q = (WithLp.ofLp q).1 := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] theorem l2Snd_apply (q : WithLp 2 (E × F)) : l2Snd E F q = (WithLp.ofLp q).2 := rfl

theorem fiberLift_properties (A : E →L[ℝ] F) {f : E → EReal} (hf : IsPiecewiseLinearQuadratic f)
    (hp : IsProper f) (hc : Convex ℝ (epigraph f)) :
    IsPiecewiseLinearQuadratic (fiberLift A f) ∧ IsProper (fiberLift A f) ∧
      Convex ℝ (epigraph (fiberLift A f)) := by
  set M : Set (WithLp 2 (E × F)) := {q | A (WithLp.ofLp q).1 = (WithLp.ofLp q).2} with hM
  have hMpoly : IsPolyhedral M := by
    have h := (IsPolyhedral.singleton (0 : F)).continuousLinear_preimage
      (A.comp (l2Fst E F) - l2Snd E F)
    convert h using 1
    ext q
    simp [hM, sub_eq_zero]
  have h1 : IsPiecewiseLinearQuadratic (fun q : WithLp 2 (E × F) ↦ f (WithLp.ofLp q).1) := by
    simpa using hf.compAffine (l2Fst E F) 0
  have h2 : IsPiecewiseLinearQuadratic (indicatorVA M) :=
    ((isPiecewiseLinear_indicatorVA_iff hMpoly.convex).2 hMpoly).isPiecewiseLinearQuadratic
  have hc1 : Convex ℝ (epigraph (fun q : WithLp 2 (E × F) ↦ f (WithLp.ofLp q).1)) := by
    simpa using convex_epigraph_compAffine hc (l2Fst E F) 0
  have hc2 : Convex ℝ (epigraph (indicatorVA M)) := by
    rw [epigraph_indicatorVA]
    exact hMpoly.convex.prod (convex_Ici _)
  have hb2 : ∀ q, indicatorVA M q ≠ ⊥ := fun q ↦ by
    by_cases hq : q ∈ M <;> simp [indicatorVA, hq]
  refine ⟨h1.add h2, ⟨?_, fun q ↦ ?_⟩, convex_epigraph_add_of_ne_bot hc1 hc2
    (fun q ↦ (hp.2 _).ne') hb2⟩
  · obtain ⟨x, hx⟩ := hp.1
    refine ⟨WithLp.toLp 2 (x, A x), ?_⟩
    change f x + indicatorVA M (WithLp.toLp 2 (x, A x)) < ⊤
    rw [show indicatorVA M (WithLp.toLp 2 (x, A x)) = 0 by simp [indicatorVA, hM], add_zero]
    exact hx
  · change ⊥ < f (WithLp.ofLp q).1 + indicatorVA M q
    exact bot_lt_iff_ne_bot.2 (EReal.add_ne_bot_iff.2 ⟨(hp.2 _).ne', hb2 q⟩)

/-- **Proposition 11.32(b)**: the image `Af` of a proper, convex, piecewise linear-quadratic
function under a linear map is convex and lower semicontinuous with polyhedral domain; it is either
proper and piecewise linear-quadratic, or `-∞` on its domain. -/
theorem IsPiecewiseLinearQuadratic.fiberInfimum_properties {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hp : IsProper f) (hc : Convex ℝ (epigraph f))
    (A : E →L[ℝ] F) :
    Convex ℝ (epigraph (fiberInfimum A f)) ∧ LowerSemicontinuous (fiberInfimum A f) ∧
      IsPolyhedral (effectiveDomain (fiberInfimum A f)) ∧
      ((IsProper (fiberInfimum A f) ∧ IsPiecewiseLinearQuadratic (fiberInfimum A f)) ∨
        ∀ u ∈ effectiveDomain (fiberInfimum A f), fiberInfimum A f u = ⊥) := by
  obtain ⟨h1, h2, h3⟩ := fiberLift_properties A hf hp hc
  rw [← parametricValue_fiberLift A hp]
  exact h1.parametricValue_properties h2 h3

/-- The joint function `(x₁, x₂) ↦ f₁ x₁ + f₂ x₂`. -/
noncomputable def sumLift (f₁ f₂ : E → EReal) (q : WithLp 2 (E × E)) : EReal :=
  f₁ (WithLp.ofLp q).1 + f₂ (WithLp.ofLp q).2

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem fiberInfimum_sumLift (f₁ f₂ : E → EReal) :
    fiberInfimum (l2Fst E E + l2Snd E E) (sumLift f₁ f₂) = epiSum f₁ f₂ := by
  funext x
  rw [epiSum_apply]
  apply le_antisymm
  · refine le_iInf fun w ↦ (iInf_le _ ⟨WithLp.toLp 2 (x - w, w), by simp⟩).trans (le_of_eq ?_)
    simp [sumLift]
  · refine le_iInf fun q ↦ (iInf_le _ (WithLp.ofLp q.1).2).trans (le_of_eq ?_)
    have hq := q.2
    simp only [ContinuousLinearMap.add_apply, l2Fst_apply, l2Snd_apply] at hq
    simp only [sumLift, ← hq, add_sub_cancel_right]

/-- **Proposition 11.32(a)**: the epi-sum of two proper, convex, piecewise linear-quadratic
functions is convex and lower semicontinuous with polyhedral domain; it is either proper and
piecewise linear-quadratic, or `-∞` on its domain. -/
theorem IsPiecewiseLinearQuadratic.epiSum_properties {f₁ f₂ : E → EReal}
    (hf₁ : IsPiecewiseLinearQuadratic f₁) (hp₁ : IsProper f₁) (hc₁ : Convex ℝ (epigraph f₁))
    (hf₂ : IsPiecewiseLinearQuadratic f₂) (hp₂ : IsProper f₂) (hc₂ : Convex ℝ (epigraph f₂)) :
    Convex ℝ (epigraph (epiSum f₁ f₂)) ∧ LowerSemicontinuous (epiSum f₁ f₂) ∧
      IsPolyhedral (effectiveDomain (epiSum f₁ f₂)) ∧
      ((IsProper (epiSum f₁ f₂) ∧ IsPiecewiseLinearQuadratic (epiSum f₁ f₂)) ∨
        ∀ x ∈ effectiveDomain (epiSum f₁ f₂), epiSum f₁ f₂ x = ⊥) := by
  have hplq : IsPiecewiseLinearQuadratic (sumLift f₁ f₂) := by
    have h1 : IsPiecewiseLinearQuadratic (fun q : WithLp 2 (E × E) ↦ f₁ (WithLp.ofLp q).1) := by
      simpa using hf₁.compAffine (l2Fst E E) 0
    have h2 : IsPiecewiseLinearQuadratic (fun q : WithLp 2 (E × E) ↦ f₂ (WithLp.ofLp q).2) := by
      simpa using hf₂.compAffine (l2Snd E E) 0
    exact h1.add h2
  have hpr : IsProper (sumLift f₁ f₂) := by
    obtain ⟨x₁, hx₁⟩ := hp₁.1
    obtain ⟨x₂, hx₂⟩ := hp₂.1
    refine ⟨⟨WithLp.toLp 2 (x₁, x₂), EReal.add_lt_top hx₁.ne hx₂.ne⟩, fun q ↦ ?_⟩
    exact bot_lt_iff_ne_bot.2 (EReal.add_ne_bot_iff.2 ⟨(hp₁.2 _).ne', (hp₂.2 _).ne'⟩)
  have hcv : Convex ℝ (epigraph (sumLift f₁ f₂)) := by
    have hc1 : Convex ℝ (epigraph (fun q : WithLp 2 (E × E) ↦ f₁ (WithLp.ofLp q).1)) := by
      simpa using convex_epigraph_compAffine hc₁ (l2Fst E E) 0
    have hc2 : Convex ℝ (epigraph (fun q : WithLp 2 (E × E) ↦ f₂ (WithLp.ofLp q).2)) := by
      simpa using convex_epigraph_compAffine hc₂ (l2Snd E E) 0
    exact convex_epigraph_add_of_ne_bot hc1 hc2 (fun q ↦ (hp₁.2 _).ne') (fun q ↦ (hp₂.2 _).ne')
  rw [← fiberInfimum_sumLift]
  exact hplq.fiberInfimum_properties hpr hcv _

end RW
