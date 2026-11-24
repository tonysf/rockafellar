/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 11: conjugate formulas in the piecewise linear-quadratic case

**Corollary 11.33**: for proper, convex, piecewise linear-quadratic functions, the conjugate
formulas of Theorem 11.23 hold without closure:
(a) `(f₁ + f₂)* = f₁* □ f₂*` when `f₁ + f₂ ≢ ∞` (`fenchelConjugate_add_of_plq`);
(b) `(g ∘ A)* = A* g*` when `g ∘ A ≢ ∞` (`fenchelConjugate_comp_of_plq`);
(c) `φ*(v) = inf_y f*(v, y) - ⟪y, ū⟫` for `φ = f(·, ū) ≢ ∞`
(`fenchelConjugate_partialFunction_of_plq`).

As in the book, the dual operations in 11.23 produce lower semicontinuous functions here by
Proposition 11.32 (applied to the conjugates, which are piecewise linear-quadratic by 11.14(b)), so
the closures can be omitted.
-/

import RockafellarWets.Chapter11.PiecewiseLinearQuadraticOperations

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Corollary 11.33(a)**: `(f₁ + f₂)* = f₁* □ f₂*` for proper, convex, piecewise
linear-quadratic `f₁`, `f₂` with `f₁ + f₂ ≢ ∞`. -/
theorem fenchelConjugate_add_of_plq {f₁ f₂ : E → EReal}
    (hf₁ : IsPiecewiseLinearQuadratic f₁) (hp₁ : IsProper f₁) (hc₁ : Convex ℝ (epigraph f₁))
    (hf₂ : IsPiecewiseLinearQuadratic f₂) (hp₂ : IsProper f₂) (hc₂ : Convex ℝ (epigraph f₂))
    (hm : ∃ x, f₁ x + f₂ x < ⊤) :
    fenchelConjugate (fun x ↦ f₁ x + f₂ x) =
      epiSum (fenchelConjugate f₁) (fenchelConjugate f₂) := by
  have hl₁ := hf₁.lowerSemicontinuous
  have hl₂ := hf₂.lowerSemicontinuous
  have hm' : (effectiveDomain f₁ ∩ effectiveDomain f₂).Nonempty := by
    obtain ⟨x, hx⟩ := hm
    refine ⟨x, ?_, ?_⟩
    · change f₁ x < ⊤
      exact lt_top_iff_ne_top.2 fun h ↦ by
        rw [h, EReal.top_add_of_ne_bot (hp₂.2 x).ne'] at hx
        exact lt_irrefl _ hx
    · change f₂ x < ⊤
      exact lt_top_iff_ne_top.2 fun h ↦ by
        rw [h, EReal.add_top_of_ne_bot (hp₁.2 x).ne'] at hx
        exact lt_irrefl _ hx
  rw [fenchelConjugate_add_eq_epiClosure hp₁ hp₂ hl₁ hl₂ hc₁ hc₂ hm']
  have hlsc := ((hf₁.isPiecewiseLinearQuadratic_fenchelConjugate hp₁ hl₁ hc₁).epiSum_properties
    (isProper_fenchelConjugate hp₁ hl₁ hc₁) (convex_epigraph_fenchelConjugate f₁)
    (hf₂.isPiecewiseLinearQuadratic_fenchelConjugate hp₂ hl₂ hc₂)
    (isProper_fenchelConjugate hp₂ hl₂ hc₂) (convex_epigraph_fenchelConjugate f₂)).2.1
  exact epiClosure_eq_of_lowerSemicontinuous hlsc

/-- **Corollary 11.33(b)**: `(g ∘ A)* = A* g*` for a proper, convex, piecewise linear-quadratic
`g` with `g ∘ A ≢ ∞`. -/
theorem fenchelConjugate_comp_of_plq {g : F → EReal} (hg : IsPiecewiseLinearQuadratic g)
    (hp : IsProper g) (hc : Convex ℝ (epigraph g)) (A : E →L[ℝ] F) (hm : ∃ x, g (A x) < ⊤) :
    fenchelConjugate (fun x ↦ g (A x)) = fiberInfimum A.adjoint (fenchelConjugate g) := by
  have hl := hg.lowerSemicontinuous
  rw [fenchelConjugate_comp_eq_epiClosure A hp hl hc hm]
  have hlsc := ((hg.isPiecewiseLinearQuadratic_fenchelConjugate hp hl hc).fiberInfimum_properties
    (isProper_fenchelConjugate hp hl hc) (convex_epigraph_fenchelConjugate g) A.adjoint).2.1
  exact epiClosure_eq_of_lowerSemicontinuous hlsc

omit [FiniteDimensional ℝ E] in
/-- The conjugate of a translate: `(f(· + c))*(w) = f*(w) - ⟪w, c⟫`. -/
theorem fenchelConjugate_comp_add_const (f : E → EReal) (c w : E) :
    fenchelConjugate (fun q ↦ f (q + c)) w =
      fenchelConjugate f w + ((-⟪w, c⟫_ℝ : ℝ) : EReal) := by
  have key : ∀ (a b : ℝ) (X : EReal),
      (a : EReal) - X = ((a + b : ℝ) : EReal) - X + ((-b : ℝ) : EReal) := by
    intro a b X
    induction X using EReal.rec with
    | bot => simp
    | top => simp
    | coe x =>
      rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]
      congr 1
      ring
  simp only [fenchelConjugate]
  rw [ereal_iSup_add]
  apply le_antisymm
  · refine iSup_le fun q ↦ le_iSup_of_le (q + c) (le_of_eq ?_)
    rw [key (⟪w, q⟫_ℝ) (⟪w, c⟫_ℝ), inner_add_right]
  · refine iSup_le fun z ↦ le_iSup_of_le (z - c) (le_of_eq ?_)
    rw [sub_add_cancel, key (⟪w, z - c⟫_ℝ) (⟪w, c⟫_ℝ), inner_sub_right, sub_add_cancel]

/-- **Corollary 11.33(c)**: for a proper, convex, piecewise linear-quadratic `f` on `E × F` and
`φ = f(·, u₀) ≢ ∞`, one has `φ*(v) = inf_y f*(v, y) - ⟪y, u₀⟫`. -/
theorem fenchelConjugate_partialFunction_of_plq {f : WithLp 2 (E × F) → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hp : IsProper f) (hc : Convex ℝ (epigraph f)) {u₀ : F}
    (hm : ∃ x, f (WithLp.toLp 2 (x, u₀)) < ⊤) (v : E) :
    fenchelConjugate (partialFunction f u₀) v =
      ⨅ y : F, fenchelConjugate f (WithLp.toLp 2 (v, y)) - ((⟪y, u₀⟫_ℝ : ℝ) : EReal) := by
  set c : WithLp 2 (E × F) := WithLp.toLp 2 ((0 : E), u₀) with hcdef
  set g : WithLp 2 (E × F) → EReal := fun q ↦ f (q + c) with hgdef
  have hgL : partialFunction f u₀ = fun x ↦ g (partialEmbeddingDerivative x) := by
    funext x
    simp only [partialFunction, hgdef, hcdef]
    congr 1
    apply WithLp.ofLp_injective
    simp [partialEmbeddingDerivative]
  have hgplq : IsPiecewiseLinearQuadratic g := by
    simpa using hf.compAffine (ContinuousLinearMap.id ℝ (WithLp 2 (E × F))) c
  have hgp : IsProper g := by
    obtain ⟨x, hx⟩ := hm
    refine ⟨⟨WithLp.toLp 2 (x, (0 : F)), ?_⟩, fun q ↦ hp.2 _⟩
    change f (WithLp.toLp 2 (x, (0 : F)) + c) < ⊤
    convert hx using 2
    apply WithLp.ofLp_injective
    simp [hcdef]
  have hgc : Convex ℝ (epigraph g) := by
    simpa using convex_epigraph_compAffine hc (ContinuousLinearMap.id ℝ (WithLp 2 (E × F))) c
  have hgm : ∃ x, g (partialEmbeddingDerivative x) < ⊤ := by
    obtain ⟨x, hx⟩ := hm
    exact ⟨x, by rw [← congrFun hgL x]; exact hx⟩
  rw [hgL, fenchelConjugate_comp_of_plq hgplq hgp hgc partialEmbeddingDerivative hgm]
  simp only [fiberInfimum]
  apply le_antisymm
  · refine le_iInf fun y ↦ (iInf_le _ ⟨WithLp.toLp 2 (v, y), by simp⟩).trans (le_of_eq ?_)
    rw [hgdef, fenchelConjugate_comp_add_const, hcdef, WithLp.prod_inner_apply]
    simp [sub_eq_add_neg]
  · refine le_iInf fun ⟨w, hwv⟩ ↦ (iInf_le _ (WithLp.ofLp w).2).trans (le_of_eq ?_)
    have hw : (WithLp.ofLp w).1 = v := by simpa using hwv
    rw [hgdef, fenchelConjugate_comp_add_const, hcdef, WithLp.prod_inner_apply]
    have hw' : WithLp.toLp 2 (v, (WithLp.ofLp w).2) = w := by
      rw [← hw, Prod.mk.eta, WithLp.toLp_ofLp]
    rw [hw']
    simp [sub_eq_add_neg]

end RW
