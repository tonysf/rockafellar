/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Full amenability of second subderivatives and the subgradient derivative formula

Proposition 13.49 (the full amenability clause, `fullyAmenableAt_secondSubderivative`) and
Exercise 13.50 (`subgradient_derivative_formula_in_full_amenability`).

For `f = g ∘ G` near `x̄` with `g` convex piecewise linear-quadratic, `G` of class `C²` and the
basic qualification, formula 13(19) of Theorem 13.14 reads
`d²f(x̄ ∣ v̄)(w) = φ(Φ(w))` with `Φ(w) = (w, ∇²G(x̄)[w, w])` and
`φ(w, z) = d²f̄(x̄ ∣ v̄)(w) + σ_Y(z)` (`secondSubderivative_comp_eq_separableSum`), where
`f̄ = g(G(x̄) + ∇G(x̄)(· - x̄))` and `σ_Y` is the support function of the multiplier set
`Y = Y(x̄, v̄)`.  Since `Y` is a nonempty compact polyhedral set, `σ_Y` is finite, convex and
piecewise linear (11.14), `φ` is convex piecewise linear-quadratic (13.9) and the qualification for
`φ ∘ Φ` reduces to `∇Φ(w)*(p, 0) = p`; so `d²f(x̄ ∣ v̄)` is fully amenable at every point of its
domain.  The chain rule for amenable functions (10.6), the product rule 10.5 and 8.25 then compute
`∂[d²f(x̄ ∣ v̄)]`, and Theorem 13.40 (13.41) turns this into the formula of 13.50.
-/

import RockafellarWets.Chapter13.SecondSubderivativeConvexity
import RockafellarWets.Chapter13.ParabolicAmenable
import RockafellarWets.Chapter13.IndicatorSecondOrder
import RockafellarWets.Chapter13.PenaltyOptimality
import RockafellarWets.Chapter13.NormalConeProjections
import RockafellarWets.Chapter11.PiecewiseLinearQuadraticConjugacy
import RockafellarWets.Chapter11.SupportConjugates
import RockafellarWets.Chapter10.SeparableSubgradients
import RockafellarWets.Chapter10.SeparableSubderivatives
import RockafellarWets.Chapter10.AmenableSums
import RockafellarWets.Chapter10.AmenableFunctionCalculus
import RockafellarWets.Chapter8.SupportSubgradients
import RockafellarWets.Chapter6.ProductCones
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

universe u

/-! ### Auxiliary facts -/

section Aux

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]

/-- The solution set of a linear equation is polyhedral. -/
theorem isPolyhedral_setOf_apply_eq (A : T →L[ℝ] E) (v : E) : IsPolyhedral {y | A y = v} := by
  set b := stdOrthonormalBasis ℝ E
  have heq : {y | A y = v} = ⋂ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      ({y | ((innerSL ℝ (b i)).comp A) y ≤ ⟪b i, v⟫_ℝ} ∩
        {y | ((innerSL ℝ (-b i)).comp A) y ≤ ⟪-b i, v⟫_ℝ}) := by
    ext y
    simp only [mem_setOf_eq, mem_iInter, Finset.mem_univ, true_implies, mem_inter_iff,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_neg_left, neg_le_neg_iff]
    constructor
    · rintro h i; rw [h]; exact ⟨le_rfl, le_rfl⟩
    · intro h
      rw [← b.sum_repr' (A y), ← b.sum_repr' v]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [le_antisymm (h i).1 (h i).2]
  rw [heq]
  exact IsPolyhedral.iInter_finset _ _ fun i _ ↦
    (isPolyhedral_linearHalfspace _ _).inter (isPolyhedral_linearHalfspace _ _)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ T] in
/-- `cl (C × T) = cl C × T` in the Euclidean product. -/
theorem closure_l2ProdSet_univ (C : Set E) :
    closure (l2ProdSet C (univ : Set T)) = l2ProdSet (closure C) univ := by
  refine Subset.antisymm (closure_minimal (fun z hz ↦ ⟨subset_closure hz.1, mem_univ _⟩)
    (isClosed_l2ProdSet isClosed_closure isClosed_univ)) ?_
  rintro z ⟨hz, -⟩
  obtain ⟨cs, hcs, hlim⟩ := mem_closure_iff_seq_limit.1 hz
  have h1 : Tendsto (fun n ↦ (cs n, z.snd)) atTop (𝓝 (z.fst, z.snd)) :=
    hlim.prodMk_nhds tendsto_const_nhds
  have h2 := ((WithLp.prodContinuousLinearEquiv 2 ℝ E T).symm.continuous.tendsto _).comp h1
  have h3 : Tendsto (fun n ↦ WithLp.toLp 2 (cs n, z.snd)) atTop (𝓝 z) := by simpa using h2
  exact mem_closure_of_tendsto h3 (Eventually.of_forall fun n ↦ ⟨hcs n, mem_univ _⟩)

/-- The inner map `Φ(w) = (w, B w w)` of the representation of second subderivatives. -/
noncomputable def quadraticGraphMap (B : E →L[ℝ] E →L[ℝ] T) (w : E) : WithLp 2 (E × T) :=
  WithLp.toLp 2 (w, B w w)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ T] in
theorem hasFDerivAt_quadraticGraphMap (B : E →L[ℝ] E →L[ℝ] T) (w : E) :
    HasFDerivAt (quadraticGraphMap B)
      ((WithLp.prodContinuousLinearEquiv 2 ℝ E T).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.id ℝ E).prod (B w + B.flip w))) w := by
  have hB : HasFDerivAt (fun w ↦ B w w) (B w + B.flip w) w := by
    have := HasFDerivAt.comp (f := fun x : E ↦ (x, x)) w (B.isBoundedBilinearMap.hasFDerivAt (w, w))
      ((hasFDerivAt_id w).prodMk (hasFDerivAt_id w))
    convert this using 1
  have h := (hasFDerivAt_id w).prodMk hB
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ E T).symm.hasFDerivAt.comp w h

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ T] in
theorem contDiff_quadraticGraphMap (B : E →L[ℝ] E →L[ℝ] T) :
    ContDiff ℝ 2 (quadraticGraphMap B) := by
  have hB : ContDiff ℝ 2 (fun w : E ↦ B w w) :=
    B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ E T).symm.contDiff.comp (contDiff_id.prodMk hB)

/-- The adjoint of `∇Φ(w)` at `(p, q)` is `p + (B w)*q + (B.flip w)*q`. -/
theorem fderiv_quadraticGraphMap_adjoint (B : E →L[ℝ] E →L[ℝ] T) (w p : E) (q : T) :
    (fderiv ℝ (quadraticGraphMap B) w).adjoint (WithLp.toLp 2 (p, q)) =
      p + (B w).adjoint q + (B.flip w).adjoint q := by
  rw [(hasFDerivAt_quadraticGraphMap B w).fderiv]
  refine ext_inner_right ℝ fun w' ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.add_apply,
    WithLp.prodContinuousLinearEquiv_symm_apply, WithLp.prod_inner_apply, inner_add_left,
    inner_add_right, ContinuousLinearMap.adjoint_inner_left]
  ring

end Aux

/-! ### The representation `d²f(x̄ ∣ v̄) = φ ∘ Φ` -/

section Representation

variable {E T : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]

/-- The linearization `f̄ = g(G(x̄) + ∇G(x̄)(· - x̄))` of `f = g ∘ G` at `x̄`. -/
noncomputable def linearizedComposite (G : E → T) (g : T → EReal) (x : E) (z : E) : EReal :=
  g (G x + fderiv ℝ G x (z - x))

/-- The outer function `φ(w, z) = d²f̄(x̄ ∣ v̄)(w) + σ_Y(z)` of the representation. -/
noncomputable def secondOrderOuter (G : E → T) (g : T → EReal) (x v : E) :
    WithLp 2 (E × T) → EReal :=
  separableSum (secondSubderivative (linearizedComposite G g x) x v)
    (supportFunction (multiplierSet G g x v))

omit [FiniteDimensional ℝ T] in
/-- A bounded set has a finite support function. -/
theorem supportFunction_lt_top_of_bounded_set {Y : Set T} (hY : Bornology.IsBounded Y) (z : T) :
    supportFunction Y z < ⊤ := by
  obtain ⟨R, hR⟩ := hY.exists_norm_le
  refine lt_of_le_of_lt ((supportFunction_le_iff _ _ _).2 fun y hy ↦ ?_)
    (EReal.coe_lt_top (R * ‖z‖))
  refine EReal.coe_le_coe_iff.2 ((real_inner_le_norm y z).trans ?_)
  exact mul_le_mul_of_nonneg_right (hR y hy) (norm_nonneg z)

/-- **Formula 13(19) as a composition**: for `g` convex piecewise linear-quadratic, `G` of class
`C²` with the basic qualification at `x̄` and `v̄ ∈ ∂(g ∘ G)(x̄)`, the linearization `f̄` is convex
piecewise linear-quadratic with `∂f̄(x̄) = ∂(g ∘ G)(x̄)`, the multiplier set `Y(x̄, v̄)` is nonempty,
compact, convex and polyhedral, and `d²(g ∘ G)(x̄ ∣ v̄)(w) = d²f̄(x̄ ∣ v̄)(w) + σ_Y(∇²G(x̄)[w, w])`. -/
theorem secondSubderivative_comp_eq_separableSum {G : E → T} (hG : ContDiff ℝ 2 G)
    {g : T → EReal} (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E}
    (hx : G x ∈ effectiveDomain g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    {v : E} (hv : v ∈ subdifferential (g ∘ G) x) :
    IsPiecewiseLinearQuadratic (linearizedComposite G g x) ∧
    Convex ℝ (epigraph (linearizedComposite G g x)) ∧
    subdifferential (linearizedComposite G g x) x = subdifferential (g ∘ G) x ∧
    (multiplierSet G g x v).Nonempty ∧ IsCompact (multiplierSet G g x v) ∧
    Convex ℝ (multiplierSet G g x v) ∧ IsPolyhedral (multiplierSet G g x v) ∧
    ProperlyTwiceEpiDifferentiableAt (g ∘ G) x v ∧
    ∀ w, secondSubderivative (g ∘ G) x v w =
      secondOrderOuter G g x v (quadraticGraphMap (fderiv ℝ (fderiv ℝ G) x) w) := by
  have hfin : g (G x) = ((g (G x)).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx) (hg.ne_bot _)).symm
  have hl := hg.lowerSemicontinuous
  have hr : IsSubdifferentiallyRegularAt g (G x) :=
    (isSubdifferentiallyRegularAt_of_convex hgc (locallyLscAt_of_lowerSemicontinuous_finite hl hfin)).1
  obtain ⟨-, hY, -, hPLQ⟩ := chain_rule_for_second_subderivatives hG hl hr hQ
  obtain ⟨hYne, hYc, hYk, -⟩ := hY v hv
  obtain ⟨⟨h1, h2, -, -, h5⟩, hv'⟩ := hPLQ hg hgc
  obtain ⟨-, hpte, -, -, hmax, -, -⟩ := hv' v hv
  have hpoly : IsPolyhedral (multiplierSet G g x v) := by
    have heq : multiplierSet G g x v =
        subdifferential g (G x) ∩ {y | (fderiv ℝ G x).adjoint y = v} := rfl
    rw [heq]
    exact (hg.convex_subgradient_properties hgc hx).2.1.inter (isPolyhedral_setOf_apply_eq _ v)
  refine ⟨h1, h2, h5, hYne, hYk, hYc, hpoly, hpte, fun w ↦ ?_⟩
  obtain ⟨y₀, hy₀, hy₀max, heq⟩ := hmax w
  have hsupp : supportFunction (multiplierSet G g x v) (fderiv ℝ (fderiv ℝ G) x w w) =
      ((⟪y₀, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal) :=
    le_antisymm ((supportFunction_le_iff _ _ _).2 fun y hy ↦ EReal.coe_le_coe_iff.2 (hy₀max y hy))
      (inner_le_supportFunction hy₀ _)
  rw [heq]
  simp only [secondOrderOuter, separableSum, quadraticGraphMap, WithLp.toLp_fst, WithLp.toLp_snd,
    hsupp]
  rfl

/-- The properties of the outer function `φ = d²f̄(x̄ ∣ v̄) ⊕ σ_Y`: proper, lsc, convex, piecewise
linear-quadratic, with `σ_Y` finite, and the qualification for `φ ∘ Φ` at every point. -/
theorem secondOrderOuter_properties {G : E → T} (hG : ContDiff ℝ 2 G)
    {g : T → EReal} (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E}
    (hx : G x ∈ effectiveDomain g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    {v : E} (hv : v ∈ subdifferential (g ∘ G) x) :
    IsProper (secondOrderOuter G g x v) ∧ LowerSemicontinuous (secondOrderOuter G g x v) ∧
    Convex ℝ (epigraph (secondOrderOuter G g x v)) ∧
    IsPiecewiseLinearQuadratic (secondOrderOuter G g x v) ∧
    (∀ z, supportFunction (multiplierSet G g x v) z < ⊤) ∧
    IsProper (secondSubderivative (linearizedComposite G g x) x v) ∧
    LowerSemicontinuous (secondSubderivative (linearizedComposite G g x) x v) ∧
    ∀ w₀, ∀ p ∈ normalCone (closure (effectiveDomain (secondOrderOuter G g x v)))
      (quadraticGraphMap (fderiv ℝ (fderiv ℝ G) x) w₀),
      (fderiv ℝ (quadraticGraphMap (fderiv ℝ (fderiv ℝ G) x)) w₀).adjoint p = 0 → p = 0 := by
  obtain ⟨h1, h2, h5, hYne, hYk, hYc, hpoly, -, -⟩ :=
    secondSubderivative_comp_eq_separableSum hG hg hgc hx hQ hv
  set B := fderiv ℝ (fderiv ℝ G) x with hB
  set Y := multiplierSet G g x v with hY
  set h₀ := secondSubderivative (linearizedComposite G g x) x v with hh₀
  have hvbar : v ∈ subdifferential (linearizedComposite G g x) x := by rw [h5]; exact hv
  have hxd : x ∈ effectiveDomain (linearizedComposite G g x) := by
    change g (G x + fderiv ℝ G x (x - x)) < ⊤
    rw [sub_self, map_zero, add_zero]; exact hx
  obtain ⟨-, hv13, -⟩ := (piecewise_linear_quadratic_second_order h1 h2 hxd)
  obtain ⟨hp₀, hc₀, hq₀, -⟩ := (hv13 v hvbar)
  have hpσ := isProper_supportFunction hYne
  have hσtop : ∀ z, supportFunction Y z < ⊤ := supportFunction_lt_top_of_bounded_set hYk.isBounded
  have hσbot : ∀ z, supportFunction Y z ≠ ⊥ := fun z ↦ (hpσ.2 z).ne'
  have h₀bot : ∀ w, h₀ w ≠ ⊥ := fun w ↦ (hp₀.2 w).ne'
  have hprop : IsProper (secondOrderOuter G g x v) := by
    obtain ⟨a, ha⟩ := hp₀.1
    refine ⟨⟨WithLp.toLp 2 (a, 0), ?_⟩, fun p ↦ ?_⟩
    · change h₀ a + supportFunction Y 0 < ⊤
      exact EReal.add_lt_top ha.ne (hσtop 0).ne
    · change ⊥ < h₀ p.fst + supportFunction Y p.snd
      exact EReal.bot_lt_add_iff.2 ⟨hp₀.2 _, hpσ.2 _⟩
  have hlsc : LowerSemicontinuous (secondOrderOuter G g x v) :=
    lowerSemicontinuous_separableSum hq₀.lowerSemicontinuous
      (lowerSemicontinuous_supportFunction Y) hp₀ hpσ
  have hconv : Convex ℝ (epigraph (secondOrderOuter G g x v)) :=
    convex_epigraph_separableSum hc₀ (convex_epigraph_of_sublinear (sublinear_supportFunction Y))
      h₀bot hσbot
  have hplqσ : IsPiecewiseLinearQuadratic (supportFunction Y) := by
    obtain ⟨hpδ, hlδ, hcδ⟩ := indicatorVA_proper_lsc_convex hYk.isClosed hYc hYne
    rw [← fenchelConjugate_indicatorVA]
    exact (isPiecewiseLinearQuadratic_fenchelConjugate_iff hpδ hlδ hcδ).2
      (isPiecewiseLinearQuadratic_indicatorVA hpoly)
  have hdomσ : effectiveDomain (supportFunction Y) = univ := eq_univ_of_forall hσtop
  have hdom : effectiveDomain (secondOrderOuter G g x v) = l2ProdSet (effectiveDomain h₀) univ := by
    rw [secondOrderOuter, effectiveDomain_separableSum hp₀ hpσ, hdomσ]
  refine ⟨hprop, hlsc, hconv, isPiecewiseLinearQuadratic_separableSum hq₀ hplqσ, hσtop, hp₀,
    hq₀.lowerSemicontinuous, fun w₀ p hp h0 ↦ ?_⟩
  rw [hdom, closure_l2ProdSet_univ, quadraticGraphMap, normalCone_l2ProdSet, normalCone_univ]
    at hp
  obtain ⟨-, hp2⟩ := hp
  have hp' : p = WithLp.toLp 2 (p.fst, 0) := WithLp.ofLp_injective 2 (Prod.ext rfl hp2)
  rw [hp', fderiv_quadraticGraphMap_adjoint, map_zero, map_zero, add_zero, add_zero] at h0
  rw [hp', h0]
  rfl

/-- The model of full amenability of `d²(g ∘ G)(x̄ ∣ v̄)` at a point `w₀` of its domain. -/
theorem fullyAmenableAt_secondSubderivative_comp {G : E → T} (hG : ContDiff ℝ 2 G)
    {g : T → EReal} (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E}
    (hx : G x ∈ effectiveDomain g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    {v : E} (hv : v ∈ subdifferential (g ∘ G) x) {w₀ : E}
    (hw₀ : secondSubderivative (g ∘ G) x v w₀ ≠ ⊤) :
    FullyAmenableAt (secondSubderivative (g ∘ G) x v) w₀ := by
  obtain ⟨-, -, -, -, -, -, -, hpte, hrep⟩ :=
    secondSubderivative_comp_eq_separableSum hG hg hgc hx hQ hv
  obtain ⟨hprop, hlsc, hconv, hplq, -, -, -, hqual⟩ :=
    secondOrderOuter_properties hG hg hgc hx hQ hv
  exact ⟨{
    Target := WithLp 2 (E × T)
    outer := secondOrderOuter G g x v
    inner := quadraticGraphMap (fderiv ℝ (fderiv ℝ G) x)
    neighborhood := univ
    isOpen := isOpen_univ
    mem := mem_univ w₀
    finite := ⟨(hpte.2.2 w₀).ne', hw₀⟩
    proper := hprop
    lsc := hlsc
    convex := hconv
    smooth := (contDiff_quadraticGraphMap _).contDiffOn
    eqOn := fun w _ ↦ hrep w
    qualification := hqual w₀
    plq := fun _ ↦ hplq }⟩

/-- `g ∘ G` is fully amenable at `x̄` for `g` convex piecewise linear-quadratic and `G` of class
`C²` with the basic qualification. -/
theorem fullyAmenableAt_comp_of_plq {G : E → T} (hG : ContDiff ℝ 2 G)
    {g : T → EReal} (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E}
    (hx : G x ∈ effectiveDomain g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    FullyAmenableAt (g ∘ G) x := by
  have hfin : g (G x) = ((g (G x)).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx) (hg.ne_bot _)).symm
  have hp : IsProper g := ⟨⟨G x, hx⟩, fun y ↦ lt_of_le_of_ne bot_le (hg.ne_bot y).symm⟩
  exact ⟨{
    Target := T
    outer := g
    inner := G
    neighborhood := univ
    isOpen := isOpen_univ
    mem := mem_univ x
    finite := ⟨hg.ne_bot _, ne_of_lt hx⟩
    proper := hp
    lsc := hg.lowerSemicontinuous
    convex := hgc
    smooth := hG.contDiffOn
    eqOn := fun _ _ ↦ rfl
    qualification := fun y hy h0 ↦ hQ y (by
      rwa [horizonSubdifferential_eq_normalCone_closure_domain hp hg.lowerSemicontinuous hgc hfin])
      h0
    plq := fun _ ↦ hg }⟩

end Representation

/-! ### Proposition 13.49 -/

section Proposition1349

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Proposition 13.49**, the full amenability clause: if `f` is fully amenable at `x̄` and
`v̄ ∈ ∂f(x̄)`, then `d²f(x̄ ∣ v̄)` is fully amenable at every point of its domain. -/
theorem FullyAmenableAt.fullyAmenableAt_secondSubderivative {f : E → EReal} {x v : E}
    (hf : FullyAmenableAt f x) (hv : v ∈ subdifferential f x) {w : E}
    (hw : secondSubderivative f x v w ≠ ⊤) :
    FullyAmenableAt (secondSubderivative f x v) w := by
  obtain ⟨M⟩ := hf
  obtain ⟨G₀, hG₀, -, hloc, hdom, hQ⟩ := M.exists_global_representation
  have hsub : subdifferential f x = subdifferential (M.outer ∘ G₀) x :=
    subdifferential_eq_of_eventuallyEq hloc
  have hd2 : secondSubderivative f x v = secondSubderivative (M.outer ∘ G₀) x v :=
    funext fun w ↦ secondSubderivative_congr_nhds hloc v w
  rw [hd2] at hw ⊢
  exact fullyAmenableAt_secondSubderivative_comp hG₀ (M.plq rfl) M.convex hdom hQ (hsub ▸ hv) hw

/-- **Proposition 13.49** (prox-regularity and amenability of second subderivatives), adapted.
* If `f` is prox-regular and (properly) twice epi-differentiable at `x̄` for `v̄`, there is `ρ ≥ 0`
  with `d²f(x̄ ∣ v̄) + ρ‖·‖²` convex, `d²f(x̄ ∣ v̄)` proper and prox-regular at every point,
  `DT(x̄ ∣ v̄) + ρI` maximal monotone for every sufficiently close `f`-attentive localization `T`
  of `∂f`, and `D(∂f)(x̄ ∣ v̄) + ρI` maximal monotone when `f` is subdifferentially continuous at
  `x̄` for `v̄` (the correction: without subdifferential continuity this last claim fails,
  `SecondSubderivativeConvexityCounterexample.printed_1349_counterexample`).
* If `f` is fully amenable at `x̄` and `v̄ ∈ ∂f(x̄)`, all of this holds with `D(∂f)(x̄ ∣ v̄)`, and
  `d²f(x̄ ∣ v̄)` is fully amenable at every point of its domain. -/
theorem prox_regularity_and_amenability_of_second_subderivatives {f : E → EReal} {x v : E} :
    (IsProxRegularAt f x v → TwiceEpiDifferentiableAt f x v → ∃ ρ ≥ 0,
      Convex ℝ (epigraph (fun w ↦ secondSubderivative f x v w + ((ρ * ‖w‖ ^ 2 : ℝ) : EReal))) ∧
      IsProper (secondSubderivative f x v) ∧
      (∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → SvMaximalMonotone (fun w ↦
        (fun z ↦ z + ρ • w) '' graphicalDerivative (attentiveLocalization f x v ε) x v w)) ∧
      (IsSubdifferentiallyContinuousAt f x v → SvMaximalMonotone (fun w ↦
        (fun z ↦ z + ρ • w) '' graphicalDerivative (subdifferential f) x v w)) ∧
      ∀ w, IsProxRegularAtPoint (secondSubderivative f x v) w) ∧
    (FullyAmenableAt f x → v ∈ subdifferential f x → ∃ ρ ≥ 0,
      Convex ℝ (epigraph (fun w ↦ secondSubderivative f x v w + ((ρ * ‖w‖ ^ 2 : ℝ) : EReal))) ∧
      SvMaximalMonotone (fun w ↦
        (fun z ↦ z + ρ • w) '' graphicalDerivative (subdifferential f) x v w) ∧
      (∀ w, IsProxRegularAtPoint (secondSubderivative f x v) w) ∧
      ∀ w, secondSubderivative f x v w ≠ ⊤ → FullyAmenableAt (secondSubderivative f x v) w) := by
  refine ⟨prox_regularity_of_second_subderivatives, fun hf hv ↦ ?_⟩
  obtain ⟨ρ, hρ, h1, h2, h3⟩ := hf.secondSubderivative_convexity hv
  exact ⟨ρ, hρ, h1, h2, h3, fun w hw ↦ hf.fullyAmenableAt_secondSubderivative hv hw⟩

end Proposition1349

/-! ### Scaling of subgradients -/

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ereal_two_mul_half_mul (a : EReal) :
    ((2 : ℝ) : EReal) * (((1 / 2 : ℝ) : EReal) * a) = a := by
  rw [← mul_assoc, ← EReal.coe_mul]; norm_num

theorem ereal_half_mul_two_mul (a : EReal) :
    ((1 / 2 : ℝ) : EReal) * (((2 : ℝ) : EReal) * a) = a := by
  rw [← mul_assoc, ← EReal.coe_mul]; norm_num

theorem continuous_ereal_coe_mul {r : ℝ} (hr : r ≠ 0) :
    Continuous (fun a : EReal ↦ (r : EReal) * a) := by
  have hr' : (r : EReal) ≠ 0 := by exact_mod_cast hr
  exact continuous_iff_continuousAt.2 fun a ↦
    (EReal.continuousAt_mul (p := ((r : EReal), a)) (Or.inl hr') (Or.inl hr')
      (Or.inl (EReal.coe_ne_bot r)) (Or.inl (EReal.coe_ne_top r))).comp
      (continuousAt_const.prodMk continuousAt_id)

theorem mem_regularSubdifferential_half_mul_iff {h : E → EReal} {w z : E} :
    z ∈ regularSubdifferential (fun y ↦ ((1 / 2 : ℝ) : EReal) * h y) w ↔
      (2 : ℝ) • z ∈ regularSubdifferential h w := by
  have h2 : (0 : EReal) ≤ ((2 : ℝ) : EReal) := by exact_mod_cast (by norm_num : (0 : ℝ) ≤ 2)
  have h12 : (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) := by
    exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor
  · rintro ⟨c, hc, hε⟩
    simp only at hc hε
    refine ⟨2 * c, ?_, fun ε hε0 ↦ ?_⟩
    · rw [← ereal_two_mul_half_mul (h w), hc, ← EReal.coe_mul]
    filter_upwards [hε (ε / 2) (by positivity)] with y hy
    have := mul_le_mul_of_nonneg_left hy h2
    rw [ereal_two_mul_half_mul, ← EReal.coe_mul] at this
    refine le_trans (EReal.coe_le_coe_iff.2 (le_of_eq ?_)) this
    rw [real_inner_smul_left]; ring
  · rintro ⟨a, ha, hε⟩
    refine ⟨1 / 2 * a, by simp only; rw [ha, ← EReal.coe_mul], fun ε hε0 ↦ ?_⟩
    filter_upwards [hε (2 * ε) (by positivity)] with y hy
    have := mul_le_mul_of_nonneg_left hy h12
    rw [← EReal.coe_mul] at this
    refine le_trans (EReal.coe_le_coe_iff.2 (le_of_eq ?_)) this
    rw [real_inner_smul_left]; ring

theorem mem_subdifferential_half_mul_iff {h : E → EReal} {w z : E} :
    z ∈ subdifferential (fun y ↦ ((1 / 2 : ℝ) : EReal) * h y) w ↔
      (2 : ℝ) • z ∈ subdifferential h w := by
  rw [mem_subdifferential_iff_exists_seq, mem_subdifferential_iff_exists_seq]
  constructor
  · rintro ⟨⟨c, hc⟩, ws, zs, hws, hfws, hzs, hzlim⟩
    refine ⟨⟨2 * c, by rw [← ereal_two_mul_half_mul (h w), hc, ← EReal.coe_mul]⟩, ws,
      fun n ↦ (2 : ℝ) • zs n, hws, ?_, fun n ↦ mem_regularSubdifferential_half_mul_iff.1 (hzs n),
      hzlim.const_smul _⟩
    have := ((continuous_ereal_coe_mul (r := 2) two_ne_zero).tendsto _).comp hfws
    have e1 : ((fun a : EReal ↦ ((2 : ℝ) : EReal) * a) ∘
        ((fun y ↦ ((1 / 2 : ℝ) : EReal) * h y) ∘ ws)) = h ∘ ws := by
      funext n; simp only [Function.comp_apply]; exact ereal_two_mul_half_mul _
    have e2 : ((2 : ℝ) : EReal) * ((fun y ↦ ((1 / 2 : ℝ) : EReal) * h y) w) = h w :=
      ereal_two_mul_half_mul _
    rwa [e1, e2] at this
  · rintro ⟨⟨a, ha⟩, ws, zs, hws, hfws, hzs, hzlim⟩
    refine ⟨⟨1 / 2 * a, by rw [ha, ← EReal.coe_mul]⟩, ws, fun n ↦ (1 / 2 : ℝ) • zs n, hws, ?_,
      fun n ↦ mem_regularSubdifferential_half_mul_iff.2 ?_, ?_⟩
    · exact ((continuous_ereal_coe_mul (r := 1 / 2) (by norm_num)).tendsto _).comp hfws
    · rw [smul_smul]; norm_num; exact hzs n
    · have := hzlim.const_smul (1 / 2 : ℝ)
      rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at this

end Scaling

/-! ### Exercise 13.50 -/

section Exercise1350

variable {E T : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]

/-- **Exercise 13.50** (subgradient derivative formula in full amenability).  Let `f = g ∘ G` with
`g` convex piecewise linear-quadratic, `G` of class `C²` and the basic qualification at `x̄` (the
setting of 13.14; `f` is then fully amenable at `x̄`), and `v̄ ∈ ∂f(x̄)`.  Then `∂f` is
proto-differentiable at `x̄` for `v̄` and, with `f̄ = g(G(x̄) + ∇G(x̄)(· - x̄))`,
`Y = Y(x̄, v̄)` and `∇²(yG)(x̄)w = (∇²G(x̄)w)* y`,
`D(∂f)(x̄ ∣ v̄)(w) = D(∂f̄)(x̄ ∣ v̄)(w) + {∇²(yG)(x̄)w ∣ y ∈ M(x̄, v̄, w)}`,
`M(x̄, v̄, w) = argmax {⟪w, ∇²(yG)(x̄)w⟫ = ⟪y, ∇²G(x̄)[w, w]⟫ ∣ y ∈ Y}`. -/
theorem subgradient_derivative_formula_in_full_amenability {G : E → T} (hG : ContDiff ℝ 2 G)
    {g : T → EReal} (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E}
    (hx : G x ∈ effectiveDomain g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    {v : E} (hv : v ∈ subdifferential (g ∘ G) x) :
    FullyAmenableAt (g ∘ G) x ∧ IsProtoDifferentiableAt (subdifferential (g ∘ G)) x v ∧
    ∀ w, graphicalDerivative (subdifferential (g ∘ G)) x v w =
      {z | ∃ z₁ ∈ graphicalDerivative (subdifferential (linearizedComposite G g x)) x v w,
        ∃ y ∈ multiplierSet G g x v,
          (∀ y' ∈ multiplierSet G g x v,
            ⟪y', fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ ≤ ⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ) ∧
          z = z₁ + (fderiv ℝ (fderiv ℝ G) x w).adjoint y} := by
  obtain ⟨h1, h2, h5, hYne, hYk, hYc, -, -, hrep⟩ :=
    secondSubderivative_comp_eq_separableSum hG hg hgc hx hQ hv
  obtain ⟨hprop, hlsc, hconv, -, hσtop, hp₀, hlsc₀, hqual⟩ :=
    secondOrderOuter_properties hG hg hgc hx hQ hv
  set B := fderiv ℝ (fderiv ℝ G) x with hB
  set Y := multiplierSet G g x v with hY
  set h₀ := secondSubderivative (linearizedComposite G g x) x v with hh₀
  have hvbar : v ∈ subdifferential (linearizedComposite G g x) x := by rw [h5]; exact hv
  have hxd : x ∈ effectiveDomain (linearizedComposite G g x) := by
    change g (G x + fderiv ℝ G x (x - x)) < ⊤
    rw [sub_self, map_zero, add_zero]; exact hx
  have hfa := fullyAmenableAt_comp_of_plq hG hg hgc hx hQ
  have hfbar := (fullyAmenableAt_of_convex_plq h1 h2 hxd).isProtoDifferentiableAt hvbar
  have hcomp := hfa.isProtoDifferentiableAt hv
  -- symmetry of `∇²G(x̄)`
  have hsymm : ∀ w, B.flip w = B w := by
    intro w
    have hGx : ContDiffAt ℝ 2 G x := hG.contDiffAt
    have hs := hGx.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
    ext w'
    rw [ContinuousLinearMap.flip_apply]
    exact hs w' w
  refine ⟨hfa, hcomp.1, fun w ↦ ?_⟩
  rw [hcomp.2, hfbar.2]
  ext z
  rw [mem_subdifferential_half_mul_iff, mem_setOf_eq]
  have hfun : secondSubderivative (g ∘ G) x v = secondOrderOuter G g x v ∘ quadraticGraphMap B :=
    funext hrep
  -- the value of `σ_Y` at `B w w` is finite
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : ℝ, supportFunction Y (B w w) = d₀ :=
    ⟨_, (EReal.coe_toReal (hσtop _).ne (isProper_supportFunction hYne |>.2 _).ne').symm⟩
  rcases eq_or_ne (h₀ w) ⊤ with htop | hfin
  · -- outside the domain both sides are empty
    have hval : secondSubderivative (g ∘ G) x v w = ⊤ := by
      rw [hrep w]
      change h₀ w + supportFunction Y (B w w) = ⊤
      rw [htop, hd₀, EReal.top_add_coe]
    constructor
    · intro hz
      obtain ⟨⟨c, hc⟩, -⟩ := hz
      rw [hval] at hc; exact absurd hc (EReal.coe_ne_top c).symm
    · rintro ⟨z₁, ⟨⟨c, hc⟩, -⟩, -⟩
      simp only at hc
      rw [show secondSubderivative (linearizedComposite G g x) x v w = ⊤ from htop,
        EReal.coe_mul_top_of_pos (by norm_num)] at hc
      exact absurd hc (EReal.coe_ne_top c).symm
  -- inside the domain
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, h₀ w = c₀ := ⟨_, (EReal.coe_toReal hfin (hp₀.2 w).ne').symm⟩
  have hφval : secondOrderOuter G g x v (quadraticGraphMap B w) = ((c₀ + d₀ : ℝ) : EReal) := by
    change h₀ w + supportFunction Y (B w w) = _
    rw [hc₀, hd₀, EReal.coe_add]
  have hreg : IsSubdifferentiallyRegularAt (secondOrderOuter G g x v) (quadraticGraphMap B w) :=
    (isSubdifferentiallyRegularAt_of_convex hconv
      (locallyLscAt_of_lowerSemicontinuous_finite hlsc hφval)).1
  have hQ' : ∀ y ∈ horizonSubdifferential (secondOrderOuter G g x v) (quadraticGraphMap B w),
      (fderiv ℝ (quadraticGraphMap B) w).adjoint y = 0 → y = 0 := by
    intro y hy h0
    rw [horizonSubdifferential_eq_normalCone_closure_domain hprop hlsc hconv hφval] at hy
    exact hqual w y hy h0
  have hchain := subdifferential_comp_eq_of_regular
    ((contDiff_quadraticGraphMap B).of_le (by norm_num)) hlsc hreg hQ'
  rw [hfun, hchain]
  -- subgradients of the separable sum and of the support function
  have hsep : ∀ q : WithLp 2 (E × T), q ∈ subdifferential (secondOrderOuter G g x v)
      (quadraticGraphMap B w) ↔ q.fst ∈ subdifferential h₀ w ∧
        q.snd ∈ Y ∧ (⟪q.snd, B w w⟫_ℝ : EReal) = supportFunction Y (B w w) := by
    intro q
    rw [quadraticGraphMap, secondOrderOuter, mem_subdifferential_separableSum_iff
      (hlsc₀.lowerSemicontinuousAt w) ((lowerSemicontinuous_supportFunction Y).lowerSemicontinuousAt _)
      hc₀ hd₀, subdifferential_supportFunction hYc hYk.isClosed hYne (hσtop _)]
    rfl
  have hadj : ∀ q : WithLp 2 (E × T), (fderiv ℝ (quadraticGraphMap B) w).adjoint q =
      q.fst + (2 : ℝ) • (B w).adjoint q.snd := by
    intro q
    have hq : q = WithLp.toLp 2 (q.fst, q.snd) := rfl
    rw [hq, fderiv_quadraticGraphMap_adjoint, hsymm w, two_smul, add_assoc]
    rfl
  have hmax : ∀ y ∈ Y, ((⟪y, B w w⟫_ℝ : EReal) = supportFunction Y (B w w) ↔
      ∀ y' ∈ Y, ⟪y', B w w⟫_ℝ ≤ ⟪y, B w w⟫_ℝ) := by
    intro y hy
    constructor
    · intro h y' hy'
      have := inner_le_supportFunction hy' (B w w)
      rw [← h] at this
      exact EReal.coe_le_coe_iff.1 this
    · intro h
      exact le_antisymm (inner_le_supportFunction hy _)
        ((supportFunction_le_iff _ _ _).2 fun y' hy' ↦ EReal.coe_le_coe_iff.2 (h y' hy'))
  constructor
  · rintro ⟨q, hq, hqz⟩
    obtain ⟨hq1, hq2, hq3⟩ := (hsep q).1 hq
    refine ⟨(1 / 2 : ℝ) • q.fst, ?_, q.snd, hq2, (hmax _ hq2).1 hq3, ?_⟩
    · rw [mem_subdifferential_half_mul_iff, smul_smul]; norm_num; exact hq1
    · rw [hadj] at hqz
      have := congrArg (fun t ↦ (1 / 2 : ℝ) • t) hqz
      simp only [smul_add, smul_smul] at this
      norm_num at this
      rw [← this]
  · rintro ⟨z₁, hz₁, y, hy, hymax, rfl⟩
    rw [mem_subdifferential_half_mul_iff] at hz₁
    refine ⟨WithLp.toLp 2 ((2 : ℝ) • z₁, y), (hsep _).2 ⟨hz₁, hy, (hmax y hy).2 hymax⟩, ?_⟩
    rw [hadj]
    simp only [smul_add]
    rfl

/-- **Exercise 13.50** for a fully amenable function: with a representation `f = g ∘ F` near `x̄`
as in the definition (an `AmenableFunctionModel`) and a `C²` extension `G₀` of `F`, `∂f` is
proto-differentiable at `x̄` for `v̄ ∈ ∂f(x̄)` and `D(∂f)(x̄ ∣ v̄)` is given by the formula of
`subgradient_derivative_formula_in_full_amenability` for `g ∘ G₀`. -/
theorem AmenableFunctionModel.subgradient_derivative_formula {f : E → EReal} {x v : E}
    (M : AmenableFunctionModel f x 2 true) (hv : v ∈ subdifferential f x) :
    ∃ G₀ : E → M.Target, ContDiff ℝ 2 G₀ ∧ G₀ =ᶠ[𝓝 x] M.inner ∧
      IsProtoDifferentiableAt (subdifferential f) x v ∧
      ∀ w, graphicalDerivative (subdifferential f) x v w =
        {z | ∃ z₁ ∈ graphicalDerivative (subdifferential (linearizedComposite G₀ M.outer x)) x v w,
          ∃ y ∈ multiplierSet G₀ M.outer x v,
            (∀ y' ∈ multiplierSet G₀ M.outer x v,
              ⟪y', fderiv ℝ (fderiv ℝ G₀) x w w⟫_ℝ ≤ ⟪y, fderiv ℝ (fderiv ℝ G₀) x w w⟫_ℝ) ∧
            z = z₁ + (fderiv ℝ (fderiv ℝ G₀) x w).adjoint y} := by
  obtain ⟨G₀, hG₀, hG₀eq, hloc, hdom, hQ⟩ := M.exists_global_representation
  have hsub : subdifferential f x = subdifferential (M.outer ∘ G₀) x :=
    subdifferential_eq_of_eventuallyEq hloc
  have hv' : v ∈ subdifferential (M.outer ∘ G₀) x := hsub ▸ hv
  obtain ⟨-, hproto, hform⟩ := subgradient_derivative_formula_in_full_amenability hG₀
    (M.plq rfl) M.convex hdom hQ hv'
  have hagree : ∀ᶠ p in 𝓝 (x, v),
      p.2 ∈ subdifferential f p.1 ↔ p.2 ∈ subdifferential (M.outer ∘ G₀) p.1 := by
    have h1 : ∀ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] M.outer ∘ G₀ := hloc.eventually_nhds
    filter_upwards [(continuous_fst.tendsto (x, v)).eventually h1] with p hp
    rw [subdifferential_eq_of_eventuallyEq hp]
  obtain ⟨hiff, hD⟩ := isProtoDifferentiableAt_congr_of_eventually hagree
  refine ⟨G₀, hG₀, hG₀eq, hiff.2 hproto, fun w ↦ ?_⟩
  rw [hD]
  exact hform w

end Exercise1350

end RW
