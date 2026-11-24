/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second subderivatives of indicators of constraint sets

Exercise 13.17.  For `C = {x ∈ X | F(x) ∈ D}` with `X`, `D` polyhedral and `F` of class `C²`,
`δ_C = δ_{D₀} ∘ F₀` with `F₀(x) = (x, F(x))` and `D₀ = X × D` (in the Euclidean product), as in
the guide.  The convex piecewise linear-quadratic case of Theorem 13.14 applies to this composition
under the qualification `y ∈ N_D(F(x̄)), -∇F(x̄)* y ∈ N_X(x̄) ⇒ y = 0` (the qualification of 13.14
for `F₀`, which is the one stated in 13.25; for `X = ℝⁿ` it is the printed one,
`indicators_and_geometry_univ`).  Here
`d²δ_{D₀}(F₀(x̄) | (a, y)) = δ` of `{u ∈ T_{D₀}(F₀(x̄)) | u ⊥ (a, y)}`, and the terms
`⟪(a, y), ∇²F₀(x̄)(w, w)⟫ = ⟪y, ∇²F(x̄)(w, w)⟫` give
`d²δ_C(x̄ | v)(w) = δ_{K(x̄,v)}(w) + max_{y ∈ Y(x̄,v)} ⟪w, ∇²(yF)(x̄)w⟫`.
-/

import RockafellarWets.Chapter13.SecondOrderChainRuleAmenable
import RockafellarWets.Chapter6.ProductCones
import RockafellarWets.Chapter6.ConvexSets

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The lifted mapping `F₀(x) = (x, F(x))` of the guide to Exercise 13.17. -/
noncomputable def graphLift (F : E → P) (z : E) : WithLp 2 (E × P) := WithLp.toLp 2 (z, F z)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem contDiff_graphLift {F : E → P} (hF : ContDiff ℝ 2 F) : ContDiff ℝ 2 (graphLift F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.contDiff.comp (contDiff_id.prodMk hF)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem fderiv_graphLift_apply {F : E → P} (hF : ContDiff ℝ 2 F) (x w : E) :
    fderiv ℝ (graphLift F) x w = WithLp.toLp 2 (w, fderiv ℝ F x w) := by
  have hd : HasFDerivAt F (fderiv ℝ F x) x := (hF.differentiable (by norm_num) x).hasFDerivAt
  have h : HasFDerivAt (graphLift F)
      ((WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ F x))) x :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.toContinuousLinearMap.hasFDerivAt.comp
      x ((hasFDerivAt_id x).prodMk hd)
  rw [h.fderiv]
  rfl

theorem adjoint_fderiv_graphLift {F : E → P} (hF : ContDiff ℝ 2 F) (x : E)
    (q : WithLp 2 (E × P)) :
    (fderiv ℝ (graphLift F) x).adjoint q = q.fst + (fderiv ℝ F x).adjoint q.snd := by
  refine ext_inner_right ℝ fun w ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, fderiv_graphLift_apply hF, WithLp.prod_inner_apply,
    inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- `∇²F₀(x̄)(w, w) = (0, ∇²F(x̄)(w, w))`, by uniqueness of the quotient limits. -/
theorem fderiv_fderiv_graphLift_apply {F : E → P} (hF : ContDiff ℝ 2 F) (x w : E) :
    fderiv ℝ (fderiv ℝ (graphLift F)) x w w = WithLp.toLp 2 (0, fderiv ℝ (fderiv ℝ F) x w w) := by
  have hray : Tendsto (fun τ : ℝ ↦ (τ, (0 : E))) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0) :=
    tendsto_id.prodMk tendsto_const_nhds
  have h1 := (tendsto_mapSecondDifferenceQuotient (contDiff_graphLift hF) x w 0).comp hray
  rw [map_zero, zero_add] at h1
  have h2 := (tendsto_mapSecondDifferenceQuotient hF x w 0).comp hray
  rw [map_zero, zero_add] at h2
  have h3 : Tendsto (fun τ : ℝ ↦ WithLp.toLp 2 ((0 : E), mapSecondDifferenceQuotient F x w τ 0))
      (𝓝[>] (0 : ℝ)) (𝓝 (WithLp.toLp 2 ((0 : E), fderiv ℝ (fderiv ℝ F) x w w))) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.continuous.tendsto _).comp
      (tendsto_const_nhds.prodMk_nhds h2)
  refine tendsto_nhds_unique h1 (h3.congr' (Eventually.of_forall fun τ ↦ ?_))
  simp only [Function.comp_apply, mapSecondDifferenceQuotient, smul_zero, add_zero]
  rw [fderiv_graphLift_apply hF]
  apply WithLp.ofLp_injective
  ext
  · simp [graphLift]
  · simp [graphLift]

theorem isPolyhedral_l2ProdSet {X : Set E} {D : Set P} (hX : IsPolyhedral X)
    (hD : IsPolyhedral D) : IsPolyhedral (l2ProdSet X D) := by
  have h1 := (hX.isHPolyhedral.continuousLinear_preimage (WithLp.fstL 2 ℝ E P)).isPolyhedral
  have h2 := (hD.isHPolyhedral.continuousLinear_preimage (WithLp.sndL 2 ℝ E P)).isPolyhedral
  exact h1.inter h2

omit [FiniteDimensional ℝ E] in
/-- The indicator of a polyhedral set is convex and piecewise linear-quadratic. -/
theorem isPiecewiseLinearQuadratic_indicatorVA {S : Set E} (hS : IsPolyhedral S) :
    IsPiecewiseLinearQuadratic (indicatorVA S) := by
  refine ⟨1, fun _ ↦ S, fun _ ↦ ⟨0, by simp, 0, 0⟩, fun _ ↦ hS, ?_, fun _ y hy ↦ ?_⟩
  · rw [effectiveDomain_indicatorVA]
    exact (iUnion_const S).symm
  · rw [indicatorVA_apply_mem hy]
    simp [QuadraticPiece.eval]

omit [FiniteDimensional ℝ E] in
theorem convex_epigraph_indicatorVA {S : Set E} (hS : Convex ℝ S) :
    Convex ℝ (epigraph (indicatorVA S)) := by
  rw [epigraph_indicatorVA]
  exact hS.prod (convex_Ici 0)

/-- `d²δ_S(x̄) = δ_{T_S(x̄)}` for a polyhedral set `S ∋ x̄`. -/
theorem secondSubderivativeAt_indicatorVA_of_isPolyhedral {S : Set E} (hS : IsPolyhedral S)
    {x : E} (hx : x ∈ S) (u : E) :
    secondSubderivativeAt (indicatorVA S) x u = indicatorVA (tangentCone S x) u := by
  have hplq := isPiecewiseLinearQuadratic_indicatorVA hS
  have hconv := convex_epigraph_indicatorVA hS.convex
  have hxd : x ∈ effectiveDomain (indicatorVA S) := by rw [effectiveDomain_indicatorVA]; exact hx
  have hlim := ((piecewise_linear_quadratic_second_order hplq hconv hxd).1.2.2 u).2
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  filter_upwards [hS.eventually_ray_mem_iff hx u, self_mem_nhdsWithin] with τ hτ hτpos
  have hτ' : (0 : ℝ) < τ := hτpos
  rw [secondDifferenceQuotientAt, subderivative_indicatorVA hx, indicatorVA_apply_mem hx]
  by_cases hu : u ∈ tangentCone S x
  · rw [indicatorVA_apply_mem hu, indicatorVA_apply_mem (hτ.2 hu)]
    simp [infAddition]
  · rw [indicatorVA_apply_not_mem hu, indicatorVA_apply_not_mem (fun h ↦ hu (hτ.1 h)),
      sub_zero, infAddition, if_pos (Or.inl rfl)]
    exact (EReal.coe_mul_top_of_pos (by positivity)).symm

/-- `{w ∈ T_X(x̄) ∣ Lw ∈ T_D(ū), w ⊥ v}` is polyhedral for polyhedral `X ∋ x̄` and `D ∋ ū`. -/
theorem isPolyhedral_setOf_tangentCone_inner_eq_zero {X : Set E} {D : Set P}
    (hX : IsPolyhedral X) (hD : IsPolyhedral D) {x : E} (hx : x ∈ X) {u : P} (hu : u ∈ D)
    (L : E →L[ℝ] P) (v : E) :
    IsPolyhedral {w | w ∈ tangentCone X x ∧ L w ∈ tangentCone D u ∧ ⟪w, v⟫_ℝ = 0} := by
  have h1 : IsPolyhedral (tangentCone X x) := hX.isPolyhedral_tangentCone hx
  have h2 : IsPolyhedral (L ⁻¹' tangentCone D u) :=
    ((hD.isPolyhedral_tangentCone hu).isHPolyhedral.continuousLinear_preimage L).isPolyhedral
  have h3 : IsPolyhedral {w : E | ⟪w, v⟫_ℝ = 0} := by
    have ha := isPolyhedral_linearHalfspace (innerSL ℝ v) 0
    have hb := isPolyhedral_linearHalfspace (innerSL ℝ (-v)) 0
    have : {w : E | ⟪w, v⟫_ℝ = 0} = {x | innerSL ℝ v x ≤ 0} ∩ {x | innerSL ℝ (-v) x ≤ 0} := by
      ext w
      simp only [mem_setOf_eq, mem_inter_iff, innerSL_apply_apply, inner_neg_left,
        real_inner_comm w v]
      constructor
      · intro h; rw [h]; simp
      · rintro ⟨h1, h2⟩; linarith
    rw [this]; exact ha.inter hb
  have : {w | w ∈ tangentCone X x ∧ L w ∈ tangentCone D u ∧ ⟪w, v⟫_ℝ = 0} =
      tangentCone X x ∩ (L ⁻¹' tangentCone D u) ∩ {w : E | ⟪w, v⟫_ℝ = 0} := by
    ext w; simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, and_assoc]
  rw [this]
  exact (h1.inter h2).inter h3

/-- `{w ∈ T_X(x̄) ∣ Lw ∈ T_D(ū), w ⊥ v}` is a cone. -/
theorem isCone_setOf_tangentCone_inner_eq_zero {X : Set E} {D : Set P} {x : E} (hx : x ∈ X)
    {u : P} (hu : u ∈ D) (L : E →L[ℝ] P) (v : E) :
    IsCone {w | w ∈ tangentCone X x ∧ L w ∈ tangentCone D u ∧ ⟪w, v⟫_ℝ = 0} := by
  refine ⟨⟨(isCone_tangentCone hx).1, by rw [map_zero]; exact (isCone_tangentCone hu).1,
    inner_zero_left _⟩, ?_⟩
  rintro w ⟨h1, h2, h3⟩ c hc
  refine ⟨(isCone_tangentCone hx).2 h1 hc, ?_, ?_⟩
  · rw [map_smul]; exact (isCone_tangentCone hu).2 h2 hc
  · rw [real_inner_smul_left, h3, mul_zero]

/-- **Exercise 13.17** (indicators and geometry), under the qualification
`y ∈ N_D(F(x̄)), -∇F(x̄)* y ∈ N_X(x̄) ⇒ y = 0`: for `C = {x ∈ X | F(x) ∈ D}` with `X`, `D`
polyhedral and `F` of class `C²`, `v ∈ N_C(x̄)` exactly when `v - ∇(yF)(x̄) ∈ N_X(x̄)` for some
`y ∈ N_D(F(x̄))`; for such `v`, `δ_C` is properly twice epi-differentiable at `x̄` for `v` with
`d²δ_C(x̄ | v)(w) = δ_{K(x̄,v)}(w) + max_{y ∈ Y(x̄,v)} ⟪w, ∇²(yF)(x̄)w⟫` (the maximum attained), for
`K(x̄, v) = {w ∈ T_X(x̄) | ∇F(x̄)w ∈ T_D(F(x̄)), w ⊥ v}`, the normal cone to `N_C(x̄)` at `v`, which
is polyhedral; the multiplier set `Y(x̄, v)` is compact. -/
theorem indicators_and_geometry {X : Set E} {D : Set P} (hX : IsPolyhedral X)
    (hD : IsPolyhedral D) {F : E → P} (hF : ContDiff ℝ 2 F) {x : E} (hxX : x ∈ X)
    (hFx : F x ∈ D)
    (hQ : ∀ y ∈ normalCone D (F x), -((fderiv ℝ F x).adjoint y) ∈ normalCone X x → y = 0) :
    (∀ v, v ∈ normalCone {z | z ∈ X ∧ F z ∈ D} x ↔
      ∃ y ∈ normalCone D (F x), v - (fderiv ℝ F x).adjoint y ∈ normalCone X x) ∧
    ∀ v ∈ normalCone {z | z ∈ X ∧ F z ∈ D} x,
      ProperlyTwiceEpiDifferentiableAt (indicatorVA {z | z ∈ X ∧ F z ∈ D}) x v ∧
      (∀ w, secondSubderivative (indicatorVA {z | z ∈ X ∧ F z ∈ D}) x v w =
        indicatorVA {w | w ∈ tangentCone X x ∧ fderiv ℝ F x w ∈ tangentCone D (F x) ∧
          ⟪w, v⟫_ℝ = 0} w +
        ⨆ y ∈ {y | y ∈ normalCone D (F x) ∧ v - (fderiv ℝ F x).adjoint y ∈ normalCone X x},
          ((⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal)) ∧
      (∀ w, ∃ y₀ ∈ {y | y ∈ normalCone D (F x) ∧ v - (fderiv ℝ F x).adjoint y ∈ normalCone X x},
        ∀ y ∈ {y | y ∈ normalCone D (F x) ∧ v - (fderiv ℝ F x).adjoint y ∈ normalCone X x},
          ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ ≤ ⟪y₀, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ) ∧
      {w | w ∈ tangentCone X x ∧ fderiv ℝ F x w ∈ tangentCone D (F x) ∧ ⟪w, v⟫_ℝ = 0} =
        normalCone (normalCone {z | z ∈ X ∧ F z ∈ D} x) v ∧
      IsPolyhedral {w | w ∈ tangentCone X x ∧ fderiv ℝ F x w ∈ tangentCone D (F x) ∧
        ⟪w, v⟫_ℝ = 0} ∧
      IsCompact {y | y ∈ normalCone D (F x) ∧ v - (fderiv ℝ F x).adjoint y ∈ normalCone X x} := by
  set C := {z | z ∈ X ∧ F z ∈ D} with hC
  have hD₀poly := isPolyhedral_l2ProdSet hX hD
  have hgplq := isPiecewiseLinearQuadratic_indicatorVA hD₀poly
  have hgc := convex_epigraph_indicatorVA hD₀poly.convex
  have hF₀C2 := contDiff_graphLift hF
  have hx₀ : graphLift F x ∈ l2ProdSet X D := ⟨hxX, hFx⟩
  have hx₀d : graphLift F x ∈ effectiveDomain (indicatorVA (l2ProdSet X D)) := by
    rw [effectiveDomain_indicatorVA]; exact hx₀
  have hcomp : indicatorVA (l2ProdSet X D) ∘ graphLift F = indicatorVA C := by
    funext z
    simp only [Function.comp_apply, indicatorVA, hC, mem_setOf_eq]
    rfl
  have hNprod : normalCone (l2ProdSet X D) (graphLift F x) =
      l2ProdSet (normalCone X x) (normalCone D (F x)) := normalCone_l2ProdSet X D x (F x)
  have hQ₀ : ∀ q ∈ horizonSubdifferential (indicatorVA (l2ProdSet X D)) (graphLift F x),
      (fderiv ℝ (graphLift F) x).adjoint q = 0 → q = 0 := by
    intro q hq h0
    rw [horizonSubdifferential_indicatorVA, hNprod] at hq
    rw [adjoint_fderiv_graphLift hF] at h0
    have h1 : q.fst = -((fderiv ℝ F x).adjoint q.snd) := eq_neg_of_add_eq_zero_left h0
    have hy := hQ q.snd hq.2 (by rw [← h1]; exact hq.1)
    rw [hy, map_zero, neg_zero] at h1
    apply WithLp.ofLp_injective
    exact Prod.ext h1 hy
  have hD₀cl : IsClosed (l2ProdSet X D) := hD₀poly.isClosed
  have hl : LowerSemicontinuous (indicatorVA (l2ProdSet X D)) := lowerSemicontinuous_indicatorVA hD₀cl
  have hlsc : IsLocallyLscAt (indicatorVA (l2ProdSet X D)) (graphLift F x) :=
    (isLocallyLscAt_indicatorVA_iff hx₀).2 (RW.IsClosed.isLocallyClosedAt hD₀cl _)
  have hr := (isSubdifferentiallyRegularAt_of_convex hgc hlsc).1
  have hF₀C1 : ContDiff ℝ 1 (graphLift F) := hF₀C2.of_le (by norm_num)
  have hsubC : normalCone C x =
      (fderiv ℝ (graphLift F) x).adjoint '' l2ProdSet (normalCone X x) (normalCone D (F x)) := by
    rw [← subdifferential_indicatorVA, ← hcomp, subdifferential_comp_eq_of_regular hF₀C1 hl hr hQ₀,
      subdifferential_indicatorVA, hNprod]
  have hchar : ∀ v, v ∈ normalCone C x ↔
      ∃ y ∈ normalCone D (F x), v - (fderiv ℝ F x).adjoint y ∈ normalCone X x := by
    intro v
    rw [hsubC]
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.snd, hq.2, ?_⟩
      rw [adjoint_fderiv_graphLift hF, add_sub_cancel_right]
      exact hq.1
    · rintro ⟨y, hy, hxy⟩
      refine ⟨WithLp.toLp 2 (v - (fderiv ℝ F x).adjoint y, y), ⟨hxy, hy⟩, ?_⟩
      rw [adjoint_fderiv_graphLift hF]
      simp
  -- the set `K(x̄, v)` and the multiplier sets
  have hrC : IsSubdifferentiallyRegularAt (indicatorVA C) x := by
    rw [← hcomp]; exact hr.comp_of_horizon_qualification hF₀C1 hl hQ₀
  refine ⟨hchar, fun v hv ↦ ?_⟩
  have hv' : v ∈ subdifferential (indicatorVA (l2ProdSet X D) ∘ graphLift F) x := by
    rw [hcomp, subdifferential_indicatorVA]; exact hv
  obtain ⟨hsup, -, -, -, hpte, hdom⟩ :=
    chain_rule_second_subderivatives_plq hF₀C2 hgplq hgc hx₀d hQ₀ hv'
  obtain ⟨hYne, -, hYcpt⟩ := multiplierSet_properties hF₀C2 hl hr hQ₀ hv'
  obtain ⟨M⟩ := hgplq.nonempty_localModel (graphLift F x)
  set K := {w | w ∈ tangentCone X x ∧ fderiv ℝ F x w ∈ tangentCone D (F x) ∧ ⟪w, v⟫_ℝ = 0}
    with hK
  set Y := {y | y ∈ normalCone D (F x) ∧ v - (fderiv ℝ F x).adjoint y ∈ normalCone X x} with hY
  have hTprod : tangentCone (l2ProdSet X D) (graphLift F x) =
      l2ProdSet (tangentCone X x) (tangentCone D (F x)) :=
    tangentCone_l2ProdSet X D hxX hFx (isGeometricallyDerivable_of_convex hX.convex hxX)
      (isGeometricallyDerivable_of_convex hD.convex hFx)
  have hp : IsProper (indicatorVA (l2ProdSet X D)) := (indicatorVA_isProper_iff _).2 ⟨_, hx₀⟩
  have hfin : indicatorVA (l2ProdSet X D) (graphLift F x) = ((0 : ℝ) : EReal) := by
    rw [indicatorVA_apply_mem hx₀, EReal.coe_zero]
  have hterm : ∀ q ∈ multiplierSet (graphLift F) (indicatorVA (l2ProdSet X D)) x v, ∀ w,
      secondSubderivative (indicatorVA (l2ProdSet X D)) (graphLift F x) q
        (fderiv ℝ (graphLift F) x w) = indicatorVA K w := by
    intro q hq w
    have hqv := inner_le_subderivative_of_convex hp hgc hfin hq.1
    rw [M.secondSubderivative_eq hgplq hx₀d hqv, ← M.secondSubderivativeAt_eq hgplq hx₀d,
      secondSubderivativeAt_indicatorVA_of_isPolyhedral hD₀poly hx₀,
      subderivative_indicatorVA hx₀, hTprod, ← ContinuousLinearMap.adjoint_inner_left, hq.2,
      fderiv_graphLift_apply hF]
    by_cases hw : w ∈ K
    · obtain ⟨h1, h2, h3⟩ := hw
      have hmem : WithLp.toLp 2 (w, fderiv ℝ F x w) ∈
          l2ProdSet (tangentCone X x) (tangentCone D (F x)) := ⟨h1, h2⟩
      rw [indicatorVA_apply_mem hmem, real_inner_comm, h3, EReal.coe_zero, if_pos rfl,
        indicatorVA_apply_mem (show w ∈ K from ⟨h1, h2, h3⟩)]
    · rw [indicatorVA_apply_not_mem hw]
      by_cases hmem : WithLp.toLp 2 (w, fderiv ℝ F x w) ∈
          l2ProdSet (tangentCone X x) (tangentCone D (F x))
      · rw [indicatorVA_apply_mem hmem, if_neg]
        intro h
        apply hw
        refine ⟨hmem.1, hmem.2, ?_⟩
        rw [real_inner_comm]
        exact_mod_cast h.symm
      · rw [indicatorVA_apply_not_mem hmem, if_neg (EReal.coe_ne_top _).symm]
  have hinner2 : ∀ q : WithLp 2 (E × P), ∀ w,
      ⟪q, fderiv ℝ (fderiv ℝ (graphLift F)) x w w⟫_ℝ = ⟪q.snd, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ := by
    intro q w
    rw [fderiv_fderiv_graphLift_apply hF, WithLp.prod_inner_apply]
    simp
  -- the multiplier set projects onto `Y`
  have hmsY : ∀ q ∈ multiplierSet (graphLift F) (indicatorVA (l2ProdSet X D)) x v, q.snd ∈ Y := by
    intro q hq
    have h1 := hq.1
    rw [subdifferential_indicatorVA, hNprod] at h1
    have h2 := hq.2
    rw [adjoint_fderiv_graphLift hF] at h2
    refine ⟨h1.2, ?_⟩
    rw [← h2, add_sub_cancel_right]
    exact h1.1
  have hYms : ∀ y ∈ Y, WithLp.toLp 2 (v - (fderiv ℝ F x).adjoint y, y) ∈
      multiplierSet (graphLift F) (indicatorVA (l2ProdSet X D)) x v := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [subdifferential_indicatorVA, hNprod]; exact ⟨hy.2, hy.1⟩
    · rw [adjoint_fderiv_graphLift hF]; simp
  have hYimage : Y = (WithLp.sndL 2 ℝ E P) ''
      multiplierSet (graphLift F) (indicatorVA (l2ProdSet X D)) x v := by
    ext y
    constructor
    · intro hy; exact ⟨_, hYms y hy, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact hmsY q hq
  have hYne' : Y.Nonempty := by rw [hYimage]; exact hYne.image _
  have hYcpt' : IsCompact Y := by rw [hYimage]; exact hYcpt.image (WithLp.sndL 2 ℝ E P).continuous
  have hformula : ∀ w, secondSubderivative (indicatorVA C) x v w =
      indicatorVA K w + ⨆ y ∈ Y, ((⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal) := by
    intro w
    rw [← hcomp, hsup w]
    simp only [hinner2]
    obtain ⟨y₀, hy₀⟩ := hYne'
    apply le_antisymm
    · refine iSup₂_le fun q hq ↦ ?_
      rw [hterm q hq w]
      exact add_le_add le_rfl (le_iSup₂ (f := fun y _ ↦
        ((⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal)) q.snd (hmsY q hq))
    · by_cases hw : w ∈ K
      · rw [indicatorVA_apply_mem hw, zero_add]
        refine iSup₂_le fun y hy ↦ le_trans (le_of_eq ?_) (le_iSup₂ (f := fun q _ ↦
          secondSubderivative (indicatorVA (l2ProdSet X D)) (graphLift F x) q
            (fderiv ℝ (graphLift F) x w) +
          ((⟪q.snd, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal)) _ (hYms y hy))
        rw [hterm _ (hYms y hy) w, indicatorVA_apply_mem hw, zero_add]
        rfl
      · rw [indicatorVA_apply_not_mem hw, EReal.top_add_of_ne_bot (ne_bot_of_le_ne_bot
          (EReal.coe_ne_bot _) (le_iSup₂ (f := fun y _ ↦
            ((⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal)) y₀ hy₀))]
        refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun q _ ↦
          secondSubderivative (indicatorVA (l2ProdSet X D)) (graphLift F x) q
            (fderiv ℝ (graphLift F) x w) +
          ((⟪q.snd, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal)) _ (hYms y₀ hy₀))
        rw [hterm _ (hYms y₀ hy₀) w, indicatorVA_apply_not_mem hw, EReal.top_add_coe]
  have hmax : ∀ w, ∃ y₀ ∈ Y, ∀ y ∈ Y,
      ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ ≤ ⟪y₀, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ := by
    intro w
    obtain ⟨y₀, hy₀, hmax⟩ := hYcpt'.exists_isMaxOn hYne'
      (show ContinuousOn (fun y : P ↦ ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ) Y from
        (continuous_id.inner continuous_const).continuousOn)
    exact ⟨y₀, hy₀, fun y hy ↦ hmax hy⟩
  have hdomK : effectiveDomain (secondSubderivative (indicatorVA C) x v) = K := by
    ext w
    rw [mem_effectiveDomain_iff, hformula w]
    obtain ⟨y₀, hy₀, hm⟩ := hmax w
    have hsupv : (⨆ y ∈ Y, ((⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal)) =
        ((⟪y₀, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal) :=
      le_antisymm (iSup₂_le fun y hy ↦ EReal.coe_le_coe_iff.2 (hm y hy))
        (le_iSup₂ (f := fun y _ ↦ ((⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal)) y₀ hy₀)
    rw [hsupv]
    by_cases hw : w ∈ K
    · rw [indicatorVA_apply_mem hw, zero_add]
      exact ⟨fun _ ↦ hw, fun _ ↦ EReal.coe_lt_top _⟩
    · rw [indicatorVA_apply_not_mem hw, EReal.top_add_coe]
      exact ⟨fun h ↦ absurd h (lt_irrefl _), fun h ↦ absurd h hw⟩
  have hKnormal : K = normalCone (normalCone C x) v := by
    rw [← hdomK, ← hcomp, hdom, hcomp, setOf_subderivative_eq_inner_eq_normalCone hrC
      (by rw [subdifferential_indicatorVA]; exact hv), subdifferential_indicatorVA]
  have hKpoly : IsPolyhedral K :=
    isPolyhedral_setOf_tangentCone_inner_eq_zero hX hD hxX hFx (fderiv ℝ F x) v
  have hpte' : ProperlyTwiceEpiDifferentiableAt (indicatorVA C) x v := by
    rw [← hcomp]; exact hpte
  exact ⟨hpte', hformula, hmax, hKnormal, hKpoly, hYcpt'⟩

/-- **Exercise 13.17 for `X = ℝⁿ`**, under the qualification exactly as printed,
`y ∈ N_D(F(x̄)), ∇F(x̄)* y = 0 ⇒ y = 0`.  Since `N_X(x̄) = {0}` for `X` the whole space, it is the
qualification of `indicators_and_geometry` (first conjunct), so all conclusions of that theorem
hold for `C = {x ∣ F(x) ∈ D}`; the normal cone formula reads `v ∈ N_C(x̄)` exactly when
`v = ∇F(x̄)* y` for some `y ∈ N_D(F(x̄))`. -/
theorem indicators_and_geometry_univ {D : Set P} (hD : IsPolyhedral D) {F : E → P}
    (hF : ContDiff ℝ 2 F) {x : E} (hFx : F x ∈ D)
    (hQ : ∀ y ∈ normalCone D (F x), (fderiv ℝ F x).adjoint y = 0 → y = 0) :
    (∀ y ∈ normalCone D (F x), -((fderiv ℝ F x).adjoint y) ∈ normalCone (univ : Set E) x →
      y = 0) ∧
    ∀ v, v ∈ normalCone {z | z ∈ (univ : Set E) ∧ F z ∈ D} x ↔
      ∃ y ∈ normalCone D (F x), v = (fderiv ℝ F x).adjoint y := by
  have hQ' : ∀ y ∈ normalCone D (F x), -((fderiv ℝ F x).adjoint y) ∈ normalCone (univ : Set E) x →
      y = 0 := fun y hy hN ↦ by
    rw [normalCone_univ, mem_singleton_iff, neg_eq_zero] at hN
    exact hQ y hy hN
  refine ⟨hQ', fun v ↦ ?_⟩
  rw [(indicators_and_geometry (X := (univ : Set E)) IsPolyhedral.univ hD hF (mem_univ x) hFx
    hQ').1 v]
  simp only [normalCone_univ, mem_singleton_iff, sub_eq_zero]

end RW
