/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: The chain rule for parabolic subderivatives

Exercise 13.63.  For `f = g ∘ G` with `G` of class `C²`, `g` lsc and finite at `ū = G(x̄)`, under
the horizon qualification, the epigraph `epi f` is the inverse image of `epi g` under
`H(x, α) = (G(x), α)`, and the qualification is the normal qualification for this inverse image
(as in 10.6).  Proposition 13.13 applied to `H` (in Euclidean coordinates of the products) gives
`df(x̄)(w) = dg(ū)(∇G(x̄)w)` and, through Example 13.62(b),
`d²f(x̄)(w | z) = d²g(ū)(∇G(x̄)w | ∇²G(x̄)(w, w) + ∇G(x̄)z)`, together with parabolic
epi-differentiability of `f` when `g` is regular and parabolically epi-differentiable.  Second-order
tangent sets and parabolic derivability are transported along continuous linear equivalences.
-/

import RockafellarWets.Chapter13.SecondOrderChainRule
import RockafellarWets.Chapter13.SecondOrderDuality
import RockafellarWets.Chapter10.EpigraphChainMaps

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

/-! ### Transport along continuous linear equivalences -/

section Transport

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

theorem parabolicBlowUp_image_continuousLinearEquiv (L : X ≃L[ℝ] Y) (C : Set X) (x w : X)
    (τ : ℝ) : parabolicBlowUp (L '' C) (L x) (L w) τ = L '' parabolicBlowUp C x w τ := by
  simp only [parabolicBlowUp, image_image]
  congr 1
  funext y
  simp [map_sub, map_smul]

theorem secondOrderTangentSet_image_continuousLinearEquiv (L : X ≃L[ℝ] Y) (C : Set X)
    (x w : X) :
    secondOrderTangentSet (L '' C) (L x) (L w) = L '' secondOrderTangentSet C x w := by
  have h := outerSetLimitAlong_image_homeomorph L.toHomeomorph (𝓝[>] (0 : ℝ))
    (parabolicBlowUp C x w)
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
  simp only [secondOrderTangentSet]
  rw [← h]
  congr 1
  funext τ
  exact parabolicBlowUp_image_continuousLinearEquiv L C x w τ

theorem isParabolicallyDerivable_image_continuousLinearEquiv_iff (L : X ≃L[ℝ] Y) (C : Set X)
    (x w : X) :
    IsParabolicallyDerivable (L '' C) (L x) (L w) ↔ IsParabolicallyDerivable C x w := by
  unfold IsParabolicallyDerivable
  rw [secondOrderTangentSet_image_continuousLinearEquiv, image_nonempty]
  refine and_congr_right fun _ ↦ ?_
  have h := pkConvergesAlong_image_homeomorph_iff L.toHomeomorph (𝓝[>] (0 : ℝ))
    (parabolicBlowUp C x w) (secondOrderTangentSet C x w)
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [← h]
  have h' : (fun τ ↦ parabolicBlowUp (L '' C) (L x) (L w) τ) =
      fun τ ↦ L '' parabolicBlowUp C x w τ := by
    funext τ
    exact parabolicBlowUp_image_continuousLinearEquiv L C x w τ
  exact Iff.of_eq (congrArg (fun S ↦ PKConvergesAlong (𝓝[>] (0 : ℝ)) S
    (L '' secondOrderTangentSet C x w)) h')

theorem tangentCone_image_continuousLinearEquiv (L : X ≃L[ℝ] Y) (C : Set X) (x : X) :
    tangentCone (L '' C) (L x) = L '' tangentCone C x := by
  have h := outerSetLimitAlong_image_homeomorph L.toHomeomorph (𝓝[>] (0 : ℝ)) (blowUp C x)
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [tangentCone_eq_outerSetLimitAlong, tangentCone_eq_outerSetLimitAlong, ← h]
  congr 1
  funext τ
  simp only [blowUp, image_image]
  congr 1
  funext y
  simp [map_sub, map_smul]

end Transport

/-! ### Exercise 13.63 -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- The Euclidean epigraph is the image of the epigraph under the Euclidean coordinates. -/
theorem euclideanEpigraph_eq_image (f : E → EReal) :
    euclideanEpigraph f = (l2ProdEquiv E).symm '' epigraph f := by
  ext p
  constructor
  · intro hp
    exact ⟨WithLp.ofLp p, hp, by simp⟩
  · rintro ⟨q, hq, rfl⟩
    exact hq

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem contDiff_two_epigraphChainMap {G : E → F} (h : ContDiff ℝ 2 G) :
    ContDiff ℝ 2 (epigraphChainMap G) :=
  (l2ProdEquiv F).symm.contDiff.comp
    ((h.comp (WithLp.fstL 2 ℝ E ℝ).contDiff).prodMk (WithLp.sndL 2 ℝ E ℝ).contDiff)

omit [FiniteDimensional ℝ E] in
theorem mem_secondOrderTangentSet_euclideanEpigraph_iff (f : E → EReal) (x w z : E)
    (c β γ : ℝ) :
    WithLp.toLp 2 (z, γ) ∈ secondOrderTangentSet (euclideanEpigraph f) (WithLp.toLp 2 (x, c))
        (WithLp.toLp 2 (w, β)) ↔
      (z, γ) ∈ secondOrderTangentSet (epigraph f) (x, c) (w, β) := by
  have h := secondOrderTangentSet_image_continuousLinearEquiv (l2ProdEquiv E).symm
    (epigraph f) (x, c) (w, β)
  rw [← euclideanEpigraph_eq_image, ContinuousLinearEquiv.image_symm_eq_preimage] at h
  change WithLp.toLp 2 (z, γ) ∈ secondOrderTangentSet (euclideanEpigraph f)
    ((l2ProdEquiv E).symm (x, c)) ((l2ProdEquiv E).symm (w, β)) ↔ _
  rw [h]
  rfl

omit [FiniteDimensional ℝ E] in
theorem isParabolicallyDerivable_euclideanEpigraph_iff (f : E → EReal) (x w : E) (c β : ℝ) :
    IsParabolicallyDerivable (euclideanEpigraph f) (WithLp.toLp 2 (x, c))
        (WithLp.toLp 2 (w, β)) ↔
      IsParabolicallyDerivable (epigraph f) (x, c) (w, β) := by
  have h := isParabolicallyDerivable_image_continuousLinearEquiv_iff (l2ProdEquiv E).symm
    (epigraph f) (x, c) (w, β)
  rw [← euclideanEpigraph_eq_image] at h
  exact h

/-- Two extended reals with the same real upper bounds are equal. -/
theorem ereal_eq_of_forall_coe_le_iff {a b : EReal} (h : ∀ β : ℝ, a ≤ β ↔ b ≤ β) : a = b := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt fun c hc ↦ ?_
    obtain ⟨β, hbβ, hβc⟩ := EReal.exists_between_coe_real hc
    exact lt_of_le_of_lt ((h β).2 hbβ.le) hβc
  · refine le_of_forall_gt fun c hc ↦ ?_
    obtain ⟨β, haβ, hβc⟩ := EReal.exists_between_coe_real hc
    exact lt_of_le_of_lt ((h β).1 haβ.le) hβc

/-- **Exercise 13.63** (chain rule for parabolic subderivatives).  Let `f = g ∘ G` with `G` of
class `C²`, `g` lsc and finite at `ū = G(x̄)`, under the qualification
`y ∈ ∂^∞g(ū), ∇G(x̄)* y = 0 ⇒ y = 0`.  Then `df(x̄)(w) = dg(ū)(∇G(x̄)w)` for every `w`, and for `w`
with this value finite, `d²f(x̄)(w | z) = d²g(ū)(∇G(x̄)w | ∇²G(x̄)(w, w) + ∇G(x̄)z)`; moreover `f`
is parabolically epi-differentiable at `x̄` for `w` when `g` is regular at `ū` and parabolically
epi-differentiable at `ū` for `∇G(x̄)w`. -/
theorem chain_rule_for_parabolic_subderivatives {G : E → F} (hG : ContDiff ℝ 2 G) {g : F → EReal}
    (hl : LowerSemicontinuous g) {x : E} {c : ℝ} (hc : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    (∀ w, subderivative (g ∘ G) x w = subderivative g (G x) (fderiv ℝ G x w)) ∧
    (∀ w, subderivative (g ∘ G) x w ≠ ⊥ → subderivative (g ∘ G) x w ≠ ⊤ → ∀ z,
      parabolicSubderivative (g ∘ G) x w z = parabolicSubderivative g (G x) (fderiv ℝ G x w)
        (fderiv ℝ (fderiv ℝ G) x w w + fderiv ℝ G x z)) ∧
    (∀ w, subderivative (g ∘ G) x w ≠ ⊥ → subderivative (g ∘ G) x w ≠ ⊤ →
      IsSubdifferentiallyRegularAt g (G x) →
      IsParabolicallyEpiDifferentiableAt g (G x) (fderiv ℝ G x w) →
      IsParabolicallyEpiDifferentiableAt (g ∘ G) x w) := by
  set H := epigraphChainMap G with hH
  set D := euclideanEpigraph g with hD
  set p := WithLp.toLp 2 (x, c) with hp
  have hHC2 : ContDiff ℝ 2 H := contDiff_two_epigraphChainMap hG
  have hDcl : IsClosed D :=
    (isClosed_epigraph_of_lsc_ereal g hl).preimage (l2ProdEquiv F).continuous
  have hpD : H p ∈ D := show (G x, c).2 ≥ g (G x, c).1 by simp [hc]
  have hQD : ∀ y ∈ normalCone D (H p), (fderiv ℝ H p).adjoint y = 0 → y = 0 := by
    intro y hy h0
    exact epigraphChain_constraintQualification (hG.of_le (by norm_num)) hl hc hQ y hy
      (by rw [normalCone_univ, mem_singleton_iff, h0, neg_zero])
  obtain ⟨hT1, hT2, hT3, -⟩ := chain_rule_for_second_order_tangents hHC2 hDcl hpD hQD
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hdH : fderiv ℝ H p = epigraphChainDerivative (fderiv ℝ G x) :=
    (hasFDerivAt_epigraphChainMap hd c).fderiv
  -- the second derivative of `H` from the quotient limits
  have hd2H : ∀ w β, fderiv ℝ (fderiv ℝ H) p (WithLp.toLp 2 (w, β)) (WithLp.toLp 2 (w, β)) =
      WithLp.toLp 2 (fderiv ℝ (fderiv ℝ G) x w w, 0) := by
    intro w β
    have hray : Tendsto (fun τ : ℝ ↦ (τ, (0 : WithLp 2 (E × ℝ)))) (𝓝[>] (0 : ℝ))
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0) := tendsto_id.prodMk tendsto_const_nhds
    have h1 := (tendsto_mapSecondDifferenceQuotient hHC2 p (WithLp.toLp 2 (w, β)) 0).comp hray
    rw [map_zero, zero_add] at h1
    have hray' : Tendsto (fun τ : ℝ ↦ (τ, (0 : E))) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0) :=
      tendsto_id.prodMk tendsto_const_nhds
    have h2 := (tendsto_mapSecondDifferenceQuotient hG x w 0).comp hray'
    rw [map_zero, zero_add] at h2
    have h3 : Tendsto (fun τ : ℝ ↦ WithLp.toLp 2
        (mapSecondDifferenceQuotient G x w τ 0, (0 : ℝ))) (𝓝[>] (0 : ℝ))
        (𝓝 (WithLp.toLp 2 (fderiv ℝ (fderiv ℝ G) x w w, (0 : ℝ)))) :=
      ((l2ProdEquiv F).symm.continuous.tendsto _).comp (h2.prodMk_nhds tendsto_const_nhds)
    refine tendsto_nhds_unique h1 (h3.congr' (Eventually.of_forall fun τ ↦ ?_))
    simp only [Function.comp_apply, mapSecondDifferenceQuotient]
    rw [hdH]
    simp only [smul_zero, add_zero, epigraphChainDerivative_apply, hH, hp, epigraphChainMap]
    apply WithLp.ofLp_injective
    ext <;> simp
  -- transport of the epigraphs
  have hEf : euclideanEpigraph (g ∘ G) = H ⁻¹' D := euclideanEpigraph_comp G g
  have hfx : (g ∘ G) x = c := hc
  -- first order
  have hfirst : ∀ w, subderivative (g ∘ G) x w = subderivative g (G x) (fderiv ℝ G x w) := by
    intro w
    refine ereal_eq_of_forall_coe_le_iff fun β ↦ ?_
    have e1 : subderivative (g ∘ G) x w ≤ β ↔ (w, β) ∈ tangentCone (epigraph (g ∘ G)) (x, c) := by
      rw [← epigraph_subderivative_eq_tangentCone hfx]; rfl
    have e2 : subderivative g (G x) (fderiv ℝ G x w) ≤ β ↔
        (fderiv ℝ G x w, β) ∈ tangentCone (epigraph g) (G x, c) := by
      rw [← epigraph_subderivative_eq_tangentCone hc]; rfl
    rw [e1, e2]
    have t1 := hT1 (WithLp.toLp 2 (w, β))
    have hHp : H p = (l2ProdEquiv F).symm (G x, c) := rfl
    have hpe : p = (l2ProdEquiv E).symm (x, c) := rfl
    rw [hHp, ← hEf, hdH, epigraphChainDerivative_apply, hD, euclideanEpigraph_eq_image,
      euclideanEpigraph_eq_image, hpe, tangentCone_image_continuousLinearEquiv,
      tangentCone_image_continuousLinearEquiv, ContinuousLinearEquiv.image_symm_eq_preimage,
      ContinuousLinearEquiv.image_symm_eq_preimage] at t1
    simpa using t1
  refine ⟨hfirst, fun w hw1 hw2 z ↦ ?_, fun w hw1 hw2 hr hpar ↦ ?_⟩
  · set β := (subderivative (g ∘ G) x w).toReal with hβ
    have hβeq : subderivative (g ∘ G) x w = β := (EReal.coe_toReal hw2 hw1).symm
    have hβg : subderivative g (G x) (fderiv ℝ G x w) = β := by rw [← hfirst]; exact hβeq
    refine ereal_eq_of_forall_coe_le_iff fun γ ↦ ?_
    have e1 : parabolicSubderivative (g ∘ G) x w z ≤ γ ↔
        (z, γ) ∈ secondOrderTangentSet (epigraph (g ∘ G)) (x, c) (w, β) := by
      rw [← epigraph_parabolicSubderivative_eq_secondOrderTangentSet hfx hβeq]; rfl
    have e2 : parabolicSubderivative g (G x) (fderiv ℝ G x w)
        (fderiv ℝ (fderiv ℝ G) x w w + fderiv ℝ G x z) ≤ γ ↔
        (fderiv ℝ (fderiv ℝ G) x w w + fderiv ℝ G x z, γ) ∈
          secondOrderTangentSet (epigraph g) (G x, c) (fderiv ℝ G x w, β) := by
      rw [← epigraph_parabolicSubderivative_eq_secondOrderTangentSet hc hβg]; rfl
    rw [e1, e2]
    have t2 := hT2 (WithLp.toLp 2 (w, β)) (WithLp.toLp 2 (z, γ))
    have hHp : H p = WithLp.toLp 2 (G x, c) := rfl
    have hdir : fderiv ℝ H p (WithLp.toLp 2 (w, β)) = WithLp.toLp 2 (fderiv ℝ G x w, β) := by
      rw [hdH]; rfl
    have hsum : fderiv ℝ H p (WithLp.toLp 2 (z, γ)) +
        fderiv ℝ (fderiv ℝ H) p (WithLp.toLp 2 (w, β)) (WithLp.toLp 2 (w, β)) =
        WithLp.toLp 2 (fderiv ℝ (fderiv ℝ G) x w w + fderiv ℝ G x z, γ) := by
      rw [hd2H, hdH]
      apply WithLp.ofLp_injective
      ext <;> simp [add_comm]
    rw [← hEf, hHp, hdir, hsum, hD, hp, mem_secondOrderTangentSet_euclideanEpigraph_iff,
      mem_secondOrderTangentSet_euclideanEpigraph_iff] at t2
    exact t2
  · set β := (subderivative (g ∘ G) x w).toReal with hβ
    have hβeq : subderivative (g ∘ G) x w = β := (EReal.coe_toReal hw2 hw1).symm
    have hβg : subderivative g (G x) (fderiv ℝ G x w) = β := by rw [← hfirst]; exact hβeq
    rw [isParabolicallyEpiDifferentiableAt_iff hfx hβeq]
    rw [isParabolicallyEpiDifferentiableAt_iff hc hβg] at hpar
    have hreg : IsClarkeRegularAt D (H p) := by
      have := hr.2.2
      rwa [show (g (G x)).toReal = c by rw [hc]; rfl] at this
    have hHp : H p = WithLp.toLp 2 (G x, c) := rfl
    have hdir : fderiv ℝ H p (WithLp.toLp 2 (w, β)) = WithLp.toLp 2 (fderiv ℝ G x w, β) := by
      rw [hdH]; rfl
    have hDpar : IsParabolicallyDerivable D (H p) (fderiv ℝ H p (WithLp.toLp 2 (w, β))) := by
      rw [hdir, hHp, hD, isParabolicallyDerivable_euclideanEpigraph_iff]
      exact hpar
    have h3 := hT3 (WithLp.toLp 2 (w, β)) hreg hDpar
    rw [← hEf, hp, isParabolicallyDerivable_euclideanEpigraph_iff] at h3
    exact h3

end RW
