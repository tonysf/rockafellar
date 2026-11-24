/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: The chain rule for second subderivatives, fully amenable case

Theorem 13.14 when `g` is fully amenable at `ū = G(x̄)`.  A model `g = g₀ ∘ G₀` near `ū` (with `g₀`
convex and piecewise linear-quadratic) is made global by a smooth cutoff (`G₀` replaced by a `C²`
mapping with the same germ), so that `f = g₀ ∘ (G₀ ∘ G)` near `x̄` with the qualification of
`AmenableFunctionModel.comp`.  The convex piecewise linear-quadratic case then applies both to
`g₀ ∘ (G₀ ∘ G)` at `x̄` and to `g₀ ∘ G₀` at `ū`, and the two suprema are merged through the
second-order chain identity `∇²(G₀ ∘ G)(x̄)(w, w) = ∇G₀(ū)∇²G(x̄)(w, w) + ∇²G₀(ū)(∇G(x̄)w, ∇G(x̄)w)`
and the subgradient formula `∂g(ū) = ∇G₀(ū)* ∂g₀(G₀(ū))`.
-/

import RockafellarWets.Chapter13.SecondOrderChainRule
import RockafellarWets.Chapter10.AmenabilityPersistence

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

/-- `(⨆ i ∈ S, a i) + c ≤ L` for real `c` as soon as every `a i + c ≤ L`. -/
theorem iSup₂_add_coe_le {ι : Type*} {S : Set ι} {a : ι → EReal} {c : ℝ} {L : EReal}
    (h : ∀ i ∈ S, a i + c ≤ L) : (⨆ i ∈ S, a i) + c ≤ L := by
  rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))]
  exact iSup₂_le fun i hi ↦
    (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))).2 (h i hi)

universe u

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Theorem 13.14** for fully amenable `g`: under the horizon qualification at `ū = G(x̄)`, for
every `v ∈ ∂f(x̄)`, `f = g ∘ G`,
`d²f(x̄ | v)(w) = sup_{y ∈ Y(x̄,v)} [d²g(ū | y)(∇G(x̄)w) + ⟪w, ∇²(yG)(x̄)w⟫]`, `f` is properly twice
epi-differentiable at `x̄` for `v`, and `dom d²f(x̄ | v) = {w | df(x̄)(w) = ⟪v, w⟫}`. -/
theorem chain_rule_second_subderivatives_fullyAmenable {G : E → F} (hG : ContDiff ℝ 2 G)
    {g : F → EReal} {x : E} (hg : FullyAmenableAt g (G x))
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0)
    {v : E} (hv : v ∈ subdifferential (g ∘ G) x) :
    (∀ w, secondSubderivative (g ∘ G) x v w = ⨆ y ∈ multiplierSet G g x v,
        (secondSubderivative g (G x) y (fderiv ℝ G x w) +
          ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal))) ∧
    ProperlyTwiceEpiDifferentiableAt (g ∘ G) x v ∧
    effectiveDomain (secondSubderivative (g ∘ G) x v) =
      {w | subderivative (g ∘ G) x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} := by
  obtain ⟨M⟩ := hg
  set u := G x with hu_def
  obtain ⟨G₀, hG₀, hG₀eq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn M.isOpen M.mem M.smooth
  have hg₀ : IsPiecewiseLinearQuadratic M.outer := M.plq rfl
  have hval : M.outer (G₀ u) = ((g u).toReal : EReal) := by
    rw [hG₀eq.self_of_nhds, ← M.eqOn u M.mem]
    exact (EReal.coe_toReal M.finite.2 M.finite.1).symm
  have hdom₀ : G₀ u ∈ effectiveDomain M.outer := by
    rw [mem_effectiveDomain_iff, hval]; exact EReal.coe_lt_top _
  -- local representations
  have hloc_g : g =ᶠ[𝓝 u] M.outer ∘ G₀ := by
    filter_upwards [M.isOpen.mem_nhds M.mem, hG₀eq] with y hy hy'
    rw [Function.comp_apply, hy', M.eqOn y hy]
  have hloc_f : g ∘ G =ᶠ[𝓝 x] M.outer ∘ (G₀ ∘ G) :=
    hG.continuous.continuousAt.tendsto.eventually hloc_g
  have hH : ContDiff ℝ 2 (G₀ ∘ G) := hG₀.comp hG
  -- derivatives of the globalized inner mappings
  have hdG₀ : fderiv ℝ G₀ u = fderiv ℝ M.inner u := hG₀eq.fderiv_eq
  have hGeq : G₀ ∘ G =ᶠ[𝓝 x] M.inner ∘ G := hG.continuous.continuousAt.tendsto.eventually hG₀eq
  have hdH : fderiv ℝ (G₀ ∘ G) x = (fderiv ℝ G₀ u).comp (fderiv ℝ G x) :=
    fderiv_comp x (hG₀.differentiable (by norm_num) _) (hG.differentiable (by norm_num) _)
  -- the qualifications
  have hnorm : horizonSubdifferential M.outer (G₀ u) =
      normalCone (closure (effectiveDomain M.outer)) (G₀ u) :=
    horizonSubdifferential_eq_normalCone_closure_domain M.proper M.lsc M.convex hval
  have hQ₀ : ∀ y₀ ∈ horizonSubdifferential M.outer (G₀ u), (fderiv ℝ G₀ u).adjoint y₀ = 0 →
      y₀ = 0 := by
    intro y₀ hy₀ h0
    rw [hnorm, hG₀eq.self_of_nhds] at hy₀
    rw [hdG₀] at h0
    exact M.qualification y₀ hy₀ h0
  have hQH : ∀ y₀ ∈ horizonSubdifferential M.outer ((G₀ ∘ G) x),
      (fderiv ℝ (G₀ ∘ G) x).adjoint y₀ = 0 → y₀ = 0 := by
    intro y₀ hy₀ h0
    rw [Function.comp_apply, hnorm, hG₀eq.self_of_nhds] at hy₀
    rw [hGeq.fderiv_eq] at h0
    exact (M.comp (by norm_num) hG hQ).qualification y₀ hy₀ h0
  -- subgradients
  have hvH : v ∈ subdifferential (M.outer ∘ (G₀ ∘ G)) x := by
    rwa [← subdifferential_eq_of_eventuallyEq hloc_f]
  have hsubg : subdifferential g u = (fderiv ℝ G₀ u).adjoint '' subdifferential M.outer (G₀ u) := by
    rw [(M.derivatives (by norm_num)).1, hdG₀, hG₀eq.self_of_nhds]
  -- the convex piecewise linear-quadratic case for `g₀ ∘ (G₀ ∘ G)`
  obtain ⟨hsupH, -, -, -, hpteH, hdomH⟩ :=
    chain_rule_second_subderivatives_plq hH hg₀ M.convex hdom₀ hQH hvH
  have hd2 : ∀ w, secondSubderivative (g ∘ G) x v w =
      secondSubderivative (M.outer ∘ (G₀ ∘ G)) x v w :=
    secondSubderivative_congr_nhds hloc_f v
  refine ⟨fun w ↦ ?_, ⟨hpteH.1.congr_nhds hloc_f, ?_⟩, ?_⟩
  · -- merging the two suprema
    rw [hd2, hsupH w]
    set z := fderiv ℝ G x w with hz
    have hHw : fderiv ℝ (G₀ ∘ G) x w = fderiv ℝ G₀ u z := by rw [hdH]; rfl
    have hH2 : fderiv ℝ (fderiv ℝ (G₀ ∘ G)) x w w = fderiv ℝ G₀ u (fderiv ℝ (fderiv ℝ G) x w w) +
        fderiv ℝ (fderiv ℝ G₀) u z z := fderiv_fderiv_comp_apply hG₀ hG x w
    have hHx : (G₀ ∘ G) x = G₀ u := rfl
    apply le_antisymm
    · refine iSup₂_le fun y₀ hy₀ ↦ ?_
      set y := (fderiv ℝ G₀ u).adjoint y₀ with hy
      have hyg : y ∈ subdifferential g u := by rw [hsubg]; exact ⟨y₀, hy₀.1, rfl⟩
      have hyY : y ∈ multiplierSet G g x v := by
        refine ⟨hyg, ?_⟩
        rw [← hy₀.2, hdH, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
      have hyg₀ : y ∈ subdifferential (M.outer ∘ G₀) u := by
        rwa [← subdifferential_eq_of_eventuallyEq hloc_g]
      obtain ⟨hsupG, -⟩ := chain_rule_second_subderivatives_plq hG₀ hg₀ M.convex hdom₀ hQ₀ hyg₀
      have hy₀Y : y₀ ∈ multiplierSet G₀ M.outer u y := ⟨hy₀.1, rfl⟩
      have hle : secondSubderivative M.outer (G₀ u) y₀ (fderiv ℝ G₀ u z) +
          ((⟪y₀, fderiv ℝ (fderiv ℝ G₀) u z z⟫_ℝ : ℝ) : EReal) ≤ secondSubderivative g u y z := by
        rw [secondSubderivative_congr_nhds hloc_g y z, hsupG z]
        exact le_iSup₂ (f := fun y₀ _ ↦ secondSubderivative M.outer (G₀ u) y₀ (fderiv ℝ G₀ u z) +
          ((⟪y₀, fderiv ℝ (fderiv ℝ G₀) u z z⟫_ℝ : ℝ) : EReal)) y₀ hy₀Y
      refine le_trans ?_ (le_iSup₂ (f := fun y _ ↦ secondSubderivative g u y z +
        ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal)) y hyY)
      have hadj : ⟪y₀, fderiv ℝ G₀ u (fderiv ℝ (fderiv ℝ G) x w w)⟫_ℝ =
          ⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ := by
        rw [hy, ContinuousLinearMap.adjoint_inner_left]
      rw [hHx, hHw, hH2, inner_add_right, hadj, EReal.coe_add,
        add_comm ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal), ← add_assoc]
      exact add_le_add hle le_rfl
    · refine iSup₂_le fun y hy ↦ ?_
      have hyg₀ : y ∈ subdifferential (M.outer ∘ G₀) u := by
        rw [← subdifferential_eq_of_eventuallyEq hloc_g]; exact hy.1
      obtain ⟨hsupG, -⟩ := chain_rule_second_subderivatives_plq hG₀ hg₀ M.convex hdom₀ hQ₀ hyg₀
      rw [secondSubderivative_congr_nhds hloc_g y z, hsupG z]
      refine iSup₂_add_coe_le fun y₀ hy₀ ↦ ?_
      have hy₀H : y₀ ∈ multiplierSet (G₀ ∘ G) M.outer x v := by
        refine ⟨hy₀.1, ?_⟩
        rw [hdH, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, hy₀.2, hy.2]
      refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun y₀ _ ↦
        secondSubderivative M.outer ((G₀ ∘ G) x) y₀ (fderiv ℝ (G₀ ∘ G) x w) +
          ((⟪y₀, fderiv ℝ (fderiv ℝ (G₀ ∘ G)) x w w⟫_ℝ : ℝ) : EReal)) y₀ hy₀H)
      have hadj : ⟪y₀, fderiv ℝ G₀ u (fderiv ℝ (fderiv ℝ G) x w w)⟫_ℝ =
          ⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ := by
        rw [← hy₀.2, ContinuousLinearMap.adjoint_inner_left]
      rw [hHx, hHw, hH2, inner_add_right, hadj, EReal.coe_add,
        add_comm ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal), ← add_assoc]
  · rw [funext (secondSubderivative_congr_nhds hloc_f v)]
    exact hpteH.2
  · rw [funext (secondSubderivative_congr_nhds hloc_f v), hdomH]
    ext w
    rw [mem_setOf_eq, mem_setOf_eq, subderivative_congr_nhds hloc_f w]

/-- For `f` regular at `x̄` and `v ∈ ∂f(x̄)`, `{w | df(x̄)(w) = ⟪v, w⟫} = N_{∂f(x̄)}(v)`. -/
theorem setOf_subderivative_eq_inner_eq_normalCone {f : E → EReal} {x v : E}
    (hr : IsSubdifferentiallyRegularAt f x) (hv : v ∈ subdifferential f x) :
    {w | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} = normalCone (subdifferential f x) v := by
  obtain ⟨-, -, hsupp, -, hconv, -, -⟩ := hr.subderivative_support_duality ⟨v, hv⟩
  rw [normalCone_eq_of_convex hconv hv, hsupp]
  ext w
  simp only [mem_setOf_eq]
  constructor
  · intro h c hc
    have h1 := (inner_le_supportFunction hc w).trans_eq h
    rw [EReal.coe_le_coe_iff] at h1
    rw [inner_sub_right]
    have e1 := real_inner_comm c w
    have e2 := real_inner_comm v w
    linarith
  · intro h
    refine le_antisymm ((supportFunction_le_iff _ _ _).2 fun c hc ↦ ?_)
      (inner_le_supportFunction hv w)
    have h1 := h c hc
    rw [inner_sub_right] at h1
    rw [EReal.coe_le_coe_iff]
    have e1 := real_inner_comm c w
    have e2 := real_inner_comm v w
    linarith

/-- The first-order facts about `f̄(z) = g(G(x̄) + ∇G(x̄)(z - x̄))` in Theorem 13.14: for convex
piecewise linear-quadratic `g` it is convex and piecewise linear-quadratic, with
`f̄(x̄) = f(x̄)`, `df̄(x̄) = df(x̄)` and `∂f̄(x̄) = ∂f(x̄)`. -/
theorem affineComp_first_order {G : E → F} (hG : ContDiff ℝ 2 G) {g : F → EReal}
    (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E}
    (hx : G x ∈ effectiveDomain g)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    IsPiecewiseLinearQuadratic (fun z ↦ g (G x + fderiv ℝ G x (z - x))) ∧
    Convex ℝ (epigraph (fun z ↦ g (G x + fderiv ℝ G x (z - x)))) ∧
    g (G x + fderiv ℝ G x (x - x)) = (g ∘ G) x ∧
    subderivative (fun z ↦ g (G x + fderiv ℝ G x (z - x))) x = subderivative (g ∘ G) x ∧
    subdifferential (fun z ↦ g (G x + fderiv ℝ G x (z - x))) x = subdifferential (g ∘ G) x := by
  set A := fderiv ℝ G x with hA
  have hfun : (fun z ↦ g (G x + A (z - x))) = fun z ↦ g (A z + (G x - A x)) := by
    funext z
    rw [map_sub]
    congr 1
    abel
  have hAx : A x + (G x - A x) = G x := by abel
  have hfin : g (G x) = ((g (G x)).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx) (hg.ne_bot _)).symm
  have hl : LowerSemicontinuous g := hg.lowerSemicontinuous
  have hlsc : IsLocallyLscAt g (G x) := isLocallyLscAt_of_isLocallyClosedAt_epigraph hfin
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal g hl) _)
  have hr : IsSubdifferentiallyRegularAt g (G x) :=
    (isSubdifferentiallyRegularAt_of_convex hgc hlsc).1
  have hx' : A x + (G x - A x) ∈ effectiveDomain g := by rw [hAx]; exact hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun]; exact hg.compAffine A _
  · rw [hfun]; exact convex_epigraph_compAffine hgc A _
  · simp
  · rw [hfun]
    funext w
    rw [hg.subderivative_compAffine A _ hx' w, hAx,
      subderivative_comp_eq_of_regular (hG.of_le (by norm_num)) hl hr hQ w]
  · rw [hfun, hg.subdifferential_compAffine hgc A _ hx', hAx,
      subdifferential_comp_eq_of_regular (hG.of_le (by norm_num)) hl hr hQ]

/-- **Theorem 13.14** (chain rule for second subderivatives).  Let `f = g ∘ G` with `G` of class
`C²`, `g` proper and lsc, finite and regular at `ū = G(x̄)`, under the qualification
`y ∈ ∂^∞g(ū), ∇G(x̄)* y = 0 ⇒ y = 0`.

* (10.6) `f` is regular at `x̄`, `df(x̄)(w) = dg(ū)(∇G(x̄)w)` and `∂f(x̄) = ∇G(x̄)* ∂g(ū)`.
* For `v ∈ ∂f(x̄)`, `Y(x̄, v)` is nonempty, convex and compact, and
  `d²f(x̄ | v)(w) ≥ sup_{y ∈ Y(x̄,v)} [d²g(ū | y)(∇G(x̄)w) + ⟪w, ∇²(yG)(x̄)w⟫]`.
* If `g` is fully amenable at `ū`, equality holds, `f` is properly twice epi-differentiable at `x̄`
  for every `v ∈ ∂f(x̄)`, and `dom d²f(x̄ | v) = {w | df(x̄)(w) = ⟪v, w⟫} = N_{∂f(x̄)}(v)`.
* If `g` is convex and piecewise linear-quadratic, the conclusions of the fully amenable case
  hold, `f̄(z) = g(ū + ∇G(x̄)(z - x̄))` is convex
  and piecewise linear-quadratic with the same value, subderivative and subgradients as `f` at
  `x̄`, formula 13(19) holds with the maximum attained, and
  `d²f̄(x̄ | v)(w) = d²g(ū | y)(∇G(x̄)w)` for any `y ∈ Y(x̄, v)`, which is `d²g(ū)(∇G(x̄)w)` when
  `dg(ū)(∇G(x̄)w) = ⟪v, w⟫` and `∞` otherwise. -/
theorem chain_rule_for_second_subderivatives {G : E → F} (hG : ContDiff ℝ 2 G) {g : F → EReal}
    (hl : LowerSemicontinuous g) {x : E} (hr : IsSubdifferentiallyRegularAt g (G x))
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    (IsSubdifferentiallyRegularAt (g ∘ G) x ∧
      (∀ w, subderivative (g ∘ G) x w = subderivative g (G x) (fderiv ℝ G x w)) ∧
      subdifferential (g ∘ G) x = (fderiv ℝ G x).adjoint '' subdifferential g (G x)) ∧
    (∀ v ∈ subdifferential (g ∘ G) x,
      (multiplierSet G g x v).Nonempty ∧ Convex ℝ (multiplierSet G g x v) ∧
      IsCompact (multiplierSet G g x v) ∧
      ∀ w, (⨆ y ∈ multiplierSet G g x v, (secondSubderivative g (G x) y (fderiv ℝ G x w) +
        ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal))) ≤ secondSubderivative (g ∘ G) x v w) ∧
    (FullyAmenableAt g (G x) → ∀ v ∈ subdifferential (g ∘ G) x,
      (∀ w, secondSubderivative (g ∘ G) x v w = ⨆ y ∈ multiplierSet G g x v,
        (secondSubderivative g (G x) y (fderiv ℝ G x w) +
          ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal))) ∧
      ProperlyTwiceEpiDifferentiableAt (g ∘ G) x v ∧
      effectiveDomain (secondSubderivative (g ∘ G) x v) =
        {w | subderivative (g ∘ G) x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} ∧
      {w | subderivative (g ∘ G) x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} =
        normalCone (subdifferential (g ∘ G) x) v) ∧
    (IsPiecewiseLinearQuadratic g → Convex ℝ (epigraph g) →
      (IsPiecewiseLinearQuadratic (fun z ↦ g (G x + fderiv ℝ G x (z - x))) ∧
        Convex ℝ (epigraph (fun z ↦ g (G x + fderiv ℝ G x (z - x)))) ∧
        g (G x + fderiv ℝ G x (x - x)) = (g ∘ G) x ∧
        subderivative (fun z ↦ g (G x + fderiv ℝ G x (z - x))) x = subderivative (g ∘ G) x ∧
        subdifferential (fun z ↦ g (G x + fderiv ℝ G x (z - x))) x =
          subdifferential (g ∘ G) x) ∧
      ∀ v ∈ subdifferential (g ∘ G) x,
        (∀ w, secondSubderivative (g ∘ G) x v w = ⨆ y ∈ multiplierSet G g x v,
          (secondSubderivative g (G x) y (fderiv ℝ G x w) +
            ((⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal))) ∧
        ProperlyTwiceEpiDifferentiableAt (g ∘ G) x v ∧
        effectiveDomain (secondSubderivative (g ∘ G) x v) =
          {w | subderivative (g ∘ G) x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} ∧
        {w | subderivative (g ∘ G) x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} =
          normalCone (subdifferential (g ∘ G) x) v ∧
        (∀ w, ∃ y₀ ∈ multiplierSet G g x v,
          (∀ y ∈ multiplierSet G g x v, ⟪y, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ ≤
            ⟪y₀, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ) ∧
          secondSubderivative (g ∘ G) x v w =
            secondSubderivative (fun z ↦ g (G x + fderiv ℝ G x (z - x))) x v w +
              ((⟪y₀, fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ : ℝ) : EReal)) ∧
        (∀ w, ∀ y ∈ multiplierSet G g x v,
          secondSubderivative (fun z ↦ g (G x + fderiv ℝ G x (z - x))) x v w =
            secondSubderivative g (G x) y (fderiv ℝ G x w)) ∧
        (∀ w, secondSubderivative (fun z ↦ g (G x + fderiv ℝ G x (z - x))) x v w =
          if subderivative g (G x) (fderiv ℝ G x w) = ((⟪v, w⟫_ℝ : ℝ) : EReal) then
            secondSubderivativeAt g (G x) (fderiv ℝ G x w) else ⊤)) := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  have hfin : g (G x) = ((g (G x)).toReal : EReal) := (EReal.coe_toReal hr.2.1 hr.1).symm
  have hrf : IsSubdifferentiallyRegularAt (g ∘ G) x := hr.comp_of_horizon_qualification hG1 hl hQ
  refine ⟨⟨hrf, subderivative_comp_eq_of_regular hG1 hl hr hQ,
    subdifferential_comp_eq_of_regular hG1 hl hr hQ⟩, fun v hv ↦ ?_, fun hga v hv ↦ ?_,
    fun hg hgc ↦ ?_⟩
  · obtain ⟨h1, h2, h3⟩ := multiplierSet_properties hG hl hr hQ hv
    exact ⟨h1, h2, h3, fun w ↦ iSup₂_le fun y hy ↦ secondSubderivative_comp_ge hG hfin hy.2 w⟩
  · obtain ⟨h1, h2, h3⟩ := chain_rule_second_subderivatives_fullyAmenable hG hga hQ hv
    exact ⟨h1, h2, h3, setOf_subderivative_eq_inner_eq_normalCone hrf hv⟩
  · have hx : G x ∈ effectiveDomain g := by
      rw [mem_effectiveDomain_iff, hfin]; exact EReal.coe_lt_top _
    refine ⟨affineComp_first_order hG hg hgc hx hQ, fun v hv ↦ ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := chain_rule_second_subderivatives_plq hG hg hgc hx hQ hv
    exact ⟨h1, h5, h6, setOf_subderivative_eq_inner_eq_normalCone hrf hv, h2, h3, h4⟩

/-! ### Corollary 13.15 -/

/-- A fully amenable function is properly twice epi-differentiable at the point for every
subgradient: Theorem 13.14 with `G = I`. -/
theorem FullyAmenableAt.properlyTwiceEpiDifferentiableAt {f : E → EReal} {x v : E}
    (hf : FullyAmenableAt f x) (hv : v ∈ subdifferential f x) :
    ProperlyTwiceEpiDifferentiableAt f x v := by
  have hid : ContDiff ℝ 2 (id : E → E) := contDiff_id
  have hQ : ∀ y ∈ horizonSubdifferential f (id x), (fderiv ℝ (id : E → E) x).adjoint y = 0 →
      y = 0 := by
    intro y _ hy
    rwa [fderiv_id, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply] at hy
  have h := (chain_rule_second_subderivatives_fullyAmenable hid (g := f) (x := x) hf hQ
    (by rwa [Function.comp_id])).2.1
  rwa [Function.comp_id] at h

/-- **Corollary 13.15** (second-order epi-differentiability from full amenability): if `f` is fully
amenable at `x̄`, there is `V ∈ 𝓝 x̄` such that `f` is properly twice epi-differentiable at `x` for
every `v ∈ ∂f(x)`, for all `x ∈ V ∩ dom f`. -/
theorem second_order_epi_differentiability_from_full_amenability {f : E → EReal} {x : E}
    (hf : FullyAmenableAt f x) :
    ∃ V ∈ 𝓝 x, ∀ y ∈ V ∩ effectiveDomain f, ∀ v ∈ subdifferential f y,
      ProperlyTwiceEpiDifferentiableAt f y v :=
  ⟨_, hf.eventually, fun _ ⟨hy, hyd⟩ _ hv ↦ (hy hyd).properlyTwiceEpiDifferentiableAt hv⟩

end RW
