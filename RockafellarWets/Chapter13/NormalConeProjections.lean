/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Normal cone mappings and projections

Corollary 13.43 (`normal_cone_mappings_and_projections`), adapted.

For a closed set `C` (the setting of 13.38, on which the book's proof relies) prox-regular at `x̄`
for `v̄ ∈ N_C(x̄)` with constants `ε, ρ`, and `0 < λ < λ₀` small, put `ū = x̄ + λv̄`.  Directly
from the prox-regularity inequality (`IsProxRegularSetAt.projection_localization`, with explicit
constants `projection_localization_of_constants`):
`P_C(u) ⊂ IB(x̄, 4‖u - ū‖)` near `ū`, `y ∈ P_C(u) ⟺ u - y ∈ N_C(y)` for `(u, y)` near `(ū, x̄)`, and
`‖y₁ - y₂‖ ≤ 2‖u₁ - u₂‖` for `yᵢ ∈ P_C(uᵢ)`.  So `P_C(ū) = {x̄}`, `P_C` is single-valued and
Lipschitz around `ū` (hence has the Aubin property), and its graph near `(ū, x̄)` is that of the
resolvent `(I + λN_C)⁻¹`; 12.64 (`graphicalDerivative_svResolvent`,
`isProtoDifferentiableAt_svResolvent_iff`) gives `DP_C(ū) = [I + λDN_C(x̄ ∣ v̄)]⁻¹` and the
equivalence of the proto-differentiability of `N_C` at `x̄` for `v̄` and of `P_C` at `ū` for `x̄`;
9.50 makes the latter semidifferentiability (`normal_cone_projection_conclusions`); Theorem 13.40
for `f = δ_C` (subdifferentially continuous) gives the equivalence with twice epi-differentiability
of `δ_C` and `DN_C(x̄ ∣ v̄) = ∂[½d²δ_C(x̄ ∣ v̄)]`
(`IsProxRegularSetAt.isProtoDifferentiableAt_normalCone_iff`).  Fully amenable sets satisfy all of
this (13.32, 13.15).

**Correction: the base point.**  The book states (b), (c) and the formula at `ū = x̄ + v̄`.  This
needs `x̄ ∈ P_C(x̄ + v̄)` with `P_C` single-valued nearby, which fails for large `v̄` on nonconvex
prox-regular sets.  For the closed set `C = {0, 1} ⊂ ℝ`, prox-regular at `x̄ = 0` for `v̄ = 1`,
`P_C(x̄ + v̄) = {1}` and `DP_C(ū ∣ x̄) ≠ [I + DN_C(x̄ ∣ v̄)]⁻¹`
(`NormalConeProjectionsCounterexample.normal_cone_projection_counterexample`); similarly, for the
circle `C` of radius `r < 1` in `ℝ²`, `x̄ = (r, 0)` and the inward unit normal `v̄ = (-1, 0)`,
`P_C(x̄ + v̄) = P_C(r - 1, 0) = {(-r, 0)}`, and the formula read at `(-r, 0)` has the wrong sign
(`NormalConeProjectionsCircle.normal_cone_projection_circle_counterexample`, for spheres in any
finite-dimensional space).  The statement holds at `ū = x̄ + λv̄` for all sufficiently small
`λ > 0`, with `DP_C(ū) = [I + λDN_C(x̄ ∣ v̄)]⁻¹`; the proof takes `λ₀ ≤ 1/2`, so this never
reaches the printed case `λ = 1`.  The printed base point is covered in two cases: for
closed convex `C` and every `v̄ ∈ N_C(x̄)` (`normal_cone_mappings_and_projections_convex`), and when
the constants `ε, ρ` of prox-regularity at `x̄` for `v̄` satisfy `2‖v̄‖ < ε` and `ρ‖v̄‖ < ‖v̄‖ + ε`
(`normal_cone_mappings_and_projections_of_constants`, below).

**The printed base point.**  Let the inequality of prox-regularity hold at `x̄` for `v̄` with
constants `ε, ρ`, `2‖v̄‖ < ε` and `ρ‖v̄‖ < ‖v̄‖ + ε`.  Normal cones are cones, so applying the
inequality to `cv'` with `c = (‖v̄‖ + ε)/(‖v̄‖ + θ)` gives a constant `κ < 1` for the normals `v'`
within some `θ > 0` of `v̄` (`exists_proxRegular_constant_lt_one`).  With it, every point `w ∈ C` at
least as close to `u` as `x̄` satisfies `(1 - κ)‖w - x̄‖ ≤ 2‖u - ū‖` for `u` near `ū = x̄ + v̄`, and
`P_C` is localized around `ū` with Lipschitz constant `(1 - κ)⁻¹`
(`projection_localization_of_lt_one`).  The bound on all such `w` makes nearest points exist near
`ū` as soon as `C ∩ IB(x̄, δ)` is closed for some `δ > 0`
(`projMapping_nonempty_of_isClosed_inter_closedBall`), and then `gph P_C` is locally closed at
`(ū, x̄)` (`isLocallyClosedAt_svGraph_projMapping`).  So the corollary holds at `ū = x̄ + v̄` for
`C` locally closed at `x̄`, as prox-regularity already requires, with no closedness of `C` away
from `x̄` (`normal_cone_mappings_and_projections_of_constants`); under the constants `ρ ≤ 1/2`,
`‖v̄‖ ≤ ε/4` of the earlier statement for closed `C`
(`normal_cone_mappings_and_projections_of_small`) this is
`normal_cone_mappings_and_projections_of_small_local`.  Neither strict inequality can be relaxed:
for `C = {0} ∪ (2, 3) ⊂ ℝ`, locally closed at `x̄ = 0`, with `v̄ = 1`, `ε = 2` and `ρ = 0`, no point
of `C` is nearest to `u ∈ (1, 2)`
(`NormalConeProjectionsCounterexample.normal_cone_projection_radius_counterexample`), and for the
closed set `C = {-1, 1}` with `x̄ = 1`, `v̄ = -1`, `ε = 3` and `ρ = 4`, `P_C(x̄ + v̄) = {-1, 1}`
(`NormalConeProjectionsCounterexample.normal_cone_projection_curvature_counterexample`).

**Closedness.**  `normal_cone_mappings_and_projections_of_proxRegular` and
`normal_cone_mappings_and_projections` assume `C` closed, as their existing uses do.  The book does
not, and the assumption is not needed: prox-regularity includes local closedness at `x̄`, and for a
neighborhood `V` of `x̄` with `C ∩ V` closed, the normal cones and `δ_C` near `x̄` and `P_C` near
`ū` do not change when `C` is replaced by `C ∩ V` (`projMapping_inter_eq_of_ball_subset`).  This
gives `normal_cone_mappings_and_projections_of_proxRegular_local` and
`normal_cone_mappings_and_projections_local`.

**The normal `λv̄`.**  Prox-regularity at `x̄` for `v̄` is prox-regularity for `λv̄`, `λ > 0`
(`isProxRegularSetAt_smul_iff`).  Since `N_C` is cone-valued, `DN_C(x̄ ∣ λv̄) = λDN_C(x̄ ∣ v̄)`
(`graphicalDerivative_normalCone_smul`), `N_C` is proto-differentiable at `x̄` for `λv̄` exactly
when it is for `v̄` (`isProtoDifferentiableAt_normalCone_smul_iff`), and
`d²δ_C(x̄ ∣ λv̄) = λd²δ_C(x̄ ∣ v̄)` (`secondSubderivative_indicatorVA_smul`).  So for all small
`λ > 0` the corollary holds as printed for the normal `λv̄`, at `ū = x̄ + λv̄`
(`normal_cone_mappings_and_projections_scaled`), and the `λ`-form above is the same statement
read at `v̄`.  What the printed statement asks for `v̄` itself is not invariant under scaling:
`x̄` must be the only nearest point to `x̄ + v̄`, with `P_C` localized around it, and the
two-point set and the circle show that prox-regularity does not give this.  The remaining
hypothesis is quantitative: `2‖v̄‖ < ε` and `ρ‖v̄‖ < ‖v̄‖ + ε` for constants `ε, ρ` at `v̄`, both
sharp, with `C` locally closed at `x̄` (`normal_cone_mappings_and_projections_of_constants`), or
`C` closed and convex.
-/

import RockafellarWets.Chapter13.SubgradientProtoDifferentiability
import RockafellarWets.Chapter13.ProxRegularProjections
import RockafellarWets.Chapter13.SecondOrderChainRuleAmenable
import RockafellarWets.Chapter12.MonotoneProtoDerivatives
import RockafellarWets.Chapter12.MonotoneDomains
import RockafellarWets.Chapter2.ProjectionsProx

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace NNReal

namespace RW

section Congruence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Proto-differentiability and graphical derivatives only depend on the graph near the point. -/
theorem isProtoDifferentiableAt_congr_of_eventually {S S' : E → Set E} {x u : E}
    (h : ∀ᶠ p in 𝓝 (x, u), p.2 ∈ S p.1 ↔ p.2 ∈ S' p.1) :
    (IsProtoDifferentiableAt S x u ↔ IsProtoDifferentiableAt S' x u) ∧
      graphicalDerivative S x u = graphicalDerivative S' x u := by
  set T₀ : E → Set E := fun y ↦ {w | w + u ∈ S y} with hT₀
  have h1 : ∀ᶠ p in 𝓝 (x, u), p.2 ∈ S p.1 ↔ p.2 - u ∈ T₀ p.1 :=
    Eventually.of_forall fun p ↦ by simp [hT₀]
  have h2 : ∀ᶠ p in 𝓝 (x, u), p.2 ∈ S' p.1 ↔ p.2 - u ∈ T₀ p.1 :=
    h.mono fun p hp ↦ by simp [hT₀, hp]
  obtain ⟨a1, b1⟩ := isProtoDifferentiableAt_iff_of_eventually h1
  obtain ⟨a2, b2⟩ := isProtoDifferentiableAt_iff_of_eventually h2
  exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩

/-- Membership in the resolvent `(I + λN_C)⁻¹`: for `λ > 0`, `y ∈ (I + λN_C)⁻¹(u)` exactly when
`u - y ∈ N_C(y)`. -/
theorem mem_svResolvent_normalCone_iff {C : Set E} {lam : ℝ} (hlam : 0 < lam) {u y : E} :
    y ∈ svResolvent (normalCone C) lam u ↔ u - y ∈ normalCone C y := by
  have h := Set.ext_iff.1 (svGraph_svResolvent_eq_preimage (normalCone C) hlam.ne') (u, y)
  change y ∈ svResolvent (normalCone C) lam u ↔ lam⁻¹ • (u - y) ∈ normalCone C y at h
  rw [h]
  constructor
  · intro hN
    have := (isCone_normalCone hN.1).2 hN hlam
    rwa [smul_inv_smul₀ hlam.ne'] at this
  · intro hN
    exact (isCone_normalCone hN.1).2 hN (inv_pos.2 hlam)

end Congruence

section ConicScaling

/-! ### Mappings with conic values

When every value of `S` is a cone, as for `N_C`, the graph of `S` is invariant under
`(x, u) ↦ (x, cu)` for `c > 0`, so the derivatives of `S` at `cū` are those at `ū` rescaled. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `(w, z) ↦ (w, cz)` on the Euclidean product, for `c ≠ 0`. -/
private noncomputable def euclideanScaleSnd (c : ℝ) (hc : c ≠ 0) :
    WithLp 2 (E × F) ≃L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).trans
    (((ContinuousLinearEquiv.refl ℝ E).prodCongr
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 c hc))).trans
        (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm)

private theorem euclideanScaleSnd_toLp (c : ℝ) (hc : c ≠ 0) (w : E) (z : F) :
    euclideanScaleSnd c hc (WithLp.toLp 2 (w, z)) = WithLp.toLp 2 (w, c • z) := by
  simp [euclideanScaleSnd, Units.smul_def]

private theorem euclideanSvGraph_preimage_scaleSnd {S : E → Set F}
    (hS : ∀ y, ∀ u ∈ S y, ∀ c : ℝ, 0 < c → c • u ∈ S y) {c : ℝ} (hc : 0 < c) :
    euclideanScaleSnd c hc.ne' ⁻¹' euclideanSvGraph S = euclideanSvGraph S := by
  ext p
  obtain ⟨w, z⟩ := p
  change euclideanScaleSnd c hc.ne' (WithLp.toLp 2 (w, z)) ∈ euclideanSvGraph S ↔ z ∈ S w
  rw [euclideanScaleSnd_toLp]
  change c • z ∈ S w ↔ z ∈ S w
  refine ⟨fun h ↦ ?_, fun h ↦ hS w z h c hc⟩
  have := hS w _ h c⁻¹ (inv_pos.2 hc)
  rwa [inv_smul_smul₀ hc.ne'] at this

open scoped Pointwise in
/-- For a mapping with conic values, `DS(x̄ ∣ cū) = c DS(x̄ ∣ ū)` for `c > 0`. -/
theorem graphicalDerivative_smul_of_conic {S : E → Set F}
    (hS : ∀ y, ∀ u ∈ S y, ∀ c : ℝ, 0 < c → c • u ∈ S y) (x : E) (u : F) {c : ℝ} (hc : 0 < c)
    (w : E) : graphicalDerivative S x (c • u) w = c • graphicalDerivative S x u w := by
  have key : tangentCone (euclideanSvGraph S) (WithLp.toLp 2 (x, u)) =
      euclideanScaleSnd c hc.ne' ⁻¹'
        tangentCone (euclideanSvGraph S) (WithLp.toLp 2 (x, c • u)) := by
    conv_lhs => rw [← euclideanSvGraph_preimage_scaleSnd hS hc]
    rw [tangentCone_preimage_continuousLinearEquiv, euclideanScaleSnd_toLp]
  ext z
  simp only [graphicalDerivative, svOfEuclideanGraph, mem_setOf_eq, mem_smul_set]
  constructor
  · intro hz
    refine ⟨c⁻¹ • z, ?_, smul_inv_smul₀ hc.ne' z⟩
    rw [key, mem_preimage, euclideanScaleSnd_toLp, smul_inv_smul₀ hc.ne']
    exact hz
  · rintro ⟨z', hz', rfl⟩
    rw [key, mem_preimage, euclideanScaleSnd_toLp] at hz'
    exact hz'

/-- For a mapping with conic values and `ū ∈ S(x̄)`, proto-differentiability at `x̄` for `cū`,
`c > 0`, is proto-differentiability at `x̄` for `ū`. -/
theorem isProtoDifferentiableAt_smul_iff_of_conic {S : E → Set F}
    (hS : ∀ y, ∀ u ∈ S y, ∀ c : ℝ, 0 < c → c • u ∈ S y) {x : E} {u : F} (hu : u ∈ S x)
    {c : ℝ} (hc : 0 < c) :
    IsProtoDifferentiableAt S x (c • u) ↔ IsProtoDifferentiableAt S x u := by
  rw [isProtoDifferentiableAt_iff_geometricallyDerivable (hS x u hu c hc),
    isProtoDifferentiableAt_iff_geometricallyDerivable hu]
  conv_rhs => rw [← euclideanSvGraph_preimage_scaleSnd hS hc]
  rw [isGeometricallyDerivable_preimage_continuousLinearEquiv, euclideanScaleSnd_toLp]

end ConicScaling

section Localization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {C : Set E} {x v : E}

/-- The values of `N_C` are cones. -/
private theorem normalCone_conic (C : Set E) :
    ∀ y, ∀ u ∈ normalCone C y, ∀ c : ℝ, 0 < c → c • u ∈ normalCone C y :=
  fun _ _ hu _ hc ↦ (isCone_normalCone hu.1).2 hu hc

open scoped Pointwise in
/-- `DN_C(x̄ ∣ cv̄) = c DN_C(x̄ ∣ v̄)` for `c > 0`, because normal cones are cones. -/
theorem graphicalDerivative_normalCone_smul {c : ℝ} (hc : 0 < c) :
    graphicalDerivative (normalCone C) x (c • v) =
      fun w ↦ c • graphicalDerivative (normalCone C) x v w :=
  funext (graphicalDerivative_smul_of_conic (normalCone_conic C) x v hc)

/-- For `v̄ ∈ N_C(x̄)` and `c > 0`, `N_C` is proto-differentiable at `x̄` for `cv̄` exactly when it
is for `v̄`. -/
theorem isProtoDifferentiableAt_normalCone_smul_iff (hv : v ∈ normalCone C x) {c : ℝ}
    (hc : 0 < c) :
    IsProtoDifferentiableAt (normalCone C) x (c • v) ↔
      IsProtoDifferentiableAt (normalCone C) x v :=
  isProtoDifferentiableAt_smul_iff_of_conic (normalCone_conic C) hv hc

/-- `d²δ_C(x̄ ∣ cv̄) = c d²δ_C(x̄ ∣ v̄)` for `x̄ ∈ C` and `c > 0`: the quotients 13(5) of `δ_C` for
`cv̄` are `c` times those for `v̄`. -/
theorem secondSubderivative_indicatorVA_smul (hx : x ∈ C) {c : ℝ} (hc : 0 < c) (w : E) :
    secondSubderivative (indicatorVA C) x (c • v) w =
      (c : EReal) * secondSubderivative (indicatorVA C) x v w := by
  have hx0 : indicatorVA C x = ((0 : ℝ) : EReal) := by
    rw [indicatorVA_apply_mem hx, EReal.coe_zero]
  rw [secondSubderivative, secondSubderivative, EReal.coe_mul_liminf_of_pos _ hc]
  apply liminf_congr
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
  obtain ⟨τ, w'⟩ := p
  change 0 < τ at hp
  by_cases hw : x + τ • w' ∈ C
  · have hw0 : indicatorVA C (x + τ • w') = ((0 : ℝ) : EReal) := by
      rw [indicatorVA_apply_mem hw, EReal.coe_zero]
    rw [secondDifferenceQuotient_of_coe hx0 hw0, secondDifferenceQuotient_of_coe hx0 hw0,
      ← EReal.coe_mul, real_inner_smul_left]
    congr 1
    ring
  · rw [secondDifferenceQuotient_of_top hp.ne' hx0 (indicatorVA_apply_not_mem hw),
      secondDifferenceQuotient_of_top hp.ne' hx0 (indicatorVA_apply_not_mem hw),
      EReal.coe_mul_top_of_pos hc]

/-- Prox-regularity of `C` at `x̄` for `v̄` passes to `cv̄`, `c > 0`, with constants `min ε (cε)`
and `cρ` in place of `ε` and `ρ`: normal cones are cones. -/
theorem IsProxRegularSetAt.smul (hpr : IsProxRegularSetAt C x v) {c : ℝ} (hc : 0 < c) :
    IsProxRegularSetAt C x (c • v) := by
  obtain ⟨hlc, hv, ε, hε, ρ, hρ, hprox⟩ := hpr
  refine ⟨hlc, (isCone_normalCone hv.1).2 hv hc, min ε (c * ε), lt_min hε (mul_pos hc hε),
    c * ρ, mul_nonneg hc.le hρ, fun y v' hv' hvv hy x' hx' ↦ ?_⟩
  have hv'' : c⁻¹ • v' ∈ normalCone C y := (isCone_normalCone hv'.1).2 hv' (inv_pos.2 hc)
  have hclose : ‖c⁻¹ • v' - v‖ < ε := by
    have e : c⁻¹ • v' - v = c⁻¹ • (v' - c • v) := by
      rw [smul_sub, inv_smul_smul₀ hc.ne']
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le), inv_mul_lt_iff₀ hc]
    exact lt_of_lt_of_le hvv (min_le_right _ _)
  have hb : x' ∈ C ∩ closedBall x ε :=
    ⟨hx'.1, closedBall_subset_closedBall (min_le_left _ _) hx'.2⟩
  have h := hprox y _ hv'' hclose (lt_of_lt_of_le hy (min_le_left _ _)) x' hb
  rw [real_inner_smul_left] at h
  have h' := mul_le_mul_of_nonneg_left h hc.le
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h'
  linarith

/-- `C` is prox-regular at `x̄` for `cv̄`, `c > 0`, exactly when it is prox-regular at `x̄` for
`v̄`. -/
theorem isProxRegularSetAt_smul_iff {c : ℝ} (hc : 0 < c) :
    IsProxRegularSetAt C x (c • v) ↔ IsProxRegularSetAt C x v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smul hc⟩
  have := h.smul (inv_pos.2 hc)
  rwa [inv_smul_smul₀ hc.ne'] at this

/-- The quantitative localization of `P_C` near `ū = x̄ + λv̄` with explicit constants.  Let
`v̄ ∈ N_C(x̄)` and suppose the inequality of `IsProxRegularSetAt` holds at `x̄` for `v̄` with
constants `ε > 0` and `ρ`; let `0 < λ ≤ 1` with `λρ ≤ 1/2` and `λ‖v̄‖ ≤ ε/4`.  Then for some
`r > 0`, nearest points to `u` with `‖u - ū‖ < r` lie in `IB(x̄, 4‖u - ū‖)`, near `(ū, x̄)` they
are characterized by `u - y ∈ N_C(y)`, and they depend Lipschitz continuously on `u` with
constant `2`. -/
theorem projection_localization_of_constants (hv : v ∈ normalCone C x) {ε ρ : ℝ} (hε : 0 < ε)
    (hprox : ∀ y v', v' ∈ normalCone C y → ‖v' - v‖ < ε → ‖y - x‖ < ε →
      ∀ x' ∈ C ∩ closedBall x ε, ⟪v', x' - y⟫_ℝ ≤ ρ / 2 * ‖x' - y‖ ^ 2)
    {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hlamρ : lam * ρ ≤ 1 / 2)
    (hlamv : lam * ‖v‖ ≤ ε / 4) :
    ∃ r > 0,
      (∀ u, ‖u - (x + lam • v)‖ < r → ∀ y ∈ projMapping C u,
        ‖y - x‖ ≤ 4 * ‖u - (x + lam • v)‖) ∧
      (∀ u y, ‖u - (x + lam • v)‖ < r → ‖y - x‖ < r →
        (y ∈ projMapping C u ↔ u - y ∈ normalCone C y)) ∧
      (∀ u₁ u₂, ‖u₁ - (x + lam • v)‖ < r → ‖u₂ - (x + lam • v)‖ < r →
        ∀ y₁ ∈ projMapping C u₁, ∀ y₂ ∈ projMapping C u₂, ‖y₁ - y₂‖ ≤ 2 * ‖u₁ - u₂‖) := by
  have hx : x ∈ C := hv.1
  set ū := x + lam • v with hū
  set r := lam * ε / 8 with hr
  have hr0 : 0 < r := by positivity
  have hrε : r ≤ ε / 8 := by rw [hr]; nlinarith
  have hux : ∀ u, ‖u - x‖ ≤ lam * ‖v‖ + ‖u - ū‖ := by
    intro u
    calc ‖u - x‖ = ‖lam • v + (u - ū)‖ := by rw [hū]; congr 1; abel
      _ ≤ ‖lam • v‖ + ‖u - ū‖ := norm_add_le _ _
      _ = lam * ‖v‖ + ‖u - ū‖ := by rw [norm_smul, Real.norm_of_nonneg hlam.le]
  -- (P1) nearest points stay close to `x̄`
  have P1 : ∀ u, ‖u - ū‖ < r → ∀ y ∈ projMapping C u, ‖y - x‖ ≤ 4 * ‖u - ū‖ := by
    intro u hu y hy
    set d := u - ū with hd
    have hyu : ‖y - u‖ ≤ ‖x - u‖ := hy.2 x hx
    have hyx : ‖y - x‖ ≤ ε := by
      calc ‖y - x‖ = ‖(y - u) + (u - x)‖ := by congr 1; abel
        _ ≤ ‖y - u‖ + ‖u - x‖ := norm_add_le _ _
        _ ≤ ‖x - u‖ + ‖u - x‖ := by gcongr
        _ = 2 * ‖u - x‖ := by rw [norm_sub_rev x u]; ring
        _ ≤ 2 * (lam * ‖v‖ + ‖d‖) := by gcongr; exact hux u
        _ ≤ ε := by linarith
    have hpi := hprox x v hv (by rw [sub_self, norm_zero]; exact hε)
      (by rw [sub_self, norm_zero]; exact hε) y ⟨hy.1, by rwa [mem_closedBall, dist_eq_norm]⟩
    have e1 : y - u = (y - x) - (lam • v + d) := by rw [hd, hū]; abel
    have e2 : x - u = -(lam • v + d) := by rw [hd, hū]; abel
    have hsq : ‖y - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyu 2
    rw [e1, e2, norm_neg, norm_sub_sq_real, inner_add_right, real_inner_smul_right,
      real_inner_comm v] at hsq
    have h1 : ⟪y - x, d⟫_ℝ ≤ ‖y - x‖ * ‖d‖ := real_inner_le_norm _ _
    have h2 : lam * ⟪y - x, v⟫_ℝ ≤ lam * (ρ / 2 * ‖y - x‖ ^ 2) := by
      rw [real_inner_comm]; exact mul_le_mul_of_nonneg_left hpi hlam.le
    have h3 : lam * (ρ / 2 * ‖y - x‖ ^ 2) ≤ 1 / 4 * ‖y - x‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hlamρ (sq_nonneg ‖y - x‖)]
    have h4 : ‖y - x‖ ^ 2 ≤ 4 * ‖d‖ * ‖y - x‖ := by nlinarith
    rcases eq_or_lt_of_le (norm_nonneg (y - x)) with h0 | hpos
    · rw [← h0]; positivity
    · nlinarith
  -- normals at nearby nearest points
  have hnormal : ∀ u y, ‖u - ū‖ < 4 * r → ‖y - x‖ < 4 * r → u - y ∈ normalCone C y →
      lam⁻¹ • (u - y) ∈ normalCone C y ∧ ‖lam⁻¹ • (u - y) - v‖ < ε := by
    intro u y hu hy hN
    refine ⟨(isCone_normalCone hN.1).2 hN (inv_pos.2 hlam), ?_⟩
    have e : lam⁻¹ • (u - y) - v = lam⁻¹ • ((u - ū) - (y - x)) := by
      rw [hū, show u - (x + lam • v) - (y - x) = (u - y) - lam • v by abel,
        smul_sub lam⁻¹ (u - y) (lam • v), inv_smul_smul₀ hlam.ne']
    rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hlam.le, inv_mul_lt_iff₀ hlam]
    calc ‖(u - ū) - (y - x)‖ ≤ ‖u - ū‖ + ‖y - x‖ := norm_sub_le _ _
      _ < 4 * r + 4 * r := by linarith
      _ = lam * ε := by rw [hr]; ring
      _ ≤ lam * ε := le_rfl
  refine ⟨r, hr0, P1, fun u y hu hy ↦ ⟨fun hP ↦ ?_, fun hN ↦ ?_⟩, ?_⟩
  · exact regularNormalCone_subset_normalCone C y (sub_mem_regularNormalCone_of_mem_projMapping hP)
  · -- (P2) normals near `λv̄` at points near `x̄` give nearest points
    have hyC : y ∈ C := hN.1
    obtain ⟨hn, hnv⟩ := hnormal u y (by linarith) (by linarith) hN
    refine ⟨hyC, fun w hw ↦ ?_⟩
    by_cases hwb : w ∈ closedBall x ε
    · have hpi := hprox y _ hn hnv (by linarith) w ⟨hw, hwb⟩
      rw [real_inner_smul_left] at hpi
      have h1 : ⟪u - y, w - y⟫_ℝ ≤ 1 / 2 * ‖w - y‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hpi hlam.le
        rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at this
        nlinarith [mul_le_mul_of_nonneg_right hlamρ (sq_nonneg ‖w - y‖)]
      have e1 : w - u = (w - y) - (u - y) := by abel
      have h2 : ‖y - u‖ ^ 2 ≤ ‖w - u‖ ^ 2 := by
        have e2 := norm_sub_sq_real (w - y) (u - y)
        rw [norm_sub_rev y u, e1, e2, real_inner_comm]
        nlinarith [sq_nonneg ‖w - y‖]
      exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.1 h2
    · rw [mem_closedBall, dist_eq_norm, not_le] at hwb
      have h1 := hux u
      calc ‖y - u‖ ≤ ‖y - x‖ + ‖x - u‖ := by
            calc ‖y - u‖ = ‖(y - x) + (x - u)‖ := by congr 1; abel
              _ ≤ _ := norm_add_le _ _
        _ ≤ ‖w - x‖ - ‖u - x‖ := by rw [norm_sub_rev x u]; linarith
        _ ≤ ‖w - u‖ := by
            have := norm_sub_le (w - u) (x - u)
            rw [show w - u - (x - u) = w - x by abel, norm_sub_rev x u] at this
            linarith
  · -- (P3) the Lipschitz estimate
    intro u₁ u₂ hu₁ hu₂ y₁ hy₁ y₂ hy₂
    have hy₁x := P1 u₁ hu₁ y₁ hy₁
    have hy₂x := P1 u₂ hu₂ y₂ hy₂
    have hN₁ := regularNormalCone_subset_normalCone C y₁
      (sub_mem_regularNormalCone_of_mem_projMapping hy₁)
    have hN₂ := regularNormalCone_subset_normalCone C y₂
      (sub_mem_regularNormalCone_of_mem_projMapping hy₂)
    obtain ⟨hn₁, hnv₁⟩ := hnormal u₁ y₁ (by linarith) (by linarith) hN₁
    obtain ⟨hn₂, hnv₂⟩ := hnormal u₂ y₂ (by linarith) (by linarith) hN₂
    have hb₁ : y₁ ∈ C ∩ closedBall x ε := ⟨hy₁.1, by rw [mem_closedBall, dist_eq_norm]; linarith⟩
    have hb₂ : y₂ ∈ C ∩ closedBall x ε := ⟨hy₂.1, by rw [mem_closedBall, dist_eq_norm]; linarith⟩
    have i1 := hprox y₁ _ hn₁ hnv₁ (by linarith) y₂ hb₂
    have i2 := hprox y₂ _ hn₂ hnv₂ (by linarith) y₁ hb₁
    rw [real_inner_smul_left] at i1 i2
    set D := y₁ - y₂ with hD
    have eD : y₂ - y₁ = -D := by rw [hD]; abel
    rw [eD, inner_neg_right, norm_neg] at i1
    have j1 : -⟪u₁ - y₁, D⟫_ℝ ≤ lam * ρ / 2 * ‖D‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left i1 hlam.le
      have e : lam * (lam⁻¹ * -⟪u₁ - y₁, D⟫_ℝ) = -⟪u₁ - y₁, D⟫_ℝ := by field_simp
      rw [e] at h; linarith
    have j2 : ⟪u₂ - y₂, D⟫_ℝ ≤ lam * ρ / 2 * ‖D‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left i2 hlam.le
      have e : lam * (lam⁻¹ * ⟪u₂ - y₂, D⟫_ℝ) = ⟪u₂ - y₂, D⟫_ℝ := by field_simp
      rw [e] at h; linarith
    have e : u₁ - u₂ = (u₁ - y₁) - (u₂ - y₂) + D := by rw [hD]; abel
    have hkey : ‖D‖ ^ 2 - lam * ρ * ‖D‖ ^ 2 ≤ ⟪u₁ - u₂, D⟫_ℝ := by
      rw [e, inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
      linarith only [j1, j2]
    have hle : ⟪u₁ - u₂, D⟫_ℝ ≤ ‖u₁ - u₂‖ * ‖D‖ := real_inner_le_norm _ _
    have h6 : lam * ρ * ‖D‖ ^ 2 ≤ 1 / 2 * ‖D‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlamρ (sq_nonneg ‖D‖)
    have h5 : ‖D‖ ^ 2 ≤ 2 * ‖u₁ - u₂‖ * ‖D‖ := by
      linarith only [hkey, hle, h6]
    rcases eq_or_lt_of_le (norm_nonneg D) with h0 | hpos
    · rw [← h0]; positivity
    · have h7 : ‖D‖ * ‖D‖ ≤ (2 * ‖u₁ - u₂‖) * ‖D‖ := by nlinarith only [h5]
      exact le_of_mul_le_mul_right h7 hpos

/-- The quantitative localization of `P_C` near `ū = x̄ + λv̄` for small `λ`: nearest points lie in
`IB(x̄, 4‖u - ū‖)`, near `(ū, x̄)` they are characterized by `u - y ∈ N_C(y)`, and they depend
Lipschitz continuously on `u` with constant `2`. -/
theorem IsProxRegularSetAt.projection_localization (hpr : IsProxRegularSetAt C x v) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ r > 0,
      (∀ u, ‖u - (x + lam • v)‖ < r → ∀ y ∈ projMapping C u,
        ‖y - x‖ ≤ 4 * ‖u - (x + lam • v)‖) ∧
      (∀ u y, ‖u - (x + lam • v)‖ < r → ‖y - x‖ < r →
        (y ∈ projMapping C u ↔ u - y ∈ normalCone C y)) ∧
      (∀ u₁ u₂, ‖u₁ - (x + lam • v)‖ < r → ‖u₂ - (x + lam • v)‖ < r →
        ∀ y₁ ∈ projMapping C u₁, ∀ y₂ ∈ projMapping C u₂, ‖y₁ - y₂‖ ≤ 2 * ‖u₁ - u₂‖) := by
  obtain ⟨-, hv, ε, hε, ρ, hρ, hprox⟩ := hpr
  refine ⟨min (1 / (2 * (ρ + 1))) (ε / (4 * (‖v‖ + 1))), lt_min (by positivity) (by positivity),
    fun lam hlam hlam₀ ↦ ?_⟩
  have hlamρ : lam * ρ ≤ 1 / 2 := by
    have h1 : lam < 1 / (2 * (ρ + 1)) := lt_of_lt_of_le hlam₀ (min_le_left _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hlam1 : lam ≤ 1 := by
    have h1 : lam < 1 / (2 * (ρ + 1)) := lt_of_lt_of_le hlam₀ (min_le_left _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hlamv : lam * ‖v‖ ≤ ε / 4 := by
    have h1 : lam < ε / (4 * (‖v‖ + 1)) := lt_of_lt_of_le hlam₀ (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg v]
  exact projection_localization_of_constants hv hε hprox hlam hlam1 hlamρ hlamv

/-- The quantitative localization of `P_C` near `ū = x̄ + v̄` with sharper constants.  Let
`v̄ ∈ N_C(x̄)` and suppose that `⟪v', x' - y⟫ ≤ κ/2‖x' - y‖²` for `x' ∈ C ∩ IB(x̄, ε)` whenever
`v' ∈ N_C(y)`, `‖v' - v̄‖ < θ` and `‖y - x̄‖ < ε`, where `θ > 0`, `0 ≤ κ < 1` and `2‖v̄‖ < ε`.
Then for some `r > 0`: every `w ∈ C` with `‖w - u‖ ≤ ‖x̄ - u‖`, in particular every nearest point
to `u`, satisfies `(1 - κ)‖w - x̄‖ ≤ 2‖u - ū‖` when `‖u - ū‖ < r`; near `(ū, x̄)`, `y ∈ P_C(u)`
exactly when `u - y ∈ N_C(y)`; and `(1 - κ)‖y₁ - y₂‖ ≤ ‖u₁ - u₂‖` for `yᵢ ∈ P_C(uᵢ)`.  The bound
on all points of `C` at least as close to `u` as `x̄` gives nearest points without closedness of
`C` away from `x̄` (`projMapping_nonempty_of_isClosed_inter_closedBall`). -/
theorem projection_localization_of_lt_one (hv : v ∈ normalCone C x) {ε θ κ : ℝ}
    (hθ : 0 < θ) (hκ0 : 0 ≤ κ) (hκ : κ < 1) (hvε : 2 * ‖v‖ < ε)
    (hprox : ∀ y v', v' ∈ normalCone C y → ‖v' - v‖ < θ → ‖y - x‖ < ε →
      ∀ x' ∈ C ∩ closedBall x ε, ⟪v', x' - y⟫_ℝ ≤ κ / 2 * ‖x' - y‖ ^ 2) :
    ∃ r > 0,
      (∀ u, ‖u - (x + v)‖ < r → ∀ w ∈ C, ‖w - u‖ ≤ ‖x - u‖ →
        (1 - κ) * ‖w - x‖ ≤ 2 * ‖u - (x + v)‖) ∧
      (∀ u y, ‖u - (x + v)‖ < r → ‖y - x‖ < r →
        (y ∈ projMapping C u ↔ u - y ∈ normalCone C y)) ∧
      (∀ u₁ u₂, ‖u₁ - (x + v)‖ < r → ‖u₂ - (x + v)‖ < r →
        ∀ y₁ ∈ projMapping C u₁, ∀ y₂ ∈ projMapping C u₂, (1 - κ) * ‖y₁ - y₂‖ ≤ ‖u₁ - u₂‖) := by
  have hx : x ∈ C := hv.1
  set ū := x + v with hū
  set m := min θ (ε - 2 * ‖v‖) with hm
  have hm0 : 0 < m := lt_min hθ (by linarith)
  have hmθ : m ≤ θ := min_le_left _ _
  have hmε : m ≤ ε - 2 * ‖v‖ := min_le_right _ _
  have hκ1 : 0 < 1 - κ := by linarith
  have hmε' : m ≤ ε := by linarith [norm_nonneg v]
  set r := (1 - κ) * m / 3 with hr
  have hr0 : 0 < r := by positivity
  have hrm : r ≤ m / 3 := by
    rw [hr]; nlinarith
  have hux : ∀ u, ‖u - x‖ ≤ ‖v‖ + ‖u - ū‖ := by
    intro u
    calc ‖u - x‖ = ‖v + (u - ū)‖ := by rw [hū]; congr 1; abel
      _ ≤ ‖v‖ + ‖u - ū‖ := norm_add_le _ _
  -- (P1) points of `C` at least as close to `u` as `x̄` stay close to `x̄`
  have P1 : ∀ u, ‖u - ū‖ < r → ∀ w ∈ C, ‖w - u‖ ≤ ‖x - u‖ →
      (1 - κ) * ‖w - x‖ ≤ 2 * ‖u - ū‖ := by
    intro u hu w hw hwu
    set d := u - ū with hd
    have hwx : ‖w - x‖ ≤ ε := by
      calc ‖w - x‖ = ‖(w - u) + (u - x)‖ := by congr 1; abel
        _ ≤ ‖w - u‖ + ‖u - x‖ := norm_add_le _ _
        _ ≤ ‖x - u‖ + ‖u - x‖ := by gcongr
        _ = 2 * ‖u - x‖ := by rw [norm_sub_rev x u]; ring
        _ ≤ 2 * (‖v‖ + ‖d‖) := by gcongr; exact hux u
        _ ≤ ε := by linarith
    have hpi := hprox x v hv (by rw [sub_self, norm_zero]; exact hθ)
      (by rw [sub_self, norm_zero]; linarith [norm_nonneg v]) w
      ⟨hw, by rwa [mem_closedBall, dist_eq_norm]⟩
    have e1 : w - u = (w - x) - (v + d) := by rw [hd, hū]; abel
    have e2 : x - u = -(v + d) := by rw [hd, hū]; abel
    have hsq : ‖w - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwu 2
    rw [e1, e2, norm_neg, norm_sub_sq_real, inner_add_right, real_inner_comm v] at hsq
    have h1 : ⟪w - x, d⟫_ℝ ≤ ‖w - x‖ * ‖d‖ := real_inner_le_norm _ _
    have h4 : (1 - κ) * ‖w - x‖ ^ 2 ≤ 2 * ‖d‖ * ‖w - x‖ := by nlinarith
    rcases eq_or_lt_of_le (norm_nonneg (w - x)) with h0 | hpos
    · rw [← h0, mul_zero]; positivity
    · have h5 : ((1 - κ) * ‖w - x‖) * ‖w - x‖ ≤ (2 * ‖d‖) * ‖w - x‖ := by nlinarith
      exact le_of_mul_le_mul_right h5 hpos
  -- nearest points of `u` near `ū` lie within `2m/3` of `x̄`
  have hnear : ∀ u, ‖u - ū‖ < r → ∀ y ∈ projMapping C u, ‖y - x‖ < 2 * m / 3 := by
    intro u hu y hy
    have h := P1 u hu y hy.1 (hy.2 x hx)
    by_contra hcon
    push_neg at hcon
    have : (1 - κ) * (2 * m / 3) ≤ (1 - κ) * ‖y - x‖ := mul_le_mul_of_nonneg_left hcon hκ1.le
    have : 2 * ‖u - ū‖ < 2 * r := by linarith
    rw [hr] at this
    nlinarith
  -- normals at points near `x̄` for `u` near `ū`
  have hnormal : ∀ u y, ‖u - ū‖ + ‖y - x‖ < θ → ‖(u - y) - v‖ < θ := by
    intro u y h
    calc ‖(u - y) - v‖ = ‖(u - ū) - (y - x)‖ := by rw [hū]; congr 1; abel
      _ ≤ ‖u - ū‖ + ‖y - x‖ := norm_sub_le _ _
      _ < θ := h
  refine ⟨r, hr0, P1, fun u y hu hy ↦ ⟨fun hP ↦ ?_, fun hN ↦ ?_⟩, ?_⟩
  · exact regularNormalCone_subset_normalCone C y (sub_mem_regularNormalCone_of_mem_projMapping hP)
  · -- (P2) normals near `v̄` at points near `x̄` give nearest points
    have hyC : y ∈ C := hN.1
    refine ⟨hyC, fun w hw ↦ ?_⟩
    by_cases hwb : w ∈ closedBall x ε
    · have hpi := hprox y _ hN (hnormal u y (by linarith)) (by linarith) w ⟨hw, hwb⟩
      have e1 : w - u = (w - y) - (u - y) := by abel
      have h2 : ‖y - u‖ ^ 2 ≤ ‖w - u‖ ^ 2 := by
        have e2 := norm_sub_sq_real (w - y) (u - y)
        rw [norm_sub_rev y u, e1, e2, real_inner_comm]
        nlinarith [sq_nonneg ‖w - y‖]
      exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.1 h2
    · rw [mem_closedBall, dist_eq_norm, not_le] at hwb
      have h1 := hux u
      calc ‖y - u‖ ≤ ‖y - x‖ + ‖x - u‖ := by
            calc ‖y - u‖ = ‖(y - x) + (x - u)‖ := by congr 1; abel
              _ ≤ _ := norm_add_le _ _
        _ ≤ ‖w - x‖ - ‖u - x‖ := by rw [norm_sub_rev x u]; linarith
        _ ≤ ‖w - u‖ := by
            have := norm_sub_le (w - u) (x - u)
            rw [show w - u - (x - u) = w - x by abel, norm_sub_rev x u] at this
            linarith
  · -- (P3) the Lipschitz estimate
    intro u₁ u₂ hu₁ hu₂ y₁ hy₁ y₂ hy₂
    have hy₁x := hnear u₁ hu₁ y₁ hy₁
    have hy₂x := hnear u₂ hu₂ y₂ hy₂
    have hN₁ := regularNormalCone_subset_normalCone C y₁
      (sub_mem_regularNormalCone_of_mem_projMapping hy₁)
    have hN₂ := regularNormalCone_subset_normalCone C y₂
      (sub_mem_regularNormalCone_of_mem_projMapping hy₂)
    have hb₁ : y₁ ∈ C ∩ closedBall x ε := ⟨hy₁.1, by rw [mem_closedBall, dist_eq_norm]; linarith⟩
    have hb₂ : y₂ ∈ C ∩ closedBall x ε := ⟨hy₂.1, by rw [mem_closedBall, dist_eq_norm]; linarith⟩
    have i1 := hprox y₁ _ hN₁ (hnormal u₁ y₁ (by linarith)) (by linarith) y₂ hb₂
    have i2 := hprox y₂ _ hN₂ (hnormal u₂ y₂ (by linarith)) (by linarith) y₁ hb₁
    set D := y₁ - y₂ with hD
    have eD : y₂ - y₁ = -D := by rw [hD]; abel
    rw [eD, inner_neg_right, norm_neg] at i1
    have e : u₁ - u₂ = (u₁ - y₁) - (u₂ - y₂) + D := by rw [hD]; abel
    have hkey : ‖D‖ ^ 2 - κ * ‖D‖ ^ 2 ≤ ⟪u₁ - u₂, D⟫_ℝ := by
      rw [e, inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
      linarith only [i1, i2]
    have hle : ⟪u₁ - u₂, D⟫_ℝ ≤ ‖u₁ - u₂‖ * ‖D‖ := real_inner_le_norm _ _
    rcases eq_or_lt_of_le (norm_nonneg D) with h0 | hpos
    · rw [← h0, mul_zero]; positivity
    · have h7 : ((1 - κ) * ‖D‖) * ‖D‖ ≤ ‖u₁ - u₂‖ * ‖D‖ := by nlinarith only [hkey, hle]
      exact le_of_mul_le_mul_right h7 hpos

/-- Normal cones are cones, so the inequality of prox-regularity at `x̄` for `v̄` with constants
`ε, ρ` improves near `v̄`: if `‖v̄‖ ≤ ε` and `ρ‖v̄‖ < ‖v̄‖ + ε`, there are `θ > 0` and
`0 ≤ κ < 1` with `⟪v', x' - y⟫ ≤ κ/2‖x' - y‖²` for `x' ∈ C ∩ IB(x̄, ε)` whenever `v' ∈ N_C(y)`,
`‖v' - v̄‖ < θ` and `‖y - x̄‖ < ε`.  Apply the given inequality to `cv'` with
`c = (‖v̄‖ + ε)/(‖v̄‖ + θ) ≥ 1`, for which `‖cv' - v̄‖ < ε`; then `κ = ρ/c`. -/
theorem exists_proxRegular_constant_lt_one {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hvε : ‖v‖ ≤ ε)
    (hρv : ρ * ‖v‖ < ‖v‖ + ε)
    (hprox : ∀ y v', v' ∈ normalCone C y → ‖v' - v‖ < ε → ‖y - x‖ < ε →
      ∀ x' ∈ C ∩ closedBall x ε, ⟪v', x' - y⟫_ℝ ≤ ρ / 2 * ‖x' - y‖ ^ 2) :
    ∃ θ > 0, ∃ κ, 0 ≤ κ ∧ κ < 1 ∧
      ∀ y v', v' ∈ normalCone C y → ‖v' - v‖ < θ → ‖y - x‖ < ε →
        ∀ x' ∈ C ∩ closedBall x ε, ⟪v', x' - y⟫_ℝ ≤ κ / 2 * ‖x' - y‖ ^ 2 := by
  set a := ‖v‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg v
  set g := a + ε - ρ * a with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set θ := g / (2 * (ρ + 1)) with hθ
  have hθ0 : 0 < θ := div_pos hg0 (by positivity)
  have hρθ : ρ * θ ≤ g / 2 := by
    rw [hθ, mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  have hθε : θ ≤ ε := by
    have : θ ≤ g / 2 := by
      rw [hθ]
      apply div_le_div_of_nonneg_left hg0.le two_pos
      linarith
    nlinarith
  have hθa : 0 < a + θ := by linarith
  set c := (a + ε) / (a + θ) with hc
  have hc0 : 0 < c := div_pos (by nlinarith [mul_nonneg hρ ha0]) hθa
  have hc1 : 1 ≤ c := by rw [hc, le_div_iff₀ hθa]; linarith
  have hcθ : c * (a + θ) = a + ε := by rw [hc]; field_simp
  refine ⟨θ, hθ0, ρ / c, div_nonneg hρ hc0.le, ?_, fun y v' hv' hvv hy x' hx' ↦ ?_⟩
  · rw [div_lt_one hc0, hc, lt_div_iff₀ hθa]
    nlinarith
  · have hcv : c • v' ∈ normalCone C y := (isCone_normalCone hv'.1).2 hv' hc0
    have hclose : ‖c • v' - v‖ < ε := by
      have e : c • v' - v = c • (v' - v) + (c - 1) • v := by
        rw [smul_sub, sub_smul, one_smul]; abel
      calc ‖c • v' - v‖ ≤ ‖c • (v' - v)‖ + ‖(c - 1) • v‖ := by rw [e]; exact norm_add_le _ _
        _ = c * ‖v' - v‖ + (c - 1) * a := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg hc0.le,
              Real.norm_of_nonneg (by linarith)]
        _ < c * θ + (c - 1) * a := by gcongr
        _ = ε := by linarith
    have h := hprox y _ hcv hclose hy x' hx'
    rw [real_inner_smul_left] at h
    have h' : ⟪v', x' - y⟫_ℝ = c⁻¹ * (c * ⟪v', x' - y⟫_ℝ) := by field_simp
    rw [h', div_eq_mul_inv ρ c]
    calc c⁻¹ * (c * ⟪v', x' - y⟫_ℝ) ≤ c⁻¹ * (ρ / 2 * ‖x' - y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hc0.le)
      _ = ρ * c⁻¹ / 2 * ‖x' - y‖ ^ 2 := by ring

omit [InnerProductSpace ℝ E] in
/-- Near `x̄ ∈ C`, nearest points in `C` and in `C ∩ V` agree when `V ⊇ int IB(x̄, r)`: for
`‖u - x̄‖ < r/3` both lie in `int IB(x̄, r)`. -/
theorem projMapping_inter_eq_of_ball_subset {V : Set E} {r : ℝ} (hx : x ∈ C)
    (hV : ball x r ⊆ V) {u : E} (hu : ‖u - x‖ < r / 3) :
    projMapping (C ∩ V) u = projMapping C u := by
  have hr : 0 < r := by linarith [norm_nonneg (u - x)]
  have hxV : x ∈ C ∩ V := ⟨hx, hV (mem_ball_self hr)⟩
  ext y
  constructor
  · rintro ⟨hy, hmin⟩
    refine ⟨hy.1, fun w' hw' ↦ ?_⟩
    by_cases hw'V : w' ∈ V
    · exact hmin w' ⟨hw', hw'V⟩
    · have h1 : r ≤ ‖w' - x‖ := by
        by_contra hlt
        push_neg at hlt
        exact hw'V (hV (by rwa [mem_ball, dist_eq_norm]))
      have h2 : ‖y - u‖ ≤ ‖x - u‖ := hmin x hxV
      have h3 : ‖w' - x‖ ≤ ‖w' - u‖ + ‖u - x‖ := by
        calc ‖w' - x‖ = ‖(w' - u) + (u - x)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      rw [norm_sub_rev x u] at h2
      linarith
  · rintro ⟨hy, hmin⟩
    have h2 : ‖y - u‖ ≤ ‖x - u‖ := hmin x hx
    have h3 : ‖y - x‖ ≤ ‖y - u‖ + ‖u - x‖ := by
      calc ‖y - x‖ = ‖(y - u) + (u - x)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev x u] at h2
    have hyV : y ∈ V := hV (by rw [mem_ball, dist_eq_norm]; linarith)
    exact ⟨⟨hy, hyV⟩, fun w' hw' ↦ hmin w' hw'.1⟩

omit [InnerProductSpace ℝ E] in
/-- If `C` is locally closed at `x̄`, then `C ∩ IB(x̄, δ)` is closed for some `δ > 0`. -/
theorem IsLocallyClosedAt.exists_isClosed_inter_closedBall (h : IsLocallyClosedAt C x) :
    ∃ δ > 0, IsClosed (C ∩ closedBall x δ) := by
  obtain ⟨V, hV, -, hCV⟩ := h
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨r / 2, half_pos hr, ?_⟩
  have heq : C ∩ closedBall x (r / 2) = (C ∩ V) ∩ closedBall x (r / 2) := by
    ext y
    constructor
    · rintro ⟨hy, hyb⟩
      exact ⟨⟨hy, hball (closedBall_subset_ball (half_lt_self hr) hyb)⟩, hyb⟩
    · rintro ⟨⟨hy, -⟩, hyb⟩
      exact ⟨hy, hyb⟩
  rw [heq]
  exact hCV.inter isClosed_closedBall

omit [InnerProductSpace ℝ E] in
/-- `C` is locally closed at `x̄` exactly when `C ∩ IB(x̄, δ)` is closed for some `δ > 0`. -/
theorem isLocallyClosedAt_iff_exists_isClosed_inter_closedBall :
    IsLocallyClosedAt C x ↔ ∃ δ > 0, IsClosed (C ∩ closedBall x δ) :=
  ⟨IsLocallyClosedAt.exists_isClosed_inter_closedBall, fun ⟨δ, hδ, h⟩ ↦
    ⟨closedBall x δ, closedBall_mem_nhds x hδ, isClosed_closedBall, h⟩⟩

omit [InnerProductSpace ℝ E] in
/-- If `C` is locally closed at `x̄`, then `gph P_C` is locally closed at `(u, x̄)` for every `u`:
for a closed neighborhood `V` of `x̄` with `C ∩ V` closed, `gph P_C ∩ (E × V)` is closed. -/
theorem isLocallyClosedAt_svGraph_projMapping (h : IsLocallyClosedAt C x) (u : E) :
    IsLocallyClosedAt (svGraph (projMapping C)) (u, x) := by
  obtain ⟨V, hV, hVc, hCV⟩ := h
  refine ⟨univ ×ˢ V, prod_mem_nhds univ_mem hV, isClosed_univ.prod hVc, ?_⟩
  have heq : svGraph (projMapping C) ∩ univ ×ˢ V =
      {p : E × E | p.2 ∈ C ∩ V} ∩ ⋂ w' ∈ C, {p : E × E | ‖p.2 - p.1‖ ≤ ‖w' - p.1‖} := by
    rw [svGraph_projMapping]
    ext p
    simp only [mem_inter_iff, mem_setOf_eq, mem_iInter, mem_prod, mem_univ, true_and]
    tauto
  rw [heq]
  exact (hCV.preimage continuous_snd).inter
    (isClosed_biInter fun w' _ ↦ isClosed_le (by fun_prop) (by fun_prop))

omit [InnerProductSpace ℝ E] in
/-- Nearest points to `u` exist when `x̄ ∈ C`, `C ∩ IB(x̄, δ)` is closed, and every point of `C`
at least as close to `u` as `x̄` lies in `IB(x̄, δ)`: a nearest point to `u` in `C ∩ IB(x̄, δ)` is
nearest in `C`. -/
theorem projMapping_nonempty_of_isClosed_inter_closedBall [ProperSpace E] {δ : ℝ}
    (hCδ : IsClosed (C ∩ closedBall x δ)) (hx : x ∈ C) {u : E}
    (hcand : ∀ w ∈ C, ‖w - u‖ ≤ ‖x - u‖ → ‖w - x‖ ≤ δ) :
    (projMapping C u).Nonempty := by
  have hxδ : x ∈ C ∩ closedBall x δ :=
    ⟨hx, by rw [mem_closedBall, dist_eq_norm]; exact hcand x hx le_rfl⟩
  obtain ⟨y, hy, hmin⟩ := projMapping_nonempty hCδ ⟨x, hxδ⟩ u
  refine ⟨y, hy.1, fun w hw ↦ ?_⟩
  by_cases hwδ : ‖w - x‖ ≤ δ
  · exact hmin w ⟨hw, by rwa [mem_closedBall, dist_eq_norm]⟩
  · have h1 : ‖x - u‖ < ‖w - u‖ := by
      by_contra hcon
      exact hwδ (hcand w hw (not_lt.1 hcon))
    exact (hmin x hxδ).trans h1.le

end Localization

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x v : E}

/-- Theorem 13.40 for `f = δ_C`: if `C` is prox-regular at `x̄` for `v̄`, then `N_C` is
proto-differentiable at `x̄` for `v̄` if and only if `δ_C` is twice epi-differentiable at `x̄`
for `v̄`, and then `DN_C(x̄ ∣ v̄) = ∂[½d²δ_C(x̄ ∣ v̄)]`. -/
theorem IsProxRegularSetAt.isProtoDifferentiableAt_normalCone_iff
    (hpr : IsProxRegularSetAt C x v) :
    (IsProtoDifferentiableAt (normalCone C) x v ↔
      TwiceEpiDifferentiableAt (indicatorVA C) x v) ∧
    (TwiceEpiDifferentiableAt (indicatorVA C) x v →
      graphicalDerivative (normalCone C) x v =
        subdifferential (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (indicatorVA C) x v w))
    := by
  have hv : v ∈ normalCone C x := hpr.2.1
  have hx : x ∈ C := hv.1
  have hsub : subdifferential (indicatorVA C) = normalCone C :=
    funext (subdifferential_indicatorVA C)
  have hf : IsProxRegularAt (indicatorVA C) x v := (isProxRegularAt_indicatorVA_iff hx).2 hpr
  have hsc : IsSubdifferentiallyContinuousAt (indicatorVA C) x v :=
    isSubdifferentiallyContinuousAtPoint_indicatorVA hx v (by rw [hsub]; exact hv)
  obtain ⟨h40, -, -⟩ := proto_differentiability_of_subgradient_mappings hf
  obtain ⟨had, hform⟩ := h40 hsc
  rw [hsub] at had hform
  exact ⟨had, hform⟩

/-- The conclusions of Corollary 13.43 at `ū = x̄ + λv̄` from a localization of `P_C` there, for `C`
locally closed at `x̄`: if nearest points to `u` exist for `u` near `ū`, `y ∈ P_C(u)` exactly when
`u - y ∈ N_C(y)` near `(ū, x̄)`, and `‖y₁ - y₂‖ ≤ L‖u₁ - u₂‖` for `yᵢ ∈ P_C(uᵢ)`, then
`P_C(ū) = {x̄}`, `P_C` is single-valued around `ū` with the Aubin property at `ū` for `x̄`,
`DP_C(ū) = [I + λDN_C(x̄ ∣ v̄)]⁻¹`, `N_C` is proto-differentiable at `x̄` for `v̄` exactly when
`P_C` is proto-differentiable at `ū` for `x̄`, and this is semidifferentiability of `P_C` at
`ū`. -/
theorem normal_cone_projection_conclusions_of_isLocallyClosedAt (hlc : IsLocallyClosedAt C x)
    (hv : v ∈ normalCone C x) {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) {L : ℝ≥0}
    (hne : ∀ u, ‖u - (x + lam • v)‖ < r → (projMapping C u).Nonempty)
    (P2 : ∀ u y, ‖u - (x + lam • v)‖ < r → ‖y - x‖ < r →
      (y ∈ projMapping C u ↔ u - y ∈ normalCone C y))
    (P3 : ∀ u₁ u₂, ‖u₁ - (x + lam • v)‖ < r → ‖u₂ - (x + lam • v)‖ < r →
      ∀ y₁ ∈ projMapping C u₁, ∀ y₂ ∈ projMapping C u₂, ‖y₁ - y₂‖ ≤ L * ‖u₁ - u₂‖) :
    projMapping C (x + lam • v) = {x} ∧
      (∀ᶠ u in 𝓝 (x + lam • v), ∃ p, projMapping C u = {p}) ∧
      HasAubinPropertyAt (projMapping C) (x + lam • v) x ∧
      graphicalDerivative (projMapping C) (x + lam • v) x =
        svResolvent (graphicalDerivative (normalCone C) x v) lam ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        IsProtoDifferentiableAt (projMapping C) (x + lam • v) x) ∧
      (IsProtoDifferentiableAt (projMapping C) (x + lam • v) x ↔
        ∃ H, HasMappingSemiderivative (projMapping C) (x + lam • v) x H) := by
  have hx : x ∈ C := hv.1
  set ū := x + lam • v with hū
  have hlamv : ū - x = lam • v := by rw [hū]; abel
  have hxū : x ∈ projMapping C ū :=
    (P2 ū x (by simpa using hr) (by simpa using hr)).2
      (by rw [hlamv]; exact (isCone_normalCone hx).2 hv hlam)
  have hsingle : ∀ u, ‖u - ū‖ < r → ∃ p, projMapping C u = {p} := by
    intro u hu
    obtain ⟨p, hp⟩ := hne u hu
    refine ⟨p, Set.eq_singleton_iff_unique_mem.2 ⟨hp, fun y hy ↦ ?_⟩⟩
    have := P3 u u hu hu y hy p hp
    rw [sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hPū : projMapping C ū = {x} := by
    obtain ⟨p, hp⟩ := hsingle ū (by simpa using hr)
    rw [hp] at hxū ⊢
    rw [mem_singleton_iff.1 hxū]
  -- the Aubin property
  have haub : HasAubinPropertyAt (projMapping C) ū x := by
    refine ⟨mem_univ _, hxū, isLocallyClosedAt_svGraph_projMapping hlc ū, L,
      ball ū r, ball_mem_nhds ū hr, univ, univ_mem, fun u₁ hu₁ u₂ hu₂ y₁ hy₁ ↦ ?_⟩
    rw [mem_inter_iff, mem_ball, dist_eq_norm] at hu₁ hu₂
    obtain ⟨y₂, hy₂⟩ := hne u₂ hu₂.2
    refine ⟨y₂, hy₂, ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    exact P3 u₁ u₂ hu₁.2 hu₂.2 y₁ hy₁.1 y₂ hy₂
  -- the graph of `P_C` near `(ū, x̄)` is that of `(I + λN_C)⁻¹`
  have hagree : ∀ᶠ p in 𝓝 (ū, x),
      p.2 ∈ projMapping C p.1 ↔ p.2 ∈ svResolvent (normalCone C) lam p.1 := by
    filter_upwards [ball_mem_nhds (ū, x) hr] with p hp
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hp
    rw [P2 p.1 p.2 hp.1 hp.2, mem_svResolvent_normalCone_iff hlam]
  obtain ⟨hcongr, hD⟩ := isProtoDifferentiableAt_congr_of_eventually hagree
  have hres := isProtoDifferentiableAt_svResolvent_iff (normalCone C) hlam.ne' hv
  refine ⟨hPū, ?_, haub, ?_, ?_, ?_⟩
  · filter_upwards [ball_mem_nhds ū hr] with u hu
    rw [mem_ball, dist_eq_norm] at hu
    exact hsingle u hu
  · rw [hD]
    exact graphicalDerivative_svResolvent (normalCone C) hlam.ne' x v
  · rw [hcongr]
    exact hres.symm
  · constructor
    · intro h
      exact ⟨_, (hasMappingSemiderivative_iff_proto_of_aubin haub).2 h⟩
    · rintro ⟨H, hH⟩
      exact hH.protoDerivative.1

/-- The conclusions of Corollary 13.43 at `ū = x̄ + λv̄` that follow from the localization of `P_C`
there (`projection_localization_of_constants`): `P_C(ū) = {x̄}`, `P_C` is single-valued around `ū`
with the Aubin property at `ū` for `x̄`, `DP_C(ū) = [I + λDN_C(x̄ ∣ v̄)]⁻¹`, `N_C` is
proto-differentiable at `x̄` for `v̄` exactly when `P_C` is proto-differentiable at `ū` for `x̄`,
and this is semidifferentiability of `P_C` at `ū`.  This is
`normal_cone_projection_conclusions_of_isLocallyClosedAt` for closed `C`. -/
theorem normal_cone_projection_conclusions (hC : IsClosed C) (hv : v ∈ normalCone C x)
    {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (P2 : ∀ u y, ‖u - (x + lam • v)‖ < r → ‖y - x‖ < r →
      (y ∈ projMapping C u ↔ u - y ∈ normalCone C y))
    (P3 : ∀ u₁ u₂, ‖u₁ - (x + lam • v)‖ < r → ‖u₂ - (x + lam • v)‖ < r →
      ∀ y₁ ∈ projMapping C u₁, ∀ y₂ ∈ projMapping C u₂, ‖y₁ - y₂‖ ≤ 2 * ‖u₁ - u₂‖) :
    projMapping C (x + lam • v) = {x} ∧
      (∀ᶠ u in 𝓝 (x + lam • v), ∃ p, projMapping C u = {p}) ∧
      HasAubinPropertyAt (projMapping C) (x + lam • v) x ∧
      graphicalDerivative (projMapping C) (x + lam • v) x =
        svResolvent (graphicalDerivative (normalCone C) x v) lam ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        IsProtoDifferentiableAt (projMapping C) (x + lam • v) x) ∧
      (IsProtoDifferentiableAt (projMapping C) (x + lam • v) x ↔
        ∃ H, HasMappingSemiderivative (projMapping C) (x + lam • v) x H) :=
  normal_cone_projection_conclusions_of_isLocallyClosedAt (IsClosed.isLocallyClosedAt hC x) hv hlam
    hr (L := 2) (fun u _ ↦ projMapping_nonempty hC ⟨x, hv.1⟩ u) P2 (by simpa using P3)

/-- **Corollary 13.43**, adapted, for prox-regular `C`: for all sufficiently small `λ > 0` and
`ū = x̄ + λv̄`, `P_C(ū) = {x̄}`, `P_C` is single-valued around `ū` with the Aubin property at `ū`
for `x̄`, `DP_C(ū) = [I + λDN_C(x̄ ∣ v̄)]⁻¹` (`svResolvent`), and the following are equivalent:
(a) `N_C` is proto-differentiable at `x̄` for `v̄`; (b) `P_C` is proto-differentiable at `ū` for
`x̄`; (c) `P_C` is semidifferentiable at `ū` (for `x̄`); (d) `δ_C` is twice epi-differentiable at
`x̄` for `v̄`; and then `DN_C(x̄ ∣ v̄) = ∂[½d²δ_C(x̄ ∣ v̄)]`. -/
theorem normal_cone_mappings_and_projections_of_proxRegular (hC : IsClosed C)
    (hpr : IsProxRegularSetAt C x v) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      projMapping C (x + lam • v) = {x} ∧
      (∀ᶠ u in 𝓝 (x + lam • v), ∃ p, projMapping C u = {p}) ∧
      HasAubinPropertyAt (projMapping C) (x + lam • v) x ∧
      graphicalDerivative (projMapping C) (x + lam • v) x =
        svResolvent (graphicalDerivative (normalCone C) x v) lam ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        IsProtoDifferentiableAt (projMapping C) (x + lam • v) x) ∧
      (IsProtoDifferentiableAt (projMapping C) (x + lam • v) x ↔
        ∃ H, HasMappingSemiderivative (projMapping C) (x + lam • v) x H) ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        TwiceEpiDifferentiableAt (indicatorVA C) x v) ∧
      (TwiceEpiDifferentiableAt (indicatorVA C) x v →
        graphicalDerivative (normalCone C) x v =
          subdifferential
            (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (indicatorVA C) x v w)) := by
  obtain ⟨had, hform⟩ := hpr.isProtoDifferentiableAt_normalCone_iff
  obtain ⟨lam₀, hlam₀, hloc⟩ := hpr.projection_localization
  refine ⟨lam₀, hlam₀, fun lam hlam hlt ↦ ?_⟩
  obtain ⟨r, hr, -, P2, P3⟩ := hloc lam hlam hlt
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := normal_cone_projection_conclusions hC hpr.2.1 hlam hr P2 P3
  exact ⟨h1, h2, h3, h4, h5, h6, had, hform⟩

/-- **Corollary 13.43 at the printed base point `ū = x̄ + v̄`**, with closedness only at `x̄`: if
`C` is locally closed at `x̄`, `v̄ ∈ N_C(x̄)`, and the inequality of `IsProxRegularSetAt` holds at
`x̄` for `v̄` with constants `ε` and `ρ ≥ 0` such that `2‖v̄‖ < ε` and `ρ‖v̄‖ < ‖v̄‖ + ε`, then
`P_C(x̄ + v̄) = {x̄}`, `P_C` is single-valued around `x̄ + v̄` with the Aubin property,
`DP_C(x̄ + v̄) = [I + DN_C(x̄ ∣ v̄)]⁻¹`, (a) ⟺ (b) ⟺ (c) ⟺ (d), and then
`DN_C(x̄ ∣ v̄) = ∂[½d²δ_C(x̄ ∣ v̄)]`.  Neither strict inequality can be relaxed
(`NormalConeProjectionsCounterexample.normal_cone_projection_radius_counterexample`,
`NormalConeProjectionsCounterexample.normal_cone_projection_curvature_counterexample`). -/
theorem normal_cone_mappings_and_projections_of_constants (hlc : IsLocallyClosedAt C x)
    (hv : v ∈ normalCone C x) {ε ρ : ℝ} (hρ : 0 ≤ ρ) (hvε : 2 * ‖v‖ < ε)
    (hρv : ρ * ‖v‖ < ‖v‖ + ε)
    (hprox : ∀ y v', v' ∈ normalCone C y → ‖v' - v‖ < ε → ‖y - x‖ < ε →
      ∀ x' ∈ C ∩ closedBall x ε, ⟪v', x' - y⟫_ℝ ≤ ρ / 2 * ‖x' - y‖ ^ 2) :
    projMapping C (x + v) = {x} ∧
      (∀ᶠ u in 𝓝 (x + v), ∃ p, projMapping C u = {p}) ∧
      HasAubinPropertyAt (projMapping C) (x + v) x ∧
      graphicalDerivative (projMapping C) (x + v) x =
        svResolvent (graphicalDerivative (normalCone C) x v) 1 ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        IsProtoDifferentiableAt (projMapping C) (x + v) x) ∧
      (IsProtoDifferentiableAt (projMapping C) (x + v) x ↔
        ∃ H, HasMappingSemiderivative (projMapping C) (x + v) x H) ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        TwiceEpiDifferentiableAt (indicatorVA C) x v) ∧
      (TwiceEpiDifferentiableAt (indicatorVA C) x v →
        graphicalDerivative (normalCone C) x v =
          subdifferential
            (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (indicatorVA C) x v w)) := by
  have hε : 0 < ε := by linarith [norm_nonneg v]
  have hpr : IsProxRegularSetAt C x v := ⟨hlc, hv, ε, hε, ρ, hρ, hprox⟩
  obtain ⟨had, hform⟩ := hpr.isProtoDifferentiableAt_normalCone_iff
  obtain ⟨θ, hθ, κ, hκ0, hκ, hprox'⟩ :=
    exists_proxRegular_constant_lt_one hρ (by linarith [norm_nonneg v]) hρv hprox
  obtain ⟨r, hr, P1, P2, P3⟩ := projection_localization_of_lt_one hv hθ hκ0 hκ hvε hprox'
  obtain ⟨δ, hδ, hCδ⟩ := hlc.exists_isClosed_inter_closedBall
  have hκ1 : 0 < 1 - κ := by linarith
  set r' := min r ((1 - κ) * δ / 2) with hr'
  have hr'0 : 0 < r' := lt_min hr (by positivity)
  have hne : ∀ u, ‖u - (x + (1 : ℝ) • v)‖ < r' → (projMapping C u).Nonempty := by
    intro u hu
    rw [one_smul] at hu
    refine projMapping_nonempty_of_isClosed_inter_closedBall hCδ hv.1 fun w hw hwu ↦ ?_
    have h1 := P1 u (lt_of_lt_of_le hu (min_le_left _ _)) w hw hwu
    have h2 : 2 * ‖u - (x + v)‖ ≤ (1 - κ) * δ := by
      have := lt_of_lt_of_le hu (min_le_right _ _)
      linarith
    nlinarith
  set L : ℝ≥0 := ⟨(1 - κ)⁻¹, inv_nonneg.2 hκ1.le⟩ with hL
  have h := normal_cone_projection_conclusions_of_isLocallyClosedAt hlc hv one_pos hr'0 (L := L)
    hne (fun u y hu hy ↦ by
      rw [one_smul] at hu
      exact P2 u y (lt_of_lt_of_le hu (min_le_left _ _)) (lt_of_lt_of_le hy (min_le_left _ _)))
    (fun u₁ u₂ hu₁ hu₂ y₁ hy₁ y₂ hy₂ ↦ by
      rw [one_smul] at hu₁ hu₂
      have := P3 u₁ u₂ (lt_of_lt_of_le hu₁ (min_le_left _ _))
        (lt_of_lt_of_le hu₂ (min_le_left _ _)) y₁ hy₁ y₂ hy₂
      change ‖y₁ - y₂‖ ≤ (1 - κ)⁻¹ * ‖u₁ - u₂‖
      rw [le_inv_mul_iff₀ hκ1]
      exact this)
  simp only [one_smul] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, had, hform⟩

/-- **Corollary 13.43 at the printed base point `ū = x̄ + v̄`** under the constants of
`normal_cone_mappings_and_projections_of_small` (`0 ≤ ρ ≤ 1/2`, `‖v̄‖ ≤ ε/4`), with `C` only locally
closed at `x̄`, as prox-regularity requires, instead of closed.  Closedness of `C ∩ IB(x̄, δ)` for
some `δ > 0` suffices, however small `δ` is
(`isLocallyClosedAt_iff_exists_isClosed_inter_closedBall`).  A case of
`normal_cone_mappings_and_projections_of_constants`. -/
theorem normal_cone_mappings_and_projections_of_small_local (hlc : IsLocallyClosedAt C x)
    (hv : v ∈ normalCone C x) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1 / 2)
    (hvε : ‖v‖ ≤ ε / 4)
    (hprox : ∀ y v', v' ∈ normalCone C y → ‖v' - v‖ < ε → ‖y - x‖ < ε →
      ∀ x' ∈ C ∩ closedBall x ε, ⟪v', x' - y⟫_ℝ ≤ ρ / 2 * ‖x' - y‖ ^ 2) :
    projMapping C (x + v) = {x} ∧
      (∀ᶠ u in 𝓝 (x + v), ∃ p, projMapping C u = {p}) ∧
      HasAubinPropertyAt (projMapping C) (x + v) x ∧
      graphicalDerivative (projMapping C) (x + v) x =
        svResolvent (graphicalDerivative (normalCone C) x v) 1 ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        IsProtoDifferentiableAt (projMapping C) (x + v) x) ∧
      (IsProtoDifferentiableAt (projMapping C) (x + v) x ↔
        ∃ H, HasMappingSemiderivative (projMapping C) (x + v) x H) ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        TwiceEpiDifferentiableAt (indicatorVA C) x v) ∧
      (TwiceEpiDifferentiableAt (indicatorVA C) x v →
        graphicalDerivative (normalCone C) x v =
          subdifferential
            (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (indicatorVA C) x v w)) :=
  normal_cone_mappings_and_projections_of_constants hlc hv hρ (by linarith)
    (by nlinarith [norm_nonneg v]) hprox

/-- **Corollary 13.43 at the printed base point `ū = x̄ + v̄`**, for closed `C` and a normal `v̄`
that is small relative to the constants of prox-regularity: if `v̄ ∈ N_C(x̄)` and the inequality of
`IsProxRegularSetAt` holds at `x̄` for `v̄` with constants `ε > 0` and `0 ≤ ρ ≤ 1/2`, and
`‖v̄‖ ≤ ε/4`, then the conclusions of `normal_cone_mappings_and_projections_of_proxRegular` hold
with `λ = 1`: `P_C(x̄ + v̄) = {x̄}`, `P_C` is single-valued around `x̄ + v̄` with the Aubin
property, `DP_C(x̄ + v̄) = [I + DN_C(x̄ ∣ v̄)]⁻¹`, (a) ⟺ (b) ⟺ (c) ⟺ (d), and then
`DN_C(x̄ ∣ v̄) = ∂[½d²δ_C(x̄ ∣ v̄)]`.  Closedness of `C` is only needed at `x̄`:
`normal_cone_mappings_and_projections_of_small_local`. -/
theorem normal_cone_mappings_and_projections_of_small (hC : IsClosed C) (hv : v ∈ normalCone C x)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 ≤ ρ) (hρ2 : ρ ≤ 1 / 2) (hvε : ‖v‖ ≤ ε / 4)
    (hprox : ∀ y v', v' ∈ normalCone C y → ‖v' - v‖ < ε → ‖y - x‖ < ε →
      ∀ x' ∈ C ∩ closedBall x ε, ⟪v', x' - y⟫_ℝ ≤ ρ / 2 * ‖x' - y‖ ^ 2) :
    projMapping C (x + v) = {x} ∧
      (∀ᶠ u in 𝓝 (x + v), ∃ p, projMapping C u = {p}) ∧
      HasAubinPropertyAt (projMapping C) (x + v) x ∧
      graphicalDerivative (projMapping C) (x + v) x =
        svResolvent (graphicalDerivative (normalCone C) x v) 1 ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        IsProtoDifferentiableAt (projMapping C) (x + v) x) ∧
      (IsProtoDifferentiableAt (projMapping C) (x + v) x ↔
        ∃ H, HasMappingSemiderivative (projMapping C) (x + v) x H) ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        TwiceEpiDifferentiableAt (indicatorVA C) x v) ∧
      (TwiceEpiDifferentiableAt (indicatorVA C) x v →
        graphicalDerivative (normalCone C) x v =
          subdifferential
            (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (indicatorVA C) x v w)) :=
  normal_cone_mappings_and_projections_of_small_local (IsClosed.isLocallyClosedAt hC x) hv hε hρ hρ2
    hvε hprox

/-- **Corollary 13.43** without closedness of `C`: the conclusions of
`normal_cone_mappings_and_projections_of_proxRegular` for a set that is only prox-regular at `x̄`
for `v̄` (hence locally closed at `x̄`), as in the book.  For a neighborhood `V` of `x̄` with
`C ∩ V` closed, `C ∩ V` has the same normal cones and indicator near `x̄`, and the same projections
near `ū = x̄ + λv̄` for small `λ`. -/
theorem normal_cone_mappings_and_projections_of_proxRegular_local
    (hpr : IsProxRegularSetAt C x v) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      projMapping C (x + lam • v) = {x} ∧
      (∀ᶠ u in 𝓝 (x + lam • v), ∃ p, projMapping C u = {p}) ∧
      HasAubinPropertyAt (projMapping C) (x + lam • v) x ∧
      graphicalDerivative (projMapping C) (x + lam • v) x =
        svResolvent (graphicalDerivative (normalCone C) x v) lam ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        IsProtoDifferentiableAt (projMapping C) (x + lam • v) x) ∧
      (IsProtoDifferentiableAt (projMapping C) (x + lam • v) x ↔
        ∃ H, HasMappingSemiderivative (projMapping C) (x + lam • v) x H) ∧
      (IsProtoDifferentiableAt (normalCone C) x v ↔
        TwiceEpiDifferentiableAt (indicatorVA C) x v) ∧
      (TwiceEpiDifferentiableAt (indicatorVA C) x v →
        graphicalDerivative (normalCone C) x v =
          subdifferential
            (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (indicatorVA C) x v w)) := by
  obtain ⟨V, hV, -, hCV⟩ := hpr.1
  have hx : x ∈ C := hpr.2.1.1
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hV
  have hxC' : x ∈ C ∩ V := ⟨hx, mem_of_mem_nhds hV⟩
  have heqC : C =ᶠ[𝓝 x] (C ∩ V : Set E) := by
    filter_upwards [hV] with y hy
    exact propext ⟨fun hc ↦ ⟨hc, hy⟩, fun hc ↦ hc.1⟩
  have hind : indicatorVA C =ᶠ[𝓝 x] indicatorVA (C ∩ V) := by
    filter_upwards [hV] with y hy
    by_cases hyC : y ∈ C
    · rw [indicatorVA_apply_mem hyC, indicatorVA_apply_mem (show y ∈ C ∩ V from ⟨hyC, hy⟩)]
    · rw [indicatorVA_apply_not_mem hyC,
        indicatorVA_apply_not_mem (fun h : y ∈ C ∩ V ↦ hyC h.1)]
  have hpr' : IsProxRegularSetAt (C ∩ V) x v :=
    (isProxRegularAt_indicatorVA_iff hxC').1
      (IsProxRegularAt.congr_nhds hind.symm ((isProxRegularAt_indicatorVA_iff hx).2 hpr))
  obtain ⟨lam₀, hlam₀, hmain⟩ := normal_cone_mappings_and_projections_of_proxRegular hCV hpr'
  refine ⟨min lam₀ (r / (3 * (‖v‖ + 1))), lt_min hlam₀ (by positivity), fun lam hlam hlt ↦ ?_⟩
  have hlamv : lam * ‖v‖ < r / 3 := by
    have h1 : lam < r / (3 * (‖v‖ + 1)) := lt_of_lt_of_le hlt (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg v]
  have hδ : 0 < r / 3 - lam * ‖v‖ := by linarith
  have hPeq : ∀ u ∈ ball (x + lam • v) (r / 3 - lam * ‖v‖),
      projMapping (C ∩ V) u = projMapping C u := by
    intro u hu
    refine projMapping_inter_eq_of_ball_subset hx hball ?_
    rw [mem_ball, dist_eq_norm] at hu
    calc ‖u - x‖ = ‖(u - (x + lam • v)) + lam • v‖ := by congr 1; abel
      _ ≤ ‖u - (x + lam • v)‖ + ‖lam • v‖ := norm_add_le _ _
      _ = ‖u - (x + lam • v)‖ + lam * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hlam.le]
      _ < r / 3 := by linarith
  have hgraphN : ∀ᶠ p in 𝓝 (x, v), p.2 ∈ normalCone C p.1 ↔ p.2 ∈ normalCone (C ∩ V) p.1 := by
    have hN : ∀ᶠ y in 𝓝 x, normalCone C y = normalCone (C ∩ V) y := by
      filter_upwards [heqC.eventuallyEq_nhds] with y hy
      exact normalCone_congr_nhds hy
    filter_upwards [(continuous_fst.tendsto (x, v)).eventually hN] with p hp
    rw [hp]
  have hgraphP : ∀ᶠ p in 𝓝 (x + lam • v, x),
      p.2 ∈ projMapping C p.1 ↔ p.2 ∈ projMapping (C ∩ V) p.1 := by
    filter_upwards [(continuous_fst.tendsto (x + lam • v, x)).eventually
      (ball_mem_nhds (x + lam • v) hδ)] with p hp
    rw [hPeq p.1 hp]
  obtain ⟨hNproto, hND⟩ := isProtoDifferentiableAt_congr_of_eventually hgraphN
  obtain ⟨hPproto, hPD⟩ := isProtoDifferentiableAt_congr_of_eventually hgraphP
  have hte : TwiceEpiDifferentiableAt (indicatorVA C) x v ↔
      TwiceEpiDifferentiableAt (indicatorVA (C ∩ V)) x v :=
    ⟨fun h ↦ h.congr_nhds hind.symm, fun h ↦ h.congr_nhds hind⟩
  have hd2 : secondSubderivative (indicatorVA C) x v =
      secondSubderivative (indicatorVA (C ∩ V)) x v :=
    funext fun w ↦ secondSubderivative_congr_nhds hind v w
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8⟩ :=
    hmain lam hlam (lt_of_lt_of_le hlt (min_le_left _ _))
  have hself : x + lam • v ∈ ball (x + lam • v) (r / 3 - lam * ‖v‖) := mem_ball_self hδ
  have haub : HasAubinPropertyAt (projMapping C) (x + lam • v) x := by
    obtain ⟨-, hxu', hlc, k, Va, hVa, Wa, hWa, hest⟩ := h3
    have hsame : svGraph (projMapping (C ∩ V)) =ᶠ[𝓝 (x + lam • v, x)] svGraph (projMapping C) := by
      filter_upwards [hgraphP] with p hp
      exact propext hp.symm
    refine ⟨mem_univ _, by rw [← hPeq _ hself]; exact hxu', hlc.congr_nhds hsame, k,
      Va ∩ ball (x + lam • v) (r / 3 - lam * ‖v‖), inter_mem hVa (ball_mem_nhds _ hδ), Wa, hWa,
      fun u₁ hu₁ u₂ hu₂ y₁ hy₁ ↦ ?_⟩
    obtain ⟨z, hz, hdist⟩ := hest u₁ ⟨mem_univ _, hu₁.2.1⟩ u₂ ⟨mem_univ _, hu₂.2.1⟩ y₁
      ⟨by rw [hPeq u₁ hu₁.2.2]; exact hy₁.1, hy₁.2⟩
    exact ⟨z, by rw [← hPeq u₂ hu₂.2.2]; exact hz, hdist⟩
  refine ⟨by rw [← hPeq _ hself]; exact h1, ?_, haub, by rw [hPD, hND]; exact h4,
    hNproto.trans (h5.trans hPproto.symm),
    ⟨fun h ↦ ⟨_, (hasMappingSemiderivative_iff_proto_of_aubin haub).2 h⟩,
      fun ⟨H, hH⟩ ↦ hH.protoDerivative.1⟩,
    hNproto.trans (h7.trans hte.symm), fun h ↦ by rw [hND, hd2]; exact h8 (hte.1 h)⟩
  filter_upwards [h2, ball_mem_nhds (x + lam • v) hδ] with u hu hub
  obtain ⟨p, hp⟩ := hu
  exact ⟨p, by rw [← hPeq u hub]; exact hp⟩

/-- **Corollary 13.43 as printed, for the normal `λv̄`.**  If `C` is prox-regular at `x̄` for `v̄`
(not necessarily closed), then for all sufficiently small `λ > 0` the corollary holds verbatim
for `λv̄` in place of `v̄`: `C` is prox-regular at `x̄` for `λv̄`, and at `ū = x̄ + λv̄`,
`P_C(ū) = {x̄}`, `P_C` is single-valued around `ū` with the Aubin property at `ū` for `x̄`,
`DP_C(ū) = [I + DN_C(x̄ ∣ λv̄)]⁻¹`, (a) `N_C` is proto-differentiable at `x̄` for `λv̄` ⟺ (b) `P_C`
is proto-differentiable at `ū` for `x̄` ⟺ (c) `P_C` is semidifferentiable at `ū` ⟺ (d) `δ_C` is
twice epi-differentiable at `x̄` for `λv̄`, and then `DN_C(x̄ ∣ λv̄) = ∂[½d²δ_C(x̄ ∣ λv̄)]`.
This is `normal_cone_mappings_and_projections_of_proxRegular_local` rewritten with
`DN_C(x̄ ∣ λv̄) = λDN_C(x̄ ∣ v̄)` (`graphicalDerivative_normalCone_smul`), together with
Theorem 13.40 at `λv̄`. -/
theorem normal_cone_mappings_and_projections_scaled (hpr : IsProxRegularSetAt C x v) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      IsProxRegularSetAt C x (lam • v) ∧
      projMapping C (x + lam • v) = {x} ∧
      (∀ᶠ u in 𝓝 (x + lam • v), ∃ p, projMapping C u = {p}) ∧
      HasAubinPropertyAt (projMapping C) (x + lam • v) x ∧
      graphicalDerivative (projMapping C) (x + lam • v) x =
        svResolvent (graphicalDerivative (normalCone C) x (lam • v)) 1 ∧
      (IsProtoDifferentiableAt (normalCone C) x (lam • v) ↔
        IsProtoDifferentiableAt (projMapping C) (x + lam • v) x) ∧
      (IsProtoDifferentiableAt (projMapping C) (x + lam • v) x ↔
        ∃ H, HasMappingSemiderivative (projMapping C) (x + lam • v) x H) ∧
      (IsProtoDifferentiableAt (normalCone C) x (lam • v) ↔
        TwiceEpiDifferentiableAt (indicatorVA C) x (lam • v)) ∧
      (TwiceEpiDifferentiableAt (indicatorVA C) x (lam • v) →
        graphicalDerivative (normalCone C) x (lam • v) =
          subdifferential (fun w ↦
            ((1 / 2 : ℝ) : EReal) * secondSubderivative (indicatorVA C) x (lam • v) w)) := by
  obtain ⟨lam₀, hlam₀, hmain⟩ := normal_cone_mappings_and_projections_of_proxRegular_local hpr
  refine ⟨lam₀, hlam₀, fun lam hlam hlt ↦ ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := hmain lam hlam hlt
  have hprl : IsProxRegularSetAt C x (lam • v) := hpr.smul hlam
  obtain ⟨had, hform⟩ := hprl.isProtoDifferentiableAt_normalCone_iff
  refine ⟨hprl, h1, h2, h3, ?_, ?_, h6, had, hform⟩
  · rw [h4, svResolvent_eq_svResolvent_smul, graphicalDerivative_normalCone_smul hlam]
  · rw [isProtoDifferentiableAt_normalCone_smul_iff hpr.2.1 hlam]
    exact h5

/-- **Corollary 13.43 as printed**, at `ū = x̄ + v̄`, for closed convex `C` and every
`v̄ ∈ N_C(x̄)`: `P_C(ū) = {x̄}`, `P_C` is single-valued with the Aubin property at `ū` for `x̄`,
`DP_C(ū) = [I + DN_C(x̄ ∣ v̄)]⁻¹`, (a) ⟺ (b) ⟺ (c) ⟺ (d), and then
`DN_C(x̄ ∣ v̄) = ∂[½d²δ_C(x̄ ∣ v̄)]`.  Projections onto convex sets are nonexpansive
(`norm_sub_le_of_mem_projMapping`), and `P_C = (I + N_C)⁻¹` (12.64 with `λ = 1`). -/
theorem normal_cone_mappings_and_projections_convex (hC : IsClosed C) (hconv : Convex ℝ C)
    (hv : v ∈ normalCone C x) :
    projMapping C (x + v) = {x} ∧
    (∀ u, ∃ p, projMapping C u = {p}) ∧
    HasAubinPropertyAt (projMapping C) (x + v) x ∧
    graphicalDerivative (projMapping C) (x + v) x =
      svResolvent (graphicalDerivative (normalCone C) x v) 1 ∧
    (IsProtoDifferentiableAt (normalCone C) x v ↔
      IsProtoDifferentiableAt (projMapping C) (x + v) x) ∧
    (IsProtoDifferentiableAt (projMapping C) (x + v) x ↔
      ∃ H, HasMappingSemiderivative (projMapping C) (x + v) x H) ∧
    (IsProtoDifferentiableAt (normalCone C) x v ↔ TwiceEpiDifferentiableAt (indicatorVA C) x v) ∧
    (TwiceEpiDifferentiableAt (indicatorVA C) x v →
      graphicalDerivative (normalCone C) x v =
        subdifferential
          (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (indicatorVA C) x v w)) := by
  have hx : x ∈ C := hv.1
  have hxu : x ∈ projMapping C (x + v) :=
    (mem_normalCone_iff_mem_projMapping_add_of_convex hconv hx).1 hv
  have hsingle : ∀ u, ∃ p, projMapping C u = {p} := by
    intro u
    obtain ⟨p, hp⟩ := projMapping_nonempty hC ⟨x, hx⟩ u
    refine ⟨p, Set.eq_singleton_iff_unique_mem.2 ⟨hp, fun y hy ↦ ?_⟩⟩
    have := norm_sub_le_of_mem_projMapping hconv hy hp
    rw [sub_self, norm_zero] at this
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hPu : projMapping C (x + v) = {x} := by
    obtain ⟨p, hp⟩ := hsingle (x + v)
    rw [hp] at hxu ⊢
    rw [mem_singleton_iff.1 hxu]
  have haub : HasAubinPropertyAt (projMapping C) (x + v) x := by
    refine ⟨mem_univ _, hxu, IsClosed.isLocallyClosedAt (isClosed_svGraph_projMapping hC) _, 1,
      univ, univ_mem, univ, univ_mem, fun u₁ _ u₂ _ y₁ hy₁ ↦ ?_⟩
    obtain ⟨y₂, hy₂⟩ := projMapping_nonempty hC ⟨x, hx⟩ u₂
    refine ⟨y₂, hy₂, ?_⟩
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact norm_sub_le_of_mem_projMapping hconv hy₁.1 hy₂
  obtain ⟨had, hform⟩ :=
    (isProxRegularSetAtPoint_of_convex hconv hC hx v hv).isProtoDifferentiableAt_normalCone_iff
  have hD := graphicalDerivative_svResolvent (normalCone C) one_ne_zero x v
  have hP := isProtoDifferentiableAt_svResolvent_iff (normalCone C) one_ne_zero hv
  rw [one_smul, svResolvent_normalCone_eq_projMapping hconv] at hD hP
  refine ⟨hPu, hsingle, haub, hD, hP.symm, ⟨fun h ↦ ⟨_, (hasMappingSemiderivative_iff_proto_of_aubin
    haub).2 h⟩, fun ⟨H, hH⟩ ↦ hH.protoDerivative.1⟩, had, hform⟩

end Main

section Amenable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x v : E}

/-- **Corollary 13.43** (normal cone mappings and projections), adapted: the conclusions of
`normal_cone_mappings_and_projections_of_proxRegular` for `C` closed and prox-regular at `x̄` for
`v̄`, at `ū = x̄ + λv̄` for all sufficiently small `λ > 0`; when `C` is fully amenable at `x̄`,
`C` is prox-regular at `x̄` for every `v̄ ∈ N_C(x̄)` and (a)-(d) hold.  The proof takes
`λ₀ ≤ 1/2`, so the book's `ū = x̄ + v̄` (`λ = 1`) is not reached; it is covered for closed convex
`C` (`normal_cone_mappings_and_projections_convex`) and when the constants of prox-regularity
satisfy `2‖v̄‖ < ε` and `ρ‖v̄‖ < ‖v̄‖ + ε`, with `C` locally closed at `x̄`
(`normal_cone_mappings_and_projections_of_constants`), and fails in general
(`NormalConeProjectionsCounterexample.normal_cone_projection_counterexample`,
`NormalConeProjectionsCircle.normal_cone_projection_circle_counterexample`); the corollary holds
as printed for the normal `λv̄` (`normal_cone_mappings_and_projections_scaled`).  Closedness of
`C` is not needed: `normal_cone_mappings_and_projections_local`. -/
theorem normal_cone_mappings_and_projections (hC : IsClosed C) (hv : v ∈ normalCone C x) :
    (IsProxRegularSetAt C x v →
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        projMapping C (x + lam • v) = {x} ∧
        (∀ᶠ u in 𝓝 (x + lam • v), ∃ p, projMapping C u = {p}) ∧
        HasAubinPropertyAt (projMapping C) (x + lam • v) x ∧
        graphicalDerivative (projMapping C) (x + lam • v) x =
          svResolvent (graphicalDerivative (normalCone C) x v) lam ∧
        (IsProtoDifferentiableAt (normalCone C) x v ↔
          IsProtoDifferentiableAt (projMapping C) (x + lam • v) x) ∧
        (IsProtoDifferentiableAt (projMapping C) (x + lam • v) x ↔
          ∃ H, HasMappingSemiderivative (projMapping C) (x + lam • v) x H) ∧
        (IsProtoDifferentiableAt (normalCone C) x v ↔
          TwiceEpiDifferentiableAt (indicatorVA C) x v) ∧
        (TwiceEpiDifferentiableAt (indicatorVA C) x v →
          graphicalDerivative (normalCone C) x v =
            subdifferential
              (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (indicatorVA C) x v w))) ∧
    (SetFullyAmenableAt C x →
      IsProxRegularSetAt C x v ∧ TwiceEpiDifferentiableAt (indicatorVA C) x v) := by
  refine ⟨normal_cone_mappings_and_projections_of_proxRegular hC, fun hA ↦ ?_⟩
  have hx : x ∈ C := hv.1
  have hfa : FullyAmenableAt (indicatorVA C) x := setFullyAmenableAt_iff_indicator.1 hA
  have hv' : v ∈ subdifferential (indicatorVA C) x := by rw [subdifferential_indicatorVA]; exact hv
  refine ⟨(isProxRegularAt_indicatorVA_iff hx).1
    ((prox_regularity_from_amenability hfa.stronglyAmenableAt).1.1 v hv'),
    (hfa.properlyTwiceEpiDifferentiableAt hv').1⟩

/-- **Corollary 13.43** (normal cone mappings and projections), adapted, for `C` prox-regular at
`x̄` for `v̄` without assuming `C` closed, as in the book: the conclusions of
`normal_cone_mappings_and_projections_of_proxRegular_local` at `ū = x̄ + λv̄` for all sufficiently
small `λ > 0`; when `C` is fully amenable at `x̄`, `C` is prox-regular at `x̄` for every
`v̄ ∈ N_C(x̄)` and (a)-(d) hold. -/
theorem normal_cone_mappings_and_projections_local (hv : v ∈ normalCone C x) :
    (IsProxRegularSetAt C x v →
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        projMapping C (x + lam • v) = {x} ∧
        (∀ᶠ u in 𝓝 (x + lam • v), ∃ p, projMapping C u = {p}) ∧
        HasAubinPropertyAt (projMapping C) (x + lam • v) x ∧
        graphicalDerivative (projMapping C) (x + lam • v) x =
          svResolvent (graphicalDerivative (normalCone C) x v) lam ∧
        (IsProtoDifferentiableAt (normalCone C) x v ↔
          IsProtoDifferentiableAt (projMapping C) (x + lam • v) x) ∧
        (IsProtoDifferentiableAt (projMapping C) (x + lam • v) x ↔
          ∃ H, HasMappingSemiderivative (projMapping C) (x + lam • v) x H) ∧
        (IsProtoDifferentiableAt (normalCone C) x v ↔
          TwiceEpiDifferentiableAt (indicatorVA C) x v) ∧
        (TwiceEpiDifferentiableAt (indicatorVA C) x v →
          graphicalDerivative (normalCone C) x v =
            subdifferential
              (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative (indicatorVA C) x v w))) ∧
    (SetFullyAmenableAt C x →
      IsProxRegularSetAt C x v ∧ TwiceEpiDifferentiableAt (indicatorVA C) x v) := by
  refine ⟨normal_cone_mappings_and_projections_of_proxRegular_local, fun hA ↦ ?_⟩
  have hx : x ∈ C := hv.1
  have hfa : FullyAmenableAt (indicatorVA C) x := setFullyAmenableAt_iff_indicator.1 hA
  have hv' : v ∈ subdifferential (indicatorVA C) x := by rw [subdifferential_indicatorVA]; exact hv
  exact ⟨(isProxRegularAt_indicatorVA_iff hx).1
    ((prox_regularity_from_amenability hfa.stronglyAmenableAt).1.1 v hv'),
    (hfa.properlyTwiceEpiDifferentiableAt hv').1⟩

end Amenable

end RW
