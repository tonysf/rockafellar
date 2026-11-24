/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Corollary 13.43 for the circle

The circle example given in prose under Corollary 13.43 (`NormalConeProjections`), formalized as a
supplement to the two-point set of `NormalConeProjectionsCounterexample`.  Let `C` be the sphere of
radius `0 < r < 1` around `0` in a finite-dimensional inner product space (the circle in `ℝ²`),
`x̄ ∈ C`, and `v̄ = -r⁻¹x̄` the inward unit normal.  Then `C` is closed and prox-regular at `x̄`
for `v̄` (`isProxRegularSetAt_sphere`, from `N_C(y) = ℝy`, `normalCone_sphere`), but
`ū = x̄ + v̄ = ((1 - r)/r)(-x̄)` lies on the ray through the antipode, so `P_C(ū) = {-x̄}`
(`projMapping_sphere_add_inward`): `x̄` is not a nearest point and
`DP_C(ū ∣ x̄) ≠ [I + DN_C(x̄ ∣ v̄)]⁻¹`, as for the two-point set
(`graphicalDerivative_projMapping_ne_of_notMem`).  Unlike the two-point set, `C` is a smooth
connected curve, and the formula fails even when it is read at the actual nearest point `-x̄`: for a
unit vector `e ⊥ x̄` and `k = r/(1 - r)`, `ke ∈ DP_C(ū ∣ -x̄)(e)`
(`mem_graphicalDerivative_projMapping_sphere`), while `[I + DN_C(x̄ ∣ v̄)]⁻¹(e)` contains `-ke` and
not `ke` (`neg_mem_svResolvent_sphere`, `notMem_svResolvent_sphere`): the sign is reversed.
Consistently with `normal_cone_mappings_and_projections_of_constants`, no constants `ε, ρ` of
prox-regularity of `C` at `x̄` for `v̄` satisfy `2‖v̄‖ < ε` and `ρ‖v̄‖ < ‖v̄‖ + ε`
(`not_exists_constants_sphere`).  Headline: `normal_cone_projection_circle_counterexample`.
-/

import RockafellarWets.Chapter13.NormalConeProjections
import RockafellarWets.Chapter6.SmoothManifolds

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {C : Set E} {x v : E}

omit [FiniteDimensional ℝ E] in
/-- If `x̄` is not a nearest point to `x̄ + v̄` in a closed set `C`, the derivative formula of
Corollary 13.43 fails at `ū = x̄ + v̄`: `(ū, x̄)` is off the closed graph of `P_C`, so
`DP_C(ū ∣ x̄)` has empty values, while `[I + DN_C(x̄ ∣ v̄)]⁻¹(0)` contains `0`. -/
theorem graphicalDerivative_projMapping_ne_of_notMem (hC : IsClosed C) (hv : v ∈ normalCone C x)
    (hxu : x ∉ projMapping C (x + v)) :
    graphicalDerivative (projMapping C) (x + v) x ≠
      svResolvent (graphicalDerivative (normalCone C) x v) 1 := by
  intro heq
  have h1 : (0 : E) ∈ svResolvent (graphicalDerivative (normalCone C) x v) 1 0 := by
    rw [mem_svResolvent]
    refine ⟨0, ?_, by simp⟩
    have hmem : (x, v) ∈ svGraph (normalCone C) := hv
    have h0 := (isCone_tangentCone hmem).1
    rw [← svGraph_graphicalDerivative] at h0
    exact h0
  rw [← heq] at h1
  have h2 : ((0 : E), (0 : E)) ∈ tangentCone (svGraph (projMapping C)) (x + v, x) := by
    rw [← svGraph_graphicalDerivative]; exact h1
  obtain ⟨xs, τs, hxs, hlim, -⟩ := h2
  exact hxu ((isClosed_svGraph_projMapping hC).mem_of_tendsto hlim (Eventually.of_forall hxs))

end General

namespace NormalConeProjectionsCircle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℝ} {x : E}

/-- The normal cone to the sphere of radius `r > 0` at `y` is the line through `y`
(Example 6.8 with `G(z) = ‖z‖² - r²`). -/
theorem normalCone_sphere [FiniteDimensional ℝ E] (hr : 0 < r) {y : E} (hy : y ∈ sphere (0 : E) r) :
    normalCone (sphere (0 : E) r) y = {v | ∃ t : ℝ, v = t • y} := by
  have hy' : ‖y‖ = r := mem_sphere_zero_iff_norm.1 hy
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy'; exact hr.ne hy'
  set G : E → ℝ := fun z ↦ ‖z‖ ^ 2 - r ^ 2 with hG
  have hset : sphere (0 : E) r = G ⁻¹' ({0} : Set ℝ) := by
    ext z
    rw [mem_sphere_zero_iff_norm, mem_preimage, mem_singleton_iff, hG, sub_eq_zero]
    exact (sq_eq_sq₀ (norm_nonneg z) hr.le).symm
  have hlocal : sphere (0 : E) r =ᶠ[𝓝 y] G ⁻¹' ({0} : Set ℝ) := Filter.EventuallyEq.of_eq hset
  have hGd : ContDiffAt ℝ 1 G y := ((contDiff_norm_sq ℝ).sub contDiff_const).contDiffAt
  have hfd : fderiv ℝ G y = 2 • innerSL ℝ y := by
    rw [hG, fderiv_sub_const, fderiv_norm_sq_apply]
  have hsurj : Function.Surjective (fderiv ℝ G y) := by
    intro s
    refine ⟨(s / (2 * r ^ 2)) • y, ?_⟩
    rw [hfd, ContinuousLinearMap.smul_apply, innerSL_apply_apply, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hy', nsmul_eq_mul, Nat.cast_ofNat]
    field_simp
  rw [normalCone_smoothManifold hy hlocal hGd hsurj, hfd]
  ext v
  simp only [mem_range, mem_setOf_eq]
  have key : ∀ s : ℝ, ContinuousLinearMap.adjoint (2 • innerSL ℝ y) s = (2 * s) • y := by
    intro s
    apply ext_inner_right ℝ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, real_inner_smul_left, RCLike.inner_apply, conj_trivial, nsmul_eq_mul,
      Nat.cast_ofNat]
    ring
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨2 * s, key s⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t / 2, ?_⟩
    rw [key]
    congr 1
    ring

/-- The multiples of `y` are normal to the sphere at `y`. -/
theorem smul_mem_normalCone_sphere [FiniteDimensional ℝ E] (hr : 0 < r) {y : E}
    (hy : y ∈ sphere (0 : E) r) (t : ℝ) :
    t • y ∈ normalCone (sphere (0 : E) r) y := by
  rw [normalCone_sphere hr hy]; exact ⟨t, rfl⟩

/-- For `x', y` on the sphere of radius `r`, `‖x' - y‖² = 2r² - 2⟪x', y⟫`. -/
theorem norm_sub_sq_sphere {y x' : E} (hy : ‖y‖ = r) (hx' : ‖x'‖ = r) :
    ‖x' - y‖ ^ 2 = 2 * r ^ 2 - 2 * ⟪x', y⟫_ℝ := by
  rw [norm_sub_sq_real, hy, hx']; ring

/-- The inequality of prox-regularity for the sphere of radius `r > 0` at `x̄` for the inward unit
normal `v̄ = -r⁻¹x̄`, with `ε = 1` and `ρ = 2/r`: the normals within `1` of `v̄` are `ty` with
`t > -2/r`, and `⟪ty, x' - y⟫ = -(t/2)‖x' - y‖²` on the sphere. -/
theorem proxRegular_inequality_sphere [FiniteDimensional ℝ E] (hr : 0 < r)
    (hx : x ∈ sphere (0 : E) r) :
    ∀ y v', v' ∈ normalCone (sphere (0 : E) r) y → ‖v' - -r⁻¹ • x‖ < 1 → ‖y - x‖ < 1 →
      ∀ x' ∈ sphere (0 : E) r ∩ closedBall x 1, ⟪v', x' - y⟫_ℝ ≤ 2 / r / 2 * ‖x' - y‖ ^ 2 := by
  intro y v' hv' hvv _ x' hx'
  have hyS : y ∈ sphere (0 : E) r := hv'.1
  have hy : ‖y‖ = r := mem_sphere_zero_iff_norm.1 hyS
  have hxn : ‖x‖ = r := mem_sphere_zero_iff_norm.1 hx
  have hx'n : ‖x'‖ = r := mem_sphere_zero_iff_norm.1 hx'.1
  rw [normalCone_sphere hr hyS] at hv'
  obtain ⟨t, rfl⟩ := hv'
  have hvbar : ‖-r⁻¹ • x‖ = 1 := by
    rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg hr.le, hxn, inv_mul_cancel₀ hr.ne']
  have ht : -(2 / r) < t := by
    have h1 : |t| * r < 2 := by
      calc |t| * r = ‖t • y‖ := by rw [norm_smul, Real.norm_eq_abs, hy]
        _ ≤ ‖t • y - -r⁻¹ • x‖ + ‖-r⁻¹ • x‖ :=
            (norm_le_insert' (t • y) (-r⁻¹ • x)).trans_eq (add_comm _ _)
        _ < 1 + 1 := by rw [hvbar]; linarith
        _ = 2 := by norm_num
    have h2 : -t * r < 2 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (neg_le_abs t) hr.le) h1
    rw [neg_lt, lt_div_iff₀ hr] at *
    linarith
  have hin : ⟪t • y, x' - y⟫_ℝ = -(t / 2) * ‖x' - y‖ ^ 2 := by
    rw [norm_sub_sq_sphere hy hx'n, real_inner_smul_left, inner_sub_right,
      real_inner_self_eq_norm_sq, hy, real_inner_comm]
    ring
  rw [hin]
  have hsq := sq_nonneg ‖x' - y‖
  have : -(t / 2) ≤ 2 / r / 2 := by linarith
  exact mul_le_mul_of_nonneg_right this hsq

/-- The sphere of radius `r > 0` is prox-regular at each of its points `x̄` for the inward unit
normal `v̄ = -r⁻¹x̄`. -/
theorem isProxRegularSetAt_sphere [FiniteDimensional ℝ E] (hr : 0 < r) (hx : x ∈ sphere (0 : E) r) :
    IsProxRegularSetAt (sphere (0 : E) r) x (-r⁻¹ • x) := by
  refine ⟨IsClosed.isLocallyClosedAt isClosed_sphere x, ?_, 1, one_pos, 2 / r, by positivity,
    proxRegular_inequality_sphere hr hx⟩
  exact smul_mem_normalCone_sphere hr hx _

/-- Points of the ray through `y` on the sphere project onto `y`: `P_S(cy) = {y}` for `c > 0`, since
`‖w - cy‖² - ‖y - cy‖² = c‖w - y‖²` for `w` on the sphere. -/
theorem projMapping_sphere_smul {y : E} (hy : y ∈ sphere (0 : E) r) {c : ℝ}
    (hc : 0 < c) : projMapping (sphere (0 : E) r) (c • y) = {y} := by
  have hyn : ‖y‖ = r := mem_sphere_zero_iff_norm.1 hy
  have key : ∀ w ∈ sphere (0 : E) r, ‖w - c • y‖ ^ 2 = ‖y - c • y‖ ^ 2 + c * ‖w - y‖ ^ 2 := by
    intro w hw
    have hwn : ‖w‖ = r := mem_sphere_zero_iff_norm.1 hw
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right,
      real_inner_smul_right, norm_smul, Real.norm_of_nonneg hc.le, real_inner_self_eq_norm_sq, hwn,
      hyn]
    ring
  ext w
  simp only [mem_projMapping, mem_singleton_iff]
  constructor
  · rintro ⟨hw, hmin⟩
    have h1 := hmin y hy
    have h2 := key w hw
    have h3 : ‖w - c • y‖ ^ 2 ≤ ‖y - c • y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h4 : c * ‖w - y‖ ^ 2 ≤ 0 := by linarith
    have h5 : ‖w - y‖ ^ 2 ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have := mul_pos hc hcon
      linarith
    have : ‖w - y‖ = 0 := by nlinarith [norm_nonneg (w - y)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · rintro rfl
    refine ⟨hy, fun w' hw' ↦ ?_⟩
    have h2 := key w' hw'
    have h3 : ‖w - c • w‖ ^ 2 ≤ ‖w' - c • w‖ ^ 2 := by
      have := mul_nonneg hc.le (sq_nonneg ‖w' - w‖)
      linarith
    exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.1 h3

/-- `x̄ + v̄` for the inward unit normal `v̄ = -r⁻¹x̄` lies on the ray through the antipode
`-x̄`. -/
theorem add_inward_normal_eq (hr : r ≠ 0) (x : E) :
    x + -r⁻¹ • x = ((1 - r) / r) • (-x) := by
  rw [smul_neg, ← neg_smul, ← one_smul ℝ x, smul_smul, ← add_smul, one_smul]
  congr 1
  field_simp
  ring

/-- For `0 < r < 1`, the point `x̄ + v̄` with `v̄ = -r⁻¹x̄` projects onto the antipode `-x̄`. -/
theorem projMapping_sphere_add_inward (hr0 : 0 < r) (hr1 : r < 1) (hx : x ∈ sphere (0 : E) r) :
    projMapping (sphere (0 : E) r) (x + -r⁻¹ • x) = {-x} := by
  rw [add_inward_normal_eq hr0.ne' x]
  refine projMapping_sphere_smul ?_ (div_pos (by linarith) hr0)
  rw [mem_sphere_zero_iff_norm, norm_neg]; exact mem_sphere_zero_iff_norm.1 hx

/-- For `0 < r < 1`, `x̄` is not a nearest point to `x̄ + v̄`, `v̄ = -r⁻¹x̄`. -/
theorem notMem_projMapping_sphere_add_inward (hr0 : 0 < r) (hr1 : r < 1)
    (hx : x ∈ sphere (0 : E) r) : x ∉ projMapping (sphere (0 : E) r) (x + -r⁻¹ • x) := by
  rw [projMapping_sphere_add_inward hr0 hr1 hx, mem_singleton_iff]
  intro h
  have hx0 : x = 0 := by
    have : (2 : ℝ) • x = 0 := by rw [two_smul]; nth_rewrite 1 [h]; abel
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  rw [hx0, mem_sphere_zero_iff_norm, norm_zero] at hx
  exact hr0.ne hx

/-! ### Great circles -/

/-- The great circle through `a` with velocity `ωb` at `t = 0`. -/
noncomputable def greatCircle (a b : E) (ω t : ℝ) : E :=
  Real.cos (ω * t) • a + Real.sin (ω * t) • b

/-- The great circle starts at `a`. -/
theorem greatCircle_zero (a b : E) (ω : ℝ) : greatCircle a b ω 0 = a := by
  simp [greatCircle]

/-- For `a ⊥ b` with `‖a‖ = ‖b‖ = r`, the great circle stays on the sphere of radius `r`. -/
theorem norm_greatCircle {a b : E} (ha : ‖a‖ = r) (hb : ‖b‖ = r) (hab : ⟪a, b⟫_ℝ = 0)
    (ω t : ℝ) : ‖greatCircle a b ω t‖ = r := by
  have hsq : ‖greatCircle a b ω t‖ ^ 2 = r ^ 2 := by
    rw [greatCircle, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, hab, ha, hb, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
      sq_abs, sq_abs]
    have := Real.cos_sq_add_sin_sq (ω * t)
    nlinarith
  have hr : 0 ≤ r := ha ▸ norm_nonneg a
  exact (sq_eq_sq₀ (norm_nonneg _) hr).1 hsq

/-- The velocity of the great circle at `t = 0` is `ωb`. -/
theorem hasDerivAt_greatCircle (a b : E) (ω : ℝ) :
    HasDerivAt (greatCircle a b ω) (ω • b) 0 := by
  have hc : HasDerivAt (fun t : ℝ ↦ Real.cos (ω * t)) (-Real.sin (ω * 0) * ω) 0 := by
    have := (Real.hasDerivAt_cos (ω * 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul ω)
    simpa using this
  have hs : HasDerivAt (fun t : ℝ ↦ Real.sin (ω * t)) (Real.cos (ω * 0) * ω) 0 := by
    have := (Real.hasDerivAt_sin (ω * 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul ω)
    simpa using this
  have h := (hc.smul_const a).add (hs.smul_const b)
  simp only [mul_zero, Real.sin_zero, neg_zero, zero_mul, zero_smul, Real.cos_zero, one_mul,
    zero_add] at h
  exact h

/-- A path in `C` through `ξ(0) = x` with derivative `w` at `0` gives a tangent vector. -/
theorem mem_tangentCone_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : Set F} {p w : F} {ξ : ℝ → F} (hξ0 : ξ 0 = p) (hξ : ∀ t, ξ t ∈ D)
    (hd : HasDerivAt ξ w 0) : w ∈ tangentCone D p := by
  have hp : p ∈ D := hξ0 ▸ hξ 0
  refine derivableCone_subset_tangentCone hp ⟨1, one_pos, ξ, hξ0, fun t _ ↦ hξ t, ?_⟩
  have := hd.tendsto_slope_zero_right
  simp only [zero_add, hξ0] at this
  exact this

/-! ### The sign change -/

section SignChange

variable [FiniteDimensional ℝ E]

/-- With `k = r/(1 - r)`, `ω = k/r = 1/(1 - r)` and `c = (1 - r)/r`: `ck = 1` and `ωr = k`. -/
theorem circle_constants (hr0 : 0 < r) (hr1 : r < 1) :
    (1 - r) / r * (r / (1 - r)) = 1 ∧ 1 / (1 - r) * r = r / (1 - r) ∧
      r / (1 - r) / r - r / (1 - r) = 1 := by
  have h1 : (1 - r) ≠ 0 := by linarith
  refine ⟨by field_simp, by field_simp, ?_⟩
  field_simp

omit [FiniteDimensional ℝ E] in
/-- **The derivative of `P_C` at the actual nearest point.**  For `e ⊥ x̄` with `‖e‖ = 1`,
`(r/(1 - r))e ∈ DP_C(ū ∣ -x̄)(e)`, `ū = x̄ + v̄`: along the great circle `y(t)` through `-x̄` with
velocity `(r/(1 - r))e`, the points `((1 - r)/r)y(t)` project onto `y(t)` and move with velocity
`e`. -/
theorem mem_graphicalDerivative_projMapping_sphere (hr0 : 0 < r) (hr1 : r < 1)
    (hx : x ∈ sphere (0 : E) r) {e : E} (he1 : ‖e‖ = 1) (he : ⟪x, e⟫_ℝ = 0) :
    (r / (1 - r)) • e ∈
      graphicalDerivative (projMapping (sphere (0 : E) r)) (x + -r⁻¹ • x) (-x) e := by
  obtain ⟨hck, hωr, -⟩ := circle_constants hr0 hr1
  have hxn : ‖x‖ = r := mem_sphere_zero_iff_norm.1 hx
  set ω : ℝ := 1 / (1 - r) with hω
  set c : ℝ := (1 - r) / r with hc
  have hc0 : 0 < c := div_pos (by linarith) hr0
  set y : ℝ → E := greatCircle (-x) (r • e) ω with hy
  have hyS : ∀ t, y t ∈ sphere (0 : E) r := by
    intro t
    rw [mem_sphere_zero_iff_norm]
    refine norm_greatCircle (by rw [norm_neg, hxn]) ?_ ?_ ω t
    · rw [norm_smul, he1, mul_one, Real.norm_of_nonneg hr0.le]
    · rw [inner_neg_left, real_inner_smul_right, he, mul_zero, neg_zero]
  set ξ : ℝ → E × E := fun t ↦ (c • y t, y t) with hξ
  have hξ0 : ξ 0 = (x + -r⁻¹ • x, -x) := by
    simp only [hξ, hy, greatCircle_zero, add_inward_normal_eq hr0.ne' x, hc]
  have hξS : ∀ t, ξ t ∈ svGraph (projMapping (sphere (0 : E) r)) := by
    intro t
    change y t ∈ projMapping (sphere (0 : E) r) (c • y t)
    rw [projMapping_sphere_smul (hyS t) hc0]
    exact mem_singleton _
  have hd : HasDerivAt ξ (e, (r / (1 - r)) • e) 0 := by
    have h := hasDerivAt_greatCircle (-x) (r • e) ω
    have h2 := (h.const_smul c).prodMk h
    convert h2 using 2
    · rw [smul_smul, smul_smul, mul_assoc c ω r, hωr, hck, one_smul]
    · rw [smul_smul, hωr]
  have hmem := mem_tangentCone_of_hasDerivAt hξ0 hξS hd
  rw [← svGraph_graphicalDerivative] at hmem
  exact hmem

/-- **The graphical derivative of `N_C` for the sphere, in tangent directions.**  If
`(w, z) ∈ T_{gph N_C}(x̄, v̄)` with `v̄ = -r⁻¹x̄`, then `⟪z, e⟫ = -r⁻¹⟪w, e⟫` for every `e ⊥ x̄`:
along `(yₙ, tₙyₙ) → (x̄, v̄)`, `tₙ → -r⁻¹` and `⟪tₙyₙ - v̄, e⟫ = tₙ⟪yₙ - x̄, e⟫`. -/
theorem inner_eq_of_mem_tangentCone_normalCone_sphere (hr : 0 < r) (hx : x ∈ sphere (0 : E) r)
    {e w z : E} (he : ⟪x, e⟫_ℝ = 0)
    (h : (w, z) ∈ tangentCone (svGraph (normalCone (sphere (0 : E) r))) (x, -r⁻¹ • x)) :
    ⟪z, e⟫_ℝ = -r⁻¹ * ⟪w, e⟫_ℝ := by
  obtain ⟨ps, τs, hps, hpsx, -, -, hq⟩ := h
  have hN : ∀ n, ∃ t : ℝ, (ps n).2 = t • (ps n).1 ∧ ‖(ps n).1‖ = r := by
    intro n
    have h1 : (ps n).2 ∈ normalCone (sphere (0 : E) r) (ps n).1 := hps n
    have h2 : (ps n).1 ∈ sphere (0 : E) r := h1.1
    rw [normalCone_sphere hr h2] at h1
    obtain ⟨t, ht⟩ := h1
    exact ⟨t, ht, mem_sphere_zero_iff_norm.1 h2⟩
  choose ts hts hnorm using hN
  have hts' : ∀ n, ts n = ⟪(ps n).2, (ps n).1⟫_ℝ / r ^ 2 := by
    intro n
    rw [hts n, real_inner_smul_left, real_inner_self_eq_norm_sq, hnorm n]
    field_simp
  have h1 : Tendsto (fun n ↦ (ps n).1) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hpsx
  have h2 : Tendsto (fun n ↦ (ps n).2) atTop (𝓝 (-r⁻¹ • x)) :=
    (continuous_snd.tendsto _).comp hpsx
  have hT : Tendsto ts atTop (𝓝 (-r⁻¹)) := by
    have h3 := (h2.inner h1).div_const (r ^ 2)
    have hlim : ⟪-r⁻¹ • x, x⟫_ℝ / r ^ 2 = -r⁻¹ := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.1 hx]
      field_simp
    rw [hlim] at h3
    exact h3.congr fun n ↦ (hts' n).symm
  have hw : Tendsto (fun n ↦ (τs n)⁻¹ • ((ps n).1 - x)) atTop (𝓝 w) := by
    have := (continuous_fst.tendsto _).comp hq
    simpa using this
  have hz : Tendsto (fun n ↦ (τs n)⁻¹ • ((ps n).2 - -r⁻¹ • x)) atTop (𝓝 z) := by
    refine ((continuous_snd.tendsto _).comp hq).congr fun n ↦ ?_
    simp only [Function.comp_apply, Prod.smul_snd, Prod.snd_sub]
  have hb : Tendsto (fun n ↦ ⟪(τs n)⁻¹ • ((ps n).1 - x), e⟫_ℝ) atTop (𝓝 ⟪w, e⟫_ℝ) :=
    hw.inner tendsto_const_nhds
  have ha : Tendsto (fun n ↦ ⟪(τs n)⁻¹ • ((ps n).2 - -r⁻¹ • x), e⟫_ℝ) atTop (𝓝 ⟪z, e⟫_ℝ) :=
    hz.inner tendsto_const_nhds
  have heq : ∀ n, ⟪(τs n)⁻¹ • ((ps n).2 - -r⁻¹ • x), e⟫_ℝ =
      ts n * ⟪(τs n)⁻¹ • ((ps n).1 - x), e⟫_ℝ := by
    intro n
    rw [hts n, real_inner_smul_left, real_inner_smul_left, inner_sub_left, inner_sub_left,
      real_inner_smul_left, real_inner_smul_left, he]
    ring
  have hprod := hT.mul hb
  exact tendsto_nhds_unique ha (hprod.congr fun n ↦ (heq n).symm)

/-- **The printed formula at `-x̄`, read with the derivative of `N_C`.**  For `e ⊥ x̄` with
`‖e‖ = 1`, `-(r/(1 - r))e ∈ [I + DN_C(x̄ ∣ v̄)]⁻¹(e)`: along the great circle `y(t)` through `x̄`
with velocity `-(r/(1 - r))e`, `-r⁻¹y(t) ∈ N_C(y(t))`. -/
theorem neg_mem_svResolvent_sphere (hr0 : 0 < r) (hr1 : r < 1) (hx : x ∈ sphere (0 : E) r)
    {e : E} (he1 : ‖e‖ = 1) (he : ⟪x, e⟫_ℝ = 0) :
    -((r / (1 - r)) • e) ∈
      svResolvent (graphicalDerivative (normalCone (sphere (0 : E) r)) x (-r⁻¹ • x)) 1 e := by
  obtain ⟨-, hωr, hk⟩ := circle_constants hr0 hr1
  have hxn : ‖x‖ = r := mem_sphere_zero_iff_norm.1 hx
  set ω : ℝ := 1 / (1 - r) with hω
  set y : ℝ → E := greatCircle x (r • e) (-ω) with hy
  have hyS : ∀ t, y t ∈ sphere (0 : E) r := by
    intro t
    rw [mem_sphere_zero_iff_norm]
    refine norm_greatCircle hxn ?_ ?_ (-ω) t
    · rw [norm_smul, he1, mul_one, Real.norm_of_nonneg hr0.le]
    · rw [real_inner_smul_right, he, mul_zero]
  set ξ : ℝ → E × E := fun t ↦ (y t, -r⁻¹ • y t) with hξ
  have hξ0 : ξ 0 = (x, -r⁻¹ • x) := by simp only [hξ, hy, greatCircle_zero]
  have hξS : ∀ t, ξ t ∈ svGraph (normalCone (sphere (0 : E) r)) :=
    fun t ↦ smul_mem_normalCone_sphere hr0 (hyS t) _
  have hd : HasDerivAt ξ (-((r / (1 - r)) • e), (r / (1 - r) / r) • e) 0 := by
    have h := hasDerivAt_greatCircle x (r • e) (-ω)
    have h2 := h.prodMk (h.const_smul (-r⁻¹))
    convert h2 using 2
    · rw [smul_smul, neg_mul, hωr, neg_smul]
    · have hr' : r ≠ 0 := hr0.ne'
      have h1r : 1 - r ≠ 0 := by linarith
      rw [smul_smul, smul_smul]
      congr 1
      rw [hω]
      field_simp
  have hmem := mem_tangentCone_of_hasDerivAt hξ0 hξS hd
  rw [← svGraph_graphicalDerivative] at hmem
  rw [mem_svResolvent]
  refine ⟨(r / (1 - r) / r) • e, hmem, ?_⟩
  rw [one_smul, ← neg_smul, ← add_smul]
  have : -(r / (1 - r)) + r / (1 - r) / r = 1 := by linarith
  rw [this, one_smul]

/-- **The sign change.**  For `e ⊥ x̄` with `‖e‖ = 1`, `(r/(1 - r))e ∉ [I + DN_C(x̄ ∣ v̄)]⁻¹(e)`:
by `inner_eq_of_mem_tangentCone_normalCone_sphere`, `z ∈ DN_C(x̄ ∣ v̄)(ke)` with `ke + z = e`,
`k = r/(1 - r)`, would give `1 - k = -k/r`, that is `r = 1`. -/
theorem notMem_svResolvent_sphere (hr0 : 0 < r) (hr1 : r < 1) (hx : x ∈ sphere (0 : E) r)
    {e : E} (he1 : ‖e‖ = 1) (he : ⟪x, e⟫_ℝ = 0) :
    (r / (1 - r)) • e ∉
      svResolvent (graphicalDerivative (normalCone (sphere (0 : E) r)) x (-r⁻¹ • x)) 1 e := by
  intro h
  rw [mem_svResolvent] at h
  obtain ⟨z, hz, hsum⟩ := h
  have hmem : ((r / (1 - r)) • e, z) ∈
      tangentCone (svGraph (normalCone (sphere (0 : E) r))) (x, -r⁻¹ • x) := by
    rw [← svGraph_graphicalDerivative]; exact hz
  have hin := inner_eq_of_mem_tangentCone_normalCone_sphere hr0 hx he hmem
  have hz' : z = (1 - r / (1 - r)) • e := by
    rw [one_smul] at hsum
    rw [eq_sub_of_add_eq' hsum, sub_smul, one_smul]
  have hee : ⟪e, e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he1, one_pow]
  rw [hz', real_inner_smul_left, real_inner_smul_left, hee] at hin
  have h1 : (1 - r) ≠ 0 := by linarith
  field_simp at hin
  nlinarith

/-- **Corollary 13.43 at `ū = x̄ + v̄` fails for the circle.**  For the sphere `C` of radius
`0 < r < 1` around `0`, `x̄ ∈ C` and the inward unit normal `v̄ = -r⁻¹x̄`: `C` is closed and
prox-regular at `x̄` for `v̄`, but `P_C(x̄ + v̄) = {-x̄}`, so `x̄ ∉ P_C(x̄ + v̄)` and
`DP_C(ū ∣ x̄) ≠ [I + DN_C(x̄ ∣ v̄)]⁻¹`.  Read at the actual nearest point `-x̄`, the formula has the
wrong sign in each unit direction `e ⊥ x̄`: with `k = r/(1 - r)`, `ke ∈ DP_C(ū ∣ -x̄)(e)`, whereas
`-ke ∈ [I + DN_C(x̄ ∣ v̄)]⁻¹(e)` and `ke ∉ [I + DN_C(x̄ ∣ v̄)]⁻¹(e)`. -/
theorem normal_cone_projection_circle_counterexample (hr0 : 0 < r) (hr1 : r < 1)
    (hx : ‖x‖ = r) :
    IsClosed (sphere (0 : E) r) ∧ IsProxRegularSetAt (sphere (0 : E) r) x (-r⁻¹ • x) ∧
      ‖-r⁻¹ • x‖ = 1 ∧ projMapping (sphere (0 : E) r) (x + -r⁻¹ • x) = {-x} ∧
      x ∉ projMapping (sphere (0 : E) r) (x + -r⁻¹ • x) ∧
      graphicalDerivative (projMapping (sphere (0 : E) r)) (x + -r⁻¹ • x) x ≠
        svResolvent (graphicalDerivative (normalCone (sphere (0 : E) r)) x (-r⁻¹ • x)) 1 ∧
      ∀ e : E, ‖e‖ = 1 → ⟪x, e⟫_ℝ = 0 →
        (r / (1 - r)) • e ∈
          graphicalDerivative (projMapping (sphere (0 : E) r)) (x + -r⁻¹ • x) (-x) e ∧
        -((r / (1 - r)) • e) ∈
          svResolvent (graphicalDerivative (normalCone (sphere (0 : E) r)) x (-r⁻¹ • x)) 1 e ∧
        (r / (1 - r)) • e ∉
          svResolvent (graphicalDerivative (normalCone (sphere (0 : E) r)) x (-r⁻¹ • x)) 1 e := by
  have hxS : x ∈ sphere (0 : E) r := mem_sphere_zero_iff_norm.2 hx
  have hpr := isProxRegularSetAt_sphere hr0 hxS
  have hnot := notMem_projMapping_sphere_add_inward hr0 hr1 hxS
  refine ⟨isClosed_sphere, hpr, ?_, projMapping_sphere_add_inward hr0 hr1 hxS, hnot,
    graphicalDerivative_projMapping_ne_of_notMem isClosed_sphere hpr.2.1 hnot,
    fun e he1 he ↦ ⟨mem_graphicalDerivative_projMapping_sphere hr0 hr1 hxS he1 he,
      neg_mem_svResolvent_sphere hr0 hr1 hxS he1 he, notMem_svResolvent_sphere hr0 hr1 hxS he1 he⟩⟩
  rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg hr0.le, hx, inv_mul_cancel₀ hr0.ne']

/-- No constants `ε, ρ` of prox-regularity of the sphere of radius `0 < r < 1` at `x̄` for the
inward unit normal `v̄ = -r⁻¹x̄` satisfy the sufficient condition `2‖v̄‖ < ε`,
`ρ‖v̄‖ < ‖v̄‖ + ε` of `normal_cone_mappings_and_projections_of_constants`, which would give
`P_C(x̄ + v̄) = {x̄}`. -/
theorem not_exists_constants_sphere (hr0 : 0 < r) (hr1 : r < 1) (hx : ‖x‖ = r) :
    ¬ ∃ ε ρ : ℝ, 0 ≤ ρ ∧ 2 * ‖-r⁻¹ • x‖ < ε ∧ ρ * ‖-r⁻¹ • x‖ < ‖-r⁻¹ • x‖ + ε ∧
      ∀ y v', v' ∈ normalCone (sphere (0 : E) r) y → ‖v' - -r⁻¹ • x‖ < ε → ‖y - x‖ < ε →
        ∀ x' ∈ sphere (0 : E) r ∩ closedBall x ε, ⟪v', x' - y⟫_ℝ ≤ ρ / 2 * ‖x' - y‖ ^ 2 := by
  rintro ⟨ε, ρ, hρ, h1, h2, hprox⟩
  have hxS : x ∈ sphere (0 : E) r := mem_sphere_zero_iff_norm.2 hx
  have hv : -r⁻¹ • x ∈ normalCone (sphere (0 : E) r) x := smul_mem_normalCone_sphere hr0 hxS _
  have h := (normal_cone_mappings_and_projections_of_constants
    (IsClosed.isLocallyClosedAt isClosed_sphere x) hv hρ h1 h2 hprox).1
  exact notMem_projMapping_sphere_add_inward hr0 hr1 hxS (by rw [h]; exact mem_singleton x)

end SignChange

end NormalConeProjectionsCircle

end RW
