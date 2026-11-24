/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Prox-regularity versus subsmoothness

Proposition 13.33.  Lower-`C²` functions on an open set are strongly amenable (10.36), hence
prox-regular and subdifferentially continuous there (13.32), and they are strictly continuous
(10.31).  Conversely, prox-regularity together with strict continuity yields, by compactness of
`∂f(x̄)` and outer semicontinuity of `∂f`, a uniform inequality
`f(x') ≥ f(x) + ⟪v, x' - x⟫ - (ρ/2)‖x' - x‖²` on a ball; then `f + (ρ/2)‖·‖²` is a pointwise
supremum of affine functions there, hence convex, and `f` is lower-`C²` by 10.33.  At a point of
strict differentiability, prox-regularity at `x̄` alone already gives the uniform inequality.
-/

import RockafellarWets.Chapter13.AmenableProxRegularity
import RockafellarWets.Chapter10.SubsmoothAmenability
import RockafellarWets.Chapter10.SubsmoothCalculus
import RockafellarWets.Chapter9.SubgradientModulus
import RockafellarWets.Chapter9.RegularStrictContinuity
import RockafellarWets.Chapter9.StrictDifferentiability

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A function with a supporting affine minorant at every point of a convex set is convex
there. -/
theorem convexOn_of_forall_exists_support {U : Set E} (hU : Convex ℝ U) {g : E → ℝ}
    (h : ∀ y ∈ U, ∃ s : E, ∀ z ∈ U, g y + ⟪s, z - y⟫_ℝ ≤ g z) : ConvexOn ℝ U g := by
  refine ⟨hU, fun x hx y hy a b ha hb hab ↦ ?_⟩
  set z := a • x + b • y
  obtain ⟨s, hs⟩ := h z (hU hx hy ha hb hab)
  have h1 := hs x hx
  have h2 := hs y hy
  have hzero : a * ⟪s, x - z⟫_ℝ + b * ⟪s, y - z⟫_ℝ = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right]
    have : a • (x - z) + b • (y - z) = 0 := by
      obtain rfl : b = 1 - a := by linarith
      simp only [z]
      module
    rw [this, inner_zero_right]
  have h1' := mul_le_mul_of_nonneg_left h1 ha
  have h2' := mul_le_mul_of_nonneg_left h2 hb
  have hz : g z = a * g z + b * g z := by rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul]
  linarith

variable [FiniteDimensional ℝ E]

/-- Outer semicontinuity and local boundedness of `∂f` at a point of strict continuity (5.19):
`∂f(x)` lies in any open set containing `∂f(x̄)` for `x` near `x̄`. -/
theorem ERealStrictlyContinuousAt.eventually_subdifferential_subset {f : E → EReal} {x : E}
    (hsc : ERealStrictlyContinuousAt f x) {W : Set E} (hW : IsOpen W)
    (hsub : subdifferential f x ⊆ W) : ∀ᶠ y in 𝓝 x, subdifferential f y ⊆ W := by
  obtain ⟨V, hV, hbdd⟩ := hsc.locallyBoundedAt_subdifferential
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
  have hK : IsCompact (closedBall (0 : E) R \ W) := (isCompact_closedBall 0 R).diff hW
  have hev : ∀ᶠ y in 𝓝 x, ∀ z ∈ closedBall (0 : E) R \ W, z ∉ subdifferential f y := by
    refine hK.eventually_forall_of_forall_eventually fun z hz ↦ ?_
    have hzx : z ∉ subdifferential f x := fun h ↦ hz.2 (hsub h)
    have hnot : z ∉ svOuterLimit (subdifferential f) x := fun h ↦
      hzx (svOscAt_subdifferential_of_eRealStrictlyContinuousAt hsc h)
    have hN : ∃ N ∈ 𝓝 z, ∀ᶠ y in 𝓝 x, ¬ (subdifferential f y ∩ N).Nonempty := by
      by_contra hc
      push_neg at hc
      exact hnot fun N hN ↦ hc N hN
    obtain ⟨N, hN, hevN⟩ := hN
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod hevN hN] with p ⟨hp1, hp2⟩ hmem
    exact hp1 ⟨p.2, hmem, hp2⟩
  filter_upwards [hV, hev] with y hyV hy v hv
  by_contra hvW
  exact hy v ⟨hR (mem_svImage.2 ⟨y, hyV, hv⟩), hvW⟩ hv

/-- A function with a supporting quadratic minorant `g(y) + ⟪s, z - y⟫ - (ρ/2)‖z - y‖²` at every
point of an open convex set is lower-`C²` there (10.33): `g + (ρ/2)‖·‖²` is a supremum of affine
functions. -/
theorem isLowerCOn_two_of_forall_quadratic_minorant {g : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hUc : Convex ℝ U) {ρ : ℝ}
    (h : ∀ y ∈ U, ∃ s : E, ∀ z ∈ U, g y + ⟪s, z - y⟫_ℝ - ρ / 2 * ‖z - y‖ ^ 2 ≤ g z) :
    IsLowerCOn 2 g U := by
  refine isLowerCOn_two_iff_locally_convex_sub.2 fun x hx ↦
    ⟨U, hU, hx, subset_rfl, fun y ↦ g y + ρ / 2 * ‖y‖ ^ 2, fun y ↦ ρ / 2 * ‖y‖ ^ 2,
      ?_, (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffOn, fun y _ ↦ by ring⟩
  refine convexOn_of_forall_exists_support hUc fun y hy ↦ ?_
  obtain ⟨s, hs⟩ := h y hy
  refine ⟨s + ρ • y, fun z hz ↦ ?_⟩
  have h1 := hs z hz
  have e1 : ‖z - y‖ ^ 2 = ‖z‖ ^ 2 - 2 * ⟪z, y⟫_ℝ + ‖y‖ ^ 2 := norm_sub_sq_real z y
  have e2 : ⟪s + ρ • y, z - y⟫_ℝ = ⟪s, z - y⟫_ℝ + ρ * (⟪z, y⟫_ℝ - ‖y‖ ^ 2) := by
    simp only [inner_add_left, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm z y]
    ring
  have e1' : ρ / 2 * ‖z - y‖ ^ 2 = ρ / 2 * (‖z‖ ^ 2 - 2 * ⟪z, y⟫_ℝ + ‖y‖ ^ 2) := by rw [e1]
  rw [e2]
  linarith

/-- A uniform prox-regularity inequality on an open convex set on which `f` is finite with
nonempty subgradients makes `f` lower-`C²` there. -/
theorem isLowerCOn_two_of_uniform_prox {f : E → EReal} {U : Set E} (hU : IsOpen U)
    (hUc : Convex ℝ U) {ρ : ℝ} (hfin : ∀ y ∈ U, f y = ((f y).toReal : EReal))
    (hne : ∀ y ∈ U, (subdifferential f y).Nonempty)
    (h : ∀ y ∈ U, ∀ v ∈ subdifferential f y, ∀ x' ∈ U,
      f y + ((⟪v, x' - y⟫_ℝ - ρ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x') :
    IsLowerCOn 2 (fun y ↦ (f y).toReal) U := by
  refine isLowerCOn_two_of_forall_quadratic_minorant hU hUc (ρ := ρ) fun y hy ↦ ?_
  obtain ⟨v, hv⟩ := hne y hy
  refine ⟨v, fun z hz ↦ ?_⟩
  have h1 := h y hy v hv z hz
  rw [hfin y hy, hfin z hz, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  linarith

/-- **Proposition 13.33**, converse part, at one point: prox-regularity and strict continuity at
`x̄` give a uniform prox-regularity inequality on a ball around `x̄`. -/
theorem exists_uniform_prox_of_strictlyContinuousAt {f : E → EReal} {x : E}
    (hsc : ERealStrictlyContinuousAt f x) (hpr : IsProxRegularAtPoint f x) :
    ∃ δ > 0, ∃ ρ : ℝ, ∀ y ∈ ball x δ, ∀ v ∈ subdifferential f y, ∀ x' ∈ ball x δ,
      f y + ((⟪v, x' - y⟫_ℝ - ρ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x' := by
  classical
  obtain ⟨hKne, hK⟩ := hsc.subdifferential_nonempty_compact
  have hpv : ∀ v ∈ subdifferential f x, ∃ ε > 0, ∃ ρ ≥ 0, ∀ y v', v' ∈ subdifferential f y →
      ‖v' - v‖ < ε → ‖y - x‖ < ε → f y < f x + ε → ∀ x' ∈ closedBall x ε,
        f y + ((⟪v', x' - y⟫_ℝ - ρ / 2 * ‖x' - y‖ ^ 2 : ℝ) : EReal) ≤ f x' :=
    fun v hv ↦ (hpr v hv).2.2
  choose! ε hε ρ hρ hineq using hpv
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun v ↦ ball v (ε v))
    (fun v hv ↦ ball_mem_nhds v (hε v hv))
  have htne : t.Nonempty := by
    obtain ⟨v, hv⟩ := hKne
    obtain ⟨w, hw, -⟩ := mem_iUnion₂.1 (hcover hv)
    exact ⟨w, hw⟩
  have hWo : IsOpen (⋃ v ∈ t, ball v (ε v)) := isOpen_biUnion fun _ _ ↦ isOpen_ball
  have hsub := hsc.eventually_subdifferential_subset hWo hcover
  have hxc : f x = ((f x).toReal : EReal) := hsc.finite
  have hval : ∀ᶠ y in 𝓝 x, ∀ v ∈ t, f y < f x + ε v := by
    refine (eventually_all_finset t).2 fun v hv ↦ hsc.continuousAt.eventually (gt_mem_nhds ?_)
    rw [hxc, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    linarith [hε v (htK v hv)]
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.1 (hsub.and hval)
  set e := t.inf' htne ε
  have he : 0 < e := (Finset.lt_inf'_iff htne).2 fun v hv ↦ hε v (htK v hv)
  set δ := min δ₁ e
  refine ⟨δ, lt_min hδ₁ he, ∑ v ∈ t, ρ v, fun y hy v' hv' x' hx' ↦ ?_⟩
  have hyδ₁ : y ∈ ball x δ₁ := ball_subset_ball (min_le_left _ _) hy
  obtain ⟨hyW, hyval⟩ := hball hyδ₁
  obtain ⟨v, hvt, hv'v⟩ := mem_iUnion₂.1 (hyW hv')
  have hδv : δ ≤ ε v := (min_le_right _ _).trans (Finset.inf'_le ε hvt)
  have hyx : ‖y - x‖ < ε v := by
    rw [← dist_eq_norm]
    exact (mem_ball.1 hy).trans_le hδv
  have hx'v : x' ∈ closedBall x (ε v) :=
    ball_subset_closedBall (ball_subset_ball hδv hx')
  have h1 := hineq v (htK v hvt) y v' hv' (by rwa [← dist_eq_norm]) hyx (hyval v hvt) x' hx'v
  refine le_trans (add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)) h1
  have hρle : ρ v ≤ ∑ w ∈ t, ρ w :=
    Finset.single_le_sum (fun w hw ↦ hρ w (htK w hw)) hvt
  nlinarith [sq_nonneg ‖x' - y‖]

/-- **Proposition 13.33**, first part: a function lower-`C²` on an open set `O` is prox-regular,
subdifferentially continuous and strictly continuous at every point of `O`. -/
theorem isProxRegular_of_isLowerCOn_two {f : E → EReal} {O : Set E} (hO : IsOpen O)
    (hfin : ∀ y ∈ O, f y ≠ ⊥ ∧ f y ≠ ⊤) (hlow : IsLowerCOn 2 (fun y ↦ (f y).toReal) O)
    {x : E} (hx : x ∈ O) :
    IsProxRegularAtPoint f x ∧ IsSubdifferentiallyContinuousAtPoint f x ∧
      ERealStrictlyContinuousAt f x := by
  have hsa : StronglyAmenableAt f x :=
    (IsLowerC2Around.stronglyAmenableAt ⟨O, hO, hx, hfin, hlow⟩).1
  refine ⟨(prox_regularity_from_amenability hsa).1.1, (prox_regularity_from_amenability hsa).1.2,
    ?_, hlow.strictlyContinuousAt (by norm_num) hx⟩
  filter_upwards [hO.mem_nhds hx] with y hy
  exact (EReal.coe_toReal (hfin y hy).2 (hfin y hy).1).symm

/-- **Proposition 13.33**, converse part: a function prox-regular and strictly continuous at
every point of an open set `O` is lower-`C²` on `O`. -/
theorem isLowerCOn_two_of_isProxRegular {f : E → EReal} {O : Set E} (hO : IsOpen O)
    (h : ∀ x ∈ O, IsProxRegularAtPoint f x ∧ ERealStrictlyContinuousAt f x) :
    (∀ y ∈ O, f y ≠ ⊥ ∧ f y ≠ ⊤) ∧ IsLowerCOn 2 (fun y ↦ (f y).toReal) O := by
  have hfin : ∀ y ∈ O, f y = ((f y).toReal : EReal) := fun y hy ↦ (h y hy).2.finite
  refine ⟨fun y hy ↦ ⟨by rw [hfin y hy]; exact EReal.coe_ne_bot _,
    by rw [hfin y hy]; exact EReal.coe_ne_top _⟩, ?_⟩
  refine isLowerCOn_of_local fun x hx ↦ ?_
  obtain ⟨δ₀, hδ₀, hρ⟩ := exists_uniform_prox_of_strictlyContinuousAt (h x hx).2 (h x hx).1
  obtain ⟨δ₁, hδ₁, hδ₁O⟩ := Metric.isOpen_iff.1 hO x hx
  set δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hδO : ball x δ ⊆ O := (ball_subset_ball (min_le_right _ _)).trans hδ₁O
  have hδ₀' : ball x δ ⊆ ball x δ₀ := ball_subset_ball (min_le_left _ _)
  obtain ⟨ρ, hρ⟩ := hρ
  refine ⟨ball x δ, isOpen_ball, mem_ball_self hδ, hδO,
    isLowerCOn_two_of_uniform_prox isOpen_ball (convex_ball x δ) (fun y hy ↦ hfin y (hδO hy))
      (fun y hy ↦ (h y (hδO hy)).2.subdifferential_nonempty_compact.1)
      (fun y hy v hv x' hx' ↦ hρ y (hδ₀' hy) v hv x' (hδ₀' hx'))⟩

/-- **Proposition 13.33**, last assertion: a function prox-regular at a point `x̄` where it is
strictly differentiable is lower-`C²` around `x̄`. -/
theorem IsProxRegularAt.isLowerC2Around_of_hasStrictGradientAt {f : E → EReal} {x v : E}
    (hpr : IsProxRegularAt f x v) (hsd : HasStrictGradientAt f v x) : IsLowerC2Around f x := by
  have hsc := hsd.eRealStrictlyContinuousAt
  have hv : subdifferential f x = {v} := hsd.subdifferential_eq
  obtain ⟨-, -, ε, hε, ρ, -, hineq⟩ := hpr
  obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hsc.2
  obtain ⟨U, hUx, hUo, hUfin, hLU⟩ := hsc.exists_lipschitzOnWith hk
  have hscU : ∀ y ∈ U, ERealStrictlyContinuousAt f y := fun y hy ↦
    ⟨Filter.eventually_of_mem (hUo.mem_nhds hy) hUfin,
      strictlyContinuousAt_iff.2 ⟨k, U, hUo.mem_nhds hy, hLU⟩⟩
  have hsub := hsc.eventually_subdifferential_subset (W := ball v ε) isOpen_ball
    (by rw [hv]; exact singleton_subset_iff.2 (mem_ball_self hε))
  have hxc : f x = ((f x).toReal : EReal) := hsc.finite
  have hval : ∀ᶠ y in 𝓝 x, f y < f x + ε := by
    refine hsc.continuousAt.eventually (gt_mem_nhds ?_)
    rw [hxc, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    linarith
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.1 ((hsub.and hval).and hUx)
  set δ := min δ₁ ε
  have hδ : 0 < δ := lt_min hδ₁ hε
  have hδ₁' : ball x δ ⊆ ball x δ₁ := ball_subset_ball (min_le_left _ _)
  refine ⟨ball x δ, isOpen_ball, mem_ball_self hδ, fun y hy ↦ ?_, ?_⟩
  · have hyU := (hball (hδ₁' hy)).2
    rw [hUfin y hyU]
    exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  refine isLowerCOn_two_of_uniform_prox (ρ := ρ) isOpen_ball (convex_ball x δ)
    (fun y hy ↦ hUfin y (hball (hδ₁' hy)).2)
    (fun y hy ↦ (hscU y (hball (hδ₁' hy)).2).subdifferential_nonempty_compact.1)
    (fun y hy v' hv' x' hx' ↦ ?_)
  obtain ⟨⟨hyW, hyval⟩, -⟩ := hball (hδ₁' hy)
  have hyx : ‖y - x‖ < ε := by
    rw [← dist_eq_norm]
    exact (mem_ball.1 hy).trans_le (min_le_right _ _)
  have hx'ε : x' ∈ closedBall x ε :=
    ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hx')
  have hv'v := hyW hv'
  rw [mem_ball, dist_eq_norm] at hv'v
  exact hineq y v' hv' hv'v hyx hyval x' hx'ε

/-- **Proposition 13.33** (prox-regularity versus subsmoothness). -/
theorem prox_regularity_versus_subsmoothness {f : E → EReal} {O : Set E} (hO : IsOpen O) :
    ((∀ y ∈ O, f y ≠ ⊥ ∧ f y ≠ ⊤) → IsLowerCOn 2 (fun y ↦ (f y).toReal) O →
      ∀ x ∈ O, IsProxRegularAtPoint f x ∧ IsSubdifferentiallyContinuousAtPoint f x ∧
        ERealStrictlyContinuousAt f x) ∧
    ((∀ x ∈ O, IsProxRegularAtPoint f x ∧ ERealStrictlyContinuousAt f x) →
      (∀ y ∈ O, f y ≠ ⊥ ∧ f y ≠ ⊤) ∧ IsLowerCOn 2 (fun y ↦ (f y).toReal) O) ∧
    (∀ x v, IsProxRegularAt f x v → HasStrictGradientAt f v x → IsLowerC2Around f x) :=
  ⟨fun hfin hlow _ hx ↦ isProxRegular_of_isLowerCOn_two hO hfin hlow hx,
    isLowerCOn_two_of_isProxRegular hO,
    fun _ _ hpr hsd ↦ hpr.isLowerC2Around_of_hasStrictGradientAt hsd⟩

end RW
