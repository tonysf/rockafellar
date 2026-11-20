/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: quadratic representations of lower-`C²` functions

From the proof of **Theorem 10.33**: if `f = max_t f_t` is a lower-`C²` representation on `V`
and `ρ` bounds `|∇²f_t|` on `T × IB(x̄, δ)` with `IB(x̄, δ) ⊂ V`, then
`f_t(x) ≥ f_t(w) + ⟪∇f_t(w), x - w⟫ - ρ|x - w|²` for `x, w ∈ IB(x̄, δ)`
(`LowerRepresentation.quadratic_lower_bound`; the book has `ρ/2` from a second-order Taylor
argument, the mean value argument used here gives the constant `ρ`, which is immaterial), so
that on `int IB(x̄, δ)`

  `f(x) = max_{(t, w) ∈ T × IB(x̄, δ)} [f_t(w) + ⟪∇f_t(w), x - w⟫ - ρ|x - w|²]`,

a representation by quadratic functions of `x` whose coefficients depend continuously on the
index (`LowerRepresentation.quadraticRepresentation`).  Consequences:

* **Corollary 10.34**: lower-`C²` functions are lower-`C^∞` (`IsLowerCOn.lowerCInfty`), so
  all classes lower-`Cᵏ`, `k ≥ 2`, coincide (`isLowerCOn_iff_two`);
* **Theorem 10.33** (one direction): a lower-`C²` function is, around each point, a finite
  convex function minus `ρ|x|²` (`IsLowerCOn.exists_convex_sub_quadratic`).

The continuity of all derivatives in the index uses `continuous_iteratedFDeriv_param`: the
iterated partial derivatives in `x` of a jointly smooth `Q(p, x)` are continuous in `(p, x)`.
-/

import RockafellarWets.Chapter10.SubsmoothFunctions
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Iterated partial derivatives in `x` of a jointly smooth function `Q(p, x)` are continuous
in `(p, x)`. -/
theorem continuous_iteratedFDeriv_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {Q : P × E → ℝ} {n : WithTop ℕ∞}
    (hQ : ContDiff ℝ n Q) {j : ℕ} (hj : (j : WithTop ℕ∞) ≤ n) :
    Continuous fun q : P × E ↦ iteratedFDeriv ℝ j (fun x ↦ Q (q.1, x)) q.2 := by
  have key : ∀ q : P × E, iteratedFDeriv ℝ j (fun x ↦ Q (q.1, x)) q.2 =
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j ↦ ContinuousLinearMap.inr ℝ P E)
        (iteratedFDeriv ℝ j Q q) := by
    intro q
    have hc : ContDiff ℝ n fun z : P × E ↦ Q ((q.1, 0) + z) := hQ.comp (contDiff_const.add contDiff_id)
    have h1 : (fun x ↦ Q (q.1, x)) =
        (fun z : P × E ↦ Q ((q.1, 0) + z)) ∘ ContinuousLinearMap.inr ℝ P E := by
      funext x
      simp
    rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _ hj,
      iteratedFDeriv_comp_add_left]
    simp
  rw [funext key]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL _).continuous.comp
    (hQ.continuous_iteratedFDeriv hj)

namespace LowerRepresentation

variable {k : ℕ∞} {f : E → ℝ} {V : Set E} (R : LowerRepresentation k f V)

omit [FiniteDimensional ℝ E] in
theorem continuousOn_iteratedFDeriv_two (hk : 2 ≤ k) :
    ContinuousOn (fun p : R.T × E ↦ iteratedFDeriv ℝ 2 (R.F p.1) p.2) (univ ×ˢ V) :=
  R.continuousOn_iteratedFDeriv 2 (by exact_mod_cast hk)

omit [FiniteDimensional ℝ E] in
theorem differentiableAt_fderiv (hk : 2 ≤ k) (hV : IsOpen V) (t : R.T) {x : E} (hx : x ∈ V) :
    DifferentiableAt ℝ (fderiv ℝ (R.F t)) x := by
  have h := (R.contDiffOn t).fderiv_of_isOpen hV (m := 1)
    (by rw [one_add_one_eq_two]
        simpa using (WithTop.coe_le_coe.2 hk : ((2 : ℕ∞) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞)))
  exact (h.differentiableOn one_ne_zero x hx).differentiableAt (hV.mem_nhds hx)

/-- A uniform bound on the second derivatives over `T × IB(x̄, δ)`. -/
theorem exists_bound_fderiv_fderiv (hk : 2 ≤ k) {x : E} {δ : ℝ} (hδV : closedBall x δ ⊆ V) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ t, ∀ y ∈ closedBall x δ, ‖fderiv ℝ (fderiv ℝ (R.F t)) y‖ ≤ ρ := by
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall x δ)).exists_bound_of_continuousOn
    ((R.continuousOn_iteratedFDeriv_two hk).mono (prod_mono Subset.rfl hδV))
  refine ⟨max C 0, le_max_right _ _, fun t y hy ↦ ?_⟩
  have h := hC (t, y) ⟨trivial, hy⟩
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact h.trans (le_max_left _ _)

omit [FiniteDimensional ℝ E] in
/-- The first-order expansion of each `f_t` is accurate to `ρ|x - w|²` on `IB(x̄, δ)`. -/
theorem quadratic_lower_bound (hk : 2 ≤ k) (hV : IsOpen V) {x₀ : E} {δ ρ : ℝ}
    (hδV : closedBall x₀ δ ⊆ V)
    (hρ : ∀ t, ∀ y ∈ closedBall x₀ δ, ‖fderiv ℝ (fderiv ℝ (R.F t)) y‖ ≤ ρ) (t : R.T) {x w : E}
    (hx : x ∈ closedBall x₀ δ) (hw : w ∈ closedBall x₀ δ) :
    R.F t w + fderiv ℝ (R.F t) w (x - w) - ρ * ‖x - w‖ ^ 2 ≤ R.F t x := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  have hseg : segment ℝ w x ⊆ closedBall x₀ δ := (convex_closedBall x₀ δ).segment_subset hw hx
  have hρ0 : 0 ≤ ρ := (norm_nonneg (fderiv ℝ (fderiv ℝ (R.F t)) w)).trans (hρ t w hw)
  -- the gradient map is `ρ`-Lipschitz on the ball
  have hLip : LipschitzOnWith ρ.toNNReal (fderiv ℝ (R.F t)) (closedBall x₀ δ) :=
    (convex_closedBall x₀ δ).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      (fun y hy ↦ R.differentiableAt_fderiv hk hV t (hδV hy))
      (fun y hy ↦ by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hρ0]
        exact hρ t y hy)
  set L := fderiv ℝ (R.F t) w with hL
  set g : E → ℝ := fun y ↦ R.F t y - L y with hg
  have hgd : ∀ y ∈ segment ℝ w x, HasFDerivAt g (fderiv ℝ (R.F t) y - L) y := fun y hy ↦
    (R.differentiableAt hk1 hV t (hδV (hseg hy))).hasFDerivAt.sub L.hasFDerivAt
  have hbound : ∀ y ∈ segment ℝ w x, ‖fderiv ℝ (R.F t) y - L‖ ≤ ρ * ‖x - w‖ := by
    intro y hy
    have h1 := hLip.dist_le_mul y (hseg hy) w hw
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hρ0] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hρ0)
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    have : a • w + b • x - w = b • (x - w) := by
      rw [show a = 1 - b by linarith, smul_sub, sub_smul, one_smul]
      abel
    rw [this, norm_smul, Real.norm_of_nonneg hb]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have hmv := (convex_segment w x).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y hy ↦ (hgd y hy).hasFDerivWithinAt) hbound (left_mem_segment ℝ w x)
    (right_mem_segment ℝ w x)
  have hmv' : |g x - g w| ≤ ρ * ‖x - w‖ * ‖x - w‖ := by rwa [← Real.norm_eq_abs]
  have hgx : g x - g w = R.F t x - R.F t w - L (x - w) := by
    simp only [hg, map_sub]
    ring
  rw [hgx] at hmv'
  have := (abs_le.1 hmv').1
  nlinarith [sq_nonneg ‖x - w‖]

/-- The jointly smooth quadratic `(a, L, w; x) ↦ a + L(x - w) - ρ|x - w|²`. -/
noncomputable def quadraticModel (ρ : ℝ) (q : (ℝ × (E →L[ℝ] ℝ) × E) × E) : ℝ :=
  q.1.1 + q.1.2.1 (q.2 - q.1.2.2) - ρ * ‖q.2 - q.1.2.2‖ ^ 2

omit [FiniteDimensional ℝ E] in
theorem contDiff_quadraticModel (ρ : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (quadraticModel (E := E) ρ) := by
  unfold quadraticModel
  have h1 : ContDiff ℝ n fun q : (ℝ × (E →L[ℝ] ℝ) × E) × E ↦ q.2 - q.1.2.2 :=
    contDiff_snd.sub (contDiff_snd.comp (contDiff_snd.comp contDiff_fst))
  have h2 : ContDiff ℝ n fun q : (ℝ × (E →L[ℝ] ℝ) × E) × E ↦ q.1.2.1 :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_fst)
  exact ((contDiff_fst.comp contDiff_fst).add (h2.clm_apply h1)).sub
    (contDiff_const.mul (h1.norm_sq ℝ))

/-- **Theorem 10.33** (proof): the quadratic representation of a lower-`C²` function around
`x₀`, on the open ball `ball x₀ δ`. -/
noncomputable def quadraticRepresentation (hk : 2 ≤ k) (hV : IsOpen V) {x₀ : E} {δ ρ : ℝ}
    (hδV : closedBall x₀ δ ⊆ V)
    (hρ : ∀ t, ∀ y ∈ closedBall x₀ δ, ‖fderiv ℝ (fderiv ℝ (R.F t)) y‖ ≤ ρ) :
    LowerRepresentation ⊤ f (ball x₀ δ) where
  T := R.T × closedBall x₀ δ
  compactSpace := by
    haveI : CompactSpace (closedBall x₀ δ) := isCompact_iff_compactSpace.1 (isCompact_closedBall x₀ δ)
    infer_instance
  F := fun s x ↦ quadraticModel ρ ((R.F s.1 s.2, fderiv ℝ (R.F s.1) s.2, (s.2 : E)), x)
  contDiffOn := fun s ↦
    ((contDiff_quadraticModel ρ).comp (contDiff_const.prodMk contDiff_id)).contDiffOn
  continuousOn_iteratedFDeriv := fun j _ ↦ by
    have hk1 : 1 ≤ k := le_trans (by norm_num) hk
    have hc : Continuous fun s : R.T × closedBall x₀ δ ↦
        ((R.F s.1 s.2, fderiv ℝ (R.F s.1) s.2, (s.2 : E)) : ℝ × (E →L[ℝ] ℝ) × E) := by
      have hmap : Continuous fun s : R.T × closedBall x₀ δ ↦ ((s.1, (s.2 : E)) : R.T × E) :=
        continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
      have hmem : ∀ s : R.T × closedBall x₀ δ, ((s.1, (s.2 : E)) : R.T × E) ∈ univ ×ˢ V :=
        fun s ↦ ⟨trivial, hδV s.2.2⟩
      refine (R.continuousOn_val.comp_continuous hmap hmem).prodMk
        (((R.continuousOn_fderiv hk1).comp_continuous hmap hmem).prodMk
          (continuous_subtype_val.comp continuous_snd))
    have hP := continuous_iteratedFDeriv_param (contDiff_quadraticModel (E := E) ρ (n := ∞))
      (j := j) (by exact_mod_cast le_top)
    exact (hP.comp (hc.prodMap continuous_id)).continuousOn
  le := fun s x hx ↦ by
    have h := R.quadratic_lower_bound hk hV hδV hρ s.1 (ball_subset_closedBall hx) s.2.2
    exact h.trans (R.le s.1 x (hδV (ball_subset_closedBall hx)))
  exists_eq := fun x hx ↦ by
    obtain ⟨t, ht⟩ := R.exists_eq x (hδV (ball_subset_closedBall hx))
    refine ⟨(t, ⟨x, ball_subset_closedBall hx⟩), ?_⟩
    simp [quadraticModel, ht]

end LowerRepresentation

omit [FiniteDimensional ℝ E] in
/-- Lower-`Cᵏ` implies lower-`Cᵐ` for `m ≤ k`. -/
theorem IsLowerCOn.mono {k m : ℕ∞} {f : E → ℝ} {O : Set E} (hf : IsLowerCOn k f O)
    (hmk : m ≤ k) : IsLowerCOn m f O := by
  intro x hx
  obtain ⟨V, hV, hxV, hVO, ⟨R⟩⟩ := hf x hx
  exact ⟨V, hV, hxV, hVO, ⟨LowerRepresentation.mk R.T R.F
    (fun t ↦ (R.contDiffOn t).of_le (by exact_mod_cast hmk))
    (fun j hj ↦ R.continuousOn_iteratedFDeriv j (hj.trans hmk)) R.le R.exists_eq⟩⟩

/-- **Corollary 10.34**: a lower-`C²` function is lower-`C^∞`. -/
theorem IsLowerCOn.lowerCInfty {f : E → ℝ} {O : Set E} (hf : IsLowerCOn 2 f O) :
    IsLowerCOn ⊤ f O := by
  intro x hx
  obtain ⟨V, hV, hxV, hVO, ⟨R⟩⟩ := hf x hx
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV x hxV
  have hδV : closedBall x (r / 2) ⊆ V := (closedBall_subset_ball (half_lt_self hr)).trans hrV
  obtain ⟨ρ, -, hρ⟩ := R.exists_bound_fderiv_fderiv le_rfl hδV
  exact ⟨ball x (r / 2), isOpen_ball, mem_ball_self (half_pos hr),
    ball_subset_closedBall.trans (hδV.trans hVO), ⟨R.quadraticRepresentation le_rfl hV hδV hρ⟩⟩

/-- **Corollary 10.34**: for `k ≥ 2` the lower-`Cᵏ` functions are exactly the lower-`C²`
functions. -/
theorem isLowerCOn_iff_two {k : ℕ∞} (hk : 2 ≤ k) {f : E → ℝ} {O : Set E} :
    IsLowerCOn k f O ↔ IsLowerCOn 2 f O :=
  ⟨fun h ↦ h.mono hk, fun h ↦ h.lowerCInfty.mono le_top⟩

/-- **Theorem 10.33** (lower-`C²` ⇒ convex minus quadratic): around each point of `O` a
lower-`C²` function `f` agrees on a ball with `g - ρ|·|²` for a finite convex `g`. -/
theorem IsLowerCOn.exists_convex_sub_quadratic {f : E → ℝ} {O : Set E} (hf : IsLowerCOn 2 f O) :
    ∀ x ∈ O, ∃ δ > 0, ball x δ ⊆ O ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧
      ConvexOn ℝ (ball x δ) (fun y ↦ f y + ρ * ‖y‖ ^ 2) := by
  intro x hx
  obtain ⟨V, hV, hxV, hVO, ⟨R⟩⟩ := hf x hx
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV x hxV
  have hδV : closedBall x (r / 2) ⊆ V := (closedBall_subset_ball (half_lt_self hr)).trans hrV
  obtain ⟨ρ, hρ0, hρ⟩ := R.exists_bound_fderiv_fderiv le_rfl hδV
  refine ⟨r / 2, half_pos hr, ball_subset_closedBall.trans (hδV.trans hVO), ρ, hρ0,
    convex_ball x (r / 2), ?_⟩
  intro y hy z hz a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  set w := a • y + (1 - a) • z with hw
  have hwB : w ∈ closedBall x (r / 2) :=
    ball_subset_closedBall ((convex_ball x (r / 2)) hy hz ha hb hab)
  obtain ⟨t, ht⟩ := R.exists_eq w (hδV hwB)
  set L := fderiv ℝ (R.F t) w with hL
  have hlow : ∀ v ∈ ball x (r / 2), R.F t w + (L v - L w) - ρ * ‖w‖ ^ 2 + 2 * ρ * ⟪v, w⟫_ℝ ≤
      f v + ρ * ‖v‖ ^ 2 := by
    intro v hv
    have h1 := R.quadratic_lower_bound le_rfl hV hδV hρ t (ball_subset_closedBall hv) hwB
    have h2 := R.le t v (hδV (ball_subset_closedBall hv))
    have h3 : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - 2 * ⟪v, w⟫_ℝ + ‖w‖ ^ 2 := norm_sub_sq_real v w
    rw [map_sub] at h1
    nlinarith [h1, h2, h3]
  have e1 : L w = a * L y + (1 - a) * L z := by
    rw [hw, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have e2 : 2 * ρ * ⟪w, w⟫_ℝ = a * (2 * ρ * ⟪y, w⟫_ℝ) + (1 - a) * (2 * ρ * ⟪z, w⟫_ℝ) := by
    have : ⟪w, w⟫_ℝ = a * ⟪y, w⟫_ℝ + (1 - a) * ⟪z, w⟫_ℝ := by
      calc ⟪w, w⟫_ℝ = ⟪a • y + (1 - a) • z, w⟫_ℝ := by rw [← hw]
        _ = _ := by rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [this]
    ring
  have e3 : ⟪w, w⟫_ℝ = ‖w‖ ^ 2 := real_inner_self_eq_norm_sq w
  have hy' := mul_le_mul_of_nonneg_left (hlow y hy) ha
  have hz' := mul_le_mul_of_nonneg_left (hlow z hz) hb
  have hfw : f w = R.F t w := ht.symm
  show f w + ρ * ‖w‖ ^ 2 ≤ a • (f y + ρ * ‖y‖ ^ 2) + (1 - a) • (f z + ρ * ‖z‖ ^ 2)
  rw [smul_eq_mul, smul_eq_mul]
  nlinarith [hy', hz', e1, e2, e3, hfw]

end RW
