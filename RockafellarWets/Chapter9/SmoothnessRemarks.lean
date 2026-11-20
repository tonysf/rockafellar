/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: the convex cases of 9.20 and 9.21, and the proximal form of 9.22

* A finite convex function `f` on an open convex set `O` is strictly continuous
  (9.14) and regular (7.27) at every point of `O`
  (`convexOn_eRealStrictlyContinuousAt_and_regular`).  Regularity is first
  obtained for the extension of `f` by `∞` off `O`, whose epigraph is convex, and
  then transferred, since the two epigraphs agree near the point.
* **Corollary 9.20**, convex case: such `f` is strictly differentiable wherever
  it is differentiable (`convexOn_hasStrictFDerivAt_of_differentiableAt`) and its
  gradient is continuous relative to the set of these points
  (`convexOn_continuousOn_gradient`).
* **Corollary 9.21**, convex case: `convexOn_regularSubdifferential_neg_eq`,
  `convexOn_neg_subdifferential_neg_eq`, `convexOn_neg_subdifferential_neg_subset`.
* The remark after **Exercise 9.22**: in condition (c) the regular subgradients
  may be replaced by proximal subgradients (`eventually_const_iff_proximal`),
  because every limiting subgradient is a limit of proximal subgradients at
  nearby points with nearby values (8.47(a)).
-/

import RockafellarWets.Chapter9.ConstancyCriterion
import RockafellarWets.Chapter9.ConvexLipschitzBounds
import RockafellarWets.Chapter7.MaxFunctionRegularity
import RockafellarWets.Chapter8.ProximalApproximation

open Filter Set Topology Metric
open scoped ENNReal NNReal InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem toReal_coe_fun (f : E → ℝ) : (fun y ↦ ((f y : EReal)).toReal) = f :=
  funext fun _ ↦ EReal.toReal_coe _

/-- A finite convex function on an open convex set is strictly continuous (9.14) and
regular (7.27) at every point of that set. -/
theorem convexOn_eRealStrictlyContinuousAt_and_regular {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ConvexOn ℝ O f) {x : E} (hx : x ∈ O) :
    ERealStrictlyContinuousAt (fun y ↦ (f y : EReal)) x ∧
      IsSubdifferentiallyRegularAt (fun y ↦ (f y : EReal)) x := by
  classical
  have hsc : ERealStrictlyContinuousAt (fun y ↦ (f y : EReal)) x := by
    refine ⟨Eventually.of_forall fun _ ↦ by rw [EReal.toReal_coe], ?_⟩
    show StrictlyContinuousAt (fun y ↦ ((f y : EReal)).toReal) x
    rw [toReal_coe_fun]
    exact strictlyContinuousAt_of_convexOn hO hf hx
  refine ⟨hsc, ?_⟩
  obtain ⟨F, hF⟩ : ∃ F : E → EReal, F = fun y ↦ if y ∈ O then (f y : EReal) else ⊤ := ⟨_, rfl⟩
  have hFeq : ∀ y ∈ O, F y = (f y : EReal) := fun y hy ↦ by rw [hF]; exact if_pos hy
  have hFout : ∀ y, y ∉ O → F y = ⊤ := fun y hy ↦ by rw [hF]; exact if_neg hy
  have hmemO : ∀ p ∈ epigraph F, p.1 ∈ O := fun p hp ↦ by
    by_contra h
    have h1 : F p.1 ≤ (p.2 : EReal) := hp
    rw [hFout _ h] at h1
    exact absurd h1 (not_le.2 (EReal.coe_lt_top _))
  have hFconv : Convex ℝ (epigraph F) := by
    intro p hp q hq a b ha hb hab
    have hp1 := hmemO p hp
    have hq1 := hmemO q hq
    have hp2 : f p.1 ≤ p.2 := by
      have h1 : F p.1 ≤ (p.2 : EReal) := hp
      rwa [hFeq _ hp1, EReal.coe_le_coe_iff] at h1
    have hq2 : f q.1 ≤ q.2 := by
      have h1 : F q.1 ≤ (q.2 : EReal) := hq
      rwa [hFeq _ hq1, EReal.coe_le_coe_iff] at h1
    have hmem : a • p.1 + b • q.1 ∈ O := hf.1 hp1 hq1 ha hb hab
    show F (a • p + b • q).1 ≤ (((a • p + b • q).2 : ℝ) : EReal)
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [hFeq _ (by simpa using hmem), EReal.coe_le_coe_iff]
    have h1 := hf.2 hp1 hq1 ha hb hab
    simp only [smul_eq_mul] at h1
    nlinarith [mul_le_mul_of_nonneg_left hp2 ha, mul_le_mul_of_nonneg_left hq2 hb]
  have hfcont : ContinuousOn f O := hf.continuousOn hO
  have hFcont : ContinuousOn F O :=
    (continuous_coe_real_ereal.comp_continuousOn hfcont).congr fun y hy ↦ hFeq y hy
  have hFlsc : IsLocallyLscAt F x :=
    isLocallyLscAt_of_lowerSemicontinuousOn hO
      (fun y hy ↦ (hFcont y hy).lowerSemicontinuousWithinAt) hx
      (by rw [hFeq x hx]; exact EReal.coe_ne_bot _) (by rw [hFeq x hx]; exact EReal.coe_ne_top _)
  have hFreg := (isSubdifferentiallyRegularAt_of_convex hFconv hFlsc).1
  refine ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _, ?_⟩
  have hW : {p : WithLp 2 (E × ℝ) | (l2ProdEquiv E p).1 ∈ O} ∈
      𝓝 (WithLp.toLp 2 (x, ((f x : EReal)).toReal)) :=
    (hO.preimage (continuous_fst.comp (l2ProdEquiv E).continuous)).mem_nhds hx
  have hset : l2Epigraph F ∩ {p : WithLp 2 (E × ℝ) | (l2ProdEquiv E p).1 ∈ O} =
      l2Epigraph (fun y ↦ (f y : EReal)) ∩ {p : WithLp 2 (E × ℝ) | (l2ProdEquiv E p).1 ∈ O} := by
    ext p
    simp only [mem_inter_iff, l2Epigraph, mem_preimage, epigraph, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [hFeq _ h2] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [← hFeq _ h2] at h1
      exact ⟨h1, h2⟩
  have hbase : (F x).toReal = ((f x : EReal)).toReal := by rw [hFeq x hx]
  have hreg := hFreg.2.2
  rw [hbase] at hreg
  exact (isClarkeRegularAt_congr_of_inter_eq hW hset).1 hreg

/-- **Corollary 9.20**, convex case: a finite convex function on an open convex set is strictly
differentiable at every point of that set where it is differentiable. -/
theorem convexOn_hasStrictGradientAt_of_differentiableAt {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ConvexOn ℝ O f) {x : E} (hx : x ∈ O) (hd : DifferentiableAt ℝ f x) :
    HasStrictGradientAt (fun y ↦ (f y : EReal)) (gradient f x) x := by
  have h := (convexOn_eRealStrictlyContinuousAt_and_regular hO hf hx).2
  have hd' : DifferentiableAt ℝ (fun y ↦ ((f y : EReal)).toReal) x := by
    rw [toReal_coe_fun]; exact hd
  have h1 := h.hasStrictGradientAt_of_differentiableAt
    (Eventually.of_forall fun _ ↦ by rw [EReal.toReal_coe]) hd'
  rwa [toReal_coe_fun] at h1

/-- **Corollary 9.20**, convex case, in Mathlib's form. -/
theorem convexOn_hasStrictFDerivAt_of_differentiableAt {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ConvexOn ℝ O f) {x : E} (hx : x ∈ O) (hd : DifferentiableAt ℝ f x) :
    HasStrictFDerivAt f (fderiv ℝ f x) x := by
  have h := (convexOn_hasStrictGradientAt_of_differentiableAt hO hf hx hd).2
  rw [toReal_coe_fun] at h
  rwa [← h.hasFDerivAt.fderiv] at h

/-- **Corollary 9.20**, convex case: relative to the set of points of `O` where the finite
convex function `f` is differentiable, the gradient mapping is continuous. -/
theorem convexOn_continuousOn_gradient {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ConvexOn ℝ O f) : ContinuousOn (gradient f) {x | x ∈ O ∧ DifferentiableAt ℝ f x} := by
  have hgrad : ∀ x ∈ {x | x ∈ O ∧ DifferentiableAt ℝ f x},
      HasStrictGradientAt (fun y ↦ (f y : EReal)) (gradient f x) x :=
    fun x hx ↦ convexOn_hasStrictGradientAt_of_differentiableAt hO hf hx.1 hx.2
  intro x hx
  refine tendsto_of_eventually_mem_subdifferential (hgrad x hx).eRealStrictlyContinuousAt
    (hgrad x hx).subdifferential_eq nhdsWithin_le_nhds ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [(hgrad z hz).subdifferential_eq]
  exact mem_singleton _

open Classical in
/-- **Corollary 9.21**, convex case: `∂̂(-f)(x̄) = {-∇f(x̄)}` or `∅` according as the finite
convex function `f` is or is not differentiable at `x̄ ∈ O`. -/
theorem convexOn_regularSubdifferential_neg_eq {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ConvexOn ℝ O f) {x : E} (hx : x ∈ O) :
    regularSubdifferential (fun y ↦ -(f y : EReal)) x =
      if DifferentiableAt ℝ f x then {-gradient f x} else ∅ := by
  obtain ⟨hsc, hreg⟩ := convexOn_eRealStrictlyContinuousAt_and_regular hO hf hx
  have h := regularSubdifferential_neg_eq hsc hreg
  rw [toReal_coe_fun] at h
  exact h

/-- **Corollary 9.21**, convex case: `-∂(-f)(x̄)` is the set of limits of gradients at nearby
points of differentiability. -/
theorem convexOn_neg_subdifferential_neg_eq {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ConvexOn ℝ O f) {x : E} (hx : x ∈ O) :
    -subdifferential (fun y ↦ -(f y : EReal)) x =
      {v | ∃ xs : ℕ → E, Tendsto xs atTop (𝓝 x) ∧ (∀ n, DifferentiableAt ℝ f (xs n)) ∧
        Tendsto (fun n ↦ gradient f (xs n)) atTop (𝓝 v)} := by
  have h := neg_subdifferential_neg_eq hO
    (fun _ hy ↦ convexOn_eRealStrictlyContinuousAt_and_regular hO hf hy) hx
  rw [toReal_coe_fun] at h
  exact h

/-- **Corollary 9.21**, convex case: `-∂(-f)(x̄) ⊆ ∂f(x̄)`. -/
theorem convexOn_neg_subdifferential_neg_subset {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ConvexOn ℝ O f) {x : E} (hx : x ∈ O) :
    -subdifferential (fun y ↦ -(f y : EReal)) x ⊆ subdifferential (fun y ↦ (f y : EReal)) x :=
  neg_subdifferential_neg_subset hO
    (fun _ hy ↦ convexOn_eRealStrictlyContinuousAt_and_regular hO hf hy) hx

/-- The remark after **Exercise 9.22**: in condition (c), regular subgradients may be
replaced by proximal subgradients. -/
theorem eventually_const_iff_proximal {f : E → EReal} {x : E} (hl : LowerSemicontinuous f)
    (hp : IsProper f) (hx : x ∈ effectiveDomain f) :
    (∀ᶠ y in 𝓝 x, f y = f x) ↔
      ∃ ε > 0, ∀ y, ‖y - x‖ ≤ ε → (((f x).toReal - ε : ℝ) : EReal) ≤ f y →
        f y ≤ (((f x).toReal + ε : ℝ) : EReal) → (proximalSubdifferential f y).Nonempty →
          proximalSubdifferential f y = {0} := by
  have htfae := tfae_eventually_const hl hp hx
  constructor
  · intro ha
    obtain ⟨ε, hε, hc⟩ := (htfae.out 0 2).1 ha
    refine ⟨ε, hε, fun y hy h1 h2 hne ↦ ?_⟩
    obtain ⟨u, hu⟩ := hne
    have hreg := hc y hy h1 h2 ⟨u, proximalSubdifferential_subset_regularSubdifferential f y hu⟩
    refine Subset.antisymm (fun v hv ↦ ?_) (singleton_subset_iff.2 ?_)
    · rw [← hreg]
      exact proximalSubdifferential_subset_regularSubdifferential f y hv
    · have hu' := proximalSubdifferential_subset_regularSubdifferential f y hu
      rw [hreg, mem_singleton_iff] at hu'
      rw [← hu']
      exact hu
  · rintro ⟨ε, hε, hc⟩
    have hcond : ∃ ε > 0, ∀ y, ‖y - x‖ ≤ ε → (((f x).toReal - ε : ℝ) : EReal) ≤ f y →
        f y ≤ (((f x).toReal + ε : ℝ) : EReal) → (regularSubdifferential f y).Nonempty →
          regularSubdifferential f y = {0} := by
      refine ⟨ε / 2, half_pos hε, fun y hy h1 h2 hne ↦ ?_⟩
      have hy1 : f y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
      have hy2 : f y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
      have hyc : f y = (((f y).toReal : ℝ) : EReal) := (EReal.coe_toReal hy2 hy1).symm
      have h1' : (f x).toReal - ε / 2 ≤ (f y).toReal := by
        rw [hyc] at h1; exact EReal.coe_le_coe_iff.1 h1
      have h2' : (f y).toReal ≤ (f x).toReal + ε / 2 := by
        rw [hyc] at h2; exact EReal.coe_le_coe_iff.1 h2
      have hzero : ∀ v ∈ regularSubdifferential f y, v = 0 := by
        intro v hv
        have hlim := regularSubdifferential_subset_subdifferential f y hv
        refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ ↦ ?_)
        obtain ⟨x', v', c', hx'c, hx', hc', hv', hvv⟩ := exists_mem_proximalSubdifferential_close hl
          hyc hlim (lt_min (half_pos hε) hδ)
        have hδ1 : min (ε / 2) δ ≤ ε / 2 := min_le_left _ _
        have hδ2 : min (ε / 2) δ ≤ δ := min_le_right _ _
        have hxx : ‖x' - x‖ ≤ ε := by
          have h3 : ‖x' - x‖ ≤ ‖x' - y‖ + ‖y - x‖ := by
            rw [show x' - x = (x' - y) + (y - x) by abel]; exact norm_add_le _ _
          linarith
        rw [abs_le] at hc'
        have hb1 : (((f x).toReal - ε : ℝ) : EReal) ≤ f x' := by
          rw [hx'c]; exact EReal.coe_le_coe_iff.2 (by linarith)
        have hb2 : f x' ≤ (((f x).toReal + ε : ℝ) : EReal) := by
          rw [hx'c]; exact EReal.coe_le_coe_iff.2 (by linarith)
        have hv'0 : v' = 0 := by
          have h3 := hc x' hxx hb1 hb2 ⟨v', hv'⟩
          rw [h3] at hv'
          exact hv'
        rw [hv'0, zero_sub, norm_neg] at hvv
        linarith
      obtain ⟨u, hu⟩ := hne
      exact Subset.antisymm (fun v hv ↦ mem_singleton_iff.2 (hzero v hv))
        (singleton_subset_iff.2 ((hzero u hu) ▸ hu))
    exact (htfae.out 0 2).2 hcond

end RW
