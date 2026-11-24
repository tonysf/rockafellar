/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2D: Distance functions, projections and proximal mappings

This file formalizes Example 2.25 and Theorem 2.26 of Rockafellar–Wets.

* Example 2.25: the distance function `d_C = infDist · C` of a convex set is
  convex; for a nonempty closed convex `C` the projection mapping
  `projMapping C` (Chapter 5) is single-valued and continuous, indeed
  nonexpansive.
* Theorem 2.26: for a proper lsc convex `f` on a finite-dimensional Euclidean
  space, `f` is prox-bounded with threshold `∞`; the proximal mapping is
  single-valued and jointly continuous in `(λ, x)`; and the envelope `e_λ f`
  is convex and continuously differentiable with `∇e_λ f(x) = λ⁻¹(x - P_λ f(x))`.
  Single-valuedness, the gradient formula and `C¹` smoothness are the Chapter 12
  results `proximalMappingEReal_eq_singleton_of_convex`,
  `hasGradientAt_moreauEnvelopeReal` and `moreauEnvelope_yosida`; joint
  continuity is Theorem 12.32 for a constant sequence.
-/

import RockafellarWets.Chapter2.ConvexOperations
import RockafellarWets.Chapter5.ProjectionMappings
import RockafellarWets.Chapter12.MoreauYosida
import RockafellarWets.Chapter12.MonotoneGraphicalConvergence

open Set Filter Topology Metric
open scoped InnerProductSpace

noncomputable section

namespace RW

/-! ## Example 2.25 -/

section Distance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Example 2.25**: the distance function of a convex set is convex. -/
theorem convexOn_infDist {C : Set E} (hC : Convex ℝ C) :
    ConvexOn ℝ univ (fun x ↦ infDist x C) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  simp only [smul_eq_mul]
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  obtain ⟨c, hc, hxc⟩ := (infDist_lt_iff hne).mp (lt_add_of_pos_right (infDist x C) hε)
  obtain ⟨c', hc', hyc⟩ := (infDist_lt_iff hne).mp (lt_add_of_pos_right (infDist y C) hε)
  have hmem : a • c + b • c' ∈ C := hC hc hc' ha hb hab
  calc infDist (a • x + b • y) C ≤ dist (a • x + b • y) (a • c + b • c') :=
        infDist_le_dist_of_mem hmem
    _ ≤ a * dist x c + b * dist y c' := by
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm,
          show a • x + b • y - (a • c + b • c') = a • (x - c) + b • (y - c') by module]
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ < a * (infDist x C + ε) + b * (infDist y C + ε) := by
        rcases ha.eq_or_lt with rfl | ha'
        · simp only [zero_add] at hab
          subst hab
          simpa using hyc
        · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxc ha')
            (mul_le_mul_of_nonneg_left hyc.le hb)
    _ = a * infDist x C + b * infDist y C + ε := by
        rw [mul_add, mul_add, add_add_add_comm, ← add_mul, hab, one_mul]

/-- With the book's convention `d_∅ ≡ ∞`, the distance function of the empty
set is also convex. -/
theorem isConvexRelative_const_top : IsConvexRelative univ (fun _ : E ↦ (⊤ : EReal)) :=
  fun _ _ _ _ _ hτ0 _ ↦ by
    rw [infAddition_convexCombination_right_top hτ0]

end Distance

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Nearest points in a convex set are characterized by the variational
inequality `⟪x - p, w - p⟫ ≤ 0`. -/
theorem inner_sub_le_zero_of_mem_projMapping {C : Set E} (hC : Convex ℝ C) {x p : E}
    (hp : p ∈ projMapping C x) : ∀ w ∈ C, ⟪x - p, w - p⟫_ℝ ≤ 0 := by
  rw [← norm_eq_iInf_iff_real_inner_le_zero hC hp.1]
  haveI : Nonempty C := ⟨⟨p, hp.1⟩⟩
  have hbdd : BddBelow (range fun w : C ↦ ‖x - w‖) := ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩
  apply le_antisymm
  · refine le_ciInf fun w ↦ ?_
    rw [norm_sub_rev x p, norm_sub_rev x (w : E)]
    exact hp.2 w w.2
  · exact ciInf_le hbdd ⟨p, hp.1⟩

/-- Projections onto a convex set are nonexpansive. -/
theorem norm_sub_le_of_mem_projMapping {C : Set E} (hC : Convex ℝ C) {x y p q : E}
    (hp : p ∈ projMapping C x) (hq : q ∈ projMapping C y) : ‖p - q‖ ≤ ‖x - y‖ := by
  have h1 := inner_sub_le_zero_of_mem_projMapping hC hp q hq.1
  have h2 := inner_sub_le_zero_of_mem_projMapping hC hq p hp.1
  have key : ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ := by
    have e : ⟪x - y, p - q⟫_ℝ - ‖p - q‖ ^ 2 = -⟪x - p, q - p⟫_ℝ - ⟪y - q, p - q⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq]
      have : q - p = -(p - q) := (neg_sub p q).symm
      rw [this, inner_neg_right]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    linarith
  rcases (norm_nonneg (p - q)).eq_or_lt with h | h
  · rw [← h]
    exact norm_nonneg _
  · have := key.trans (real_inner_le_norm _ _)
    nlinarith

/-- **Example 2.25**: for a nonempty closed convex set in a complete inner
product space (in particular `ℝⁿ`), the projection mapping `P_C` is
single-valued, and the resulting map is nonexpansive, hence continuous. -/
theorem exists_projection_of_convex [CompleteSpace E] {C : Set E} (hC : Convex ℝ C)
    (hcl : IsClosed C) (hne : C.Nonempty) :
    ∃ P : E → E, (∀ x, projMapping C x = {P x}) ∧ LipschitzWith 1 P ∧ Continuous P := by
  have hmem : ∀ x, ∃ p, p ∈ projMapping C x := by
    intro x
    obtain ⟨v, hv, hveq⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hC x
    have hbdd : BddBelow (range fun w : C ↦ ‖x - w‖) := ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩
    refine ⟨v, hv, fun w' hw' ↦ ?_⟩
    rw [norm_sub_rev v x, norm_sub_rev w' x, hveq]
    exact ciInf_le hbdd ⟨w', hw'⟩
  choose P hP using hmem
  have huniq : ∀ x q, q ∈ projMapping C x → q = P x := by
    intro x q hq
    have := norm_sub_le_of_mem_projMapping hC hq (hP x)
    rw [sub_self, norm_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hlip : LipschitzWith 1 P := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact norm_sub_le_of_mem_projMapping hC (hP x) (hP y)
  refine ⟨P, fun x ↦ ?_, hlip, hlip.continuous⟩
  ext q
  exact ⟨fun hq ↦ huniq x q hq, fun hq ↦ hq ▸ hP x⟩

end Projection

/-! ## Theorem 2.26 -/

section Proximal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Adding a real convex function to a convex extended-real function preserves
convexity. -/
theorem IsConvexRelative.add_convexOn {F : Type*} [AddCommGroup F] [Module ℝ F]
    {f : F → EReal} (hf : IsConvexRelative univ f) {h : F → ℝ} (hh : ConvexOn ℝ univ h) :
    IsConvexRelative univ (fun x ↦ f x + (h x : EReal)) := by
  rw [isConvexRelative_iff_lt convex_univ]
  intro x₀ _ x₁ _ α₀ α₁ h₀ h₁ τ hτ0 hτ1
  have h₀' : f x₀ < ((α₀ - h x₀ : ℝ) : EReal) := by
    rw [EReal.coe_sub]
    exact EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
      |>.mpr h₀
  have h₁' : f x₁ < ((α₁ - h x₁ : ℝ) : EReal) := by
    rw [EReal.coe_sub]
    exact EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
      |>.mpr h₁
  have hf' := (isConvexRelative_iff_lt convex_univ f).mp hf (mem_univ x₀) (mem_univ x₁) h₀' h₁'
    hτ0 hτ1
  have hh' := hh.2 (mem_univ x₀) (mem_univ x₁) (by linarith : (0 : ℝ) ≤ 1 - τ) hτ0.le (by ring)
  simp only [smul_eq_mul] at hh'
  calc f ((1 - τ) • x₀ + τ • x₁) + (h ((1 - τ) • x₀ + τ • x₁) : EReal)
      ≤ (((1 - τ) * (α₀ - h x₀) + τ * (α₁ - h x₁) : ℝ) : EReal) +
          (((1 - τ) * h x₀ + τ * h x₁ : ℝ) : EReal) :=
        add_le_add hf' (EReal.coe_le_coe_iff.mpr hh')
    _ = (((1 - τ) * α₀ + τ * α₁ : ℝ) : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        ring

/-- **Theorem 2.26**: a proper lsc convex function is prox-bounded with
threshold `∞` (also `proxThreshold_eq_top_of_convex` in Chapter 14). -/
theorem isProxBounded_and_proxThreshold_eq_top_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    IsProxBounded f ∧ proxThreshold f = ⊤ := by
  have hadm : ∀ lam : ℝ, 0 < lam →
      ⊥ < ⨅ w : E, f w + ((1 / (2 * lam)) * ‖w - 0‖ ^ 2 : ℝ) := by
    intro lam hlam
    have h := (moreauEnvelopeReal_eq_of_convex hp hl hc hlam 0).1
    change ⊥ < moreauEnvelopeEReal f lam 0
    rw [h]
    exact EReal.bot_lt_coe _
  refine ⟨⟨1, one_pos, 0, hadm 1 one_pos⟩, (EReal.eq_top_iff_forall_lt _).mpr fun y ↦ ?_⟩
  have hpos : 0 < max y 0 + 1 := by positivity
  calc (y : EReal) < ((max y 0 + 1 : ℝ) : EReal) :=
        EReal.coe_lt_coe_iff.mpr (by linarith [le_max_left y 0])
    _ ≤ proxThreshold f :=
        le_iSup₂_of_le (f := fun (lam : ℝ) (_ : lam > 0 ∧ ∃ x : E,
          (⨅ w : E, f w + ((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ)) > ⊥) ↦ (lam : EReal))
          (max y 0 + 1) ⟨hpos, 0, hadm _ hpos⟩ le_rfl

/-- **Theorem 2.26(a)**: the proximal mapping of a proper lsc convex function
is single-valued. -/
theorem proximalMappingEReal_singleton_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam)
    (x : E) : proximalMappingEReal f lam x = {resolventMap (subdifferential f) lam x} :=
  proximalMappingEReal_eq_singleton_of_convex hp hl hc hlam x

/-- **Theorem 2.26(a)**: `P_λ f(x) → P_λ̄ f(x̄)` whenever `(λ, x) → (λ̄, x̄)` with
`λ̄ > 0` (sequential form, Theorem 12.32 with a constant sequence). -/
theorem tendsto_proximal_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℕ → ℝ} {lam₀ : ℝ}
    (hlam : ∀ n, 0 < lam n) (hlam₀ : 0 < lam₀) (hlim : Tendsto lam atTop (𝓝 lam₀))
    {x : ℕ → E} {x₀ : E} (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto (fun n ↦ resolventMap (subdifferential f) (lam n) (x n)) atTop
      (𝓝 (resolventMap (subdifferential f) lam₀ x₀)) := by
  have hT := svMaximalMonotone_subdifferential_of_convex hp hl hc
  refine tendsto_resolventMap_of_subset_graphicalInnerLimit (fun _ ↦ hT) hT ?_ hlam hlam₀ hlim hx
  intro y v hv
  exact mem_graphicalInnerLimit_iff.mpr ⟨fun _ ↦ y, fun _ ↦ v, Eventually.of_forall fun _ ↦ hv,
    tendsto_const_nhds, tendsto_const_nhds⟩

/-- **Theorem 2.26(a)**: the map `(λ, x) ↦ P_λ f(x)` is continuous on
`(0, ∞) × ℝⁿ`; in particular each `P_λ f` is continuous. -/
theorem continuousOn_proximal_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    ContinuousOn (fun q : ℝ × E ↦ resolventMap (subdifferential f) q.1 q.2) {q | 0 < q.1} := by
  intro q hq
  refine ContinuousAt.continuousWithinAt ?_
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro u hu
  have h1 : Tendsto (fun n ↦ (u n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hu
  have h2 : Tendsto (fun n ↦ (u n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hu
  have hev : ∀ᶠ n in atTop, 0 < (u n).1 := h1.eventually (lt_mem_nhds hq)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hshift := tendsto_proximal_of_convex hp hl hc (lam := fun n ↦ (u (n + N)).1)
    (fun n ↦ hN _ (Nat.le_add_left N n)) hq ((tendsto_add_atTop_iff_nat N).mpr h1)
    (x := fun n ↦ (u (n + N)).2) ((tendsto_add_atTop_iff_nat N).mpr h2)
  exact (tendsto_add_atTop_iff_nat N).mp hshift

/-- **Theorem 2.26(b)**: the Moreau envelope of a proper lsc convex function is
convex. -/
theorem convexOn_moreauEnvelopeReal {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam) :
    ConvexOn ℝ univ (moreauEnvelopeReal f lam) := by
  have hf : IsConvexRelative univ f := (isConvexRelative_univ_iff f).mpr hc
  have hq : ConvexOn ℝ univ (fun p : E × E ↦ (1 / (2 * lam)) * ‖p.1 - p.2‖ ^ 2) := by
    have hn : ConvexOn ℝ univ (fun v : E ↦ ‖v‖ ^ 2) := by
      have := (convexOn_norm (E := E) convex_univ).pow (fun x _ ↦ norm_nonneg x) 2
      simpa [Pi.pow_def] using this
    have hcomp := hn.comp_linearMap (LinearMap.fst ℝ E E - LinearMap.snd ℝ E E)
    simp only [preimage_univ] at hcomp
    have := hcomp.smul (by positivity : (0 : ℝ) ≤ 1 / (2 * lam))
    simpa [Function.comp_def, smul_eq_mul] using this
  have hg : IsConvexRelative univ
      (fun p : E × E ↦ f p.1 + (((1 / (2 * lam)) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal)) :=
    (hf.comp_affine (LinearMap.fst ℝ E E) 0 |>.congr convex_univ (fun p _ ↦ by simp)).add_convexOn
      hq
  have hv := isConvexRelative_valueFunction hg
  have heq : valueFunction
      (fun p : E × E ↦ f p.1 + (((1 / (2 * lam)) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal)) =
      fun x ↦ (moreauEnvelopeReal f lam x : EReal) := by
    funext x
    rw [← (moreauEnvelopeReal_eq_of_convex hp hl hc hlam x).1]
    rfl
  rw [heq] at hv
  exact (isConvexRelative_coe_iff convex_univ _).mp hv

/-- **Theorem 2.26(b)**: the Moreau envelope of a proper lsc convex function is
finite, convex and continuously differentiable with
`∇e_λ f(x) = λ⁻¹(x - P_λ f(x))`. -/
theorem moreauEnvelope_convex_smooth {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam) :
    (∀ x, moreauEnvelopeEReal f lam x = (moreauEnvelopeReal f lam x : EReal)) ∧
      ConvexOn ℝ univ (moreauEnvelopeReal f lam) ∧ ContDiff ℝ 1 (moreauEnvelopeReal f lam) ∧
      ∀ x, HasGradientAt (moreauEnvelopeReal f lam)
        (lam⁻¹ • (x - resolventMap (subdifferential f) lam x)) x :=
  ⟨(moreauEnvelope_yosida hp hl hc hlam).1, convexOn_moreauEnvelopeReal hp hl hc hlam,
    (moreauEnvelope_yosida hp hl hc hlam).2.2.2.2.2,
    hasGradientAt_moreauEnvelopeReal hp hl hc hlam⟩

end Proximal

end RW
