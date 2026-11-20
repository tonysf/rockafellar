/-
Copyright (c) 2026 Kai Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Lam

# Euclidean change of variables in epi-convergence

The argument proves domain invariance using stability of the inverse on
a compact ball, smooth approximation, and Brouwer’s fixed-point theorem.
Adapted for Lean 4.28 from Kai Lam’s invariance-of-domain proof.
https://github.com/leanprover-community/mathlib4/pull/36770
-/
import FixedPointTheorems.brouwer
import RockafellarWets.Chapter7.EpiOperations
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Complex.Tietze
import Mathlib.MeasureTheory.Function.Jacobian

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem differentiable_approx_of_continuous {δ : ℝ} (hδ : 0 < δ) {K : Set E}
    (hK : IsCompact K) (f : E → E) (hf : Continuous f) :
    ∃ P : E → E, Differentiable ℝ P ∧ ∀ x ∈ K, ‖P x - f x‖ < δ := by
  let F : C(E, E) := ⟨f, hf⟩
  have h := ContinuousMap.dense_setOf_contDiff (E := E) (F := E) F
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity uniformity_basis_dist.compactConvergenceUniformity)] at h
  obtain ⟨P, hp, hdist⟩ := h (K, δ) ⟨hK, hδ⟩
  change ContDiff ℝ ∞ (P : E → E) at hp
  change ∀ x ∈ K, dist (P x) (f x) < δ at hdist
  exact ⟨P, hp.differentiable (by simp), fun x hx ↦ by
    simpa only [dist_eq_norm] using hdist x hx⟩


/-- Stability of zero (Lemma 6). If `G` is a left inverse of `f` on the closed ball,
    and `Gtilde` is a continuous function on `f(Bⁿ)` with `‖G - Gtilde‖ ≤ 1` pointwise,
    then `Gtilde` has a zero in `f(Bⁿ)`. -/
private theorem stability_of_zero (f : E → E) (hf_cont : ContinuousOn f (closedBall 0 1))
    (G : C(E, E)) (hG_left_inv : ∀ x ∈ closedBall 0 1, G (f x) = x)
    (Gtilde : E → E) (hGtilde_cont : ContinuousOn Gtilde (f '' closedBall 0 1))
    (hbound : ∀ y ∈ f '' closedBall 0 1, ‖G y - Gtilde y‖ ≤ 1) :
    ∃ y ∈ f '' closedBall 0 1, Gtilde y = 0 := by
  let diff_fun : E → E := fun x => x - Gtilde (f x)
  have hMapsTo : Set.MapsTo diff_fun (closedBall 0 1) (closedBall 0 1) :=
    fun x hx => by grind [mem_closedBall_zero_iff]
  have diff_fun_cont_on : ContinuousOn diff_fun (closedBall 0 1) :=
    (continuousOn_id' _).sub (hGtilde_cont.comp hf_cont (mapsTo_image f _))
  obtain ⟨x, hx⟩ := brouwer_fixed_point _ (convex_closedBall _ _) (isCompact_closedBall _ _)
    ⟨0, by simp⟩ ⟨_, diff_fun_cont_on.mapsToRestrict hMapsTo⟩
  have hx_eq : diff_fun (x : E) = (x : E) := congr_arg Subtype.val hx
  grind

/-- Let `B^n` be the closed unit ball (closedBall 0 1).
Let `f : B^n → ℝ^n` be a continuous injective map.
Then `f(0)` lies in the interior of `f(B^n)`. -/
private theorem ball_image_mem_interior (f : E → E)
    (hf_cont : ContinuousOn f (closedBall 0 1)) (hf_inj : Set.InjOn f (closedBall 0 1))
    : f 0 ∈ interior (f '' (closedBall 0 1)) := by
  cases subsingleton_or_nontrivial E
  · have hne : (f '' closedBall (0 : E) 1).Nonempty := ⟨_, 0, by simp, rfl⟩
    rw [hne.eq_univ, interior_univ]
    trivial
  let FEquiv := Equiv.Set.imageOfInjOn f (closedBall 0 1) hf_inj
  let FInvCmap : C(f '' closedBall 0 1, (closedBall (0 : E) 1)) :=
  ⟨FEquiv.symm, Continuous.continuous_symm_of_equiv_compact_to_t2 (continuous_induced_rng.mpr <|
    ContinuousOn.restrict hf_cont)⟩
  have hballimageclosed : IsClosed (f '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn hf_cont).isClosed
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hballimageclosed FInvCmap
  have hG0 : G (f 0) = (0 : E) := by
    let fzero' : (f '' closedBall 0 1) := ⟨f 0, ⟨0, by simp, rfl⟩⟩
    have := congr($hG fzero')
    conv_lhs at this => simp [fzero']
    have H : (⟨f 0, ⟨0, by simp, rfl⟩⟩ : f '' closedBall 0 1) = FEquiv ⟨0, by simp⟩ :=
      Subtype.ext rfl
    simp [this, FInvCmap, fzero', H]
  let G' : C(E, E) := ⟨fun x => (G x : E), continuous_subtype_val.comp (ContinuousMap.continuous G)⟩
  have hG_eq : ∀ y (hy : y ∈ f '' closedBall 0 1), G y = FInvCmap ⟨y, hy⟩ := by
    grind [ContinuousMap.restrict_apply]
  have hG'_left_inv : ∀ x ∈ closedBall 0 1, G' (f x) = x := fun x hx =>
    (congr_arg Subtype.val (hG_eq (f x) (mem_image_of_mem f hx))).trans
    (congr_arg Subtype.val (FEquiv.symm_apply_apply ⟨x, hx⟩))
  have hStability_of_zero (Gtilde : E → E) (hGtilde : ContinuousOn Gtilde (f '' closedBall 0 1))
      (hy : ∀ y ∈ (f '' closedBall 0 1), ‖G y - Gtilde y‖ ≤ 1) :
      ∃ y ∈ f '' closedBall 0 1, Gtilde y = 0 :=
    stability_of_zero f hf_cont G' hG'_left_inv Gtilde hGtilde hy
  -- A point outside the image lets us push the nearby part of the image onto a sphere.
  by_contra hnotinterior
  have hG_cont_at_f0 : ContinuousAt (fun x => (G x : E)) (f 0) := Continuous.continuousAt
    (continuous_subtype_val.comp (ContinuousMap.continuous G))
  rw [continuousAt_iff] at hG_cont_at_f0
  obtain ⟨twoε, h2εpos, h2ε1⟩ := hG_cont_at_f0 0.1 (by norm_num)
  let ε : ℝ := twoε /2
  have hε1 : ε > 0 := half_pos h2εpos
  have h2εeq : twoε = 2 * ε := by ring
  obtain ⟨c, hc1, hc2⟩ : ∃ c, dist c (f 0) < ε ∧ c ∉ f '' closedBall 0 1 := by
    rw [mem_interior] at hnotinterior
    push_neg at hnotinterior
    specialize hnotinterior (ball (f 0) ε)
    simp only [isOpen_ball, mem_ball, dist_self, forall_const, imp_not_comm] at hnotinterior
    have hnotball := hnotinterior hε1
    rw [Set.not_subset] at hnotball
    obtain ⟨c, hc⟩ := hnotball
    exact ⟨c, ⟨mem_ball.mp hc.1, (Set.mem_compl_iff (f '' closedBall 0 1) c).mp hc.2⟩⟩
  have hG_small (y : E) (h : ‖y - c‖ ≤ ε) : ‖(G y : E)‖ ≤ 0.1 := by
    rw [dist_eq_norm] at hc1
    have hdist : ‖y - f 0‖ < 2 * ε := by
      have hineq := norm_add_le (y - c) (c - f 0)
      simp only [sub_add_sub_cancel] at hineq
      linarith
    grind [dist_zero_right, dist_eq_norm]
  let sigma1 : Set (E) := {y ∈ f '' closedBall 0 1 | ‖y - c‖ ≥ ε}
  let sigma2 : Set (E) := sphere c ε
  let sigma := sigma1 ∪ sigma2
  have hsigma1compact : IsCompact sigma1 :=
    ((isCompact_closedBall 0 1).image_of_continuousOn hf_cont).inter_right
      (isClosed_le continuous_const ((continuous_id.sub continuous_const).norm))
  have hsigmacompact : IsCompact sigma := IsCompact.union hsigma1compact (isCompact_sphere c ε)
  let Phi : (E) → (E) := fun y => c + (max (ε / ‖y - c‖) (1 : ℝ)) • (y - c)
  have hPhiimg (y : E) (hy : y ∈ f '' closedBall 0 1) : Phi y ∈ sigma := by
    by_cases h : ε < ‖y - c‖
    · have hyc : 0 < ‖y - c‖ := by linarith
      grind [max_eq_right_of_lt, one_smul, add_sub_cancel, div_lt_one hyc]
    · right
      simp only [not_lt] at h
      have hy_neq_c : c ≠ y := by
        by_contra h
        rw [← h] at hy
        exact hc2 hy
      have hleft : 1 ≤ ε / ‖y - c‖ :=
      (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy_neq_c)))).mpr h
      have hPhi : Phi y = c + (ε / ‖y - c‖) • (y - c) := by
        dsimp [Phi]
        rwa [max_eq_left]
      rw [hPhi]
      simp [sigma2, norm_smul, (sub_ne_zero_of_ne (Ne.symm hy_neq_c)), hε1.le]
  have hPhicont : ContinuousOn Phi (f '' closedBall 0 1) := by
    refine ContinuousOn.add continuousOn_const (ContinuousOn.smul ?_
    (ContinuousOn.sub (continuousOn_id' (f '' closedBall 0 1)) continuousOn_const))
    rw [continuousOn_iff_continuous_restrict]
    exact Continuous.max ((Continuous.div continuous_const (Continuous.norm
    (Continuous.sub continuous_subtype_val continuous_const)))
    (by grind [norm_eq_zero, sub_ne_zero])) continuous_const
  have hGavoids : ∀ y ∈ sigma1, G y ≠ (0 : (E)) := by
    intro y hy
    by_contra hGeq
    have hG_inj_on_image : Set.InjOn G (f '' closedBall 0 1) := by
      intro x hx y hy h
      have hx_eq : G x = FInvCmap ⟨x, hx⟩ := by grind
      have hy_eq : G y = FInvCmap ⟨y, hy⟩ := by grind
      rw [hx_eq, hy_eq] at h
      exact congr_arg Subtype.val (FEquiv.symm.injective h)
    have hyeq : y = f 0 := by
      have hf0_image : f 0 ∈ f '' closedBall 0 1 := ⟨0, by simp, rfl⟩
      have heq : G y = G (f 0) := SetCoe.ext (Eq.trans hGeq hG0.symm)
      exact hG_inj_on_image hy.1 hf0_image heq
    rw [Set.mem_sep_iff, hyeq] at hy
    rw [dist_eq_norm, ← norm_neg, neg_sub] at hc1
    linarith
  let normG : E → ℝ := fun y => ‖(G y : E)‖
  have hGconton : ContinuousOn G (f '' closedBall 0 1) := (ContinuousMap.continuous G).continuousOn
  have hgnormconton1 : ContinuousOn normG sigma1 :=
    ContinuousOn.norm (continuous_subtype_val.comp_continuousOn
    (ContinuousOn.mono hGconton (Set.sep_subset (f '' closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)))
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ : ∃ (δ : ℝ), 0 < δ ∧ δ < 0.1 ∧ ∀ y ∈ sigma1, δ ≤ ‖(G y : E)‖ := by
    by_cases hP : sigma1.Nonempty
    · obtain ⟨z, hz, hmin⟩ := IsCompact.exists_isMinOn hsigma1compact hP hgnormconton1
      let δ := min (normG z) (0.05)
      have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨norm_pos_iff.mpr (hGavoids z hz), by norm_num⟩
      have hδ_lt_0_1 : δ < 0.1 := (min_le_right _ 0.05).trans_lt (by norm_num)
      have hδ_lower : ∀ y ∈ sigma1, normG y ≥ δ := fun y hy => (min_le_left _ _).trans (hmin hy)
      exact ⟨δ, hδ_pos, hδ_lt_0_1, hδ_lower⟩
    · exact ⟨0.05, by norm_num, by norm_num, fun y hy ↦ False.elim (hP ⟨y, hy⟩)⟩
  -- A smooth approximation maps this sphere to a null set. A small translation
  -- then removes all zeros without changing the inverse by more than one.
  obtain ⟨P, hP_diff, hP_bound⟩ :=
    differentiable_approx_of_continuous hδ1 hsigmacompact (fun (y : E) => (G y : E)) (by fun_prop)
  have h0_notin_image : (0 : E) ∉ P '' sigma1 := by
    rintro ⟨y, hy, h⟩
    have hG : ‖(G y : E)‖ ≥ δ := hδ3 y hy
    have hP : ‖P y - G y‖ < δ := hP_bound y (Set.subset_union_left hy)
    simp only [h, _root_.zero_sub, norm_neg] at hP
    linarith
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hP_image_null : volume (P '' (sphere c ε)) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hP_diff.differentiableOn
    (MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume c (ne_of_gt hε1))
  obtain ⟨v, hvnorm, hv1, hv2⟩ : ∃ (v : E), ‖v‖ < δ ∧ ¬ v ∈ P '' sigma1 ∧ ¬ v ∈ P '' sigma2 := by
    have hclosed := (hsigma1compact.image hP_diff.continuous).isClosed
    obtain ⟨k, hk, hsub⟩ := Metric.mem_nhds_iff.mp
      (inter_mem (ball_mem_nhds (0 : E) hδ1) (hclosed.isOpen_compl.mem_nhds h0_notin_image))
    have hn : ¬ ball (0 : E) k ⊆ P '' sigma2 := by
      intro h
      exact (measure_ball_pos volume (0 : E) hk).not_ge (hP_image_null ▸ measure_mono h)
    obtain ⟨v, hv, hv'⟩ := Set.not_subset.mp hn
    exact ⟨v, mem_ball_zero_iff.mp (hsub hv).1, (hsub hv).2, hv'⟩
  let P' : C(E, E) := {toFun := fun y => P y - v, continuous_toFun := hP_diff.continuous.sub continuous_const}
  have hv_notin_sigma : v ∉ P '' sigma := by grind
  let Gtilde : E → E := fun y => P' (Phi y)
  have hGtilde_cont : ContinuousOn Gtilde (f '' closedBall 0 1) :=
    (ContinuousMap.continuous P').comp_continuousOn hPhicont
  have hGtilde_nonzero : ∀ y ∈ f '' closedBall 0 1, (P' ∘ Phi) y ≠ 0 :=
    fun y hy h_eq => (hv_notin_sigma) ⟨Phi y, hPhiimg y hy, sub_eq_zero.mp h_eq⟩
  have hperturb_bound : ∀ y ∈ f '' (closedBall (0 : E) 1), ‖G y - Gtilde y‖ ≤ 1 := by
    intro y hy
    by_cases hP : ε < ‖y - c‖
    ·
      have hPhi : Phi y = y := by
        have hright : ε / ‖y - c‖ < 1 := by
          have hyc : 0 < ‖y - c‖ := by linarith
          rwa [div_lt_one hyc]
        simp [Phi, max_eq_right_of_lt hright]
      simp only [hPhi, Gtilde]
      calc
        ‖G y - P' y‖ = ‖G y - (P y - v)‖ := rfl
        _ ≤ _ := by grw [sub_sub_eq_add_sub, add_sub_right_comm, norm_add_le, norm_sub_rev,
          hP_bound y (Or.inl ⟨hy, le_of_lt hP⟩), add_comm, hvnorm]
        _ ≤ _ := by linarith
    · -- If `‖y - c‖ ≤ ε`, then `Φ y ∈ Σ₂`.
      simp only [not_lt] at hP
      have hy_neq_c : c ≠ y := by grind
      have hleft : 1 ≤ ε / ‖y - c‖ :=
        (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy_neq_c)))).mpr hP
      have hPhi : Phi y = c + (ε / ‖y - c‖) • (y - c) := by grind [max_eq_left]
      have hyimg : Phi y ∈ sphere c ε := by
        simp [hPhi, mem_sphere_iff_norm, add_sub_cancel_left, norm_smul,
          (sub_ne_zero_of_ne (Ne.symm hy_neq_c)), hε1.le]
      have hP_approx_le : ‖P (Phi y)‖ ≤ ‖(G (Phi y) : E)‖ + δ := by
        linarith [norm_sub_rev (P (Phi y)) (G (Phi y) : E), hP_bound (Phi y) (Or.inr hyimg),
        norm_le_norm_add_norm_sub' (P (Phi y)) (G (Phi y))]
      have hG_phi_small : ‖(G (Phi y) : E)‖ ≤ 0.1 := by
        rw [dist_eq_norm] at hc1
        have hdist : ‖Phi y - f 0‖ < 2 * ε := calc
          ‖Phi y - f 0‖  ≤ ‖Phi y - c‖ + ‖c - f 0‖ := by grw [← sub_add_sub_cancel,norm_add_le]
          _ = ε + ‖c - f 0‖ := by rw [mem_sphere_iff_norm.mp hyimg]
          _ < ε + ε := add_lt_add_right hc1 ε
          _ = 2 * ε := by ring
        rw [← h2εeq, ← dist_eq_norm] at hdist
        grind [h2ε1 hdist, dist_zero_right]
      specialize hG_small y hP
      calc
        ‖G y - P' (Phi y)‖
          = ‖G y - (P (Phi y) - v)‖ := rfl
        _ ≤ ‖(G y : E)‖ + ‖P (Phi y)‖ + ‖v‖ := by grw [sub_sub_eq_add_sub, add_sub_right_comm,
          norm_add_le, norm_sub_le]
        _ ≤ _ := by linarith
  obtain ⟨y, hy1, hy2⟩ := hStability_of_zero Gtilde hGtilde_cont hperturb_bound
  exact hGtilde_nonzero y hy1 hy2

/-- The invariance of domain theorem: if `U ⊆ E` is open,
  `f : E → E` is continuous on `U` and injective on `U`, then the image `f '' U` is open in `E`. -/
theorem isOpen_image_of_continuousOn_injective_euclidean (f : E → E) (U : Set E) (hU : IsOpen U)
    (hf_cont : ContinuousOn f U) (hf_inj : Set.InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hxU, hfx⟩
  rw [isOpen_iff] at hU
  have hclosedball: ∀ x' ∈ U, ∃ ε' > 0, closedBall x' ε' ⊆ U := by
    intro x' hx'
    obtain ⟨ε, hε, hball⟩ := hU x' hx'
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (div_two_lt_of_pos hε)).trans hball⟩
  obtain ⟨ε, hε , hclosedball⟩ := hclosedball x hxU
  let g := fun (v : E) => ε • v + x
  have hg_inj : Function.Injective g := by simp [Function.Injective, g, hε.ne']
  have h_g_eq : g '' closedBall 0 1 = closedBall x ε := by
    rw [← Set.image_image (fun v ↦ v + x) (fun v ↦ ε • v) (closedBall 0 1), Set.image_smul,
      smul_unitClosedBall]
    simp only [Real.norm_eq_abs, Set.image_add_right, preimage_add_right_closedBall,
      sub_neg_eq_add, zero_add]
    rw [abs_of_pos hε]
  let e := f ∘ g
  have he_cont : ContinuousOn e (closedBall 0 1):=
    ContinuousOn.image_comp_continuous (h_g_eq ▸ hf_cont.mono hclosedball) (by fun_prop)
  have he_inj : Set.InjOn e (closedBall 0 1) := by
    rw [Set.InjOn.comp_iff hg_inj.injOn, h_g_eq]
    exact Set.InjOn.mono hclosedball hf_inj
  have h_interior : e 0 ∈ interior (e '' closedBall 0 1) :=
    ball_image_mem_interior e he_cont he_inj
  refine ⟨interior (f '' U), ⟨interior_subset, isOpen_interior, ?_⟩⟩
  unfold e g at h_interior
  rw [Set.image_comp, h_g_eq] at h_interior
  simp only [Function.comp_apply, smul_zero, zero_add] at h_interior
  grw [hfx, hclosedball] at h_interior
  exact h_interior

/-- **Exercise 7.8(b).** Every continuous bijection of a finite-dimensional
real inner product space preserves epi-convergence under precomposition. -/
theorem EpiConverges.comp_continuous_bijective {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) {F : E → E} (hc : Continuous F) (hb : Function.Bijective F) :
    EpiConverges (fun n ↦ f n ∘ F) (g ∘ F) := by
  let e := Equiv.ofBijective F hb
  have ho : IsOpenMap F := fun U hU ↦
    isOpen_image_of_continuousOn_injective_euclidean F U hU hc.continuousOn hb.injective.injOn
  exact h.comp_homeomorph (e.toHomeomorphOfContinuousOpen hc ho)

end RW
