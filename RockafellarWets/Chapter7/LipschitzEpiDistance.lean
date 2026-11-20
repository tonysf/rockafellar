/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Distances between indicators and constrained Lipschitz functions
-/

import RockafellarWets.Chapter7.EpiDistances

open Metric Set
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem truncation_subset_iff_witness {C D : Set E} (hD : IsClosed D)
    {r e : ℝ} (he : 0 ≤ e) :
    C ∩ closedBall 0 r ⊆ cthickening e D ↔
      ∀ x ∈ C ∩ closedBall 0 r, ∃ y ∈ D, dist x y ≤ e := by
  simp only [hD.cthickening_eq_biUnion_closedBall he, subset_def, mem_iUnion, mem_closedBall, exists_prop]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem euclideanEpigraph_indicatorVA_iff (C : Set E) (p : WithLp 2 (E × ℝ)) :
    p ∈ euclideanEpigraph (indicatorVA C) ↔ p.fst ∈ C ∧ 0 ≤ p.snd := by
  change WithLp.ofLp p ∈ epigraph (indicatorVA C) ↔ _
  rw [epigraph_indicatorVA]
  rfl

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem dist_same_height (x y : E) (a : ℝ) :
    dist (WithLp.toLp 2 (x, a)) (WithLp.toLp 2 (y, a)) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  have h := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (x, a) - WithLp.toLp 2 (y, a))
  change _ = ‖x - y‖ ^ 2 + ‖a - a‖ ^ 2 at h
  simpa [sub_self, sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] using h

private theorem epi_truncation_indicator_iff {C D : Set E} (hD : IsClosed D)
    {r e : ℝ} (he : 0 ≤ e) :
    euclideanEpigraph (indicatorVA C) ∩ closedBall 0 r ⊆
        cthickening e (euclideanEpigraph (indicatorVA D)) ↔
      C ∩ closedBall 0 r ⊆ cthickening e D := by
  rw [truncation_subset_iff_witness (isClosed_euclideanEpigraph (lowerSemicontinuous_indicatorVA hD)) he,
    truncation_subset_iff_witness hD he]
  constructor
  · intro h x hx
    let p := WithLp.toLp 2 (x, (0 : ℝ))
    have hp : p ∈ euclideanEpigraph (indicatorVA C) :=
      (euclideanEpigraph_indicatorVA_iff C p).mpr ⟨hx.1, le_rfl⟩
    have hnorm : dist p 0 = dist x 0 := dist_same_height x 0 0
    obtain ⟨q, hq, hdist⟩ := h p ⟨hp, hnorm.trans_le hx.2⟩
    refine ⟨q.fst, ((euclideanEpigraph_indicatorVA_iff D q).mp hq).1, ?_⟩
    rw [dist_eq_norm] at hdist ⊢
    exact (WithLp.norm_fst_le _ (p - q)).trans hdist
  · intro h p hp
    obtain ⟨hx, ha⟩ := (euclideanEpigraph_indicatorVA_iff C p).mp hp.1
    have hnorm : ‖p‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hp.2
    have hxball : p.fst ∈ closedBall 0 r := by
      simpa only [mem_closedBall, dist_zero_right] using (WithLp.norm_fst_le _ p).trans hnorm
    obtain ⟨y, hy, hxy⟩ := h p.fst ⟨hx, hxball⟩
    refine ⟨WithLp.toLp 2 (y, p.snd), (euclideanEpigraph_indicatorVA_iff _ _).mpr ⟨hy, ha⟩, ?_⟩
    exact (dist_same_height p.fst y p.snd).trans_le hxy

/-- The localized epigraph excess for indicators is exactly the localized
set excess in the original space. -/
theorem rhoHatEpiDistance_indicatorVA (r : ℝ≥0) {C D : Set E}
    (hC : IsClosed C) (hnC : C.Nonempty) (hD : IsClosed D) (hnD : D.Nonempty) :
    rhoHatEpiDistance r (indicatorVA C) (indicatorVA D) = rhoHatDistance r C D := by
  have hEC := euclideanEpigraph_nonempty ((effectiveDomain_indicatorVA C).symm ▸ hnC)
  have hED := euclideanEpigraph_nonempty ((effectiveDomain_indicatorVA D).symm ▸ hnD)
  have hiff (e : ℝ) (he : 0 ≤ e) :
      rhoHatEpiDistance r (indicatorVA C) (indicatorVA D) ≤ e ↔ rhoHatDistance r C D ≤ e := by
    rw [rhoHatEpiDistance, rhoHatDistance_le_iff r hEC hED he, rhoHatDistance_le_iff r hnC hnD he,
      epi_truncation_indicator_iff hC he, epi_truncation_indicator_iff hD he]
  exact le_antisymm ((hiff _ (rhoHatDistance_nonneg _ _ _)).mpr le_rfl)
    ((hiff _ (rhoHatDistance_nonneg _ _ _)).mp le_rfl)

/-- **Theorem 7.58**, failure of the triangle inequality for the localized
excess on lsc functions with nonempty domain. -/
theorem not_rhoHatEpiDistance_triangle :
    ¬ rhoHatEpiDistance 1 (indicatorVA ({1} : Set ℝ)) (indicatorVA {-1}) ≤
      rhoHatEpiDistance 1 (indicatorVA ({1} : Set ℝ)) (indicatorVA {-(6/5),6/5}) +
        rhoHatEpiDistance 1 (indicatorVA ({-(6/5),6/5} : Set ℝ)) (indicatorVA {-1}) := by
  simpa only [rhoHatEpiDistance_indicatorVA _ isClosed_singleton (singleton_nonempty _)
      isClosed_singleton (singleton_nonempty _),
    rhoHatEpiDistance_indicatorVA _ isClosed_singleton (singleton_nonempty _)
      ((finite_singleton _).insert _).isClosed (insert_nonempty _ _),
    rhoHatEpiDistance_indicatorVA _ ((finite_singleton _).insert _).isClosed (insert_nonempty _ _)
      isClosed_singleton (singleton_nonempty _)] using not_rhoHatDistance_triangle

private theorem auxEpiComparison_indicatorVA_iff {C D : Set E} (hD : IsClosed D)
    {r : ℝ≥0} {e : ℝ} (he : 0 ≤ e) :
    auxEpiComparison r (indicatorVA C) (indicatorVA D) e ↔
      C ∩ closedBall 0 (r : ℝ) ⊆ cthickening e D := by
  rw [truncation_subset_iff_witness hD he]
  constructor
  · intro h x hx
    obtain ⟨y, hxy, hy⟩ := h x hx.2
    refine ⟨y, ?_, hxy⟩
    by_contra hyD
    simp [indicatorVA_apply_not_mem hyD, indicatorVA_apply_mem hx.1] at hy
  · intro h x hx
    by_cases hxC : x ∈ C
    · obtain ⟨y, hy, hxy⟩ := h x ⟨hxC, hx⟩
      exact ⟨y, hxy, by simp [indicatorVA_apply_mem hxC, indicatorVA_apply_mem hy,
        EReal.coe_nonneg.mpr he]⟩
    · exact ⟨x, by simpa using he, by simp [indicatorVA_apply_not_mem hxC]⟩

/-- **Example 7.62**, equality of the auxiliary distance for indicators with
the truncated set excess, at every nonnegative radius. -/
theorem auxEpiDistance_indicatorVA (r : ℝ≥0) {C D : Set E}
    (hC : IsClosed C) (hnC : C.Nonempty) (hD : IsClosed D) (hnD : D.Nonempty) :
    auxEpiDistance r (indicatorVA C) (indicatorVA D) = rhoHatDistance r C D := by
  have hiff (e : ℝ) (he : 0 ≤ e) :
      auxEpiAdmissible r (indicatorVA C) (indicatorVA D) e ↔ rhoHatDistance r C D ≤ e := by
    simp only [auxEpiAdmissible, he, true_and, rhoHatDistance_le_iff r hnC hnD he,
      auxEpiComparison_indicatorVA_iff hC he, auxEpiComparison_indicatorVA_iff hD he]
  have hm := (hiff _ (rhoHatDistance_nonneg r C D)).mpr le_rfl
  exact le_antisymm (csInf_le (auxEpiAdmissible_bddBelow _ _ _) hm)
    (le_csInf ⟨_, hm⟩ fun e he ↦ (hiff e he.1).mp he)

/-- **Example 7.62**. A Lipschitz estimate on the larger ball controls
the auxiliary distance of the two constrained objectives. -/
theorem auxEpiDistance_add_indicatorVA_le {r s : ℝ≥0} {C D : Set E}
    (hC : IsClosed C) (hnC : C.Nonempty) (hD : IsClosed D) (hnD : D.Nonempty)
    {f g : E → ℝ} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f (closedBall 0 (s : ℝ)))
    (hg : LipschitzOnWith L g (closedBall 0 (s : ℝ)))
    (hrs : rhoHatDistance r C D ≤ (s : ℝ) - r) :
    auxEpiDistance r (fun x ↦ (f x : EReal) + indicatorVA C x)
      (fun x ↦ (g x : EReal) + indicatorVA D x) ≤
        sSup ((fun x ↦ |f x - g x|) '' closedBall 0 (r : ℝ)) +
          (1 + max (K : ℝ) (L : ℝ)) * rhoHatDistance r C D := by
  let d := rhoHatDistance r C D
  let M := sSup ((fun x ↦ |f x - g x|) '' closedBall 0 (r : ℝ))
  have hd : 0 ≤ d := rhoHatDistance_nonneg _ _ _
  have hrs' : (r : ℝ) ≤ s := by dsimp [d] at hd; linarith
  have hsub := closedBall_subset_closedBall (x := (0 : E)) hrs'
  have hmax (x : E) (hx : x ∈ closedBall 0 (r : ℝ)) : |f x - g x| ≤ M :=
    le_csSup ((isCompact_closedBall 0 (r : ℝ)).image_of_continuousOn
      (((hf.continuousOn.mono hsub).sub (hg.continuousOn.mono hsub)).abs)).bddAbove
      (mem_image_of_mem _ hx)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hmax 0 (mem_closedBall_self r.2))
  let e := M + (1 + max (K : ℝ) (L : ℝ)) * d
  have hde : d ≤ e := by
    have hp := mul_nonneg (K.coe_nonneg.trans (le_max_left (K : ℝ) L)) hd
    dsimp [e]; linarith
  have hdir {A B : Set E} {u v : E → ℝ} (hB : IsClosed B) {k : ℝ≥0}
      (hinc : A ∩ closedBall 0 (r : ℝ) ⊆ cthickening d B)
      (hvk : LipschitzOnWith k v (closedBall 0 (s : ℝ))) (hk : (k : ℝ) ≤ max (K : ℝ) L)
      (hvu : ∀ x ∈ closedBall 0 (r : ℝ), v x - u x ≤ M) :
      auxEpiComparison r (fun x ↦ (u x : EReal) + indicatorVA A x)
        (fun x ↦ (v x : EReal) + indicatorVA B x) e := by
    intro x hx
    by_cases hxA : x ∈ A
    · obtain ⟨y, hy, hxy⟩ := (truncation_subset_iff_witness hB hd).mp hinc x ⟨hxA, hx⟩
      have hys : y ∈ closedBall 0 (s : ℝ) := by
        calc
          dist y 0 ≤ dist y x + dist x 0 := dist_triangle _ _ _
          _ ≤ d + r := add_le_add (dist_comm x y ▸ hxy) hx
          _ ≤ s := by dsimp [d]; linarith
      have hv := hvk.dist_le_mul y hys x (hsub hx)
      rw [Real.dist_eq, dist_comm y x] at hv
      have hv' : v y - v x ≤ max (K : ℝ) L * d :=
        (le_abs_self _).trans (hv.trans (mul_le_mul hk hxy dist_nonneg
          (K.coe_nonneg.trans (le_max_left _ _))))
      have hval : v y ≤ u x + e := by dsimp [e]; linarith [hvu x hx]
      refine ⟨y, hxy.trans hde, ?_⟩
      simp only [indicatorVA_apply_mem hxA, indicatorVA_apply_mem hy, add_zero]
      exact ((EReal.coe_le_coe_iff.mpr hval).trans_eq (EReal.coe_add _ _)).trans
        (add_le_add_left (le_max_left _ _) _)
    · refine ⟨x, by simpa using hd.trans hde, ?_⟩
      simp [indicatorVA_apply_not_mem hxA]
  obtain ⟨hCD, hDC⟩ := (rhoHatDistance_le_iff r hnC hnD hd).mp le_rfl
  apply csInf_le (auxEpiAdmissible_bddBelow _ _ _)
  refine ⟨hd.trans hde, hdir hD hCD hg (le_max_right _ _) ?_,
    hdir hC hDC hf (le_max_left _ _) ?_⟩
  · intro x hx
    exact (le_abs_self _).trans ((abs_sub_comm (g x) (f x)).le.trans (hmax x hx))
  · exact fun x hx ↦ (le_abs_self _).trans (hmax x hx)

end RW
