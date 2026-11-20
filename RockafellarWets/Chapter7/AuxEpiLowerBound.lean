/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A local height condition for the lower bound in Proposition 7.61
-/

import RockafellarWets.Chapter7.AuxEpiComparison

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- Points of the source epigraph in the box of radius `r` can be tested
at Euclidean radius `√2 r`. Source values above the top of the box are
precisely those excluded by the additional hypothesis. -/
private theorem auxEpiComparison_of_height_bound {r ρ : ℝ≥0} (hr : Real.sqrt 2 * r ≤ ρ)
    {f g : E → EReal} (hg : (effectiveDomain g).Nonempty)
    (hf : ∀ x ∈ closedBall (0 : E) (r : ℝ), f x = ⊤ ∨ f x ≤ (r : ℝ))
    {d η : ℝ} (hd : 0 ≤ d) (hη : d < η)
    (hsub : euclideanEpigraph f ∩ closedBall 0 (ρ : ℝ) ⊆ cthickening d (euclideanEpigraph g)) :
    auxEpiComparison r f g η := by
  intro x hx
  rcases hf x hx with hxTop | hxHi
  · exact ⟨x, by simpa using hd.trans hη.le, by simp [hxTop]⟩
  let a := max (f x) ((-(r : ℝ) : ℝ) : EReal)
  have hlow : ((-(r : ℝ) : ℝ) : EReal) ≤ a := le_max_right _ _
  have hhi : a ≤ (r : ℝ) := max_le hxHi (EReal.coe_le_coe_iff.mpr (by linarith [r.coe_nonneg]))
  have heq : (a.toReal : EReal) = a :=
    EReal.coe_toReal (hhi.trans_lt (EReal.coe_lt_top _)).ne ((EReal.bot_lt_coe _).trans_le hlow).ne'
  let p := WithLp.toLp 2 (x, a.toReal)
  have hp : p ∈ euclideanEpigraph f := by
    change f x ≤ (a.toReal : EReal)
    rw [heq]
    exact le_max_left _ _
  have hball : p ∈ closedBall 0 (ρ : ℝ) := by
    have hx' : ‖x‖ ≤ (r : ℝ) := by simpa using hx
    have ha' : |a.toReal| ≤ (r : ℝ) := abs_le.mpr
      ⟨EReal.coe_le_coe_iff.mp (heq.symm ▸ hlow), EReal.coe_le_coe_iff.mp (heq.symm ▸ hhi)⟩
    change dist p 0 ≤ (ρ : ℝ)
    rw [dist_zero_right]
    apply le_trans _ hr
    have hsq := WithLp.prod_norm_sq_eq_of_L2 p
    change ‖p‖ ^ 2 = ‖x‖ ^ 2 + ‖a.toReal‖ ^ 2 at hsq
    rw [Real.norm_eq_abs] at hsq
    have hsqR : (Real.sqrt 2 * (r : ℝ))^2 = 2 * (r : ℝ)^2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
    have hr' : 0 ≤ Real.sqrt 2 * (r : ℝ) := mul_nonneg (Real.sqrt_nonneg _) r.coe_nonneg
    nlinarith [sq_le_sq' ((neg_nonpos.mpr r.coe_nonneg).trans (norm_nonneg x)) hx',
      sq_le_sq' ((neg_nonpos.mpr r.coe_nonneg).trans (abs_nonneg _)) ha']
  have hs := mem_cthickening_iff.mp (hsub ⟨hp, hball⟩)
  have hne := euclideanEpigraph_nonempty hg
  have hinf : infDist p (euclideanEpigraph g) ≤ d :=
    (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hne) hd).1 hs
  obtain ⟨q, hq, hpq⟩ := (infDist_lt_iff hne).mp (hinf.trans_lt hη)
  refine ⟨q.fst, (WithLp.dist_fst_le p q).trans hpq.le, ?_⟩
  have hsnd : dist a.toReal q.snd ≤ η := (WithLp.dist_snd_le p q).trans hpq.le
  have hs' : q.snd ≤ a.toReal + η := by
    rw [Real.dist_eq, abs_le] at hsnd
    linarith [hsnd.1]
  change g q.fst ≤ a + (η : EReal)
  rw [← heq, ← EReal.coe_add]
  exact (show g q.fst ≤ (q.snd : EReal) from hq).trans (EReal.coe_le_coe_iff.mpr hs')

/-- **Proposition 7.61, qualified lower bound.** If both functions take
finite values at most `r` wherever their effective domains meet the horizontal
ball of radius `r`, ordinary epigraph distance at `ρ ≥ √2 r` controls the
auxiliary distance at `r`. Negative infinity is allowed as a source value. -/
theorem auxEpiDistance_le_rhoHatDistance_of_height_bound [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {r ρ : ℝ≥0} (hr : Real.sqrt 2 * r ≤ ρ) {f g : E → EReal}
    (hf : (effectiveDomain f).Nonempty) (hg : (effectiveDomain g).Nonempty)
    (hfHi : ∀ x ∈ closedBall (0 : E) (r : ℝ), f x = ⊤ ∨ f x ≤ (r : ℝ))
    (hgHi : ∀ x ∈ closedBall (0 : E) (r : ℝ), g x = ⊤ ∨ g x ≤ (r : ℝ)) :
    auxEpiDistance r f g ≤ rhoHatDistance ρ (euclideanEpigraph f) (euclideanEpigraph g) := by
  let d := rhoHatDistance ρ (euclideanEpigraph f) (euclideanEpigraph g)
  have hd : 0 ≤ d := rhoHatDistance_nonneg _ _ _
  have hsub := (rhoHatDistance_le_iff ρ (euclideanEpigraph_nonempty hf)
    (euclideanEpigraph_nonempty hg) hd).mp le_rfl
  apply le_of_forall_gt_imp_ge_of_dense
  intro η hη
  apply csInf_le (auxEpiAdmissible_bddBelow _ _ _)
  exact ⟨hd.trans hη.le, auxEpiComparison_of_height_bound hr hg hfHi hd hη hsub.1,
    auxEpiComparison_of_height_bound hr hf hgHi hd hη hsub.2⟩

end RW
