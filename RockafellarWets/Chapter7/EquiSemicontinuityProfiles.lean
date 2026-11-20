/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Scalar tests for equi-semicontinuity of profiles

The height cutoff in Definition 5.38 tests the part of a ray inside
`[-ρ, ρ]`. Consequently the epigraphical test on a nonempty truncated ray
uses its lowest height, `max (fₙ y) (-ρ)`, and the hypographical test uses
its highest height, `min (fₙ y) ρ`. The extra truncation is relevant when
the base values escape to infinity (see `EquiSemicontinuityCounterexample`).
-/
import RockafellarWets.Chapter5.Equicontinuity
import RockafellarWets.Chapter5.ProfileMappings

open Filter Metric Set Topology

namespace RW

private theorem mem_thickening_epiRay {a : EReal} {t ε : ℝ} (hε : 0 < ε) :
    t ∈ thickening ε {s : ℝ | a ≤ (s : EReal)} ↔ a < ((t + ε : ℝ) : EReal) := by
  rw [mem_thickening_iff]
  constructor
  · rintro ⟨s, hs, hst⟩
    rw [Real.dist_eq, abs_lt] at hst
    exact hs.trans_lt (EReal.coe_lt_coe_iff.2 (by linarith))
  · intro ht
    obtain ⟨s, has, hst⟩ := EReal.exists_between_coe_real ht
    have hst' : s < t + ε := EReal.coe_lt_coe_iff.1 hst
    refine ⟨max t s, has.le.trans (EReal.coe_le_coe_iff.2 (le_max_right ..)), ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor
    · rw [lt_sub_iff_add_lt]
      rcases le_total t s with h | h <;> simp only [max_eq_right h, max_eq_left h] <;> linarith
    · linarith [le_max_left t s]

private theorem mem_thickening_hypoRay {a : EReal} {t ε : ℝ} (hε : 0 < ε) :
    t ∈ thickening ε {s : ℝ | (s : EReal) ≤ a} ↔ ((t - ε : ℝ) : EReal) < a := by
  rw [mem_thickening_iff]
  constructor
  · rintro ⟨s, hs, hst⟩
    rw [Real.dist_eq, abs_lt] at hst
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) hs
  · intro ht
    obtain ⟨s, hts, hsa⟩ := EReal.exists_between_coe_real ht
    have hts' : t - ε < s := EReal.coe_lt_coe_iff.1 hts
    refine ⟨min t s, (EReal.coe_le_coe_iff.2 (min_le_right ..)).trans hsa.le, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [min_le_left t s]
    · rcases le_total t s with h | h <;> simp only [min_eq_right h, min_eq_left h] <;> linarith

/-- The exact comparison of two epi rays at fixed cutoff and tolerance. -/
theorem epiRay_inter_closedBall_subset_thickening_iff {a c : EReal} {ε ρ : ℝ}
    (hε : 0 < ε) (hρ : 0 ≤ ρ) :
    {t : ℝ | c ≤ (t : EReal)} ∩ closedBall 0 ρ ⊆ thickening ε {t : ℝ | a ≤ (t : EReal)} ↔
      c ≤ ρ → a < max c ((-ρ : ℝ) : EReal) + ε := by
  constructor
  · intro h hc
    let m := max c ((-ρ : ℝ) : EReal)
    have hlo : ((-ρ : ℝ) : EReal) ≤ m := le_max_right ..
    have hhi : m ≤ (ρ : EReal) := max_le hc (EReal.coe_le_coe_iff.2 (by linarith))
    have hfin : (m.toReal : EReal) = m :=
      EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi)
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo)
    have ht : m.toReal ∈ closedBall (0 : ℝ) ρ := by
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      exact ⟨EReal.coe_le_coe_iff.1 (by rw [hfin]; exact hlo),
        EReal.coe_le_coe_iff.1 (by rw [hfin]; exact hhi)⟩
    have hcm : c ≤ (m.toReal : EReal) := by rw [hfin]; exact le_max_left ..
    have ha := (mem_thickening_epiRay hε).1 (h ⟨hcm, ht⟩)
    simpa only [EReal.coe_add, hfin] using ha
  · intro h t ht
    have hb : -ρ ≤ t ∧ t ≤ ρ := by simpa [mem_closedBall, Real.dist_eq, abs_le] using ht.2
    apply (mem_thickening_epiRay hε).2
    rw [EReal.coe_add]
    exact (h (ht.1.trans (EReal.coe_le_coe_iff.2 hb.2))).trans_le
      (add_le_add (max_le ht.1 (EReal.coe_le_coe_iff.2 hb.1)) le_rfl)

/-- The corresponding exact comparison of two hypo rays. -/
theorem hypoRay_inter_closedBall_subset_thickening_iff {a c : EReal} {ε ρ : ℝ}
    (hε : 0 < ε) (hρ : 0 ≤ ρ) :
    {t : ℝ | (t : EReal) ≤ c} ∩ closedBall 0 ρ ⊆ thickening ε {t : ℝ | (t : EReal) ≤ a} ↔
      ((-ρ : ℝ) : EReal) ≤ c → min c (ρ : EReal) - ε < a := by
  constructor
  · intro h hc
    let m := min c (ρ : EReal)
    have hhi : m ≤ (ρ : EReal) := min_le_right ..
    have hlo : ((-ρ : ℝ) : EReal) ≤ m := le_min hc (EReal.coe_le_coe_iff.2 (by linarith))
    have hfin : (m.toReal : EReal) = m :=
      EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi)
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo)
    have ht : m.toReal ∈ closedBall (0 : ℝ) ρ := by
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      exact ⟨EReal.coe_le_coe_iff.1 (by rw [hfin]; exact hlo),
        EReal.coe_le_coe_iff.1 (by rw [hfin]; exact hhi)⟩
    have hmc : (m.toReal : EReal) ≤ c := by rw [hfin]; exact min_le_left ..
    have ha := (mem_thickening_hypoRay hε).1 (h ⟨hmc, ht⟩)
    simpa only [EReal.coe_sub, hfin] using ha
  · intro h t ht
    have hb : -ρ ≤ t ∧ t ≤ ρ := by simpa [mem_closedBall, Real.dist_eq, abs_le] using ht.2
    apply (mem_thickening_hypoRay hε).2
    rw [EReal.coe_sub, sub_eq_add_neg]
    exact lt_of_le_of_lt (add_le_add (le_min ht.1 (EReal.coe_le_coe_iff.2 hb.2)) le_rfl)
      (h ((EReal.coe_le_coe_iff.2 hb.1).trans ht.1))

variable {E : Type*} [PseudoMetricSpace E] (f : ℕ → E → EReal) (X : Set E) (x : E)

/-- Exercise 7.9(a) in a form valid for every extended-real sequence. -/
theorem svEquiOscWithinAt_epiProfile_iff_clipped :
    SvEquiOscWithinAt (fun n ↦ epiProfile (f n)) X x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ 𝓝 x, ∀ n, ∀ y ∈ V ∩ X,
        f n y ≤ (ρ : ℝ) → f n x < max (f n y) ((-ρ : ℝ) : EReal) + (ε : ℝ) := by
  unfold SvEquiOscWithinAt epiProfile
  refine forall_congr' fun ε ↦ forall_congr' fun hε ↦
    forall_congr' fun ρ ↦ forall_congr' fun hρ ↦ ?_
  simp_rw [epiRay_inter_closedBall_subset_thickening_iff hε hρ.le]

theorem svAsymptoticallyEquiOscWithinAt_epiProfile_iff_clipped :
    SvAsymptoticallyEquiOscWithinAt (fun n ↦ epiProfile (f n)) X x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ 𝓝 x, ∀ᶠ n in atTop, ∀ y ∈ V ∩ X,
        f n y ≤ (ρ : ℝ) → f n x < max (f n y) ((-ρ : ℝ) : EReal) + (ε : ℝ) := by
  unfold SvAsymptoticallyEquiOscWithinAt epiProfile
  refine forall_congr' fun ε ↦ forall_congr' fun hε ↦
    forall_congr' fun ρ ↦ forall_congr' fun hρ ↦ ?_
  simp_rw [epiRay_inter_closedBall_subset_thickening_iff hε hρ.le]

/-- Exercise 7.9(b) with its height cutoff on both sides. -/
theorem svEquiOscWithinAt_hypoProfile_iff_clipped :
    SvEquiOscWithinAt (fun n ↦ hypoProfile (f n)) X x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ 𝓝 x, ∀ n, ∀ y ∈ V ∩ X,
        ((-ρ : ℝ) : EReal) ≤ f n y → min (f n y) (ρ : ℝ) - (ε : ℝ) < f n x := by
  unfold SvEquiOscWithinAt hypoProfile
  refine forall_congr' fun ε ↦ forall_congr' fun hε ↦
    forall_congr' fun ρ ↦ forall_congr' fun hρ ↦ ?_
  simp_rw [hypoRay_inter_closedBall_subset_thickening_iff hε hρ.le]

theorem svAsymptoticallyEquiOscWithinAt_hypoProfile_iff_clipped :
    SvAsymptoticallyEquiOscWithinAt (fun n ↦ hypoProfile (f n)) X x ↔
      ∀ ε > 0, ∀ ρ > 0, ∃ V ∈ 𝓝 x, ∀ᶠ n in atTop, ∀ y ∈ V ∩ X,
        ((-ρ : ℝ) : EReal) ≤ f n y → min (f n y) (ρ : ℝ) - (ε : ℝ) < f n x := by
  unfold SvAsymptoticallyEquiOscWithinAt hypoProfile
  refine forall_congr' fun ε ↦ forall_congr' fun hε ↦
    forall_congr' fun ρ ↦ forall_congr' fun hρ ↦ ?_
  simp_rw [hypoRay_inter_closedBall_subset_thickening_iff hε hρ.le]

end RW
