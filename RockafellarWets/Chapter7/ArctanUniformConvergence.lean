/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The arctangent test for extended uniform convergence

This gives the compactification description following Definition 7.12.
-/

import RockafellarWets.Chapter7.ExtendedUniformConvergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

open Filter Metric Set Topology

namespace RW

/-- Arctangent with the two endpoints filled in at ±π/2. -/
noncomputable def erealArctan : EReal → ℝ :=
  EReal.rec (-(Real.pi / 2)) Real.arctan (Real.pi / 2)

theorem strictMono_erealArctan : StrictMono erealArctan := by
  intro a b hab
  cases a <;> cases b <;> simp_all only [bot_lt_iff_ne_bot, lt_top_iff_ne_top,
    EReal.coe_lt_coe_iff, not_lt_bot, not_top_lt, lt_self_iff_false]
  · exact Real.neg_pi_div_two_lt_arctan _
  · change -(Real.pi / 2) < Real.pi / 2
    linarith [Real.pi_pos]
  · exact Real.arctan_strictMono hab
  · exact Real.arctan_lt_pi_div_two _

theorem range_erealArctan : range erealArctan = Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  ext t
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨strictMono_erealArctan.monotone (bot_le : ⊥ ≤ a),
      strictMono_erealArctan.monotone (le_top : a ≤ ⊤)⟩
  · intro ht
    rcases ht.1.eq_or_lt with heq | hlo
    · exact ⟨⊥, heq⟩
    rcases ht.2.eq_or_lt with heq | hhi
    · exact ⟨⊤, heq.symm⟩
    exact ⟨((Real.tan t : ℝ) : EReal), Real.arctan_tan hlo hhi⟩

theorem continuous_erealArctan : Continuous erealArctan :=
  (strictMono_erealArctan.isEmbedding_of_ordConnected (by
    rw [range_erealArctan]; infer_instance)).continuous

private theorem erealTrunc_separates {a b : EReal}
    (h : ∀ ρ > 0, erealTrunc ρ a = erealTrunc ρ b) : a = b := by
  suffices sep : ∀ u v : EReal, u < v → ∃ r > 0, erealTrunc r u < erealTrunc r v by
    rcases lt_trichotomy a b with hab | heq | hba
    · obtain ⟨r, hr, hlt⟩ := sep a b hab
      exact (hlt.ne (h r hr)).elim
    · exact heq
    · obtain ⟨r, hr, hlt⟩ := sep b a hba
      exact (hlt.ne (h r hr).symm).elim
  intro u v huv
  obtain ⟨s, hus, hsv⟩ := EReal.exists_between_coe_real huv
  obtain ⟨t, hst, htv⟩ := EReal.exists_between_coe_real hsv
  let r := |s| + |t| + 1
  refine ⟨r, by dsimp [r]; positivity, ?_⟩
  have hs : -r ≤ s := by dsimp [r]; linarith [neg_abs_le s, abs_nonneg t]
  have ht : t ≤ r := by dsimp [r]; linarith [le_abs_self t, abs_nonneg s]
  exact (erealTrunc_le_of_le hs hus.le).trans_lt
    ((EReal.coe_lt_coe_iff.mp hst).trans_le (le_erealTrunc_of_le ht htv.le))

/-- On the compact extended line, continuous scalar tests that separate
points control uniform convergence of every continuous real observable. -/
private theorem tendstoUniformlyOn_of_separating_tests {E : Type*}
    {f : ℕ → E → EReal} {g : E → EReal} {X : Set E} {P : ℝ → EReal → ℝ} {T : EReal → ℝ}
    (hP : ∀ r > 0, Continuous (P r))
    (hsep : ∀ a b, (∀ r > 0, P r a = P r b) → a = b) (hT : Continuous T)
    (h : ∀ r > 0, TendstoUniformlyOn (fun n x ↦ P r (f n x)) (fun x ↦ P r (g x)) atTop X) :
    TendstoUniformlyOn (fun n x ↦ T (f n x)) (fun x ↦ T (g x)) atTop X := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  by_contra hn
  rw [not_eventually] at hn
  have hbad := hn.mono fun n hbad ↦ by
    push_neg at hbad
    exact hbad
  obtain ⟨φ, hφ, hx⟩ := extraction_of_frequently_atTop hbad
  choose z hz hgap using hx
  let q := fun n ↦ (g (z n), f (φ n) (z n))
  obtain ⟨p, ψ, hψ, hp⟩ := CompactSpace.tendsto_subseq q
  have heq : p.1 = p.2 := by
    apply hsep
    intro r hr
    have hdist : Tendsto (fun k ↦ dist (P r (q (ψ k)).1) (P r (q (ψ k)).2)) atTop
        (𝓝 (0 : ℝ)) := by
      apply Metric.tendsto_nhds.mpr
      intro δ hδ
      filter_upwards [(hφ.comp hψ).tendsto_atTop.eventually
        (Metric.tendstoUniformlyOn_iff.mp (h r hr) δ hδ)] with k hk
      simpa [Real.dist_eq, abs_of_nonneg (dist_nonneg (x := P r (q (ψ k)).1))] using hk _ (hz (ψ k))
    exact dist_eq_zero.mp (tendsto_nhds_unique
      (((hP r hr).continuousAt.tendsto.comp hp.fst_nhds).dist ((hP r hr).continuousAt.tendsto.comp hp.snd_nhds)) hdist)
  have hd := (hT.continuousAt.tendsto.comp hp.fst_nhds).dist (hT.continuousAt.tendsto.comp hp.snd_nhds)
  have hle := le_of_tendsto_of_tendsto' tendsto_const_nhds hd (fun n ↦ hgap (ψ n))
  exact hε.not_ge (by simpa [heq] using hle)

/-- Uniform convergence of every truncation is equivalent to usual uniform
convergence of the extended arctangents, as stated after Definition 7.12. -/
theorem erealConvergesUniformlyOn_iff_tendstoUniformlyOn_arctan {E : Type*}
    {f : ℕ → E → EReal} {g : E → EReal} {X : Set E} :
    ERealConvergesUniformlyOn f g X ↔
      TendstoUniformlyOn (fun n x ↦ erealArctan (f n x)) (fun x ↦ erealArctan (g x)) atTop X := by
  constructor
  · exact tendstoUniformlyOn_of_separating_tests (fun r _ ↦ continuous_erealTrunc r)
      (fun _ _ ↦ erealTrunc_separates) continuous_erealArctan
  · intro h ρ _
    exact tendstoUniformlyOn_of_separating_tests (P := fun _ ↦ erealArctan)
      (fun _ _ ↦ continuous_erealArctan) (fun _ _ h ↦ strictMono_erealArctan.injective (h 1 one_pos))
      (continuous_erealTrunc ρ) (fun _ _ ↦ h)

end RW
