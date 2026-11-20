/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Scalar formulas for horizon epi-limits
-/

import RockafellarWets.Chapter7.EpiLimitFormulas
import RockafellarWets.Chapter7.HorizonEpiLimits

open Filter Function Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lowerHorizonEpiLimit_le_liminf_subsequence {f : ℕ → E → EReal} {x : E}
    {φ : ℕ → ℕ} {z : ℕ → E} {s : ℕ → ℝ} (hφ : StrictMono φ) (hs : ∀ n, 0 < s n)
    (hs0 : Tendsto s atTop (𝓝 0)) (hz : Tendsto (fun n ↦ s n • z n) atTop (𝓝 x)) :
    lowerHorizonEpiLimit f x ≤ liminf (fun n ↦ (s n : EReal) * f (φ n) (z n)) atTop := by
  simpa only [lowerHorizonEpiLimit, positiveScalePerspective_smul _ (hs _)] using
    epiLowerLimit_le_liminf_subsequence (f := fun n ↦ positiveScalePerspective (f n))
      hφ (hs0.prodMk_nhds hz)

theorem upperHorizonEpiLimit_le_limsup {f : ℕ → E → EReal} {x : E}
    {z : ℕ → E} {s : ℕ → ℝ} (hs : ∀ n, 0 < s n)
    (hs0 : Tendsto s atTop (𝓝 0)) (hz : Tendsto (fun n ↦ s n • z n) atTop (𝓝 x)) :
    upperHorizonEpiLimit f x ≤ limsup (fun n ↦ (s n : EReal) * f n (z n)) atTop := by
  simpa only [upperHorizonEpiLimit, positiveScalePerspective_smul _ (hs _)] using
    epiUpperLimit_le_limsup (f := fun n ↦ positiveScalePerspective (f n)) (hs0.prodMk_nhds hz)

private theorem replace_by_positive_scales (f : ℕ → E → EReal) {p : ℕ → ℝ × E} {x : E}
    (hp : Tendsto p atTop (𝓝 (0, x))) :
    ∃ (s : ℕ → ℝ) (z : ℕ → E), (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      Tendsto (fun n ↦ s n • z n) atTop (𝓝 x) ∧
      ∀ n, (s n : EReal) * f n (z n) ≤ positiveScalePerspective (f n) (p n) := by
  let s := fun n ↦ if 0 < (p n).1 then (p n).1 else 1 / ((n : ℝ) + 1)
  have hs (n : ℕ) : 0 < s n := by
    dsimp [s]
    split_ifs with h
    · exact h
    · positivity
  refine ⟨s, fun n ↦ (s n)⁻¹ • (p n).2, hs, ?_, ?_, ?_⟩
  · intro V hV
    change ∀ᶠ n in atTop, s n ∈ V
    filter_upwards [((continuous_fst.tendsto _).comp hp) hV,
      tendsto_one_div_add_atTop_nhds_zero_nat hV] with n hn h'n
    exact if h : 0 < (p n).1 then by simpa [s, h] using hn else by simpa [s, h] using h'n
  · simp only [smul_smul, mul_inv_cancel₀ (hs _).ne', one_smul]
    exact (continuous_snd.tendsto _).comp hp
  · intro n
    by_cases hn : 0 < (p n).1 <;> simp [positiveScalePerspective, s, hn]

/-- **Exercise 7.50**, the attained minimum for the lower horizon epi-limit. -/
theorem isLeast_liminf_lowerHorizonEpiLimit (f : ℕ → E → EReal) (x : E) :
    IsLeast {a | ∃ (s : ℕ → ℝ) (z : ℕ → E), (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      Tendsto (fun n ↦ s n • z n) atTop (𝓝 x) ∧
      liminf (fun n ↦ (s n : EReal) * f n (z n)) atTop = a} (lowerHorizonEpiLimit f x) := by
  constructor
  · obtain ⟨p, hp, heq⟩ := exists_tendsto_liminf_eq_epiLowerLimit
      (fun n ↦ positiveScalePerspective (f n)) (0, x)
    obtain ⟨s, z, hs, hs0, hz, hle⟩ := replace_by_positive_scales f hp
    exact ⟨s, z, hs, hs0, hz, le_antisymm ((liminf_le_liminf (.of_forall hle)).trans_eq heq)
      (lowerHorizonEpiLimit_le_liminf_subsequence strictMono_id hs hs0 hz)⟩
  · rintro _ ⟨s, z, hs, hs0, hz, rfl⟩
    exact lowerHorizonEpiLimit_le_liminf_subsequence strictMono_id hs hs0 hz

/-- **Exercise 7.50**, the attained minimum for the upper horizon epi-limit. -/
theorem isLeast_limsup_upperHorizonEpiLimit (f : ℕ → E → EReal) (x : E) :
    IsLeast {a | ∃ (s : ℕ → ℝ) (z : ℕ → E), (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      Tendsto (fun n ↦ s n • z n) atTop (𝓝 x) ∧
      limsup (fun n ↦ (s n : EReal) * f n (z n)) atTop = a} (upperHorizonEpiLimit f x) := by
  constructor
  · obtain ⟨p, hp, heq⟩ := exists_tendsto_limsup_eq_epiUpperLimit
      (fun n ↦ positiveScalePerspective (f n)) (0, x)
    obtain ⟨s, z, hs, hs0, hz, hle⟩ := replace_by_positive_scales f hp
    exact ⟨s, z, hs, hs0, hz, le_antisymm ((limsup_le_limsup (.of_forall hle)).trans_eq heq)
      (upperHorizonEpiLimit_le_limsup hs hs0 hz)⟩
  · rintro _ ⟨s, z, hs, hs0, hz, rfl⟩
    exact upperHorizonEpiLimit_le_limsup hs hs0 hz


/-- Inner infimum in the neighborhood and ball formulas of 7.50. -/
noncomputable def horizonLocalInf (h : E → EReal) (V : Set E) (δ : ℝ) : EReal :=
  ⨅ y ∈ V, ⨅ s ∈ Ioo (0 : ℝ) δ, (s : EReal) * h (s⁻¹ • y)

private theorem horizonLocalInf_eq (h : E → EReal) (V : Set E) {δ : ℝ} (hδ : 0 < δ) :
    horizonLocalInf h V δ =
      ⨅ p ∈ Ioo (-δ) δ ×ˢ V, positiveScalePerspective h p := by
  apply le_antisymm
  · refine le_iInf₂ fun ⟨s, y⟩ hp ↦ ?_
    by_cases hs : 0 < s
    · exact (iInf₂_le_of_le y hp.2 <| iInf₂_le_of_le s ⟨hs, hp.1.2⟩ le_rfl).trans
        (by simp [positiveScalePerspective, hs])
    · simp [positiveScalePerspective, hs]
  · refine le_iInf₂ fun y hy ↦ le_iInf₂ fun s hs ↦ ?_
    have hm : (s, y) ∈ Ioo (-δ) δ ×ˢ V := ⟨⟨(neg_lt_zero.mpr hδ).trans hs.1, hs.2⟩, hy⟩
    exact (iInf₂_le (f := fun p (_ : p ∈ Ioo (-δ) δ ×ˢ V) ↦ positiveScalePerspective h p)
      (s, y) hm).trans (by simp [positiveScalePerspective, hs.1])

private theorem perspective_nhds_sup (f : ℕ → E → EReal) (x : E)
    (L : (ℕ → EReal) → EReal) (hL : Monotone L) :
    (⨆ W ∈ 𝓝 ((0 : ℝ), x), L (fun n ↦ ⨅ p ∈ W, positiveScalePerspective (f n) p)) =
      ⨆ V ∈ 𝓝 x, ⨆ δ > (0 : ℝ), L (fun n ↦ horizonLocalInf (f n) V δ) := by
  apply le_antisymm
  · refine iSup₂_le fun W hW ↦ ?_
    obtain ⟨U, hU, V, hV, hsub⟩ := mem_nhds_prod_iff.mp hW
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
    refine le_iSup₂_of_le V hV <| le_iSup₂_of_le δ hδ <| hL fun n ↦ ?_
    rw [horizonLocalInf_eq _ _ hδ]
    refine le_iInf₂ fun p hp ↦ iInf₂_le p (hsub ⟨hball ?_, hp.2⟩)
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hp.1
  · refine iSup₂_le fun V hV ↦ iSup₂_le fun δ hδ ↦ ?_
    simp_rw [horizonLocalInf_eq _ _ hδ]
    exact le_iSup₂ (f := fun W (_ : W ∈ 𝓝 ((0 : ℝ), x)) ↦
      L (fun n ↦ ⨅ p ∈ W, positiveScalePerspective (f n) p)) _
      (prod_mem_nhds (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ) hV)

private theorem tendsto_horizonLocalInf (f : ℕ → E → EReal) (x : E)
    (L : (ℕ → EReal) → EReal) (hL : Monotone L) :
    Tendsto (fun δ ↦ L (fun n ↦ horizonLocalInf (f n) (closedBall x δ) δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (⨆ V ∈ 𝓝 x, ⨆ δ > (0 : ℝ), L (fun n ↦ horizonLocalInf (f n) V δ))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨V, hV⟩ := lt_iSup_iff.mp ha
    obtain ⟨hV, ha⟩ := lt_iSup_iff.mp hV
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp ha
    obtain ⟨hr, ha⟩ := lt_iSup_iff.mp hr
    obtain ⟨t, ht, htV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hV
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_min hr ht))] with δ hδ
    apply ha.trans_le (hL fun n ↦ ?_)
    refine le_iInf₂ fun y hy ↦ le_iInf₂ fun s hs ↦ ?_
    apply iInf₂_le_of_le y (htV (closedBall_subset_closedBall (hδ.le.trans (min_le_right ..)) hy))
    exact iInf₂_le s ⟨hs.1, hs.2.trans_le (hδ.le.trans (min_le_left ..))⟩
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact lt_of_le_of_lt (le_iSup₂_of_le (closedBall x δ) (closedBall_mem_nhds x hδ)
      (le_iSup₂ (f := fun r (_ : 0 < r) ↦ L (fun n ↦ horizonLocalInf (f n) (closedBall x δ) r)) δ (show 0 < δ from hδ))) hb

/-- **Exercise 7.50**, the neighborhood and cofinite-index formula for the lower horizon limit. -/
theorem lowerHorizonEpiLimit_eq_iSup_iSup_iInf (f : ℕ → E → EReal) (x : E) :
    lowerHorizonEpiLimit f x = ⨆ V ∈ 𝓝 x, ⨆ δ > (0 : ℝ),
      ⨆ N ∈ (atTop : Filter ℕ), ⨅ n ∈ N, horizonLocalInf (f n) V δ := by
  rw [lowerHorizonEpiLimit, epiLowerLimit_eq_iSup_liminf,
    perspective_nhds_sup _ _ (fun v ↦ liminf v atTop) (fun _ _ h ↦ liminf_le_liminf (.of_forall h))]
  simp only [liminf_eq_iSup_iInf]

/-- **Exercise 7.50**, the neighborhood and cofinite-index formula for the upper horizon limit. -/
theorem upperHorizonEpiLimit_eq_iSup_iInf_iSup (f : ℕ → E → EReal) (x : E) :
    upperHorizonEpiLimit f x = ⨆ V ∈ 𝓝 x, ⨆ δ > (0 : ℝ),
      ⨅ N ∈ (atTop : Filter ℕ), ⨆ n ∈ N, horizonLocalInf (f n) V δ := by
  rw [upperHorizonEpiLimit, epiUpperLimit_eq_iSup_limsup,
    perspective_nhds_sup _ _ (fun v ↦ limsup v atTop) (fun _ _ h ↦ limsup_le_limsup (.of_forall h))]
  simp only [limsup_eq_iInf_iSup]

theorem tendsto_liminf_closedBall_lowerHorizonEpiLimit (f : ℕ → E → EReal) (x : E) :
    Tendsto (fun δ ↦ liminf (fun n ↦ horizonLocalInf (f n) (closedBall x δ) δ) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 (lowerHorizonEpiLimit f x)) := by
  rw [lowerHorizonEpiLimit, epiLowerLimit_eq_iSup_liminf,
    perspective_nhds_sup _ _ (fun v ↦ liminf v atTop) (fun _ _ h ↦ liminf_le_liminf (.of_forall h))]
  exact tendsto_horizonLocalInf f x (fun v ↦ liminf v atTop) fun _ _ h ↦ liminf_le_liminf (.of_forall h)

theorem tendsto_limsup_closedBall_upperHorizonEpiLimit (f : ℕ → E → EReal) (x : E) :
    Tendsto (fun δ ↦ limsup (fun n ↦ horizonLocalInf (f n) (closedBall x δ) δ) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 (upperHorizonEpiLimit f x)) := by
  rw [upperHorizonEpiLimit, epiUpperLimit_eq_iSup_limsup,
    perspective_nhds_sup _ _ (fun v ↦ limsup v atTop) (fun _ _ h ↦ limsup_le_limsup (.of_forall h))]
  exact tendsto_horizonLocalInf f x (fun v ↦ limsup v atTop) fun _ _ h ↦ limsup_le_limsup (.of_forall h)

end RW
