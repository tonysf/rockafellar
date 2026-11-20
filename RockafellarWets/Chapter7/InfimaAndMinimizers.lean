/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convergence of infima and approximate minimizers

Propositions 7.29–7.30 and Theorem 7.31. The test for convergence of the
infima uses a compact set which may depend on the prescribed tolerance.
-/

import RockafellarWets.Chapter7.ApproximateMinimizers
import RockafellarWets.Chapter7.EpiLimitCharacterization
import RockafellarWets.Chapter7.LevelSetConvergence

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [PseudoMetricSpace E]

/-- **Proposition 7.29(a)**. -/
theorem le_epiLowerLimit_iff_infimumOn_compact [ProperSpace E]
    {f : ℕ → E → EReal} {g : E → EReal} (hg : LowerSemicontinuous g) :
    g ≤ epiLowerLimit f ↔ ∀ B : Set E, IsCompact B →
      infimumOn g B ≤ liminf (fun n ↦ infimumOn (f n) B) atTop := by
  rw [← epigraph_subset_epigraph_iff, epigraph_epiLowerLimit,
    epigraph_outerSetLimit_subset_iff_infimumOn_compact hg]

/-- **Proposition 7.29(b)**. -/
theorem epiUpperLimit_le_iff_infimumOn_open {f : ℕ → E → EReal} {g : E → EReal} :
    epiUpperLimit f ≤ g ↔ ∀ O : Set E, IsOpen O →
      limsup (fun n ↦ infimumOn (f n) O) atTop ≤ infimumOn g O := by
  rw [← epigraph_subset_epigraph_iff, epigraph_epiUpperLimit,
    epigraph_subset_innerSetLimit_iff_infimumOn_open]

/-- **Proposition 7.29**, characterization of epi-convergence via minimization. -/
theorem epiConverges_iff_infimumOn_compact_open [ProperSpace E]
    {f : ℕ → E → EReal} {g : E → EReal} (hg : LowerSemicontinuous g) :
    EpiConverges f g ↔
      (∀ B : Set E, IsCompact B → infimumOn g B ≤ liminf (fun n ↦ infimumOn (f n) B) atTop) ∧
      (∀ O : Set E, IsOpen O → limsup (fun n ↦ infimumOn (f n) O) atTop ≤ infimumOn g O) := by
  rw [← le_epiLowerLimit_iff_infimumOn_compact hg, ← epiUpperLimit_le_iff_infimumOn_open,
    epiConverges_iff_epiLimits_eq]
  obtain hlu := epiLowerLimit_le_epiUpperLimit f
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨hl.ge, hu.le⟩
  · rintro ⟨hl, hu⟩
    exact ⟨le_antisymm (hlu.trans hu) hl, le_antisymm hu (hl.trans hlu)⟩

/-- **Proposition 7.30**, the unconditional bound on the optimal values. -/
theorem limsup_iInf_le_of_epiUpperLimit_le {f : ℕ → E → EReal} {g : E → EReal}
    (h : epiUpperLimit f ≤ g) :
    limsup (fun n ↦ ⨅ x, f n x) atTop ≤ ⨅ x, g x := by
  simpa only [infimumOn_univ] using (epiUpperLimit_le_iff_infimumOn_open.1 h) univ isOpen_univ

theorem liminf_add_tendsto_real_le {u : ℕ → EReal} {v : ℕ → ℝ} {e : ℝ}
    (hv : Tendsto v atTop (𝓝 e)) :
    liminf (fun n ↦ u n + (v n : EReal)) atTop ≤ liminf u atTop + (e : EReal) := by
  have he := (EReal.tendsto_coe.2 hv).limsup_eq
  simpa only [Pi.add_apply, add_comm, he] using
    (EReal.liminf_add_le (u := fun n ↦ (v n : EReal)) (v := u) (f := atTop)
      (.inl (he ▸ EReal.coe_ne_bot _)) (.inl (he ▸ EReal.coe_ne_top _)))

/-- **Proposition 7.30**, the approximate-minimizer conclusion from upper
epigraphical nesting and convergence of values on convergent near-minimizers.
The feasible limit hypothesis is necessary by `epigraphicalNesting_top_argmin_obstruction`. -/
theorem outerSetLimit_approxArgmin_subset_argmin_of_epiUpperLimit_le
    {f : ℕ → E → EReal} {g : E → EReal} (h : epiUpperLimit f ≤ g) (hg : (⨅ x, g x) < ⊤)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hvals : ∀ (φ : ℕ → ℕ) (xs : ℕ → E) (x : E), StrictMono φ →
      (∀ k, xs k ∈ approxArgmin (f (φ k)) (ε (φ k))) → Tendsto xs atTop (𝓝 x) →
      Tendsto (fun k ↦ f (φ k) (xs k)) atTop (𝓝 (g x))) :
    outerSetLimit (fun n ↦ approxArgmin (f n) (ε n)) ⊆ argmin g := by
  apply outerSetLimit_approxArgmin_subset_argmin_of_values_tendsto _ hg hε hvals
  rw [← epigraph_epiUpperLimit]
  exact epigraph_subset_epigraph_iff.2 h

/-- **Theorem 7.31(a)**. The real number `a` is the finite infimum of `g`. -/
theorem tendsto_iInf_iff_compact_approximation [ProperSpace E]
    {f : ℕ → E → EReal} {g : E → EReal} (h : EpiConverges f g)
    {a : ℝ} (ha : (⨅ x, g x) = (a : EReal)) :
    Tendsto (fun n ↦ ⨅ x, f n x) atTop (𝓝 (a : EReal)) ↔
      ∀ ε : ℝ, 0 < ε → ∃ B : Set E, IsCompact B ∧
        ∀ᶠ n in atTop, infimumOn (f n) B ≤ (⨅ x, f n x) + (ε : EReal) := by
  obtain ⟨hl, hu⟩ := epiConverges_iff_epiLimits_eq.1 h
  have hg := lowerSemicontinuous_of_isClosed_epigraph_ereal g (PKConverges.isClosed h)
  have hlo := (le_epiLowerLimit_iff_infimumOn_compact hg).1 hl.ge
  have hup := epiUpperLimit_le_iff_infimumOn_open.1 hu.le
  have hopt := limsup_iInf_le_of_epiUpperLimit_le hu.le
  rw [ha] at hopt
  constructor
  · intro ht ε hε
    have hlt : (⨅ x, g x) < ((a + ε / 3 : ℝ) : EReal) := by
      rw [ha, EReal.coe_lt_coe_iff]; linarith
    obtain ⟨x, hx⟩ := iInf_lt_iff.mp hlt
    let O := ball x 1
    let B := closedBall x 1
    have h₁ := eventually_lt_of_limsup_lt ((hup O isOpen_ball).trans_lt
      ((infimumOn_le (mem_ball_self zero_lt_one)).trans_lt hx))
    have h₂ : ∀ᶠ n in atTop, ((a - ε / 3 : ℝ) : EReal) < ⨅ y, f n y :=
      ht.eventually_const_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
    refine ⟨B, isCompact_closedBall _ _, ?_⟩
    filter_upwards [h₁, h₂] with n hn₁ hn₂
    have hBO : infimumOn (f n) B ≤ infimumOn (f n) O :=
      le_infimumOn fun y hy ↦ infimumOn_le (ball_subset_closedBall hy)
    calc
      _ ≤ ((a + ε / 3 : ℝ) : EReal) := hBO.trans hn₁.le
      _ ≤ ((a - ε / 3 : ℝ) : EReal) + (ε : EReal) := by
        rw [← EReal.coe_add, EReal.coe_le_coe_iff]; linarith
      _ ≤ _ := add_le_add hn₂.le le_rfl
  · intro hB
    apply tendsto_of_le_liminf_of_limsup_le _ hopt
    by_contra! hlt
    obtain ⟨b, hLb, hba⟩ := EReal.exists_between_coe_real hlt
    let ε := (a - b) / 2
    have hε : 0 < ε := by have := EReal.coe_lt_coe_iff.mp hba; dsimp [ε]; linarith
    obtain ⟨B, hc, he⟩ := hB ε hε
    have hglob : (a : EReal) ≤ infimumOn g B := ha ▸ le_infimumOn fun x _ ↦ iInf_le g x
    have hall := ((hglob.trans (hlo B hc)).trans (liminf_le_liminf he)).trans
      (liminf_add_tendsto_real_le (v := fun _ ↦ ε) tendsto_const_nhds)
    have hbound := hall.trans (add_le_add hLb.le (le_rfl : (ε : EReal) ≤ ε))
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hbound
    have := EReal.coe_lt_coe_iff.mp hba
    dsimp [ε] at hbound
    linarith

/-- **Theorem 7.31(b)**, allowing any real tolerances converging to `e`. -/
theorem outerSetLimit_approxArgmin_subset_of_epiConverges
    {f : ℕ → E → EReal} {g : E → EReal} (h : EpiConverges f g)
    {ε : ℕ → ℝ} {e : ℝ} (hε : Tendsto ε atTop (𝓝 e)) :
    outerSetLimit (fun n ↦ approxArgmin (f n) (ε n)) ⊆ approxArgmin g e := by
  obtain ⟨hl, hu⟩ := epiConverges_iff_epiLimits_eq.1 h
  intro x hx
  obtain ⟨φ, xs, hφ, hxs, hto⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hx
  have hlow := epiLowerLimit_le_liminf_subsequence (f := f) hφ hto
  rw [hl] at hlow
  exact (hlow.trans (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault))).trans
    (limsup_le_of_mem_approxArgmin (limsup_iInf_le_of_epiUpperLimit_le hu.le) hε hφ (Eventually.of_forall hxs))

/-- **Theorem 7.31(b)**, cluster points of vanishing-error minimizers. -/
theorem outerSetLimit_approxArgmin_subset_argmin_of_epiConverges
    {f : ℕ → E → EReal} {g : E → EReal} (h : EpiConverges f g)
    (hg : (⨅ x, g x) < ⊤) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) :
    outerSetLimit (fun n ↦ approxArgmin (f n) (ε n)) ⊆ argmin g := by
  simpa only [approxArgmin_zero hg] using outerSetLimit_approxArgmin_subset_of_epiConverges h hε

/-- A null sequence has a nonnegative decreasing majorant tending to zero. -/
private theorem exists_antitone_majorant_tendsto_zero {d : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ, Antitone ε ∧ (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧ ∀ n, d n ≤ ε n := by
  let S := fun n : ℕ ↦ (fun k ↦ |d k|) '' Ici n
  let ε := fun n ↦ sSup (S n)
  have habs : Tendsto (fun n ↦ |d n|) atTop (𝓝 0) := by simpa using hd.abs
  have hb : ∀ n, BddAbove (S n) := fun _ ↦
    (isBounded_range_of_tendsto _ habs).bddAbove.mono (image_subset_range _ _)
  have hself : ∀ n, |d n| ∈ S n := fun n ↦ ⟨n, (show n ≤ n from Nat.le_refl n), rfl⟩
  have hmajor : ∀ n, |d n| ≤ ε n := fun n ↦ le_csSup (hb _) (hself n)
  have hpos : ∀ n, 0 ≤ ε n := fun n ↦ (abs_nonneg _).trans (hmajor n)
  refine ⟨ε, fun n m hnm ↦ csSup_le_csSup (hb n) ⟨_, hself m⟩
    (image_mono (Ici_subset_Ici.2 hnm)), hpos, ?_, fun n ↦ (le_abs_self _).trans (hmajor n)⟩
  rw [Metric.tendsto_atTop]
  intro r hr
  obtain ⟨N, hN⟩ := eventually_atTop.1 (habs.eventually_le_const (half_pos hr))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpos n)]
  apply lt_of_le_of_lt _ (half_lt_self hr)
  apply csSup_le ⟨_, hself n⟩
  rintro _ ⟨k, hk, rfl⟩
  exact hN k (hn.trans hk)

/-- Transfer a common family of recovering levels (Proposition 7.7) into the
vanishing-error sets in **Theorem 7.31(c)**. Taking a majorant also ensures
the errors can be chosen decreasing even when the optimal values oscillate. -/
theorem exists_antitone_approxArgmin_of_recovering_levels {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) {a : ℝ} (ha : (⨅ x, g x) = (a : EReal))
    (ht : Tendsto (fun n ↦ ⨅ x, f n x) atTop (𝓝 (a : EReal))) {b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 a))
    (hin : levelSet g a ⊆ innerSetLimit (fun n ↦ levelSet (f n) (b n))) :
    ∃ ε : ℕ → ℝ, Antitone ε ∧ (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      PKConverges (fun n ↦ approxArgmin (f n) (ε n)) (argmin g) := by
  let v := fun n ↦ (⨅ x, f n x).toReal
  have hv : Tendsto v atTop (𝓝 a) := by
    simpa only [v, EReal.toReal_coe] using
      (EReal.tendsto_toReal (EReal.coe_ne_top a) (EReal.coe_ne_bot a)).comp ht
  have hd : Tendsto (fun n ↦ b n - v n) atTop (𝓝 0) := by simpa using hb.sub hv
  obtain ⟨ε, hmono, hpos, hε, hmaj⟩ := exists_antitone_majorant_tendsto_zero hd
  have hfin : ∀ᶠ n in atTop, (v n : EReal) = ⨅ x, f n x := by
    filter_upwards [ht.eventually_const_lt (EReal.bot_lt_coe a),
      ht.eventually_lt_const (EReal.coe_lt_top a)] with n hlow hupp
    exact EReal.coe_toReal hupp.ne hlow.ne'
  have hsub : ∀ᶠ n in atTop, levelSet (f n) (b n) ⊆ approxArgmin (f n) (ε n) := by
    filter_upwards [hfin] with n hn y hy
    change f n y ≤ (⨅ x, f n x) + (ε n : EReal)
    apply le_trans (show f n y ≤ (b n : EReal) from hy)
    rw [← hn, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith [hmaj n]
  have hu := outerSetLimit_approxArgmin_subset_argmin_of_epiConverges h
    (ha ▸ EReal.coe_lt_top a) hε
  have hl : argmin g ⊆ innerSetLimit (fun n ↦ approxArgmin (f n) (ε n)) := by
    intro x hx V hV
    have hxlevel : x ∈ levelSet g a := (hx.1.trans ha).le
    filter_upwards [hin hxlevel V hV, hsub] with n hn hs
    obtain ⟨y, hy, hyV⟩ := hn
    exact ⟨y, hs hy, hyV⟩
  exact ⟨ε, hmono, hpos, hε, ((innerSetLimit_subset_outerSetLimit _).trans hu).antisymm hl,
    hu.antisymm (hl.trans (innerSetLimit_subset_outerSetLimit _))⟩

/-- **Theorem 7.31(c)**, convergence of finite infima supplies a single
decreasing sequence of errors recovering the entire limiting optimal set. -/
theorem exists_antitone_approxArgmin_of_tendsto_iInf [SecondCountableTopology E] {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) {a : ℝ} (ha : (⨅ x, g x) = (a : EReal))
    (ht : Tendsto (fun n ↦ ⨅ x, f n x) atTop (𝓝 (a : EReal))) :
    ∃ ε : ℕ → ℝ, Antitone ε ∧ (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      PKConverges (fun n ↦ approxArgmin (f n) (ε n)) (argmin g) := by
  obtain ⟨b, _, hb, hin⟩ := epiUpperLimit_le_iff_exists_antitone_level.1
    (epiConverges_iff_epiLimits_eq.1 h).2.le a
  exact exists_antitone_approxArgmin_of_recovering_levels h ha ht hb hin

/-- **Theorem 7.31(c)**, converse: convergence of vanishing-error minimizer
sets to a nonempty `argmin g` forces the optimal values to converge. -/
theorem tendsto_iInf_of_approxArgmin_converges {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hg : (argmin g).Nonempty) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0))
    (hsets : PKConverges (fun n ↦ approxArgmin (f n) (ε n)) (argmin g)) :
    Tendsto (fun n ↦ ⨅ x, f n x) atTop (𝓝 (⨅ x, g x)) := by
  obtain ⟨x, hx⟩ := hg
  obtain ⟨hl, hu⟩ := epiConverges_iff_epiLimits_eq.1 h
  obtain ⟨xs, hxs, hto⟩ := mem_innerSetLimit_iff_exists_seq.1 (hsets.inner_eq.symm ▸ hx)
  apply tendsto_of_le_liminf_of_limsup_le _ (limsup_iInf_le_of_epiUpperLimit_le hu.le)
  have hlow := epiLowerLimit_le_liminf (f := f) hto
  rw [hl, hx.1] at hlow
  have hvals : ∀ᶠ n in atTop, f n (xs n) ≤ (⨅ y, f n y) + (ε n : EReal) := hxs
  simpa only [EReal.coe_zero, add_zero] using
    (hlow.trans (liminf_le_liminf hvals)).trans (liminf_add_tendsto_real_le hε)

end RW
