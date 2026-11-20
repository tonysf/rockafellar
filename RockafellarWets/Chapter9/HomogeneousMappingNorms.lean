/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: outer and inner norms of positively homogeneous mappings

Formulas 9(4) and 9(5) and Proposition 9.23.

* `svOuterNorm H = |H|⁺ = sup_{w ∈ IB} sup_{z ∈ H(w)} |z|` and
  `svInnerNorm H = |H|⁻ = sup_{w ∈ IB} inf_{z ∈ H(w)} |z|`, valued in `[0, ∞]`
  (an infimum over an empty set is `∞`, matching `d(0, ∅) = ∞`).
* For positively homogeneous `H`, `|H|⁺` is the least `κ ≥ 0` with
  `|z| ≤ κ|w|` on `gph H` (`SvPositivelyHomogeneous.svOuterNorm_eq_iInf`), and
  `H` is locally bounded if and only if `|H|⁺ < ∞`
  (`SvPositivelyHomogeneous.svLocallyBounded_iff`).
* Both norms of `w ↦ {Aw}` equal `‖A‖`.
* **Proposition 9.23**: the three characterizations of osc, locally bounded,
  positively homogeneous mappings, and `limsup |Hν|⁺ ≤ |H|⁺` whenever
  `g-limsup Hν ⊂ H`, so local boundedness of `H` passes to `Hν` eventually.

The remark "`|H|⁻ ≤ |H|⁺` always" after 9(5) needs `H` nonempty-valued on
`IB` (`svInnerNorm_le_svOuterNorm`): `svOuterNorm_lt_svInnerNorm_example` is
a positively homogeneous `H` with `|H|⁺ = 0` and `|H|⁻ = ∞`.
-/

import RockafellarWets.Chapter8.HomogeneousMappings
import RockafellarWets.Chapter5.LocalBoundedness
import RockafellarWets.Chapter5.SemicontinuityCriteria
import RockafellarWets.Chapter5.GraphicalLimits
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Filter Set Topology Metric
open scoped ENNReal NNReal Pointwise

namespace RW

section Relative

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- Outer semicontinuity at `x` implies it relative to any set. -/
theorem SvOscAt.svOscWithinAt {S : E → Set F} {x : E} (h : SvOscAt S x) (X : Set E) :
    SvOscWithinAt S X x := by
  intro u hu
  apply h
  intro V hV
  exact (hu V hV).filter_mono nhdsWithin_le_nhds

/-- A sequence eventually in `X` tending to `x`, along which points of `S`
converge, puts the limit in the relative outer limit. -/
theorem mem_svOuterLimitWithin_of_eventually {S : E → Set F} {X : Set E} {x : E}
    {xs : ℕ → E} {us : ℕ → F} {u : F} (hxX : ∀ᶠ n in atTop, xs n ∈ X)
    (hxto : Tendsto xs atTop (𝓝 x)) (hus : ∀ n, us n ∈ S (xs n))
    (huto : Tendsto us atTop (𝓝 u)) : u ∈ svOuterLimitWithin S X x := by
  intro V hV
  rw [Filter.frequently_iff]
  intro A hA
  have h1 : ∀ᶠ n in atTop, xs n ∈ A := (tendsto_nhdsWithin_iff.2 ⟨hxto, hxX⟩) hA
  obtain ⟨n, hnA, hnV⟩ := (h1.and (huto hV)).exists
  exact ⟨xs n, hnA, us n, hus n, hnV⟩

end Relative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Formula 9(4)**: the outer norm `|H|⁺ = sup_{w ∈ IB} sup_{z ∈ H(w)} |z|`. -/
noncomputable def svOuterNorm (H : E → Set F) : ℝ≥0∞ :=
  ⨆ w ∈ closedBall (0 : E) 1, ⨆ z ∈ H w, (‖z‖₊ : ℝ≥0∞)

/-- **Formula 9(5)**: the inner norm `|H|⁻ = sup_{w ∈ IB} inf_{z ∈ H(w)} |z|`. -/
noncomputable def svInnerNorm (H : E → Set F) : ℝ≥0∞ :=
  ⨆ w ∈ closedBall (0 : E) 1, ⨅ z ∈ H w, (‖z‖₊ : ℝ≥0∞)

omit [NormedSpace ℝ F] in
private theorem coe_nnnorm_le_ofReal' {z : F} {r : ℝ} (h : ‖z‖ ≤ r) :
    (‖z‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal r := by
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  exact ENNReal.ofReal_le_ofReal h

omit [NormedSpace ℝ F] in
private theorem coe_nnnorm_le_coe' {z : F} {κ : ℝ≥0} (h : ‖z‖ ≤ κ) : (‖z‖₊ : ℝ≥0∞) ≤ κ :=
  ENNReal.coe_le_coe.2 (by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact h)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem coe_nnnorm_le_svOuterNorm {H : E → Set F} {w : E} {z : F} (hw : ‖w‖ ≤ 1)
    (hz : z ∈ H w) : (‖z‖₊ : ℝ≥0∞) ≤ svOuterNorm H := by
  unfold svOuterNorm
  exact le_iSup₂_of_le w (mem_closedBall_zero_iff.2 hw) (le_iSup₂_of_le z hz le_rfl)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem svOuterNorm_le_iff_ball {H : E → Set F} {κ : ℝ≥0∞} :
    svOuterNorm H ≤ κ ↔ ∀ w : E, ‖w‖ ≤ 1 → ∀ z ∈ H w, (‖z‖₊ : ℝ≥0∞) ≤ κ := by
  simp only [svOuterNorm, iSup_le_iff, mem_closedBall_zero_iff]

/-- A positively homogeneous `H` with `|H|⁺ < ∞` has `|z| ≤ |H|⁺ |w|` on its
graph. -/
theorem SvPositivelyHomogeneous.norm_le_svOuterNorm_mul {H : E → Set F}
    (h : SvPositivelyHomogeneous H) (hfin : svOuterNorm H ≠ ⊤) {w : E} {z : F}
    (hz : z ∈ H w) : ‖z‖ ≤ (svOuterNorm H).toReal * ‖w‖ := by
  have hbound : ∀ w' : E, ‖w'‖ ≤ 1 → ∀ z' ∈ H w', ‖z'‖ ≤ (svOuterNorm H).toReal := by
    intro w' hw' z' hz'
    have h1 := ENNReal.toReal_mono hfin (coe_nnnorm_le_svOuterNorm hw' hz')
    simpa using h1
  have hscale : ∀ c : ℝ, 0 < c → c • z ∈ H (c • w) := fun c hc ↦ by
    rw [h.2 w c hc]
    exact smul_mem_smul_set hz
  rcases eq_or_ne w 0 with rfl | hw
  · -- `H 0` is a cone inside `IB`, hence `{0}`
    by_contra hlt
    rw [norm_zero, mul_zero, not_le] at hlt
    have hM : 0 ≤ (svOuterNorm H).toReal := ENNReal.toReal_nonneg
    have hc : 0 < ((svOuterNorm H).toReal + 1) / ‖z‖ := by positivity
    have h1 := hbound _ (by simp) _ (hscale _ hc)
    rw [norm_smul, Real.norm_of_nonneg hc.le, div_mul_cancel₀ _ hlt.ne'] at h1
    linarith
  · have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hnorm : ‖‖w‖⁻¹ • w‖ ≤ 1 := le_of_eq (by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hw'.le), inv_mul_cancel₀ hw'.ne'])
    have h1 := hbound _ hnorm _ (hscale _ (inv_pos.2 hw'))
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hw'.le), inv_mul_le_iff₀ hw'] at h1
    linarith

/-- For positively homogeneous `H`, `|H|⁺ ≤ κ` exactly when `|z| ≤ κ|w|` on
`gph H`. -/
theorem SvPositivelyHomogeneous.svOuterNorm_le_iff {H : E → Set F}
    (h : SvPositivelyHomogeneous H) {κ : ℝ≥0} :
    svOuterNorm H ≤ κ ↔ ∀ w z, z ∈ H w → ‖z‖ ≤ κ * ‖w‖ := by
  constructor
  · intro hκ w z hz
    have hfin : svOuterNorm H ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hκ
    have hM : (svOuterNorm H).toReal ≤ κ := by
      have := ENNReal.toReal_mono ENNReal.coe_ne_top hκ
      simpa using this
    calc ‖z‖ ≤ (svOuterNorm H).toReal * ‖w‖ := h.norm_le_svOuterNorm_mul hfin hz
      _ ≤ κ * ‖w‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg w)
  · intro hκ
    refine svOuterNorm_le_iff_ball.2 fun w hw z hz ↦ ?_
    have h1 : ‖z‖ ≤ κ := by
      have := mul_le_mul_of_nonneg_left hw κ.coe_nonneg
      linarith [hκ w z hz]
    exact coe_nnnorm_le_coe' h1

/-- The sentence after 9(4): `|H|⁺` is the infimum of all `κ ≥ 0` with
`|z| ≤ κ|w|` for all `(w, z) ∈ gph H`. -/
theorem SvPositivelyHomogeneous.svOuterNorm_eq_iInf {H : E → Set F}
    (h : SvPositivelyHomogeneous H) :
    svOuterNorm H = ⨅ (κ : ℝ≥0) (_ : ∀ w z, z ∈ H w → ‖z‖ ≤ κ * ‖w‖), (κ : ℝ≥0∞) := by
  refine le_antisymm (le_iInf₂ fun κ hκ ↦ h.svOuterNorm_le_iff.2 hκ) ?_
  rcases eq_or_ne (svOuterNorm H) ⊤ with htop | hfin
  · rw [htop]
    exact le_top
  · refine iInf₂_le_of_le (svOuterNorm H).toNNReal (fun w z hz ↦ ?_)
      (le_of_eq (ENNReal.coe_toNNReal hfin))
    simpa using h.norm_le_svOuterNorm_mul hfin hz

/-- Part of 9.23: a positively homogeneous mapping that is locally bounded at
`0` has `|H|⁺ < ∞`. -/
theorem SvPositivelyHomogeneous.svOuterNorm_lt_top_of_svLocallyBoundedAt {H : E → Set F}
    (h : SvPositivelyHomogeneous H) (hlb : SvLocallyBoundedAt H 0) : svOuterNorm H < ⊤ := by
  obtain ⟨δ, hδ, ρ, _, hsub⟩ := svLocallyBoundedAt_iff_exists_closedBall.1 hlb
  have hle : svOuterNorm H ≤ ENNReal.ofReal (ρ / δ) := by
    refine svOuterNorm_le_iff_ball.2 fun w hw z hz ↦ ?_
    have hmem : δ • z ∈ svImage H (closedBall 0 δ) := by
      refine mem_svImage.2 ⟨δ • w, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hδ.le]
        nlinarith [norm_nonneg w]
      · rw [h.2 w δ hδ]
        exact smul_mem_smul_set hz
    have h1 := mem_closedBall_zero_iff.1 (hsub hmem)
    rw [norm_smul, Real.norm_of_nonneg hδ.le] at h1
    have h2 : ‖z‖ ≤ ρ / δ := by
      rw [le_div_iff₀ hδ]
      linarith
    exact coe_nnnorm_le_ofReal' h2
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

/-- Part of 9.23: `|H|⁺ < ∞` makes a positively homogeneous mapping locally
bounded. -/
theorem SvPositivelyHomogeneous.svLocallyBounded_of_svOuterNorm_lt_top {H : E → Set F}
    (h : SvPositivelyHomogeneous H) (hfin : svOuterNorm H < ⊤) : SvLocallyBounded H := by
  intro x
  refine ⟨ball x 1, ball_mem_nhds x one_pos,
    (isBounded_closedBall (x := (0 : F)) (r := (svOuterNorm H).toReal * (‖x‖ + 1))).subset ?_⟩
  intro z hz
  obtain ⟨w, hw, hzw⟩ := mem_svImage.1 hz
  rw [mem_closedBall_zero_iff]
  have hw' : ‖w‖ ≤ ‖x‖ + 1 := by
    have h1 : dist w x < 1 := hw
    have h2 := norm_le_insert' w x
    rw [← dist_eq_norm] at h2
    linarith
  exact (h.norm_le_svOuterNorm_mul hfin.ne hzw).trans
    (mul_le_mul_of_nonneg_left hw' ENNReal.toReal_nonneg)

/-- A positively homogeneous mapping is locally bounded if and only if its
outer norm is finite. -/
theorem SvPositivelyHomogeneous.svLocallyBounded_iff {H : E → Set F}
    (h : SvPositivelyHomogeneous H) : SvLocallyBounded H ↔ svOuterNorm H < ⊤ :=
  ⟨fun hlb ↦ h.svOuterNorm_lt_top_of_svLocallyBoundedAt (hlb 0),
    h.svLocallyBounded_of_svOuterNorm_lt_top⟩

/-- Part of 9.23: the cone `H(0)` is `{0}` once `|H|⁺ < ∞`. -/
theorem SvPositivelyHomogeneous.apply_zero_eq_of_svOuterNorm_lt_top {H : E → Set F}
    (h : SvPositivelyHomogeneous H) (hfin : svOuterNorm H < ⊤) : H 0 = {0} := by
  refine Subset.antisymm (fun z hz ↦ ?_) (singleton_subset_iff.2 h.1)
  have h1 := h.norm_le_svOuterNorm_mul hfin.ne hz
  rw [norm_zero, mul_zero] at h1
  exact mem_singleton_iff.2 (norm_le_zero_iff.1 h1)

/-- Part of 9.23: by positive homogeneity, outer semicontinuity relative to a
neighborhood of `0` is outer semicontinuity everywhere. -/
theorem SvPositivelyHomogeneous.svOsc_of_svOscOn {H : E → Set F}
    (h : SvPositivelyHomogeneous H) {U : Set E} (hU : U ∈ 𝓝 (0 : E)) (hosc : SvOscOn H U) :
    SvOsc H := by
  rw [← isClosed_svGraph_iff_svOsc]
  refine IsSeqClosed.isClosed fun ps p hps hlim ↦ ?_
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hpos : 0 < ‖p.1‖ + 1 := by positivity
  set c : ℝ := r / (2 * (‖p.1‖ + 1)) with hc_def
  have hc : 0 < c := by positivity
  have hcw : c • p.1 ∈ ball (0 : E) r := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hc.le]
    calc c * ‖p.1‖ ≤ c * (‖p.1‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) hc.le
      _ = r / 2 := by rw [hc_def, div_mul_eq_mul_div, mul_div_mul_right _ _ hpos.ne']
      _ < r := by linarith
  have h1 : Tendsto (fun n ↦ c • (ps n).1) atTop (𝓝 (c • p.1)) :=
    ((continuous_fst.tendsto p).comp hlim).const_smul c
  have h2 : Tendsto (fun n ↦ c • (ps n).2) atTop (𝓝 (c • p.2)) :=
    ((continuous_snd.tendsto p).comp hlim).const_smul c
  have hev : ∀ᶠ n in atTop, c • (ps n).1 ∈ U :=
    (h1.eventually (isOpen_ball.mem_nhds hcw)).mono fun n hn ↦ hrU hn
  have hmem : c • p.2 ∈ svOuterLimitWithin H U (c • p.1) := by
    refine mem_svOuterLimitWithin_of_eventually hev h1 (fun n ↦ ?_) h2
    rw [h.2 _ c hc]
    exact smul_mem_smul_set (hps n)
  have h3 := hosc _ (hrU hcw) hmem
  rw [h.2 _ c hc] at h3
  exact (smul_mem_smul_set_iff₀ hc.ne' (H p.1) p.2).1 h3

/-- Part of 9.23: osc at `0` relative to a neighborhood together with
`H(0) = {0}` forces `|H|⁺ < ∞` (compactness of the unit sphere). -/
theorem SvPositivelyHomogeneous.svOuterNorm_lt_top_of_svOscWithinAt [ProperSpace F]
    {H : E → Set F} (h : SvPositivelyHomogeneous H) {U : Set E} (hU : U ∈ 𝓝 (0 : E))
    (hosc : SvOscWithinAt H U 0) (hzero : H 0 = {0}) : svOuterNorm H < ⊤ := by
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  have hpick : ∀ n : ℕ, ∃ w : E, ‖w‖ ≤ 1 ∧ ∃ z ∈ H w, (n : ℝ) + 1 < ‖z‖ := by
    intro n
    by_contra hne
    push_neg at hne
    have h1 : svOuterNorm H ≤ ENNReal.ofReal ((n : ℝ) + 1) := by
      refine svOuterNorm_le_iff_ball.2 fun w hw z hz ↦ ?_
      exact coe_nnnorm_le_ofReal' (hne w hw z hz)
    rw [htop] at h1
    exact ENNReal.ofReal_ne_top (top_le_iff.1 h1)
  choose w hw z hz hzn using hpick
  have hzpos : ∀ n, 0 < ‖z n‖ := fun n ↦ lt_trans (by positivity) (hzn n)
  have hz'mem : ∀ n, ‖z n‖⁻¹ • z n ∈ H (‖z n‖⁻¹ • w n) := fun n ↦ by
    rw [h.2 _ _ (inv_pos.2 (hzpos n))]
    exact smul_mem_smul_set (hz n)
  have hz'norm : ∀ n, ‖z n‖⁻¹ • z n ∈ sphere (0 : F) 1 := fun n ↦ by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hzpos n).le),
      inv_mul_cancel₀ (hzpos n).ne']
  have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hw'lim : Tendsto (fun n ↦ ‖z n‖⁻¹ • w n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) h0
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hzpos n).le)]
    calc ‖z n‖⁻¹ * ‖w n‖ ≤ ‖z n‖⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hw n) (inv_nonneg.2 (hzpos n).le)
      _ ≤ 1 / ((n : ℝ) + 1) := by
          rw [mul_one, one_div]
          exact inv_anti₀ (by positivity) (hzn n).le
  obtain ⟨zbar, hzbar, φ, hφ, hlim⟩ := (isCompact_sphere (0 : F) 1).tendsto_subseq hz'norm
  have hwφ := hw'lim.comp hφ.tendsto_atTop
  have hmem : zbar ∈ svOuterLimitWithin H U 0 :=
    mem_svOuterLimitWithin_of_eventually (hwφ.eventually hU) hwφ (fun n ↦ hz'mem (φ n)) hlim
  have h1 := hosc hmem
  rw [hzero, mem_singleton_iff] at h1
  rw [mem_sphere_zero_iff_norm, h1, norm_zero] at hzbar
  exact zero_ne_one hzbar

/-- **Proposition 9.23**: for positively homogeneous `H`, the following are
equivalent: (a) `H` is osc and locally bounded; (b) `H` is osc relative to some
neighborhood of `0`, and `H(0) = {0}`; (c) `H` is osc relative to `IB`, and
`|H|⁺ < ∞`. -/
theorem SvPositivelyHomogeneous.tfae_svOsc_svLocallyBounded [ProperSpace F] {H : E → Set F}
    (h : SvPositivelyHomogeneous H) :
    List.TFAE [SvOsc H ∧ SvLocallyBounded H,
      (∃ U ∈ 𝓝 (0 : E), SvOscOn H U) ∧ H 0 = {0},
      SvOscOn H (closedBall (0 : E) 1) ∧ svOuterNorm H < ⊤] := by
  tfae_have 1 → 3 := fun ⟨hosc, hlb⟩ ↦
    ⟨fun x _ ↦ (hosc x).svOscWithinAt _, h.svOuterNorm_lt_top_of_svLocallyBoundedAt (hlb 0)⟩
  tfae_have 3 → 2 := fun ⟨hosc, hfin⟩ ↦
    ⟨⟨closedBall 0 1, closedBall_mem_nhds 0 one_pos, hosc⟩,
      h.apply_zero_eq_of_svOuterNorm_lt_top hfin⟩
  tfae_have 2 → 1 := fun ⟨⟨U, hU, hosc⟩, hzero⟩ ↦
    ⟨h.svOsc_of_svOscOn hU hosc, h.svLocallyBounded_of_svOuterNorm_lt_top
      (h.svOuterNorm_lt_top_of_svOscWithinAt hU (hosc 0 (mem_of_mem_nhds hU)) hzero)⟩
  tfae_finish

/-- **Proposition 9.23**, second part: whenever `g-limsup Hν ⊂ H` for positively
homogeneous mappings, `limsup |Hν|⁺ ≤ |H|⁺`. -/
theorem limsup_svOuterNorm_le [ProperSpace E] [ProperSpace F] {Hs : ℕ → E → Set F}
    {H : E → Set F} (hHs : ∀ n, SvPositivelyHomogeneous (Hs n)) (h : SvPositivelyHomogeneous H)
    (hlim : ∀ w, graphicalOuterLimit Hs w ⊆ H w) :
    limsup (fun n ↦ svOuterNorm (Hs n)) atTop ≤ svOuterNorm H := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨κ, hκH, hκlim⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  have hfreq : ∃ᶠ n in atTop, (κ : ℝ≥0∞) < svOuterNorm (Hs n) :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hκlim
  have hpick : ∃ᶠ n in atTop, ∃ w : E, ‖w‖ ≤ 1 ∧ ∃ z ∈ Hs n w, (κ : ℝ) < ‖z‖ := by
    refine hfreq.mono fun n hn ↦ ?_
    by_contra hne
    push_neg at hne
    have h1 : svOuterNorm (Hs n) ≤ κ := svOuterNorm_le_iff_ball.2 fun w hw z hz ↦ by
      exact coe_nnnorm_le_coe' (hne w hw z hz)
    exact absurd hn (not_lt.2 h1)
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hpick
  choose w hw z hz hzκ using hφP
  have hzpos : ∀ n, 0 < ‖z n‖ := fun n ↦ lt_of_le_of_lt κ.coe_nonneg (hzκ n)
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℝ, s = fun n ↦ ‖w n‖ + ‖z n‖ := ⟨_, rfl⟩
  have hsn : ∀ n, s n = ‖w n‖ + ‖z n‖ := fun n ↦ by rw [hs]
  have hspos : ∀ n, 0 < s n := fun n ↦ by
    rw [hsn]
    have := hzpos n
    positivity
  have hsinv : ∀ n, ‖(s n)⁻¹‖ = (s n)⁻¹ := fun n ↦ Real.norm_of_nonneg (inv_nonneg.2 (hspos n).le)
  obtain ⟨p, hp⟩ : ∃ p : ℕ → E × F, p = fun n ↦ ((s n)⁻¹ • w n, (s n)⁻¹ • z n) := ⟨_, rfl⟩
  have hpmem : ∀ n, p n ∈ svGraph (Hs (φ n)) := fun n ↦ by
    rw [hp]
    show (s n)⁻¹ • z n ∈ Hs (φ n) ((s n)⁻¹ • w n)
    rw [(hHs (φ n)).2 _ _ (inv_pos.2 (hspos n))]
    exact smul_mem_smul_set (hz n)
  have hpnorm : ∀ n, ‖(p n).1‖ + ‖(p n).2‖ = 1 := fun n ↦ by
    rw [hp]
    simp only [norm_smul, hsinv]
    rw [← mul_add, ← hsn]
    exact inv_mul_cancel₀ (hspos n).ne'
  have hpbdd : ∀ n, p n ∈ closedBall (0 : E) 1 ×ˢ closedBall (0 : F) 1 := fun n ↦ by
    have h1 := hpnorm n
    have h2 := norm_nonneg (p n).1
    have h3 := norm_nonneg (p n).2
    exact ⟨mem_closedBall_zero_iff.2 (by linarith), mem_closedBall_zero_iff.2 (by linarith)⟩
  obtain ⟨q, -, ψ, hψ, hqlim⟩ :=
    ((isCompact_closedBall (0 : E) 1).prod (isCompact_closedBall (0 : F) 1)).tendsto_subseq hpbdd
  have hqgraph : q ∈ outerSetLimit (fun n ↦ svGraph (Hs n)) :=
    mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ ∘ ψ, p ∘ ψ, hφ.comp hψ, fun n ↦ hpmem (ψ n), hqlim⟩
  have hqH : q.2 ∈ H q.1 := hlim q.1 hqgraph
  have hqnorm : ‖q.1‖ + ‖q.2‖ = 1 := by
    have hc : Continuous fun r : E × F ↦ ‖r.1‖ + ‖r.2‖ := by fun_prop
    have h1 := (hc.tendsto q).comp hqlim
    have h2 : (fun r : E × F ↦ ‖r.1‖ + ‖r.2‖) ∘ (p ∘ ψ) = fun _ ↦ (1 : ℝ) := by
      funext n
      exact hpnorm (ψ n)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hpineq : ∀ n, (κ : ℝ) * ‖(p n).1‖ ≤ ‖(p n).2‖ := fun n ↦ by
    rw [hp]
    simp only [norm_smul, hsinv]
    have h1 : (κ : ℝ) * ‖w n‖ ≤ ‖z n‖ := by
      have := mul_le_mul_of_nonneg_left (hw n) κ.coe_nonneg
      linarith [hzκ n]
    calc (κ : ℝ) * ((s n)⁻¹ * ‖w n‖) = (s n)⁻¹ * ((κ : ℝ) * ‖w n‖) := by ring
      _ ≤ (s n)⁻¹ * ‖z n‖ := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (hspos n).le)
  have hqineq : (κ : ℝ) * ‖q.1‖ ≤ ‖q.2‖ := by
    have hc : Continuous fun r : E × F ↦ ‖r.2‖ - (κ : ℝ) * ‖r.1‖ := by fun_prop
    have h1 := (hc.tendsto q).comp hqlim
    exact sub_nonneg.1 (ge_of_tendsto h1 (Eventually.of_forall fun n ↦
      sub_nonneg.2 (hpineq (ψ n))))
  have hfin : svOuterNorm H ≠ ⊤ := ne_top_of_lt hκH
  have hM : (svOuterNorm H).toReal < κ := by
    have := ENNReal.toReal_strict_mono ENNReal.coe_ne_top hκH
    simpa using this
  have hbound := h.norm_le_svOuterNorm_mul hfin hqH
  have hq1 : ‖q.1‖ = 0 := by
    by_contra hne
    have hq1pos : 0 < ‖q.1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  rw [hq1, mul_zero] at hbound
  have hq2 : ‖q.2‖ = 0 := le_antisymm hbound (norm_nonneg _)
  rw [hq1, hq2] at hqnorm
  norm_num at hqnorm

/-- **Proposition 9.23**, last assertion: if `H` is locally bounded and
`g-limsup Hν ⊂ H`, then `Hν` is locally bounded for all large `ν`. -/
theorem eventually_svLocallyBounded_of_graphicalOuterLimit_subset [ProperSpace E] [ProperSpace F]
    {Hs : ℕ → E → Set F} {H : E → Set F} (hHs : ∀ n, SvPositivelyHomogeneous (Hs n))
    (h : SvPositivelyHomogeneous H) (hlim : ∀ w, graphicalOuterLimit Hs w ⊆ H w)
    (hlb : SvLocallyBounded H) : ∀ᶠ n in atTop, SvLocallyBounded (Hs n) := by
  have hfin := h.svLocallyBounded_iff.1 hlb
  have hev := eventually_lt_of_limsup_lt (lt_of_le_of_lt (limsup_svOuterNorm_le hHs h hlim) hfin)
  exact hev.mono fun n hn ↦ (hHs n).svLocallyBounded_of_svOuterNorm_lt_top hn

/-! ### Linear and single-valued mappings -/

theorem svPositivelyHomogeneous_linear (A : E →L[ℝ] F) :
    SvPositivelyHomogeneous (fun w ↦ ({A w} : Set F)) :=
  ⟨by simp, fun w c _ ↦ by simp [Set.smul_set_singleton]⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- For single-valued mappings the inner and outer norms agree. -/
theorem svInnerNorm_singleton (f : E → F) :
    svInnerNorm (fun w ↦ ({f w} : Set F)) = svOuterNorm (fun w ↦ ({f w} : Set F)) := by
  simp only [svInnerNorm, svOuterNorm, iInf_singleton, iSup_singleton]

/-- When `H(w) = Aw`, `|H|⁺ = ‖A‖`. -/
theorem svOuterNorm_linear (A : E →L[ℝ] F) :
    svOuterNorm (fun w ↦ ({A w} : Set F)) = ‖A‖₊ := by
  have h := svPositivelyHomogeneous_linear A
  refine le_antisymm (h.svOuterNorm_le_iff.2 fun w z hz ↦ ?_) ?_
  · rw [mem_singleton_iff.1 hz]
    exact A.le_opNorm w
  · rcases eq_or_ne (svOuterNorm (fun w ↦ ({A w} : Set F))) ⊤ with htop | hfin
    · rw [htop]
      exact le_top
    · rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
        ENNReal.coe_toNNReal_eq_toReal]
      exact A.opNorm_le_bound ENNReal.toReal_nonneg fun w ↦
        h.norm_le_svOuterNorm_mul hfin (mem_singleton (A w))

/-- When `H(w) = Aw`, `|H|⁻ = ‖A‖`. -/
theorem svInnerNorm_linear (A : E →L[ℝ] F) :
    svInnerNorm (fun w ↦ ({A w} : Set F)) = ‖A‖₊ := by
  rw [svInnerNorm_singleton, svOuterNorm_linear]

/-! ### Inner versus outer norm -/

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- `|H|⁻ ≤ |H|⁺` when `H` has nonempty values on `IB`. -/
theorem svInnerNorm_le_svOuterNorm {H : E → Set F} (hne : ∀ w : E, ‖w‖ ≤ 1 → (H w).Nonempty) :
    svInnerNorm H ≤ svOuterNorm H := by
  unfold svInnerNorm svOuterNorm
  refine iSup₂_mono fun w hw ↦ ?_
  obtain ⟨z, hz⟩ := hne w (mem_closedBall_zero_iff.1 hw)
  exact (iInf₂_le z hz).trans (le_iSup₂ (f := fun z (_ : z ∈ H w) ↦ (‖z‖₊ : ℝ≥0∞)) z hz)

/-- The remark "`|H|⁻ ≤ |H|⁺` always" after 9(5) fails without nonempty
values: the positively homogeneous `H` with `gph H = {(0, 0)}` has `|H|⁺ = 0`
but `|H|⁻ = ∞`, since `inf ∅ = ∞`. -/
theorem svOuterNorm_lt_svInnerNorm_example :
    SvPositivelyHomogeneous (fun w : ℝ ↦ if w = 0 then ({0} : Set ℝ) else ∅) ∧
      svOuterNorm (fun w : ℝ ↦ if w = 0 then ({0} : Set ℝ) else ∅) = 0 ∧
      svInnerNorm (fun w : ℝ ↦ if w = 0 then ({0} : Set ℝ) else ∅) = ⊤ := by
  refine ⟨⟨by simp, fun w c hc ↦ ?_⟩, ?_, ?_⟩
  · by_cases hw : w = 0
    · simp [hw]
    · simp [hw, hc.ne']
  · refine le_antisymm (svOuterNorm_le_iff_ball.2 fun w _ z hz ↦ ?_) (zero_le _)
    split_ifs at hz with hw
    · rw [mem_singleton_iff.1 hz]
      simp
    · simp at hz
  · refine top_le_iff.1 ?_
    unfold svInnerNorm
    refine le_iSup₂_of_le (1 : ℝ) (by simp) ?_
    simp

end RW
