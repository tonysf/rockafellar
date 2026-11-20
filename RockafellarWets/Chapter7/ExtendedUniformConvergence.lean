/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Extended uniform convergence

Definitions and characterizations of uniform convergence for functions with
values in the extended reals (7.12–7.14).
-/

import RockafellarWets.Chapter7.ProfileConvergence
import RockafellarWets.Chapter5.ContinuousVersusUniform

open Filter Metric Set Topology

namespace RW

/-- The real-valued truncation at height `ρ` from Definition 7.12. -/
noncomputable def erealTrunc (ρ : ℝ) (a : EReal) : ℝ :=
  (max ((-ρ : ℝ) : EReal) (min a (ρ : EReal))).toReal

theorem coe_erealTrunc (ρ : ℝ) (a : EReal) :
    (erealTrunc ρ a : EReal) = max ((-ρ : ℝ) : EReal) (min a (ρ : EReal)) := by
  apply EReal.coe_toReal
  · exact (max_lt (EReal.coe_lt_top _) ((min_le_right ..).trans_lt (EReal.coe_lt_top _))).ne
  · exact ((EReal.bot_lt_coe _).trans_le (le_max_left ..)).ne'

theorem continuous_erealTrunc (ρ : ℝ) : Continuous (erealTrunc ρ) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have h : Continuous (fun z : EReal ↦ max ((-ρ : ℝ) : EReal) (min z (ρ : EReal))) :=
    continuous_const.max (continuous_id.min continuous_const)
  apply (EReal.tendsto_toReal _ _).comp h.continuousAt
  · exact (max_lt (EReal.coe_lt_top _) ((min_le_right ..).trans_lt (EReal.coe_lt_top _))).ne
  · exact ((EReal.bot_lt_coe _).trans_le (le_max_left ..)).ne'

theorem erealTrunc_mem_Icc {ρ : ℝ} (hρ : 0 ≤ ρ) (a : EReal) :
    erealTrunc ρ a ∈ Icc (-ρ) ρ := by
  constructor <;> apply EReal.coe_le_coe_iff.mp <;> rw [coe_erealTrunc]
  · exact le_max_left ..
  · exact max_le (EReal.coe_le_coe_iff.mpr (by linarith)) (min_le_right ..)

/-- The lower branch of the truncation, including the value `⊥`. -/
theorem erealTrunc_of_le_lower {ρ : ℝ} {a : EReal} (ha : a ≤ ((-ρ : ℝ) : EReal)) :
    erealTrunc ρ a = -ρ := by
  apply EReal.coe_injective
  rw [coe_erealTrunc, max_eq_left ((min_le_left ..).trans ha)]

/-- The upper branch, including the value `⊤`. -/
theorem erealTrunc_of_upper_le {ρ : ℝ} (hρ : 0 ≤ ρ) {a : EReal} (ha : (ρ : EReal) ≤ a) :
    erealTrunc ρ a = ρ := by
  apply EReal.coe_injective
  rw [coe_erealTrunc, min_eq_right ha, max_eq_right (EReal.coe_le_coe_iff.mpr (by linarith))]

theorem erealTrunc_le_of_le {a : EReal} {ρ t : ℝ} (hlt : -ρ ≤ t) (ha : a ≤ (t : EReal)) :
    erealTrunc ρ a ≤ t := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_erealTrunc]
  exact max_le (EReal.coe_le_coe_iff.mpr hlt) ((min_le_left ..).trans ha)

theorem le_erealTrunc_of_le {a : EReal} {ρ t : ℝ} (ht : t ≤ ρ) (ha : (t : EReal) ≤ a) :
    t ≤ erealTrunc ρ a := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_erealTrunc]
  exact (le_min ha (EReal.coe_le_coe_iff.mpr ht)).trans (le_max_right ..)

theorem le_coe_erealTrunc_of_lt {a : EReal} {ρ : ℝ} (ha : erealTrunc ρ a < ρ) :
    a ≤ (erealTrunc ρ a : EReal) := by
  have h : (erealTrunc ρ a : EReal) < (ρ : EReal) := EReal.coe_lt_coe_iff.mpr ha
  rw [coe_erealTrunc] at h ⊢
  have h' : a < (ρ : EReal) := lt_of_not_ge fun hn ↦
    (not_le_of_gt h) (by rw [min_eq_right hn]; exact le_max_right ..)
  rw [min_eq_left h'.le]
  exact le_max_right ..

theorem coe_erealTrunc_le_of_lt {a : EReal} {ρ : ℝ} (ha : -ρ < erealTrunc ρ a) :
    (erealTrunc ρ a : EReal) ≤ a := by
  have h := EReal.coe_lt_coe_iff.mpr ha
  rw [coe_erealTrunc] at h ⊢
  rw [max_eq_right ((lt_max_iff.mp h).resolve_left (lt_irrefl _)).le]
  exact min_le_left ..

/-- **Definition 7.12.** Every finite truncation converges uniformly in the
usual real-valued sense. -/
def ERealConvergesUniformlyOn {E : Type*} (f : ℕ → E → EReal) (g : E → EReal)
    (X : Set E) : Prop :=
  ∀ ρ > 0, TendstoUniformlyOn (fun n x ↦ erealTrunc ρ (f n x))
    (fun x ↦ erealTrunc ρ (g x)) atTop X

theorem erealTrunc_coe_of_mem {ρ t : ℝ} (ht : t ∈ Icc (-ρ) ρ) :
    erealTrunc ρ (t : EReal) = t :=
  (erealTrunc_le_of_le ht.1 le_rfl).antisymm (le_erealTrunc_of_le ht.2 le_rfl)

/-- When the limit is bounded on the test set, extended uniform convergence
of finite functions gives ordinary uniform convergence (remark after 7.12). -/
theorem ERealConvergesUniformlyOn.tendstoUniformlyOn_of_bounded
    {E : Type*} {f : ℕ → E → ℝ} {g : E → ℝ} {X : Set E}
    (hu : ERealConvergesUniformlyOn (fun n x ↦ (f n x : EReal)) (fun x ↦ (g x : EReal)) X)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x ∈ X, |g x| ≤ M) : TendstoUniformlyOn f g atTop X := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let ρ := M + ε + 1
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hu ρ hρ) ε hε] with n hn
  intro x hx
  have hg := abs_le.mp (hb x hx)
  have hg' : erealTrunc ρ (g x : EReal) = g x := erealTrunc_coe_of_mem
    ⟨by dsimp [ρ]; linarith [hg.1], by dsimp [ρ]; linarith [hg.2]⟩
  have hd := hn x hx
  rw [hg', Real.dist_eq, abs_lt] at hd
  have hlo : -ρ < erealTrunc ρ (f n x : EReal) := by dsimp [ρ] at *; linarith [hd.2, hg.1]
  have hhi : erealTrunc ρ (f n x : EReal) < ρ := by dsimp [ρ] at *; linarith [hd.1, hg.2]
  have heq : erealTrunc ρ (f n x : EReal) = f n x := EReal.coe_injective
    ((coe_erealTrunc_le_of_lt hlo).antisymm (le_coe_erealTrunc_of_lt hhi))
  simpa only [heq, Real.dist_eq, abs_lt] using hd

private theorem epiProfile_inclusion_of_trunc {a b : EReal} {ρ ε : ℝ}
    (hε : 0 < ε)
    (h : erealTrunc (ρ + ε) b < erealTrunc (ρ + ε) a + ε / 2) :
    {t : ℝ | a ≤ (t : EReal)} ∩ closedBall 0 ρ ⊆
      thickening ε {t : ℝ | b ≤ (t : EReal)} := by
  rintro t ⟨ha, ht⟩
  have ht' := abs_le.mp (mem_closedBall_zero_iff.mp ht : |t| ≤ ρ)
  have hta := erealTrunc_le_of_le (by linarith : -(ρ + ε) ≤ t) ha
  have htb : erealTrunc (ρ + ε) b < t + ε / 2 := by linarith
  have hb := le_coe_erealTrunc_of_lt (lt_of_lt_of_le htb (by linarith))
  refine mem_thickening_iff.mpr ⟨t + ε / 2, hb.trans (EReal.coe_le_coe_iff.mpr htb.le), ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private theorem trunc_le_of_epiProfile_inclusion {a b : EReal} {ρ ε : ℝ}
    (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (h : {t : ℝ | a ≤ (t : EReal)} ∩ closedBall 0 ρ ⊆
      thickening ε {t : ℝ | b ≤ (t : EReal)}) :
    erealTrunc ρ b < erealTrunc ρ a + ε := by
  have ha := erealTrunc_mem_Icc hρ a
  by_cases ht : erealTrunc ρ a < ρ
  · obtain ⟨s, hs, hdist⟩ := mem_thickening_iff.mp
      (h ⟨le_coe_erealTrunc_of_lt ht, mem_closedBall_zero_iff.mpr (abs_le.mpr ha)⟩)
    rw [Real.dist_eq, abs_lt] at hdist
    have hs' := hdist.1
    by_cases hlow : -ρ ≤ s
    · linarith [erealTrunc_le_of_le hlow hs]
    · have hb := erealTrunc_le_of_le (le_refl (-ρ))
          (hs.trans (EReal.coe_le_coe_iff.mpr (le_of_not_ge hlow)))
      linarith [ha.1]
  · linarith [(erealTrunc_mem_Icc hρ b).2]

/-- **Proposition 7.13(a,b).** Upper rays converge uniformly as set-valued
maps precisely when the functions converge uniformly in the extended sense. -/
theorem erealConvergesUniformlyOn_iff_epiProfile {E : Type*}
    {f : ℕ → E → EReal} {g : E → EReal} {X : Set E} :
    ERealConvergesUniformlyOn f g X ↔
      SvConvergesUniformlyOn (fun n ↦ epiProfile (f n)) (epiProfile g) X := by
  constructor
  · intro h ε hε ρ hρ
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h (ρ + ε) (by linarith))
      (ε / 2) (by linarith)] with n hn
    intro x hx
    have hd := hn x hx
    rw [Real.dist_eq, abs_lt] at hd
    exact ⟨epiProfile_inclusion_of_trunc hε (by linarith [hd.2]),
      epiProfile_inclusion_of_trunc hε (by linarith [hd.1])⟩
  · intro h ρ hρ
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [h ε hε ρ hρ] with n hn
    intro x hx
    obtain ⟨h₁, h₂⟩ := hn x hx
    rw [Real.dist_eq, abs_lt]
    have h₃ := trunc_le_of_epiProfile_inclusion hρ.le hε h₁
    have h₄ := trunc_le_of_epiProfile_inclusion hρ.le hε h₂
    constructor <;> linarith

private theorem hypoProfile_inclusion_of_trunc {a b : EReal} {ρ ε : ℝ}
    (hε : 0 < ε)
    (h : erealTrunc (ρ + ε) a - ε / 2 < erealTrunc (ρ + ε) b) :
    {t : ℝ | (t : EReal) ≤ a} ∩ closedBall 0 ρ ⊆
      thickening ε {t : ℝ | (t : EReal) ≤ b} := by
  rintro t ⟨ha, ht⟩
  have ht' := abs_le.mp (mem_closedBall_zero_iff.mp ht : |t| ≤ ρ)
  have hta := le_erealTrunc_of_le (by linarith : t ≤ ρ + ε) ha
  have htb : t - ε / 2 < erealTrunc (ρ + ε) b := by linarith
  have hb := coe_erealTrunc_le_of_lt (lt_of_le_of_lt (by linarith) htb)
  refine mem_thickening_iff.mpr ⟨t - ε / 2, (EReal.coe_le_coe_iff.mpr htb.le).trans hb, ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private theorem le_trunc_of_hypoProfile_inclusion {a b : EReal} {ρ ε : ℝ}
    (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (h : {t : ℝ | (t : EReal) ≤ a} ∩ closedBall 0 ρ ⊆
      thickening ε {t : ℝ | (t : EReal) ≤ b}) :
    erealTrunc ρ a - ε < erealTrunc ρ b := by
  have ha := erealTrunc_mem_Icc hρ a
  by_cases ht : -ρ < erealTrunc ρ a
  · obtain ⟨s, hs, hdist⟩ := mem_thickening_iff.mp
      (h ⟨coe_erealTrunc_le_of_lt ht, mem_closedBall_zero_iff.mpr (abs_le.mpr ha)⟩)
    rw [Real.dist_eq, abs_lt] at hdist
    have hs' := hdist.2
    by_cases hhigh : s ≤ ρ
    · linarith [le_erealTrunc_of_le hhigh hs]
    · have hb := le_erealTrunc_of_le (le_refl ρ)
          ((EReal.coe_le_coe_iff.mpr (le_of_not_ge hhigh)).trans hs)
      linarith [ha.2]
  · linarith [(erealTrunc_mem_Icc hρ b).1]

/-- **Proposition 7.13(a,c).** Lower rays likewise characterize uniform convergence. -/
theorem erealConvergesUniformlyOn_iff_hypoProfile {E : Type*}
    {f : ℕ → E → EReal} {g : E → EReal} {X : Set E} :
    ERealConvergesUniformlyOn f g X ↔
      SvConvergesUniformlyOn (fun n ↦ hypoProfile (f n)) (hypoProfile g) X := by
  constructor
  · intro h ε hε ρ hρ
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h (ρ + ε) (by linarith))
      (ε / 2) (by linarith)] with n hn
    intro x hx
    have hd := hn x hx
    rw [Real.dist_eq, abs_lt] at hd
    exact ⟨hypoProfile_inclusion_of_trunc hε (by linarith [hd.1]),
      hypoProfile_inclusion_of_trunc hε (by linarith [hd.2])⟩
  · intro h ρ hρ
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [h ε hε ρ hρ] with n hn
    intro x hx
    obtain ⟨h₁, h₂⟩ := hn x hx
    rw [Real.dist_eq, abs_lt]
    have h₃ := le_trunc_of_hypoProfile_inclusion hρ.le hε h₁
    have h₄ := le_trunc_of_hypoProfile_inclusion hρ.le hε h₂
    constructor <;> linarith

/-- If the limit is real and bounded on the test set, the approximants
are eventually finite and bounded there by a single constant. -/
theorem ERealConvergesUniformlyOn.eventually_bounded_of_bounded_limit
    {E : Type*} {f : ℕ → E → EReal} {g : E → ℝ} {X : Set E}
    (hu : ERealConvergesUniformlyOn f (fun x ↦ (g x : EReal)) X)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x ∈ X, |g x| ≤ M) :
    ∀ᶠ n in atTop, ∀ x ∈ X, ∃ r : ℝ, f n x = (r : EReal) ∧ |r| < M + 1 := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hu (M + 1) (by linarith)) 1 one_pos]
    with n hn
  intro x hx
  have hg := abs_le.mp (hb x hx)
  have hd := hn x hx
  rw [erealTrunc_coe_of_mem (t := g x) ⟨by linarith [hg.1], by linarith [hg.2]⟩,
    Real.dist_eq, abs_lt] at hd
  have hlo : -(M + 1) < erealTrunc (M + 1) (f n x) := by linarith [hg.1, hd.2]
  have hhi : erealTrunc (M + 1) (f n x) < M + 1 := by linarith [hg.2, hd.1]
  exact ⟨_, (le_coe_erealTrunc_of_lt hhi).antisymm (coe_erealTrunc_le_of_lt hlo),
    abs_lt.mpr ⟨hlo, hhi⟩⟩

/-- The two inequalities in 7(14). On its stated range, the first
truncation is the larger of the limit value and `-ρ`; the second is the
smaller of the limit value and `ρ`. -/
def ERealUniformBoundsOn {E : Type*} (f : ℕ → E → EReal) (g : E → EReal)
    (X : Set E) : Prop :=
  ∀ ρ > 0, ∀ ε ∈ Ioo (0 : ℝ) ρ, ∀ᶠ n in atTop, ∀ x ∈ X,
    (g x ≤ ((ρ - ε : ℝ) : EReal) → f n x ≤ ((erealTrunc ρ (g x) + ε : ℝ) : EReal)) ∧
    (((-ρ + ε : ℝ) : EReal) ≤ g x → ((erealTrunc ρ (g x) - ε : ℝ) : EReal) ≤ f n x)

/-- **Proposition 7.13(a,d).** Two-sided bounds only where the limit is
away from the corresponding truncation endpoint suffice. -/
theorem erealConvergesUniformlyOn_iff_uniformBounds {E : Type*}
    {f : ℕ → E → EReal} {g : E → EReal} {X : Set E} :
    ERealConvergesUniformlyOn f g X ↔ ERealUniformBoundsOn f g X := by
  constructor
  · intro h ρ hρ ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h ρ hρ) ε hε.1] with n hn
    intro x hx
    have hd := hn x hx
    rw [Real.dist_eq, abs_lt] at hd
    constructor
    · intro hg
      have ht := erealTrunc_le_of_le (by linarith [hε.2] : -ρ ≤ ρ - ε) hg
      exact (le_coe_erealTrunc_of_lt (by linarith [hd.1] : erealTrunc ρ (f n x) < ρ)).trans
        (EReal.coe_le_coe_iff.mpr (by linarith [hd.1]))
    · intro hg
      have ht := le_erealTrunc_of_le (by linarith [hε.2] : -ρ + ε ≤ ρ) hg
      exact (EReal.coe_le_coe_iff.mpr (by linarith [hd.2])).trans
        (coe_erealTrunc_le_of_lt (by linarith [hd.2] : -ρ < erealTrunc ρ (f n x)))
  · intro h ρ hρ
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    let δ := min ρ ε / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hdρ : δ < ρ := by dsimp [δ]; linarith [min_le_left ρ ε]
    have hdε : δ < ε := by dsimp [δ]; linarith [min_le_right ρ ε]
    filter_upwards [h ρ hρ δ ⟨hδ, hdρ⟩] with n hn
    intro x hx
    obtain ⟨h₁, h₂⟩ := hn x hx
    have hg := erealTrunc_mem_Icc hρ.le (g x)
    have hf := erealTrunc_mem_Icc hρ.le (f n x)
    rw [Real.dist_eq, abs_lt]
    constructor
    · by_cases hlow : g x ≤ ((ρ - δ : ℝ) : EReal)
      · have : erealTrunc ρ (f n x) ≤ erealTrunc ρ (g x) + δ :=
          erealTrunc_le_of_le (by linarith [hg.1]) (h₁ hlow)
        linarith
      · have := le_erealTrunc_of_le (by linarith : ρ - δ ≤ ρ) (le_of_not_ge hlow)
        linarith [hf.2]
    · by_cases hhigh : ((-ρ + δ : ℝ) : EReal) ≤ g x
      · have : erealTrunc ρ (g x) - δ ≤ erealTrunc ρ (f n x) :=
          le_erealTrunc_of_le (by linarith [hg.2]) (h₂ hhigh)
        linarith
      · have := erealTrunc_le_of_le (by linarith : -ρ ≤ -ρ + δ) (le_of_not_ge hhigh)
        linarith [hf.1]

/-- **Theorem 7.14.** Continuous convergence on a set is equivalent to continuity
of the limit there and extended uniform convergence on each compact subset. -/
theorem convergesContinuouslyOn_iff_continuousOn_and_erealConvergesUniformlyOn
    {E : Type*} [PseudoMetricSpace E] {f : ℕ → E → EReal} {g : E → EReal} {X : Set E} :
    (∀ x ∈ X, ConvergesContinuouslyWithinAt f g X x) ↔
      ContinuousOn g X ∧ ∀ B ⊆ X, IsCompact B → ERealConvergesUniformlyOn f g B := by
  simp only [← svConvergesContinuouslyWithinAt_epiProfile_iff,
    erealConvergesUniformlyOn_iff_epiProfile]
  change SvConvergesContinuouslyOn _ _ _ ↔ _
  rw [svConvergesContinuouslyOn_iff, and_comm]
  exact and_congr (forall_congr' fun x ↦ forall_congr' fun _ ↦
    svContinuousWithinAt_epiProfile_iff g X x) Iff.rfl

/-- **Theorem 7.14**, local conclusion. Pointwise convergence in a relative
neighborhood suffices for continuity at a point of continuous convergence. -/
theorem continuousWithinAt_of_convergesContinuouslyWithinAt {E : Type*} [PseudoMetricSpace E]
    {f : ℕ → E → EReal} {g : E → EReal} {X : Set E} {x : E} (hx : x ∈ X)
    (hc : ConvergesContinuouslyWithinAt f g X x)
    (hp : ∃ V ∈ 𝓝 x, ∀ y ∈ X ∩ V, Tendsto (fun n ↦ f n y) atTop (𝓝 (g y))) :
    ContinuousWithinAt g X x := by
  obtain ⟨V, hV, h⟩ := hp
  exact (svContinuousWithinAt_epiProfile_iff g X x).mp
    (svContinuousWithinAt_of_svConvergesContinuouslyWithinAt hx
      (svConvergesContinuouslyWithinAt_epiProfile_iff.mpr hc)
      ⟨V, hV, fun y hy ↦ (pkConverges_epiProfile_iff_tendsto _ _).mpr (h y hy)⟩)

end RW
