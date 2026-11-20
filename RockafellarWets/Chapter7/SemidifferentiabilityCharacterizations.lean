/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Characterizations of semidifferentiability

Theorem 7.21 and Corollary 7.22.

Clause (b) of 7.21 (continuous convergence of the difference quotients as
`τ ↓ 0`) is read pointwise in the direction: for every `w`, the quotients tend
to `h(w)` along `τ ↓ 0, w' → w`.  Clause (c) uses uniform convergence in the
extended sense of Definition 7.12, i.e. uniform convergence in the bounded
sense of every `ρ`-truncation. The filter and sequential versions use the
same truncation from `ExtendedUniformConvergence`.  Clause (e) is the
first-order expansion `f(x) = f(x̄) + h(x - x̄) + o(|x - x̄|)`, read with
Mathlib's little-o; since the expansion is an identity of real numbers it
includes the finiteness of `f` near `x̄`.

The companion module `SemiderivativeGraphs` proves clause (d), the graphical
characterization on closed balls.

The book's proof is followed: the limit function in (b) is continuous (the
first half of 7.14), vanishes at `0`, is positively homogeneous, and is
therefore finite; compactness of the unit sphere upgrades continuous
convergence to the estimate 7(22), which is (e); (e) gives (c) directly; and
(c) gives back (b) because truncations detect convergence in `EReal`.

Differentiability in Corollary 7.22 is formula 7(16) with the linear term
`⟨v, x - x̄⟩` written as a continuous linear functional, which is the
coordinate-free form of the same condition.
-/

import RockafellarWets.Chapter7.Semiderivatives
import RockafellarWets.Chapter7.ExtendedUniformConvergence
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.TFAE

open Filter Set Topology Metric Asymptotics

namespace RW

/-! ### Definition 7.12: truncations and extended uniform convergence -/

section Truncation

private theorem coe_erealTrunc_swap {ρ : ℝ} (_ : 0 ≤ ρ) (a : EReal) :
    ((erealTrunc ρ a : ℝ) : EReal) = max ((-ρ : ℝ) : EReal) (min (ρ : EReal) a) := by
  rw [coe_erealTrunc, min_comm]

/-- On real values the truncation is the clamp to `[-ρ, ρ]`. -/
theorem erealTrunc_coe {ρ : ℝ} (hρ : 0 ≤ ρ) (a : ℝ) :
    erealTrunc ρ a = max (-ρ) (min ρ a) := by
  have h := coe_erealTrunc_swap hρ (a : EReal)
  have hmono := EReal.coe_strictMono.monotone
  rw [← hmono.map_min, ← hmono.map_max] at h
  exact EReal.coe_injective h

/-- The clamp to `[-ρ, ρ]` is `1`-Lipschitz. -/
theorem abs_clamp_sub_clamp_le (ρ a b : ℝ) :
    |max (-ρ) (min ρ a) - max (-ρ) (min ρ b)| ≤ |a - b| := by
  rw [max_comm (-ρ), max_comm (-ρ)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

/-- Truncations detect convergence in `EReal`: if every truncation of `u`
converges to the corresponding truncation of `a`, then `u → a`. -/
theorem tendsto_of_forall_tendsto_erealTrunc {ι : Type*} {l : Filter ι}
    {u : ι → EReal} {a : EReal}
    (h : ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun i ↦ erealTrunc ρ (u i)) l (𝓝 (erealTrunc ρ a))) :
    Tendsto u l (𝓝 a) := by
  rw [tendsto_order]
  constructor
  · intro a' ha'
    obtain ⟨b, hab', hba⟩ := EReal.exists_between_coe_real ha'
    have hρ : (0 : ℝ) < |b| + 1 := by positivity
    have hlt : b < erealTrunc (|b| + 1) a := by
      have : ((b : ℝ) : EReal) < ((erealTrunc (|b| + 1) a : ℝ) : EReal) := by
        rw [coe_erealTrunc_swap hρ.le]
        exact lt_max_of_lt_right (lt_min (EReal.coe_lt_coe_iff.2 (by
          linarith [le_abs_self b])) hba)
      exact EReal.coe_lt_coe_iff.1 this
    filter_upwards [(h _ hρ).eventually (lt_mem_nhds hlt)] with i hi
    have hi' : ((b : ℝ) : EReal) <
        max ((-(|b| + 1) : ℝ) : EReal) (min ((|b| + 1 : ℝ) : EReal) (u i)) := by
      rw [← coe_erealTrunc_swap hρ.le]
      exact EReal.coe_lt_coe_iff.2 hi
    have hb : ((-(|b| + 1) : ℝ) : EReal) ≤ (b : EReal) :=
      EReal.coe_le_coe_iff.2 (by linarith [neg_abs_le b])
    rcases lt_max_iff.1 hi' with h1 | h1
    · exact absurd h1 (not_lt.2 hb)
    · exact hab'.trans (lt_of_lt_of_le h1 (min_le_right _ _))
  · intro a' ha'
    obtain ⟨b, hab, hba'⟩ := EReal.exists_between_coe_real ha'
    have hρ : (0 : ℝ) < |b| + 1 := by positivity
    have hlt : erealTrunc (|b| + 1) a < b := by
      have : ((erealTrunc (|b| + 1) a : ℝ) : EReal) < ((b : ℝ) : EReal) := by
        rw [coe_erealTrunc_swap hρ.le]
        exact max_lt (EReal.coe_lt_coe_iff.2 (by linarith [neg_abs_le b]))
          (lt_of_le_of_lt (min_le_right _ _) hab)
      exact EReal.coe_lt_coe_iff.1 this
    filter_upwards [(h _ hρ).eventually (gt_mem_nhds hlt)] with i hi
    have hi' : max ((-(|b| + 1) : ℝ) : EReal) (min ((|b| + 1 : ℝ) : EReal) (u i)) <
        ((b : ℝ) : EReal) := by
      rw [← coe_erealTrunc_swap hρ.le]
      exact EReal.coe_lt_coe_iff.2 hi
    have hb : (b : EReal) < ((|b| + 1 : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.2 (by linarith [le_abs_self b])
    have h1 := lt_of_le_of_lt (le_max_right _ _) hi'
    rcases min_lt_iff.1 h1 with h2 | h2
    · exact absurd (h2.trans hb) (lt_irrefl _)
    · exact h2.trans hba'

/-- **Definition 7.12** along an arbitrary filter: `F i` converges to `g`
uniformly on `X` in the extended sense when, for every `ρ > 0`, the
truncations converge uniformly on `X` in the bounded sense 7(13). -/
def ExtendedTendstoUniformlyOn {ι α : Type*} (F : ι → α → EReal) (g : α → EReal)
    (l : Filter ι) (X : Set α) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ w ∈ X,
    |erealTrunc ρ (F i w) - erealTrunc ρ (g w)| ≤ ε

/-- For a sequence the filter version agrees with Definition 7.12. -/
theorem extendedTendstoUniformlyOn_atTop_iff {α : Type*} {F : ℕ → α → EReal}
    {g : α → EReal} {X : Set α} :
    ExtendedTendstoUniformlyOn F g atTop X ↔ ERealConvergesUniformlyOn F g X := by
  constructor
  · intro h ρ hρ
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [h ρ hρ (ε/2) (half_pos hε)] with n hn
    intro x hx
    simpa only [Real.dist_eq, abs_sub_comm] using (hn x hx).trans_lt (half_lt_self hε)
  · intro h ρ hρ ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (h ρ hρ) ε hε] with n hn
    intro x hx
    simpa only [Real.dist_eq, abs_sub_comm] using (hn x hx).le

end Truncation

/-! ### Continuous convergence of the difference quotients -/

section ContinuousConvergence

/-- The first half of 7.14 in the form needed here: a continuous limit of a
family converging continuously is continuous. -/
theorem continuous_of_forall_tendsto_prod {ι α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [RegularSpace β] {l : Filter ι} [l.NeBot] {F : ι → α → β}
    {g : α → β}
    (hF : ∀ a, Tendsto (fun p : ι × α ↦ F p.1 p.2) (l ×ˢ 𝓝 a) (𝓝 (g a))) :
    Continuous g := by
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  rw [ContinuousAt, (closed_nhds_basis (g a)).tendsto_right_iff]
  rintro U ⟨hU, hUc⟩
  obtain ⟨t, ht, V, hV, htV⟩ := mem_prod_iff.1 (hF a hU)
  obtain ⟨V', hV'V, hV'o, haV'⟩ := mem_nhds_iff.1 hV
  filter_upwards [hV'o.mem_nhds haV'] with b hb
  apply hUc.mem_of_tendsto (hF b)
  filter_upwards [prod_mem_prod ht (hV'o.mem_nhds hb)] with p hp
  exact htV ⟨hp.1, hV'V hp.2⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Under continuous convergence the limit vanishes at the origin. -/
theorem limit_zero_of_forall_tendsto {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c)
    {h : E → EReal}
    (hb : ∀ w, Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (h w))) :
    h 0 = 0 := by
  have h1 := (hb 0).comp (tendsto_pair_const (0 : E))
  have h2 : Tendsto (fun τ : ℝ ↦ differenceQuotient f x τ 0) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simp only [differenceQuotient_zero_right hx]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

/-- Under continuous convergence the limit is positively homogeneous. -/
theorem limit_smul_of_forall_tendsto {f : E → EReal} {x : E} (hx : f x ≠ ⊥)
    (hx' : f x ≠ ⊤) {h : E → EReal}
    (hb : ∀ w, Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (h w))) {a : ℝ} (ha : 0 < a) (w : E) :
    h (a • w) = (a : EReal) * h w :=
  HasSemiderivative.unique ⟨hx, hx', hb (a • w)⟩ (HasSemiderivative.smul ⟨hx, hx', hb w⟩ ha)

/-- The book's proof of 7.21: the limit in (b) is finite, being continuous,
zero at the origin and positively homogeneous. -/
theorem limit_finite_of_forall_tendsto {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c)
    {h : E → EReal}
    (hb : ∀ w, Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (h w))) (w : E) :
    h w ≠ ⊤ ∧ h w ≠ ⊥ := by
  have hx1 : f x ≠ ⊥ := by rw [hx]; exact EReal.coe_ne_bot c
  have hx2 : f x ≠ ⊤ := by rw [hx]; exact EReal.coe_ne_top c
  have hcont : Continuous h := continuous_of_forall_tendsto_prod hb
  have h0 : h 0 = 0 := limit_zero_of_forall_tendsto hx hb
  have hU : h ⁻¹' Ioo ((-1 : ℝ) : EReal) ((1 : ℝ) : EReal) ∈ 𝓝 (0 : E) := by
    apply hcont.continuousAt.preimage_mem_nhds
    rw [h0]
    exact Ioo_mem_nhds
      (lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (show (-1 : ℝ) < 0 by norm_num))
        (le_of_eq EReal.coe_zero))
      (lt_of_le_of_lt (le_of_eq EReal.coe_zero.symm)
        (EReal.coe_lt_coe_iff.2 (show (0 : ℝ) < 1 by norm_num)))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
  rcases eq_or_ne w 0 with rfl | hw
  · rw [h0]
    exact ⟨EReal.zero_ne_top, EReal.zero_ne_bot⟩
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hw0 : ‖w‖ ≠ 0 := hwpos.ne'
    set s : ℝ := δ / (2 * ‖w‖) with hs_def
    have hs : 0 < s := by positivity
    have hu : s • w ∈ ball (0 : E) δ := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hs.le, hs_def]
      have : δ / (2 * ‖w‖) * ‖w‖ = δ / 2 * (‖w‖ / ‖w‖) := by ring
      rw [this, div_self hw0, mul_one]
      linarith
    have hmem : h (s • w) ∈ Ioo ((-1 : ℝ) : EReal) ((1 : ℝ) : EReal) := hball hu
    have hne_top : h (s • w) ≠ ⊤ := ne_top_of_lt hmem.2
    have hne_bot : h (s • w) ≠ ⊥ := ne_bot_of_gt hmem.1
    have hw' : w = s⁻¹ • (s • w) := by rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    rw [hw', limit_smul_of_forall_tendsto hx1 hx2 hb (inv_pos.2 hs),
      ← EReal.coe_toReal hne_top hne_bot, ← EReal.coe_mul]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

omit [NormedSpace ℝ E] in
/-- Continuous convergence of the difference quotients to a continuous real
limit is uniform on compact sets (the second half of 7.14). -/
theorem eventually_forall_mem_of_forall_tendsto {K : Set E} (hK : IsCompact K) {g : E → ℝ}
    (hg : Continuous g) {F : ℝ → E → EReal}
    (hF : ∀ w ∈ K, Tendsto (fun p : ℝ × E ↦ F p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      (𝓝 (g w : EReal)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ w ∈ K,
      ((g w - ε : ℝ) : EReal) < F τ w ∧ F τ w < ((g w + ε : ℝ) : EReal) := by
  have hS : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝ˢ K,
      ((g p.2 - ε : ℝ) : EReal) < F p.1 p.2 ∧ F p.1 p.2 < ((g p.2 + ε : ℝ) : EReal) := by
    refine hK.mem_prod_nhdsSet_of_forall fun w hw ↦ ?_
    have h1 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
        F p.1 p.2 ∈ Ioo ((g w - ε / 2 : ℝ) : EReal) ((g w + ε / 2 : ℝ) : EReal) :=
      hF w hw (Ioo_mem_nhds (EReal.coe_lt_coe_iff.2 (by linarith))
        (EReal.coe_lt_coe_iff.2 (by linarith)))
    have h2 : ∀ᶠ u in 𝓝 w, g u ∈ ball (g w) (ε / 2) :=
      (hg.tendsto w) (ball_mem_nhds (g w) (half_pos hε))
    filter_upwards [h1, tendsto_snd.eventually h2] with p hp1 hp2
    rw [mem_ball, Real.dist_eq, abs_lt] at hp2
    exact ⟨lt_trans (EReal.coe_lt_coe_iff.2 (by linarith [hp2.2])) hp1.1,
      lt_trans hp1.2 (EReal.coe_lt_coe_iff.2 (by linarith [hp2.1]))⟩
  filter_upwards [hS.curry] with τ hτ w hw
  exact hτ.self_of_nhdsSet w hw

end ContinuousConvergence

/-! ### Theorem 7.21 -/

section Theorem721

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 7.21**, `(b) ⇒ (e)`, which is the estimate 7(22): continuous
convergence to a continuous, positively homogeneous real `h` yields the
first-order expansion `f(x) = f(x̄) + h(x - x̄) + o(|x - x̄|)`. -/
theorem isLittleO_of_forall_tendsto [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    {c : ℝ} (hx : f x = c) {g : E → ℝ} (hg : Continuous g)
    (hgs : ∀ a : ℝ, 0 < a → ∀ w, g (a • w) = a * g w)
    (hF : ∀ w, Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (g w : EReal))) :
    (∀ᶠ y in 𝓝 x, f y ≠ ⊥ ∧ f y ≠ ⊤) ∧
      (fun y ↦ (f y).toReal - c - g (y - x)) =o[𝓝 x] (fun y ↦ y - x) := by
  have hg0 : g 0 = 0 := by
    have := hgs 2 two_pos 0
    rw [smul_zero] at this
    linarith
  have key : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y, ‖y - x‖ < δ →
      ∃ r : ℝ, f y = r ∧ |r - c - g (y - x)| ≤ ε * ‖y - x‖ := by
    intro ε hε
    have hU := eventually_forall_mem_of_forall_tendsto (isCompact_sphere (0 : E) 1) hg
      (fun w _ ↦ hF w) hε
    obtain ⟨δ, hδ, hδU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
    refine ⟨δ, hδ, fun y hy ↦ ?_⟩
    rcases eq_or_ne y x with rfl | hyx
    · exact ⟨c, hx, by simp [hg0]⟩
    · have hτ : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
      set τ := ‖y - x‖ with hτ_def
      have hz : τ⁻¹ • (y - x) ∈ sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hτ.le),
          ← hτ_def, inv_mul_cancel₀ hτ.ne']
      have hmem := hδU ⟨hτ, hy⟩ (τ⁻¹ • (y - x)) hz
      have hxz : x + τ • (τ⁻¹ • (y - x)) = y := by
        rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, add_sub_cancel]
      have hfy' : ∀ v : EReal, f y = v → f (x + τ • (τ⁻¹ • (y - x))) = v :=
        fun v hv ↦ by rw [hxz]; exact hv
      have hfy_top : f y ≠ ⊤ := by
        intro htop
        rw [differenceQuotient_eq_top hτ hx (hfy' ⊤ htop)] at hmem
        exact not_top_lt hmem.2
      have hfy_bot : f y ≠ ⊥ := by
        intro hbot
        rw [differenceQuotient_eq_bot hτ hx (hfy' ⊥ hbot)] at hmem
        exact not_lt_bot hmem.1
      have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hfy_top hfy_bot).symm
      rw [differenceQuotient_eq_coe hx (hfy' _ hfy)] at hmem
      have h1 := EReal.coe_lt_coe_iff.1 hmem.1
      have h2 := EReal.coe_lt_coe_iff.1 hmem.2
      refine ⟨(f y).toReal, hfy, ?_⟩
      have hgu : g (y - x) = τ * g (τ⁻¹ • (y - x)) := by
        rw [← hgs τ hτ, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
      have hrc : (f y).toReal - c = τ * (τ⁻¹ * ((f y).toReal - c)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul]
      rw [hgu, hrc, ← mul_sub, abs_mul, abs_of_pos hτ, mul_comm ε]
      refine mul_le_mul_of_nonneg_left ?_ hτ.le
      rw [abs_le]
      constructor <;> linarith
  refine ⟨?_, isLittleO_iff.2 fun ε hε ↦ ?_⟩
  · obtain ⟨δ, hδ, hk⟩ := key 1 one_pos
    filter_upwards [ball_mem_nhds x hδ] with y hy
    obtain ⟨r, hr, -⟩ := hk y (by rwa [mem_ball, dist_eq_norm] at hy)
    rw [hr]
    exact ⟨EReal.coe_ne_bot r, EReal.coe_ne_top r⟩
  · obtain ⟨δ, hδ, hk⟩ := key ε hε
    filter_upwards [ball_mem_nhds x hδ] with y hy
    obtain ⟨r, hr, hest⟩ := hk y (by rwa [mem_ball, dist_eq_norm] at hy)
    rw [hr, EReal.toReal_coe, Real.norm_eq_abs]
    exact hest

/-- The joint path `(τ, w') ↦ x̄ + τw'` tends to `x̄` along `τ ↓ 0, w' → w`. -/
theorem tendsto_add_smul_nhds (x w : E) :
    Tendsto (fun p : ℝ × E ↦ x + p.1 • p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 x) := by
  have h : Tendsto (fun p : ℝ × E ↦ x + p.1 • p.2) (𝓝 ((0 : ℝ), w))
      (𝓝 (x + (0 : ℝ) • w)) :=
    (continuous_const.add (continuous_fst.smul continuous_snd)).tendsto _
  rw [zero_smul, add_zero, nhds_prod_eq] at h
  exact h.mono_left (Filter.prod_mono nhdsWithin_le_nhds le_rfl)

/-- **Theorem 7.21**, `(e) ⇒ (b)`: a first-order expansion with a continuous,
positively homogeneous `h` gives continuous convergence to `h`. -/
theorem tendsto_of_isLittleO {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) {g : E → ℝ}
    (hg : Continuous g) (hgs : ∀ a : ℝ, 0 < a → ∀ w, g (a • w) = a * g w)
    (hfin : ∀ᶠ y in 𝓝 x, f y ≠ ⊥ ∧ f y ≠ ⊤)
    (ho : (fun y ↦ (f y).toReal - c - g (y - x)) =o[𝓝 x] (fun y ↦ y - x)) (w : E) :
    Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)
      (𝓝 (g w : EReal)) := by
  have hpath := tendsto_add_smul_nhds x w
  set G : ℝ × E → ℝ := fun p ↦ p.1⁻¹ * ((f (x + p.1 • p.2)).toReal - c) with hG
  have heq : (fun p : ℝ × E ↦ ((G p : ℝ) : EReal)) =ᶠ[𝓝[>] (0 : ℝ) ×ˢ 𝓝 w]
      (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2) := by
    filter_upwards [hpath.eventually hfin] with p hp
    rw [differenceQuotient_eq_coe hx (EReal.coe_toReal hp.2 hp.1).symm]
  refine Tendsto.congr' heq (EReal.tendsto_coe.2 ?_)
  rw [Metric.tendsto_nhds]
  intro η hη
  have hM : 0 < ‖w‖ + 1 := by positivity
  set ε : ℝ := η / (2 * (‖w‖ + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have h1 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      ‖(f (x + p.1 • p.2)).toReal - c - g (x + p.1 • p.2 - x)‖ ≤
        ε * ‖x + p.1 • p.2 - x‖ :=
    hpath.eventually (isLittleO_iff.1 ho hε)
  have h2 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, p.2 ∈ ball w 1 :=
    tendsto_snd.eventually (ball_mem_nhds w one_pos)
  have h3' : ∀ᶠ u in 𝓝 w, g u ∈ ball (g w) (η / 2) :=
    (hg.tendsto w) (ball_mem_nhds (g w) (half_pos hη))
  have h3 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, g p.2 ∈ ball (g w) (η / 2) :=
    tendsto_snd.eventually h3'
  have h4 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  filter_upwards [h1, h2, h3, h4] with p hp1 hp2 hp3 hp4
  obtain ⟨τ, v⟩ := p
  simp only [add_sub_cancel_left] at hp1
  simp only [mem_ball, dist_eq_norm] at hp2
  simp only [mem_ball, Real.dist_eq] at hp3
  change 0 < τ at hp4
  rw [Real.dist_eq]
  have hv : ‖v‖ < ‖w‖ + 1 := by linarith [norm_sub_norm_le v w]
  rw [hgs τ hp4, norm_smul, Real.norm_of_nonneg hp4.le, Real.norm_eq_abs] at hp1
  have hGv : G (τ, v) - g v = τ⁻¹ * ((f (x + τ • v)).toReal - c - τ * g v) := by
    rw [hG, mul_sub, ← mul_assoc, inv_mul_cancel₀ hp4.ne', one_mul]
  have hGv' : |G (τ, v) - g v| ≤ ε * ‖v‖ := by
    rw [hGv, abs_mul, abs_of_pos (inv_pos.2 hp4)]
    calc τ⁻¹ * |(f (x + τ • v)).toReal - c - τ * g v|
        ≤ τ⁻¹ * (ε * (τ * ‖v‖)) := mul_le_mul_of_nonneg_left hp1 (inv_nonneg.2 hp4.le)
      _ = ε * ‖v‖ * (τ⁻¹ * τ) := by ring
      _ = ε * ‖v‖ := by rw [inv_mul_cancel₀ hp4.ne', mul_one]
  have hεv : ε * ‖v‖ ≤ η / 2 := by
    have : ε * (‖w‖ + 1) = η / 2 := by
      rw [hε_def]
      rw [div_mul_eq_mul_div, mul_div_mul_right η 2 hM.ne']
    calc ε * ‖v‖ ≤ ε * (‖w‖ + 1) := mul_le_mul_of_nonneg_left hv.le hε.le
      _ = η / 2 := this
  calc |G (τ, v) - g w| ≤ |G (τ, v) - g v| + |g v - g w| := abs_sub_le _ _ _
    _ < η / 2 + η / 2 := by linarith
    _ = η := by ring

/-- **Theorem 7.21**, `(e) ⇒ (c)`: a first-order expansion gives uniform
convergence of the difference quotients on every bounded set. -/
theorem extendedTendstoUniformlyOn_of_isLittleO {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) {g : E → ℝ} (hgs : ∀ a : ℝ, 0 < a → ∀ w, g (a • w) = a * g w)
    (hfin : ∀ᶠ y in 𝓝 x, f y ≠ ⊥ ∧ f y ≠ ⊤)
    (ho : (fun y ↦ (f y).toReal - c - g (y - x)) =o[𝓝 x] (fun y ↦ y - x))
    {B : Set E} (hB : Bornology.IsBounded B) :
    ExtendedTendstoUniformlyOn (fun τ ↦ differenceQuotient f x τ) (fun w ↦ (g w : EReal))
      (𝓝[>] (0 : ℝ)) B := by
  intro ρ hρ ε hε
  obtain ⟨R, hR⟩ := hB.subset_closedBall (0 : E)
  set R' : ℝ := max R 1 with hR'_def
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hkey : ∀ᶠ y in 𝓝 x, (f y ≠ ⊥ ∧ f y ≠ ⊤) ∧
      ‖(f y).toReal - c - g (y - x)‖ ≤ ε / R' * ‖y - x‖ :=
    hfin.and (isLittleO_iff.1 ho (div_pos hε hR'))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hkey
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR')] with τ hτ w hw
  have hτ0 : 0 < τ := hτ.1
  have hwR : ‖w‖ ≤ R' := by
    have := hR hw
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hy : x + τ • w ∈ ball x δ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0.le]
    calc τ * ‖w‖ ≤ τ * R' := mul_le_mul_of_nonneg_left hwR hτ0.le
      _ < δ / R' * R' := mul_lt_mul_of_pos_right hτ.2 hR'
      _ = δ * (R' / R') := by ring
      _ = δ := by rw [div_self hR'.ne', mul_one]
  obtain ⟨⟨hb, ht⟩, hest⟩ := hball hy
  have hfy : f (x + τ • w) = ((f (x + τ • w)).toReal : EReal) := (EReal.coe_toReal ht hb).symm
  show |erealTrunc ρ (differenceQuotient f x τ w) - erealTrunc ρ (g w)| ≤ ε
  rw [differenceQuotient_eq_coe hx hfy, erealTrunc_coe hρ.le, erealTrunc_coe hρ.le]
  refine (abs_clamp_sub_clamp_le ρ _ _).trans ?_
  rw [add_sub_cancel_left, hgs τ hτ0, norm_smul, Real.norm_of_nonneg hτ0.le,
    Real.norm_eq_abs] at hest
  have hrw : τ⁻¹ * ((f (x + τ • w)).toReal - c) - g w =
      τ⁻¹ * ((f (x + τ • w)).toReal - c - τ * g w) := by
    rw [mul_sub τ⁻¹ ((f (x + τ • w)).toReal - c) (τ * g w), ← mul_assoc,
      inv_mul_cancel₀ hτ0.ne', one_mul]
  rw [hrw, abs_mul, abs_of_pos (inv_pos.2 hτ0)]
  calc τ⁻¹ * |(f (x + τ • w)).toReal - c - τ * g w|
      ≤ τ⁻¹ * (ε / R' * (τ * ‖w‖)) := mul_le_mul_of_nonneg_left hest (inv_nonneg.2 hτ0.le)
    _ = ε / R' * ‖w‖ * (τ⁻¹ * τ) := by ring
    _ = ε / R' * ‖w‖ := by rw [inv_mul_cancel₀ hτ0.ne', mul_one]
    _ ≤ ε / R' * R' := mul_le_mul_of_nonneg_left hwR (div_pos hε hR').le
    _ = ε * (R' / R') := by ring
    _ = ε := by rw [div_self hR'.ne', mul_one]

omit [NormedSpace ℝ E] in
/-- **Theorem 7.21**, `(c) ⇒ (b)`: uniform convergence on bounded sets to a
continuous limit gives continuous convergence. -/
theorem tendsto_of_extendedTendstoUniformlyOn {F : ℝ → E → EReal} {h : E → EReal}
    (hh : Continuous h)
    (hu : ∀ B : Set E, Bornology.IsBounded B → ExtendedTendstoUniformlyOn F h (𝓝[>] (0 : ℝ)) B)
    (w : E) :
    Tendsto (fun p : ℝ × E ↦ F p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (h w)) := by
  apply tendsto_of_forall_tendsto_erealTrunc
  intro ρ hρ
  rw [Metric.tendsto_nhds]
  intro η hη
  have h1 := hu (ball w 1) isBounded_ball ρ hρ (η / 2) (half_pos hη)
  have h2 : ∀ᶠ v in 𝓝 w, erealTrunc ρ (h v) ∈ ball (erealTrunc ρ (h w)) (η / 2) :=
    (((continuous_erealTrunc ρ).comp hh).tendsto w) (ball_mem_nhds _ (half_pos hη))
  have h3 : ∀ᶠ v in 𝓝 w, v ∈ ball w 1 := ball_mem_nhds w one_pos
  filter_upwards [tendsto_fst.eventually h1, tendsto_snd.eventually h2,
    tendsto_snd.eventually h3] with p hp1 hp2 hp3
  rw [mem_ball, Real.dist_eq] at hp2
  rw [Real.dist_eq]
  have := hp1 p.2 hp3
  calc |erealTrunc ρ (F p.1 p.2) - erealTrunc ρ (h w)|
      ≤ |erealTrunc ρ (F p.1 p.2) - erealTrunc ρ (h p.2)| +
        |erealTrunc ρ (h p.2) - erealTrunc ρ (h w)| := abs_sub_le _ _ _
    _ < η / 2 + η / 2 := by linarith
    _ = η := by ring

/-- From continuous convergence to a finite real limit. -/
theorem exists_real_limit_of_forall_tendsto {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c)
    {h : E → EReal}
    (hb : ∀ w, Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (h w))) :
    ∃ g : E → ℝ, (∀ w, h w = g w) ∧ Continuous g ∧
      (∀ a : ℝ, 0 < a → ∀ w, g (a • w) = a * g w) := by
  have hx1 : f x ≠ ⊥ := by rw [hx]; exact EReal.coe_ne_bot c
  have hx2 : f x ≠ ⊤ := by rw [hx]; exact EReal.coe_ne_top c
  have hfin := limit_finite_of_forall_tendsto hx hb
  have hhg : ∀ w, h w = (((h w).toReal : ℝ) : EReal) := fun w ↦
    (EReal.coe_toReal (hfin w).1 (hfin w).2).symm
  refine ⟨fun w ↦ (h w).toReal, hhg, ?_, ?_⟩
  · rw [← EReal.continuous_coe_iff]
    simp only [← hhg]
    exact continuous_of_forall_tendsto_prod hb
  · intro a ha w
    show (h (a • w)).toReal = a * (h w).toReal
    rw [limit_smul_of_forall_tendsto hx1 hx2 hb ha, EReal.toReal_mul, EReal.toReal_coe]

/-- **Theorem 7.21**: for `f` finite at `x̄`, the following are equivalent:
(a) `f` is semidifferentiable at `x̄`;
(b) as `τ ↓ 0` the difference quotients converge continuously to some `h`;
(c) as `τ ↓ 0` the difference quotients converge uniformly (Definition 7.12)
on all bounded sets to some continuous `h`;
(e) there is a finite, continuous, positively homogeneous `h` with
`f(x) = f(x̄) + h(x - x̄) + o(|x - x̄|)`.
Clause (d) is not formalized. -/
theorem semidifferentiableAt_tfae [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    (hx : f x ≠ ⊥) (hx' : f x ≠ ⊤) :
    List.TFAE [
      SemidifferentiableAt f x,
      ∃ h : E → EReal, ∀ w, Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (h w)),
      ∃ h : E → EReal, Continuous h ∧ ∀ B : Set E, Bornology.IsBounded B →
        ExtendedTendstoUniformlyOn (fun τ ↦ differenceQuotient f x τ) h (𝓝[>] (0 : ℝ)) B,
      ∃ h : E → ℝ, Continuous h ∧ (∀ a : ℝ, 0 < a → ∀ w, h (a • w) = a * h w) ∧
        (∀ᶠ y in 𝓝 x, f y ≠ ⊥ ∧ f y ≠ ⊤) ∧
        (fun y ↦ (f y).toReal - (f x).toReal - h (y - x)) =o[𝓝 x] (fun y ↦ y - x)] := by
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hx' hx).symm
  tfae_have 1 → 2 := fun ha ↦ ⟨fun w ↦ subderivative f x w,
    fun w ↦ (ha w).hasSemiderivative.2.2⟩
  tfae_have 2 → 1 := fun ⟨h, hb⟩ w ↦ ⟨h w, hx, hx', hb w⟩
  tfae_have 2 → 4 := by
    rintro ⟨h, hb⟩
    obtain ⟨g, hhg, hg, hgs⟩ := exists_real_limit_of_forall_tendsto hxc hb
    have hF : ∀ w, Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (g w : EReal)) := fun w ↦ hhg w ▸ hb w
    obtain ⟨hfin, ho⟩ := isLittleO_of_forall_tendsto hxc hg hgs hF
    exact ⟨g, hg, hgs, hfin, ho⟩
  tfae_have 4 → 3 := by
    rintro ⟨g, hg, hgs, hfin, ho⟩
    exact ⟨fun w ↦ (g w : EReal), continuous_coe_real_ereal.comp hg,
      fun B hB ↦ extendedTendstoUniformlyOn_of_isLittleO hxc hgs hfin ho hB⟩
  tfae_have 3 → 2 := by
    rintro ⟨h, hh, hu⟩
    exact ⟨h, tendsto_of_extendedTendstoUniformlyOn hh hu⟩
  tfae_finish

/-- **Theorem 7.21**, the concluding clauses: at a point of
semidifferentiability the semiderivative is finite, depends continuously and
positively homogeneously on `w`, and equals both `df(x̄)(w)` and the one-sided
directional derivative `f'(x̄; w)`. -/
theorem SemidifferentiableAt.exists_semiderivative {f : E → EReal} {x : E}
    (hs : SemidifferentiableAt f x) :
    ∃ h : E → ℝ, Continuous h ∧ (∀ a : ℝ, 0 < a → ∀ w, h (a • w) = a * h w) ∧
      ∀ w, HasSemiderivative f x w (h w) ∧ subderivative f x w = h w ∧
        HasOneSidedDirDeriv f x w (h w) := by
  obtain ⟨β, hβ⟩ := hs 0
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hβ.2.1 hβ.1).symm
  have hb : ∀ w, Tendsto (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (subderivative f x w)) :=
    fun w ↦ (hs w).hasSemiderivative.2.2
  obtain ⟨g, hhg, hg, hgs⟩ := exists_real_limit_of_forall_tendsto hxc hb
  refine ⟨g, hg, hgs, fun w ↦ ?_⟩
  have hw : HasSemiderivative f x w (g w) := by
    rw [← hhg w]
    exact (hs w).hasSemiderivative
  exact ⟨hw, hw.subderivative_eq, hw.hasOneSidedDirDeriv⟩

/-- **Theorem 7.21**: a function semidifferentiable at `x̄` is continuous
there. -/
theorem SemidifferentiableAt.continuousAt [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    (hs : SemidifferentiableAt f x) : ContinuousAt f x := by
  obtain ⟨β, hβ⟩ := hs 0
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hβ.2.1 hβ.1).symm
  obtain ⟨g, hg, hgs, hall⟩ := hs.exists_semiderivative
  obtain ⟨hfin, ho⟩ := isLittleO_of_forall_tendsto hxc hg hgs fun w ↦ (hall w).1.2.2
  have hg0 : g 0 = 0 := by
    have := hgs 2 two_pos 0
    rw [smul_zero] at this
    linarith
  have hlin : Tendsto (fun y ↦ y - x) (𝓝 x) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 tendsto_id
  have h1 : Tendsto (fun y ↦ (f y).toReal - (f x).toReal - g (y - x)) (𝓝 x) (𝓝 0) :=
    ho.trans_tendsto hlin
  have h2 : Tendsto (fun y ↦ g (y - x)) (𝓝 x) (𝓝 0) := by
    have := (hg.tendsto 0).comp hlin
    rwa [hg0] at this
  have h3 : Tendsto (fun y ↦ (f y).toReal) (𝓝 x) (𝓝 (f x).toReal) := by
    have := (h1.add h2).add_const (f x).toReal
    simp only [sub_add_cancel, zero_add] at this
    exact this
  rw [ContinuousAt, hxc]
  refine (EReal.tendsto_coe.2 h3).congr' ?_
  filter_upwards [hfin] with y hy
  exact EReal.coe_toReal hy.2 hy.1

end Theorem721

/-! ### Corollary 7.22 -/

section Corollary722

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Formula 7(16): `f` is differentiable at `x̄`, a point where `f(x̄)` is
finite, with linear term given by a continuous linear functional `L` (in `ℝⁿ`,
`L = ⟨v, ·⟩` for the gradient `v = ∇f(x̄)`). -/
def HasERealGradientAt (f : E → EReal) (x : E) (L : E →L[ℝ] ℝ) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ (∀ᶠ y in 𝓝 x, f y ≠ ⊥ ∧ f y ≠ ⊤) ∧
    (fun y ↦ (f y).toReal - (f x).toReal - L (y - x)) =o[𝓝 x] (fun y ↦ y - x)

/-- Formula 7(16): `f` is differentiable at `x̄`. -/
def ERealDifferentiableAt (f : E → EReal) (x : E) : Prop :=
  ∃ L : E →L[ℝ] ℝ, HasERealGradientAt f x L

/-- **Corollary 7.22**: `f` is differentiable at `x̄` if and only if it is
semidifferentiable at `x̄` with a semiderivative depending linearly on `w`. -/
theorem erealDifferentiableAt_iff [FiniteDimensional ℝ E] {f : E → EReal} {x : E} :
    ERealDifferentiableAt f x ↔
      SemidifferentiableAt f x ∧ ∃ L : E →ₗ[ℝ] ℝ, ∀ w, HasSemiderivative f x w (L w) := by
  constructor
  · rintro ⟨L, hx, hx', hfin, ho⟩
    have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hx' hx).symm
    have hL : ∀ w, HasSemiderivative f x w (L w) := fun w ↦
      ⟨hx, hx', tendsto_of_isLittleO hxc L.continuous
        (fun a _ w ↦ by rw [map_smul, smul_eq_mul]) hfin ho w⟩
    exact ⟨fun w ↦ ⟨_, hL w⟩, L.toLinearMap, hL⟩
  · rintro ⟨hs, L, hL⟩
    obtain ⟨β, hβ⟩ := hs 0
    have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hβ.2.1 hβ.1).symm
    have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
    obtain ⟨hfin, ho⟩ := isLittleO_of_forall_tendsto hxc hLc
      (fun a _ w ↦ by rw [map_smul, smul_eq_mul]) fun w ↦ (hL w).2.2
    exact ⟨⟨L, hLc⟩, hβ.1, hβ.2.1, hfin, ho⟩

end Corollary722

end RW
