/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: calmness as a constraint qualification

**Proposition 10.47**: for a proper lsc `f : ℓ²(E × P) → ℝ̄`, a local minimizer `x̄` of
`f(·, ū)` satisfying the calmness condition 10(10) with constant `κ ≥ 0` admits a multiplier
`ȳ` with `(0, ȳ) ∈ ∂f(x̄, ū)` and `|ȳ| ≤ κ` (`exists_multiplier_of_calm`).  Condition 10(10),
`liminf_{u → ū, u ≠ ū, x → x̄} (f(x, u) - f(x̄, ū))/|u - ū| ≥ -κ`, is used in the unpacked
form stated in the book's proof: for every `ε > 0`, `f(x, u) ≥ f(x̄, ū) - (κ + ε)|u - ū|` for
`(x, u)` near `(x̄, ū)` with `u ≠ ū` (`IsCalmAt`).  It holds when `x̄` is globally optimal and
`p(u) = inf_x f(x, u)` is calm from below at `ū` with constant `κ` (`isCalmAt_of_value_calm`).

As in the book: `(x̄, ū)` locally minimizes `f + (κ + ε)|u - ū|`; Fermat's rule 10.1, the
sum rule 10.10 and the separable subgradient formula 10.5 give `(0, y_ε) ∈ ∂f(x̄, ū)` with
`|y_ε| ≤ κ + ε`, and a cluster point as `ε ↘ 0` lies in the closed set `∂f(x̄, ū)` (8.6).
-/

import RockafellarWets.Chapter10.FermatRule
import RockafellarWets.Chapter10.LipschitzSums
import RockafellarWets.Chapter10.SeparableSubgradients
import RockafellarWets.Chapter9.StrictContinuityCriteria
import RockafellarWets.Chapter9.StrictDifferentiability
import RockafellarWets.Chapter8.SubgradientRelationships

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- Condition 10(10) of Proposition 10.47 (calmness of the problem at `x̄` relative to the
parameterization in `u` at `ū`), in the unpacked `ε`-form. -/
def IsCalmAt (f : WithLp 2 (E × P) → EReal) (x : E) (u : P) (κ : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ q : E × P in 𝓝 (x, u), q.2 ≠ u →
    f (WithLp.toLp 2 (x, u)) - (((κ + ε) * ‖q.2 - u‖ : ℝ) : EReal) ≤ f (WithLp.toLp 2 q)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P] in
/-- **Proposition 10.47**: global optimality of `x̄` together with calmness from below of
`p(u) = inf_x f(x, u)` at `ū` gives condition 10(10). -/
theorem isCalmAt_of_value_calm {f : WithLp 2 (E × P) → EReal} {x : E} {u : P} {c κ : ℝ}
    (hc : f (WithLp.toLp 2 (x, u)) = c)
    (hp : ∀ᶠ u' in 𝓝 u, (((c - κ * ‖u' - u‖ : ℝ) : EReal)) ≤ ⨅ y, f (WithLp.toLp 2 (y, u'))) :
    IsCalmAt f x u κ := by
  intro ε hε
  have hsnd : Tendsto (fun q : E × P ↦ q.2) (𝓝 (x, u)) (𝓝 u) := continuous_snd.tendsto _
  filter_upwards [hsnd.eventually hp] with q hq _
  rw [hc]
  calc ((c : ℝ) : EReal) - (((κ + ε) * ‖q.2 - u‖ : ℝ) : EReal)
      = (((c - (κ + ε) * ‖q.2 - u‖ : ℝ)) : EReal) := by rw [EReal.coe_sub]
    _ ≤ (((c - κ * ‖q.2 - u‖ : ℝ)) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        nlinarith [norm_nonneg (q.2 - u)]
    _ ≤ ⨅ y, f (WithLp.toLp 2 (y, q.2)) := hq
    _ ≤ f (WithLp.toLp 2 (q.1, q.2)) := iInf_le _ q.1

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ P] in
private theorem norm_snd_le (p : WithLp 2 (E × P)) : ‖p.snd‖ ≤ ‖p‖ := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [WithLp.prod_norm_sq_eq_of_L2 p]
  nlinarith [sq_nonneg ‖p.fst‖]

/-- **Proposition 10.47** (calmness as a constraint qualification). -/
theorem exists_multiplier_of_calm {f : WithLp 2 (E × P) → EReal} (hl : LowerSemicontinuous f)
    (hpf : IsProper f) {x : E} {u : P} {c : ℝ} (hc : f (WithLp.toLp 2 (x, u)) = c)
    (hmin : IsLocalMin (fun y ↦ f (WithLp.toLp 2 (y, u))) x) {κ : ℝ} (hκ : 0 ≤ κ)
    (hcalm : IsCalmAt f x u κ) :
    ∃ y : P, WithLp.toLp 2 ((0 : E), y) ∈ subdifferential f (WithLp.toLp 2 (x, u)) ∧ ‖y‖ ≤ κ := by
  set p₀ : WithLp 2 (E × P) := WithLp.toLp 2 (x, u) with hp₀
  -- the multipliers for a positive slack `ε`
  have hstep : ∀ ε > 0, ∃ y : P, WithLp.toLp 2 ((0 : E), y) ∈ subdifferential f p₀ ∧
      ‖y‖ ≤ κ + ε := by
    intro ε hε
    set k := κ + ε with hk
    have hk0 : 0 < k := by positivity
    set φ : P → EReal := fun u' ↦ ((k * ‖u' - u‖ : ℝ) : EReal) with hφ
    set h : WithLp 2 (E × P) → EReal := separableSum (fun _ : E ↦ (0 : EReal)) φ with hh
    have hval : ∀ p : WithLp 2 (E × P), h p = ((k * ‖p.snd - u‖ : ℝ) : EReal) := fun p ↦ by
      simp [hh, separableSum, hφ]
    -- `h` is Lipschitz
    have hhL : LipschitzWith ⟨k, hk0.le⟩ (fun p : WithLp 2 (E × P) ↦ k * ‖p.snd - u‖) := by
      refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
      rw [Real.dist_eq, dist_eq_norm, NNReal.coe_mk, ← mul_sub, abs_mul, abs_of_pos hk0]
      refine mul_le_mul_of_nonneg_left ?_ hk0.le
      have h1 := abs_norm_sub_norm_le (p.snd - u) (q.snd - u)
      rw [sub_sub_sub_cancel_right] at h1
      refine h1.trans ?_
      have := norm_snd_le (p - q)
      simpa [WithLp.sub_snd] using this
    have hhfun : h = fun p ↦ ((k * ‖p.snd - u‖ : ℝ) : EReal) := funext hval
    have hhsc : ERealStrictlyContinuousAt h p₀ := by
      rw [hhfun]
      exact eRealStrictlyContinuousAt_coe_of_lipschitz hhL
    -- `(x̄, ū)` locally minimizes `h + f`
    have hloc : IsLocalMin (h + f) p₀ := by
      have hcont : Continuous fun p : WithLp 2 (E × P) ↦ ((p.fst, p.snd) : E × P) :=
        (WithLp.continuous_fst 2 E P).prodMk (WithLp.continuous_snd 2 E P)
      have hev1 := (hcont.tendsto p₀).eventually (hcalm ε hε)
      have hmin' : ∀ᶠ y in 𝓝 x, f p₀ ≤ f (WithLp.toLp 2 (y, u)) := hmin
      have hev2 := ((WithLp.continuous_fst 2 E P).tendsto p₀).eventually hmin'
      filter_upwards [hev1, hev2] with p hp1 hp2
      show h p₀ + f p₀ ≤ h p + f p
      rw [hval, hval]
      simp only [hp₀, WithLp.toLp_snd, sub_self, norm_zero, mul_zero, EReal.coe_zero, zero_add]
      by_cases hu : p.snd = u
      · have hp' : WithLp.toLp 2 (p.fst, u) = p := by rw [← hu]; rfl
        rw [hu, sub_self, norm_zero, mul_zero, EReal.coe_zero, zero_add, ← hp']
        exact hp2
      · have h1 := hp1 hu
        have hpq : WithLp.toLp 2 ((p.fst, p.snd) : E × P) = p := rfl
        rw [hpq] at h1
        rw [hc] at h1 ⊢
        -- c - k|p.snd - u| ≤ f p  ⟹  c ≤ k|..| + f p
        by_cases hfp : f p = ⊤
        · rw [hfp, EReal.coe_add_top]
          exact le_top
        have hfp_bot : f p ≠ ⊥ := ne_of_gt (hpf.2 p)
        rw [← EReal.coe_toReal hfp hfp_bot] at h1 ⊢
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h1
        rw [← EReal.coe_add, EReal.coe_le_coe_iff]
        linarith
    have hval0 : (h + f) p₀ = (c : EReal) := by
      show h p₀ + f p₀ = (c : EReal)
      rw [hval, hc]
      simp [hp₀]
    have h0 := IsLocalMin.zero_mem_subdifferential hloc hval0
    obtain ⟨a, ha, b, hb, hab⟩ := subdifferential_add_subset_of_strictlyContinuous hhsc hl hpf hc h0
    -- the subgradients of the penalty
    have hafst : a.fst = 0 := by
      have hsep := (mem_subdifferential_separableSum_iff (f := fun _ : E ↦ (0 : EReal)) (g := φ)
        (x := x) (y := u) (c := 0) (d := 0) (lowerSemicontinuous_const.lowerSemicontinuousAt x)
        (by
          have hφc : Continuous φ := continuous_coe_real_ereal.comp
            (continuous_const.mul ((continuous_id.sub continuous_const).norm))
          exact hφc.lowerSemicontinuous.lowerSemicontinuousAt u)
        rfl (by simp [hφ]) a).1 ha
      have h0E : subdifferential (fun _ : E ↦ (0 : EReal)) x = {0} := by
        have hs : HasStrictGradientAt (fun _ : E ↦ (0 : EReal)) 0 x := by
          refine ⟨Eventually.of_forall fun _ ↦ by simp, ?_⟩
          simp only [EReal.toReal_zero, map_zero]
          exact hasStrictFDerivAt_const 0 x
        exact hs.subdifferential_eq
      have := hsep.1
      rwa [h0E, mem_singleton_iff] at this
    have hanorm : ‖a‖ ≤ k := by
      have hfin : ∀ y ∈ (univ : Set (WithLp 2 (E × P))), h y = ((h y).toReal : EReal) :=
        fun y _ ↦ by rw [hval, EReal.toReal_coe]
      have hLip : LipschitzOnWith ⟨k, hk0.le⟩ (fun y ↦ (h y).toReal) univ := by
        have hr : (fun y ↦ (h y).toReal) = fun p : WithLp 2 (E × P) ↦ k * ‖p.snd - u‖ :=
          funext fun y ↦ by rw [hval, EReal.toReal_coe]
        rw [hr]
        exact hhL.lipschitzOnWith
      exact norm_le_of_mem_subdifferential_of_lipschitzOnWith isOpen_univ hfin hLip (mem_univ _) ha
    have hb' : b = -a := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hab
    have hbfst : b.fst = 0 := by simp [hb', hafst]
    refine ⟨b.snd, ?_, ?_⟩
    · have hbeq : WithLp.toLp 2 ((0 : E), b.snd) = b := by
        rw [← hbfst]
        rfl
      rw [hbeq]
      exact hb
    · refine (norm_snd_le b).trans ?_
      rw [hb', norm_neg]
      exact hanorm
  -- pass to the limit `ε ↘ 0`
  choose ys hys hyn using fun n : ℕ ↦ hstep (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hbdd : ∀ n, ys n ∈ closedBall (0 : P) (κ + 1) := fun n ↦ by
    rw [mem_closedBall_zero_iff]
    refine (hyn n).trans ?_
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    linarith
  obtain ⟨ybar, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : P) (κ + 1)).tendsto_subseq hbdd
  have hclosed : IsClosed (subdifferential f p₀) :=
    (subdifferential_properties (f := f) (x := p₀) (c := c) hc).2.2.1
  have hcont : Continuous fun y : P ↦ WithLp.toLp 2 ((0 : E), y) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.continuous.comp
      (continuous_const.prodMk continuous_id)
  refine ⟨ybar, hclosed.mem_of_tendsto ((hcont.tendsto ybar).comp hlim)
    (Eventually.of_forall fun n ↦ hys (φ n)), ?_⟩
  have hεlim : Tendsto (fun n ↦ κ + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 (κ + 0)) :=
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  rw [add_zero] at hεlim
  exact le_of_tendsto_of_tendsto ((continuous_norm.tendsto ybar).comp hlim) hεlim
    (Eventually.of_forall fun n ↦ hyn (φ n))

end RW
