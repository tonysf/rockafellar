/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1I*: Proximal hulls and double envelopes

* **Example 1.44**: the `λ`-proximal hull `hλ f` (`proximalHull`, Chapter 11): `eλ f ≤ hλ f ≤ f`,
  the formulas `hλ f = -eλ[-eλ f]` and `eλ f = eλ[hλ f]`, lower semicontinuity, properness below
  the threshold, agreement with `f` on `rge Pλ f`, and `hλ f ↗ f` as `λ ↘ 0` (corrected: this
  needs `f` lsc).
* **Exercise 1.45**: proximal inequalities.
* **Example 1.46**: Lasry–Lions double envelopes (`doubleEnvelope`, Chapter 12): the bracket,
  formula 1(19), and the infima and minimizers.

The book's `ℝⁿ` is a real inner product space `E`, finite-dimensional where compactness is used.
-/

import RockafellarWets.Chapter1.EpiOperations
import RockafellarWets.Chapter12.DoubleEnvelopes

open Set Filter Topology Metric

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Example 1.44 -/

section ProximalHull

/-- **Example 1.44**: `f` is `λ`-proximal when `hλ f = f`. -/
def IsProximalFunction (f : E → EReal) (t : ℝ) : Prop := proximalHull f t = f

/-- **Example 1.44**: `eλ f ≤ hλ f`. -/
theorem moreauEnvelopeEReal_le_proximalHull (f : E → EReal) (t : ℝ) (x : E) :
    moreauEnvelopeEReal f t x ≤ proximalHull f t x := by
  rw [proximalHull_eq_iSup_envelope]
  exact le_iSup_of_le x (by simp [moreauQuadratic])

omit [InnerProductSpace ℝ E] in
/-- **Example 1.44**: `hλ f ≤ f`. -/
theorem proximalHull_le (f : E → EReal) (t : ℝ) (x : E) : proximalHull f t x ≤ f x :=
  iSup₂_le fun _ a ↦ a.2 x

/-- **Example 1.44**: `eλ f = eλ[hλ f]`, i.e. `eλ f(x) = inf_w {hλ f(w) + (1/2λ)|x - w|²}`. -/
theorem moreauEnvelopeEReal_proximalHull (f : E → EReal) (t : ℝ) :
    moreauEnvelopeEReal (proximalHull f t) t = moreauEnvelopeEReal f t := by
  funext x
  apply le_antisymm
  · exact iInf_mono fun w ↦ add_le_add (proximalHull_le f t w) le_rfl
  · refine le_iInf fun w ↦ ?_
    have h : moreauEnvelopeEReal f t x - (moreauQuadratic t (w - x) : EReal) ≤
        proximalHull f t w := by
      rw [proximalHull_eq_iSup_envelope]
      exact le_iSup (fun z ↦ moreauEnvelopeEReal f t z - (moreauQuadratic t (w - z) : EReal)) x
    calc moreauEnvelopeEReal f t x
        = moreauEnvelopeEReal f t x - (moreauQuadratic t (w - x) : EReal) +
            (moreauQuadratic t (w - x) : EReal) := (EReal.sub_add_cancel).symm
      _ ≤ proximalHull f t w + (moreauQuadratic t (w - x) : EReal) := add_le_add h le_rfl
      _ = proximalHull f t w + (((1 / (2 * t)) * ‖w - x‖ ^ 2 : ℝ) : EReal) := by
          simp [moreauQuadratic]

/-- **Example 1.44**: `hλ f` is lower semicontinuous. -/
theorem lowerSemicontinuous_proximalHull (f : E → EReal) (t : ℝ) :
    LowerSemicontinuous (proximalHull f t) := by
  unfold proximalHull
  refine lowerSemicontinuous_iSup fun w ↦ lowerSemicontinuous_iSup fun a ↦ ?_
  refine (continuous_coe_real_ereal.comp ?_).lowerSemicontinuous
  unfold moreauQuadratic
  fun_prop

omit [InnerProductSpace ℝ E] in
/-- Below the threshold the envelope never takes the value `-∞` (no semicontinuity needed). -/
theorem bot_lt_moreauEnvelopeEReal_of_lt_proxThreshold {f : E → EReal} {t : ℝ} (ht : 0 < t)
    (hthr : (t : EReal) < proxThreshold f) (x : E) : ⊥ < moreauEnvelopeEReal f t x := by
  obtain ⟨s, hs⟩ := lt_iSup_iff.1 hthr
  obtain ⟨⟨hspos, x₁, hx₁⟩, hts⟩ := lt_iSup_iff.1 hs
  have hts' : t < s := EReal.coe_lt_coe_iff.1 hts
  have hr : (1 / s + 1 / t) / 2 ∈ quadraticShiftSet f :=
    mem_quadraticShiftSet_of_bot_lt hspos hx₁ (by
      have : 1 / s < 1 / t := one_div_lt_one_div_of_lt ht hts'
      linarith)
  exact bot_lt_moreauEnvelopeEReal_of_mem_quadraticShiftSet hr ht (by
    have : 1 / s < 1 / t := one_div_lt_one_div_of_lt ht hts'
    linarith) x

/-- **Example 1.44**: `hλ f` is proper when `f` is proper and prox-bounded with `λ_f > λ`. -/
theorem isProper_proximalHull {f : E → EReal} (hp : IsProper f) {t : ℝ} (ht : 0 < t)
    (hthr : (t : EReal) < proxThreshold f) : IsProper (proximalHull f t) := by
  obtain ⟨x₀, hx₀⟩ := hp.1
  exact ⟨⟨x₀, lt_of_le_of_lt (proximalHull_le f t x₀) hx₀⟩, fun x ↦
    lt_of_lt_of_le (bot_lt_moreauEnvelopeEReal_of_lt_proxThreshold ht hthr x)
      (moreauEnvelopeEReal_le_proximalHull f t x)⟩

/-- **Example 1.44**: at `λ`-proximal points, where `f(x)` is finite and `x ∈ Pλ f(w)` for some
`w`, one has `hλ f(x) = f(x)`; thus `hλ f` agrees with `f` on `rge Pλ f`. -/
theorem proximalHull_eq_of_mem_proximalMappingEReal {f : E → EReal} {t : ℝ} {x w : E}
    (hx : x ∈ proximalMappingEReal f t w) : proximalHull f t x = f x := by
  refine le_antisymm (proximalHull_le f t x) ?_
  have hval : f x + (((1 / (2 * t)) * ‖x - w‖ ^ 2 : ℝ) : EReal) = moreauEnvelopeEReal f t w :=
    hx.1
  have h : moreauEnvelopeEReal f t w - (moreauQuadratic t (x - w) : EReal) ≤
      proximalHull f t x := by
    rw [proximalHull_eq_iSup_envelope]
    exact le_iSup (fun z ↦ moreauEnvelopeEReal f t z - (moreauQuadratic t (x - z) : EReal)) w
  refine le_trans (le_of_eq ?_) h
  rw [← hval]
  simp only [moreauQuadratic]
  exact (EReal.add_sub_cancel_right).symm

/-- The quadratic comparison behind the monotonicity of proximal hulls: for `0 < μ ≤ λ`, every
quadratic `α - (1/2λ)|· - w|²` lies above a quadratic `α' - (1/2μ)|· - w'|²` touching it at `x̄`. -/
theorem exists_touching_quadratic {mu lam : ℝ} (hmu : 0 < mu) (hml : mu ≤ lam) (a : ℝ)
    (w xb : E) :
    ∃ a' : ℝ, ∃ w' : E, (∀ y, a' - moreauQuadratic mu (y - w') ≤ a - moreauQuadratic lam (y - w)) ∧
      a' - moreauQuadratic mu (xb - w') = a - moreauQuadratic lam (xb - w) := by
  have hlam : 0 < lam := lt_of_lt_of_le hmu hml
  refine ⟨a - moreauQuadratic lam (xb - w) + mu / (2 * lam ^ 2) * ‖xb - w‖ ^ 2,
    xb - (mu / lam) • (xb - w), fun y ↦ ?_, ?_⟩
  · have h1 : y - (xb - (mu / lam) • (xb - w)) = (y - xb) + (mu / lam) • (xb - w) := by abel
    have h2 : y - w = (y - xb) + (xb - w) := by abel
    simp only [moreauQuadratic]
    rw [h1, h2, norm_add_sq_real, norm_add_sq_real, norm_smul, real_inner_smul_right,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < mu / lam)]
    have hd : 0 ≤ ‖y - xb‖ ^ 2 := sq_nonneg _
    have hc : 1 / (2 * lam) ≤ 1 / (2 * mu) := one_div_le_one_div_of_le (by positivity) (by linarith)
    have key : 1 / (2 * lam) * ‖y - xb‖ ^ 2 ≤ 1 / (2 * mu) * ‖y - xb‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hc hd
    field_simp
    field_simp at key
    nlinarith [key]
  · simp only [moreauQuadratic, sub_sub_cancel, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < mu / lam)]
    field_simp
    ring

/-- **Example 1.44**: `hλ f(x)` increases as `λ ↘ 0`. -/
theorem antitoneOn_proximalHull (f : E → EReal) (x : E) :
    AntitoneOn (fun t ↦ proximalHull f t x) (Ioi 0) := by
  intro mu hmu lam _ hml
  refine iSup₂_le fun w ⟨a, ha⟩ ↦ ?_
  obtain ⟨a', w', hle, heq⟩ := exists_touching_quadratic hmu hml a w x
  have ha' : ∀ y, ((a' - moreauQuadratic mu (y - w') : ℝ) : EReal) ≤ f y := fun y ↦
    (EReal.coe_le_coe_iff.2 (hle y)).trans (ha y)
  exact le_iSup_of_le w' (le_iSup_of_le ⟨a', ha'⟩ (le_of_eq (by rw [heq])))

/-- **Example 1.44**, corrected: for `f` proper, lsc and prox-bounded, `hλ f(x) ↗ f(x)` as
`λ ↘ 0` (monotonicity is `antitoneOn_proximalHull`).  Lower semicontinuity cannot be dropped:
see `proximalHull_not_tendsto_counterexample`. -/
theorem tendsto_proximalHull_nhdsGT_zero {f : E → EReal} (hl : LowerSemicontinuous f)
    (hpb : IsProxBounded f) (x : E) :
    Tendsto (fun t ↦ proximalHull f t x) (𝓝[>] 0) (𝓝 (f x)) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_moreauEnvelopeEReal_nhdsGT_zero hl hpb x)
    tendsto_const_nhds (fun t ↦ moreauEnvelopeEReal_le_proximalHull f t x)
    (fun t ↦ proximalHull_le f t x)

end ProximalHull

/-- The printed convergence `hλ f ↗ f` fails without lower semicontinuity: `f = δ_(0,1)` on `ℝ`
is proper and bounded below (so prox-bounded with `λ_f = ∞`), yet `hλ f(0) ≤ 0 < ∞ = f(0)` for
every `λ`, because `hλ f` is an lsc minorant of `f`. -/
theorem proximalHull_not_tendsto_counterexample :
    IsProper (indicatorVA (Ioo (0 : ℝ) 1)) ∧ IsProxBounded (indicatorVA (Ioo (0 : ℝ) 1)) ∧
      proxThreshold (indicatorVA (Ioo (0 : ℝ) 1)) = ⊤ ∧
      ¬ Tendsto (fun t ↦ proximalHull (indicatorVA (Ioo (0 : ℝ) 1)) t 0) (𝓝[>] 0)
        (𝓝 (indicatorVA (Ioo (0 : ℝ) 1) 0)) := by
  set f := indicatorVA (Ioo (0 : ℝ) 1) with hf
  have hp : IsProper f := (indicatorVA_isProper_iff _).2 ⟨1 / 2, by norm_num, by norm_num⟩
  have hinf : ⊥ < ⨅ x, f x := by
    refine lt_of_lt_of_le (EReal.bot_lt_coe (-1)) (le_iInf fun x ↦ ?_)
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · rw [hf, indicatorVA_apply_mem hx]; norm_num
    · rw [hf, indicatorVA_apply_not_mem hx]; exact le_top
  obtain ⟨hpb, hthr⟩ := isProxBounded_and_proxThreshold_eq_top_of_bot_lt_iInf hinf
  refine ⟨hp, hpb, hthr, fun hlim ↦ ?_⟩
  have h0 : f 0 = ⊤ := indicatorVA_apply_not_mem (by norm_num)
  -- every hull value at `0` is at most `0`
  have hle : ∀ t, proximalHull f t 0 ≤ 0 := by
    intro t
    have hl := (lowerSemicontinuousAt_iff_le_lowerLimit.1
      (lowerSemicontinuous_proximalHull f t 0)).trans
      (lowerLimit_mono (fun y ↦ proximalHull_le f t y) 0)
    refine hl.trans (iSup₂_le fun δ hδ ↦ ?_)
    have hy : min (δ / 2) (1 / 2) ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_min (by positivity) (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    have hyball : min (δ / 2) (1 / 2) ∈ closedBall (0 : ℝ) δ := by
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos hy.1]
      linarith [min_le_left (δ / 2) (1 / 2)]
    exact (biInf_le _ hyball).trans (by rw [hf, indicatorVA_apply_mem hy])
  rw [h0] at hlim
  have hev := hlim.eventually (lt_mem_nhds (show (1 : EReal) < ⊤ from EReal.coe_lt_top 1))
  obtain ⟨t, ht⟩ := hev.exists
  exact absurd (lt_of_lt_of_le ht (hle t)) (by norm_num)

/-! ## Exercise 1.45 -/

section ProximalInequalities

omit [InnerProductSpace ℝ E] in
theorem moreauEnvelopeEReal_mono {f g : E → EReal} (h : ∀ x, f x ≤ g x) (t : ℝ) (x : E) :
    moreauEnvelopeEReal f t x ≤ moreauEnvelopeEReal g t x :=
  iInf_mono fun w ↦ add_le_add (h w) le_rfl

/-- **Exercise 1.45** (proximal inequalities): `eλ f₁ ≤ eλ f₂` iff `hλ f₁ ≤ hλ f₂`. -/
theorem moreauEnvelopeEReal_le_iff_proximalHull_le {f₁ f₂ : E → EReal} {t : ℝ} :
    (∀ x, moreauEnvelopeEReal f₁ t x ≤ moreauEnvelopeEReal f₂ t x) ↔
      ∀ x, proximalHull f₁ t x ≤ proximalHull f₂ t x := by
  constructor
  · intro h x
    rw [proximalHull_eq_iSup_envelope, proximalHull_eq_iSup_envelope]
    exact iSup_mono fun w ↦ EReal.sub_le_sub (h w) le_rfl
  · intro h x
    rw [← moreauEnvelopeEReal_proximalHull f₁ t, ← moreauEnvelopeEReal_proximalHull f₂ t]
    exact moreauEnvelopeEReal_mono h t x

/-- **Exercise 1.45**: `f₁` and `f₂` have the same Moreau `λ`-envelope iff they have the same
`λ`-proximal hull. -/
theorem moreauEnvelopeEReal_eq_iff_proximalHull_eq {f₁ f₂ : E → EReal} {t : ℝ} :
    moreauEnvelopeEReal f₁ t = moreauEnvelopeEReal f₂ t ↔
      proximalHull f₁ t = proximalHull f₂ t := by
  constructor
  · intro h
    funext x
    exact le_antisymm (moreauEnvelopeEReal_le_iff_proximalHull_le.1 (fun y ↦ (congrFun h y).le) x)
      (moreauEnvelopeEReal_le_iff_proximalHull_le.1 (fun y ↦ (congrFun h y).ge) x)
  · intro h
    funext x
    exact le_antisymm (moreauEnvelopeEReal_le_iff_proximalHull_le.2 (fun y ↦ (congrFun h y).le) x)
      (moreauEnvelopeEReal_le_iff_proximalHull_le.2 (fun y ↦ (congrFun h y).ge) x)

end ProximalInequalities

/-! ## Example 1.46 -/

section DoubleEnvelopes

omit [InnerProductSpace ℝ E] in
/-- `inf eλ f = inf f` for `λ > 0`. -/
theorem iInf_moreauEnvelopeEReal (f : E → EReal) {t : ℝ} (ht : 0 < t) :
    (⨅ x, moreauEnvelopeEReal f t x) = ⨅ x, f x := by
  apply le_antisymm
  · exact iInf_mono fun x ↦ moreauEnvelopeEReal_le f t x
  · refine le_iInf fun x ↦ le_iInf fun w ↦ ?_
    exact (iInf_le f w).trans (le_add_of_nonneg_right (EReal.coe_nonneg.2 (by positivity)))

variable [FiniteDimensional ℝ E]

/-- `argmin eλ f = argmin f` for proper lsc `f` and `λ ∈ (0, λ_f)`. -/
theorem argmin_moreauEnvelopeEReal {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    {t : ℝ} (ht : 0 < t) (hthr : (t : EReal) < proxThreshold f) :
    argmin (moreauEnvelopeEReal f t) = argmin f := by
  ext x
  rw [mem_argmin_iff, mem_argmin_iff, iInf_moreauEnvelopeEReal f ht]
  constructor
  · rintro ⟨hx, hlt⟩
    obtain ⟨w, hw⟩ := (proximalMappingEReal_nonempty_isCompact hp hl ht hthr x).1
    have hwval : f w + (((1 / (2 * t)) * ‖w - x‖ ^ 2 : ℝ) : EReal) =
        moreauEnvelopeEReal f t x := hw.1
    have hle : f w + (((1 / (2 * t)) * ‖w - x‖ ^ 2 : ℝ) : EReal) ≤ f w := by
      rw [hwval, hx]; exact iInf_le f w
    have hfw_top : f w ≠ ⊤ := by
      intro h
      have hlt' : f w + (((1 / (2 * t)) * ‖w - x‖ ^ 2 : ℝ) : EReal) < ⊤ := by
        rw [hwval, hx]; exact hlt
      rw [h, EReal.top_add_coe] at hlt'
      exact lt_irrefl _ hlt'
    have ha : f w = ((f w).toReal : EReal) := (EReal.coe_toReal hfw_top (hp.2 w).ne').symm
    rw [ha, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
    have hq : ‖w - x‖ ^ 2 ≤ 0 := by
      have hc : 0 < 1 / (2 * t) := by positivity
      nlinarith [sq_nonneg ‖w - x‖]
    have hwx : w = x := by
      have : ‖w - x‖ = 0 := by nlinarith [norm_nonneg (w - x)]
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    subst hwx
    refine ⟨le_antisymm ?_ (iInf_le f w), hlt⟩
    have h2 : f w + (((1 / (2 * t)) * ‖w - w‖ ^ 2 : ℝ) : EReal) = f w := by simp
    rw [← h2, hwval, hx]
  · rintro ⟨hx, hlt⟩
    exact ⟨le_antisymm ((moreauEnvelopeEReal_le f t x).trans hx.le)
      ((iInf_moreauEnvelopeEReal f ht).symm.le.trans (iInf_le _ x)), hlt⟩

omit [FiniteDimensional ℝ E] in
/-- **Example 1.46**, formula 1(19), second equality: `e_{λ,μ} f = hμ[e_{λ-μ} f]`, for every
`f`. -/
theorem doubleEnvelope_eq_proximalHull_moreauEnvelope (f : E → EReal) {lam mu : ℝ}
    (hmu : 0 < mu) (hml : mu < lam) :
    doubleEnvelope f lam mu = proximalHull (moreauEnvelopeEReal f (lam - mu)) mu := by
  rw [doubleEnvelope_eq_neg_moreauEnvelope_neg, proximalHull_eq_neg_moreauEnvelope_neg,
    moreauEnvelopeEReal_moreauEnvelopeEReal f hmu (sub_pos.2 hml), add_sub_cancel]

/-- **Example 1.46**, formula 1(19), first equality: `e_{λ,μ} f = e_{λ-μ}[hλ f]`.  It follows from
the `(λ - μ)`-proximality of `-e_{λ,μ} f` (Proposition 12.62) and the semigroup law 1.29(c). -/
theorem doubleEnvelope_eq_moreauEnvelope_proximalHull {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) {lam mu : ℝ} (hmu : 0 < mu) (hml : mu < lam)
    (hthr : (lam : EReal) < proxThreshold f) :
    doubleEnvelope f lam mu = moreauEnvelopeEReal (proximalHull f lam) (lam - mu) := by
  have hnegD : (fun x ↦ -doubleEnvelope f lam mu x) =
      moreauEnvelopeEReal (fun y ↦ -moreauEnvelopeEReal f lam y) mu := by
    funext x
    rw [doubleEnvelope_eq_neg_moreauEnvelope_neg, neg_neg]
  have hsemi : moreauEnvelopeEReal (moreauEnvelopeEReal (fun y ↦ -moreauEnvelopeEReal f lam y) mu)
      (lam - mu) = moreauEnvelopeEReal (fun y ↦ -moreauEnvelopeEReal f lam y) lam := by
    rw [moreauEnvelopeEReal_moreauEnvelopeEReal _ (sub_pos.2 hml) hmu, sub_add_cancel]
  have hhull : (fun x ↦ -moreauEnvelopeEReal (fun y ↦ -doubleEnvelope f lam mu y) (lam - mu) x) =
      proximalHull f lam := by
    rw [hnegD, hsemi, proximalHull_eq_neg_moreauEnvelope_neg]
  have hneg := (doubleEnvelope_hypoconvexity hp hl hmu hml hthr).2.1
  rw [proximalHull_eq_neg_moreauEnvelope_neg, hhull] at hneg
  funext x
  exact (neg_inj.1 (congrFun hneg x)).symm

/-- **Example 1.46**: `eλ f ≤ e_{λ,μ} f ≤ e_{λ-μ} f ≤ f`. -/
theorem doubleEnvelope_bracket {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    {lam mu : ℝ} (hmu : 0 < mu) (hml : mu < lam) (hthr : (lam : EReal) < proxThreshold f)
    (x : E) :
    moreauEnvelopeEReal f lam x ≤ doubleEnvelope f lam mu x ∧
      doubleEnvelope f lam mu x ≤ moreauEnvelopeEReal f (lam - mu) x ∧
      moreauEnvelopeEReal f (lam - mu) x ≤ f x := by
  refine ⟨le_iSup_of_le x (by simp), ?_, moreauEnvelopeEReal_le f _ x⟩
  rw [doubleEnvelope_eq_moreauEnvelope_proximalHull hp hl hmu hml hthr]
  exact moreauEnvelopeEReal_mono (proximalHull_le f lam) _ x

/-- **Example 1.46**: `inf e_{λ,μ} f = inf eλ f = inf f`. -/
theorem iInf_doubleEnvelope {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    {lam mu : ℝ} (hmu : 0 < mu) (hml : mu < lam) (hthr : (lam : EReal) < proxThreshold f) :
    (⨅ x, doubleEnvelope f lam mu x) = ⨅ x, f x ∧
      (⨅ x, moreauEnvelopeEReal f lam x) = ⨅ x, f x := by
  have hlam : 0 < lam := hmu.trans hml
  have he := iInf_moreauEnvelopeEReal f hlam
  refine ⟨le_antisymm ?_ ?_, he⟩
  · exact iInf_mono fun x ↦ (doubleEnvelope_bracket hp hl hmu hml hthr x).2.1.trans
      (doubleEnvelope_bracket hp hl hmu hml hthr x).2.2
  · exact he.symm.le.trans (iInf_mono fun x ↦ (doubleEnvelope_bracket hp hl hmu hml hthr x).1)

/-- **Example 1.46**: `argmin e_{λ,μ} f = argmin eλ f = argmin f`. -/
theorem argmin_doubleEnvelope {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    {lam mu : ℝ} (hmu : 0 < mu) (hml : mu < lam) (hthr : (lam : EReal) < proxThreshold f) :
    argmin (doubleEnvelope f lam mu) = argmin f ∧
      argmin (moreauEnvelopeEReal f lam) = argmin f := by
  have hlam : 0 < lam := hmu.trans hml
  have harg := argmin_moreauEnvelopeEReal hp hl hlam hthr
  obtain ⟨hinfD, hinfe⟩ := iInf_doubleEnvelope hp hl hmu hml hthr
  refine ⟨?_, harg⟩
  ext x
  rw [mem_argmin_iff, mem_argmin_iff, hinfD]
  constructor
  · rintro ⟨hx, hlt⟩
    have hmem : x ∈ argmin (moreauEnvelopeEReal f lam) := by
      rw [mem_argmin_iff, hinfe]
      refine ⟨le_antisymm (((doubleEnvelope_bracket hp hl hmu hml hthr x).1).trans hx.le) ?_, hlt⟩
      exact hinfe.symm.le.trans (iInf_le _ x)
    rw [harg] at hmem
    exact hmem
  · rintro ⟨hx, hlt⟩
    refine ⟨le_antisymm (((doubleEnvelope_bracket hp hl hmu hml hthr x).2.1.trans
      (doubleEnvelope_bracket hp hl hmu hml hthr x).2.2).trans hx.le) ?_, hlt⟩
    exact hinfD.symm.le.trans (iInf_le _ x)

end DoubleEnvelopes

end RW
