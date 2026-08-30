/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Proximal Mappings

Example 5.23(b) says that for a proper lsc `f` that is prox-bounded with
threshold `λf`, and any `λ ∈ (0, λf)`, the proximal mapping `Pλf` of
Definition 1.22 is everywhere outer semicontinuous and locally bounded.  The
book's Detail specializes 5.22 to it, "cf. 1.25", and that is the route taken
here.

What was missing was the mapping itself.  Chapter 1 carries `IsProxBounded`
and the threshold `proxThreshold`, and Chapter 3 carries the extended-real
envelope `moreauEnvelopeEReal`, but `Pλf` had no extended-real form.  It is
supplied here as `paramArgmin` of the *proximal integrand*

    proxIntegrand f λ (w, x) = f(w) + (1/2λ)|w - x|²,

which makes `eλf = valueFunction (proxIntegrand f λ)` and
`Pλf = paramArgmin (proxIntegrand f λ)` true by definition, so that 5.22
applies to `Pλf` with nothing to translate.

Three facts about that integrand are what 5.22 consumes, and they are the
content of the file:

* it is lower semicontinuous and proper when `f` is.  Neither is formal:
  `EReal` addition is not continuous, so lower semicontinuity of a sum
  `F + g` with `F` lsc and `g` a *continuous real* function is proved here
  from scratch, in `lowerSemicontinuousAt_add_coe`.  The one place the
  argument could go wrong -- `⊥ + ⊤` -- cannot arise, because the second
  summand is a real number, and that is also why `(a, t) ↦ a + t` is
  genuinely continuous as a map `EReal × ℝ → EReal`;
* the envelope is bounded above near every point, and upper semicontinuous
  everywhere.  Both come from `eλf(x) ≤ f(w₀) + (1/2λ)|w₀ - x|²` at a single
  `w₀ ∈ dom f`: the bound is uniform on a ball, and an infimum of continuous
  functions is upper semicontinuous.  **The book obtains upper
  semicontinuity from the full continuity of `eλf` in 1.25; that is not
  needed, and 1.25 is not used**;
* it is level-bounded in `w` locally uniformly in `x` when `λ < λf`.  This is
  the one substantive step, and it is the argument inside the proof of 1.25,
  extracted for a fixed `λ`: the threshold supplies `λ₁ ∈ (λ, λf)` and a
  point `x₁` with `e_{λ₁}f(x₁) > -∞`, hence a real `β` with
  `f(w) + (1/2λ₁)|w - x₁|² ≥ β` for every `w`.  Comparing that with
  `f(w) + (1/2λ)|w - x|² ≤ α` cancels the `f(w)` and leaves a purely
  real inequality between two quadratics whose leading coefficients differ by
  `1/2λ - 1/2λ₁ > 0`, which bounds `|w|` uniformly for `x` in a ball.

**Each clause needs less than the printed statement supplies.**  Outer
semicontinuity uses no prox-boundedness at all -- only that `f` is proper and
lsc -- and holds for every `λ`; past the threshold it holds because `Pλf` is
then empty-valued.  Local boundedness uses no lower semicontinuity.  The
combined statement is recorded with the book's own hypotheses.
-/

import RockafellarWets.Chapter5.OptimalSetMappings
import RockafellarWets.Chapter3.ExtendedCancellationCompletion

open Bornology Filter Metric Set Topology

namespace RW

section ERealAddition

/-- If `c < a + t` with `t` real, then `a` can be lowered strictly and the
inequality kept.  The side conditions of `EReal.sub_lt_iff` are automatic
because a real coercion is neither `⊥` nor `⊤`. -/
theorem exists_lt_add_coe {c a : EReal} {t : ℝ} (h : c < a + (t : EReal)) :
    ∃ a' < a, c < a' + (t : EReal) := by
  obtain ⟨a', h1, h2⟩ := exists_between (EReal.sub_lt_of_lt_add h)
  exact ⟨a', h2, (EReal.sub_lt_iff (.inl (EReal.coe_ne_bot t))
    (.inl (EReal.coe_ne_top t))).1 h1⟩

variable {X : Type*} [TopologicalSpace X]

/-- Adding a *real* continuous function to a constant `EReal` is continuous.
`EReal` addition is not continuous in general, but the exceptional pairs are
`(⊥, ⊤)` and `(⊤, ⊥)`, and a real coercion is neither. -/
theorem continuousAt_ereal_const_add {u : X → ℝ} {x : X} (a : EReal)
    (hu : ContinuousAt u x) :
    ContinuousAt (fun y ↦ a + ((u y : ℝ) : EReal)) x := by
  have hpair : Tendsto (fun y ↦ ((a, ((u y : ℝ) : EReal)) : EReal × EReal))
      (nhds x) (nhds (a, ((u x : ℝ) : EReal))) :=
    ContinuousAt.prodMk continuousAt_const
      (continuous_coe_real_ereal.continuousAt.comp hu)
  have hadd := EReal.continuousAt_add (p := (a, ((u x : ℝ) : EReal)))
    (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))
  exact Filter.Tendsto.comp (f := fun y ↦ ((a, ((u y : ℝ) : EReal)) : EReal × EReal))
    (g := fun p : EReal × EReal ↦ p.1 + p.2) hadd hpair

theorem continuous_ereal_const_add {u : X → ℝ} (a : EReal) (hu : Continuous u) :
    Continuous fun y ↦ a + ((u y : ℝ) : EReal) :=
  continuous_iff_continuousAt.2 fun _ ↦ continuousAt_ereal_const_add a hu.continuousAt

/-- A lower semicontinuous `EReal` function plus a continuous real one is
lower semicontinuous.  Mathlib's `LowerSemicontinuous.add` does not apply,
since it wants `ContinuousAdd` on the codomain and `EReal` has none.

Below the value `F x + g x` sits some `a' < F x` with `a' + g x` still above
it; lower semicontinuity keeps `F` above `a'` nearby, and `y ↦ a' + g y` is
continuous, so the sum stays above. -/
theorem lowerSemicontinuousAt_add_coe {F : X → EReal} {g : X → ℝ} {x : X}
    (hF : LowerSemicontinuousAt F x) (hg : ContinuousAt g x) :
    LowerSemicontinuousAt (fun y ↦ F y + ((g y : ℝ) : EReal)) x := by
  intro b hb
  obtain ⟨a', ha', hb'⟩ := exists_lt_add_coe hb
  have hcont := continuousAt_ereal_const_add (u := g) (x := x) a' hg
  filter_upwards [hF a' ha', hcont (eventually_gt_nhds hb')] with y hy1 hy2
  exact lt_of_lt_of_le hy2 (add_le_add hy1.le le_rfl)

theorem lowerSemicontinuous_add_coe {F : X → EReal} {g : X → ℝ}
    (hF : LowerSemicontinuous F) (hg : Continuous g) :
    LowerSemicontinuous fun y ↦ F y + ((g y : ℝ) : EReal) :=
  fun x ↦ lowerSemicontinuousAt_add_coe (hF x) hg.continuousAt

end ERealAddition

section ValueFunctionUsc

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

omit [NormedAddCommGroup E] in
/-- A value function is upper semicontinuous as soon as every slice
`u ↦ f(x, u)` is: an infimum of upper semicontinuous functions is upper
semicontinuous, because the strict sublevel sets are unions.

This is all of the continuity of `p` that the outer semicontinuity clause of
5.22 asks for. -/
theorem upperSemicontinuous_valueFunction {g : E × F → EReal}
    (h : ∀ x : E, UpperSemicontinuous fun u ↦ g (x, u)) :
    UpperSemicontinuous (valueFunction g) := by
  intro u a ha
  obtain ⟨x, hx⟩ := iInf_lt_iff.1 ha
  filter_upwards [h x u a hx] with u' hu'
  exact lt_of_le_of_lt (iInf_le _ x) hu'

end ValueFunctionUsc

section ProximalDefs

variable {E : Type*} [NormedAddCommGroup E]

/-- The integrand of **Definition 1.22** read as a parametric minimization
problem: the decision variable is `w`, the parameter is `x`. -/
noncomputable def proxIntegrand (f : E → EReal) (lam : ℝ) : E × E → EReal :=
  fun p ↦ f p.1 + (((1 / (2 * lam)) * ‖p.1 - p.2‖ ^ 2 : ℝ) : EReal)

/-- The Moreau envelope is the value function of the proximal integrand. -/
theorem moreauEnvelopeEReal_eq_valueFunction (f : E → EReal) (lam : ℝ) :
    moreauEnvelopeEReal f lam = valueFunction (proxIntegrand f lam) := rfl

/-- **Definition 1.22**, the proximal mapping `Pλf` for extended-real `f`:
the argmin of the proximal integrand, under Chapter 1's `argmin` convention
that an identically-`+∞` slice has no minimizers. -/
noncomputable def proxMappingEReal (f : E → EReal) (lam : ℝ) : E → Set E :=
  paramArgmin (proxIntegrand f lam)

theorem mem_proxMappingEReal {f : E → EReal} {lam : ℝ} {x w : E} :
    w ∈ proxMappingEReal f lam x ↔
      proxIntegrand f lam (w, x) = moreauEnvelopeEReal f lam x ∧
        moreauEnvelopeEReal f lam x < ⊤ :=
  mem_paramArgmin_iff _ _ _

theorem lowerSemicontinuous_proxIntegrand {f : E → EReal}
    (hf : LowerSemicontinuous f) (lam : ℝ) :
    LowerSemicontinuous (proxIntegrand f lam) :=
  lowerSemicontinuous_add_coe
    (fun p b hb ↦ continuous_fst.continuousAt.eventually (hf p.1 b hb))
    (by fun_prop)

theorem isProper_proxIntegrand {f : E → EReal} (hf : IsProper f) {lam : ℝ} :
    IsProper (proxIntegrand f lam) := by
  obtain ⟨w₀, hw₀⟩ := hf.1
  refine ⟨⟨(w₀, w₀), ?_⟩, fun p ↦ ?_⟩
  · exact EReal.add_lt_top hw₀.ne_top (EReal.coe_ne_top _)
  · exact EReal.bot_lt_add_iff.2 ⟨hf.2 p.1, EReal.bot_lt_coe _⟩

/-- The envelope is finite above: a single point of `dom f` bounds it. -/
theorem valueFunction_proxIntegrand_lt_top {f : E → EReal} (hf : IsProper f)
    (lam : ℝ) (x : E) : valueFunction (proxIntegrand f lam) x < ⊤ := by
  obtain ⟨w₀, hw₀⟩ := hf.1
  exact lt_of_le_of_lt (iInf_le _ w₀)
    (EReal.add_lt_top hw₀.ne_top (EReal.coe_ne_top _))

/-- The envelope is bounded above on a whole ball, which is the hypothesis
the local-boundedness clause of 5.22 asks for.  The bound is the value of the
integrand at a fixed `w₀ ∈ dom f`, taken at the farthest admissible `x`. -/
theorem exists_eventually_valueFunction_proxIntegrand_le {f : E → EReal}
    (hf : IsProper f) {lam : ℝ} (hlam : 0 < lam) (x : E) :
    ∃ α : ℝ, ∀ᶠ x' in nhds x,
      valueFunction (proxIntegrand f lam) x' ≤ (α : EReal) := by
  obtain ⟨w₀, hw₀⟩ := hf.1
  obtain ⟨β, hβ, -⟩ := EReal.exists_between_coe_real hw₀
  have hc : (0 : ℝ) < 1 / (2 * lam) := by positivity
  refine ⟨β + (1 / (2 * lam)) * (‖w₀ - x‖ + 1) ^ 2, ?_⟩
  filter_upwards [closedBall_mem_nhds x one_pos] with x' hx'
  have hx'1 : ‖x - x'‖ ≤ 1 := by
    rw [← dist_eq_norm]
    exact mem_closedBall'.1 hx'
  have hnorm : ‖w₀ - x'‖ ≤ ‖w₀ - x‖ + 1 := by
    have := norm_sub_le_norm_sub_add_norm_sub w₀ x x'
    linarith
  have hsq : (1 / (2 * lam)) * ‖w₀ - x'‖ ^ 2
      ≤ (1 / (2 * lam)) * (‖w₀ - x‖ + 1) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hc.le
  calc valueFunction (proxIntegrand f lam) x'
      ≤ proxIntegrand f lam (w₀, x') := iInf_le _ w₀
    _ ≤ (β : EReal) + (((1 / (2 * lam)) * ‖w₀ - x'‖ ^ 2 : ℝ) : EReal) :=
        add_le_add hβ.le le_rfl
    _ ≤ ((β + (1 / (2 * lam)) * (‖w₀ - x‖ + 1) ^ 2 : ℝ) : EReal) := by
        rw [← EReal.coe_add]
        exact EReal.coe_le_coe_iff.2 (by linarith)

/-- The envelope is upper semicontinuous, being an infimum of the continuous
functions `x ↦ f(w) + (1/2λ)|w - x|²`.  The book takes this from the full
continuity of `eλf` in 1.25; only the upper half is needed, and it costs
nothing. -/
theorem upperSemicontinuous_valueFunction_proxIntegrand (f : E → EReal)
    (lam : ℝ) : UpperSemicontinuous (valueFunction (proxIntegrand f lam)) :=
  upperSemicontinuous_valueFunction fun w ↦
    (continuous_ereal_const_add (f w) (by fun_prop)).upperSemicontinuous

/-- The real-number core of the level-boundedness argument: two quadratics in
`t` whose leading coefficients differ by `c - c₁ > 0` can cross only for
bounded `t`.  Dividing the expanded inequality by `t ≥ 1` avoids the
quadratic formula. -/
private theorem le_max_of_quadratic_gap {c c₁ α β R S t : ℝ} (hcc : c₁ < c)
    (h : β + c * (t - R) ^ 2 ≤ α + c₁ * (t + S) ^ 2) :
    t ≤ max 1 ((|α - β + c₁ * S ^ 2 - c * R ^ 2|
      + (2 * c * R + 2 * c₁ * S)) / (c - c₁)) := by
  rcases le_or_gt t 1 with h1 | h1
  · exact le_max_of_le_left h1
  refine le_max_of_le_right ?_
  rw [le_div_iff₀ (by linarith)]
  set A := α - β + c₁ * S ^ 2 - c * R ^ 2 with hA_def
  set B := 2 * c * R + 2 * c₁ * S with hB_def
  have hexp : (c - c₁) * t ^ 2 ≤ A + B * t := by rw [hA_def, hB_def]; nlinarith [h]
  nlinarith [hexp, le_abs_self A,
    mul_nonneg (abs_nonneg A) (by linarith : (0 : ℝ) ≤ t - 1)]

/-- The step of **Exercise 1.24** that 5.23(b) needs, in the form the proof of
1.25 uses it: below the prox-threshold the proximal integrand is level-bounded
in `w` locally uniformly in `x`.

Being below the threshold gives a larger `λ₁` whose envelope is finite
somewhere, hence a real `β` with `f(w) + (1/2λ₁)|w - x₁|² ≥ β` for every `w`.
Adding `(1/2λ)|w - x|²` to that and using `f(w) + (1/2λ)|w - x|² ≤ α` cancels
`f(w)` between the two, leaving a real inequality between quadratics in `|w|`
with a strictly positive gap `1/2λ - 1/2λ₁` in the leading coefficient. -/
theorem isLevelBoundedInXLocallyUniformly_proxIntegrand {f : E → EReal} {lam : ℝ}
    (hlam : 0 < lam) (hthr : (lam : EReal) < proxThreshold f) :
    IsLevelBoundedInXLocallyUniformly (proxIntegrand f lam) := by
  obtain ⟨lam₁, hlam₁⟩ := lt_iSup_iff.1 hthr
  obtain ⟨⟨hlam₁pos, x₁, hx₁⟩, hlt⟩ := lt_iSup_iff.1 hlam₁
  have hll : lam < lam₁ := EReal.coe_lt_coe_iff.1 hlt
  obtain ⟨β, -, hβ⟩ := EReal.exists_between_coe_real hx₁
  have hlow : ∀ w : E, (β : EReal)
      ≤ f w + (((1 / (2 * lam₁)) * ‖w - x₁‖ ^ 2 : ℝ) : EReal) :=
    fun w ↦ (lt_of_lt_of_le hβ (iInf_le _ w)).le
  have hcpos : (0 : ℝ) < 1 / (2 * lam) := by positivity
  have hc₁pos : (0 : ℝ) < 1 / (2 * lam₁) := by positivity
  have hcc : 1 / (2 * lam₁) < 1 / (2 * lam) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  intro xBar α
  refine ⟨1, one_pos, ?_⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max (max 1 ((|α - β + (1 / (2 * lam₁)) * ‖x₁‖ ^ 2
      - (1 / (2 * lam)) * (‖xBar‖ + 1) ^ 2|
      + (2 * (1 / (2 * lam)) * (‖xBar‖ + 1) + 2 * (1 / (2 * lam₁)) * ‖x₁‖))
      / (1 / (2 * lam) - 1 / (2 * lam₁)))) (‖xBar‖ + 1), ?_⟩
  rintro ⟨w, x⟩ ⟨⟨-, hx⟩, hlev⟩
  have hxR : ‖x‖ ≤ ‖xBar‖ + 1 := by
    have h1 : ‖x - xBar‖ ≤ 1 := by rw [← dist_eq_norm]; exact hx
    linarith [norm_sub_norm_le x xBar]
  -- The two integrands compared through the common value `f w`.
  have hkey : ((β + (1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)
      ≤ ((α + (1 / (2 * lam₁)) * ‖w - x₁‖ ^ 2 : ℝ) : EReal) := by
    rw [EReal.coe_add, EReal.coe_add]
    calc (β : EReal) + (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)
        ≤ (f w + (((1 / (2 * lam₁)) * ‖w - x₁‖ ^ 2 : ℝ) : EReal))
          + (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal) :=
          add_le_add (hlow w) le_rfl
      _ = (f w + (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal))
          + (((1 / (2 * lam₁)) * ‖w - x₁‖ ^ 2 : ℝ) : EReal) := by
          rw [add_assoc, add_assoc,
            add_comm (((1 / (2 * lam₁)) * ‖w - x₁‖ ^ 2 : ℝ) : EReal)]
      _ ≤ (α : EReal) + (((1 / (2 * lam₁)) * ‖w - x₁‖ ^ 2 : ℝ) : EReal) :=
          add_le_add hlev le_rfl
  have hreal : β + (1 / (2 * lam)) * ‖w - x‖ ^ 2
      ≤ α + (1 / (2 * lam₁)) * ‖w - x₁‖ ^ 2 := EReal.coe_le_coe_iff.1 hkey
  rw [Prod.norm_mk, max_le_iff]
  refine ⟨?_, le_max_of_le_right hxR⟩
  rcases le_or_gt ‖w‖ (‖xBar‖ + 1) with hw | hw
  · exact le_max_of_le_right hw
  refine le_max_of_le_left (le_max_of_quadratic_gap hcc ?_)
  have hle1 : (‖w‖ - (‖xBar‖ + 1)) ^ 2 ≤ ‖w - x‖ ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith [norm_sub_norm_le w x]) 2
  have hle2 : ‖w - x₁‖ ^ 2 ≤ (‖w‖ + ‖x₁‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
  linarith [mul_le_mul_of_nonneg_left hle1 hcpos.le,
    mul_le_mul_of_nonneg_left hle2 hc₁pos.le]

end ProximalDefs

section ProximalContinuity

variable {E : Type*} [NormedAddCommGroup E]

theorem svLocallyBoundedAt_of_within_univ {F : Type*} [PseudoMetricSpace F]
    {S : E → Set F} {x : E} (h : SvLocallyBoundedWithinAt S univ x) :
    SvLocallyBoundedAt S x := by
  obtain ⟨V, hV, hb⟩ := h
  exact ⟨V, hV, by rwa [univ_inter] at hb⟩

/-- **Example 5.23(b)**, local boundedness.  This is the first clause of 5.22,
whose two hypotheses are the level-boundedness of the proximal integrand and
an upper bound on the envelope near the point.

Lower semicontinuity of `f` is not used. -/
theorem svLocallyBounded_proxMappingEReal {f : E → EReal} (hf : IsProper f)
    {lam : ℝ} (hlam : 0 < lam) (hthr : (lam : EReal) < proxThreshold f) :
    SvLocallyBounded (proxMappingEReal f lam) := by
  intro x
  obtain ⟨α, hα⟩ := exists_eventually_valueFunction_proxIntegrand_le hf hlam x
  exact svLocallyBoundedAt_of_within_univ
    (svLocallyBoundedWithinAt_paramArgmin
      (isLevelBoundedInXLocallyUniformly_proxIntegrand hlam hthr)
      ⟨α, nhdsWithin_le_nhds hα⟩)

/-- **Example 5.23(b)**, outer semicontinuity.  This is the second clause of
5.22, which needs no level boundedness -- only lower semicontinuity of the
integrand and upper semicontinuity of the envelope.

Neither prox-boundedness nor `λ < λf` is used, and neither is `λ > 0`: past
the threshold the envelope can be `-∞`, and a proper `f` then leaves `Pλf`
empty-valued, which is outer semicontinuous for want of anything to
contradict. -/
theorem svOsc_proxMappingEReal {f : E → EReal} (hf : IsProper f)
    (hlsc : LowerSemicontinuous f) (lam : ℝ) :
    SvOsc (proxMappingEReal f lam) := fun x ↦
  svOscWithinAt_univ.1 (svOscWithinAt_paramArgmin
    (lowerSemicontinuous_proxIntegrand hlsc lam)
    (valueFunction_proxIntegrand_lt_top hf lam x)
    fun y hy ↦ nhdsWithin_le_nhds
      (upperSemicontinuous_valueFunction_proxIntegrand f lam x y hy))

/-- **Example 5.23(b)** as printed: for a proper lsc `f` and `λ` strictly
between `0` and the prox-threshold, `Pλf` is everywhere outer semicontinuous
and locally bounded. -/
theorem svOsc_and_svLocallyBounded_proxMappingEReal {f : E → EReal}
    (hf : IsProper f) (hlsc : LowerSemicontinuous f) {lam : ℝ} (hlam : 0 < lam)
    (hthr : (lam : EReal) < proxThreshold f) :
    SvOsc (proxMappingEReal f lam) ∧ SvLocallyBounded (proxMappingEReal f lam) :=
  ⟨svOsc_proxMappingEReal hf hlsc lam,
    svLocallyBounded_proxMappingEReal hf hlam hthr⟩

end ProximalContinuity

end RW
