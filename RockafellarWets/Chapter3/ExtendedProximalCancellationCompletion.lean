/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Extended-real proximal cancellation infrastructure

This file supplies the attainment substrate for the exact extended-real form
of Corollary 3.37.  For a proper lower-semicontinuous convex function, every
positive-parameter proximal objective is proper, lower-semicontinuous, and
level-coercive.  Consequently its minimizer set is nonempty, its Moreau
envelope is finite, and every proximal point belongs to the effective domain.
-/

import RockafellarWets.Chapter3.ERealInfimum
import RockafellarWets.Chapter3.ExtendedCancellationCompletion

open Bornology EReal Set Topology

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The extended-real objective minimized in the Moreau envelope. -/
def proximalObjectiveEReal (f : E → EReal) (lam : ℝ) (x w : E) : EReal :=
  f w + (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)

/-- The proximal mapping of an extended-real-valued function. -/
def proximalMappingEReal (f : E → EReal) (lam : ℝ) (x : E) : Set E :=
  argmin (proximalObjectiveEReal f lam x)

omit [InnerProductSpace ℝ E] in
@[simp]
theorem mem_proximalMappingEReal_iff
    {f : E → EReal} {lam : ℝ} {x w : E} :
    w ∈ proximalMappingEReal f lam x ↔
      proximalObjectiveEReal f lam x w = moreauEnvelopeEReal f lam x := by
  rfl

omit [InnerProductSpace ℝ E] in
/-- Adding the finite quadratic proximal kernel to a proper function preserves
properness. -/
theorem isProper_proximalObjectiveEReal
    {f : E → EReal} (hproper : IsProper f) (lam : ℝ) (x : E) :
    IsProper (proximalObjectiveEReal f lam x) := by
  constructor
  · rcases hproper.1 with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    exact EReal.add_lt_top (ne_of_lt hw) (EReal.coe_ne_top _)
  · intro w
    exact EReal.bot_lt_add_iff.mpr ⟨hproper.2 w, EReal.bot_lt_coe _⟩

omit [InnerProductSpace ℝ E] in
/-- Adding the finite continuous quadratic proximal kernel preserves lower
semicontinuity of an extended-real function. -/
theorem lowerSemicontinuous_proximalObjectiveEReal
    {f : E → EReal} (hlsc : LowerSemicontinuous f) (lam : ℝ) (x : E) :
    LowerSemicontinuous (proximalObjectiveEReal f lam x) := by
  have hnorm : Continuous (fun w : E ↦ ‖w - x‖) :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hquadReal : Continuous (fun w : E ↦
      (1 / (2 * lam)) * ‖w - x‖ ^ 2) :=
    continuous_const.mul (hnorm.pow 2)
  have hquad : LowerSemicontinuous (fun w : E ↦
      ((((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal))) :=
    (continuous_coe_real_ereal.comp hquadReal).lowerSemicontinuous
  refine LowerSemicontinuous.add' hlsc hquad ?_
  intro w
  exact EReal.continuousAt_add
    (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _))

omit [InnerProductSpace ℝ E] in
/-- Completing the square bounds a positive quadratic below by any prescribed
linear function. -/
private theorem quadratic_lower_bound_selection
    {gamma lam t : ℝ} (hlam : 0 < lam) :
    -(lam * gamma ^ 2) / 2 ≤
      gamma * t + (1 / (2 * lam)) * t ^ 2 := by
  have h2lam : 0 < 2 * lam := by positivity
  have hs : 0 ≤ ((t + lam * gamma) ^ 2) / (2 * lam) :=
    div_nonneg (sq_nonneg _) h2lam.le
  have hEq :
      ((t + lam * gamma) ^ 2) / (2 * lam) =
        (1 / (2 * lam)) * t ^ 2 + gamma * t +
          (lam * gamma ^ 2) / 2 := by
    field_simp [hlam.ne']
    ring
  rw [hEq] at hs
  linarith

/-- An affine minorant makes every positive-parameter proximal objective
level-coercive. -/
theorem isLevelCoercive_proximalObjectiveEReal_of_affineMinorant
    {f : E → EReal} (l : E →L[ℝ] ℝ) (b : ℝ)
    (hminor : ∀ w : E, (((l w + b : ℝ) : EReal) ≤ f w))
    {lam : ℝ} (hlam : 0 < lam) (x : E) :
    IsLevelCoercive (proximalObjectiveEReal f lam x) := by
  let L : ℝ := ‖l‖
  let beta : ℝ :=
    b - (L + 1) * ‖x‖ - lam * (L + 1) ^ 2 / 2
  refine ⟨1, zero_lt_one, beta, ?_⟩
  intro w
  have hlower : -L * ‖w‖ ≤ l w := by
    have hop : ‖l w‖ ≤ L * ‖w‖ := by
      simpa only [L] using l.le_opNorm w
    have hneg : -L * ‖w‖ ≤ -‖l w‖ := by linarith
    exact hneg.trans (by
      simpa only [Real.norm_eq_abs] using neg_abs_le (l w))
  have htriangle : ‖w‖ ≤ ‖w - x‖ + ‖x‖ := by
    calc
      ‖w‖ = ‖(w - x) + x‖ := by rw [_root_.sub_add_cancel]
      _ ≤ ‖w - x‖ + ‖x‖ := norm_add_le _ _
  have hL : 0 ≤ L + 1 := by
    dsimp only [L]
    positivity
  have htriangle_mul :
      (L + 1) * ‖w‖ ≤ (L + 1) * (‖w - x‖ + ‖x‖) :=
    mul_le_mul_of_nonneg_left htriangle hL
  have hquad := quadratic_lower_bound_selection
    (gamma := -(L + 1)) (lam := lam) (t := ‖w - x‖) hlam
  have hreal :
      ‖w‖ + beta ≤
        l w + b + (1 / (2 * lam)) * ‖w - x‖ ^ 2 := by
    dsimp only [beta]
    nlinarith
  have hcoe :
      (((‖w‖ + beta : ℝ) : EReal) ≤
        ((l w + b + (1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) := by
    exact_mod_cast hreal
  calc
    (((1 * ‖w‖ + beta : ℝ) : EReal) ≤
        ((l w + b + (1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) := by
      simpa only [one_mul] using hcoe
    _ = ((l w + b : ℝ) : EReal) +
        (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal) := by
      rw [← EReal.coe_add]
    _ ≤ proximalObjectiveEReal f lam x w := by
      exact add_le_add (hminor w) le_rfl

/-- Every proper lower-semicontinuous convex extended-real function has a
level-coercive proximal objective at every positive parameter. -/
theorem isLevelCoercive_proximalObjectiveEReal
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    {lam : ℝ} (hlam : 0 < lam) (x : E) :
    IsLevelCoercive (proximalObjectiveEReal f lam x) := by
  obtain ⟨l, b, hminor⟩ :=
    exists_continuousAffineMinorant_of_convex_lsc_isProper
      hconv hlsc hproper
  exact isLevelCoercive_proximalObjectiveEReal_of_affineMinorant
    l b hminor hlam x

/-- The extended-real proximal mapping of a proper closed convex function is
nonempty at every positive parameter and every base point. -/
theorem proximalMappingEReal_nonempty
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    {lam : ℝ} (hlam : 0 < lam) (x : E) :
    (proximalMappingEReal f lam x).Nonempty := by
  have hproperObj := isProper_proximalObjectiveEReal hproper lam x
  have hlscObj := lowerSemicontinuous_proximalObjectiveEReal hlsc lam x
  have hlevel :=
    isLevelCoercive_proximalObjectiveEReal hconv hlsc hproper hlam x
  have hifc : IsInfCompact (proximalObjectiveEReal f lam x) :=
    isInfCompact_of_isLevelBounded_of_lsc hlscObj hlevel.isLevelBounded
  exact argmin_nonempty_of_isInfCompact_of_lsc_of_isProper
    hifc hlscObj hproperObj

/-- The extended-real Moreau envelope of a proper closed convex function is
finite everywhere at every positive parameter. -/
theorem moreauEnvelopeEReal_finite
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    {lam : ℝ} (hlam : 0 < lam) (x : E) :
    ⊥ < moreauEnvelopeEReal f lam x ∧
      moreauEnvelopeEReal f lam x < ⊤ := by
  rcases proximalMappingEReal_nonempty hconv hlsc hproper hlam x with ⟨w, hw⟩
  have hwEq : proximalObjectiveEReal f lam x w =
      moreauEnvelopeEReal f lam x :=
    mem_proximalMappingEReal_iff.mp hw
  have hproperObj := isProper_proximalObjectiveEReal hproper lam x
  constructor
  · rw [← hwEq]
    exact hproperObj.2 w
  · rcases hproperObj.1 with ⟨z, hz⟩
    have hwle : proximalObjectiveEReal f lam x w ≤
        proximalObjectiveEReal f lam x z := by
      rw [hwEq, moreauEnvelopeEReal]
      exact iInf_le _ z
    rw [← hwEq]
    exact hwle.trans_lt hz

/-- Every point selected by an extended-real proximal mapping lies in the
effective domain of the original function. -/
theorem mem_effectiveDomain_of_mem_proximalMappingEReal
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    {lam : ℝ} (hlam : 0 < lam) {x w : E}
    (hw : w ∈ proximalMappingEReal f lam x) :
    w ∈ effectiveDomain f := by
  have hwEq : proximalObjectiveEReal f lam x w =
      moreauEnvelopeEReal f lam x :=
    mem_proximalMappingEReal_iff.mp hw
  have henvTop := (moreauEnvelopeEReal_finite
    hconv hlsc hproper hlam x).2
  have hsum : proximalObjectiveEReal f lam x w ≠ ⊤ := by
    rw [hwEq]
    exact ne_of_lt henvTop
  have hpenBot :
      ((((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) ≠ ⊥ :=
    EReal.coe_ne_bot _
  have hfinite : f w ≠ ⊤ :=
    ((EReal.add_ne_top_iff_ne_top₂ (ne_of_gt (hproper.2 w)) hpenBot).mp hsum).1
  exact (mem_effectiveDomain_iff f w).2 (lt_top_iff_ne_top.mpr hfinite)

/-- The squared-distance identity at the midpoint of two vectors. -/
private theorem norm_midpoint_sub_sq_ereal (u v x : E) :
    ‖(2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v - x‖ ^ 2 =
      (2 : ℝ)⁻¹ * ‖u - x‖ ^ 2 + (2 : ℝ)⁻¹ * ‖v - x‖ ^ 2 -
        (4 : ℝ)⁻¹ * ‖u - v‖ ^ 2 := by
  have hvec :
      (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v - x =
        (2 : ℝ)⁻¹ • ((u - x) + (v - x)) := by
    module
  have hsub : (u - x) - (v - x) = u - v := by abel
  have hpara := parallelogram_law_with_norm ℝ (u - x) (v - x)
  rw [hsub] at hpara
  rw [hvec, norm_smul, Real.norm_eq_abs]
  norm_num
  nlinarith

/-- Any two proximal minimizers of a proper closed convex extended-real
function satisfy a global factor-two Lipschitz estimate. -/
theorem norm_sub_proximalEReal_le_two_mul
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    {lam : ℝ} (hlam : 0 < lam) {x y u v : E}
    (hu : u ∈ proximalMappingEReal f lam x)
    (hv : v ∈ proximalMappingEReal f lam y) :
    ‖u - v‖ ≤ 2 * ‖x - y‖ := by
  let a : ℝ := 1 / (2 * lam)
  let m : E := (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v
  let fu : ℝ := (f u).toReal
  let fv : ℝ := (f v).toReal
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have huDom :=
    mem_effectiveDomain_of_mem_proximalMappingEReal
      hconv hlsc hproper hlam hu
  have hvDom :=
    mem_effectiveDomain_of_mem_proximalMappingEReal
      hconv hlsc hproper hlam hv
  have hfuTop : f u ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff f u).mp huDom)
  have hfvTop : f v ≠ ⊤ := ne_of_lt ((mem_effectiveDomain_iff f v).mp hvDom)
  have hfuBot : f u ≠ ⊥ := ne_of_gt (hproper.2 u)
  have hfvBot : f v ≠ ⊥ := ne_of_gt (hproper.2 v)
  have hfu : f u = (fu : EReal) :=
    (EReal.coe_toReal hfuTop hfuBot).symm
  have hfv : f v = (fv : EReal) :=
    (EReal.coe_toReal hfvTop hfvBot).symm
  have huEpi : (u, fu) ∈ epigraph f := by
    rw [mem_epigraph_iff, hfu]
  have hvEpi : (v, fv) ∈ epigraph f := by
    rw [mem_epigraph_iff, hfv]
  have hmEpi := hconv huEpi hvEpi
    (show 0 ≤ (2 : ℝ)⁻¹ by norm_num)
    (show 0 ≤ (2 : ℝ)⁻¹ by norm_num)
    (show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 by norm_num)
  have hfmidE : f m ≤
      (((2 : ℝ)⁻¹ * fu + (2 : ℝ)⁻¹ * fv : ℝ) : EReal) := by
    simpa [m, mem_epigraph_iff, Prod.smul_mk, smul_eq_mul] using hmEpi
  have hfmTop : f m ≠ ⊤ := ne_of_lt <|
    hfmidE.trans_lt (EReal.coe_lt_top _)
  have hfmBot : f m ≠ ⊥ := ne_of_gt (hproper.2 m)
  let fm : ℝ := (f m).toReal
  have hfm : f m = (fm : EReal) :=
    (EReal.coe_toReal hfmTop hfmBot).symm
  have hfmid : fm ≤ (2 : ℝ)⁻¹ * fu + (2 : ℝ)⁻¹ * fv := by
    rw [hfm] at hfmidE
    exact EReal.coe_le_coe_iff.mp hfmidE
  have huLeE : proximalObjectiveEReal f lam x u ≤
      proximalObjectiveEReal f lam x m := by
    rw [mem_proximalMappingEReal_iff.mp hu, moreauEnvelopeEReal]
    exact iInf_le _ m
  have hvLeE : proximalObjectiveEReal f lam y v ≤
      proximalObjectiveEReal f lam y m := by
    rw [mem_proximalMappingEReal_iff.mp hv, moreauEnvelopeEReal]
    exact iInf_le _ m
  have huLe : fu + a * ‖u - x‖ ^ 2 ≤ fm + a * ‖m - x‖ ^ 2 := by
    simpa only [proximalObjectiveEReal, hfu, hfm, a, ← EReal.coe_add,
      EReal.coe_le_coe_iff] using huLeE
  have hvLe : fv + a * ‖v - y‖ ^ 2 ≤ fm + a * ‖m - y‖ ^ 2 := by
    simpa only [proximalObjectiveEReal, hfv, hfm, a, ← EReal.coe_add,
      EReal.coe_le_coe_iff] using hvLeE
  have hmid_x :
      fm + a * ‖m - x‖ ^ 2 ≤
        (2 : ℝ)⁻¹ * (fu + a * ‖u - x‖ ^ 2) +
          (2 : ℝ)⁻¹ * (fv + a * ‖v - x‖ ^ 2) -
            a * (4 : ℝ)⁻¹ * ‖u - v‖ ^ 2 := by
    rw [norm_midpoint_sub_sq_ereal u v x]
    nlinarith
  have hmid_y :
      fm + a * ‖m - y‖ ^ 2 ≤
        (2 : ℝ)⁻¹ * (fu + a * ‖u - y‖ ^ 2) +
          (2 : ℝ)⁻¹ * (fv + a * ‖v - y‖ ^ 2) -
            a * (4 : ℝ)⁻¹ * ‖u - v‖ ^ 2 := by
    rw [norm_midpoint_sub_sq_ereal u v y]
    nlinarith
  have hstrong_x :
      fu + a * ‖u - x‖ ^ 2 + a * (2 : ℝ)⁻¹ * ‖u - v‖ ^ 2 ≤
        fv + a * ‖v - x‖ ^ 2 := by
    nlinarith [huLe, hmid_x]
  have hstrong_y :
      fv + a * ‖v - y‖ ^ 2 + a * (2 : ℝ)⁻¹ * ‖u - v‖ ^ 2 ≤
        fu + a * ‖u - y‖ ^ 2 := by
    nlinarith [hvLe, hmid_y]
  have hsum :
      ‖u - v‖ ^ 2 ≤
        ‖v - x‖ ^ 2 - ‖u - x‖ ^ 2 +
          ‖u - y‖ ^ 2 - ‖v - y‖ ^ 2 := by
    nlinarith
  have hcross :
      ‖v - x‖ ^ 2 - ‖u - x‖ ^ 2 +
          ‖u - y‖ ^ 2 - ‖v - y‖ ^ 2 =
        2 * inner ℝ (u - v) (x - y) := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
    ring
  rw [hcross] at hsum
  have hinner : inner ℝ (u - v) (x - y) ≤ ‖u - v‖ * ‖x - y‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hsq : ‖u - v‖ ^ 2 ≤ 2 * (‖u - v‖ * ‖x - y‖) :=
    hsum.trans (by gcongr)
  by_cases huv : u = v
  · simp [huv]
  · have hnorm : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
    nlinarith [norm_nonneg (x - y)]

/-- An extended-real proximal mapping admits a selection with some finite
global Lipschitz constant. -/
def HasLipschitzProximalSelectionEReal (f : E → EReal) (lam : ℝ) : Prop :=
  ∃ K : NNReal, ∃ P : E → E, LipschitzWith K P ∧
    ∀ x : E, P x ∈ proximalMappingEReal f lam x

/-- Every proper lower-semicontinuous convex extended-real function admits a
globally `2`-Lipschitz proximal selection at every positive parameter. -/
theorem hasLipschitzProximalSelectionEReal
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f)
    {lam : ℝ} (hlam : 0 < lam) :
    HasLipschitzProximalSelectionEReal f lam := by
  classical
  choose P hP using fun x : E ↦
    proximalMappingEReal_nonempty hconv hlsc hproper hlam x
  refine ⟨2, P, ?_, hP⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using
    norm_sub_proximalEReal_le_two_mul
      hconv hlsc hproper hlam (hP x) (hP y)

end RW
