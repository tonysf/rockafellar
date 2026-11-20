/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Optimal values and solution sets under perturbations
-/

import Mathlib.Analysis.Convex.PathConnected
import RockafellarWets.Chapter3.Parametric
import RockafellarWets.Chapter7.ConditioningFunctions
import RockafellarWets.Chapter7.SharpAuxEpiDistance

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E : Type*}

/-- Minimizers over a set, excluding the identically infinite restricted problem. -/
def argminOn (f : E → EReal) (S : Set E) : Set E :=
  {x | x ∈ S ∧ f x = infimumOn f S ∧ infimumOn f S < ⊤}

variable [NormedAddCommGroup E] [ProperSpace E]

/-- The value estimates and the comparison point for each perturbed minimizer.
Only one reference minimizer must lie in the smaller ball. -/
theorem ball_minimizer_stability_witness {f g : E → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) (hp : IsProper f) (hq : IsProper g)
    {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) {r₀ r : ℝ≥0}
    (hA : (argmin f ∩ closedBall (0 : E) (r₀ : ℝ)).Nonempty) (hm₀ : -(r₀ : ℝ) ≤ m)
    (hclose : auxEpiDistance r f g < (r : ℝ) - r₀) :
    let d := auxEpiDistance r f g
    let B := closedBall (0 : E) (r : ℝ)
    ∃ k : ℝ, infimumOn g B = (k : EReal) ∧ |k - m| ≤ d ∧ (argminOn g B).Nonempty ∧
      ∀ x ∈ argminOn g B, ∃ y, dist x y ≤ d ∧ f y ≤ ((m + 2*d : ℝ) : EReal) := by
  obtain ⟨d₀, hfg, hgf⟩ := auxEpiAdmissible_at_distance hf hg hp.1 hq.1 (r := r)
  let d := auxEpiDistance r f g
  let B := closedBall (0 : E) (r : ℝ)
  have hd : 0 ≤ d := d₀
  change d < (r : ℝ) - r₀ at hclose
  obtain ⟨z, hzA, hz₀⟩ := hA
  have hzr : z ∈ B := closedBall_subset_closedBall (by linarith : (r₀ : ℝ) ≤ r) hz₀
  obtain ⟨w, hzw, hgw⟩ := hfg z hzr
  have hwr : w ∈ B := by
    calc
      dist w 0 ≤ dist w z + dist z 0 := dist_triangle _ _ _
      _ ≤ d + r₀ := add_le_add ((dist_comm w z).trans_le hzw) hz₀
      _ ≤ r := by linarith
  have hcut : -(r : ℝ) ≤ m := by linarith
  rw [hzA.1, hm, max_eq_left (EReal.coe_le_coe_iff.mpr hcut), ← EReal.coe_add] at hgw
  have hminU : infimumOn g B ≤ ((m+d : ℝ) : EReal) := (infimumOn_le hwr).trans hgw
  have hsource (x : E) (hx : x ∈ B) :
      ∃ y, dist x y ≤ d ∧ f y ≤ g x + (d : EReal) := by
    obtain ⟨y, hxy, hy⟩ := hgf x hx
    refine ⟨y, hxy, ?_⟩
    have hmfy : (m : EReal) ≤ f y := hm ▸ iInf_le f y
    have hgcut : ((-(r : ℝ) : ℝ) : EReal) ≤ g x := by
      by_contra! h
      rw [max_eq_right h.le, ← EReal.coe_add] at hy
      have hh := EReal.coe_le_coe_iff.mp (hmfy.trans hy)
      change m ≤ -(r : ℝ) + d at hh
      linarith
    simpa only [max_eq_left hgcut] using hy
  have hminL : ((m-d : ℝ) : EReal) ≤ infimumOn g B := by
    apply le_infimumOn
    intro x hx
    obtain ⟨y, _, hy⟩ := hsource x hx
    rw [EReal.coe_sub, EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))]
    exact (hm ▸ iInf_le f y).trans hy
  let k := (infimumOn g B).toReal
  have hk : infimumOn g B = (k : EReal) :=
    (EReal.coe_toReal (hminU.trans_lt (EReal.coe_lt_top _)).ne
      ((EReal.bot_lt_coe _).trans_le hminL).ne').symm
  have hL : m - d ≤ k := EReal.coe_le_coe_iff.mp (hminL.trans hk.le)
  have hU : k ≤ m + d := EReal.coe_le_coe_iff.mp (hk.ge.trans hminU)
  obtain ⟨v, hv, hmin⟩ := (hg.lowerSemicontinuousOn B).exists_isMinOn ⟨w, hwr⟩ (isCompact_closedBall _ _)
  refine ⟨k, hk, abs_le.mpr ⟨by linarith, by linarith⟩,
    ⟨v, hv, le_antisymm (le_infimumOn (isMinOn_iff.mp hmin)) (infimumOn_le hv),
      hk.trans_lt (EReal.coe_lt_top _)⟩, ?_⟩
  intro x hx
  obtain ⟨y, hxy, hy⟩ := hsource x hx.1
  rw [hx.2.1, hk, ← EReal.coe_add] at hy
  exact ⟨y, hxy, hy.trans (EReal.coe_le_coe_iff.mpr (by linarith))⟩

section FiniteDimensional

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [ProperSpace E] in
/-- For lsc, proper, level-bounded functions, the real parameter representing
the minimum in the solution estimates always exists. -/
theorem exists_real_minimum_of_levelBounded {f : E → EReal}
    (hf : LowerSemicontinuous f) (hp : IsProper f) (hb : IsLevelBounded f) :
    ∃ m : ℝ, (⨅ x, f x) = (m : EReal) := by
  obtain ⟨z, hz⟩ := argmin_nonempty_of_isInfCompact_of_lsc_of_isProper
    (isInfCompact_of_isLevelBounded_of_lsc hf hb) hf hp
  exact ⟨_, (EReal.coe_toReal hz.2.ne ((hp.2 z).trans_le hz.1.le).ne').symm⟩

omit [ProperSpace E] in
/-- **Theorem 7.64**. The optimal value on the ball is attained and differs
by at most the auxiliary distance. Each perturbed minimizer is within
`Ψ(d)` of some original minimizer. -/
theorem ball_minimizer_stability {f g : E → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) (hp : IsProper f) (hq : IsProper g)
    (hb : IsLevelBounded f) {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) {r₀ r : ℝ≥0}
    (hA : argmin f ⊆ closedBall (0 : E) (r₀ : ℝ)) (hm₀ : -(r₀ : ℝ) ≤ m)
    (hclose : auxEpiDistance r f g < (r : ℝ) - r₀) :
    let d := auxEpiDistance r f g
    let B := closedBall (0 : E) (r : ℝ)
    ∃ k : ℝ, infimumOn g B = (k : EReal) ∧ |k - m| ≤ d ∧ (argminOn g B).Nonempty ∧
      ∀ x ∈ argminOn g B, ∃ z ∈ argmin f, dist x z ≤ solutionRadius f m d := by
  have hc := isInfCompact_of_isLevelBounded_of_lsc hf hb
  have hne := argmin_nonempty_of_isInfCompact_of_lsc_of_isProper hc hf hp
  have hcomp := isCompact_argmin_of_isInfCompact_of_lsc_of_isProper hc hf hp
  obtain ⟨k, hk, hkm, hneB, hall⟩ := ball_minimizer_stability_witness hf hg hp hq hm
    (hne.mono fun _ h ↦ ⟨h, hA h⟩) hm₀ hclose
  refine ⟨k, hk, hkm, hneB, fun x hx ↦ ?_⟩
  obtain ⟨y, hxy, hy⟩ := hall x hx
  obtain ⟨z, hz, hdist⟩ := hcomp.exists_infDist_eq_dist hne y
  exact ⟨z, hz, (dist_triangle x y z).trans (add_le_add hxy
    (hdist.ge.trans (infDist_argmin_le_conditioningRadius hc hy)))⟩

omit [ProperSpace E] [FiniteDimensional ℝ E] in
/-- If every minimizer on the closed ball lies in its interior, convexity
ensures the restricted and unrestricted problems have the same solutions. -/
theorem argminOn_closedBall_eq_argmin_of_convex {g : E → EReal} (hg : Convex ℝ (epigraph g))
    {r k : ℝ} (hk : infimumOn g (closedBall 0 r) = (k : EReal))
    (hne : (argminOn g (closedBall 0 r)).Nonempty) (hinside : argminOn g (closedBall 0 r) ⊆ ball 0 r) :
    (⨅ x, g x) = (k : EReal) ∧ argminOn g (closedBall 0 r) = argmin g := by
  obtain ⟨v, hv⟩ := hne
  have hvk : g v = (k : EReal) := hv.2.1.trans hk
  have hvnorm : ‖v‖ < r := by simpa only [mem_ball, dist_zero_right] using hinside hv
  have hsub : levelSet g (k : EReal) ⊆ closedBall 0 r := by
    intro x hx
    by_contra hxout
    have hxr : r ≤ ‖x‖ := (lt_of_not_ge (by simpa only [mem_closedBall, dist_zero_right] using hxout)).le
    obtain ⟨y, hy, hyr⟩ := (convex_levelSet_of_convex_epigraph hg k).isPreconnected.intermediate_value
      (a := v) (b := x) hvk.le hx continuous_norm.continuousOn ⟨hvnorm.le, hxr⟩
    have hyB : y ∈ closedBall 0 r := by simp [mem_closedBall, hyr]
    have hyA : y ∈ argminOn g (closedBall 0 r) :=
      ⟨hyB, le_antisymm (hy.trans hk.ge) (infimumOn_le hyB), hk.trans_lt (EReal.coe_lt_top _)⟩
    have hcontra : ‖y‖ < r := by simpa using hinside hyA
    exact hcontra.ne hyr
  have hgl (x : E) : (k : EReal) ≤ g x := by
    by_contra! h
    exact h.not_ge (hk.ge.trans (infimumOn_le (hsub h.le)))
  have hmin : (⨅ x, g x) = (k : EReal) := le_antisymm ((iInf_le _ v).trans hvk.le) (le_iInf hgl)
  refine ⟨hmin, ext fun x ↦ ?_⟩
  constructor
  · intro hx
    exact ⟨hx.2.1.trans (hk.trans hmin.symm), hmin.trans_lt (EReal.coe_lt_top _)⟩
  · intro hx
    have hxk := hx.1.trans hmin
    exact ⟨hsub hxk.le, hxk.trans hk.symm, hk.trans_lt (EReal.coe_lt_top _)⟩

omit [ProperSpace E] in
/-- **Theorem 7.64**, global variant with the printed tighter cutoff. Only
the perturbed objective needs convex epigraph for this step. -/
theorem global_minimizer_stability_of_convex {f g : E → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) (hp : IsProper f) (hq : IsProper g)
    (hb : IsLevelBounded f) (hgc : Convex ℝ (epigraph g))
    {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) {r₀ r : ℝ≥0}
    (hA : argmin f ⊆ closedBall (0 : E) (r₀ : ℝ)) (hm₀ : -(r₀ : ℝ) ≤ m)
    (hclose : auxEpiDistance r f g < ((r : ℝ) - r₀)/2)
    (hgap : ((2 * auxEpiDistance r f g : ℝ) : EReal) < conditioningValue f m (((r : ℝ) - r₀)/2)) :
    let d := auxEpiDistance r f g
    ∃ k : ℝ, (⨅ x, g x) = (k : EReal) ∧ |k - m| ≤ d ∧ (argmin g).Nonempty ∧
      ∀ x ∈ argmin g, ∃ z ∈ argmin f, dist x z ≤ solutionRadius f m d := by
  let d := auxEpiDistance r f g
  have hd : 0 ≤ d := auxEpiDistance_nonneg hp.1 hq.1
  change d < ((r : ℝ) - r₀)/2 at hclose
  have hc := isInfCompact_of_isLevelBounded_of_lsc hf hb
  have hne := argmin_nonempty_of_isInfCompact_of_lsc_of_isProper hc hf hp
  obtain ⟨k, hk, hkm, hn, hall⟩ := ball_minimizer_stability hf hg hp hq hb hm hA hm₀
    (show d < (r : ℝ) - r₀ by linarith)
  have hrad : conditioningRadius f m (2*d) < ((r : ℝ) - r₀)/2 := by
    by_contra! h
    exact hgap.not_ge ((conditioningValue_le_iff_le_radius hf hc hne hm (mul_nonneg (by norm_num) hd) _).mpr h)
  have hinter : argminOn g (closedBall (0 : E) (r : ℝ)) ⊆ ball 0 (r : ℝ) := by
    intro x hx
    obtain ⟨z, hz, hdist⟩ := hall x hx
    have htri := (dist_triangle x z 0).trans (add_le_add hdist (hA hz))
    change dist x 0 ≤ (d + conditioningRadius f m (2*d)) + r₀ at htri
    change dist x 0 < (r : ℝ)
    linarith
  obtain ⟨hglob, harg⟩ := argminOn_closedBall_eq_argmin_of_convex hgc hk hn hinter
  exact ⟨k, hglob, hkm, harg ▸ hn, harg ▸ hall⟩

end FiniteDimensional
end RW
