/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exact completions and counterexamples for Exercises 3.48–3.49

The literal nonconvex full-domain claim in 3.48 and the unconditional
extended-real sublinearity claim in 3.49(b) are false with the definitions
used by this project.  This file records formal counterexamples, the exact
corrected sublinearity theorem, and the lower-closure form of 3.49(c).
-/

import RockafellarWets.Chapter3.HomogeneousCompletion
import RockafellarWets.Chapter3.HorizonFunctionFormulas

open Set EReal Filter Topology Metric
open scoped BigOperators Pointwise

namespace RW

/-! ## Exercise 3.48: the nonconvex full-domain claim is false -/

/-- A continuous, finite-valued function on `ℝ²` whose values grow linearly
on the positive horizontal ray but stay equal to `1` along `(n,1)`.
Normalized points `(n,1)/n` approach the horizontal unit vector, producing a
horizon value strictly below the positive-hull value on that ray. -/
noncomputable def fullDomainPositiveHullCounterexample (p : ℝ × ℝ) : EReal :=
  ((1 + |p.1| * (p.2 - 1) ^ 2 : ℝ) : EReal)

theorem lowerSemicontinuous_fullDomainPositiveHullCounterexample :
    LowerSemicontinuous fullDomainPositiveHullCounterexample := by
  have hcont : Continuous (fun p : ℝ × ℝ ↦
      (1 + |p.1| * (p.2 - 1) ^ 2 : ℝ)) := by
    fun_prop
  exact (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

@[simp]
theorem fullDomainPositiveHullCounterexample_zero :
    fullDomainPositiveHullCounterexample (0, 0) = 1 := by
  simp [fullDomainPositiveHullCounterexample]

theorem effectiveDomain_fullDomainPositiveHullCounterexample :
    effectiveDomain fullDomainPositiveHullCounterexample = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  change fullDomainPositiveHullCounterexample p < ⊤
  exact EReal.coe_lt_top _

private theorem positiveHullFunction_counterexample_le_add
    {eps : ℝ} (heps : 0 < eps) :
    positiveHullFunction fullDomainPositiveHullCounterexample ((1 : ℝ), 0) ≤
      ((1 + eps : ℝ) : EReal) := by
  have hepi :
      (((eps⁻¹, 0), 1 + eps⁻¹) : (ℝ × ℝ) × ℝ) ∈
        epigraph fullDomainPositiveHullCounterexample := by
    rw [mem_epigraph_iff]
    simp [fullDomainPositiveHullCounterexample, abs_of_pos (inv_pos.mpr heps)]
  have hmem :
      ((((1 : ℝ), 0), 1 + eps) : (ℝ × ℝ) × ℝ) ∈
        positiveHull (epigraph fullDomainPositiveHullCounterexample) := by
    right
    refine ⟨eps, heps, ((eps⁻¹, 0), 1 + eps⁻¹), hepi, ?_⟩
    ext <;> simp [Prod.smul_mk, smul_eq_mul, heps.ne']
    field_simp [heps.ne']
    ring
  exact positiveHullFunction_le_of_mem_positiveHull_epigraph hmem

theorem positiveHullFunction_fullDomainCounterexample_horizontal :
    positiveHullFunction fullDomainPositiveHullCounterexample ((1 : ℝ), 0) = 1 := by
  apply le_antisymm
  · by_contra hnot
    have hlt : (1 : EReal) <
        positiveHullFunction fullDomainPositiveHullCounterexample ((1 : ℝ), 0) :=
      lt_of_not_ge hnot
    obtain ⟨r, h1r, hrpos⟩ := EReal.exists_between_coe_real hlt
    have h1rReal : 1 < r := by exact_mod_cast h1r
    let eps : ℝ := (r - 1) / 2
    have heps : 0 < eps := by dsimp [eps]; linarith
    have hle := positiveHullFunction_counterexample_le_add heps
    have hbelow : ((1 + eps : ℝ) : EReal) < (r : EReal) := by
      exact_mod_cast (show 1 + eps < r by dsimp [eps]; linarith)
    exact not_lt_of_ge hle (hbelow.trans hrpos)
  · refine le_iInf ?_
    intro a
    rcases a.property with hzero | ⟨c, hc, p, hp, hpEq⟩
    · have hbad : ((1 : ℝ), 0) = 0 := by
        simpa using congrArg Prod.fst hzero
      norm_num at hbad
    · rcases p with ⟨⟨u, v⟩, b⟩
      have hcu : c * u = 1 := by
        simpa [Prod.smul_mk, smul_eq_mul] using
          (congrArg (fun q : ((ℝ × ℝ) × ℝ) ↦ q.1.1) hpEq).symm
      have hcv : c * v = 0 := by
        simpa [Prod.smul_mk, smul_eq_mul] using
          congrArg (fun q : ((ℝ × ℝ) × ℝ) ↦ q.1.2) hpEq
      have hcb : c * b = (a : ℝ) := by
        simpa [Prod.smul_mk, smul_eq_mul] using (congrArg Prod.snd hpEq).symm
      have hu : u = c⁻¹ := by
        exact eq_inv_of_mul_eq_one_right hcu
      have hv : v = 0 := by
        exact (mul_eq_zero.mp hcv).resolve_left hc.ne'
      rw [mem_epigraph_iff] at hp
      have hb : 1 + c⁻¹ ≤ b := by
        rw [hu, hv] at hp
        have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
        have hp' : ((1 + c⁻¹ : ℝ) : EReal) ≤ (b : EReal) := by
          simpa [fullDomainPositiveHullCounterexample, abs_of_pos hcinv] using hp
        exact_mod_cast hp'
      have ha : 1 ≤ (a : ℝ) := by
        have hcInv : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
        nlinarith
      exact_mod_cast ha

theorem horizonFunction_fullDomainCounterexample_horizontal_le_zero :
    horizonFunction fullDomainPositiveHullCounterexample ((1 : ℝ), 0) ≤ 0 := by
  have hne : (epigraph fullDomainPositiveHullCounterexample).Nonempty := by
    refine ⟨(((0 : ℝ), 0), 1), ?_⟩
    rw [mem_epigraph_iff]
    simp
  apply (horizonFunction_le_iff_exists_expanding_epigraph_sequence hne).2
  let c : ℕ → ℝ := fun n ↦ (n : ℝ) + 1
  let u : ℕ → (ℝ × ℝ) × ℝ := fun n ↦
    (((1 : ℝ), (c n)⁻¹), (c n)⁻¹)
  have hc : Tendsto c atTop atTop := by
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n ↦ (c n)⁻¹) atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp hc
  refine ⟨c, u, hc, ?_, ?_, ?_⟩
  · exact (tendsto_const_nhds.prodMk_nhds hinv).prodMk_nhds hinv
  · intro n
    dsimp [c]
    positivity
  · intro n
    have hcn : 0 < c n := by dsimp [c]; positivity
    rw [mem_epigraph_iff]
    simp [u, fullDomainPositiveHullCounterexample, Prod.smul_mk,
      smul_eq_mul, hcn.ne']

/-- Formal counterexample to the literal nonconvex full-domain sufficient
case in Exercise 3.48.  All stated book-side hypotheses hold, but `pos f` is
not lower semicontinuous. -/
theorem not_lowerSemicontinuous_positiveHullFunction_fullDomainCounterexample :
    ¬ LowerSemicontinuous
      (positiveHullFunction fullDomainPositiveHullCounterexample) := by
  intro hposLsc
  have hle := positiveHullFunction_le_horizonFunction_of_lowerSemicontinuous
    lowerSemicontinuous_fullDomainPositiveHullCounterexample
    (by
      change (0 : EReal) < fullDomainPositiveHullCounterexample (0, 0)
      rw [fullDomainPositiveHullCounterexample_zero]
      norm_num)
    (by
      change fullDomainPositiveHullCounterexample (0, 0) < ⊤
      rw [fullDomainPositiveHullCounterexample_zero]
      exact EReal.coe_lt_top 1)
    hposLsc
  have hbad : (1 : EReal) ≤ 0 := by
    calc
      (1 : EReal) =
          positiveHullFunction fullDomainPositiveHullCounterexample ((1 : ℝ), 0) :=
        positiveHullFunction_fullDomainCounterexample_horizontal.symm
      _ ≤ horizonFunction fullDomainPositiveHullCounterexample ((1 : ℝ), 0) :=
        hle ((1 : ℝ), 0)
      _ ≤ 0 := horizonFunction_fullDomainCounterexample_horizontal_le_zero
  exact (by norm_num : ¬ (1 : EReal) ≤ 0) hbad

theorem exists_fullDomain_counterexample_to_lsc_positiveHull :
    ∃ f : (ℝ × ℝ) → EReal,
      LowerSemicontinuous f ∧
      f ≠ (fun _ ↦ ⊤) ∧
      (0 : EReal) < f 0 ∧
      effectiveDomain f = Set.univ ∧
      ¬ LowerSemicontinuous (positiveHullFunction f) := by
  refine ⟨fullDomainPositiveHullCounterexample,
    lowerSemicontinuous_fullDomainPositiveHullCounterexample, ?_, ?_,
    effectiveDomain_fullDomainPositiveHullCounterexample,
    not_lowerSemicontinuous_positiveHullFunction_fullDomainCounterexample⟩
  · intro h
    have := congrFun h (0, 0)
    rw [fullDomainPositiveHullCounterexample_zero] at this
    exact (EReal.coe_ne_top 1) this
  · norm_num [fullDomainPositiveHullCounterexample]

/-! ## Exercise 3.49(b): the mixed-infinity obstruction -/

/-- A positively homogeneous convex function whose value is `⊥` on the
nonnegative ray and `⊤` on the negative ray. -/
noncomputable def mixedInfinityRayFunction (x : ℝ) : EReal :=
  if 0 ≤ x then ⊥ else ⊤

theorem epigraph_mixedInfinityRayFunction :
    epigraph mixedInfinityRayFunction = Set.Ici (0 : ℝ) ×ˢ Set.univ := by
  ext p
  rcases p with ⟨x, a⟩
  by_cases hx : 0 ≤ x
  · simp [epigraph, mixedInfinityRayFunction, hx]
  · simp [epigraph, mixedInfinityRayFunction, hx]

theorem convex_epigraph_mixedInfinityRayFunction :
    Convex ℝ (epigraph mixedInfinityRayFunction) := by
  rw [epigraph_mixedInfinityRayFunction]
  exact (convex_Ici 0).prod convex_univ

theorem positivelyHomogeneous_mixedInfinityRayFunction :
    PositivelyHomogeneous mixedInfinityRayFunction := by
  constructor
  · simp [mixedInfinityRayFunction]
  · intro x c hc
    by_cases hx : 0 ≤ x
    · have hcx : 0 ≤ c * x := mul_nonneg hc.le hx
      simp only [mixedInfinityRayFunction, smul_eq_mul, if_pos hx, if_pos hcx]
      rw [EReal.coe_mul_bot_of_pos hc]
    · have hxneg : x < 0 := lt_of_not_ge hx
      have hcx : c * x < 0 := mul_neg_of_pos_of_neg hc hxneg
      have hcxnot : ¬ 0 ≤ c * x := not_le.mpr hcx
      simp only [mixedInfinityRayFunction, smul_eq_mul, if_neg hx,
        if_neg hcxnot]
      rw [EReal.coe_mul_top_of_pos hc]

theorem positiveHullFunction_mixedInfinityRayFunction :
    positiveHullFunction mixedInfinityRayFunction = mixedInfinityRayFunction :=
  positiveHullFunction_eq_self_of_positivelyHomogeneous
    positivelyHomogeneous_mixedInfinityRayFunction

/-- Formal obstruction to the literal statement of Exercise 3.49(b): convex
epigraph does not imply sublinearity when `⊥ + ⊤` is defined to be `⊥`.
Here subadditivity fails at `1 + (-2) = -1`. -/
theorem not_sublinear_positiveHullFunction_mixedInfinityRayFunction :
    ¬ Sublinear (positiveHullFunction mixedInfinityRayFunction) := by
  intro hsub
  have h := hsub.2 (1 : ℝ) (-2 : ℝ)
  rw [positiveHullFunction_mixedInfinityRayFunction] at h
  simp [mixedInfinityRayFunction] at h

/-- Exercise 3.49(b), exact version for the project's absorbing-`⊥`
arithmetic.  Excluding `⊥` values removes precisely the mixed `⊥/⊤`
obstruction exhibited above. -/
theorem sublinear_positiveHullFunction_of_convex_exact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → EReal} (hconv : Convex ℝ (epigraph f))
    (hbot : ∀ x, positiveHullFunction f x ≠ ⊥) :
    Sublinear (positiveHullFunction f) :=
  sublinear_positiveHullFunction_of_convex_of_ne_bot hconv hbot

/-! ## Exercise 3.49(c): lower closure before perspective -/

/-- `cl_f` is an epigraphical lower closure of `f`. -/
def IsLowerClosure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f cl_f : E → EReal) : Prop :=
  epigraph cl_f = closure (epigraph f)

/-- Compatibility form of Exercise 3.49(c), retaining an explicit properness
hypothesis on the chosen epigraphical lower closure.  The book-facing theorem
which discharges this hypothesis is in `LowerClosureProperness.lean`. -/
theorem sublinear_closedPerspectiveFunction_lowerClosure_of_isProper
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f cl_f : E → EReal} (hproper : IsProper f)
    (hconv : Convex ℝ (epigraph f))
    (hcl : IsLowerClosure f cl_f) (hclProper : IsProper cl_f) :
    Sublinear (closedPerspectiveFunction cl_f) := by
  have hclLsc : LowerSemicontinuous cl_f := by
    apply lowerSemicontinuous_of_isClosed_epigraph_ereal
    rw [hcl]
    exact isClosed_closure
  have hclConv : Convex ℝ (epigraph cl_f) := by
    rw [hcl]
    exact hconv.closure
  have hclFinite : ∃ x, cl_f x < ⊤ := by
    rcases hproper.1 with ⟨x, hxTop⟩
    have hxBot : f x ≠ ⊥ := ne_of_gt (hproper.2 x)
    let a : ℝ := (f x).toReal
    have hxf : f x = (a : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hxTop) hxBot).symm
    have hepi : (x, a) ∈ epigraph f := by
      rw [mem_epigraph_iff, hxf]
    have hclmem : (x, a) ∈ epigraph cl_f := by
      rw [hcl]
      exact subset_closure hepi
    refine ⟨x, ?_⟩
    have hclle : cl_f x ≤ (a : EReal) := by
      simpa [mem_epigraph_iff] using hclmem
    exact hclle.trans_lt (EReal.coe_lt_top a)
  have hclProper' : IsProper cl_f := ⟨hclFinite, hclProper.2⟩
  exact sublinear_closedPerspectiveFunction hclLsc hclProper' hclConv

end RW
