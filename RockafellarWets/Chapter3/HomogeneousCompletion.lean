/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Completion lemmas for homogeneous functions

This file collects the remaining operation and closure statements from
Exercises 3.19, 3.40, 3.48, and 3.49.
-/

import RockafellarWets.Chapter3.HomogeneousOperations
import RockafellarWets.Chapter3.PositiveHulls
import RockafellarWets.Chapter3.EpiAddition
import RockafellarWets.Chapter3.HorizonAddition

open Set EReal Topology
open scoped Pointwise

namespace RW

section ConeClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closure of a cone is a cone. -/
theorem IsCone.closure {K : Set E} (hK : IsCone K) :
    IsCone (closure K) := by
  refine ⟨subset_closure hK.1, ?_⟩
  intro x hx c hc
  exact map_mem_closure (continuous_const.smul continuous_id) hx fun y hy ↦
    hK.2 hy hc

/-- Exercise 3.19: taking a lower closure does not change the horizon
function. Here a lower closure is specified epigraphically, which avoids
introducing a second envelope operator. -/
theorem horizonFunction_lowerClosure_eq
    {f g : E → EReal} (hcl : epigraph g = closure (epigraph f)) :
    horizonFunction g = horizonFunction f := by
  have hcone :
      horizonCone (epigraph g) = horizonCone (epigraph f) := by
    rw [hcl, horizonCone_closure]
  unfold horizonFunction
  rw [hcone]

/-- Exercise 3.19: the horizon function of a positively homogeneous function
is its lower closure. -/
theorem horizonFunction_eq_lowerClosure_of_positivelyHomogeneous
    {f g : E → EReal} (hf : PositivelyHomogeneous f)
    (hcl : epigraph g = closure (epigraph f)) :
    horizonFunction f = g := by
  have hgcone : IsCone (epigraph g) := by
    rw [hcl]
    exact (isCone_epigraph_of_positivelyHomogeneous hf).closure
  have hglsc : LowerSemicontinuous g := by
    apply lowerSemicontinuous_of_isClosed_epigraph_ereal
    rw [hcl]
    exact isClosed_closure
  calc
    horizonFunction f = horizonFunction g :=
      (horizonFunction_lowerClosure_eq hcl).symm
    _ = g :=
      horizonFunction_eq_self_of_lowerSemicontinuous_of_positivelyHomogeneous
        hglsc (positivelyHomogeneous_of_isCone_epigraph hgcone)

end ConeClosure

section HomogeneousOperations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exercise 3.40(a): a nonempty union of cones is a cone. The nonemptiness
assumption is necessary because the union of an empty family is empty. -/
theorem isCone_iUnion {ι : Type*} [Nonempty ι] {K : ι → Set E}
    (hK : ∀ i, IsCone (K i)) :
    IsCone (⋃ i, K i) := by
  classical
  refine ⟨?_, ?_⟩
  · exact mem_iUnion.2 ⟨Classical.choice inferInstance, (hK _).1⟩
  · intro x hx c hc
    rcases mem_iUnion.1 hx with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, (hK i).2 hi hc⟩

/-- Multiplication by a positive real coefficient commutes with arbitrary
infima in `EReal`. -/
private theorem coe_mul_iInf {ι : Sort*} (a : ι → EReal) {c : ℝ} (hc : 0 < c) :
    (c : EReal) * (⨅ i, a i) = ⨅ i, (c : EReal) * a i := by
  apply le_antisymm
  · refine le_iInf fun i ↦ ?_
    gcongr
    exact iInf_le a i
  · have hinv :
        ((c⁻¹ : ℝ) : EReal) * (⨅ i, (c : EReal) * a i) ≤ ⨅ i, a i := by
      refine le_iInf fun i ↦ ?_
      calc
        ((c⁻¹ : ℝ) : EReal) * (⨅ j, (c : EReal) * a j)
            ≤ ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * a i) := by
              gcongr
              exact iInf_le (fun j ↦ (c : EReal) * a j) i
        _ = a i := by
          rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hc.ne', EReal.coe_one,
            one_mul]
    have hmul :
        (c : EReal) * (((c⁻¹ : ℝ) : EReal) *
          (⨅ i, (c : EReal) * a i)) ≤
        (c : EReal) * (⨅ i, a i) := by
      gcongr
    simpa [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne'] using hmul

private theorem bot_lt_coe_mul_of_pos {a : EReal} {c : ℝ}
    (hc : 0 < c) (ha : ⊥ < a) :
    ⊥ < (c : EReal) * a := by
  cases a using EReal.rec with
  | bot => simp at ha
  | coe r => simp [← EReal.coe_mul]
  | top => simp [EReal.coe_mul_top_of_pos hc]

/-- Exercise 3.40(e): nonempty pointwise infima of positively homogeneous
functions are positively homogeneous. The family must be nonempty because the
empty infimum is the constant `⊤` function. -/
theorem PositivelyHomogeneous.iInf {ι : Sort*} [Nonempty ι] {h : ι → E → EReal}
    (hh : ∀ i, PositivelyHomogeneous (h i)) :
    PositivelyHomogeneous (fun x ↦ ⨅ i, h i x) := by
  refine ⟨?_, ?_⟩
  · let i₀ : ι := Classical.choice inferInstance
    exact lt_of_le_of_lt (iInf_le (fun i ↦ h i 0) i₀) (hh i₀).1
  · intro x c hc
    calc
      (⨅ i, h i (c • x)) = ⨅ i, (c : EReal) * h i x := by
        congr 1
        funext i
        exact (hh i).2 hc
      _ = (c : EReal) * (⨅ i, h i x) := (coe_mul_iInf _ hc).symm

/-- Binary pointwise infima preserve positive homogeneity. -/
theorem PositivelyHomogeneous.inf {h₁ h₂ : E → EReal}
    (hh₁ : PositivelyHomogeneous h₁) (hh₂ : PositivelyHomogeneous h₂) :
    PositivelyHomogeneous (fun x ↦ h₁ x ⊓ h₂ x) := by
  have hInf : PositivelyHomogeneous
      (fun x ↦ ⨅ b : Bool, cond b (h₁ x) (h₂ x)) :=
    PositivelyHomogeneous.iInf (h := fun b x ↦ cond b (h₁ x) (h₂ x)) <| by
      intro b
      cases b
      · simpa using hh₂
      · simpa using hh₁
  simpa [inf_eq_iInf] using hInf

/-- Exercise 3.40(f): epi-addition (infimal convolution) preserves positive
homogeneity. -/
theorem PositivelyHomogeneous.epiSum {h₁ h₂ : E → EReal}
    (hh₁ : PositivelyHomogeneous h₁) (hh₂ : PositivelyHomogeneous h₂) :
    PositivelyHomogeneous (RW.epiSum h₁ h₂) := by
  refine ⟨?_, ?_⟩
  · have hle :
        RW.epiSum h₁ h₂ 0 ≤ h₁ 0 + h₂ 0 := by
      exact iInf_le_of_le 0 (by simp)
    exact lt_of_le_of_lt hle
      (EReal.add_lt_top (ne_of_lt hh₁.1) (ne_of_lt hh₂.1))
  · intro x c hc
    have hsurj : Function.Surjective (fun w : E ↦ c • w) := by
      intro w
      refine ⟨c⁻¹ • w, ?_⟩
      simp [smul_smul, mul_inv_cancel₀ hc.ne']
    rw [epiSum_apply, epiSum_apply, ← hsurj.iInf_comp]
    calc
      (⨅ w : E, h₁ (c • x - c • w) + h₂ (c • w))
          = ⨅ w : E, (c : EReal) * (h₁ (x - w) + h₂ w) := by
              congr 1
              funext w
              rw [← smul_sub, hh₁.2 hc, hh₂.2 hc]
              exact (EReal.left_distrib_of_nonneg_of_ne_top
                (by exact_mod_cast hc.le) (EReal.coe_ne_top c)
                (h₁ (x - w)) (h₂ w)).symm
      _ = (c : EReal) * (⨅ w : E, h₁ (x - w) + h₂ w) :=
        (coe_mul_iInf _ hc).symm

end HomogeneousOperations

section PositiveHulls

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Reverse epigraph inclusion is pointwise order. -/
private theorem le_of_epigraph_subset {f g : E → EReal}
    (hfg : epigraph g ⊆ epigraph f) :
    f ≤ g := by
  intro x
  by_contra hle
  have hlt : g x < f x := lt_of_not_ge hle
  obtain ⟨a, hga, haf⟩ := EReal.exists_between_coe_real hlt
  have ha : (x, a) ∈ epigraph g := by
    rw [mem_epigraph_iff]
    exact hga.le
  have := hfg ha
  rw [mem_epigraph_iff] at this
  exact not_le_of_gt haf this

/-- Once the positive hull is lower semicontinuous, the comparison
`pos f ≤ f∞` in Exercise 3.48 is automatic. -/
theorem positiveHullFunction_le_horizonFunction_of_lowerSemicontinuous
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (h0pos : (0 : EReal) < f 0)
    (h0fin : f 0 < ⊤)
    (hposlsc : LowerSemicontinuous (positiveHullFunction f)) :
    positiveHullFunction f ≤ horizonFunction f := by
  have hclosed :
      IsClosed (epigraph (positiveHullFunction f)) :=
    isClosed_epigraph_of_lsc_ereal _ hposlsc
  have heq :=
    closure_epigraph_positiveHullFunction_eq_union_horizonFunction
      (f := f) hlsc h0pos h0fin
  rw [hclosed.closure_eq] at heq
  apply le_of_epigraph_subset
  exact Set.union_eq_left.mp heq.symm

/-- Exercise 3.48(b), coercive sufficient case. Coercivity alone forces the
horizon value to be `⊤` away from the origin and `0` at the origin, hence
`pos f ≤ f∞`. -/
theorem positiveHullFunction_le_horizonFunction_of_isCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hcoercive : IsCoercive f) :
    positiveHullFunction f ≤ horizonFunction f := by
  intro x
  by_cases hx : x = 0
  · subst hx
    have hnonneg : (0 : EReal) ≤ horizonFunction f 0 := by
      obtain ⟨β, hminor⟩ := hcoercive 1 zero_lt_one
      simpa using hminor.le_horizonFunction (0 : E)
    have hzero : horizonFunction f 0 = 0 :=
      le_antisymm (positivelyHomogeneous_horizonFunction f).map_zero_le_zero hnonneg
    rw [hzero]
    exact (positivelyHomogeneous_positiveHullFunction f).map_zero_le_zero
  · have htop : horizonFunction f x = ⊤ := by
      rw [EReal.eq_top_iff_forall_lt]
      intro r
      let γ : ℝ := (|r| + 1) / ‖x‖
      have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hγ : 0 < γ := div_pos (by positivity) hxnorm
      obtain ⟨β, hminor⟩ := hcoercive γ hγ
      have hlower :
          ((γ * ‖x‖ : ℝ) : EReal) ≤ horizonFunction f x :=
        hminor.le_horizonFunction x
      have hrγ : r < γ * ‖x‖ := by
        dsimp [γ]
        field_simp [hxnorm.ne']
        linarith [le_abs_self r]
      have hrγ' :
          (r : EReal) < ((γ * ‖x‖ : ℝ) : EReal) := by
        exact_mod_cast hrγ
      exact hrγ'.trans_le hlower
    rw [htop]
    exact le_top

/-- Exercise 3.48(b), coercive lower-semicontinuity consequence. -/
theorem lowerSemicontinuous_positiveHullFunction_of_isCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hcoercive : IsCoercive f)
    (h0pos : (0 : EReal) < f 0) (h0fin : f 0 < ⊤) :
    LowerSemicontinuous (positiveHullFunction f) :=
  lowerSemicontinuous_positiveHullFunction_of_le_horizonFunction
    hlsc h0pos h0fin
    (positiveHullFunction_le_horizonFunction_of_isCoercive hcoercive)

/-- Exercise 3.48(b), full-domain sufficient case. A proper closed convex
function with full effective domain and positive value at the origin has a
finite continuous positive hull. -/
theorem lowerSemicontinuous_positiveHullFunction_of_effectiveDomain_eq_univ
    [FiniteDimensional ℝ E] [CompleteSpace E] {f : E → EReal}
    (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) (hdom : effectiveDomain f = Set.univ)
    (h0pos : (0 : EReal) < f 0) :
    LowerSemicontinuous (positiveHullFunction f) := by
  have htop : ∀ x, f x ≠ ⊤ := by
    intro x
    exact ne_of_lt <| by
      rw [← mem_effectiveDomain_iff, hdom]
      exact Set.mem_univ x
  have hcoe : ∀ x, (((f x).toReal : ℝ) : EReal) = f x := fun x ↦
    EReal.coe_toReal (htop x) (ne_of_gt (hproper.2 x))
  let fr : E → ℝ := fun x ↦ (f x).toReal
  have hfr : (fun x ↦ ((fr x : ℝ) : EReal)) = f := by
    funext x
    exact hcoe x
  have hconvfr : Convex ℝ (epigraph (fun x ↦ ((fr x : ℝ) : EReal))) := by
    rw [hfr]
    exact hconv
  have hlscfr : LowerSemicontinuous (fun x ↦ ((fr x : ℝ) : EReal)) := by
    rw [hfr]
    exact hlsc
  have hfr0 : 0 < fr 0 := by
    have : (0 : EReal) < ((fr 0 : ℝ) : EReal) := by
      rw [congrFun hfr 0]
      exact h0pos
    exact_mod_cast this
  obtain ⟨l, b, hb, hminor⟩ :=
    exists_affine_minorant_gt_of_lt_of_convex_lsc
      (f := fr) hconvfr hlscfr hfr0
  have hbpos : 0 < b := by simpa using hb
  let q : E → EReal := fun x ↦ (l x : EReal)
  have hqph : PositivelyHomogeneous q := by
    refine ⟨by simp [q], ?_⟩
    intro x c hc
    simp [q, ← EReal.coe_mul]
  have hqf : q ≤ f := by
    intro x
    have hl : l x ≤ fr x := le_trans (le_add_of_nonneg_right hbpos.le) (hminor x)
    change (l x : EReal) ≤ f x
    rw [← hfr]
    change (l x : EReal) ≤ (fr x : EReal)
    exact_mod_cast hl
  have hqpos : q ≤ positiveHullFunction f :=
    le_positiveHullFunction_of_positivelyHomogeneous_of_le hqph hqf
  have hposbot : ∀ x, positiveHullFunction f x ≠ ⊥ := by
    intro x hx
    have hle := hqpos x
    rw [hx] at hle
    exact (not_le_of_gt (EReal.bot_lt_coe (l x))) hle
  have hpostop : ∀ x, positiveHullFunction f x ≠ ⊤ := by
    intro x hx
    have hle := positiveHullFunction_le_apply f x
    rw [hx] at hle
    exact (htop x) (top_le_iff.mp hle)
  let pr : E → ℝ := fun x ↦ (positiveHullFunction f x).toReal
  have hpr : (fun x ↦ ((pr x : ℝ) : EReal)) = positiveHullFunction f := by
    funext x
    exact EReal.coe_toReal (hpostop x) (hposbot x)
  have hconvpr : Convex ℝ (epigraph (fun x ↦ ((pr x : ℝ) : EReal))) := by
    rw [hpr]
    exact convex_epigraph_positiveHullFunction hconv
  have hconvOn : ConvexOn ℝ Set.univ pr := by
    rw [← convex_epigraph_iff_convexOn pr Set.univ convex_univ]
    simpa only [epigraph, mem_setOf_eq, EReal.coe_le_coe_iff, Set.mem_univ,
      true_and] using hconvpr
  have hcont : Continuous pr := by
    exact continuousOn_univ.mp <|
      continuous_of_convexOn_open isOpen_univ convex_univ hconvOn
  have hlscpr : LowerSemicontinuous (fun x ↦ ((pr x : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  rwa [hpr] at hlscpr

/-- Exercise 3.48(b), full-domain comparison `pos f ≤ f∞`. -/
theorem positiveHullFunction_le_horizonFunction_of_effectiveDomain_eq_univ
    [FiniteDimensional ℝ E] [CompleteSpace E] {f : E → EReal}
    (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) (hdom : effectiveDomain f = Set.univ)
    (h0pos : (0 : EReal) < f 0) (h0fin : f 0 < ⊤) :
    positiveHullFunction f ≤ horizonFunction f :=
  positiveHullFunction_le_horizonFunction_of_lowerSemicontinuous
    hlsc h0pos h0fin
    (lowerSemicontinuous_positiveHullFunction_of_effectiveDomain_eq_univ
      hconv hlsc hproper hdom h0pos)

/-- Exercise 3.49(b), in the `EReal`-safe form: the positive hull of a convex
function is sublinear whenever its positive hull has no `⊥` values. -/
theorem sublinear_positiveHullFunction_of_convex_of_ne_bot
    {f : E → EReal} (hconv : Convex ℝ (epigraph f))
    (hbot : ∀ x, positiveHullFunction f x ≠ ⊥) :
    Sublinear (positiveHullFunction f) :=
  sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_ne_bot
    (positivelyHomogeneous_positiveHullFunction f)
    (convex_epigraph_positiveHullFunction hconv) hbot

/-- Nonnegative convex functions give an unconditional `EReal`-safe instance
of Exercise 3.49(b). -/
theorem sublinear_positiveHullFunction_of_convex_of_nonneg
    {f : E → EReal} (hconv : Convex ℝ (epigraph f))
    (hnonneg : ∀ x, 0 ≤ f x) :
    Sublinear (positiveHullFunction f) :=
  sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_nonneg
    (positivelyHomogeneous_positiveHullFunction f)
    (convex_epigraph_positiveHullFunction hconv)
    (nonneg_positiveHullFunction_of_nonneg hnonneg)

/-- The perspective of a proper function is proper. -/
theorem isProper_perspectiveFunction {f : E → EReal} (hf : IsProper f) :
    IsProper (perspectiveFunction f) := by
  constructor
  · rcases hf.1 with ⟨x, hx⟩
    refine ⟨(1, x), ?_⟩
    simpa [perspectiveFunction] using hx
  · rintro ⟨lam, x⟩
    by_cases hlam : 0 < lam
    · simp only [perspectiveFunction, hlam, ↓reduceDIte]
      exact bot_lt_coe_mul_of_pos hlam (hf.2 _)
    · by_cases h0 : lam = 0
      · subst h0
        by_cases hx : x = 0
        · simp [perspectiveFunction, hx]
        · simp [perspectiveFunction, hx]
      · simp [perspectiveFunction, hlam, h0]

/-- Exercise 3.49(c): the perspective of a proper convex function is
sublinear. -/
theorem sublinear_perspectiveFunction {f : E → EReal}
    (hproper : IsProper f) (hconv : Convex ℝ (epigraph f)) :
    Sublinear (perspectiveFunction f) := by
  apply (sublinear_iff_convex_isCone_epigraph_of_isProper
    (isProper_perspectiveFunction hproper)).2
  exact ⟨convex_epigraph_perspectiveFunction hproper hconv,
    isCone_epigraph_of_positivelyHomogeneous
      (positivelyHomogeneous_perspectiveFunction hproper)⟩

/-- Exercise 3.49(c): the closed perspective is sublinear as well as lower
semicontinuous. -/
theorem sublinear_closedPerspectiveFunction [FiniteDimensional ℝ E]
    {f : E → EReal} (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) (hconv : Convex ℝ (epigraph f)) :
    Sublinear (closedPerspectiveFunction f) := by
  have hconvClosed : Convex ℝ (epigraph (closedPerspectiveFunction f)) := by
    rw [← closure_epigraph_perspectiveFunction_eq_epigraph_closedPerspectiveFunction
      hlsc hproper]
    exact (convex_epigraph_perspectiveFunction hproper hconv).closure
  have hconeClosed : IsCone (epigraph (closedPerspectiveFunction f)) := by
    rw [← closure_epigraph_perspectiveFunction_eq_epigraph_closedPerspectiveFunction
      hlsc hproper]
    exact (isCone_epigraph_of_positivelyHomogeneous
      (positivelyHomogeneous_perspectiveFunction hproper)).closure
  refine sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_ne_bot
    (positivelyHomogeneous_of_isCone_epigraph hconeClosed) hconvClosed ?_
  intro p
  rcases p with ⟨lam, x⟩
  by_cases hlam : 0 < lam
  · simp only [closedPerspectiveFunction, hlam, ↓reduceDIte]
    exact ne_of_gt <| bot_lt_coe_mul_of_pos hlam (hproper.2 _)
  · by_cases h0 : lam = 0
    · subst h0
      simp only [closedPerspectiveFunction, lt_self_iff_false, ↓reduceDIte]
      exact ne_of_gt (bot_lt_horizonFunction_of_convex hconv hlsc hproper x)
    · simp [closedPerspectiveFunction, hlam, h0]

end PositiveHulls

end RW
