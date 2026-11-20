/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Support functions of sets
-/

import RockafellarWets.Chapter3.HomogeneousOperations
import RockafellarWets.Chapter6.Polarity
import RockafellarWets.Chapter6.SupportingHalfspaces

open Set
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function, formula 8(10), with values in the extended reals. -/
noncomputable def supportFunction (D : Set E) (w : E) : EReal :=
  ⨆ v : D, (⟪(v : E), w⟫_ℝ : EReal)

/-- Vectors inducing linear minorants of an extended-real function. -/
def linearMinorantSet (h : E → EReal) : Set E :=
  {v | ∀ w, (⟪v,w⟫_ℝ : EReal) ≤ h w}

theorem inner_le_supportFunction {D : Set E} {v : E} (hv : v ∈ D) (w : E) :
    (⟪v,w⟫_ℝ : EReal) ≤ supportFunction D w :=
  le_iSup (fun u : D ↦ (⟪(u : E),w⟫_ℝ : EReal)) ⟨v,hv⟩

/-- Formula 8(11) identifies the halfspaces containing a set. -/
theorem supportFunction_le_iff (D : Set E) (w : E) (a : EReal) :
    supportFunction D w ≤ a ↔ ∀ v ∈ D, (⟪v,w⟫_ℝ : EReal) ≤ a := by
  simp [supportFunction]

@[simp] theorem supportFunction_empty (w : E) : supportFunction (∅ : Set E) w = ⊥ := by
  simp [supportFunction]

@[simp] theorem supportFunction_singleton (v w : E) : supportFunction {v} w = (⟪v,w⟫_ℝ : EReal) :=
  le_antisymm ((supportFunction_le_iff _ _ _).2 (by simp)) (inner_le_supportFunction (mem_singleton v) w)

theorem supportFunction_zero {D : Set E} (hD : D.Nonempty) : supportFunction D 0 = 0 := by
  obtain ⟨v,hv⟩ := hD
  exact le_antisymm ((supportFunction_le_iff _ _ _).2 (by simp)) (by simpa using inner_le_supportFunction hv 0)

theorem supportFunction_mono {C D : Set E} (h : C ⊆ D) : supportFunction C ≤ supportFunction D :=
  fun w ↦ (supportFunction_le_iff _ _ _).2 fun _ hv ↦ inner_le_supportFunction (h hv) w

/-- The first assertion of Theorem 8.24, including the empty set. -/
theorem sublinear_supportFunction (D : Set E) : Sublinear (supportFunction D) := by
  apply Sublinear.iSup
  intro v
  refine ⟨⟨by simp, fun x c _ ↦ ?_⟩, fun x y ↦ ?_⟩
  · simp [real_inner_smul_right, EReal.coe_mul]
  · simp [inner_add_right, EReal.coe_add]

theorem lowerSemicontinuous_supportFunction (D : Set E) : LowerSemicontinuous (supportFunction D) :=
  lowerSemicontinuous_iSup fun v : D ↦ (continuous_coe_real_ereal.comp (by fun_prop :
    Continuous (fun w : E ↦ ⟪(v : E),w⟫_ℝ))).lowerSemicontinuous

theorem isProper_supportFunction {D : Set E} (hD : D.Nonempty) : IsProper (supportFunction D) := by
  obtain ⟨v,hv⟩ := hD
  refine ⟨⟨0, by simp [supportFunction_zero ⟨v,hv⟩]⟩, fun w ↦ ?_⟩
  exact (EReal.bot_lt_coe _).trans_le (inner_le_supportFunction hv w)

theorem isClosed_linearMinorantSet (h : E → EReal) : IsClosed (linearMinorantSet h) := by
  rw [show linearMinorantSet h = ⋂ w, {v : E | (⟪v,w⟫_ℝ : EReal) ≤ h w} by ext; simp [linearMinorantSet]]
  exact isClosed_iInter fun w ↦ isClosed_le (continuous_coe_real_ereal.comp (by fun_prop)) continuous_const

theorem convex_linearMinorantSet (h : E → EReal) : Convex ℝ (linearMinorantSet h) := by
  intro x hx y hy a b ha hb hab w
  cases hval : h w with
  | bot => exact False.elim ((EReal.coe_ne_bot _ ) (le_bot_iff.mp ((hx w).trans_eq hval)))
  | coe c =>
    have h₁ := EReal.coe_le_coe_iff.1 ((hx w).trans_eq hval)
    have h₂ := EReal.coe_le_coe_iff.1 ((hy w).trans_eq hval)
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, EReal.coe_le_coe_iff]
    nlinarith [mul_le_mul_of_nonneg_left h₁ ha, mul_le_mul_of_nonneg_left h₂ hb, congrArg (fun t : ℝ ↦ t*c) hab]
  | top => exact le_top

/-- The support function depends precisely on the closed convex hull
(Theorem 8.24). -/
theorem linearMinorantSet_supportFunction [FiniteDimensional ℝ E] (D : Set E) :
    linearMinorantSet (supportFunction D) = closure (convexHull ℝ D) := by
  refine le_antisymm ?_ (closure_minimal (convexHull_min (fun v hv w ↦ inner_le_supportFunction hv w)
    (convex_linearMinorantSet _)) (isClosed_linearMinorantSet _))
  intro z hz
  rcases D.eq_empty_or_nonempty with rfl | hD
  · exact False.elim ((EReal.coe_ne_bot _) (le_bot_iff.mp ((hz 0).trans_eq (supportFunction_empty _))))
  by_contra hnot
  obtain ⟨x,v,hs,hzout⟩ := exists_supportingHalfspace_separating
    (hD.mono ((subset_convexHull ℝ D).trans subset_closure)) isClosed_closure (convex_convexHull ℝ D).closure hnot
  have hupper : supportFunction D v ≤ (⟪x,v⟫_ℝ : EReal) := by
    apply (supportFunction_le_iff _ _ _).2
    intro w hw
    have h := hs.subset ((subset_convexHull ℝ D).trans subset_closure hw)
    simpa [mem_supportingHalfspace, inner_sub_right, real_inner_comm v, sub_nonpos] using h
  have h := EReal.coe_le_coe_iff.1 ((hz v).trans hupper)
  exact hzout (by simpa [mem_supportingHalfspace, inner_sub_right, real_inner_comm v, sub_nonpos] using h)

theorem supportFunction_closure_convexHull [FiniteDimensional ℝ E] (D : Set E) :
    supportFunction (closure (convexHull ℝ D)) = supportFunction D := by
  apply le_antisymm _ (supportFunction_mono ((subset_convexHull ℝ D).trans subset_closure))
  intro w
  exact (supportFunction_le_iff _ _ _).2 fun v hv ↦ ((linearMinorantSet_supportFunction D).symm ▸ hv :
    v ∈ linearMinorantSet (supportFunction D)) w

/-- The support function of a finitely generated convex hull is the attained
maximum of the generator pairings. -/
theorem supportFunction_convexHull_finset [FiniteDimensional ℝ E] (s : Finset E) (hs : s.Nonempty) (w : E) :
    supportFunction (convexHull ℝ (s : Set E)) w = (s.sup' hs (fun v ↦ ⟪v,w⟫_ℝ) : ℝ) := by
  have hc := s.finite_toSet.isCompact_convexHull.isClosed.closure_eq
  have he := supportFunction_closure_convexHull (s : Set E)
  rw [hc] at he
  rw [he]
  obtain ⟨v,hv,hmax⟩ := Finset.exists_mem_eq_sup' hs (fun u ↦ ⟪u,w⟫_ℝ)
  refine le_antisymm ((supportFunction_le_iff _ _ _).2 fun u hu ↦ ?_) ?_
  · exact EReal.coe_le_coe_iff.2 (Finset.le_sup' (fun z ↦ ⟪z,w⟫_ℝ) hu)
  · rw [hmax]
    exact inner_le_supportFunction (D := (s : Set E)) hv w

/-- **Example 8.28.** The support of any cone is the indicator of its polar. -/
theorem supportFunction_cone {K : Set E} (hK : IsCone K) :
    supportFunction K = indicatorVA (polarCone K) := by
  funext w
  by_cases hw : w ∈ polarCone K
  · rw [indicatorVA_apply_mem hw]
    exact le_antisymm ((supportFunction_le_iff _ _ _).2 (fun v hv ↦ by simpa [real_inner_comm] using hw v hv))
      (by simpa using inner_le_supportFunction hK.1 w)
  · rw [indicatorVA_apply_not_mem hw]
    by_contra hfin
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.2 hfin)
    simp only [mem_polarCone, not_forall, not_le] at hw
    obtain ⟨v,hv,hpos⟩ := hw
    let t := (|r|+1)/⟪w,v⟫_ℝ
    have ht : 0 < t := by dsimp [t]; positivity
    have h := EReal.coe_lt_coe_iff.1 ((inner_le_supportFunction (hK.2 hv ht) w).trans_lt hr)
    rw [real_inner_smul_left, real_inner_comm w v, show t*⟪w,v⟫_ℝ = |r|+1 by dsimp [t]; field_simp] at h
    linarith [le_abs_self r]

/-- The support function of the full space is the indicator of the origin. -/
theorem supportFunction_univ : supportFunction (univ : Set E) = indicatorVA {0} := by
  rw [supportFunction_cone (show IsCone (univ : Set E) from ⟨mem_univ _,fun {_} _ {_} _ ↦ mem_univ _⟩),polarCone_univ]

end RW
