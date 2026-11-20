/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The inverse gradient in the classical Legendre transform
-/

import RockafellarWets.Chapter11.DualMinimizationGrowth
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

open Filter Set Topology InnerProductSpace
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A globally differentiable mapping with positive definite derivative
quadratic forms is injective. The proof integrates strict monotonicity along
each line segment. -/
theorem injective_of_fderiv_inner_pos {G : E → E} (hG : Differentiable ℝ G)
    (hpos : ∀ x w, w ≠ 0 → 0 < ⟪fderiv ℝ G x w,w⟫_ℝ) : Function.Injective G := by
  intro x y hxy
  by_contra hne
  let w := y-x
  have hw : w ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let φ : ℝ → ℝ := fun t ↦ ⟪w,G (x+t • w)⟫_ℝ
  have hd (t : ℝ) : HasDerivAt φ ⟪w,fderiv ℝ G (x+t • w) w⟫_ℝ t := by
    exact (innerSL ℝ w).hasFDerivAt.comp_hasDerivAt t
      ((hG _).hasFDerivAt.comp_hasDerivAt t (by simpa only [id_eq,one_smul] using (((hasDerivAt_id t).smul_const w).const_add x)))
  have hm : StrictMono φ := strictMono_of_hasDerivAt_pos hd fun t ↦ by
    rw [real_inner_comm]
    exact hpos _ w hw
  have hh := hm (show (0:ℝ)<1 by norm_num)
  simp only [φ,zero_smul,add_zero,one_smul,w,add_sub_cancel,← hxy,lt_self_iff_false] at hh

/-- The gradient of a twice continuously differentiable function is `C¹`. -/
theorem contDiff_one_gradient {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (gradient f) := by
  let L : StrongDual ℝ E →L[ℝ] E := (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact L.contDiff.comp (hf.fderiv_right (m := 1) (by norm_num))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Finite-valued functions are proper in the extended-real encoding. -/
theorem isProper_coe_real (f : E → ℝ) : IsProper (fun x ↦ (f x:EReal)) :=
  ⟨⟨0,EReal.coe_lt_top _⟩,fun _ ↦ EReal.bot_lt_coe _⟩

/-- A differentiable convex function has its gradient as its only subgradient. -/
theorem subdifferential_coe_real_eq_gradient {f : E → ℝ}
    (hc : Convex ℝ (epigraph (fun x ↦ (f x:EReal)))) {x : E}
    (hd : DifferentiableAt ℝ f x) :
    subdifferential (fun y ↦ (f y:EReal)) x = {gradient f x} := by
  rw [subdifferential_eq_regularSubdifferential_of_convex hc (isProper_coe_real f) rfl]
  exact (regularSubdifferential_of_hasGradientAt hd.hasGradientAt).1

/-- Coercivity guarantees that every linear tilt has a critical point, so
the gradient of a differentiable convex function is surjective. -/
theorem gradient_surjective_of_coercive_convex {f : E → ℝ} (hd : Differentiable ℝ f)
    (hc : Convex ℝ (epigraph (fun x ↦ (f x:EReal))))
    (hco : IsCoercive (fun x ↦ (f x:EReal))) : Function.Surjective (gradient f) := by
  intro a
  have hp := isProper_coe_real f
  have hl : LowerSemicontinuous (fun x ↦ (f x:EReal)) :=
    (continuous_coe_real_ereal.comp hd.continuous).lowerSemicontinuous
  have hpt := isProper_sub_inner hp a
  have hlt := lowerSemicontinuous_sub_inner hl a
  have hct := convex_epigraph_sub_inner hc a
  obtain ⟨x,hx⟩ := argmin_nonempty_of_isInfCompact_of_lsc_of_isProper
    (isInfCompact_of_isCoercive hct hlt hpt (hco.sub_inner a)) hlt hpt
  have hs := (mem_argmin_sub_inner_iff_subgradient hp hc a x).mp hx
  rw [subdifferential_coe_real_eq_gradient hc (hd x)] at hs
  exact ⟨x,hs.symm⟩

/-- **11.9**, the primal gradient is a bijection. -/
theorem classicalLegendre_gradient_bijective {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : Convex ℝ (epigraph (fun x ↦ (f x:EReal))))
    (hco : IsCoercive (fun x ↦ (f x:EReal)))
    (hpos : ∀ x w, w ≠ 0 → 0 < ⟪fderiv ℝ (gradient f) x w,w⟫_ℝ) :
    Function.Bijective (gradient f) :=
  ⟨injective_of_fderiv_inner_pos ((contDiff_one_gradient hf).differentiable (by norm_num)) hpos,
    gradient_surjective_of_coercive_convex (hf.differentiable (by norm_num)) hc hco⟩

/-- The conjugate is finite everywhere in the classical coercive setting. -/
theorem classicalLegendre_conjugate_finite {f : E → ℝ}
    (hco : IsCoercive (fun x ↦ (f x:EReal))) (v : E) :
    fenchelConjugate (fun x ↦ (f x:EReal)) v =
      ((fenchelConjugate (fun x ↦ (f x:EReal)) v).toReal:EReal) :=
  (EReal.coe_toReal (fenchelConjugate_lt_top_of_isCoercive hco v).ne
    (bot_lt_fenchelConjugate_of_finite (f := fun y ↦ (f y:EReal)) (x := 0) rfl v).ne').symm

/-- At conjugate points the inverse primal gradient is the derivative of
the real-valued conjugate. -/
theorem conjugate_hasGradientAt_of_gradient_injective {f : E → ℝ}
    (hd : Differentiable ℝ f) (hc : Convex ℝ (epigraph (fun x ↦ (f x:EReal))))
    (hinj : Function.Injective (gradient f)) (x : E) :
    HasGradientAt (fun v ↦ (fenchelConjugate (fun y ↦ (f y:EReal)) v).toReal) x (gradient f x) := by
  have hp := isProper_coe_real f
  have hl : LowerSemicontinuous (fun x ↦ (f x:EReal)) :=
    (continuous_coe_real_ereal.comp hd.continuous).lowerSemicontinuous
  have hs : subdifferential (fenchelConjugate (fun y ↦ (f y:EReal))) (gradient f x) = {x} := by
    ext y
    rw [mem_subdifferential_fenchelConjugate_iff hp hl hc,
      subdifferential_coe_real_eq_gradient hc (hd y)]
    change gradient f x=gradient f y ↔ y=x
    exact ⟨fun h ↦ (hinj h).symm,fun h ↦ by rw [h]⟩
  exact ((subdifferential_eq_singleton_iff_hasGradientAt_of_convex
    (isProper_fenchelConjugate hp hl hc) (lowerSemicontinuous_fenchelConjugate _)
    (convex_epigraph_fenchelConjugate _)).mp hs).2

/-- **11(7)**, the conjugate value at a gradient image. -/
theorem classicalLegendre_value_at_gradient {f : E → ℝ} (hd : Differentiable ℝ f)
    (hc : Convex ℝ (epigraph (fun x ↦ (f x:EReal)))) (x : E) :
    fenchelConjugate (fun y ↦ (f y:EReal)) (gradient f x) =
      ((⟪gradient f x,x⟫_ℝ-f x:ℝ):EReal) := by
  apply (mem_subdifferential_iff_fenchelConjugate_eq (isProper_coe_real f) hc rfl).mp
  rw [subdifferential_coe_real_eq_gradient hc (hd x)]
  rfl

end RW
