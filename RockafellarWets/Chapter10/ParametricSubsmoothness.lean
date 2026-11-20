/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local subsmoothness and gradient formulas in parametric optimization
-/

import RockafellarWets.Chapter10.ParametricSubsmoothRepresentation
import RockafellarWets.Chapter10.ParametricSubsmoothnessFormulas
import RockafellarWets.Chapter10.FiniteInfimumSubderivatives

open Filter Set Topology InnerProductSpace MeasureTheory
open scoped InnerProductSpace

namespace RW

universe u

variable {E P : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P]

/-- The local conclusions of 10.58, stated for the original extended-real
value function. Here `Y` consists of partial gradients at optimal decisions. -/
structure HasMarginalGradientFormulas (p : P → EReal) (Y : P → Set P) (O : Set P) : Prop where
  finite : ∀ u ∈ O, ((p u).toReal : EReal) = p u
  upperC : IsUpperCOn 1 (fun u ↦ (p u).toReal) O
  strict_iff : ∀ u ∈ O, (HasStrictFDerivAt (fun v ↦ (p v).toReal)
    (fderiv ℝ (fun v ↦ (p v).toReal) u) u ↔ ∃ y, Y u = {y})
  null_exceptional : volume (O \ {u | ∃ y, Y u = {y}}) = 0
  at_parameter : ∀ u ∈ O,
    let q := fun v ↦ (p v).toReal
    let D := {v | v ∈ O ∧ DifferentiableAt ℝ q v}
    let Z := reachableGradients q D u
    subdifferential p u = Z ∧ Z ⊆ Y u ∧ convexHull ℝ Z = convexHull ℝ (Y u) ∧
      (DifferentiableAt ℝ q u → subdifferential p u = Y u) ∧
      ∀ w, (∃ y ∈ Z, subderivative p u w = (⟪y,w⟫_ℝ : EReal) ∧
        ∀ z ∈ Z, ⟪y,w⟫_ℝ ≤ ⟪z,w⟫_ℝ) ∧
        ∃ y ∈ Y u, subderivative p u w = (⟪y,w⟫_ℝ : EReal) ∧
          ∀ z ∈ Y u, ⟪y,w⟫_ℝ ≤ ⟪z,w⟫_ℝ

/-- **Theorem 10.58**, on a possibly smaller open neighborhood of the
reference parameter as in the proof in the book. -/
theorem parametric_subsmoothness {f : E × P → EReal} {g : E × P → ℝ} {G : E × P → P}
    {V : Set E} {W : Set P} {u₀ : P} (hf : LowerSemicontinuous f) (hp : IsProper f)
    (hb : IsLevelBoundedInXLocallyUniformly f) (hu₀ : valueFunction f u₀ < ⊤)
    (hV : IsOpen V) (hW : IsOpen W) (huW : u₀ ∈ W) (hPV : paramArgmin f u₀ ⊆ V)
    (hfg : ∀ t ∈ V ×ˢ W, f t = (g t : EReal)) (hg : ContinuousOn g (V ×ˢ W))
    (hG : ContinuousOn G (V ×ˢ W))
    (hd : ∀ x ∈ V, ∀ u ∈ W, HasGradientAt (fun v ↦ g (x,v)) (G (x,u)) u) :
    ∃ O, IsOpen O ∧ u₀ ∈ O ∧ O ⊆ W ∧ HasMarginalGradientFormulas (valueFunction f)
      (fun u ↦ (fun x ↦ G (x,u)) '' paramArgmin f u) O := by
  obtain ⟨O,hO,huO,hOW,hupper,R,hY⟩ :=
    exists_upperC_parametric_representation hf hp hb hu₀ hV hW huW hPV hfg hg hG hd
  obtain ⟨x₀,hx₀⟩ := paramArgmin_nonempty hf hp hb hu₀
  have hfinite (u : P) (hu : u ∈ O) : ((valueFunction f u).toReal : EReal) = valueFunction f u := by
    have hlt := (iInf_le (fun x ↦ f (x,u)) x₀).trans_lt
      ((hfg _ ⟨hPV hx₀,hOW hu⟩).trans_lt (EReal.coe_lt_top _))
    exact EReal.coe_toReal hlt.ne ((isProper_valueFunction_of_lsc_localUniform hf hp hb).2 u).ne'
  refine ⟨O,hO,huO,hOW,hfinite,hupper,fun u hu ↦ R.upper_strictDifferentiable_iff_singleton
    hO hu (hY u hu),R.upper_singleton_complement_null hO hY volume,?_⟩
  intro u hu
  have he : valueFunction f =ᶠ[𝓝 u] (fun v ↦ ((valueFunction f v).toReal : EReal)) := by
    filter_upwards [hO.mem_nhds hu] with v hv
    exact (hfinite v hv).symm
  have hs := subdifferential_congr_nhds_of_finite (hfinite u hu).symm he
  have hr := R.upper_subdifferential_eq_reachable hO hu
  refine ⟨hs.trans hr,hr ▸ R.upper_subdifferential_subset hO hu (hY u hu),
    R.upper_convexHull_reachable hO hu (hY u hu),fun h ↦ hs.trans
      (R.upper_subdifferential_eq_active_of_differentiable hO hu (hY u hu) h),?_⟩
  intro w
  rw [subderivative_congr_nhds he w]
  exact ⟨R.upper_subderivative_min_reachable hO hu w,R.upper_subderivative_min_active hO hu (hY u hu) w⟩

end RW
