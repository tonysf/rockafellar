/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Smooth functions and indicators as amenable models
-/
import RockafellarWets.Chapter10.Amenability
import RockafellarWets.Chapter1.Semicontinuity
import RockafellarWets.Chapter2.Defs

open Set Filter Topology Classical
open scoped InnerProductSpace

noncomputable section
namespace RW

private theorem convex_epigraph_real_id : Convex ℝ (epigraph (fun y : ℝ ↦ (y : EReal))) := by
  have h := (convex_epigraph_iff_convexOn (fun y : ℝ ↦ y) univ convex_univ).mpr (convexOn_id convex_univ)
  simpa [epigraph] using h

private theorem plq_real_id : IsPiecewiseLinearQuadratic (fun y : ℝ ↦ (y : EReal)) := by
  let q : QuadraticPiece ℝ := ⟨0,by simp,1,0⟩
  simpa [q,QuadraticPiece.eval] using isPiecewiseLinearQuadratic_piece (IsPolyhedral.univ (E := ℝ)) q

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A local smooth scalar function has an amenable model with the identity
outer function. The second-order model is fully amenable. -/
theorem smooth_amenable_model {f : E → ℝ} {x : E} {V : Set E} {r : ℕ}
    (hV : IsOpen V) (hx : x ∈ V) (hf : ContDiffOn ℝ r f V) (full : Bool) :
    Nonempty (AmenableFunctionModel (fun y ↦ (f y : EReal)) x r full) := by
  refine ⟨{
    Target := ℝ, outer := fun y ↦ (y : EReal), inner := f, neighborhood := V,
    isOpen := hV, mem := hx, finite := ⟨EReal.coe_ne_bot _,EReal.coe_ne_top _⟩,
    proper := ⟨⟨0,by simp⟩,fun _ ↦ by simp⟩, lsc := continuous_coe_real_ereal.lowerSemicontinuous,
    convex := convex_epigraph_real_id, smooth := hf, eqOn := fun _ _ ↦ rfl,
    qualification := ?_, plq := fun _ ↦ plq_real_id }⟩
  intro v hv _
  have hdom : effectiveDomain (fun y : ℝ ↦ (y : EReal)) = univ := by ext y; simp [effectiveDomain]
  simpa [hdom,normalCone_univ] using hv

/-- **Example 10.24(a)**, including the local form of its C¹ assertion. -/
theorem amenableAt_of_contDiffOn {f : E → ℝ} {x : E} {V : Set E}
    (hV : IsOpen V) (hx : x ∈ V) (hf : ContDiffOn ℝ 1 f V) :
    AmenableAt (fun y ↦ (f y : EReal)) x := smooth_amenable_model hV hx hf false

/-- **Example 10.24(a)**, including the local form of its C² assertion. -/
theorem fullyAmenableAt_of_contDiffOn {f : E → ℝ} {x : E} {V : Set E}
    (hV : IsOpen V) (hx : x ∈ V) (hf : ContDiffOn ℝ 2 f V) :
    FullyAmenableAt (fun y ↦ (f y : EReal)) x := smooth_amenable_model hV hx hf true

/-- Polyhedral indicators are a special case of Definition 10.20. -/
theorem IsPolyhedral.isPiecewiseLinearQuadratic_indicator {C : Set E} (hC : IsPolyhedral C) :
    IsPiecewiseLinearQuadratic (indicatorVA C) := by
  let q : QuadraticPiece E := ⟨0,by simp,0,0⟩
  simpa [q,QuadraticPiece.eval,indicatorVA] using isPiecewiseLinearQuadratic_piece hC q

/-- The forward indicator equivalence in the paragraph following
Definition 10.23, simultaneously for all smoothness orders and full models. -/
def AmenableSetModel.indicator {C : Set E} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableSetModel C x r full) : AmenableFunctionModel (indicatorVA C) x r full where
  Target := M.Target
  outer := indicatorVA M.constraint
  inner := M.inner
  neighborhood := M.neighborhood
  isOpen := M.isOpen
  mem := M.mem
  finite := by simp [indicatorVA,M.base]
  proper := (indicatorVA_isProper_iff M.constraint).mpr ⟨M.inner x,(M.eqOn x M.mem).mp M.base⟩
  lsc := lowerSemicontinuous_indicatorVA M.closed
  convex := by rw [epigraph_indicatorVA]; exact M.convex.prod (convex_Ici 0)
  smooth := M.smooth
  eqOn := by
    intro y hy
    simp only [indicatorVA,M.eqOn y hy]
  qualification := by
    simpa only [effectiveDomain_indicatorVA,M.closed.closure_eq] using M.qualification
  plq := fun h ↦ (M.polyhedral h).isPiecewiseLinearQuadratic_indicator

theorem SetAmenableAt.indicator {C : Set E} {x : E} (h : SetAmenableAt C x) :
    AmenableAt (indicatorVA C) x := h.map AmenableSetModel.indicator

theorem SetStronglyAmenableAt.indicator {C : Set E} {x : E} (h : SetStronglyAmenableAt C x) :
    StronglyAmenableAt (indicatorVA C) x := h.map AmenableSetModel.indicator

theorem SetFullyAmenableAt.indicator {C : Set E} {x : E} (h : SetFullyAmenableAt C x) :
    FullyAmenableAt (indicatorVA C) x := h.map AmenableSetModel.indicator

end RW
end
