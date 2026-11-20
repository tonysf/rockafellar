/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Amenable sets and functions
-/
import RockafellarWets.Chapter10.PiecewiseLinearQuadratic
import RockafellarWets.Chapter6.ElementaryCones
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear

open Set Filter Topology

noncomputable section
namespace RW
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A witness for Definition 10.23(a). Its auxiliary space is arbitrary
finite-dimensional Euclidean space, so the definition is independent of coordinates. -/
structure AmenableFunctionModel (f : E → EReal) (x : E) (r : ℕ) (full : Bool) where
  Target : Type u
  [normedTarget : NormedAddCommGroup Target]
  [innerTarget : InnerProductSpace ℝ Target]
  [finiteTarget : FiniteDimensional ℝ Target]
  outer : Target → EReal
  inner : E → Target
  neighborhood : Set E
  isOpen : IsOpen neighborhood
  mem : x ∈ neighborhood
  finite : f x ≠ ⊥ ∧ f x ≠ ⊤
  proper : IsProper outer
  lsc : LowerSemicontinuous outer
  convex : Convex ℝ (epigraph outer)
  smooth : ContDiffOn ℝ r inner neighborhood
  eqOn : ∀ y ∈ neighborhood, f y = outer (inner y)
  qualification : ∀ v ∈ normalCone (closure (effectiveDomain outer)) (inner x),
    (fderiv ℝ inner x).adjoint v = 0 → v = 0
  plq : full = true → IsPiecewiseLinearQuadratic outer

attribute [instance] AmenableFunctionModel.normedTarget AmenableFunctionModel.innerTarget
  AmenableFunctionModel.finiteTarget

/-- **Definition 10.23(a)**, amenability. -/
def AmenableAt (f : E → EReal) (x : E) : Prop := Nonempty (AmenableFunctionModel f x 1 false)
/-- **Definition 10.23(a)**, strong amenability. -/
def StronglyAmenableAt (f : E → EReal) (x : E) : Prop := Nonempty (AmenableFunctionModel f x 2 false)
/-- **Definition 10.23(a)**, full amenability. -/
def FullyAmenableAt (f : E → EReal) (x : E) : Prop := Nonempty (AmenableFunctionModel f x 2 true)

/-- A witness for the set version of Definition 10.23(b). -/
structure AmenableSetModel (C : Set E) (x : E) (r : ℕ) (full : Bool) where
  Target : Type u
  [normedTarget : NormedAddCommGroup Target]
  [innerTarget : InnerProductSpace ℝ Target]
  [finiteTarget : FiniteDimensional ℝ Target]
  constraint : Set Target
  inner : E → Target
  neighborhood : Set E
  isOpen : IsOpen neighborhood
  mem : x ∈ neighborhood
  base : x ∈ C
  closed : IsClosed constraint
  convex : Convex ℝ constraint
  smooth : ContDiffOn ℝ r inner neighborhood
  eqOn : ∀ y ∈ neighborhood, y ∈ C ↔ inner y ∈ constraint
  qualification : ∀ v ∈ normalCone constraint (inner x),
    (fderiv ℝ inner x).adjoint v = 0 → v = 0
  polyhedral : full = true → IsPolyhedral constraint

attribute [instance] AmenableSetModel.normedTarget AmenableSetModel.innerTarget
  AmenableSetModel.finiteTarget

/-- **Definition 10.23(b)**, amenability of a set. -/
def SetAmenableAt (C : Set E) (x : E) : Prop := Nonempty (AmenableSetModel C x 1 false)
def SetStronglyAmenableAt (C : Set E) (x : E) : Prop := Nonempty (AmenableSetModel C x 2 false)
def SetFullyAmenableAt (C : Set E) (x : E) : Prop := Nonempty (AmenableSetModel C x 2 true)

theorem StronglyAmenableAt.amenableAt {f : E → EReal} {x : E}
    (h : StronglyAmenableAt f x) : AmenableAt f x := by
  obtain ⟨M⟩ := h
  exact ⟨{ M with smooth := M.smooth.of_le (by norm_num) }⟩

theorem FullyAmenableAt.stronglyAmenableAt {f : E → EReal} {x : E}
    (h : FullyAmenableAt f x) : StronglyAmenableAt f x := by
  obtain ⟨M⟩ := h
  exact ⟨{ M with plq := by simp }⟩

theorem FullyAmenableAt.amenableAt {f : E → EReal} {x : E}
    (h : FullyAmenableAt f x) : AmenableAt f x := h.stronglyAmenableAt.amenableAt

theorem SetStronglyAmenableAt.setAmenableAt {C : Set E} {x : E}
    (h : SetStronglyAmenableAt C x) : SetAmenableAt C x := by
  obtain ⟨M⟩ := h
  exact ⟨{ M with smooth := M.smooth.of_le (by norm_num) }⟩

theorem SetFullyAmenableAt.setStronglyAmenableAt {C : Set E} {x : E}
    (h : SetFullyAmenableAt C x) : SetStronglyAmenableAt C x := by
  obtain ⟨M⟩ := h
  exact ⟨{ M with polyhedral := by simp }⟩

/-- **Example 10.24(b)**: proper lower semicontinuous convex functions are
strongly amenable at every point of their effective domain. -/
theorem stronglyAmenableAt_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    {x : E} (hx : x ∈ effectiveDomain f) : StronglyAmenableAt f x := by
  refine ⟨{
    Target := E, outer := f, inner := id, neighborhood := univ,
    isOpen := isOpen_univ, mem := mem_univ x, finite := ⟨ne_of_gt (hp.2 x),ne_of_lt hx⟩,
    proper := hp, lsc := hl, convex := hc, smooth := contDiff_id.contDiffOn,
    eqOn := fun _ _ ↦ rfl, qualification := ?_, plq := by simp }⟩
  intro v hv hzero
  simpa using hzero

/-- **Example 10.24(b)**: convex PLQ functions are fully amenable. -/
theorem fullyAmenableAt_of_convex_plq {f : E → EReal} (hp : IsPiecewiseLinearQuadratic f)
    (hc : Convex ℝ (epigraph f)) {x : E} (hx : x ∈ effectiveDomain f) : FullyAmenableAt f x := by
  have hproper : IsProper f := ⟨⟨x,hx⟩,fun y ↦ lt_of_le_of_ne bot_le (hp.ne_bot y).symm⟩
  refine ⟨{
    Target := E, outer := f, inner := id, neighborhood := univ,
    isOpen := isOpen_univ, mem := mem_univ x, finite := ⟨hp.ne_bot x,ne_of_lt hx⟩,
    proper := hproper, lsc := hp.lowerSemicontinuous, convex := hc,
    smooth := contDiff_id.contDiffOn, eqOn := fun _ _ ↦ rfl,
    qualification := ?_, plq := fun _ ↦ hp }⟩
  intro v hv hzero
  simpa using hzero

/-- **Example 10.24(c)**: closed convex sets are strongly amenable. -/
theorem setStronglyAmenableAt_of_convex {C : Set E} (hclosed : IsClosed C)
    (hconvex : Convex ℝ C) {x : E} (hx : x ∈ C) : SetStronglyAmenableAt C x := by
  refine ⟨{
    Target := E, constraint := C, inner := id, neighborhood := univ,
    isOpen := isOpen_univ, mem := mem_univ x, base := hx, closed := hclosed,
    convex := hconvex, smooth := contDiff_id.contDiffOn, eqOn := fun _ _ ↦ Iff.rfl,
    qualification := ?_, polyhedral := by simp }⟩
  intro v hv hzero
  simpa using hzero

/-- **Example 10.24(c)**: polyhedra are fully amenable. -/
theorem setFullyAmenableAt_of_polyhedral {C : Set E} (hC : IsPolyhedral C)
    {x : E} (hx : x ∈ C) : SetFullyAmenableAt C x := by
  refine ⟨{
    Target := E, constraint := C, inner := id, neighborhood := univ,
    isOpen := isOpen_univ, mem := mem_univ x, base := hx, closed := hC.isClosed,
    convex := hC.convex, smooth := contDiff_id.contDiffOn, eqOn := fun _ _ ↦ Iff.rfl,
    qualification := ?_, polyhedral := fun _ ↦ hC }⟩
  intro v hv hzero
  simpa using hzero

end RW
end
