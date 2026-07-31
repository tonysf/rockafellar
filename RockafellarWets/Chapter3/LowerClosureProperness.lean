/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Properness of epigraphical lower closures
-/

import RockafellarWets.Chapter3.PositiveHullExactCompletion
import Mathlib.Analysis.Convex.Intrinsic

open EReal Set Topology

namespace RW

/-- In finite dimension, closing the epigraph of a proper convex function
cannot create a `-∞` value. -/
theorem isProper_of_isLowerClosure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f cl_f : E → EReal} (hproper : IsProper f)
    (hconv : Convex ℝ (epigraph f))
    (hcl : IsLowerClosure f cl_f) :
    IsProper cl_f := by
  have hne : (epigraph f).Nonempty := by
    rcases hproper.1 with ⟨x, hxTop⟩
    have hxBot : f x ≠ ⊥ := ne_of_gt (hproper.2 x)
    refine ⟨(x, (f x).toReal), ?_⟩
    rw [mem_epigraph_iff]
    rw [EReal.coe_toReal (ne_of_lt hxTop) hxBot]
  have hfinite : ∃ x, cl_f x < ⊤ := by
    rcases hproper.1 with ⟨x, hxTop⟩
    have hxBot : f x ≠ ⊥ := ne_of_gt (hproper.2 x)
    let a : ℝ := (f x).toReal
    have hxa : (x, a) ∈ epigraph f := by
      rw [mem_epigraph_iff]
      rw [EReal.coe_toReal (ne_of_lt hxTop) hxBot]
    refine ⟨x, ?_⟩
    have hmem : (x, a) ∈ epigraph cl_f := by
      rw [hcl]
      exact subset_closure hxa
    exact (show cl_f x ≤ (a : EReal) by simpa [mem_epigraph_iff] using hmem).trans_lt
      (EReal.coe_lt_top a)
  refine ⟨hfinite, ?_⟩
  intro x
  by_contra hx
  have hxbot : cl_f x = ⊥ := bot_unique (le_of_not_gt hx)
  obtain ⟨p, hp⟩ := hne.intrinsicInterior hconv
  rcases mem_intrinsicInterior.mp hp with ⟨p', hp'int, hp'eq⟩
  let A := affineSpan ℝ (epigraph f)
  have hclosureA : closure (epigraph f) ⊆ A := by
    exact closure_minimal (subset_affineSpan ℝ (epigraph f))
      A.closed_of_finiteDimensional
  let z : E := (1 / 2 : ℝ) • (p.1 + x)
  let r : ℝ := if f z = ⊤ then 0 else (f z).toReal - 1
  let a : ℝ := 2 * r - p.2
  have hqcl : (x, a) ∈ closure (epigraph f) := by
    rw [← hcl]
    simp [mem_epigraph_iff, hxbot]
  let q' : A := ⟨(x, a), hclosureA hqcl⟩
  have hq'cl : q' ∈ closure ((↑) ⁻¹' epigraph f : Set A) := by
    have hqi : (x, a) ∈ intrinsicClosure ℝ (epigraph f) := by
      rwa [intrinsicClosure_eq_closure]
    rcases mem_intrinsicClosure.mp hqi with ⟨q'', hq'', hq''eq⟩
    have hqq : q'' = q' := Subtype.ext hq''eq
    simpa [hqq] using hq''
  letI : Nonempty A := ⟨p'⟩
  let e := AffineIsometryEquiv.constVSub ℝ (V := A.direction) p'
  let φ : A.direction →ᵃ[ℝ] E × ℝ :=
    A.subtype.comp e.symm.toAffineMap
  let D : Set A.direction := φ ⁻¹' epigraph f
  have hconvD : Convex ℝ D := hconv.affine_preimage φ
  have hpreimage :
      D = e.toHomeomorph '' ((↑) ⁻¹' epigraph f : Set A) := by
    ext v
    constructor
    · intro hv
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      simpa [D, φ] using hv
    · rintro ⟨y, hy, hyeq⟩
      rw [← hyeq]
      change (↑(e.symm (e y)) : E × ℝ) ∈ epigraph f
      rw [e.symm_apply_apply]
      exact hy
  have hpD : e p' ∈ interior D := by
    rw [hpreimage, ← e.toHomeomorph.image_interior]
    exact mem_image_of_mem e hp'int
  have hqD : e q' ∈ closure D := by
    rw [hpreimage, ← e.toHomeomorph.image_closure]
    exact mem_image_of_mem e hq'cl
  have hmidOpen :
      AffineMap.lineMap (e p') (e q') (1 / 2 : ℝ) ∈
        openSegment ℝ (e p') (e q') :=
    lineMap_mem_openSegment ℝ _ _ (by norm_num)
  have hmidD :
      AffineMap.lineMap (e p') (e q') (1 / 2 : ℝ) ∈ D := by
    exact interior_subset
      (hconvD.openSegment_interior_closure_subset_interior hpD hqD hmidOpen)
  have hmid :
      AffineMap.lineMap p (x, a) (1 / 2 : ℝ) ∈ epigraph f := by
    have hφ := hmidD
    change φ (AffineMap.lineMap (e p') (e q') (1 / 2 : ℝ)) ∈ epigraph f at hφ
    rw [φ.apply_lineMap] at hφ
    have hpφ : φ (e p') = p := by
      change (↑(e.symm (e p')) : E × ℝ) = p
      rw [e.symm_apply_apply]
      exact hp'eq
    have hqφ : φ (e q') = (x, a) := by
      change (↑(e.symm (e q')) : E × ℝ) = (x, a)
      rw [e.symm_apply_apply]
    rwa [hpφ, hqφ] at hφ
  have hcoords :
      AffineMap.lineMap p (x, a) (1 / 2 : ℝ) = (z, r) := by
    rcases p with ⟨y, b⟩
    ext
    · simp [AffineMap.lineMap_apply_module, z]
      module
    · simp [AffineMap.lineMap_apply_module, a]
      ring
  rw [hcoords, mem_epigraph_iff] at hmid
  by_cases hztop : f z = ⊤
  · simp [hztop] at hmid
  · have hzbot : f z ≠ ⊥ := ne_of_gt (hproper.2 z)
    have hrlt : (r : EReal) < f z := by
      rw [show f z = ((f z).toReal : EReal) by
        exact (EReal.coe_toReal hztop hzbot).symm]
      have hr : r = (f z).toReal - 1 := by simp [r, hztop]
      rw [hr]
      exact_mod_cast (show (f z).toReal - 1 < (f z).toReal by linarith)
    exact (not_le_of_gt hrlt) hmid

/-- Exercise 3.49(c), book-facing form.  Finite-dimensional properness of the
epigraphical lower closure is now discharged internally. -/
theorem sublinear_closedPerspectiveFunction_lowerClosure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f cl_f : E → EReal} (hproper : IsProper f)
    (hconv : Convex ℝ (epigraph f))
    (hcl : IsLowerClosure f cl_f) :
    Sublinear (closedPerspectiveFunction cl_f) :=
  sublinear_closedPerspectiveFunction_lowerClosure_of_isProper
    hproper hconv hcl (isProper_of_isLowerClosure hproper hconv hcl)

end RW
