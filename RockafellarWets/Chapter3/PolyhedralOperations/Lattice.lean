/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Lattice Polyhedral Operations

This file packages supremum, infimum, intersection, union, and separated-addition constructions.
-/

import RockafellarWets.Chapter3.PolyhedralOperations.Affine

open Set EReal
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def separatedAddLinearEquiv :
    (E × E) ≃L[ℝ] (E × E) :=
  ContinuousLinearEquiv.mk
    { toFun := fun p => (p.2, p.1 + p.2)
      invFun := fun p => (p.2 - p.1, p.1)
      left_inv := by
        intro p
        ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      right_inv := by
        intro p
        ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_add' := by
        intro p q
        ext <;> simp [add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a p
        ext <;> simp [smul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] }
    (continuous_snd.prodMk (continuous_fst.add continuous_snd))
    ((continuous_snd.sub continuous_fst).prodMk continuous_fst)

/-- The scalar-height epigraph integrand attached to a proper function with
closed polyhedral epigraph is again convex piecewise-linear. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epigraphHeightIntegrand
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (hproper : IsProper f) :
    IsConvexPiecewiseLinear (epigraphHeightIntegrand f) := by
  have hInd : IsConvexPiecewiseLinear (indicatorVA (epigraph f)) :=
    IsClosedPolyhedral.isConvexPiecewiseLinear_indicatorVA
      (hC := (hf : IsClosedPolyhedral (epigraph f)))
      (hCne := epigraph_nonempty_of_isProper hproper)
  have hSwap :
      IsConvexPiecewiseLinear (fun p : ℝ × E => indicatorVA (epigraph f) (p.2, p.1)) := by
    simpa using IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearEquiv hInd
      (ContinuousLinearEquiv.prodComm ℝ ℝ E)
  simpa [epigraphHeightIntegrand] using
    IsConvexPiecewiseLinear.isConvexPiecewiseLinear_addAffine hSwap (LinearMap.fst ℝ ℝ E) 0

/-- The scalar-height epigraph integrand attached to a convex piecewise-linear
function is again convex piecewise-linear. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_epigraphHeightIntegrand
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f) :
    IsConvexPiecewiseLinear (epigraphHeightIntegrand f) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_epigraphHeightIntegrand hf.isProper

/-- If the intersection `epi f ∩ epi g` is polyhedral, then the scalar-height
model for `f ⊔ g` has a polyhedral epigraph. This isolates the remaining
set-side intersection input behind the `max` part of Proposition `3.55(b)`. -/
theorem hasPolyhedralEpigraph_supHeightIntegrand_of_isPolyhedral_inter_epigraph
    [FiniteDimensional ℝ E]
    {f g : E → EReal} (hinter : IsPolyhedral (epigraph f ∩ epigraph g)) :
    HasPolyhedralEpigraph (supHeightIntegrand f g) := by
  have hind : HasPolyhedralEpigraph (indicatorVA (epigraph f ∩ epigraph g)) :=
    hinter.hasPolyhedralEpigraph_indicatorVA
  have hswap :
      HasPolyhedralEpigraph
        (fun p : ℝ × E => indicatorVA (epigraph f ∩ epigraph g) (p.2, p.1)) := by
    simpa using
      hind.hasPolyhedralEpigraph_precompose_linearEquiv
        (ContinuousLinearEquiv.prodComm ℝ ℝ E)
  simpa [supHeightIntegrand, indicatorVA_inter, epigraph_sup, ← add_assoc] using
    hswap.hasPolyhedralEpigraph_addAffine (LinearMap.fst ℝ ℝ E) 0

/-- If the intersection `epi f ∩ epi g` is closed polyhedral, then the
scalar-height model for `f ⊔ g` has a closed polyhedral epigraph. -/
theorem hasClosedPolyhedralEpigraph_supHeightIntegrand_of_isClosedPolyhedral_inter_epigraph
    [FiniteDimensional ℝ E]
    {f g : E → EReal} (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    HasClosedPolyhedralEpigraph (supHeightIntegrand f g) := by
  have hind : HasClosedPolyhedralEpigraph (indicatorVA (epigraph f ∩ epigraph g)) :=
    hinter.hasClosedPolyhedralEpigraph_indicatorVA
  have hswap :
      HasClosedPolyhedralEpigraph
        (fun p : ℝ × E => indicatorVA (epigraph f ∩ epigraph g) (p.2, p.1)) := by
    simpa using
      hind.hasClosedPolyhedralEpigraph_precompose_linearEquiv
        (ContinuousLinearEquiv.prodComm ℝ ℝ E)
  simpa [supHeightIntegrand, indicatorVA_inter, epigraph_sup, ← add_assoc] using
    hswap.hasClosedPolyhedralEpigraph_addAffine (LinearMap.fst ℝ ℝ E) 0

/-- The pointwise supremum of two convex piecewise-linear functions with a
common finite-domain point admits the scalar-height value-function model from
`valueFunction_sup_eq`, and that model already satisfies the proper/lsc/local
uniform hypotheses of Theorem 3.31. -/
theorem IsConvexPiecewiseLinear.supHeightIntegrand_regular_of_nonempty_effectiveDomain_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (supHeightIntegrand f g) ∧
      LowerSemicontinuous (supHeightIntegrand f g) ∧
      IsLevelBoundedInXLocallyUniformly (supHeightIntegrand f g) ∧
      valueFunction (E := ℝ) (F := E) (supHeightIntegrand f g) =
        fun x => f x ⊔ g x := by
  have hreg := hf.sup_regular_of_nonempty_effectiveDomain_inter hg hdom
  refine ⟨isProper_supHeightIntegrand (f := f) (g := g) hreg.1, ?_, ?_, valueFunction_sup_eq f g⟩
  · exact lowerSemicontinuous_supHeightIntegrand (f := f) (g := g) hreg.2.1
  · exact isLevelBoundedInXLocallyUniformly_supHeightIntegrand (f := f) (g := g) hreg.2.1 hreg.1

theorem HasClosedPolyhedralEpigraph.supHeightIntegrand_regular_of_nonempty_effectiveDomain_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (supHeightIntegrand f g) ∧
      LowerSemicontinuous (supHeightIntegrand f g) ∧
      IsLevelBoundedInXLocallyUniformly (supHeightIntegrand f g) ∧
      valueFunction (E := ℝ) (F := E) (supHeightIntegrand f g) =
        fun x => f x ⊔ g x := by
  have hreg :=
    hf.sup_regular_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  refine ⟨isProper_supHeightIntegrand (f := f) (g := g) hreg.1, ?_, ?_, valueFunction_sup_eq f g⟩
  · exact lowerSemicontinuous_supHeightIntegrand (f := f) (g := g) hreg.2.1
  · exact isLevelBoundedInXLocallyUniformly_supHeightIntegrand (f := f) (g := g) hreg.2.1 hreg.1

/-- Direct epigraph form of the pointwise supremum operation: if the
intersection of the epigraphs is closed polyhedral, then the pointwise
supremum has a closed polyhedral epigraph. -/
theorem hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral
    {ι : Type*} {f : ι → E → EReal}
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    HasClosedPolyhedralEpigraph (fun x : E => ⨆ i, f i x) := by
  change IsClosedPolyhedral (epigraph (fun x : E => ⨆ i, f i x))
  rwa [epigraph_iSup]

/-- Binary direct epigraph form of the pointwise supremum operation. -/
theorem hasClosedPolyhedralEpigraph_sup_of_inter_closedPolyhedral
    {f g : E → EReal}
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    HasClosedPolyhedralEpigraph (fun x : E => f x ⊔ g x) := by
  change IsClosedPolyhedral (epigraph (fun x : E => f x ⊔ g x))
  rwa [epigraph_sup]

/-- If an arbitrary pointwise supremum is proper and its epigraph intersection
is closed polyhedral, then it is convex piecewise-linear. -/
theorem isConvexPiecewiseLinear_iSup_of_iInter_closedPolyhedral
    {ι : Type*} {f : ι → E → EReal}
    (hproper : IsProper (fun x : E => ⨆ i, f i x))
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨆ i, f i x) :=
  ⟨hproper, hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral hinter⟩

/-- Binary direct epigraph form of the pointwise maximum operation at the CPL
layer. -/
theorem isConvexPiecewiseLinear_sup_of_inter_closedPolyhedral
    {f g : E → EReal}
    (hproper : IsProper (fun x : E => f x ⊔ g x))
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    IsConvexPiecewiseLinear (fun x : E => f x ⊔ g x) :=
  ⟨hproper, hasClosedPolyhedralEpigraph_sup_of_inter_closedPolyhedral hinter⟩

/-- If every member of a finite nonempty family is proper, the effective
domains have a common point, and the epigraph intersection is closed
polyhedral, then the pointwise supremum is convex piecewise-linear. -/
theorem isConvexPiecewiseLinear_iSup_of_isProper_of_iInter_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsProper (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty)
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨆ i, f i x) :=
  isConvexPiecewiseLinear_iSup_of_iInter_closedPolyhedral
    (isProper_iSup_of_finite_of_isProper_of_nonempty_iInter_effectiveDomain hf hdom)
    hinter

/-- Method form of the finite pointwise-supremum epigraph criterion: a
closed-polyhedral theorem for the epigraph intersection gives a
closed-polyhedral epigraph for the supremum. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (_hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    HasClosedPolyhedralEpigraph (fun x : E => ⨆ i, f i x) :=
  RW.hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral hinter

/-- Finite pointwise suprema of closed-polyhedral-epigraph functions are convex
piecewise-linear when the family has a common finite-domain point and the
epigraph intersection is closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_iSup_of_iInter_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty)
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨆ i, f i x) :=
  ⟨HasClosedPolyhedralEpigraph.isProper_iSup_of_nonempty_iInter_effectiveDomain
      hf hproper hdom,
    HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral
      hf hinter⟩

/-- The finite pointwise-supremum operation theorem together with the
horizon-function equality from Proposition 3.30. -/
theorem HasClosedPolyhedralEpigraph.iSup_cpl_and_horizon_eq_of_iInter_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty)
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨆ i, f i x) ∧
      horizonFunction (fun x => ⨆ i, f i x) =
        fun w => ⨆ i, horizonFunction (f i) w := by
  exact
    ⟨HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_iSup_of_iInter_closedPolyhedral
        hf hproper hdom hinter,
      HasClosedPolyhedralEpigraph.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
        hf hproper hdom⟩

/-- CPL method form of the finite pointwise-supremum epigraph criterion. -/
theorem IsConvexPiecewiseLinear.hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    HasClosedPolyhedralEpigraph (fun x : E => ⨆ i, f i x) :=
  HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral
    (fun i => (hf i).hasClosedPolyhedralEpigraph) hinter

/-- Finite pointwise suprema of convex piecewise-linear functions are convex
piecewise-linear under the closed-polyhedral epigraph-intersection criterion. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_iSup_of_iInter_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty)
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨆ i, f i x) :=
  HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_iSup_of_iInter_closedPolyhedral
    (fun i => (hf i).hasClosedPolyhedralEpigraph)
    (fun i => (hf i).isProper)
    hdom
    hinter

/-- CPL operation package for finite pointwise suprema: the result is CPL and
its horizon function is the pointwise supremum of the horizon functions. -/
theorem IsConvexPiecewiseLinear.iSup_cpl_and_horizon_eq_of_iInter_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty)
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨆ i, f i x) ∧
      horizonFunction (fun x => ⨆ i, f i x) =
        fun w => ⨆ i, horizonFunction (f i) w := by
  exact
    ⟨IsConvexPiecewiseLinear.isConvexPiecewiseLinear_iSup_of_iInter_closedPolyhedral
        hf hdom hinter,
      IsConvexPiecewiseLinear.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
        hf hdom⟩

/-- The closed-polyhedral epigraph-intersection hypothesis for a finite
pointwise supremum makes the intersection of the effective domains closed
polyhedral. -/
theorem effectiveDomain_iInter_isClosedPolyhedral_of_iInter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    IsClosedPolyhedral (⋂ i, effectiveDomain (f i)) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x : E => ⨆ i, f i x) :=
    hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral hinter
  simpa [effectiveDomain_iSup_of_finite] using hsup.effectiveDomain_isClosedPolyhedral

/-- Under the finite closed-polyhedral epigraph-intersection hypothesis, the
intersection of effective domains admits finite ordinary and direction
generators. -/
theorem exists_effectiveDomain_iInter_generators_of_iInter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    ∃ s t : Finset E,
      (⋂ i, effectiveDomain (f i)) =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x : E => ⨆ i, f i x) :=
    hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral hinter
  simpa [effectiveDomain_iSup_of_finite] using hsup.exists_effectiveDomain_generators

/-- If the finite intersection of effective domains is nonempty, the same
generators can be chosen with a nonempty ordinary generator set. -/
theorem exists_nonempty_effectiveDomain_iInter_generators_of_iInter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i)))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    ∃ s t : Finset E, s.Nonempty ∧
      (⋂ i, effectiveDomain (f i)) =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x : E => ⨆ i, f i x) :=
    hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral hinter
  simpa [effectiveDomain_iSup_of_finite] using
    hsup.exists_nonempty_effectiveDomain_generators_of_nonempty
      (by simpa [effectiveDomain_iSup_of_finite] using hdom)

/-- The finite intersection of effective domains inherits the finite
coefficient formula from the closed-polyhedral pointwise-supremum epigraph. -/
theorem exists_effectiveDomain_iInter_generator_formula_of_iInter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i))) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ (⋂ i, effectiveDomain (f i)) ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x : E => ⨆ i, f i x) :=
    hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral hinter
  simpa [effectiveDomain_iSup_of_finite] using hsup.exists_effectiveDomain_generator_formula

/-- Nonempty finite-intersection coefficient formula with a nonempty ordinary
generator set. -/
theorem exists_nonempty_effectiveDomain_iInter_generator_formula_of_iInter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hinter : IsClosedPolyhedral (⋂ i, epigraph (f i)))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ (⋂ i, effectiveDomain (f i)) ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x : E => ⨆ i, f i x) :=
    hasClosedPolyhedralEpigraph_iSup_of_iInter_closedPolyhedral hinter
  simpa [effectiveDomain_iSup_of_finite] using
    hsup.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
      (by simpa [effectiveDomain_iSup_of_finite] using hdom)

/-- Direct epigraph form of the finite pointwise infimum operation: if the
union of the epigraphs is closed polyhedral, then the pointwise infimum has a
closed polyhedral epigraph. -/
theorem hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    HasClosedPolyhedralEpigraph (fun x : E => ⨅ i, f i x) := by
  change IsClosedPolyhedral (epigraph (fun x : E => ⨅ i, f i x))
  rwa [epigraph_iInf_of_finite]

/-- Binary direct epigraph form of the pointwise minimum operation. -/
theorem hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral
    {f g : E → EReal}
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    HasClosedPolyhedralEpigraph (fun x : E => f x ⊓ g x) := by
  change IsClosedPolyhedral (epigraph (fun x : E => f x ⊓ g x))
  rwa [epigraph_inf]

/-- If a finite pointwise infimum is proper and its epigraph union is closed
polyhedral, then it is convex piecewise-linear. -/
theorem isConvexPiecewiseLinear_iInf_of_iUnion_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hproper : IsProper (fun x : E => ⨅ i, f i x))
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨅ i, f i x) :=
  ⟨hproper, hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral hunion⟩

/-- If every member of a finite nonempty family is proper and the union of the
epigraphs is closed polyhedral, then the pointwise infimum is convex
piecewise-linear. -/
theorem isConvexPiecewiseLinear_iInf_of_isProper_of_iUnion_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsProper (f i))
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨅ i, f i x) :=
  isConvexPiecewiseLinear_iInf_of_iUnion_closedPolyhedral
    (isProper_iInf_of_finite hf) hunion

/-- If a binary pointwise infimum is proper and its epigraph union is closed
polyhedral, then it is convex piecewise-linear. -/
theorem isConvexPiecewiseLinear_inf_of_union_closedPolyhedral
    {f g : E → EReal}
    (hproper : IsProper (fun x : E => f x ⊓ g x))
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    IsConvexPiecewiseLinear (fun x : E => f x ⊓ g x) :=
  ⟨hproper, hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral hunion⟩

/-- If `f` and `g` are proper and their epigraph union is closed polyhedral,
then the pointwise minimum is convex piecewise-linear. -/
theorem isConvexPiecewiseLinear_inf_of_isProper_of_union_closedPolyhedral
    {f g : E → EReal} (hf : IsProper f) (hg : IsProper g)
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    IsConvexPiecewiseLinear (fun x : E => f x ⊓ g x) :=
  isConvexPiecewiseLinear_inf_of_union_closedPolyhedral
    (isProper_inf_of_isProper hf hg) hunion

/-- Method form of the finite pointwise-infimum epigraph criterion: a
closed-polyhedral theorem for the epigraph union gives a closed-polyhedral
epigraph for the infimum. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (_hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    HasClosedPolyhedralEpigraph (fun x : E => ⨅ i, f i x) :=
  RW.hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral hunion

/-- Finite pointwise infima of closed-polyhedral-epigraph functions are convex
piecewise-linear when every member is proper and the epigraph union is closed
polyhedral. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_iInf_of_iUnion_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i))
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨅ i, f i x) :=
  ⟨isProper_iInf_of_finite hproper,
    HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral
      hf hunion⟩

/-- The finite pointwise-infimum operation theorem together with the
horizon-function equality from Proposition 3.30. -/
theorem HasClosedPolyhedralEpigraph.iInf_cpl_and_horizon_eq_of_iUnion_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i))
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨅ i, f i x) ∧
      horizonFunction (fun x => ⨅ i, f i x) =
        fun w => ⨅ i, horizonFunction (f i) w := by
  exact
    ⟨HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_iInf_of_iUnion_closedPolyhedral
        hf hproper hunion,
      horizonFunction_iInf_eq_iInf_of_finite (f := f)⟩

/-- CPL method form of the finite pointwise-infimum epigraph criterion. -/
theorem IsConvexPiecewiseLinear.hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    HasClosedPolyhedralEpigraph (fun x : E => ⨅ i, f i x) :=
  HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral
    (fun i => (hf i).hasClosedPolyhedralEpigraph) hunion

/-- Finite pointwise infima of convex piecewise-linear functions are convex
piecewise-linear under the closed-polyhedral epigraph-union criterion. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_iInf_of_iUnion_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨅ i, f i x) :=
  HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_iInf_of_iUnion_closedPolyhedral
    (fun i => (hf i).hasClosedPolyhedralEpigraph)
    (fun i => (hf i).isProper)
    hunion

/-- CPL operation package for finite pointwise infima: the result is CPL and
its horizon function is the pointwise infimum of the horizon functions. -/
theorem IsConvexPiecewiseLinear.iInf_cpl_and_horizon_eq_of_iUnion_closedPolyhedral
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    IsConvexPiecewiseLinear (fun x : E => ⨅ i, f i x) ∧
      horizonFunction (fun x => ⨅ i, f i x) =
        fun w => ⨅ i, horizonFunction (f i) w := by
  exact
    ⟨IsConvexPiecewiseLinear.isConvexPiecewiseLinear_iInf_of_iUnion_closedPolyhedral
        hf hunion,
      horizonFunction_iInf_eq_iInf_of_finite (f := f)⟩

/-- Method form of the binary pointwise-minimum epigraph criterion. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral
    {f g : E → EReal}
    (_hf : HasClosedPolyhedralEpigraph f) (_hg : HasClosedPolyhedralEpigraph g)
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    HasClosedPolyhedralEpigraph (fun x : E => f x ⊓ g x) :=
  RW.hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral hunion

/-- Binary pointwise minima of closed-polyhedral-epigraph functions are convex
piecewise-linear when both inputs are proper and the epigraph union is closed
polyhedral. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_inf_of_union_closedPolyhedral
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    IsConvexPiecewiseLinear (fun x : E => f x ⊓ g x) :=
  ⟨isProper_inf_of_isProper hproperf hproperg,
    hf.hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral hg hunion⟩

/-- The binary pointwise-minimum operation theorem together with horizon
commutation for `inf`. -/
theorem HasClosedPolyhedralEpigraph.inf_cpl_and_horizon_eq_of_union_closedPolyhedral
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    IsConvexPiecewiseLinear (fun x : E => f x ⊓ g x) ∧
      horizonFunction (fun x => f x ⊓ g x) =
        fun w => horizonFunction f w ⊓ horizonFunction g w := by
  exact
    ⟨HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_inf_of_union_closedPolyhedral
        hf hg hproperf hproperg hunion,
      horizonFunction_inf_eq_inf (f := f) (g := g)⟩

/-- CPL method form of the binary pointwise-minimum epigraph criterion. -/
theorem IsConvexPiecewiseLinear.hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    HasClosedPolyhedralEpigraph (fun x : E => f x ⊓ g x) :=
  HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral
    hf.hasClosedPolyhedralEpigraph hg.hasClosedPolyhedralEpigraph hunion

/-- Binary pointwise minima of convex piecewise-linear functions are convex
piecewise-linear under the closed-polyhedral epigraph-union criterion. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_inf_of_union_closedPolyhedral
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    IsConvexPiecewiseLinear (fun x : E => f x ⊓ g x) :=
  HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_inf_of_union_closedPolyhedral
    hf.hasClosedPolyhedralEpigraph
    hg.hasClosedPolyhedralEpigraph
    hf.isProper
    hg.isProper
    hunion

/-- CPL operation package for binary pointwise minima. -/
theorem IsConvexPiecewiseLinear.inf_cpl_and_horizon_eq_of_union_closedPolyhedral
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    IsConvexPiecewiseLinear (fun x : E => f x ⊓ g x) ∧
      horizonFunction (fun x => f x ⊓ g x) =
        fun w => horizonFunction f w ⊓ horizonFunction g w := by
  exact
    ⟨IsConvexPiecewiseLinear.isConvexPiecewiseLinear_inf_of_union_closedPolyhedral
        hf hg hunion,
      horizonFunction_inf_eq_inf (f := f) (g := g)⟩

/-- The closed-polyhedral epigraph-union hypothesis for a finite pointwise
infimum makes the union of the effective domains closed polyhedral. -/
theorem effectiveDomain_iUnion_isClosedPolyhedral_of_iUnion_closedPolyhedral
    [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    IsClosedPolyhedral (⋃ i, effectiveDomain (f i)) := by
  have hinf :
      HasClosedPolyhedralEpigraph (fun x : E => ⨅ i, f i x) :=
    hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral hunion
  simpa [effectiveDomain_iInf_of_finite] using hinf.effectiveDomain_isClosedPolyhedral

/-- Under the finite closed-polyhedral epigraph-union hypothesis, the union of
effective domains admits finite ordinary and direction generators. -/
theorem exists_effectiveDomain_iUnion_generators_of_iUnion_closedPolyhedral
    [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    ∃ s t : Finset E,
      (⋃ i, effectiveDomain (f i)) =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hinf :
      HasClosedPolyhedralEpigraph (fun x : E => ⨅ i, f i x) :=
    hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral hunion
  simpa [effectiveDomain_iInf_of_finite] using hinf.exists_effectiveDomain_generators

/-- If the finite union of effective domains is nonempty, the same generators
can be chosen with a nonempty ordinary generator set. -/
theorem exists_nonempty_effectiveDomain_iUnion_generators_of_iUnion_closedPolyhedral
    [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i)))
    (hdom : (⋃ i, effectiveDomain (f i)).Nonempty) :
    ∃ s t : Finset E, s.Nonempty ∧
      (⋃ i, effectiveDomain (f i)) =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hinf :
      HasClosedPolyhedralEpigraph (fun x : E => ⨅ i, f i x) :=
    hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral hunion
  simpa [effectiveDomain_iInf_of_finite] using
    hinf.exists_nonempty_effectiveDomain_generators_of_nonempty
      (by simpa [effectiveDomain_iInf_of_finite] using hdom)

/-- The finite union of effective domains inherits the finite coefficient
formula from the closed-polyhedral pointwise-infimum epigraph. -/
theorem exists_effectiveDomain_iUnion_generator_formula_of_iUnion_closedPolyhedral
    [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i))) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ (⋃ i, effectiveDomain (f i)) ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hinf :
      HasClosedPolyhedralEpigraph (fun x : E => ⨅ i, f i x) :=
    hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral hunion
  simpa [effectiveDomain_iInf_of_finite] using hinf.exists_effectiveDomain_generator_formula

/-- Nonempty finite-union coefficient formula with a nonempty ordinary
generator set. -/
theorem exists_nonempty_effectiveDomain_iUnion_generator_formula_of_iUnion_closedPolyhedral
    [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hunion : IsClosedPolyhedral (⋃ i, epigraph (f i)))
    (hdom : (⋃ i, effectiveDomain (f i)).Nonempty) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ (⋃ i, effectiveDomain (f i)) ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hinf :
      HasClosedPolyhedralEpigraph (fun x : E => ⨅ i, f i x) :=
    hasClosedPolyhedralEpigraph_iInf_of_iUnion_closedPolyhedral hunion
  simpa [effectiveDomain_iInf_of_finite] using
    hinf.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
      (by simpa [effectiveDomain_iInf_of_finite] using hdom)

/-- The same closed-polyhedral union hypothesis that yields a closed-polyhedral
epigraph for `f ⊓ g` also makes the effective-domain union `dom f ∪ dom g`
closed polyhedral. -/
theorem effectiveDomain_union_isClosedPolyhedral_of_union_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    IsClosedPolyhedral (effectiveDomain f ∪ effectiveDomain g) := by
  have hinf :
      HasClosedPolyhedralEpigraph (fun x => f x ⊓ g x) :=
    hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral hunion
  simpa [effectiveDomain_inf] using hinf.effectiveDomain_isClosedPolyhedral

/-- Under the same closed-polyhedral epigraph-union hypothesis, the
effective-domain union admits finite ordinary and direction generators. -/
theorem exists_effectiveDomain_union_generators_of_union_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    ∃ s t : Finset E,
      effectiveDomain f ∪ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hinf :
      HasClosedPolyhedralEpigraph (fun x => f x ⊓ g x) :=
    hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral hunion
  simpa [effectiveDomain_inf] using hinf.exists_effectiveDomain_generators

/-- If `dom f ∪ dom g` is nonempty, the same closed-polyhedral union hypothesis
gives an ordinary generator description with a nonempty finite point set. -/
theorem exists_nonempty_effectiveDomain_union_generators_of_union_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g))
    (hdom : (effectiveDomain f ∪ effectiveDomain g).Nonempty) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∪ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hinf :
      HasClosedPolyhedralEpigraph (fun x => f x ⊓ g x) :=
    hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral hunion
  simpa [effectiveDomain_inf] using
    hinf.exists_nonempty_effectiveDomain_generators_of_nonempty
      (by simpa [effectiveDomain_inf] using hdom)

/-- The effective-domain union also inherits the finite coefficient formula
from the closed-polyhedral `inf` epigraph. -/
theorem exists_effectiveDomain_union_generator_formula_of_union_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g)) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∪ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hinf :
      HasClosedPolyhedralEpigraph (fun x => f x ⊓ g x) :=
    hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral hunion
  simpa [effectiveDomain_inf] using hinf.exists_effectiveDomain_generator_formula

/-- If `dom f ∪ dom g` is nonempty, the same coefficient formula can be chosen
with a nonempty ordinary generator set. -/
theorem exists_nonempty_effectiveDomain_union_generator_formula_of_union_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hunion : IsClosedPolyhedral (epigraph f ∪ epigraph g))
    (hdom : (effectiveDomain f ∪ effectiveDomain g).Nonempty) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∪ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hinf :
      HasClosedPolyhedralEpigraph (fun x => f x ⊓ g x) :=
    hasClosedPolyhedralEpigraph_inf_of_union_closedPolyhedral hunion
  simpa [effectiveDomain_inf] using
    hinf.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
      (by simpa [effectiveDomain_inf] using hdom)

/-- If the scalar-height model for `f ⊔ g` has a polyhedral epigraph, then the
pointwise supremum itself has a closed polyhedral epigraph. This isolates the
remaining structural step in the `max` part of Proposition `3.55(b)`. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hpoly : HasPolyhedralEpigraph (supHeightIntegrand f g)) :
    HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) := by
  have hreg :=
    hf.supHeightIntegrand_regular_of_nonempty_effectiveDomain_inter
      hg hproperf hproperg hdom
  have hclosedInt : HasClosedPolyhedralEpigraph (supHeightIntegrand f g) :=
    hpoly.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous hreg.2.1
  have hval :
      HasClosedPolyhedralEpigraph
        (valueFunction (E := ℝ) (F := E) (supHeightIntegrand f g)) :=
    hclosedInt.hasClosedPolyhedralEpigraph_valueFunction_of_lsc_localUniform
      hreg.2.2.1
  simpa [hreg.2.2.2] using hval

/-- A polyhedral scalar-height model is enough to conclude that `f ⊔ g` is
convex piecewise-linear. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hpoly : HasPolyhedralEpigraph (supHeightIntegrand f g)) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hreg :=
    hf.sup_regular_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  refine ⟨hreg.1, ?_⟩
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
      hg hproperf hproperg hdom hpoly

/-- Top-level reduction of the CPL `max` theorem to polyhedrality of the
scalar-height model. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hpoly : HasPolyhedralEpigraph (supHeightIntegrand f g)) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hclosedf : HasClosedPolyhedralEpigraph f := hf.hasClosedPolyhedralEpigraph
  exact
    hclosedf.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
      hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hpoly

/-- A polyhedral intersection theorem for `epi f ∩ epi g` is enough to conclude
that `f ⊔ g` has a closed polyhedral epigraph. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_polyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsPolyhedral (epigraph f ∩ epigraph g)) :
    HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) := by
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
      hg hproperf hproperg hdom
      (hasPolyhedralEpigraph_supHeightIntegrand_of_isPolyhedral_inter_epigraph hinter)

/-- A polyhedral intersection theorem for `epi f ∩ epi g` is enough to conclude
that `f ⊔ g` is convex piecewise-linear. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_inter_polyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsPolyhedral (epigraph f ∩ epigraph g)) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  exact
    hf.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_supHeightIntegrand_polyhedral
      hg hdom
      (hasPolyhedralEpigraph_supHeightIntegrand_of_isPolyhedral_inter_epigraph hinter)

/-- A closed-polyhedral intersection theorem for `epi f ∩ epi g` is enough to
conclude that `f ⊔ g` has a closed polyhedral epigraph. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) := by
  have hreg :=
    hf.supHeightIntegrand_regular_of_nonempty_effectiveDomain_inter
      hg hproperf hproperg hdom
  have hclosedInt : HasClosedPolyhedralEpigraph (supHeightIntegrand f g) :=
    hasClosedPolyhedralEpigraph_supHeightIntegrand_of_isClosedPolyhedral_inter_epigraph hinter
  have hval :
      HasClosedPolyhedralEpigraph
        (valueFunction (E := ℝ) (F := E) (supHeightIntegrand f g)) :=
    hclosedInt.hasClosedPolyhedralEpigraph_valueFunction_of_lsc_localUniform
      hreg.2.2.1
  simpa [hreg.2.2.2] using hval

/-- A closed-polyhedral intersection theorem for `epi f ∩ epi g` is enough to
conclude that `f ⊔ g` is convex piecewise-linear. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hreg := hf.sup_regular_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  refine ⟨hreg.1, ?_⟩
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- The same closed-polyhedral intersection hypothesis that yields a
closed-polyhedral epigraph for `f ⊔ g` also makes the effective-domain
intersection `dom f ∩ dom g` closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter
  simpa [effectiveDomain_sup] using hsup.effectiveDomain_isClosedPolyhedral

/-- Under the same closed-polyhedral epigraph-intersection hypothesis, the
effective-domain intersection admits finite ordinary and direction
generators. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter
  simpa [effectiveDomain_sup] using hsup.exists_effectiveDomain_generators

/-- If the effective-domain intersection is nonempty, the same hypothesis gives
an ordinary generator description with a nonempty finite point set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter
  simpa [effectiveDomain_sup] using
    hsup.exists_nonempty_effectiveDomain_generators_of_nonempty
      (by simpa [effectiveDomain_sup] using hdom)

/-- The effective-domain intersection also inherits the finite coefficient
formula from the closed-polyhedral `sup` epigraph. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter
  simpa [effectiveDomain_sup] using hsup.exists_effectiveDomain_generator_formula

/-- If `dom f ∩ dom g` is nonempty, the same coefficient formula can be chosen
with a nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter
  simpa [effectiveDomain_sup] using
    hsup.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
      (by simpa [effectiveDomain_sup] using hdom)

/-- A closed-polyhedral theorem for the product epigraphs intersected with the
diagonal already implies the closed-polyhedral epigraph theorem for `f ⊔ g`. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) := by
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- Product-epigraph intersection with the diagonal is enough to conclude that
`f ⊔ g` is convex piecewise-linear at the closed-polyhedral middle layer. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hreg := hf.sup_regular_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  refine ⟨hreg.1, ?_⟩
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_prod_inter_diagonal
      hg hproperf hproperg hdom hdiag

/-- The product-diagonal closed-polyhedral criterion also makes the common
effective domain closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) := by
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.effectiveDomain_inter_isClosedPolyhedral_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- Under the product-diagonal closed-polyhedral criterion, the common
effective domain admits finite ordinary and direction generators. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.exists_effectiveDomain_inter_generators_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- Under the product-diagonal closed-polyhedral criterion, a nonempty common
effective domain admits finite generators with a nonempty ordinary generator
set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.exists_nonempty_effectiveDomain_inter_generators_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- Under the product-diagonal closed-polyhedral criterion, the common
effective domain inherits a finite coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.exists_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- Under the product-diagonal closed-polyhedral criterion, the finite
coefficient formula for the common effective domain can be chosen with a
nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    IsClosedPolyhedral.inter_of_prod_inter_diagonal
      (E := E × ℝ) (C := epigraph f) (D := epigraph g) hdiag
  exact
    hf.exists_nonempty_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- A finitely generated ray-space cone intersection for `epi f` and `epi g`
is enough to conclude that `f ⊔ g` has a closed polyhedral epigraph. This
packages the new set-side ray-space reduction directly at the function layer. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) := by
  have hreg := hf.sup_regular_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  have hne_inter : (epigraph f ∩ epigraph g).Nonempty := by
    simpa [epigraph_sup] using epigraph_nonempty_of_isProper hreg.1
  have hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g) :=
    hf.inter_of_isFinitelyGeneratedCone_raySpaceCone_inter hg hne_inter hRay
  exact
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg hproperf hproperg hdom hinter

/-- The ray-space finite-generation criterion for `epi f ∩ epi g` also makes
`dom f ∩ dom g` closed polyhedral. -/
theorem HasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_sup] using hsup.effectiveDomain_isClosedPolyhedral

/-- Under the ray-space finite-generation criterion for `epi f ∩ epi g`, the
effective-domain intersection admits finite ordinary and direction generators.
-/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_sup] using hsup.exists_effectiveDomain_generators

/-- Under the ray-space finite-generation criterion for `epi f ∩ epi g`, a
nonempty effective-domain intersection admits finite generators with a nonempty
ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_sup] using
    hsup.exists_nonempty_effectiveDomain_generators_of_nonempty
      (by simpa [effectiveDomain_sup] using hdom)

/-- Under the ray-space finite-generation criterion for `epi f ∩ epi g`, the
effective-domain intersection inherits the finite coefficient formula. -/
theorem HasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_sup] using hsup.exists_effectiveDomain_generator_formula

/-- Under the ray-space finite-generation criterion for `epi f ∩ epi g`, the
finite coefficient formula for a nonempty effective-domain intersection can be
chosen with a nonempty ordinary generator set. -/
theorem HasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x := by
  have hsup :
      HasClosedPolyhedralEpigraph (fun x => f x ⊔ g x) :=
    hf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg hproperf hproperg hdom hRay
  simpa [effectiveDomain_sup] using
    hsup.exists_nonempty_effectiveDomain_generator_formula_of_nonempty
      (by simpa [effectiveDomain_sup] using hdom)

/-- Top-level CPL consequence of a closed-polyhedral theorem for
`epi f ∩ epi g`. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hclosedf : HasClosedPolyhedralEpigraph f := hf.hasClosedPolyhedralEpigraph
  exact
    hclosedf.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_inter_closedPolyhedral
      hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Top-level CPL version: a closed-polyhedral theorem for `epi f ∩ epi g`
makes the common effective domain closed polyhedral. -/
theorem IsConvexPiecewiseLinear.effectiveDomain_inter_isClosedPolyhedral_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) :=
  hf.hasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_inter_closedPolyhedral
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Top-level CPL version: a closed-polyhedral theorem for `epi f ∩ epi g`
gives finite generators for the common effective domain. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Top-level CPL version: a nonempty common effective domain admits finite
generators with a nonempty ordinary generator set under the closed-polyhedral
epigraph-intersection hypothesis. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_inter_closedPolyhedral
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Top-level CPL version: the common effective domain inherits the finite
coefficient formula from a closed-polyhedral theorem for `epi f ∩ epi g`. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Top-level CPL version: the finite coefficient formula for the common
effective domain can be chosen with a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hinter : IsClosedPolyhedral (epigraph f ∩ epigraph g)) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_inter_closedPolyhedral
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hinter

/-- Product-epigraph intersection with the diagonal is enough to conclude that
`f ⊔ g` is convex piecewise-linear. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hclosedf : HasClosedPolyhedralEpigraph f := hf.hasClosedPolyhedralEpigraph
  exact
    HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_prod_inter_diagonal
      hclosedf hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: the product-diagonal closed-polyhedral criterion
makes the common effective domain closed polyhedral. -/
theorem IsConvexPiecewiseLinear.effectiveDomain_inter_isClosedPolyhedral_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) :=
  hf.hasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_prod_inter_diagonal
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: the product-diagonal closed-polyhedral criterion
gives finite generators for the common effective domain. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generators_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_prod_inter_diagonal
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: under the product-diagonal closed-polyhedral
criterion, a nonempty common effective domain admits finite generators with a
nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generators_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_prod_inter_diagonal
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: under the product-diagonal closed-polyhedral
criterion, the common effective domain inherits a finite coefficient formula.
-/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL version: under the product-diagonal closed-polyhedral
criterion, the common effective-domain coefficient formula can be chosen with
a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hdiag :
      IsClosedPolyhedral
        (((epigraph f) ×ˢ (epigraph g)) ∩
          {p : (E × ℝ) × (E × ℝ) | p.1 = p.2})) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_prod_inter_diagonal
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hdiag

/-- Top-level CPL consequence of the ray-space finite-generation criterion for
`epi f ∩ epi g`. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    IsConvexPiecewiseLinear (fun x => f x ⊔ g x) := by
  have hclosedf : HasClosedPolyhedralEpigraph f := hf.hasClosedPolyhedralEpigraph
  refine ⟨hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hdom, ?_⟩
  exact
    hclosedf.hasClosedPolyhedralEpigraph_sup_of_nonempty_effectiveDomain_inter_of_isFinitelyGeneratedCone_raySpaceCone_inter
      hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: the ray-space finite-generation criterion for
`epi f ∩ epi g` makes `dom f ∩ dom g` closed polyhedral. -/
theorem IsConvexPiecewiseLinear.effectiveDomain_inter_isClosedPolyhedral_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    IsClosedPolyhedral (effectiveDomain f ∩ effectiveDomain g) :=
  hf.hasClosedPolyhedralEpigraph.effectiveDomain_inter_isClosedPolyhedral_of_isFinitelyGeneratedCone_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the ray-space finite-generation criterion for
`epi f ∩ epi g`, the effective-domain intersection admits finite generators. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E,
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the ray-space finite-generation criterion for
`epi f ∩ epi g`, a nonempty effective-domain intersection admits finite
generators with a nonempty ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E, s.Nonempty ∧
      effectiveDomain f ∩ effectiveDomain g =
        extendedConvexHull (↑s : Set E) (↑t : Set E) :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generators_of_isFinitelyGeneratedCone_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the ray-space finite-generation criterion for
`epi f ∩ epi g`, the effective-domain intersection inherits the finite
coefficient formula. -/
theorem IsConvexPiecewiseLinear.exists_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E,
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  hf.hasClosedPolyhedralEpigraph.exists_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Top-level CPL version: under the ray-space finite-generation criterion for
`epi f ∩ epi g`, the finite coefficient formula can be chosen with a nonempty
ordinary generator set. -/
theorem IsConvexPiecewiseLinear.exists_nonempty_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hRay :
      IsFinitelyGeneratedCone
        (raySpaceCone (epigraph f) (horizonCone (epigraph f)) ∩
          raySpaceCone (epigraph g) (horizonCone (epigraph g)))) :
    ∃ s t : Finset E, s.Nonempty ∧
      ∀ {x : E},
        x ∈ effectiveDomain f ∩ effectiveDomain g ↔
          ∃ w : E → ℝ,
            (∀ y ∈ s, 0 ≤ w y) ∧
            ∑ y ∈ s, w y = 1 ∧
            ∃ c : E →₀ ℝ,
              ↑c.support ⊆ (↑t : Set E) ∧
              (∀ y, 0 ≤ c y) ∧
              (∑ y ∈ s, w y • y) + c.sum (fun y r => r • y) = x :=
  hf.hasClosedPolyhedralEpigraph.exists_nonempty_effectiveDomain_inter_generator_formula_of_isFinitelyGeneratedCone_raySpaceCone_inter
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper hdom hRay

/-- Closed polyhedral epigraphs are stable under separated addition on a
product space. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_separatedAdd
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g) :
    HasClosedPolyhedralEpigraph (fun p : E × E => f p.1 + g p.2) := by
  have hsep : HasClosedPolyhedralEpigraph (RW.epiSumIntegrand f g) :=
    HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSumIntegrand
      (hf.hasPolyhedralEpigraph) (hg.hasPolyhedralEpigraph)
      hf.lowerSemicontinuous hg.lowerSemicontinuous hproperf hproperg
  simpa [separatedAddLinearEquiv, RW.epiSumIntegrand, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    hsep.hasClosedPolyhedralEpigraph_precompose_linearEquiv
      (separatedAddLinearEquiv (E := E))

/-- Convex piecewise-linearity is stable under separated addition on a product
space. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_separatedAdd
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    IsConvexPiecewiseLinear (fun p : E × E => f p.1 + g p.2) := by
  refine ⟨?_, hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_separatedAdd
    hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper⟩
  simpa [separatedAddLinearEquiv, RW.epiSumIntegrand, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    isProper_precompose_linearEquiv
      (isProper_epiSumIntegrand hf.isProper hg.isProper)
      (separatedAddLinearEquiv (E := E))

end RW
