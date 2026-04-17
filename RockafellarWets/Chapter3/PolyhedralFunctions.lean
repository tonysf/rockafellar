/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Polyhedral Epigraphs

This file packages the function-side language for the polyhedral tail of
Chapter 3:
- functions with polyhedral epigraphs;
- functions with closed polyhedral epigraphs;
- the resulting lower-semicontinuity and convexity consequences;
- the project wrapper for proper convex piecewise-linear functions.
-/

import RockafellarWets.Chapter1.Semicontinuity
import RockafellarWets.Chapter3.GeneratedSets
import RockafellarWets.Chapter3.Pointwise
import RockafellarWets.Chapter3.PositiveHomogeneity

open Set EReal
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function has a polyhedral epigraph if its real epigraph is polyhedral in
the Chapter 3 generated-set sense. -/
abbrev HasPolyhedralEpigraph (f : E → EReal) : Prop :=
  IsPolyhedral (epigraph f)

/-- A function has a closed polyhedral epigraph if its real epigraph is closed
polyhedral in the Chapter 3 generated-set sense. -/
abbrev HasClosedPolyhedralEpigraph (f : E → EReal) : Prop :=
  IsClosedPolyhedral (epigraph f)

/-- Project wrapper for proper convex piecewise-linear functions: properness
plus a closed polyhedral epigraph. -/
abbrev IsConvexPiecewiseLinear (f : E → EReal) : Prop :=
  IsProper f ∧ HasClosedPolyhedralEpigraph f

theorem HasPolyhedralEpigraph.convex {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    Convex ℝ (epigraph f) :=
  IsPolyhedral.convex hf

theorem HasPolyhedralEpigraph.exists_generators {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    ∃ s t : Finset (E × ℝ),
      epigraph f = extendedConvexHull (↑s : Set (E × ℝ)) (↑t : Set (E × ℝ)) :=
  hf

theorem HasPolyhedralEpigraph.closure_isClosedPolyhedral {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    IsClosedPolyhedral (closure (epigraph f)) :=
  IsPolyhedral.closure_isClosedPolyhedral hf

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_of_isClosed {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hclosed : IsClosed (epigraph f)) :
    HasClosedPolyhedralEpigraph f :=
  IsPolyhedral.isClosedPolyhedral_of_isClosed hf hclosed

theorem HasPolyhedralEpigraph.hasClosedPolyhedralEpigraph_of_lowerSemicontinuous
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (hlsc : LowerSemicontinuous f) :
    HasClosedPolyhedralEpigraph f :=
  hf.hasClosedPolyhedralEpigraph_of_isClosed (isClosed_epigraph_of_lsc_ereal f hlsc)

theorem IsPolyhedral.hasPolyhedralEpigraph_indicatorVA {C : Set E}
    (hC : IsPolyhedral C) :
    HasPolyhedralEpigraph (indicatorVA C) := by
  change IsPolyhedral (epigraph (indicatorVA C))
  rw [epigraph_indicatorVA]
  exact hC.prod IsPolyhedral.Ici_zero

theorem IsClosedPolyhedral.hasClosedPolyhedralEpigraph_indicatorVA {C : Set E}
    [FiniteDimensional ℝ E]
    (hC : IsClosedPolyhedral C) :
    HasClosedPolyhedralEpigraph (indicatorVA C) := by
  change IsClosedPolyhedral (epigraph (indicatorVA C))
  rw [epigraph_indicatorVA]
  exact hC.prod IsClosedPolyhedral.Ici_zero

theorem HasClosedPolyhedralEpigraph.isClosed {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    IsClosed (epigraph f) :=
  IsClosedPolyhedral.isClosed hf

theorem HasClosedPolyhedralEpigraph.convex {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    Convex ℝ (epigraph f) :=
  IsClosedPolyhedral.convex hf

theorem HasClosedPolyhedralEpigraph.exists_generators {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    ∃ s t : Finset (E × ℝ),
      epigraph f =
        convexHull ℝ (↑s : Set (E × ℝ)) +
          closure (conicHull (↑t : Set (E × ℝ))) :=
  hf

theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    LowerSemicontinuous f :=
  lowerSemicontinuous_of_isClosed_epigraph_ereal f hf.isClosed

theorem HasPolyhedralEpigraph.effectiveDomain_isPolyhedral {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) :
    IsPolyhedral (effectiveDomain f) := by
  rw [← epigraph_proj_eq_effectiveDomain f]
  exact hf.linear_image (LinearMap.fst ℝ E ℝ)

theorem HasClosedPolyhedralEpigraph.effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    IsClosedPolyhedral (effectiveDomain f) := by
  rw [← epigraph_proj_eq_effectiveDomain f]
  exact hf.linear_image (LinearMap.fst ℝ E ℝ)

theorem HasClosedPolyhedralEpigraph.hasPolyhedralEpigraph [FiniteDimensional ℝ E]
    {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) :
    HasPolyhedralEpigraph f :=
  IsClosedPolyhedral.isPolyhedral hf

theorem hasPolyhedralEpigraph_zero [FiniteDimensional ℝ E] :
    HasPolyhedralEpigraph (fun _ : E => (0 : EReal)) := by
  have hzero : indicatorVA (Set.univ : Set E) = (fun _ : E => (0 : EReal)) := by
    funext x
    simp [indicatorVA]
  simpa [hzero] using
    (IsPolyhedral.univ (E := E)).hasPolyhedralEpigraph_indicatorVA

theorem hasClosedPolyhedralEpigraph_zero [FiniteDimensional ℝ E] :
    HasClosedPolyhedralEpigraph (fun _ : E => (0 : EReal)) := by
  have hzero : indicatorVA (Set.univ : Set E) = (fun _ : E => (0 : EReal)) := by
    funext x
    simp [indicatorVA]
  simpa [hzero] using
    (IsClosedPolyhedral.univ (E := E)).hasClosedPolyhedralEpigraph_indicatorVA

theorem isProper_zero : IsProper (fun _ : E => (0 : EReal)) := by
  constructor
  · exact ⟨0, by simp⟩
  · intro x
    simp

theorem lowerSemicontinuous_zero : LowerSemicontinuous (fun _ : E => (0 : EReal)) := by
  simpa using
    (continuous_const : Continuous (fun _ : E => ((0 : ℝ) : EReal))).lowerSemicontinuous

theorem isConvexPiecewiseLinear_zero [FiniteDimensional ℝ E] :
    IsConvexPiecewiseLinear (fun _ : E => (0 : EReal)) :=
  ⟨isProper_zero, hasClosedPolyhedralEpigraph_zero⟩

theorem IsClosedPolyhedral.isConvexPiecewiseLinear_indicatorVA
    [FiniteDimensional ℝ E] {C : Set E}
    (hC : IsClosedPolyhedral C) (hCne : C.Nonempty) :
    IsConvexPiecewiseLinear (indicatorVA C) := by
  refine ⟨(indicatorVA_isProper_iff C).2 hCne, ?_⟩
  exact hC.hasClosedPolyhedralEpigraph_indicatorVA

theorem IsConvexPiecewiseLinear.isProper {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsProper f :=
  hf.1

theorem IsConvexPiecewiseLinear.hasClosedPolyhedralEpigraph {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    HasClosedPolyhedralEpigraph f :=
  hf.2

theorem IsConvexPiecewiseLinear.isClosed_epigraph {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosed (epigraph f) :=
  hf.2.isClosed

theorem IsConvexPiecewiseLinear.lowerSemicontinuous {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    LowerSemicontinuous f :=
  hf.2.lowerSemicontinuous

theorem IsConvexPiecewiseLinear.effectiveDomain_isClosedPolyhedral
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsClosedPolyhedral (effectiveDomain f) :=
  hf.2.effectiveDomain_isClosedPolyhedral

theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_indicatorVA_effectiveDomain
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    IsConvexPiecewiseLinear (indicatorVA (effectiveDomain f)) := by
  refine IsClosedPolyhedral.isConvexPiecewiseLinear_indicatorVA
    (hC := hf.effectiveDomain_isClosedPolyhedral) ?_
  exact hf.isProper.1

theorem HasClosedPolyhedralEpigraph.isProper_sup_of_nonempty_effectiveDomain_inter
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x => f x ⊔ g x) :=
  isProper_sup_of_isProper_of_nonempty_effectiveDomain_inter hproperf hproperg hdom

theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous_sup
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g) :
    LowerSemicontinuous (fun x => f x ⊔ g x) :=
  RW.lowerSemicontinuous_sup hf.lowerSemicontinuous hg.lowerSemicontinuous

theorem HasClosedPolyhedralEpigraph.convex_epigraph_sup
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g) :
    Convex ℝ (epigraph (fun x => f x ⊔ g x)) :=
  RW.convex_epigraph_sup hf.convex hg.convex

theorem HasClosedPolyhedralEpigraph.horizonFunction_sup_eq_sup_of_nonempty_effectiveDomain_inter
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    horizonFunction (fun x => f x ⊔ g x) = fun w => horizonFunction f w ⊔ horizonFunction g w := by
  have hproperSup :
      IsProper (fun x => f x ⊔ g x) :=
    hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom
  exact RW.horizonFunction_sup_eq_sup
    hf.convex
    hg.convex
    hf.lowerSemicontinuous
    hg.lowerSemicontinuous
    hproperf
    hproperg
    (epigraph_nonempty_of_isProper hproperSup)

theorem HasClosedPolyhedralEpigraph.sup_regular_of_nonempty_effectiveDomain_inter
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x => f x ⊔ g x) ∧
      LowerSemicontinuous (fun x => f x ⊔ g x) ∧
      Convex ℝ (epigraph (fun x => f x ⊔ g x)) ∧
      horizonFunction (fun x => f x ⊔ g x) = fun w => horizonFunction f w ⊔ horizonFunction g w := by
  refine ⟨hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom, ?_, ?_, ?_⟩
  · exact hf.lowerSemicontinuous_sup hg
  · exact hf.convex_epigraph_sup hg
  · exact hf.horizonFunction_sup_eq_sup_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom

theorem IsConvexPiecewiseLinear.isProper_sup_of_nonempty_effectiveDomain_inter
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x => f x ⊔ g x) :=
  isProper_sup_of_isProper_of_nonempty_effectiveDomain_inter hf.isProper hg.isProper hdom

theorem IsConvexPiecewiseLinear.lowerSemicontinuous_sup
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    LowerSemicontinuous (fun x => f x ⊔ g x) :=
  RW.lowerSemicontinuous_sup hf.lowerSemicontinuous hg.lowerSemicontinuous

theorem IsConvexPiecewiseLinear.convex_epigraph_sup
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    Convex ℝ (epigraph (fun x => f x ⊔ g x)) :=
  RW.convex_epigraph_sup hf.2.convex hg.2.convex

theorem IsConvexPiecewiseLinear.horizonFunction_sup_eq_sup_of_nonempty_effectiveDomain_inter
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    horizonFunction (fun x => f x ⊔ g x) = fun w => horizonFunction f w ⊔ horizonFunction g w := by
  have hproperSup :
      IsProper (fun x => f x ⊔ g x) :=
    hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hdom
  exact RW.horizonFunction_sup_eq_sup
    hf.2.convex
    hg.2.convex
    hf.lowerSemicontinuous
    hg.lowerSemicontinuous
    hf.isProper
    hg.isProper
    (epigraph_nonempty_of_isProper hproperSup)

theorem IsConvexPiecewiseLinear.sup_regular_of_nonempty_effectiveDomain_inter
    {f g : E → EReal} (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x => f x ⊔ g x) ∧
      LowerSemicontinuous (fun x => f x ⊔ g x) ∧
      Convex ℝ (epigraph (fun x => f x ⊔ g x)) ∧
      horizonFunction (fun x => f x ⊔ g x) = fun w => horizonFunction f w ⊔ horizonFunction g w := by
  refine ⟨hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hdom, ?_, ?_, ?_⟩
  · exact hf.lowerSemicontinuous_sup hg
  · exact hf.convex_epigraph_sup hg
  · exact hf.horizonFunction_sup_eq_sup_of_nonempty_effectiveDomain_inter hg hdom

theorem IsConvexPiecewiseLinear.convex_epigraph {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    Convex ℝ (epigraph f) :=
  hf.2.convex

theorem IsConvexPiecewiseLinear.exists_epigraph_generators {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∃ s t : Finset (E × ℝ),
      epigraph f =
        convexHull ℝ (↑s : Set (E × ℝ)) +
          closure (conicHull (↑t : Set (E × ℝ))) :=
  hf.2

theorem IsConvexPiecewiseLinear.convex_inequality {f : E → EReal}
    (hf : IsConvexPiecewiseLinear f) :
    ∀ ⦃x y : E⦄ ⦃a b : ℝ⦄,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y :=
  convex_inequality_of_convex_epigraph_of_ne_bot hf.convex_epigraph
    (fun x => ne_of_gt (hf.1.2 x))

end RW
