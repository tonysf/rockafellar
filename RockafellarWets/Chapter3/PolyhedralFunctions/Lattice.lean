/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Lattice Operations on Polyhedral Functions

This file packages finite pointwise supremum and infimum regularity for polyhedral functions.
-/

import RockafellarWets.Chapter3.PolyhedralFunctions.Generated

open Set EReal
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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
    horizonFunction (fun x => f x ⊔ g x) =
      fun w => horizonFunction f w ⊔ horizonFunction g w := by
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
      horizonFunction (fun x => f x ⊔ g x) =
        fun w => horizonFunction f w ⊔ horizonFunction g w := by
  refine
    ⟨hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom,
      ?_, ?_, ?_⟩
  · exact hf.lowerSemicontinuous_sup hg
  · exact hf.convex_epigraph_sup hg
  · exact hf.horizonFunction_sup_eq_sup_of_nonempty_effectiveDomain_inter hg hproperf hproperg hdom

/-- Finite pointwise suprema of proper closed-polyhedral-epigraph functions are
proper when the effective domains have a common point. -/
theorem HasClosedPolyhedralEpigraph.isProper_iSup_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (_hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    IsProper (fun x => ⨆ i, f i x) :=
  isProper_iSup_of_finite_of_isProper_of_nonempty_iInter_effectiveDomain hproper hdom

/-- Lower semicontinuity is preserved by finite pointwise suprema of
closed-polyhedral-epigraph functions. -/
theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous_iSup
    {ι : Type*} {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i)) :
    LowerSemicontinuous (fun x => ⨆ i, f i x) :=
  RW.lowerSemicontinuous_iSup fun i => (hf i).lowerSemicontinuous

/-- Convex epigraphs are preserved by finite pointwise suprema of
closed-polyhedral-epigraph functions. -/
theorem HasClosedPolyhedralEpigraph.convex_epigraph_iSup
    {ι : Type*} {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i)) :
    Convex ℝ (epigraph (fun x => ⨆ i, f i x)) :=
  RW.convex_epigraph_iSup fun i => (hf i).convex

/-- Finite-family form of Proposition 3.30 for closed-polyhedral-epigraph
functions: under a common effective-domain point, the horizon function commutes
with the pointwise supremum. -/
theorem HasClosedPolyhedralEpigraph.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    horizonFunction (fun x => ⨆ i, f i x) = fun w => ⨆ i, horizonFunction (f i) w := by
  have hproperSup :
      IsProper (fun x => ⨆ i, f i x) :=
    HasClosedPolyhedralEpigraph.isProper_iSup_of_nonempty_iInter_effectiveDomain
      hf hproper hdom
  exact RW.horizonFunction_iSup_eq_iSup
    (fun i => (hf i).convex)
    (fun i => (hf i).lowerSemicontinuous)
    hproper
    (epigraph_nonempty_of_isProper hproperSup)

/-- Regularity package for finite pointwise suprema of closed-polyhedral-epigraph
functions with a common finite-domain point. -/
theorem HasClosedPolyhedralEpigraph.iSup_regular_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    IsProper (fun x => ⨆ i, f i x) ∧
      LowerSemicontinuous (fun x => ⨆ i, f i x) ∧
      Convex ℝ (epigraph (fun x => ⨆ i, f i x)) ∧
      horizonFunction (fun x => ⨆ i, f i x) = fun w => ⨆ i, horizonFunction (f i) w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      HasClosedPolyhedralEpigraph.isProper_iSup_of_nonempty_iInter_effectiveDomain
        hf hproper hdom
  · exact HasClosedPolyhedralEpigraph.lowerSemicontinuous_iSup hf
  · exact HasClosedPolyhedralEpigraph.convex_epigraph_iSup hf
  · exact
      HasClosedPolyhedralEpigraph.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
        hf hproper hdom

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
    horizonFunction (fun x => f x ⊔ g x) =
      fun w => horizonFunction f w ⊔ horizonFunction g w := by
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
      horizonFunction (fun x => f x ⊔ g x) =
        fun w => horizonFunction f w ⊔ horizonFunction g w := by
  refine ⟨hf.isProper_sup_of_nonempty_effectiveDomain_inter hg hdom, ?_, ?_, ?_⟩
  · exact hf.lowerSemicontinuous_sup hg
  · exact hf.convex_epigraph_sup hg
  · exact hf.horizonFunction_sup_eq_sup_of_nonempty_effectiveDomain_inter hg hdom

/-- Finite pointwise suprema of convex piecewise-linear functions are proper
when the effective domains have a common point. -/
theorem IsConvexPiecewiseLinear.isProper_iSup_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    IsProper (fun x => ⨆ i, f i x) :=
  isProper_iSup_of_finite_of_isProper_of_nonempty_iInter_effectiveDomain
    (fun i => (hf i).isProper) hdom

/-- Lower semicontinuity is preserved by finite pointwise suprema of convex
piecewise-linear functions. -/
theorem IsConvexPiecewiseLinear.lowerSemicontinuous_iSup
    {ι : Type*} {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    LowerSemicontinuous (fun x => ⨆ i, f i x) :=
  RW.lowerSemicontinuous_iSup fun i => (hf i).lowerSemicontinuous

/-- Convex epigraphs are preserved by finite pointwise suprema of convex
piecewise-linear functions. -/
theorem IsConvexPiecewiseLinear.convex_epigraph_iSup
    {ι : Type*} {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    Convex ℝ (epigraph (fun x => ⨆ i, f i x)) :=
  RW.convex_epigraph_iSup fun i => (hf i).hasClosedPolyhedralEpigraph.convex

/-- Finite-family form of Proposition 3.30 for convex piecewise-linear
functions with a common effective-domain point. -/
theorem IsConvexPiecewiseLinear.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    horizonFunction (fun x => ⨆ i, f i x) = fun w => ⨆ i, horizonFunction (f i) w :=
  HasClosedPolyhedralEpigraph.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
    (fun i => (hf i).hasClosedPolyhedralEpigraph)
    (fun i => (hf i).isProper)
    hdom

/-- Regularity package for finite pointwise suprema of convex piecewise-linear
functions with a common finite-domain point. -/
theorem IsConvexPiecewiseLinear.iSup_regular_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    IsProper (fun x => ⨆ i, f i x) ∧
      LowerSemicontinuous (fun x => ⨆ i, f i x) ∧
      Convex ℝ (epigraph (fun x => ⨆ i, f i x)) ∧
      horizonFunction (fun x => ⨆ i, f i x) = fun w => ⨆ i, horizonFunction (f i) w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IsConvexPiecewiseLinear.isProper_iSup_of_nonempty_iInter_effectiveDomain hf hdom
  · exact IsConvexPiecewiseLinear.lowerSemicontinuous_iSup hf
  · exact IsConvexPiecewiseLinear.convex_epigraph_iSup hf
  · exact
      IsConvexPiecewiseLinear.horizonFunction_iSup_eq_iSup_of_nonempty_iInter_effectiveDomain
        hf hdom

theorem HasClosedPolyhedralEpigraph.isProper_inf_of_closedPolyhedralEpigraph
    {f g : E → EReal}
    (_hf : HasClosedPolyhedralEpigraph f) (_hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g) :
    IsProper (fun x => f x ⊓ g x) :=
  isProper_inf_of_isProper hproperf hproperg

theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous_inf_of_closedPolyhedralEpigraph
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g) :
    LowerSemicontinuous (fun x => f x ⊓ g x) :=
  RW.lowerSemicontinuous_inf hf.lowerSemicontinuous hg.lowerSemicontinuous

theorem HasClosedPolyhedralEpigraph.horizonFunction_inf_eq_inf_of_closedPolyhedralEpigraph
    {f g : E → EReal}
    (_hf : HasClosedPolyhedralEpigraph f) (_hg : HasClosedPolyhedralEpigraph g) :
    horizonFunction (fun x => f x ⊓ g x) =
      fun w => horizonFunction f w ⊓ horizonFunction g w :=
  RW.horizonFunction_inf_eq_inf

/-- Regularity package for binary pointwise infima of proper
closed-polyhedral-epigraph functions. -/
theorem HasClosedPolyhedralEpigraph.inf_regular
    {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f) (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g) :
    IsProper (fun x => f x ⊓ g x) ∧
      LowerSemicontinuous (fun x => f x ⊓ g x) ∧
      horizonFunction (fun x => f x ⊓ g x) =
        fun w => horizonFunction f w ⊓ horizonFunction g w := by
  refine ⟨hf.isProper_inf_of_closedPolyhedralEpigraph hg hproperf hproperg, ?_, ?_⟩
  · exact hf.lowerSemicontinuous_inf_of_closedPolyhedralEpigraph hg
  · exact hf.horizonFunction_inf_eq_inf_of_closedPolyhedralEpigraph hg

/-- Finite pointwise infima of proper closed-polyhedral-epigraph functions are
proper. -/
theorem HasClosedPolyhedralEpigraph.isProper_iInf_of_finite_of_closedPolyhedralEpigraph
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (_hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i)) :
    IsProper (fun x => ⨅ i, f i x) :=
  RW.isProper_iInf_of_finite hproper

/-- Lower semicontinuity is preserved by finite pointwise infima of
closed-polyhedral-epigraph functions. -/
theorem HasClosedPolyhedralEpigraph.lowerSemicontinuous_iInf_of_finite_of_closedPolyhedralEpigraph
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i)) :
    LowerSemicontinuous (fun x => ⨅ i, f i x) :=
  RW.lowerSemicontinuous_iInf_of_finite fun i => (hf i).lowerSemicontinuous

/-- Finite-family form of Proposition 3.30 for closed-polyhedral-epigraph
functions: the horizon function commutes with the pointwise infimum. -/
theorem
    HasClosedPolyhedralEpigraph.horizonFunction_iInf_eq_iInf_of_finite_of_closedPolyhedralEpigraph
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (_hf : ∀ i, HasClosedPolyhedralEpigraph (f i)) :
    horizonFunction (fun x => ⨅ i, f i x) = fun w => ⨅ i, horizonFunction (f i) w :=
  RW.horizonFunction_iInf_eq_iInf_of_finite f

/-- Regularity package for finite pointwise infima of proper
closed-polyhedral-epigraph functions. -/
theorem HasClosedPolyhedralEpigraph.iInf_regular_of_finite
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, HasClosedPolyhedralEpigraph (f i))
    (hproper : ∀ i, IsProper (f i)) :
    IsProper (fun x => ⨅ i, f i x) ∧
      LowerSemicontinuous (fun x => ⨅ i, f i x) ∧
      horizonFunction (fun x => ⨅ i, f i x) = fun w => ⨅ i, horizonFunction (f i) w := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      HasClosedPolyhedralEpigraph.isProper_iInf_of_finite_of_closedPolyhedralEpigraph
        hf hproper
  · exact
      HasClosedPolyhedralEpigraph.lowerSemicontinuous_iInf_of_finite_of_closedPolyhedralEpigraph
        hf
  · exact
      HasClosedPolyhedralEpigraph.horizonFunction_iInf_eq_iInf_of_finite_of_closedPolyhedralEpigraph
        hf

theorem IsConvexPiecewiseLinear.isProper_inf_of_cpl
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    IsProper (fun x => f x ⊓ g x) :=
  isProper_inf_of_isProper hf.isProper hg.isProper

theorem IsConvexPiecewiseLinear.lowerSemicontinuous_inf_of_cpl
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    LowerSemicontinuous (fun x => f x ⊓ g x) :=
  RW.lowerSemicontinuous_inf hf.lowerSemicontinuous hg.lowerSemicontinuous

theorem IsConvexPiecewiseLinear.horizonFunction_inf_eq_inf_of_cpl
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    horizonFunction (fun x => f x ⊓ g x) =
      fun w => horizonFunction f w ⊓ horizonFunction g w :=
  HasClosedPolyhedralEpigraph.horizonFunction_inf_eq_inf_of_closedPolyhedralEpigraph
    hf.hasClosedPolyhedralEpigraph
    hg.hasClosedPolyhedralEpigraph

/-- Regularity package for binary pointwise infima of convex piecewise-linear
functions. -/
theorem IsConvexPiecewiseLinear.inf_regular
    {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g) :
    IsProper (fun x => f x ⊓ g x) ∧
      LowerSemicontinuous (fun x => f x ⊓ g x) ∧
      horizonFunction (fun x => f x ⊓ g x) =
        fun w => horizonFunction f w ⊓ horizonFunction g w := by
  refine ⟨hf.isProper_inf_of_cpl hg, ?_, ?_⟩
  · exact hf.lowerSemicontinuous_inf_of_cpl hg
  · exact hf.horizonFunction_inf_eq_inf_of_cpl hg

/-- Finite pointwise infima of convex piecewise-linear functions are proper. -/
theorem IsConvexPiecewiseLinear.isProper_iInf_of_finite_of_cpl
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    IsProper (fun x => ⨅ i, f i x) :=
  RW.isProper_iInf_of_finite fun i => (hf i).isProper

/-- Lower semicontinuity is preserved by finite pointwise infima of convex
piecewise-linear functions. -/
theorem IsConvexPiecewiseLinear.lowerSemicontinuous_iInf_of_finite_of_cpl
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    LowerSemicontinuous (fun x => ⨅ i, f i x) :=
  RW.lowerSemicontinuous_iInf_of_finite fun i => (hf i).lowerSemicontinuous

/-- Finite-family form of Proposition 3.30 for convex piecewise-linear
functions: the horizon function commutes with the pointwise infimum. -/
theorem IsConvexPiecewiseLinear.horizonFunction_iInf_eq_iInf_of_finite_of_cpl
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    horizonFunction (fun x => ⨅ i, f i x) = fun w => ⨅ i, horizonFunction (f i) w :=
  HasClosedPolyhedralEpigraph.horizonFunction_iInf_eq_iInf_of_finite_of_closedPolyhedralEpigraph
    (fun i => (hf i).hasClosedPolyhedralEpigraph)

/-- Regularity package for finite pointwise infima of convex piecewise-linear
functions. -/
theorem IsConvexPiecewiseLinear.iInf_regular_of_finite
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsConvexPiecewiseLinear (f i)) :
    IsProper (fun x => ⨅ i, f i x) ∧
      LowerSemicontinuous (fun x => ⨅ i, f i x) ∧
      horizonFunction (fun x => ⨅ i, f i x) = fun w => ⨅ i, horizonFunction (f i) w := by
  refine ⟨?_, ?_, ?_⟩
  · exact IsConvexPiecewiseLinear.isProper_iInf_of_finite_of_cpl hf
  · exact IsConvexPiecewiseLinear.lowerSemicontinuous_iInf_of_finite_of_cpl hf
  · exact
      IsConvexPiecewiseLinear.horizonFunction_iInf_eq_iInf_of_finite_of_cpl hf

end RW
