/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Optimal-Set Mappings

Example 5.22 reads the parametric minimization of Chapter 1 in the language
of Chapter 5.  For a proper lsc integrand `f(x,u)` that is level-bounded in
`x` locally uniformly in `u`, the value function `p(u) = inf_x f(x,u)` and the
optimal-set mapping `P(u) = argmin_x f(x,u)` are related by:

* `P` is locally bounded relative to `U` as soon as `p` is bounded from above
  relative to `U` near the point;
* `P` is outer semicontinuous relative to `U` as soon as `p` is upper
  semicontinuous relative to `U`;
* at a point of `U` where `P` is single-valued and `p` is continuous relative
  to `U`, the mapping `P` is continuous relative to `U`.

The book's Detail says this "restates part of 1.17".  Theorem 1.17 is not
formalized in this project, so nothing is taken from it: the first two clauses
are proved directly, from the definition of `argmin` and from 5.17(b)
respectively, and the third combines them with the relative form of 5.19.
Only the nonemptiness of `P(u)` for `u ∈ dom p`, which is 1.17(a), is needed
for the third clause, and that is obtained here from Chapter 3's existence
theorem for minimizers of an inf-compact proper lsc function.

Note how little each clause needs.  Local boundedness uses no
semicontinuity at all; outer semicontinuity uses no level boundedness and
only the upper half of the continuity of `p`.
-/

import RockafellarWets.Chapter3.Coercivity
import RockafellarWets.Chapter5.LevelBoundedness
import RockafellarWets.Chapter5.LocallyBoundedContinuity

open Bornology Filter Set Topology

namespace RW

section OptimalSets

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : E × F → EReal} {U : Set F} {u : F}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- A minimizer of the slice at `u` lies in every level set of that slice that
the optimal value reaches. -/
theorem paramArgmin_subset_paramLevelSet {α : ℝ}
    (h : valueFunction f u ≤ (α : EReal)) :
    paramArgmin f u ⊆ paramLevelSet f α u := by
  intro x hx
  rw [mem_paramLevelSet, (mem_paramArgmin_iff f u x).1 hx |>.1]
  exact h

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- **Example 5.22**, first clause: `P` is locally bounded relative to `U` at
a point where `p` is bounded from above relative to `U`.

No semicontinuity is used.  A bound `p ≤ α` near the point confines the
optimal sets inside the level sets `lev≤α f(·,u)`, and 5.17(b) makes those
uniformly bounded. -/
theorem svLocallyBoundedWithinAt_paramArgmin
    (hlb : IsLevelBoundedInXLocallyUniformly f)
    (hbdd : ∃ α : ℝ, ∀ᶠ u' in nhdsWithin u U, valueFunction f u' ≤ (α : EReal)) :
    SvLocallyBoundedWithinAt (paramArgmin f) U u := by
  obtain ⟨α, hα⟩ := hbdd
  obtain ⟨V, hV, hVsub⟩ := eventually_nhdsWithin_iff_exists_nhds.1 hα
  obtain ⟨V', hV', hbounded⟩ :=
    (isLevelBoundedInXLocallyUniformly_iff_svLocallyBounded f).1 hlb α u
  refine ⟨V ∩ V', Filter.inter_mem hV hV', hbounded.subset ?_⟩
  rintro x hx
  obtain ⟨u', ⟨hu'U, hu'V, hu'V'⟩, hxu'⟩ := mem_svImage.1 hx
  exact mem_svImage.2
    ⟨u', hu'V', paramArgmin_subset_paramLevelSet (hVsub u' ⟨hu'U, hu'V⟩) hxu'⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- **Example 5.22**, second clause: `P` is outer semicontinuous relative to
`U` at a point of `dom p` where `p` is upper semicontinuous relative to `U`.

No level boundedness is used.  If a limit point `x̄` of optimal solutions were
not optimal, lower semicontinuity of `f` would keep `f` above some `β` on a
whole product neighborhood, while upper semicontinuity of `p` would push the
nearby optimal values below `β`. -/
theorem svOscWithinAt_paramArgmin (hlsc : LowerSemicontinuous f)
    (hu : valueFunction f u < ⊤)
    (husc : UpperSemicontinuousWithinAt (valueFunction f) U u) :
    SvOscWithinAt (paramArgmin f) U u := by
  intro x hx
  rw [mem_paramArgmin_iff]
  refine ⟨le_antisymm ?_ (iInf_le (fun x' ↦ f (x', u)) x), hu⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨β, hβp, hβf⟩ := exists_between hlt
  have hev : ∀ᶠ q in nhds ((x, u) : E × F), β < f q := hlsc (x, u) β hβf
  rw [nhds_prod_eq] at hev
  obtain ⟨pa, hpa, pb, hpb, hcomb⟩ := Filter.eventually_prod_iff.1 hev
  obtain ⟨u', ⟨x', hx'arg, hx'pa⟩, hu'val, hu'pb⟩ :=
    ((hx {a | pa a} hpa).and_eventually
      ((husc β hβp).and (nhdsWithin_le_nhds hpb))).exists
  have hopt : f (x', u') = valueFunction f u' :=
    ((mem_paramArgmin_iff f u' x').1 hx'arg).1
  have hgt : β < f (x', u') := hcomb hx'pa hu'pb
  rw [hopt] at hgt
  exact absurd hgt (not_lt.2 hu'val.le)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- **Example 5.22**, second clause in its set-wide form: `P` is outer
semicontinuous relative to `U` when `p` is upper semicontinuous relative to
`U` at every point of `U ⊂ dom p`. -/
theorem svOscOn_paramArgmin (hlsc : LowerSemicontinuous f)
    (hU : ∀ u' ∈ U, valueFunction f u' < ⊤)
    (husc : ∀ u' ∈ U, UpperSemicontinuousWithinAt (valueFunction f) U u') :
    SvOscOn (paramArgmin f) U :=
  fun u' hu' ↦ svOscWithinAt_paramArgmin hlsc (hU u' hu') (husc u' hu')

variable [FiniteDimensional ℝ E]

omit [NormedSpace ℝ F] in
/-- The nonemptiness clause of 1.17(a), which the third clause of 5.22 needs:
at a parameter where the optimal value is finite, the slice is proper, lsc and
level-bounded, so it attains its infimum. -/
theorem paramArgmin_nonempty (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) (hlb : IsLevelBoundedInXLocallyUniformly f)
    (hu : valueFunction f u < ⊤) : (paramArgmin f u).Nonempty := by
  have hslice : LowerSemicontinuous (fun x ↦ f (x, u)) := fun x β hβ ↦
    ((continuous_id.prodMk continuous_const).tendsto x).eventually (hlsc (x, u) β hβ)
  have hlevel : IsLevelBounded (fun x ↦ f (x, u)) := fun α ↦
    ((isLevelBoundedInXLocallyUniformly_iff_svLocallyBounded f).1 hlb α u).isBounded_apply
  refine argmin_nonempty_of_isInfCompact_of_lsc_of_isProper
    (isInfCompact_of_isLevelBounded_of_lsc hslice hlevel) hslice ⟨?_, fun x ↦ hproper.2 (x, u)⟩
  exact iInf_lt_iff.1 hu

omit [NormedSpace ℝ F] in
/-- **Example 5.22**, third clause: at a point of `U` where `p` is continuous
relative to `U` and `P` is single-valued, `P` is continuous relative to `U`.

Outer semicontinuity is the second clause.  For the inner half, continuity of
`p` bounds it from above nearby, so the first clause makes `P` locally bounded
relative to `U`; the relative form of 5.19 then drives the whole nearby
optimal sets into any neighborhood of the unique optimal solution, and those
sets are nonempty because `U` lies in `dom p`. -/
theorem svContinuousWithinAt_paramArgmin (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) (hlb : IsLevelBoundedInXLocallyUniformly f)
    (hU : ∀ u' ∈ U, valueFunction f u' < ⊤) (hu : u ∈ U)
    (hcont : ContinuousWithinAt (valueFunction f) U u)
    {x : E} (hsingle : paramArgmin f u = {x}) :
    SvContinuousWithinAt (paramArgmin f) U u := by
  have huval : valueFunction f u < ⊤ := hU u hu
  have hosc : SvOscWithinAt (paramArgmin f) U u :=
    svOscWithinAt_paramArgmin hlsc huval hcont.upperSemicontinuousWithinAt
  refine ⟨hosc, ?_⟩
  -- `p` is bounded above near `u` relative to `U`, so `P` is locally bounded there.
  obtain ⟨α, hαp, -⟩ := EReal.exists_between_coe_real huval
  have hlbP : SvLocallyBoundedWithinAt (paramArgmin f) U u :=
    svLocallyBoundedWithinAt_paramArgmin hlb
      ⟨α, (hcont.upperSemicontinuousWithinAt _ hαp).mono fun _ h ↦ h.le⟩
  intro y hy W hW
  rw [hsingle, mem_singleton_iff] at hy
  subst hy
  obtain ⟨O, hOW, hOopen, hyO⟩ := _root_.mem_nhds_iff.1 hW
  obtain ⟨V, hV, hVsub⟩ :=
    hosc.exists_nhds_svImage_inter_subset hlbP hu hOopen
      (by rw [hsingle]; exact singleton_subset_iff.2 hyO)
  rw [eventually_nhdsWithin_iff_exists_nhds]
  refine ⟨V, hV, fun u' hu' ↦ ?_⟩
  obtain ⟨z, hz⟩ := paramArgmin_nonempty hlsc hproper hlb (hU u' hu'.1)
  exact ⟨z, hz, hOW (hVsub (mem_svImage.2 ⟨u', hu', hz⟩))⟩

end OptimalSets

end RW
