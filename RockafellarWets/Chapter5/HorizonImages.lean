/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Horizon Criteria for Closed Images

Exercise 5.26 refines 5.25 by replacing local boundedness with a horizon
condition: `S⁻¹(D)` is closed once `S∞(0) ∩ D∞ = {0}`, and then
`S⁻¹(D)∞ ⊂ (S∞)⁻¹(D∞)`.  As in 5.25, clause (a) is clause (b) read through
the inverse, which needs the identity `(S⁻¹)∞ = (S∞)⁻¹` recorded after
formula 5(5).

The book's Guide suggests showing that the truncation `S∩D` is locally
bounded and appealing to 5.25.  That intermediate claim is proved here, since
it is cheap and worth having, but the results themselves take a shorter route.
The set `S⁻¹(D)` is the image of `(gph S) ∩ (IRⁿ × D)` under the projection
`(x, u) → x`, and Theorem 3.10 of Chapter 3 says exactly when a linear image
of a closed set is closed: when no nonzero horizon direction of the set lies
in the kernel.  Here that condition unpacks to the book's own hypothesis
`S∞(0) ∩ D∞ = {0}`.  The same theorem's equality clause `L(C∞) = L(C)∞` holds
under the identical hypothesis, so the trailing horizon inclusion costs
nothing extra -- and needs neither outer semicontinuity of `S` nor closedness
of `D`.
-/

import RockafellarWets.Chapter3.LinearImages
import RockafellarWets.Chapter5.ClosedImages
import RockafellarWets.Chapter5.HorizonMappings
import RockafellarWets.Chapter5.LocallyBoundedContinuity

open Bornology Filter Set Topology

namespace RW

section HorizonImages

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {S : E → Set F} {C : Set E} {D : Set F}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The graph of a truncation is the graph cut by a cylinder. -/
theorem svGraph_svTrunc (S : E → Set F) (D : Set F) :
    svGraph (svTrunc S D) = svGraph S ∩ ((univ : Set E) ×ˢ D) := by
  ext p
  simp [svGraph, svTrunc, mem_prod]

/-- The horizon cone of a cylinder lies inside the cylinder over the horizon
cone.  This is 3.10 applied to the second projection. -/
theorem horizonCone_univ_prod_subset (D : Set F) :
    horizonCone ((univ : Set E) ×ˢ D) ⊆ (univ : Set E) ×ˢ horizonCone D := by
  rintro ⟨a, v⟩ hav
  refine ⟨mem_univ a, ?_⟩
  have himg : ⇑(LinearMap.snd ℝ E F) '' ((univ : Set E) ×ˢ D) = D := by
    rw [LinearMap.coe_snd]
    exact Set.snd_image_prod (s := (univ : Set E)) ⟨0, mem_univ 0⟩ D
  have hmem : v ∈ ⇑(LinearMap.snd ℝ E F) '' horizonCone ((univ : Set E) ×ˢ D) :=
    ⟨(a, v), hav, rfl⟩
  have := linearMap_image_horizonCone_subset (LinearMap.snd ℝ E F) hmem
  rwa [himg] at this

/-- A horizon direction of a truncation is a horizon direction of the mapping
and of the truncating set at once. -/
theorem svHorizon_svTrunc_subset (S : E → Set F) (D : Set F) (x : E) :
    svHorizon (svTrunc S D) x ⊆ svHorizon S x ∩ horizonCone D := by
  intro v hv
  rw [mem_svHorizon, svGraph_svTrunc] at hv
  exact ⟨horizonCone_mono inter_subset_left hv,
    (horizonCone_univ_prod_subset D (horizonCone_mono inter_subset_right hv)).2⟩

/-- The intermediate claim of the book's Guide: the horizon condition makes
the truncation's horizon mapping trivial over `0`. -/
theorem svHorizon_svTrunc_zero (h : svHorizon S 0 ∩ horizonCone D = ({0} : Set F)) :
    svHorizon (svTrunc S D) 0 = ({0} : Set F) := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨zero_mem_svHorizon_zero _, fun v hv ↦ ?_⟩
  have hmem := svHorizon_svTrunc_subset S D 0 hv
  rw [h] at hmem
  exact hmem

/-- The rest of the Guide: by 5.18 the truncation is then locally bounded. -/
theorem svLocallyBounded_svTrunc_of_svHorizon
    (h : svHorizon S 0 ∩ horizonCone D = ({0} : Set F)) :
    SvLocallyBounded (svTrunc S D) :=
  svLocallyBounded_of_svHorizon_zero (svHorizon_svTrunc_zero h)

/-- The horizon condition, transcribed as the kernel condition of 3.10 for the
projection `(x, u) → x`. -/
private theorem fst_ker_of_svHorizon
    (h : svHorizon S 0 ∩ horizonCone D = ({0} : Set F)) :
    ∀ ⦃v : E × F⦄, v ∈ horizonCone (svGraph S ∩ ((univ : Set E) ×ˢ D)) →
      (LinearMap.fst ℝ E F) v = 0 → v = 0 := by
  rintro ⟨a, w⟩ hv hfst
  have ha : a = 0 := by simpa using hfst
  subst ha
  have hw : w ∈ svHorizon S 0 ∩ horizonCone D := by
    refine svHorizon_svTrunc_subset S D 0 ?_
    rw [mem_svHorizon, svGraph_svTrunc]
    exact hv
  rw [h, mem_singleton_iff] at hw
  simp [hw]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- `S⁻¹(D)` is the projection of the part of the graph lying under `D`. -/
theorem svPreimage_eq_image_fst (S : E → Set F) (D : Set F) :
    svPreimage S D = ⇑(LinearMap.fst ℝ E F) '' (svGraph S ∩ ((univ : Set E) ×ˢ D)) := by
  rw [LinearMap.coe_fst, ← inter_svPreimage_eq_image_fst, univ_inter]

/-- **Exercise 5.26(b)**: `S⁻¹(D)` is closed when `D` is closed and
`S∞(0) ∩ D∞ = {0}`.  This is 3.10 for the projection `(x, u) → x`. -/
theorem SvOsc.isClosed_svPreimage_of_svHorizon (hosc : SvOsc S) (hD : IsClosed D)
    (h : svHorizon S 0 ∩ horizonCone D = ({0} : Set F)) :
    IsClosed (svPreimage S D) := by
  rw [svPreimage_eq_image_fst]
  exact isClosed_linearImage_of_horizonCone_ker_trivial
    ((isClosed_svGraph_iff_svOsc.2 hosc).inter (isClosed_univ.prod hD))
    (fst_ker_of_svHorizon h)

/-- **Exercise 5.26(b)**, the horizon inclusion `S⁻¹(D)∞ ⊂ (S∞)⁻¹(D∞)`.

It needs neither outer semicontinuity of `S` nor closedness of `D`: the
equality clause of 3.10 holds under the same kernel condition that the
closedness clause does. -/
theorem horizonCone_svPreimage_subset
    (h : svHorizon S 0 ∩ horizonCone D = ({0} : Set F)) :
    horizonCone (svPreimage S D) ⊆ svPreimage (svHorizon S) (horizonCone D) := by
  intro x hx
  rw [svPreimage_eq_image_fst, ← linearImage_horizonCone_eq (fst_ker_of_svHorizon h)] at hx
  obtain ⟨⟨a, v⟩, hav, rfl⟩ := hx
  have hmem : v ∈ svHorizon S a ∩ horizonCone D := by
    refine svHorizon_svTrunc_subset S D a ?_
    rw [mem_svHorizon, svGraph_svTrunc]
    exact hav
  exact ⟨v, hmem⟩

/-- The remark after formula 5(5): `(S⁻¹)∞ = (S∞)⁻¹`.  Swapping coordinates is
a linear isomorphism, so 3.10 applies with a trivial kernel condition. -/
theorem horizonCone_svGraph_svInv (S : E → Set F) :
    horizonCone (svGraph (svInv S)) = Prod.swap ⁻¹' horizonCone (svGraph S) := by
  have hcoe : ⇑((LinearEquiv.prodComm ℝ E F).toLinearMap) = (Prod.swap : E × F → F × E) := rfl
  have hker : ∀ ⦃v : E × F⦄, v ∈ horizonCone (svGraph S) →
      ((LinearEquiv.prodComm ℝ E F).toLinearMap) v = 0 → v = 0 := by
    intro v _ hv
    rw [hcoe] at hv
    exact Prod.ext (by simpa using congrArg Prod.snd hv) (by simpa using congrArg Prod.fst hv)
  have himg : ⇑((LinearEquiv.prodComm ℝ E F).toLinearMap) '' svGraph S = svGraph (svInv S) := by
    rw [hcoe, svGraph_svInv, ← Set.image_swap_eq_preimage_swap]
  rw [← himg, ← linearImage_horizonCone_eq hker, hcoe, Set.image_swap_eq_preimage_swap]

/-- The remark after formula 5(5): `(S⁻¹)∞ = (S∞)⁻¹`. -/
theorem svHorizon_svInv (S : E → Set F) : svHorizon (svInv S) = svInv (svHorizon S) := by
  funext u
  ext x
  simp only [mem_svHorizon, mem_svInv, horizonCone_svGraph_svInv, mem_preimage,
    Prod.swap_prod_mk]

/-- **Exercise 5.26(a)**: `S(C)` is closed when `C` is closed and
`(S∞)⁻¹(0) ∩ C∞ = {0}`. -/
theorem SvOsc.isClosed_svImage_of_svHorizon (hosc : SvOsc S) (hC : IsClosed C)
    (h : svInv (svHorizon S) 0 ∩ horizonCone C = ({0} : Set E)) :
    IsClosed (svImage S C) := by
  rw [svImage_eq_svPreimage_svInv]
  refine (svOsc_svInv_iff.2 hosc).isClosed_svPreimage_of_svHorizon hC ?_
  rwa [svHorizon_svInv]

/-- **Exercise 5.26(a)**, the horizon inclusion `S(C)∞ ⊂ S∞(C∞)`. -/
theorem horizonCone_svImage_subset
    (h : svInv (svHorizon S) 0 ∩ horizonCone C = ({0} : Set E)) :
    horizonCone (svImage S C) ⊆ svImage (svHorizon S) (horizonCone C) := by
  have hyp : svHorizon (svInv S) 0 ∩ horizonCone C = ({0} : Set E) := by
    rw [svHorizon_svInv]; exact h
  have hkey := horizonCone_svPreimage_subset hyp
  rw [svHorizon_svInv] at hkey
  rwa [← svImage_eq_svPreimage_svInv S C,
    ← svImage_eq_svPreimage_svInv (svHorizon S) (horizonCone C)] at hkey

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The book's parenthetical sufficient condition: `S∞(0) = {0}` gives the
horizon hypothesis for every `D`. -/
theorem svHorizon_inter_horizonCone_eq_of_svHorizon_zero
    (h : svHorizon S 0 = ({0} : Set F)) (D : Set F) :
    svHorizon S 0 ∩ horizonCone D = ({0} : Set F) := by
  rw [h]
  exact Set.inter_eq_self_of_subset_left
    (singleton_subset_iff.2 (zero_mem_horizonCone D))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The book's other parenthetical: `D∞ = {0}` gives the horizon hypothesis
for every `S`. -/
theorem svHorizon_inter_horizonCone_eq_of_horizonCone_zero (S : E → Set F)
    (h : horizonCone D = ({0} : Set F)) :
    svHorizon S 0 ∩ horizonCone D = ({0} : Set F) := by
  rw [h]
  exact Set.inter_eq_self_of_subset_right
    (singleton_subset_iff.2 (zero_mem_svHorizon_zero S))

end HorizonImages

end RW
