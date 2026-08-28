/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Closedness of Images

Theorem 5.25 records when an outer semicontinuous mapping carries closed sets
to closed sets.  Outer semicontinuity alone is not enough -- `rge S` and
`dom S` need not be closed -- and the two repairs the book offers are
compactness of the set being mapped, or local boundedness of the mapping in
the other direction.

Clause (b) is proved and clause (a) is read off it by inversion, exactly as
the book does: `S(C) = S⁻¹⁻¹(C)`, and 5.7(a) says `S` is osc precisely when
`S⁻¹` is.

The compact case is 5.7(b) with `X = IRⁿ`, already available.  The locally
bounded case is the argument the book gives: `S⁻¹(D) ∩ B` is the first
projection of `(gph S) ∩ (B × D)`, which is closed because all three factors
are and bounded because it lies inside `B × S(B)`, bounded by 5.15.  A set
whose intersection with every compact set is closed is closed, which is the
small reusable lemma the file opens with.
-/

import RockafellarWets.Chapter5.LocalBoundedness

open Bornology Filter Metric Set Topology

namespace RW

section LocallyClosed

variable {E : Type*} [PseudoMetricSpace E] [ProperSpace E]

/-- A set that meets every compact set in a closed set is closed.  In a proper
space it is enough to test against closed balls, one around each candidate
point of the closure. -/
theorem isClosed_of_forall_isClosed_inter_isCompact {A : Set E}
    (h : ∀ B : Set E, IsCompact B → IsClosed (A ∩ B)) : IsClosed A := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  have hcl : IsClosed (A ∩ closedBall y 1) := h _ (isCompact_closedBall y 1)
  have hmem : y ∈ closure (A ∩ closedBall y 1) := by
    rw [mem_closure_iff_nhds]
    intro V hV
    obtain ⟨z, ⟨hzV, hzball⟩, hzA⟩ :=
      mem_closure_iff_nhds.1 hy (V ∩ ball y 1)
        (Filter.inter_mem hV (ball_mem_nhds y one_pos))
    exact ⟨z, hzV, hzA, ball_subset_closedBall hzball⟩
  rw [hcl.closure_eq] at hmem
  exact hmem.1

end LocallyClosed

section Inversion

variable {E F : Type*}

/-- The book's `S(C)` and `S⁻¹(D)` are each other's mirror image: the forward
image under `S` is the inverse image under `S⁻¹`. -/
theorem svImage_eq_svPreimage_svInv (S : E → Set F) (C : Set E) :
    svImage S C = svPreimage (svInv S) C := by
  ext u
  simp only [mem_svImage, svPreimage, mem_setOf_eq, Set.inter_nonempty]
  exact ⟨fun ⟨x, hxC, hux⟩ ↦ ⟨x, hux, hxC⟩, fun ⟨x, hux, hxC⟩ ↦ ⟨x, hxC, hux⟩⟩

end Inversion

section CompactCase

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Theorem 5.25(b)**, first assertion: an outer semicontinuous mapping has
closed inverse images of compact sets.  This is 5.7(b) with `X = IRⁿ`. -/
theorem SvOsc.isClosed_svPreimage_of_isCompact {S : E → Set F} (hosc : SvOsc S)
    {D : Set F} (hD : IsCompact D) : IsClosed (svPreimage S D) := by
  have h := (svOscOn_univ.2 hosc).isClosed_svPreimage hD
  rwa [isClosed_univ.inter_preimage_val_iff, univ_inter] at h

/-- **Theorem 5.25(a)**, first assertion: an outer semicontinuous mapping
carries compact sets to closed sets. -/
theorem SvOsc.isClosed_svImage_of_isCompact {S : E → Set F} (hosc : SvOsc S)
    {C : Set E} (hC : IsCompact C) : IsClosed (svImage S C) := by
  rw [svImage_eq_svPreimage_svInv]
  exact (svOsc_svInv_iff.2 hosc).isClosed_svPreimage_of_isCompact hC

end CompactCase

section LocallyBoundedCase

variable {E F : Type*} [MetricSpace E] [ProperSpace E]
variable [MetricSpace F] [ProperSpace F]

omit [MetricSpace E] [ProperSpace E] [MetricSpace F] [ProperSpace F] in
/-- The book's projection identity: the part of `S⁻¹(D)` inside `B` is the
first projection of the part of `gph S` lying over `B` and under `D`. -/
theorem inter_svPreimage_eq_image_fst (S : E → Set F) (D : Set F) (B : Set E) :
    B ∩ svPreimage S D = Prod.fst '' (svGraph S ∩ (B ×ˢ D)) := by
  ext x
  simp only [mem_inter_iff, svPreimage, mem_setOf_eq, Set.inter_nonempty, mem_image,
    mem_svGraph, mem_prod, Prod.exists]
  constructor
  · rintro ⟨hxB, u, huS, huD⟩
    exact ⟨x, u, ⟨huS, hxB, huD⟩, rfl⟩
  · rintro ⟨y, u, ⟨huS, hyB, huD⟩, rfl⟩
    exact ⟨hyB, u, huS, huD⟩

/-- **Theorem 5.25(b)**, second assertion: an outer semicontinuous, locally
bounded mapping has closed inverse images of closed sets.

The set `(gph S) ∩ (B × D)` is closed, being an intersection of closed sets,
and bounded, being contained in `B × S(B)` with `S(B)` bounded by 5.15; so it
is compact, and its first projection `B ∩ S⁻¹(D)` is compact too. -/
theorem SvOsc.isClosed_svPreimage_of_svLocallyBounded {S : E → Set F}
    (hosc : SvOsc S) (hlb : SvLocallyBounded S) {D : Set F} (hD : IsClosed D) :
    IsClosed (svPreimage S D) := by
  refine isClosed_of_forall_isClosed_inter_isCompact fun B hB ↦ ?_
  rw [inter_comm, inter_svPreimage_eq_image_fst]
  refine (IsCompact.image ?_ continuous_fst).isClosed
  refine isCompact_iff_isClosed_bounded.2 ⟨?_, ?_⟩
  · exact (isClosed_svGraph_iff_svOsc.2 hosc).inter (hB.isClosed.prod hD)
  · refine IsBounded.subset
      (hB.isBounded.prod
        (svLocallyBounded_iff_isBounded_svImage.1 hlb B hB.isBounded)) ?_
    rintro ⟨x, u⟩ ⟨huS, hxB, -⟩
    exact ⟨hxB, mem_svImage.2 ⟨x, hxB, huS⟩⟩

/-- **Theorem 5.25(a)**, second assertion: if `S⁻¹` is locally bounded, an
outer semicontinuous `S` carries closed sets to closed sets. -/
theorem SvOsc.isClosed_svImage_of_svLocallyBounded_svInv {S : E → Set F}
    (hosc : SvOsc S) (hlb : SvLocallyBounded (svInv S)) {C : Set E}
    (hC : IsClosed C) : IsClosed (svImage S C) := by
  rw [svImage_eq_svPreimage_svInv]
  exact (svOsc_svInv_iff.2 hosc).isClosed_svPreimage_of_svLocallyBounded hlb hC

/-- **Theorem 5.25(b)**, parenthetical: a locally bounded outer semicontinuous
mapping has closed domain. -/
theorem SvOsc.isClosed_svDom {S : E → Set F} (hosc : SvOsc S)
    (hlb : SvLocallyBounded S) : IsClosed (svDom S) := by
  rw [← svPreimage_univ]
  exact hosc.isClosed_svPreimage_of_svLocallyBounded hlb isClosed_univ

/-- **Theorem 5.25(a)**, parenthetical: if `S⁻¹` is locally bounded, an outer
semicontinuous `S` has closed range. -/
theorem SvOsc.isClosed_svRange {S : E → Set F} (hosc : SvOsc S)
    (hlb : SvLocallyBounded (svInv S)) : IsClosed (svRange S) := by
  rw [← svImage_univ]
  exact hosc.isClosed_svImage_of_svLocallyBounded_svInv hlb isClosed_univ

end LocallyBoundedCase

end RW
