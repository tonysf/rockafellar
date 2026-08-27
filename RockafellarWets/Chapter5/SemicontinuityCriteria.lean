/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Criteria and Characterizations of Semicontinuity

This file proves the neighborhood criteria of Exercise 5.6(a)(b) and the
graph and preimage characterizations of Theorem 5.7(a)(c).

The inverse image `S⁻¹(W) = {x | S(x) ∩ W ≠ ∅}` used throughout is the
set-valued preimage of the book, not the preimage of a single point.
-/

import RockafellarWets.Chapter5.Semicontinuity

open Filter Set Topology

namespace RW

section Preimage

variable {E F : Type*}

/-- The set-valued inverse image `S⁻¹(W) = {x | S(x) ∩ W ≠ ∅}`. -/
def svPreimage (S : E → Set F) (W : Set F) : Set E := {x | (S x ∩ W).Nonempty}

@[simp]
theorem mem_svPreimage {S : E → Set F} {W : Set F} {x : E} :
    x ∈ svPreimage S W ↔ (S x ∩ W).Nonempty := Iff.rfl

/-- At a singleton the set-valued preimage is the pointwise inverse. -/
theorem svPreimage_singleton (S : E → Set F) (u : F) :
    svPreimage S {u} = svInv S u := by
  ext x
  simp [svPreimage, svInv]

theorem svPreimage_mono {S : E → Set F} {W W' : Set F} (h : W ⊆ W') :
    svPreimage S W ⊆ svPreimage S W' :=
  fun _ ⟨v, hv, hvW⟩ ↦ ⟨v, hv, h hvW⟩

theorem svPreimage_univ (S : E → Set F) : svPreimage S univ = svDom S := by
  ext x
  simp [svPreimage, svDom]

end Preimage

section FilterHelpers

variable {ι E : Type*} [TopologicalSpace E]

/-- Failure of membership in an outer limit, made explicit. -/
theorem not_mem_outerSetLimitAlong {l : Filter ι} {C : ι → Set E} {x : E} :
    x ∉ outerSetLimitAlong l C ↔
      ∃ V ∈ nhds x, ∀ᶠ i in l, C i ∩ V = ∅ := by
  simp only [mem_outerSetLimitAlong, not_forall, Filter.not_frequently,
    not_nonempty_iff_eq_empty, exists_prop]

end FilterHelpers

section NeighborhoodCriteria

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- An eventuality along `𝓝[X] x` is a statement about `X ∩ V` for some
neighborhood `V` of `x`, which is the form used in Exercise 5.6. -/
theorem eventually_nhdsWithin_iff_exists_nhds {X : Set E} {x : E}
    {p : E → Prop} :
    (∀ᶠ y in nhdsWithin x X, p y) ↔ ∃ V ∈ nhds x, ∀ y ∈ X ∩ V, p y := by
  constructor
  · intro h
    rcases mem_nhdsWithin.1 h with ⟨U, hUopen, hxU, hUsub⟩
    exact ⟨U, hUopen.mem_nhds hxU, fun y hy ↦ hUsub ⟨hy.2, hy.1⟩⟩
  · rintro ⟨V, hV, hsub⟩
    rcases mem_nhds_iff.1 hV with ⟨U, hUV, hUopen, hxU⟩
    exact mem_nhdsWithin.2
      ⟨U, hUopen, hxU, fun y hy ↦ hsub y ⟨hy.2, hUV hy.1⟩⟩

/-- **Exercise 5.6(a).**  Outer semicontinuity relative to `X` at `x` is the
statement that every point outside `S x` is separated from the nearby
images. -/
theorem svOscWithinAt_iff {S : E → Set F} {X : Set E} {x : E} :
    SvOscWithinAt S X x ↔
      ∀ u ∉ S x, ∃ W ∈ nhds u, ∃ V ∈ nhds x,
        X ∩ V ∩ svPreimage S W = ∅ := by
  constructor
  · intro h u hu
    have hnot : u ∉ svOuterLimitWithin S X x := fun hmem ↦ hu (h hmem)
    rcases not_mem_outerSetLimitAlong.1 hnot with ⟨W, hW, hev⟩
    rcases eventually_nhdsWithin_iff_exists_nhds.1 hev with ⟨V, hV, hsub⟩
    refine ⟨W, hW, V, hV, ?_⟩
    rw [← not_nonempty_iff_eq_empty]
    rintro ⟨y, hyXV, hyPre⟩
    exact absurd hyPre (not_nonempty_iff_eq_empty.2 (hsub y hyXV))
  · intro h u hu
    by_contra hcon
    rcases h u hcon with ⟨W, hW, V, hV, hempty⟩
    have hnot : u ∉ svOuterLimitWithin S X x := by
      refine not_mem_outerSetLimitAlong.2 ⟨W, hW, ?_⟩
      refine eventually_nhdsWithin_iff_exists_nhds.2 ⟨V, hV, fun y hy ↦ ?_⟩
      rw [← not_nonempty_iff_eq_empty]
      intro hne
      have hmem : y ∈ X ∩ V ∩ svPreimage S W := ⟨hy, hne⟩
      rw [hempty] at hmem
      exact hmem
    exact hnot hu

/-- **Exercise 5.6(b).**  Inner semicontinuity relative to `X` at `x` is the
statement that each neighborhood of each image point is reached from all
nearby points of `X`. -/
theorem svIscWithinAt_iff {S : E → Set F} {X : Set E} {x : E} :
    SvIscWithinAt S X x ↔
      ∀ u ∈ S x, ∀ W ∈ nhds u, ∃ V ∈ nhds x,
        X ∩ V ⊆ svPreimage S W := by
  constructor
  · intro h u hu W hW
    exact eventually_nhdsWithin_iff_exists_nhds.1 (h hu W hW)
  · intro h u hu W hW
    exact eventually_nhdsWithin_iff_exists_nhds.2 (h u hu W hW)

end NeighborhoodCriteria

section GraphCharacterization

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Theorem 5.7(a).**  Outer semicontinuity everywhere is closedness of the
graph. -/
theorem isClosed_svGraph_iff_svOsc {S : E → Set F} :
    IsClosed (svGraph S) ↔ SvOsc S := by
  constructor
  · intro hclosed x u hu
    have hmem : (x, u) ∈ closure (svGraph S) := by
      rw [mem_closure_iff_nhds]
      intro t ht
      rcases mem_nhds_prod_iff.1 ht with ⟨V, hV, W, hW, hsub⟩
      rcases Filter.frequently_iff.1 (hu W hW) hV with ⟨y, hyV, v, hvS, hvW⟩
      exact ⟨(y, v), hsub (mk_mem_prod hyV hvW), hvS⟩
    rwa [hclosed.closure_eq] at hmem
  · intro hosc
    rw [← closure_subset_iff_isClosed]
    rintro ⟨x, u⟩ hp
    refine hosc x ?_
    intro W hW
    rw [Filter.frequently_iff]
    intro V hV
    rcases mem_closure_iff_nhds.1 hp _ (prod_mem_nhds hV hW)
      with ⟨⟨y, v⟩, ⟨hyV, hvW⟩, hgr⟩
    exact ⟨y, hyV, ⟨v, hgr, hvW⟩⟩

/-- **Theorem 5.7(a)**, second clause: `S` is osc exactly when `S⁻¹` is. -/
theorem svOsc_svInv_iff {S : E → Set F} : SvOsc (svInv S) ↔ SvOsc S := by
  rw [← isClosed_svGraph_iff_svOsc, ← isClosed_svGraph_iff_svOsc,
    svGraph_svInv]
  constructor
  · intro h
    have := h.preimage (continuous_swap (X := E) (Y := F))
    simpa [Set.preimage_preimage] using this
  · intro h
    exact h.preimage continuous_swap

end GraphCharacterization

section OpenPreimageCharacterization

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Theorem 5.7(c)**, absolute form: inner semicontinuity everywhere is
openness of the inverse images of open sets. -/
theorem svIsc_iff_isOpen_svPreimage {S : E → Set F} :
    SvIsc S ↔ ∀ O : Set F, IsOpen O → IsOpen (svPreimage S O) := by
  constructor
  · intro h O hO
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rcases hx with ⟨u, huS, huO⟩
    exact h x huS O (hO.mem_nhds huO)
  · intro h x u hu W hW
    rcases mem_nhds_iff.1 hW with ⟨O, hOW, hOopen, huO⟩
    have hxO : x ∈ svPreimage S O := ⟨u, hu, huO⟩
    have := (h O hOopen).mem_nhds hxO
    filter_upwards [this] with y hy
    exact hy.imp fun v hv ↦ ⟨hv.1, hOW hv.2⟩

/-- **Theorem 5.7(c)**, relative form: inner semicontinuity relative to `X`
is relative openness of the inverse images of open sets. -/
theorem svIscOn_iff_eventually_svPreimage {S : E → Set F} {X : Set E} :
    SvIscOn S X ↔
      ∀ O : Set F, IsOpen O → ∀ x ∈ X, x ∈ svPreimage S O →
        ∀ᶠ y in nhdsWithin x X, y ∈ svPreimage S O := by
  constructor
  · intro h O hO x hx ⟨u, huS, huO⟩
    exact h x hx huS O (hO.mem_nhds huO)
  · intro h x hx u hu W hW
    rcases mem_nhds_iff.1 hW with ⟨O, hOW, hOopen, huO⟩
    have hev := h O hOopen x hx ⟨u, hu, huO⟩
    filter_upwards [hev] with y hy
    exact hy.imp fun v hv ↦ ⟨hv.1, hOW hv.2⟩

end OpenPreimageCharacterization

end RW
