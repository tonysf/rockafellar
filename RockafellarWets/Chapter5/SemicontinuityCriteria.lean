/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Criteria and Characterizations of Semicontinuity

This file proves the neighborhood criteria of Exercise 5.6(a)(b), the
sequential criteria 5.6(c)(d), and the graph and preimage characterizations
of Theorem 5.7(a)(b)(c).

The inverse image `S⁻¹(W) = {x | S(x) ∩ W ≠ ∅}` used throughout is the
set-valued preimage of the book, not the preimage of a single point.
-/

import RockafellarWets.Chapter5.SequentialLimits

open Filter Set Topology

open scoped Set.Notation

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

section CompactPreimageCharacterization

variable {E F : Type*} [TopologicalSpace E]

/-- One half of **Theorem 5.7(b)**, and the half that needs no structure on
the target: outer semicontinuity relative to `X` makes the inverse image of
every compact set closed relative to `X`.

The compact set is covered by the separating neighborhoods `W u` supplied by
5.6(a); a finite subcover leaves a finite intersection of the matching
neighborhoods of the base point, which is still a neighborhood. -/
theorem SvOscOn.isClosed_svPreimage [TopologicalSpace F] {S : E → Set F}
    {X : Set E} (h : SvOscOn S X) {B : Set F} (hB : IsCompact B) :
    IsClosed (X ↓∩ svPreimage S B) := by
  classical
  rw [isClosed_preimage_val]
  rintro x ⟨hxX, hxcl⟩
  by_contra hcon
  have hmiss : ∀ u ∈ B, u ∉ S x := fun u huB huS ↦ hcon ⟨u, huS, huB⟩
  choose! W hWnhds V hVnhds hempty using
    fun u (hu : u ∉ S x) ↦ svOscWithinAt_iff.1 (h x hxX) u hu
  obtain ⟨t, htB, hcover⟩ :=
    hB.elim_nhds_subcover W fun u huB ↦ hWnhds u (hmiss u huB)
  have hVt : (⋂ u ∈ t, V u) ∈ nhds x :=
    Finset.iInter_mem_sets t |>.2 fun u hu ↦ hVnhds u (hmiss u (htB u hu))
  obtain ⟨y, hy⟩ := mem_closure_iff_nhds.1 hxcl _ hVt
  obtain ⟨hyX, v, hvS, hvB⟩ := hy.2
  have hyV : y ∈ ⋂ u ∈ t, V u := hy.1
  obtain ⟨u, hut, hvW⟩ := mem_iUnion₂.1 (hcover hvB)
  have hyu : y ∈ X ∩ V u ∩ svPreimage S (W u) :=
    ⟨⟨hyX, mem_iInter₂.1 hyV u hut⟩, v, hvS, hvW⟩
  rw [hempty u (hmiss u (htB u hut))] at hyu
  exact hyu

/-- The converse half of **Theorem 5.7(b)** for a closed-valued mapping into
a proper metric space.  Closed balls around a candidate limit point `u` are
compact, so relative closedness of their inverse images puts a point of
`S(x̄)` within every distance of `u`; closed-valuedness then puts `u` itself
in `S(x̄)`. -/
theorem svOscOn_of_isClosed_svPreimage [PseudoMetricSpace F] [ProperSpace F]
    {S : E → Set F} {X : Set E} (hval : ∀ x ∈ X, IsClosed (S x))
    (h : ∀ B : Set F, IsCompact B → IsClosed (X ↓∩ svPreimage S B)) :
    SvOscOn S X := by
  intro x hxX u hu
  have key : ∀ ε > 0, (S x ∩ Metric.closedBall u ε).Nonempty := by
    intro ε hε
    refine isClosed_preimage_val.1 (h _ (isCompact_closedBall u ε)) ⟨hxX, ?_⟩
    rw [mem_closure_iff_nhds]
    intro V hV
    have hfreq := hu (Metric.ball u ε) (Metric.ball_mem_nhds u hε)
    have hmemX : ∀ᶠ y in nhdsWithin x X, y ∈ X :=
      Filter.eventually_mem_set.2 self_mem_nhdsWithin
    have hmemV : ∀ᶠ y in nhdsWithin x X, y ∈ V :=
      Filter.eventually_mem_set.2 (nhdsWithin_le_nhds hV)
    obtain ⟨y, hhit, hyX, hyV⟩ :=
      (hfreq.and_eventually (hmemX.and hmemV)).exists
    obtain ⟨w, hwS, hwB⟩ := hhit
    exact ⟨y, hyV, hyX, w, hwS, Metric.ball_subset_closedBall hwB⟩
  rw [← (hval x hxX).closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, hvS, hvB⟩ := key (ε / 2) (by positivity)
  exact ⟨v, hvS, lt_of_le_of_lt (by simpa [dist_comm] using hvB) (by linarith)⟩

/-- **Theorem 5.7(b).**  For a closed-valued mapping, outer semicontinuity
relative to `X` is exactly closedness relative to `X` of the inverse image of
every compact set. -/
theorem svOscOn_iff_isClosed_svPreimage [PseudoMetricSpace F] [ProperSpace F]
    {S : E → Set F} {X : Set E} (hval : ∀ x ∈ X, IsClosed (S x)) :
    SvOscOn S X ↔ ∀ B : Set F, IsCompact B → IsClosed (X ↓∩ svPreimage S B) :=
  ⟨fun h _ hB ↦ h.isClosed_svPreimage hB, svOscOn_of_isClosed_svPreimage hval⟩

/-- **Theorem 5.7(b)** with relative closedness spelled out as a closure
condition inside `X`, avoiding the subtype. -/
theorem svOscOn_iff_closure_svPreimage [PseudoMetricSpace F] [ProperSpace F]
    {S : E → Set F} {X : Set E} (hval : ∀ x ∈ X, IsClosed (S x)) :
    SvOscOn S X ↔ ∀ B : Set F, IsCompact B →
      X ∩ closure (X ∩ svPreimage S B) ⊆ svPreimage S B := by
  simp only [svOscOn_iff_isClosed_svPreimage hval, isClosed_preimage_val]

/-- The absolute case `X = IRⁿ` of 5.7(b): a closed-valued mapping is outer
semicontinuous exactly when the inverse image of every compact set is
closed. -/
theorem svOsc_iff_isClosed_svPreimage [PseudoMetricSpace F] [ProperSpace F]
    {S : E → Set F} (hval : ∀ x, IsClosed (S x)) :
    SvOsc S ↔ ∀ B : Set F, IsCompact B → IsClosed (svPreimage S B) := by
  rw [← svOscOn_univ, svOscOn_iff_isClosed_svPreimage fun x _ ↦ hval x]
  exact forall_congr' fun B ↦ forall_congr' fun _ ↦ by
    rw [isClosed_univ.inter_preimage_val_iff, univ_inter]

end CompactPreimageCharacterization

section SequentialCriteria

variable {E F : Type*} [TopologicalSpace E] [FirstCountableTopology E]
variable [PseudoMetricSpace F] [SecondCountableTopology F]

/-- **Exercise 5.6(c).**  Outer semicontinuity relative to `X` at `x` says
that every Painleve--Kuratowski limit of images along a sequence in `X`
tending to `x` is contained in `S(x)`.

One direction only transports `atTop` forward into `𝓝[X] x`.  The other uses
the diagonal extraction of `SequentialLimits.lean` to reach a candidate point
of the outer limit in the *inner* limit sense, so that Chapter 4's
subsequence compactness 4.18 can then produce a convergent sequence of images
that still captures the point. -/
theorem svOscWithinAt_iff_seq {S : E → Set F} {X : Set E} {x : E}
    (hx : x ∈ X) :
    SvOscWithinAt S X x ↔
      ∀ y : ℕ → E, (∀ n, y n ∈ X) → Tendsto y atTop (nhds x) →
        ∀ D : Set F, PKConverges (fun n ↦ S (y n)) D → D ⊆ S x := by
  constructor
  · intro h y hyX hyto D hD
    rw [← hD.outer_eq]
    exact subset_trans
      (outerSetLimit_comp_subset (tendsto_nhdsWithin_of_forall_mem hyX hyto)) h
  · intro h u hu
    obtain ⟨y, hyX, hyto, hmem⟩ :=
      exists_seq_mem_innerSetLimit_of_mem_svOuterLimitWithin hx hu
    obtain ⟨φ, D, hφ, hD⟩ := exists_pkConvergent_subsequence fun n ↦ S (y n)
    refine h (y ∘ φ) (fun n ↦ hyX _) (hyto.comp hφ.tendsto_atTop) D hD ?_
    rw [← hD.inner_eq]
    exact innerSetLimit_subset_subsequence hφ hmem

/-- **Exercise 5.6(d).**  Inner semicontinuity relative to `X` at `x` says
that every Painleve--Kuratowski limit of images along a sequence in `X`
tending to `x` contains `S(x)`. -/
theorem svIscWithinAt_iff_seq {S : E → Set F} {X : Set E} {x : E}
    (hx : x ∈ X) :
    SvIscWithinAt S X x ↔
      ∀ y : ℕ → E, (∀ n, y n ∈ X) → Tendsto y atTop (nhds x) →
        ∀ D : Set F, PKConverges (fun n ↦ S (y n)) D → S x ⊆ D := by
  constructor
  · intro h y hyX hyto D hD
    rw [← hD.inner_eq]
    exact subset_trans h (innerSetLimitAlong_subset_innerSetLimit_comp
      (tendsto_nhdsWithin_of_forall_mem hyX hyto))
  · intro h
    by_contra hcon
    rw [SvIscWithinAt, Set.not_subset] at hcon
    obtain ⟨u, huS, hunot⟩ := hcon
    obtain ⟨y, hyX, hyto, hnot⟩ :=
      exists_seq_not_mem_outerSetLimit_of_not_mem_svInnerLimitWithin hx hunot
    obtain ⟨φ, D, hφ, hD⟩ := exists_pkConvergent_subsequence fun n ↦ S (y n)
    have huD : u ∈ D :=
      h (y ∘ φ) (fun n ↦ hyX _) (hyto.comp hφ.tendsto_atTop) D hD huS
    rw [← hD.outer_eq] at huD
    exact hnot (outerSetLimit_subsequence_subset hφ huD)

/-- The absolute case `X = IRⁿ` of 5.6(c). -/
theorem svOscAt_iff_seq {S : E → Set F} {x : E} :
    SvOscAt S x ↔
      ∀ y : ℕ → E, Tendsto y atTop (nhds x) →
        ∀ D : Set F, PKConverges (fun n ↦ S (y n)) D → D ⊆ S x := by
  rw [← svOscWithinAt_univ, svOscWithinAt_iff_seq (mem_univ x)]
  exact forall_congr' fun y ↦
    ⟨fun h hyto ↦ h (fun _ ↦ mem_univ _) hyto, fun h _ hyto ↦ h hyto⟩

/-- The absolute case `X = IRⁿ` of 5.6(d). -/
theorem svIscAt_iff_seq {S : E → Set F} {x : E} :
    SvIscAt S x ↔
      ∀ y : ℕ → E, Tendsto y atTop (nhds x) →
        ∀ D : Set F, PKConverges (fun n ↦ S (y n)) D → S x ⊆ D := by
  rw [← svIscWithinAt_univ, svIscWithinAt_iff_seq (mem_univ x)]
  exact forall_congr' fun y ↦
    ⟨fun h hyto ↦ h (fun _ ↦ mem_univ _) hyto, fun h _ hyto ↦ h hyto⟩

end SequentialCriteria

end RW
