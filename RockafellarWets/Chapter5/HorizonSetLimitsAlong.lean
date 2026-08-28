/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Horizon Set Limits Along a Filter

Chapter 4 builds the horizon limits of formula 4(6) on top of the sequential
Painleve--Kuratowski limits, by reading off the direction part of a cosmic
limit.  Section D of Chapter 5 needs the same limits taken as `x → x̄`, so
this file repeats the layering over `outerSetLimitAlong` and
`innerSetLimitAlong` and records that the Chapter 4 notions are exactly the
`atTop` case.

The definitions transfer for free, since they are layered rather than
primitive.  The *theorems* do not: Chapter 4 identifies the ordinary part of
a cosmic limit by extracting a convergent subsequence, and no subsequence is
available along a neighborhood filter.  The replacement here is that
`cosmicEmbed` is an open embedding, which turns the identification into a
one-line transport of neighborhoods in each direction.
-/

import RockafellarWets.Chapter4.HorizonLimits
import RockafellarWets.Chapter5.SetLimitsAlong

open Filter Metric Set Topology

namespace RW

section GeneralLimits

variable {ι E : Type*} [TopologicalSpace E]

/-- Outer limits split over a binary union of families.  For sequences this
is proved by extracting a subsequence lying in one of the two families; along
an arbitrary filter it is instead the fact that a neighborhood filter is
closed under intersection, so two separate escapes can be combined into
one. -/
theorem outerSetLimitAlong_union (l : Filter ι) (A B : ι → Set E) :
    outerSetLimitAlong l (fun i ↦ A i ∪ B i) =
      outerSetLimitAlong l A ∪ outerSetLimitAlong l B := by
  refine Subset.antisymm ?_ ?_
  · intro x hx
    by_contra hcon
    rw [mem_union, not_or] at hcon
    obtain ⟨V, hV, hVA⟩ := not_mem_outerSetLimitAlong.1 hcon.1
    obtain ⟨W, hW, hWB⟩ := not_mem_outerSetLimitAlong.1 hcon.2
    refine absurd (hx (V ∩ W) (Filter.inter_mem hV hW)) (Filter.not_frequently.2 ?_)
    filter_upwards [hVA, hWB] with i hiA hiB
    rw [not_nonempty_iff_eq_empty]
    refine eq_empty_of_forall_notMem fun z hz ↦ ?_
    rcases hz.1 with hzA | hzB
    · have : z ∈ A i ∩ V := ⟨hzA, hz.2.1⟩
      rw [hiA] at this
      exact this
    · have : z ∈ B i ∩ W := ⟨hzB, hz.2.2⟩
      rw [hiB] at this
      exact this
  · rintro x (hx | hx)
    · exact outerSetLimitAlong_mono (fun i ↦ subset_union_left) hx
    · exact outerSetLimitAlong_mono (fun i ↦ subset_union_right) hx

/-- Inner limits absorb a binary union, in the one direction that is true of
them. -/
theorem union_subset_innerSetLimitAlong (l : Filter ι) (A B : ι → Set E) :
    innerSetLimitAlong l A ∪ innerSetLimitAlong l B ⊆
      innerSetLimitAlong l (fun i ↦ A i ∪ B i) := by
  rintro x (hx | hx)
  · exact innerSetLimitAlong_mono (fun i ↦ subset_union_left) hx
  · exact innerSetLimitAlong_mono (fun i ↦ subset_union_right) hx

/-- A family that eventually sits inside a closed set has its outer limit
inside that set. -/
theorem outerSetLimitAlong_subset_of_eventually_subset {l : Filter ι}
    {C : ι → Set E} {Z : Set E} (hZ : IsClosed Z) (h : ∀ᶠ i in l, C i ⊆ Z) :
    outerSetLimitAlong l C ⊆ Z := by
  intro x hx
  by_contra hxZ
  refine absurd (hx Zᶜ (hZ.isOpen_compl.mem_nhds hxZ)) (Filter.not_frequently.2 ?_)
  filter_upwards [h] with i hi
  rw [not_nonempty_iff_eq_empty]
  exact eq_empty_of_forall_notMem fun z hz ↦ hz.2 (hi hz.1)

private theorem nonempty_inter_of_closure {A V : Set E} (hV : IsOpen V)
    (h : (closure A ∩ V).Nonempty) : (A ∩ V).Nonempty := by
  obtain ⟨p, hpA, hpV⟩ := h
  obtain ⟨z, hzV, hzA⟩ := _root_.mem_closure_iff.1 hpA V hV hpV
  exact ⟨z, hzA, hzV⟩

/-- Both limits along a filter only see the termwise closures.  This is
Theorem 4.4 for an arbitrary index filter, and its proof is the same: a
neighborhood filter has a basis of open sets, and an open set meets a closure
exactly when it meets the set. -/
theorem outerSetLimitAlong_closure (l : Filter ι) (C : ι → Set E) :
    outerSetLimitAlong l (fun i ↦ closure (C i)) = outerSetLimitAlong l C := by
  refine Subset.antisymm (fun x hx V hV ↦ ?_)
    (outerSetLimitAlong_mono fun i ↦ subset_closure)
  obtain ⟨U, hUV, hUopen, hxU⟩ := mem_nhds_iff.1 hV
  exact (hx U (hUopen.mem_nhds hxU)).mono fun i hi ↦
    ((nonempty_inter_of_closure hUopen hi).mono
      (inter_subset_inter_right _ hUV))

theorem innerSetLimitAlong_closure (l : Filter ι) (C : ι → Set E) :
    innerSetLimitAlong l (fun i ↦ closure (C i)) = innerSetLimitAlong l C := by
  refine Subset.antisymm (fun x hx V hV ↦ ?_)
    (innerSetLimitAlong_mono fun i ↦ subset_closure)
  obtain ⟨U, hUV, hUopen, hxU⟩ := mem_nhds_iff.1 hV
  exact (hx U (hUopen.mem_nhds hxU)).mono fun i hi ↦
    ((nonempty_inter_of_closure hUopen hi).mono
      (inter_subset_inter_right _ hUV))

/-- **Definition 4.1** along an arbitrary index filter: the limit exists and
equals `D`. -/
def PKConvergesAlong (l : Filter ι) (C : ι → Set E) (D : Set E) : Prop :=
  innerSetLimitAlong l C = D ∧ outerSetLimitAlong l C = D

theorem pkConvergesAlong_atTop (C : ℕ → Set E) (D : Set E) :
    PKConvergesAlong atTop C D ↔ PKConverges C D := Iff.rfl

/-- Convergence is unaffected by taking termwise closures. -/
theorem pkConvergesAlong_closure_iff (l : Filter ι) (C : ι → Set E)
    (D : Set E) :
    PKConvergesAlong l (fun i ↦ closure (C i)) D ↔ PKConvergesAlong l C D := by
  rw [PKConvergesAlong, PKConvergesAlong, outerSetLimitAlong_closure,
    innerSetLimitAlong_closure]

theorem PKConvergesAlong.inner_eq {l : Filter ι} {C : ι → Set E} {D : Set E}
    (h : PKConvergesAlong l C D) : innerSetLimitAlong l C = D := h.1

theorem PKConvergesAlong.outer_eq {l : Filter ι} {C : ι → Set E} {D : Set E}
    (h : PKConvergesAlong l C D) : outerSetLimitAlong l C = D := h.2

/-- A limit set is closed. -/
theorem PKConvergesAlong.isClosed {l : Filter ι} {C : ι → Set E} {D : Set E}
    (h : PKConvergesAlong l C D) : IsClosed D := by
  rw [← h.outer_eq]
  exact isClosed_outerSetLimitAlong l C

end GeneralLimits

section OrdinaryPart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ordinary points form an *open* embedded copy of `E` in cosmic space:
they are exactly the points of norm less than one.  Chapter 4 has the
embedding; openness of the range is what replaces subsequence extraction
below. -/
theorem isOpenEmbedding_cosmicEmbed :
    IsOpenEmbedding (cosmicEmbed : E → CosmicSpace E) := by
  refine ⟨isEmbedding_cosmicEmbed, ?_⟩
  have hrange : Set.range (cosmicEmbed : E → CosmicSpace E) =
      (Subtype.val : CosmicSpace E → E) ⁻¹' ball 0 1 := by
    ext p
    simpa only [mem_preimage, mem_ball_zero_iff] using exists_cosmicEmbed_eq_iff p
  rw [hrange]
  exact isOpen_ball.preimage continuous_subtype_val

variable {ι : Type*}

/-- **The ordinary part of a cosmic outer limit**, filter-natively.  An
ordinary point of the cosmic outer limit of `C(i) ∪ dir K(i)` sees only the
ordinary parts `C(i)`: a small enough cosmic neighborhood of an ordinary
point is the image of a neighborhood in `E`, and so contains no direction
points at all. -/
theorem cosmicEmbed_mem_outerSetLimitAlong_cosmicSet_iff {l : Filter ι}
    {C K : ι → Set E} {x : E} :
    cosmicEmbed x ∈ outerSetLimitAlong l (fun i ↦ cosmicSet (C i) (K i)) ↔
      x ∈ outerSetLimitAlong l C := by
  constructor
  · intro hx W hW
    obtain ⟨U, hUW, hUopen, hxU⟩ := _root_.mem_nhds_iff.1 hW
    refine (hx (cosmicEmbed '' U)
      (isOpenEmbedding_cosmicEmbed.isOpenMap _ hUopen |>.mem_nhds ⟨x, hxU, rfl⟩)).mono ?_
    rintro i ⟨p, hpS, y, hyU, rfl⟩
    exact ⟨y, cosmicEmbed_mem_cosmicSet_iff.1 hpS, hUW hyU⟩
  · intro hx V hV
    refine (hx (cosmicEmbed ⁻¹' V)
      (continuous_cosmicEmbed.continuousAt.preimage_mem_nhds hV)).mono ?_
    rintro i ⟨y, hyC, hyV⟩
    exact ⟨cosmicEmbed y, cosmicEmbed_mem_cosmicSet_iff.2 hyC, hyV⟩

/-- **The ordinary part of a cosmic inner limit**, filter-natively. -/
theorem cosmicEmbed_mem_innerSetLimitAlong_cosmicSet_iff {l : Filter ι}
    {C K : ι → Set E} {x : E} :
    cosmicEmbed x ∈ innerSetLimitAlong l (fun i ↦ cosmicSet (C i) (K i)) ↔
      x ∈ innerSetLimitAlong l C := by
  constructor
  · intro hx W hW
    obtain ⟨U, hUW, hUopen, hxU⟩ := _root_.mem_nhds_iff.1 hW
    refine (hx (cosmicEmbed '' U)
      (isOpenEmbedding_cosmicEmbed.isOpenMap _ hUopen |>.mem_nhds ⟨x, hxU, rfl⟩)).mono ?_
    rintro i ⟨p, hpS, y, hyU, rfl⟩
    exact ⟨y, cosmicEmbed_mem_cosmicSet_iff.1 hpS, hUW hyU⟩
  · intro hx V hV
    refine (hx (cosmicEmbed ⁻¹' V)
      (continuous_cosmicEmbed.continuousAt.preimage_mem_nhds hV)).mono ?_
    rintro i ⟨y, hyC, hyV⟩
    exact ⟨cosmicEmbed y, cosmicEmbed_mem_cosmicSet_iff.2 hyC, hyV⟩

theorem cosmicOrdinaryPart_outerSetLimitAlong_cosmicSet (l : Filter ι)
    (C K : ι → Set E) :
    cosmicOrdinaryPart (outerSetLimitAlong l (fun i ↦ cosmicSet (C i) (K i))) =
      outerSetLimitAlong l C := by
  ext x
  exact cosmicEmbed_mem_outerSetLimitAlong_cosmicSet_iff

theorem cosmicOrdinaryPart_innerSetLimitAlong_cosmicSet (l : Filter ι)
    (C K : ι → Set E) :
    cosmicOrdinaryPart (innerSetLimitAlong l (fun i ↦ cosmicSet (C i) (K i))) =
      innerSetLimitAlong l C := by
  ext x
  exact cosmicEmbed_mem_innerSetLimitAlong_cosmicSet_iff

end OrdinaryPart

section Definitions

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The family of ordinary sets viewed in cosmic space, with no direction
points inserted beforehand.  For `ι = ℕ` this is `ordinaryCosmicSequence`. -/
noncomputable def ordinaryCosmicFamily (C : ι → Set E) :
    ι → Set (CosmicSpace E) :=
  fun i ↦ cosmicSet (C i) ({0} : Set E)

theorem ordinaryCosmicFamily_eq_ordinaryCosmicSequence (C : ℕ → Set E) :
    ordinaryCosmicFamily C = ordinaryCosmicSequence C := rfl

/-- Formula 4(6) along an arbitrary index filter, outer form. -/
noncomputable def horizonOuterSetLimitAlong (l : Filter ι) (C : ι → Set E) :
    Set E :=
  cosmicDirectionCone (outerSetLimitAlong l (ordinaryCosmicFamily C))

/-- Formula 4(6) along an arbitrary index filter, inner form. -/
noncomputable def horizonInnerSetLimitAlong (l : Filter ι) (C : ι → Set E) :
    Set E :=
  cosmicDirectionCone (innerSetLimitAlong l (ordinaryCosmicFamily C))

/-- The Chapter 4 sequential horizon outer limit is the `atTop` case. -/
theorem horizonOuterSetLimitAlong_atTop (C : ℕ → Set E) :
    horizonOuterSetLimitAlong atTop C = horizonOuterSetLimit C := rfl

/-- The Chapter 4 sequential horizon inner limit is the `atTop` case. -/
theorem horizonInnerSetLimitAlong_atTop (C : ℕ → Set E) :
    horizonInnerSetLimitAlong atTop C = horizonInnerSetLimit C := rfl

@[simp]
theorem cosmicDirection_mem_outer_ordinaryCosmicFamily_iff {l : Filter ι}
    {C : ι → Set E} {u : CosmicBoundary E} :
    cosmicDirection u ∈ outerSetLimitAlong l (ordinaryCosmicFamily C) ↔
      (u : E) ∈ horizonOuterSetLimitAlong l C :=
  cosmicDirection_mem_iff_mem_cosmicDirectionCone

@[simp]
theorem cosmicDirection_mem_inner_ordinaryCosmicFamily_iff {l : Filter ι}
    {C : ι → Set E} {u : CosmicBoundary E} :
    cosmicDirection u ∈ innerSetLimitAlong l (ordinaryCosmicFamily C) ↔
      (u : E) ∈ horizonInnerSetLimitAlong l C :=
  cosmicDirection_mem_iff_mem_cosmicDirectionCone

@[simp]
theorem cosmicEmbed_mem_outer_ordinaryCosmicFamily_iff {l : Filter ι}
    {C : ι → Set E} {x : E} :
    cosmicEmbed x ∈ outerSetLimitAlong l (ordinaryCosmicFamily C) ↔
      x ∈ outerSetLimitAlong l C :=
  cosmicEmbed_mem_outerSetLimitAlong_cosmicSet_iff

@[simp]
theorem cosmicEmbed_mem_inner_ordinaryCosmicFamily_iff {l : Filter ι}
    {C : ι → Set E} {x : E} :
    cosmicEmbed x ∈ innerSetLimitAlong l (ordinaryCosmicFamily C) ↔
      x ∈ innerSetLimitAlong l C :=
  cosmicEmbed_mem_innerSetLimitAlong_cosmicSet_iff

theorem isCone_horizonOuterSetLimitAlong (l : Filter ι) (C : ι → Set E) :
    IsCone (horizonOuterSetLimitAlong l C) :=
  isCone_cosmicDirectionCone _

theorem isCone_horizonInnerSetLimitAlong (l : Filter ι) (C : ι → Set E) :
    IsCone (horizonInnerSetLimitAlong l C) :=
  isCone_cosmicDirectionCone _

theorem isClosed_horizonOuterSetLimitAlong [FiniteDimensional ℝ E]
    (l : Filter ι) (C : ι → Set E) :
    IsClosed (horizonOuterSetLimitAlong l C) :=
  IsClosed.isClosed_cosmicDirectionCone (isClosed_outerSetLimitAlong _ _)

theorem isClosed_horizonInnerSetLimitAlong [FiniteDimensional ℝ E]
    (l : Filter ι) (C : ι → Set E) :
    IsClosed (horizonInnerSetLimitAlong l C) :=
  IsClosed.isClosed_cosmicDirectionCone (isClosed_innerSetLimitAlong _ _)

theorem horizonInnerSetLimitAlong_subset_horizonOuterSetLimitAlong
    (l : Filter ι) [l.NeBot] (C : ι → Set E) :
    horizonInnerSetLimitAlong l C ⊆ horizonOuterSetLimitAlong l C :=
  cosmicDirectionCone_mono (innerSetLimitAlong_subset_outerSetLimitAlong _)

theorem horizonOuterSetLimitAlong_mono {l : Filter ι} {C D : ι → Set E}
    (h : ∀ i, C i ⊆ D i) :
    horizonOuterSetLimitAlong l C ⊆ horizonOuterSetLimitAlong l D :=
  cosmicDirectionCone_mono
    (outerSetLimitAlong_mono fun i ↦ cosmicSet_mono (h i) Subset.rfl)

theorem horizonInnerSetLimitAlong_mono {l : Filter ι} {C D : ι → Set E}
    (h : ∀ i, C i ⊆ D i) :
    horizonInnerSetLimitAlong l C ⊆ horizonInnerSetLimitAlong l D :=
  cosmicDirectionCone_mono
    (innerSetLimitAlong_mono fun i ↦ cosmicSet_mono (h i) Subset.rfl)

/-- Both horizon limits along a filter only see the eventual behavior of the
family. -/
theorem horizonOuterSetLimitAlong_congr {l : Filter ι} {C D : ι → Set E}
    (h : C =ᶠ[l] D) :
    horizonOuterSetLimitAlong l C = horizonOuterSetLimitAlong l D := by
  have hfam : ordinaryCosmicFamily C =ᶠ[l] ordinaryCosmicFamily D :=
    h.mono fun i hi ↦ by simp only [ordinaryCosmicFamily, hi]
  rw [horizonOuterSetLimitAlong, horizonOuterSetLimitAlong,
    outerSetLimitAlong_congr hfam]

theorem horizonInnerSetLimitAlong_congr {l : Filter ι} {C D : ι → Set E}
    (h : C =ᶠ[l] D) :
    horizonInnerSetLimitAlong l C = horizonInnerSetLimitAlong l D := by
  have hfam : ordinaryCosmicFamily C =ᶠ[l] ordinaryCosmicFamily D :=
    h.mono fun i hi ↦ by simp only [ordinaryCosmicFamily, hi]
  rw [horizonInnerSetLimitAlong, horizonInnerSetLimitAlong,
    innerSetLimitAlong_congr hfam]

/-- The cosmic outer limit of a family of ordinary sets splits into the
ordinary outer limit and the horizon outer limit.  This is Exercise 4.20 with
`K(i) = {0}`, along an arbitrary filter. -/
theorem outerSetLimitAlong_ordinaryCosmicFamily (l : Filter ι)
    (C : ι → Set E) :
    outerSetLimitAlong l (ordinaryCosmicFamily C) =
      cosmicSet (outerSetLimitAlong l C) (horizonOuterSetLimitAlong l C) := by
  conv_lhs => rw [← cosmicSet_parts (outerSetLimitAlong l (ordinaryCosmicFamily C))]
  congr 1
  exact cosmicOrdinaryPart_outerSetLimitAlong_cosmicSet l C fun _ ↦ ({0} : Set E)

/-- The inner form of the same splitting. -/
theorem innerSetLimitAlong_ordinaryCosmicFamily (l : Filter ι)
    (C : ι → Set E) :
    innerSetLimitAlong l (ordinaryCosmicFamily C) =
      cosmicSet (innerSetLimitAlong l C) (horizonInnerSetLimitAlong l C) := by
  conv_lhs => rw [← cosmicSet_parts (innerSetLimitAlong l (ordinaryCosmicFamily C))]
  congr 1
  exact cosmicOrdinaryPart_innerSetLimitAlong_cosmicSet l C fun _ ↦ ({0} : Set E)

/-- **Exercise 4.21(c)** along an arbitrary index filter: a set contained in
the inner limit has its horizon cone inside the horizon inner limit.  The
Chapter 4 proof never mentions the index, once the ordinary part of a cosmic
inner limit is available. -/
theorem horizonCone_subset_horizonInnerSetLimitAlong [FiniteDimensional ℝ E]
    {l : Filter ι} {Cf : ι → Set E} {C : Set E}
    (hC : C ⊆ innerSetLimitAlong l Cf) :
    horizonCone C ⊆ horizonInnerSetLimitAlong l Cf := by
  have hraw : cosmicSet C ({0} : Set E) ⊆
      innerSetLimitAlong l (ordinaryCosmicFamily Cf) := by
    intro p hp
    rw [mem_cosmicSet] at hp
    rcases hp with ⟨x, hx, rfl⟩ | ⟨u, hu0, rfl⟩
    · exact cosmicEmbed_mem_innerSetLimitAlong_cosmicSet_iff.2 (hC hx)
    · have huZero : (u : E) = 0 := by simpa using hu0
      have huNorm : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
      simp [huZero] at huNorm
  have hclosure : closure (cosmicSet C ({0} : Set E)) ⊆
      innerSetLimitAlong l (ordinaryCosmicFamily Cf) :=
    closure_minimal hraw (isClosed_innerSetLimitAlong _ _)
  intro w hw
  by_cases hw0 : w = 0
  · simpa [hw0] using (isCone_horizonInnerSetLimitAlong l Cf).1
  · have huHor : ((cosmicDirectionOf w hw0 : CosmicBoundary E) : E) ∈
        horizonCone C := by
      change NormedSpace.normalize w ∈ horizonCone C
      exact (isCone_horizonCone C).smul_mem hw
        (inv_nonneg.mpr (norm_nonneg w))
    have huInner : ((cosmicDirectionOf w hw0 : CosmicBoundary E) : E) ∈
        horizonInnerSetLimitAlong l Cf :=
      cosmicDirection_mem_inner_ordinaryCosmicFamily_iff.1
        (hclosure (cosmicDirection_mem_closure_cosmicSet_of_mem_horizonCone huHor))
    have hscaled := (isCone_horizonInnerSetLimitAlong l Cf).smul_mem huInner
      (norm_nonneg w)
    simpa only [coe_cosmicDirectionOf, NormedSpace.norm_smul_normalize w]
      using hscaled

end Definitions

end RW
