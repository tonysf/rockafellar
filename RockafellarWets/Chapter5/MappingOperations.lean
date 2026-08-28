/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Operations on Set-Valued Mappings

Propositions 5.51 and 5.52, on sums and compositions.

Both outer semicontinuity clauses run on the same device, and it is worth
naming: the sum and the composition are each the *domain* of an auxiliary
mapping whose graph is visibly closed, and 5.25 turns local boundedness of
that auxiliary mapping into closedness of its domain.  For the sum the
auxiliary mapping is `R(x, y) = S(x) ∩ (y - T(x))`, whose domain is
`gph(S + T)`; for the composition it is `R(x, w) = S(x) ∩ T⁻¹(w)`, whose
domain is `gph(T ∘ S)`.

The book describes each `gph R` by an explicit parameterization -- for the
sum, the intersection of `{(x, y, u) | (x, u) ∈ gph S}` with
`{(x, y, y - u) | (x, u) ∈ gph T}`.  Here each is instead read as a *preimage*
of `gph S` or `gph T` under a continuous map of the ambient product, which is
shorter and needs no closedness of images.
-/

import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Analysis.Normed.Module.FiniteDimension
import RockafellarWets.Chapter4.FiniteSumConvergence
import RockafellarWets.Chapter5.ClosedImages
import RockafellarWets.Chapter5.ImageConvergence
import RockafellarWets.Chapter5.PerturbedMappings

open Bornology Filter Set Topology
open scoped Pointwise

namespace RW

section Sum

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {S T : E → Set F} {x : E}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- **Proposition 5.51(a)**, at a point. -/
theorem SvLocallyBoundedAt.svAdd (hS : SvLocallyBoundedAt S x)
    (hT : SvLocallyBoundedAt T x) : SvLocallyBoundedAt (svAdd S T) x := by
  obtain ⟨V, hV, hVb⟩ := hS
  obtain ⟨W, hW, hWb⟩ := hT
  refine ⟨V ∩ W, Filter.inter_mem hV hW, IsBounded.subset (Bornology.IsBounded.add hVb hWb) ?_⟩
  rintro u hu
  obtain ⟨z, hz, hu⟩ := mem_svImage.1 hu
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_svAdd.1 hu
  exact Set.add_mem_add (mem_svImage.2 ⟨z, hz.1, ha⟩) (mem_svImage.2 ⟨z, hz.2, hb⟩)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- **Proposition 5.51(a)**: a sum of locally bounded mappings is locally
bounded. -/
theorem SvLocallyBounded.svAdd (hS : SvLocallyBounded S)
    (hT : SvLocallyBounded T) : SvLocallyBounded (svAdd S T) :=
  fun x ↦ (hS x).svAdd (hT x)

/-- The auxiliary mapping `R(x, y) = S(x) ∩ (y - T(x))` of 5.51(b). -/
def svAddAux (S T : E → Set F) : E × F → Set F :=
  fun p ↦ S p.1 ∩ (({p.2} : Set F) - T p.1)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
@[simp]
theorem mem_svAddAux {p : E × F} {u : F} :
    u ∈ svAddAux S T p ↔ u ∈ S p.1 ∧ p.2 - u ∈ T p.1 := by
  simp only [svAddAux, mem_inter_iff, Set.singleton_sub, mem_image,
    and_congr_right_iff]
  intro _
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨p.2 - u, h, by abel⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The domain of the auxiliary mapping is the graph of the sum: this is what
turns 5.25 into outer semicontinuity of `S + T`. -/
theorem svDom_svAddAux (S T : E → Set F) :
    svDom (svAddAux S T) = svGraph (svAdd S T) := by
  ext p
  constructor
  · rintro ⟨u, hu⟩
    rw [mem_svAddAux] at hu
    exact mem_svAdd.2 ⟨u, hu.1, p.2 - u, hu.2, by abel⟩
  · intro hp
    obtain ⟨a, ha, b, hb, hab⟩ := mem_svAdd.1 hp
    exact ⟨a, mem_svAddAux.2 ⟨ha, by rw [← hab]; simpa using hb⟩⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- The graph of the auxiliary mapping is the intersection of two preimages of
`gph S` and `gph T` under continuous maps, hence closed. -/
theorem svOsc_svAddAux (hS : SvOsc S) (hT : SvOsc T) : SvOsc (svAddAux S T) := by
  refine isClosed_svGraph_iff_svOsc.1 ?_
  have hset : svGraph (svAddAux S T) =
      (fun q : (E × F) × F ↦ (q.1.1, q.2)) ⁻¹' svGraph S ∩
        (fun q : (E × F) × F ↦ (q.1.1, q.1.2 - q.2)) ⁻¹' svGraph T := by
    ext q
    exact mem_svAddAux
  rw [hset]
  refine IsClosed.inter ?_ ?_
  · exact (isClosed_svGraph_iff_svOsc.2 hS).preimage
      (by fun_prop)
  · exact (isClosed_svGraph_iff_svOsc.2 hT).preimage
      (by fun_prop)

/-- **Proposition 5.51(b)**. -/
theorem SvOsc.svAdd (hS : SvOsc S) (hT : SvOsc T)
    (hR : SvLocallyBounded (svAddAux S T)) : SvOsc (svAdd S T) :=
  isClosed_svGraph_iff_svOsc.1
    (svDom_svAddAux S T ▸ (svOsc_svAddAux hS hT).isClosed_svDom hR)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- **Proposition 5.51(b)**, first parenthetical: the auxiliary mapping is
locally bounded when `S` is, since `R(x, y) ⊂ S(x)`. -/
theorem svLocallyBounded_svAddAux_left (hS : SvLocallyBounded S) :
    SvLocallyBounded (svAddAux S T) := by
  rintro ⟨x, y⟩
  obtain ⟨V, hV, hVb⟩ := hS x
  refine ⟨V ×ˢ univ, prod_mem_nhds hV univ_mem, IsBounded.subset hVb ?_⟩
  rintro u hu
  obtain ⟨p, hp, hu⟩ := mem_svImage.1 hu
  exact mem_svImage.2 ⟨p.1, hp.1, (mem_svAddAux.1 hu).1⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- **Proposition 5.51(b)**, second parenthetical: the auxiliary mapping is
locally bounded when `T` is, since `R(x, y) ⊂ y - T(x)`. -/
theorem svLocallyBounded_svAddAux_right (hT : SvLocallyBounded T) :
    SvLocallyBounded (svAddAux S T) := by
  rintro ⟨x, y⟩
  obtain ⟨V, hV, hVb⟩ := hT x
  have hball : IsBounded (Metric.ball y 1) := Metric.isBounded_ball
  refine ⟨V ×ˢ Metric.ball y 1,
    prod_mem_nhds hV (Metric.ball_mem_nhds y one_pos),
    IsBounded.subset (Bornology.IsBounded.sub hball hVb) ?_⟩
  rintro u hu
  obtain ⟨p, hp, hu⟩ := mem_svImage.1 hu
  have hmem := Set.sub_mem_sub hp.2
    (mem_svImage.2 ⟨p.1, hp.1, (mem_svAddAux.1 hu).2⟩)
  simpa using hmem

end Sum

section SequentialContinuity

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- Definition 5.4 read over sequences: continuity at `x̄` is convergence of
`S(xν)` to `S(x̄)` along every sequence `xν → x̄`.  This is the two bridges of
`SequentialLimits.lean` put together, and it is what lets the sequential
results of 5.30 be applied to the values of a continuous mapping. -/
theorem svContinuousAt_iff_forall_seq [FirstCountableTopology E]
    [FirstCountableTopology F] {S : E → Set F} {x : E} :
    SvContinuousAt S x ↔
      ∀ y : ℕ → E, Tendsto y atTop (nhds x) →
        PKConverges (fun n ↦ S (y n)) (S x) := by
  constructor
  · rintro ⟨hosc, hisc⟩ y hy
    have houter : outerSetLimit (fun n ↦ S (y n)) ⊆ S x := by
      refine subset_trans ?_ hosc
      rw [svOuterLimit_eq_iUnion S x]
      exact subset_iUnion₂ (s := fun y (_ : y ∈ {y : ℕ → E |
        Tendsto y atTop (nhds x)}) ↦ outerSetLimit fun n ↦ S (y n)) y hy
    have hinner : S x ⊆ innerSetLimit (fun n ↦ S (y n)) := by
      refine subset_trans hisc ?_
      rw [svInnerLimit_eq_iInter S x]
      exact iInter₂_subset y hy
    exact ⟨Subset.antisymm
        ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner,
      Subset.antisymm houter
        (hinner.trans (innerSetLimit_subset_outerSetLimit _))⟩
  · intro h
    constructor
    · rw [SvOscAt, svOuterLimit_eq_iUnion S x]
      exact iUnion₂_subset fun y hy ↦ (h y hy).outer_eq.subset
    · rw [SvIscAt, svInnerLimit_eq_iInter S x]
      exact subset_iInter₂ fun y hy ↦ (h y hy).inner_eq.ge

end SequentialContinuity

section SequentialTotalContinuity

variable {ι : Type*}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- The cosmic form of `outerSetLimit_comp_subset`: a horizon outer limit
along a sequence drawn from `l` is no larger than the horizon outer limit
along `l`. -/
theorem horizonOuterSetLimit_comp_subset {l : Filter ι} {C : ι → Set F}
    {y : ℕ → ι} (hy : Tendsto y atTop l) :
    horizonOuterSetLimit (C ∘ y) ⊆ horizonOuterSetLimitAlong l C := by
  refine cosmicDirectionCone_mono ?_
  have hseq : ordinaryCosmicSequence (C ∘ y) = ordinaryCosmicFamily C ∘ y := rfl
  rw [hseq]
  exact outerSetLimit_comp_subset hy

variable {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]

/-- Definition 5.28 read over sequences, in the direction the sequential
results of Chapter 4 consume: total continuity at `x̄` gives total convergence
of the values along every approaching sequence. -/
theorem SvTotallyContinuousAt.totalConverges_comp {S : E → Set F} {x : E}
    {y : ℕ → E} (h : SvTotallyContinuousAt S x)
    (hy : Tendsto y atTop (nhds x)) :
    TotalConverges (fun n ↦ S (y n)) (S x) := by
  have hcont : SvContinuousAt S x :=
    ⟨h.pkConvergesAlong.outer_eq.subset, h.pkConvergesAlong.inner_eq.ge⟩
  refine totalConverges_iff_pkConverges_and_horizonOuter_subset.2
    ⟨svContinuousAt_iff_forall_seq.1 hcont y hy, ?_⟩
  exact (horizonOuterSetLimit_comp_subset hy).trans h.horizonOuter_subset

omit [FiniteDimensional ℝ F] in
/-- **The horizon extraction.**  Every horizon direction of a family along a
countably generated filter is a horizon direction along a single sequence
drawn from that filter.  The cosmic space is first countable, so this is the
diagonal extraction of `SequentialLimits.lean` applied there and read back
through `cosmicDirectionCone`. -/
theorem exists_seq_mem_horizonOuterSetLimit {l : Filter ι} [l.NeBot]
    [l.IsCountablyGenerated] {C : ι → Set F} {w : F}
    (hw : w ∈ horizonOuterSetLimitAlong l C) :
    ∃ y : ℕ → ι, Tendsto y atTop l ∧ w ∈ horizonOuterSetLimit (C ∘ y) := by
  obtain ⟨y₀, hy₀⟩ := l.exists_seq_tendsto
  rcases hw with rfl | ⟨u, hu, r, hr, rfl⟩
  · exact ⟨y₀, hy₀, Or.inl rfl⟩
  · obtain ⟨y, hy, hmem⟩ := exists_seq_mem_innerSetLimit hu
    exact ⟨y, hy, Or.inr ⟨u, innerSetLimit_subset_outerSetLimit _ hmem, r, hr, rfl⟩⟩

omit [FiniteDimensional ℝ F] in
/-- The horizon half of Definition 5.28 is decided by sequences. -/
theorem svHorizonOuterLimit_subset_of_forall_seq {S : E → Set F} {x : E}
    {K : Set F} (h : ∀ y : ℕ → E, Tendsto y atTop (nhds x) →
      horizonOuterSetLimit (fun n ↦ S (y n)) ⊆ K) :
    svHorizonOuterLimit S x ⊆ K := by
  intro w hw
  obtain ⟨y, hy, hmem⟩ := exists_seq_mem_horizonOuterSetLimit hw
  exact h y hy hmem

/-- **Definition 5.28 read over sequences**: total continuity at `x̄` is total
convergence of the values along every approaching sequence.  Both directions
are used below, the forward one to feed the sequential results of 5.30 and the
backward one to assemble their conclusions. -/
theorem svTotallyContinuousAt_iff_forall_seq {S : E → Set F} {x : E} :
    SvTotallyContinuousAt S x ↔
      ∀ y : ℕ → E, Tendsto y atTop (nhds x) →
        TotalConverges (fun n ↦ S (y n)) (S x) := by
  refine ⟨fun h y hy ↦ h.totalConverges_comp hy, fun h ↦ ?_⟩
  refine svTotallyContinuousAt_iff.2 ⟨svContinuousAt_iff_forall_seq.2
    fun y hy ↦ (h y hy).pkConverges, ?_⟩
  exact svHorizonOuterLimit_subset_of_forall_seq fun y hy ↦
    (totalConverges_iff_pkConverges_and_horizonOuter_subset.1 (h y hy)).2

end SequentialTotalContinuity

section SumTotalContinuity

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {S T : E → Set F} {x : E}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Proposition 5.51(c)**: total continuity of a sum.  This is 4.29(d) in
two-term form, read along an approaching sequence through
`svTotallyContinuousAt_iff_forall_seq`. -/
theorem svTotallyContinuousAt_svAdd
    (hS : SvTotallyContinuousAt S x) (hT : SvTotallyContinuousAt T x)
    (hprod : horizonCone (S x ×ˢ T x) = horizonCone (S x) ×ˢ horizonCone (T x))
    (hopp : horizonCone (S x) ∩ -(horizonCone (T x)) = ({0} : Set F)) :
    SvTotallyContinuousAt (svAdd S T) x := by
  rw [svTotallyContinuousAt_iff_forall_seq]
  intro y hy
  exact TotalConverges.add_of_horizon_prod (hS.totalConverges_comp hy)
    (hT.totalConverges_comp hy) hprod hopp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Proposition 5.51(c)**, convexity clause: the product-horizon hypothesis
is 3.11 for nonempty convex values. -/
theorem horizonCone_prod_eq_of_convex_values (hSc : Convex ℝ (S x))
    (hTc : Convex ℝ (T x)) (hSne : (S x).Nonempty) (hTne : (T x).Nonempty) :
    horizonCone (S x ×ˢ T x) = horizonCone (S x) ×ˢ horizonCone (T x) :=
  horizonCone_prod_eq_of_convex_nonempty hSc hTc hSne hTne

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem svAdd_comm (S T : E → Set F) : svAdd S T = svAdd T S := by
  funext z
  exact add_comm (S z) (T z)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Proposition 5.51(c)**, local-boundedness clause: both hypotheses hold as
soon as the second mapping is locally bounded at `x̄` with a nonempty value
there, by 3.11 and 3.5. -/
theorem svTotallyContinuousAt_svAdd_of_svLocallyBoundedAt_right
    (hS : SvTotallyContinuousAt S x) (hT : SvTotallyContinuousAt T x)
    (hTne : (T x).Nonempty) (hTb : SvLocallyBoundedAt T x) :
    SvTotallyContinuousAt (svAdd S T) x := by
  have hTzero : horizonCone (T x) = ({0} : Set F) :=
    isBounded_iff_horizonCone_eq_singleton_zero.mp hTb.isBounded_apply
  refine svTotallyContinuousAt_svAdd hS hT ?_ ?_
  · rw [horizonCone_prod_eq_of_bounded_right hTne hTb.isBounded_apply, hTzero]
  · rw [hTzero, Set.neg_singleton, neg_zero, Set.inter_eq_right]
    exact Set.singleton_subset_iff.2 (zero_mem_horizonCone _)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Proposition 5.51(c)**, local-boundedness clause on the other side. -/
theorem svTotallyContinuousAt_svAdd_of_svLocallyBoundedAt_left
    (hS : SvTotallyContinuousAt S x) (hT : SvTotallyContinuousAt T x)
    (hSne : (S x).Nonempty) (hSb : SvLocallyBoundedAt S x) :
    SvTotallyContinuousAt (svAdd S T) x := by
  rw [svAdd_comm]
  exact svTotallyContinuousAt_svAdd_of_svLocallyBoundedAt_right hT hS hSne hSb

end SumTotalContinuity

section CompositionDefs

variable {E F G : Type*} {S : E → Set F} {T : F → Set G}

/-- The composition `(T ∘ S)(x) = T(S(x))` of 5.52. -/
def svComp (T : F → Set G) (S : E → Set F) : E → Set G :=
  fun x ↦ svImage T (S x)

@[simp]
theorem mem_svComp {x : E} {u : G} :
    u ∈ svComp T S x ↔ ∃ w ∈ S x, u ∈ T w := mem_svImage

theorem svImage_svComp (T : F → Set G) (S : E → Set F) (V : Set E) :
    svImage (svComp T S) V = svImage T (svImage S V) := by
  ext u
  simp only [mem_svImage, mem_svComp]
  constructor
  · rintro ⟨z, hz, w, hw, hu⟩
    exact ⟨w, ⟨z, hz, hw⟩, hu⟩
  · rintro ⟨w, ⟨z, hz, hw⟩, hu⟩
    exact ⟨z, hz, w, hw, hu⟩

/-- The auxiliary mapping `R(x, w) = S(x) ∩ T⁻¹(w)` of 5.52(b). -/
def svCompAux (T : F → Set G) (S : E → Set F) : E × G → Set F :=
  fun p ↦ S p.1 ∩ svInv T p.2

@[simp]
theorem mem_svCompAux {p : E × G} {u : F} :
    u ∈ svCompAux T S p ↔ u ∈ S p.1 ∧ p.2 ∈ T u := Iff.rfl

/-- The domain of the auxiliary mapping is the graph of the composition. -/
theorem svDom_svCompAux (T : F → Set G) (S : E → Set F) :
    svDom (svCompAux T S) = svGraph (svComp T S) := by
  ext p
  constructor
  · rintro ⟨u, hu⟩
    exact mem_svComp.2 ⟨u, hu.1, hu.2⟩
  · intro hp
    obtain ⟨w, hw, hu⟩ := mem_svComp.1 hp
    exact ⟨w, hw, hu⟩

end CompositionDefs

section Composition

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
variable {S : E → Set F} {T : F → Set G}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] in
/-- **Proposition 5.52(a)**: by 5.15, a composition of locally bounded
mappings carries bounded sets to bounded sets. -/
theorem SvLocallyBounded.svComp (hS : SvLocallyBounded S)
    (hT : SvLocallyBounded T) : SvLocallyBounded (svComp T S) := by
  intro x
  obtain ⟨V, hV, hVb⟩ := hS x
  refine ⟨V, hV, ?_⟩
  rw [svImage_svComp]
  exact svLocallyBounded_iff_isBounded_svImage.1 hT _ hVb

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedSpace ℝ G] [FiniteDimensional ℝ G] in
/-- The graph of the auxiliary mapping is again an intersection of two
preimages, of `gph S` and of `gph T`. -/
theorem svOsc_svCompAux (hS : SvOsc S) (hT : SvOsc T) :
    SvOsc (svCompAux T S) := by
  refine isClosed_svGraph_iff_svOsc.1 ?_
  have hset : svGraph (svCompAux T S) =
      (fun q : (E × G) × F ↦ (q.1.1, q.2)) ⁻¹' svGraph S ∩
        (fun q : (E × G) × F ↦ (q.2, q.1.2)) ⁻¹' svGraph T := by
    ext q
    exact mem_svCompAux
  rw [hset]
  exact ((isClosed_svGraph_iff_svOsc.2 hS).preimage (by fun_prop)).inter
    ((isClosed_svGraph_iff_svOsc.2 hT).preimage (by fun_prop))

/-- **Proposition 5.52(b)**. -/
theorem SvOsc.svComp (hS : SvOsc S) (hT : SvOsc T)
    (hR : SvLocallyBounded (svCompAux T S)) : SvOsc (svComp T S) :=
  isClosed_svGraph_iff_svOsc.1
    (svDom_svCompAux T S ▸ (svOsc_svCompAux hS hT).isClosed_svDom hR)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedSpace ℝ G] [FiniteDimensional ℝ G] in
/-- **Proposition 5.52(b)**, first parenthetical: `R(x, w) ⊂ S(x)`. -/
theorem svLocallyBounded_svCompAux_left (hS : SvLocallyBounded S) :
    SvLocallyBounded (svCompAux T S) := by
  rintro ⟨x, w⟩
  obtain ⟨V, hV, hVb⟩ := hS x
  refine ⟨V ×ˢ univ, prod_mem_nhds hV univ_mem, IsBounded.subset hVb ?_⟩
  rintro u hu
  obtain ⟨p, hp, hu⟩ := mem_svImage.1 hu
  exact mem_svImage.2 ⟨p.1, hp.1, (mem_svCompAux.1 hu).1⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedSpace ℝ G] [FiniteDimensional ℝ G] in
/-- **Proposition 5.52(b)**, second parenthetical: `R(x, w) ⊂ T⁻¹(w)`. -/
theorem svLocallyBounded_svCompAux_right (hT : SvLocallyBounded (svInv T)) :
    SvLocallyBounded (svCompAux T S) := by
  rintro ⟨x, w⟩
  obtain ⟨W, hW, hWb⟩ := hT w
  refine ⟨univ ×ˢ W, prod_mem_nhds univ_mem hW, IsBounded.subset hWb ?_⟩
  rintro u hu
  obtain ⟨p, hp, hu⟩ := mem_svImage.1 hu
  exact mem_svImage.2 ⟨p.2, hp.2, (mem_svCompAux.1 hu).2⟩

/-- A sequence eventually inside a bounded set has bounded range, the finitely
many early terms being harmless. -/
private theorem isBounded_range_of_eventually_mem {α : Type*}
    [PseudoMetricSpace α] {p : ℕ → α} {B : Set α} (hB : IsBounded B)
    (h : ∀ᶠ n in atTop, p n ∈ B) : IsBounded (Set.range p) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine IsBounded.subset (((Set.finite_Iio N).image p).isBounded.union hB) ?_
  rintro _ ⟨n, rfl⟩
  rcases lt_or_ge n N with hn | hn
  · exact Or.inl ⟨n, hn, rfl⟩
  · exact Or.inr (hN n hn)

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] in
/-- A third alternative to the two the book lists for the no-escape condition
of 5.30(b): if the argument sets are eventually contained in one bounded set,
nothing can escape.  This is what local boundedness of the inner mapping
supplies in 5.52(c). -/
theorem noConvergentImageEscapeAlong_snd_of_eventually_subset
    (T : F → Set G) {C : ℕ → Set F} {B : Set F} (hB : IsBounded B)
    (hC : ∀ᶠ n in atTop, C n ⊆ B) :
    NoConvergentImageEscapeAlong (Prod.snd : F × G → G)
      (fun n ↦ svGraph T ∩ Prod.fst ⁻¹' C n) := by
  intro φ p u hφ hpG hpu
  have hsnd : IsBounded (Set.range (Prod.snd ∘ p)) :=
    Metric.isBounded_range_of_tendsto _ hpu
  have hfst : IsBounded (Set.range (Prod.fst ∘ p)) := by
    refine isBounded_range_of_eventually_mem hB ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 hC
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN (φ n) (le_trans hn hφ.le_apply) (hpG n).2
  refine IsBounded.subset (hfst.prod hsnd) ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨⟨n, rfl⟩, ⟨n, rfl⟩⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Proposition 5.52(c)**.  The book obtains this from the second version of
(d); here it is 5.30(c) directly, the local boundedness of `S` supplying the
no-escape condition without any horizon hypothesis at all. -/
theorem SvContinuous.svComp (hS : SvContinuous S) (hT : SvContinuous T)
    (hlb : SvLocallyBounded S) : SvContinuous (svComp T S) := by
  intro x
  rw [svContinuousAt_iff_forall_seq]
  intro y hy
  obtain ⟨V, hV, hVb⟩ := hlb x
  have hpk : PKConverges (fun n ↦ S (y n)) (S x) :=
    svContinuousAt_iff_forall_seq.1 (hS x) y hy
  have hev : ∀ᶠ n in atTop, S (y n) ⊆ svImage S V := by
    filter_upwards [hy.eventually_mem hV] with n hn
    exact fun u hu ↦ mem_svImage.2 ⟨y n, hn, hu⟩
  exact PKConverges.svImage_of_noEscape hpk hT
    (noConvergentImageEscapeAlong_snd_of_eventually_subset T hVb hev)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Proposition 5.52(d)**, first version: `S` continuous at `x̄`, `T`
continuous with `T⁻¹` locally bounded.  This is 5.30(c), first alternative,
read along an approaching sequence. -/
theorem SvContinuousAt.svComp_of_svLocallyBounded_svInv {x : E}
    (hS : SvContinuousAt S x) (hT : SvContinuous T)
    (hlb : SvLocallyBounded (svInv T)) : SvContinuousAt (svComp T S) x := by
  rw [svContinuousAt_iff_forall_seq]
  intro y hy
  exact PKConverges.svImage_of_svLocallyBounded_svInv
    (svContinuousAt_iff_forall_seq.1 hS y hy) hT hlb

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Proposition 5.52(d)**, second version: `S` totally continuous at `x̄`,
`T` continuous with `(T∞)⁻¹(0) ∩ S(x̄)∞ = {0}`.  This is 5.30(c), second
alternative, read along an approaching sequence. -/
theorem svContinuousAt_svComp_of_svTotallyContinuousAt {x : E}
    (hS : SvTotallyContinuousAt S x) (hT : SvContinuous T)
    (h : svInv (svHorizon T) 0 ∩ horizonCone (S x) = ({0} : Set F)) :
    SvContinuousAt (svComp T S) x := by
  rw [svContinuousAt_iff_forall_seq]
  intro y hy
  exact TotalConverges.pkConverges_svImage (hS.totalConverges_comp hy) hT h

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Proposition 5.52(e)**: total continuity of the composition.  This is
5.30(d) read along an approaching sequence, the sequential criterion of
`svTotallyContinuousAt_iff_forall_seq` serving in both directions -- forward to
supply total convergence of the arguments, backward to reassemble the
conclusion. -/
theorem svTotallyContinuousAt_svComp {x : E}
    (hS : SvTotallyContinuousAt S x) (hT : SvTotallyContinuous T)
    (h : svInv (svHorizon T) 0 ∩ horizonCone (S x) = ({0} : Set F))
    (himg : svImage (svHorizon T) (horizonCone (S x)) ⊆
      horizonCone (svImage T (S x))) :
    SvTotallyContinuousAt (svComp T S) x := by
  rw [svTotallyContinuousAt_iff_forall_seq]
  intro y hy
  exact TotalConverges.svImage_of_svTotallyContinuous
    (hS.totalConverges_comp hy) hT h himg

end Composition

end RW
