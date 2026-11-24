/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Compositions and Carathéodory images

Theorem 14.13 (composition of mappings), Corollary 14.14, Example 14.15 (images under
Carathéodory mappings), Theorem 14.16 (implicit measurable functions), Exercise 14.17
(projection mappings), Exercise 14.18 (mixed operations) and Example 14.19 (variable scalar
multiplication) of Rockafellar–Wets.

The spaces `ℝⁿ`, `ℝᵐ` of the book are proper metric spaces (finite-dimensional normed spaces
where linear structure is used), with their Borel σ-fields.
-/

import RockafellarWets.Chapter14.MeasurabilityOperations
import RockafellarWets.Chapter5.ProjectionMappings

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace RW

section Theorem1413

variable {T F G : Type*} [MeasurableSpace T]

/-- **Theorem 14.13(a)**: if `S` is measurable and `M` is inner semicontinuous, then
`t ↦ M(S(t))` is measurable. -/
theorem SvMeasurable.comp_svIsc [TopologicalSpace F] [TopologicalSpace G] {S : T → Set F}
    (hS : SvMeasurable S) {M : F → Set G} (hM : SvIsc M) : SvMeasurable (RW.svComp M S) := by
  intro O hO
  have : svPreimage (RW.svComp M S) O = svPreimage S (svPreimage M O) := by
    ext t
    simp only [mem_svPreimage]
    constructor
    · rintro ⟨u, hu, huO⟩
      obtain ⟨w, hw, hwu⟩ := mem_svComp.1 hu
      exact ⟨w, hw, u, hwu, huO⟩
    · rintro ⟨w, hw, u, hwu, huO⟩
      exact ⟨u, mem_svComp.2 ⟨w, hw, hwu⟩, huO⟩
  rw [this]
  exact hS _ (svIsc_iff_isOpen_svPreimage.1 hM O hO)

variable [MetricSpace F] [ProperSpace F] [MetricSpace G] [ProperSpace G]

/-- **Theorem 14.13(b)**: for closed-valued measurable `S` and mappings `M(t, ·)` with closed
graphs (osc mappings) depending measurably on `t`, the mapping `t ↦ M(t, S(t))` is
measurable. -/
theorem SvMeasurable.svImage_of_svGraph {S : T → Set F} (hS : SvMeasurable S)
    (hSc : ∀ t, IsClosed (S t)) {M : T → F → Set G} (hMosc : ∀ t, SvOsc (M t))
    (hM : SvMeasurable (fun t ↦ svGraph (M t))) :
    SvMeasurable (fun t ↦ svImage (M t) (S t)) := by
  have hQ : SvMeasurable (fun t ↦ svGraph (M t) ∩ Prod.fst ⁻¹' S t) := by
    have h := hM.inter (hS.prod (svMeasurable_const (univ : Set G)))
      (fun t ↦ isClosed_svGraph_iff_svOsc.2 (hMosc t)) (fun t ↦ (hSc t).prod isClosed_univ)
    simpa only [prod_univ] using h
  have heq : (fun t ↦ svImage (M t) (S t)) =
      fun t ↦ Prod.snd '' (svGraph (M t) ∩ Prod.fst ⁻¹' S t) :=
    funext fun t ↦ svImage_eq_image_snd (M t) (S t)
  rw [heq]
  exact hQ.image continuous_snd

/-- The book's statement of Theorem 14.13(b) when `M(t, ·) ≡ M` does not depend on `t`. -/
theorem SvMeasurable.svImage_of_svOsc {S : T → Set F} (hS : SvMeasurable S)
    (hSc : ∀ t, IsClosed (S t)) {M : F → Set G} (hM : SvOsc M) :
    SvMeasurable (fun t ↦ svImage M (S t)) :=
  hS.svImage_of_svGraph hSc (fun _ ↦ hM) (svMeasurable_const _)

/-- **Theorem 14.13 (composition of mappings)**, both parts. -/
theorem composition_of_mappings :
    (∀ {S : T → Set F} {M : F → Set G}, SvMeasurable S → SvIsc M →
        SvMeasurable (RW.svComp M S)) ∧
      (∀ {S : T → Set F} {M : T → F → Set G}, SvMeasurable S → (∀ t, IsClosed (S t)) →
        (∀ t, SvOsc (M t)) → SvMeasurable (fun t ↦ svGraph (M t)) →
          SvMeasurable (fun t ↦ svImage (M t) (S t))) :=
  ⟨fun hS hM ↦ hS.comp_svIsc hM, fun hS hSc hMosc hM ↦ hS.svImage_of_svGraph hSc hMosc hM⟩

variable [MeasurableSpace F] [BorelSpace F]

/-- **Corollary 14.14 (composition with measurable functions)**: `t ↦ M(t, x(t))` is
closed-valued and measurable. -/
theorem composition_with_measurable_functions {M : T → F → Set G} (hMosc : ∀ t, SvOsc (M t))
    (hM : SvMeasurable (fun t ↦ svGraph (M t))) {x : T → F} (hx : Measurable x) :
    (∀ t, IsClosed (M t (x t))) ∧ SvMeasurable (fun t ↦ M t (x t)) := by
  refine ⟨fun t ↦ ?_, ?_⟩
  · have hc := isClosed_svGraph_iff_svOsc.2 (hMosc t)
    have : M t (x t) = (fun u ↦ (x t, u)) ⁻¹' svGraph (M t) := rfl
    rw [this]
    exact hc.preimage (Continuous.prodMk_right (x t))
  · have h := (svMeasurable_singleton_iff.2 hx).svImage_of_svGraph (fun t ↦ isClosed_singleton)
      hMosc hM
    have heq : (fun t ↦ svImage (M t) {x t}) = fun t ↦ M t (x t) := by
      funext t
      ext u
      simp [mem_svImage]
    rwa [heq] at h

end Theorem1413

section Example1415

variable {T E G : Type*} [MeasurableSpace T]

/-- A **Carathéodory mapping** `Φ : T × E → G`: measurable in `t` for each fixed `x` and
continuous in `x` for each fixed `t` (Example 14.15). -/
def IsCaratheodory [TopologicalSpace E] [TopologicalSpace G] [MeasurableSpace G]
    (Φ : T → E → G) : Prop :=
  (∀ x, Measurable fun t ↦ Φ t x) ∧ ∀ t, Continuous (Φ t)

variable [MetricSpace E] [ProperSpace E] [MetricSpace G] [ProperSpace G]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]

/-- The graph `t ↦ gph Φ(t, ·)` of a Carathéodory mapping is closed-valued and measurable,
through the Castaing representation `t ↦ (q, Φ(t, q))` over a countable dense set of `q`. -/
theorem IsCaratheodory.svMeasurable_graph {Φ : T → E → G} (hΦ : IsCaratheodory Φ) :
    SvMeasurable (fun t ↦ svGraph (fun x ↦ ({Φ t x} : Set G))) := by
  rcases isEmpty_or_nonempty E with hE | hE
  · intro O _
    have : svPreimage (fun t ↦ svGraph (fun x ↦ ({Φ t x} : Set G))) O = ∅ := by
      ext t
      simp only [mem_svPreimage, mem_empty_iff_false, iff_false]
      rintro ⟨p, -⟩
      exact hE.elim p.1
    rw [this]
    exact MeasurableSet.empty
  set d := denseSeq E
  have hd : DenseRange d := denseRange_denseSeq E
  set z : ℕ → T → E × G := fun q t ↦ (d q, Φ t (d q))
  have hz : IsCastaingRepresentation (fun t ↦ svGraph (fun x ↦ ({Φ t x} : Set G))) z := by
    refine ⟨fun q ↦ measurable_const.prodMk (hΦ.1 (d q)), fun t _ ↦ ?_⟩
    show svGraph (fun x ↦ ({Φ t x} : Set G)) = closure (range fun n ↦ z n t)
    have hgraph : svGraph (fun x ↦ ({Φ t x} : Set G)) = range fun x ↦ (x, Φ t x) := by
      ext ⟨x, u⟩
      simp only [mem_svGraph, mem_singleton_iff, mem_range, Prod.mk.injEq]
      constructor
      · rintro rfl
        exact ⟨x, rfl, rfl⟩
      · rintro ⟨y, rfl, rfl⟩
        rfl
    have hcont : Continuous fun x ↦ (x, Φ t x) := continuous_id.prodMk (hΦ.2 t)
    have hclosed : IsClosed (svGraph (fun x ↦ ({Φ t x} : Set G))) := by
      have : svGraph (fun x ↦ ({Φ t x} : Set G)) = {p : E × G | p.2 = Φ t p.1} := by
        ext p
        simp
      rw [this]
      exact isClosed_eq continuous_snd ((hΦ.2 t).comp continuous_fst)
    apply Subset.antisymm
    · rw [hgraph]
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ closure (range d) := by rw [hd.closure_range]; trivial
      have := image_closure_subset_closure_image hcont ⟨x, hx, rfl⟩
      rwa [← range_comp] at this
    · refine closure_minimal ?_ hclosed
      rintro _ ⟨q, rfl⟩
      simp [z]
  refine hz.svMeasurable ?_
  have : svDom (fun t ↦ svGraph (fun x ↦ ({Φ t x} : Set G))) = univ := by
    ext t
    simp only [mem_svDom, mem_univ, iff_true]
    obtain ⟨x⟩ := hE
    exact ⟨(x, Φ t x), rfl⟩
  rw [this]
  exact MeasurableSet.univ

/-- **Example 14.15(a)**: `t ↦ Φ(t, S(t))` is measurable for closed-valued measurable `S`. -/
theorem IsCaratheodory.svMeasurable_image {Φ : T → E → G} (hΦ : IsCaratheodory Φ)
    {S : T → Set E} (hS : SvMeasurable S) (hSc : ∀ t, IsClosed (S t)) :
    SvMeasurable (fun t ↦ Φ t '' S t) := by
  have h := hS.svImage_of_svGraph hSc (M := fun t x ↦ ({Φ t x} : Set G))
    (fun t ↦ isClosed_svGraph_iff_svOsc.1 (by
      have : svGraph (fun x ↦ ({Φ t x} : Set G)) = {p : E × G | p.2 = Φ t p.1} := by
        ext p
        simp
      rw [this]
      exact isClosed_eq continuous_snd ((hΦ.2 t).comp continuous_fst)))
    hΦ.svMeasurable_graph
  have heq : (fun t ↦ svImage (fun x ↦ ({Φ t x} : Set G)) (S t)) = fun t ↦ Φ t '' S t := by
    funext t
    ext u
    simp only [mem_svImage, mem_singleton_iff, mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rwa [heq] at h

/-- **Example 14.15(b)**: `t ↦ {x | Φ(t, x) ∈ S(t)}` is closed-valued and measurable for
closed-valued measurable `S`. -/
theorem IsCaratheodory.svMeasurable_preimage {Φ : T → E → G} (hΦ : IsCaratheodory Φ)
    {S : T → Set G} (hS : SvMeasurable S) (hSc : ∀ t, IsClosed (S t)) :
    (∀ t, IsClosed {x | Φ t x ∈ S t}) ∧ SvMeasurable (fun t ↦ {x | Φ t x ∈ S t}) := by
  refine ⟨fun t ↦ (hSc t).preimage (hΦ.2 t), ?_⟩
  set M : T → G → Set E := fun t u ↦ {x | Φ t x = u}
  have hgraph : ∀ t, svGraph (M t) = Prod.swap '' svGraph (fun x ↦ ({Φ t x} : Set G)) := by
    intro t
    ext ⟨u, x⟩
    simp only [M, mem_svGraph, mem_setOf_eq, mem_image, Prod.exists, mem_singleton_iff,
      Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro rfl
      exact ⟨x, Φ t x, rfl, rfl, rfl⟩
    · rintro ⟨a, b, rfl, rfl, rfl⟩
      rfl
  have hMosc : ∀ t, SvOsc (M t) := fun t ↦ isClosed_svGraph_iff_svOsc.1 (by
    have : svGraph (M t) = {p : G × E | Φ t p.2 = p.1} := rfl
    rw [this]
    exact isClosed_eq ((hΦ.2 t).comp continuous_snd) continuous_fst)
  have hM : SvMeasurable (fun t ↦ svGraph (M t)) := by
    have heq : (fun t ↦ svGraph (M t)) =
        fun t ↦ Prod.swap '' svGraph (fun x ↦ ({Φ t x} : Set G)) := funext hgraph
    rw [heq]
    exact hΦ.svMeasurable_graph.image continuous_swap
  have h := hS.svImage_of_svGraph hSc hMosc hM
  have heq : (fun t ↦ svImage (M t) (S t)) = fun t ↦ {x | Φ t x ∈ S t} := by
    funext t
    ext x
    simp only [M, mem_svImage, mem_setOf_eq, exists_eq_right']
  rwa [heq] at h

/-- **Example 14.15 (images under Carathéodory mappings)**, both parts. -/
theorem images_under_caratheodory_mappings {Φ : T → E → G} (hΦ : IsCaratheodory Φ) :
    (∀ {S : T → Set E}, SvMeasurable S → (∀ t, IsClosed (S t)) →
        SvMeasurable (fun t ↦ Φ t '' S t)) ∧
      (∀ {S : T → Set G}, SvMeasurable S → (∀ t, IsClosed (S t)) →
        SvMeasurable (fun t ↦ {x | Φ t x ∈ S t})) :=
  ⟨fun hS hSc ↦ hΦ.svMeasurable_image hS hSc, fun hS hSc ↦ (hΦ.svMeasurable_preimage hS hSc).2⟩

/-- **Theorem 14.16 (implicit measurable functions)**: for a Carathéodory mapping `Φ` and
closed-valued measurable `X`, `D`, the set `E = {t | ∃ x ∈ X(t), Φ(t, x) ∈ D(t)}` is measurable
and there is a measurable `x` with `x(t) ∈ X(t)` and `Φ(t, x(t)) ∈ D(t)` for all `t ∈ E`. -/
theorem implicit_measurable_functions [Nonempty E] {Φ : T → E → G} (hΦ : IsCaratheodory Φ)
    {X : T → Set E} {D : T → Set G} (hX : SvMeasurable X) (hXc : ∀ t, IsClosed (X t))
    (hD : SvMeasurable D) (hDc : ∀ t, IsClosed (D t)) :
    MeasurableSet {t | ∃ x ∈ X t, Φ t x ∈ D t} ∧
      ∃ x : T → E, Measurable x ∧ ∀ t ∈ {t | ∃ x ∈ X t, Φ t x ∈ D t},
        x t ∈ X t ∧ Φ t (x t) ∈ D t := by
  obtain ⟨hRc, hR⟩ := hΦ.svMeasurable_preimage hD hDc
  have hS : SvMeasurable (fun t ↦ X t ∩ {x | Φ t x ∈ D t}) := hX.inter hR hXc hRc
  have hSc : ∀ t, IsClosed (X t ∩ {x | Φ t x ∈ D t}) := fun t ↦ (hXc t).inter (hRc t)
  have hdom : {t | ∃ x ∈ X t, Φ t x ∈ D t} = svDom (fun t ↦ X t ∩ {x | Φ t x ∈ D t}) := by
    ext t
    simp only [mem_setOf_eq, mem_svDom]
    exact ⟨fun ⟨x, hx, hxD⟩ ↦ ⟨x, hx, hxD⟩, fun ⟨x, hx, hxD⟩ ↦ ⟨x, hx, hxD⟩⟩
  refine ⟨hdom ▸ hS.measurableSet_svDom, ?_⟩
  obtain ⟨x, hxm, hxS⟩ := hS.exists_measurable_selection hSc
  refine ⟨x, hxm, fun t ht ↦ ?_⟩
  rw [hdom] at ht
  exact hxS t ht

end Example1415


section Exercise1417

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The guide of Exercise 14.17: `gph P_C` consists of the pairs `(x, y) ∈ E × C` with
`|x − y| − d(x, C) ≤ 0`. -/
theorem svGraph_projMapping_eq (C : Set E) :
    svGraph (projMapping C) = (univ ×ˢ C) ∩ {p : E × E | ‖p.2 - p.1‖ - infDist p.1 C ≤ 0} := by
  ext ⟨x, w⟩
  simp only [mem_svGraph, mem_projMapping, mem_inter_iff, mem_prod, mem_univ, true_and,
    mem_setOf_eq, sub_nonpos]
  constructor
  · rintro ⟨hw, hmin⟩
    refine ⟨hw, (le_infDist ⟨w, hw⟩).2 fun y hy ↦ ?_⟩
    rw [dist_eq_norm, norm_sub_rev x y]
    exact hmin y hy
  · rintro ⟨hw, hle⟩
    refine ⟨hw, fun y hy ↦ ?_⟩
    have := (le_infDist ⟨w, hw⟩).1 hle hy
    rwa [dist_eq_norm, norm_sub_rev x y] at this

/-- **Exercise 14.17 (projection mappings)**: for closed-valued measurable `S`,
(a) `t ↦ gph P_{S(t)}` is closed-valued and measurable; (b) `t ↦ P_{S(t)}(X(t))` is
measurable for every closed-valued measurable `X` (for instance `X(t) = {x(t)}`). -/
theorem projection_mappings_measurable {S : T → Set E} (hS : SvMeasurable S)
    (hSc : ∀ t, IsClosed (S t)) :
    ((∀ t, IsClosed (svGraph (projMapping (S t)))) ∧
        SvMeasurable (fun t ↦ svGraph (projMapping (S t)))) ∧
      ∀ {X : T → Set E}, SvMeasurable X → (∀ t, IsClosed (X t)) →
        SvMeasurable (fun t ↦ svImage (projMapping (S t)) (X t)) := by
  set φ : T → E × E → ℝ := fun t p ↦ ‖p.2 - p.1‖ - infDist p.1 (S t)
  have hφ : IsCaratheodory φ := by
    refine ⟨fun p ↦ ?_, fun t ↦ ?_⟩
    · exact measurable_const.sub (hS.measurable_infEDist p.1).ennreal_toReal
    · exact (continuous_norm.comp (continuous_snd.sub continuous_fst)).sub
        ((continuous_infDist_pt _).comp continuous_fst)
  obtain ⟨hLc, hL⟩ := hφ.svMeasurable_preimage (S := fun _ ↦ Iic (0 : ℝ))
    (svMeasurable_const _) (fun _ ↦ isClosed_Iic)
  have hgraph : ∀ t, svGraph (projMapping (S t)) =
      (univ ×ˢ S t) ∩ {p : E × E | φ t p ∈ Iic 0} := fun t ↦ svGraph_projMapping_eq (S t)
  have hclosed : ∀ t, IsClosed (svGraph (projMapping (S t))) := fun t ↦ by
    rw [hgraph t]
    exact (isClosed_univ.prod (hSc t)).inter (hLc t)
  have hmeas : SvMeasurable (fun t ↦ svGraph (projMapping (S t))) := by
    have heq : (fun t ↦ svGraph (projMapping (S t))) =
        fun t ↦ (univ ×ˢ S t) ∩ {p : E × E | φ t p ∈ Iic 0} := funext hgraph
    rw [heq]
    exact ((svMeasurable_const univ).prod hS).inter hL (fun t ↦ isClosed_univ.prod (hSc t)) hLc
  refine ⟨⟨hclosed, hmeas⟩, fun hX hXc ↦ ?_⟩
  exact hX.svImage_of_svGraph hXc (fun t ↦ isClosed_svGraph_iff_svOsc.1 (hclosed t)) hmeas

end Exercise1417

section Exercise1418

variable {T D E G : Type*} [MeasurableSpace T]
  [MetricSpace D] [ProperSpace D] [MeasurableSpace D] [BorelSpace D]
  [MetricSpace E] [ProperSpace E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace G] [ProperSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **Exercise 14.18 (mixed operations)**: for closed-valued measurable
`S : T ⇉ ℝᵈ × ℝⁿ × ℝᵐ` and measurable `u : T → ℝᵐ`, the mapping
`t ↦ {x | ∃ w, (w, x, u(t)) ∈ S(t)}` is measurable. -/
theorem mixed_operations {S : T → Set (D × E × G)} (hS : SvMeasurable S)
    (hSc : ∀ t, IsClosed (S t)) {u : T → G} (hu : Measurable u) :
    SvMeasurable (fun t ↦ {x : E | ∃ w : D, (w, x, u t) ∈ S t}) := by
  set Φ : T → D × E → D × E × G := fun t p ↦ (p.1, p.2, u t)
  have hΦ : IsCaratheodory Φ := by
    refine ⟨fun p ↦ ?_, fun t ↦ ?_⟩
    · exact measurable_const.prodMk (measurable_const.prodMk hu)
    · exact continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  have hR := (hΦ.svMeasurable_preimage hS hSc).2
  have heq : (fun t ↦ {x : E | ∃ w : D, (w, x, u t) ∈ S t}) =
      fun t ↦ Prod.snd '' {p : D × E | Φ t p ∈ S t} := by
    funext t
    ext x
    simp only [mem_setOf_eq, mem_image, Prod.exists, exists_eq_right, Φ]
  rw [heq]
  exact hR.image continuous_snd

end Exercise1418

section Example1419

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem finsetSum_smul_eq_image {J : Type*} [Fintype J] (c : J → ℝ) (A : J → Set E) :
    ∑ j, c j • A j = (fun x : J → E ↦ ∑ j, c j • x j) '' Set.pi univ A := by
  ext x
  rw [Set.mem_finset_sum]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : ∀ j, ∃ y ∈ A j, c j • y = g j := fun j ↦
      Set.mem_smul_set.1 (hg (Finset.mem_univ j))
    choose y hy hyg using hg'
    exact ⟨y, fun j _ ↦ hy j, by simp only [hyg]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun j ↦ c j • y j, fun {j} _ ↦ Set.smul_mem_smul_set (hy j (mem_univ j)), rfl⟩

/-- **Example 14.19 (variable scalar multiplication)**: for closed-valued measurable mappings
`Sⱼ : T ⇉ ℝⁿ` (the book's `Sj : IRⁿ ⇉ IRᵐ` is a misprint for `T ⇉ IRⁿ`), `j = 1, …, r`, and
measurable scalars `λⱼ(t)`, the mapping `t ↦ ∑ⱼ λⱼ(t) Sⱼ(t)` is measurable. -/
theorem variable_scalar_multiplication {J : Type*} [Fintype J] {S : J → T → Set E}
    (hS : ∀ j, SvMeasurable (S j)) (hSc : ∀ j t, IsClosed (S j t)) {lam : J → T → ℝ}
    (hlam : ∀ j, Measurable (lam j)) :
    SvMeasurable (fun t ↦ ∑ j, lam j t • S j t) := by
  set Φ : T → (J → E) → E := fun t x ↦ ∑ j, lam j t • x j
  have hΦ : IsCaratheodory Φ := by
    refine ⟨fun x ↦ ?_, fun t ↦ ?_⟩
    · exact Finset.measurable_sum _ fun j _ ↦ (hlam j).smul_const (x j)
    · exact continuous_finset_sum _ fun j _ ↦ (continuous_apply j).const_smul (lam j t)
  have hR : SvMeasurable (fun t ↦ Set.pi univ fun j ↦ S j t) := SvMeasurable.pi hS
  have hRc : ∀ t, IsClosed (Set.pi univ fun j ↦ S j t) := fun t ↦
    isClosed_set_pi fun j _ ↦ hSc j t
  have heq : (fun t ↦ ∑ j, lam j t • S j t) = fun t ↦ Φ t '' Set.pi univ fun j ↦ S j t :=
    funext fun t ↦ finsetSum_smul_eq_image (fun j ↦ lam j t) (fun j ↦ S j t)
  rw [heq]
  exact hΦ.svMeasurable_image hR hRc

end Example1419

end RW
