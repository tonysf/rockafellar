/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1B-C: Epigraphs, Semicontinuity, and Attainment

This file formalizes:
- Theorem 1.6: Characterization of lower semicontinuity via epigraphs and
  level sets (restating Mathlib results in our notation)
- Theorem 1.9: Attainment of a minimum
- Corollary 1.10: Lower bounds on bounded sets
- Proposition 1.26: Semicontinuity under pointwise operations
-/

import RockafellarWets.Chapter1.Defs
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic

open Set Filter Topology EReal Classical

noncomputable section

namespace RW

variable {E : Type*} [TopologicalSpace E]

/-! ## Theorem 1.6: Characterization of lower semicontinuity

Mathlib already has the key equivalences. We restate them here connecting
to the R&W presentation.

Theorem 1.6 equivalences:
  (a) f is lsc ⟺ (b) epi f is closed ⟺ (c) all sublevel sets are closed
-/

/-- **Theorem 1.6 (a) ↔ (b)**: `f` is lsc iff its epigraph is closed. -/
theorem lsc_iff_epigraph_closed (f : E → ℝ) :
    LowerSemicontinuous f ↔ IsClosed {p : E × ℝ | f p.1 ≤ p.2} :=
  lowerSemicontinuous_iff_isClosed_epigraph

/-- For `EReal`-valued functions, lower semicontinuity implies closedness of
the real epigraph used in this project. -/
theorem isClosed_epigraph_of_lsc_ereal (f : E → EReal)
    (hf : LowerSemicontinuous f) :
    IsClosed (epigraph f) := by
  let φ : E × ℝ → E × EReal := fun p => (p.1, (p.2 : EReal))
  have hφ : Continuous φ := continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  simpa [epigraph, φ, ge_iff_le] using
    (LowerSemicontinuous.isClosed_epigraph (f := f) hf).preimage hφ

/-- Closedness of the real epigraph implies lower semicontinuity for
`EReal`-valued functions. -/
theorem lowerSemicontinuous_of_isClosed_epigraph_ereal (f : E → EReal)
    (hf : IsClosed (epigraph f)) :
    LowerSemicontinuous f := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  rcases eq_top_or_lt_top y with rfl | hy
  · simp
  · refine isOpen_iff_mem_nhds.2 ?_
    intro x hx
    obtain ⟨a, hya, hax⟩ := EReal.exists_between_coe_real hx
    have hxa : (x, a) ∈ (epigraph f)ᶜ := by
      simpa [mem_epigraph_iff, not_le_of_gt hax]
    rcases mem_nhds_prod_iff.mp (hf.isOpen_compl.mem_nhds hxa) with ⟨U, hU, V, hV, hUV⟩
    have haV : a ∈ V := mem_of_mem_nhds hV
    refine mem_of_superset hU ?_
    intro x' hx'
    have hnot : ¬ f x' ≤ (a : EReal) := by
      have hcomp : (x', a) ∈ (epigraph f)ᶜ :=
        hUV (show (x', a) ∈ U ×ˢ V from ⟨hx', haV⟩)
      simpa [mem_epigraph_iff] using hcomp
    simpa using hya.trans (lt_of_not_ge hnot)

/-- **Theorem 1.6 (a) ↔ (b)** for `EReal`-valued functions, expressed through
the project's real-valued epigraph convention. -/
theorem lsc_iff_epigraph_closed_ereal (f : E → EReal) :
    LowerSemicontinuous f ↔ IsClosed (epigraph f) := by
  constructor
  · exact isClosed_epigraph_of_lsc_ereal f
  · exact lowerSemicontinuous_of_isClosed_epigraph_ereal f

/-- **Theorem 1.6 (a) ↔ (c)**: `f` is lsc iff all sublevel sets are closed. -/
theorem lsc_iff_sublevelSets_closed (f : E → ℝ) :
    LowerSemicontinuous f ↔ ∀ α : ℝ, IsClosed {x | f x ≤ α} := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  rfl

/-- The epigraph of the variational-analysis indicator of a set is the vertical
half-cylinder over the set. -/
theorem epigraph_indicatorVA (C : Set E) :
    epigraph (indicatorVA C) = C ×ˢ Set.Ici (0 : ℝ) := by
  ext p
  rcases p with ⟨x, a⟩
  by_cases hx : x ∈ C <;> simp [epigraph, indicatorVA, hx, ge_iff_le]

/-- The variational-analysis indicator of a closed set is lower
semicontinuous. -/
theorem lowerSemicontinuous_indicatorVA {C : Set E} (hC : IsClosed C) :
    LowerSemicontinuous (indicatorVA C) := by
  apply (lsc_iff_epigraph_closed_ereal _).2
  simpa [epigraph_indicatorVA] using hC.prod isClosed_Ici

/-! ## Theorem 1.9: Attainment of a minimum

If `f` is lsc, level-bounded, and proper, then `inf f` is finite and
`argmin f` is nonempty and compact.
-/

/-- **Theorem 1.9** (on compact sublevel sets):
An lsc function on a closed set with compact sublevel sets attains its
infimum. -/
theorem exists_isMinOn_of_lsc_compact_sublevel [MetricSpace E]
    {f : E → ℝ} {s : Set E}
    (_hs_closed : IsClosed s) (hs_ne : s.Nonempty)
    (hf_lsc : LowerSemicontinuousOn f s)
    (hf_compact : ∀ α : ℝ, IsCompact {x ∈ s | f x ≤ α}) :
    ∃ x ∈ s, IsMinOn f s x := by
  obtain ⟨x₀, hx₀⟩ := hs_ne
  have hK := hf_compact (f x₀)
  have hK_ne : {x ∈ s | f x ≤ f x₀}.Nonempty := ⟨x₀, hx₀, le_refl _⟩
  have hf_lsc' : LowerSemicontinuousOn f {x ∈ s | f x ≤ f x₀} :=
    hf_lsc.mono (fun x hx => hx.1)
  obtain ⟨x_min, hx_min_mem, hx_min⟩ :=
    hf_lsc'.exists_isMinOn hK_ne hK
  refine ⟨x_min, hx_min_mem.1, fun y hy => ?_⟩
  by_cases h : f y ≤ f x₀
  · exact hx_min ⟨hy, h⟩
  · push_neg at h
    exact le_trans hx_min_mem.2 (le_of_lt h)

/-- **Corollary 1.10**: An lsc function is bounded below on any compact set
and attains its minimum there. -/
theorem bddBelow_image_of_lsc_compact
    {f : E → ℝ} {K : Set E}
    (hf : LowerSemicontinuousOn f K) (hK : IsCompact K) (hK_ne : K.Nonempty) :
    BddBelow (f '' K) := by
  obtain ⟨x, hx, hmin⟩ := hf.exists_isMinOn hK_ne hK
  exact ⟨f x, fun _ ⟨y, hy, hfy⟩ => hfy ▸ hmin hy⟩

/-- An lsc function attains its minimum on a compact nonempty set. -/
theorem exists_min_of_lsc_compact
    {f : E → ℝ} {K : Set E}
    (hf : LowerSemicontinuousOn f K) (hK : IsCompact K) (hK_ne : K.Nonempty) :
    ∃ x ∈ K, IsMinOn f K x :=
  hf.exists_isMinOn hK_ne hK

/-! ## Proposition 1.26: Semicontinuity under pointwise operations -/

/-- **Proposition 1.26(a)**: The pointwise supremum of a family of lsc
functions is lsc (assuming the sup is bounded above pointwise). -/
theorem lsc_of_iSup {ι : Type*} {f : ι → E → ℝ}
    (hf : ∀ i, LowerSemicontinuous (f i))
    (hbdd : ∀ x, BddAbove (range (fun i => f i x))) :
    LowerSemicontinuous (fun x => ⨆ i, f i x) :=
  lowerSemicontinuous_ciSup hbdd (fun i => hf i)

/-- **Proposition 1.26(b)**: The pointwise minimum of finitely many lsc
functions is lsc. -/
theorem lsc_of_finite_iInf {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → ℝ}
    (hf : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (fun x => ⨅ i, f i x) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro α
  -- {x | ⨅ i, f i x ≤ α} = ⋃ i, {x | f i x ≤ α}
  -- because for finite families, inf ≤ α iff some element ≤ α
  have key : (fun x => ⨅ i, f i x) ⁻¹' Iic α = ⋃ i, (f i) ⁻¹' Iic α := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_iUnion]
    have hbdd : BddBelow (range (fun i => f i x)) :=
      (Set.finite_range _).bddBelow
    constructor
    · intro h
      -- The infimum over a finite nonempty type is attained
      obtain ⟨i, hi⟩ := Finite.exists_min (fun i => f i x)
      exact ⟨i, le_trans (le_trans (le_ciInf hi) h) le_rfl⟩
    · rintro ⟨i, hi⟩
      exact le_trans (ciInf_le hbdd i) hi
  rw [key]
  exact isClosed_iUnion_of_finite fun i =>
    (lsc_iff_sublevelSets_closed _).mp (hf i) α

end RW
