/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: The Aubin property and its graphical modulus
-/

import RockafellarWets.Chapter5.Semicontinuity
import RockafellarWets.Chapter6.NormalCones

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- Formula 9(17), expressed by the point in the comparison fiber that realizes the
geometric inclusion. Both input points vary in the same relative neighborhood. -/
def AubinEstimate (S : E → Set F) (X : Set E) (x : E) (u : F) (k : ℝ≥0) : Prop :=
  ∃ V ∈ 𝓝 x, ∃ W ∈ 𝓝 u, ∀ x' ∈ X ∩ V, ∀ y ∈ X ∩ V, ∀ v ∈ S x' ∩ W,
    ∃ z ∈ S y, dist v z ≤ k * dist x' y

/-- **Definition 9.36.** The relative Aubin property at a point of the graph. -/
def HasAubinPropertyWithinAt (S : E → Set F) (X : Set E) (x : E) (u : F) : Prop :=
  x ∈ X ∧ u ∈ S x ∧ IsLocallyClosedAt (svGraph S) (x,u) ∧ ∃ k, AubinEstimate S X x u k

abbrev HasAubinPropertyAt (S : E → Set F) (x : E) (u : F) : Prop := HasAubinPropertyWithinAt S univ x u

/-- The infimum of the admissible constants can be infinite. -/
noncomputable def graphicalLipschitzModulusWithin (S : E → Set F) (X : Set E) (x : E) (u : F) : ℝ≥0∞ :=
  ⨅ k : {k : ℝ≥0 // AubinEstimate S X x u k}, ((k : ℝ≥0) : ℝ≥0∞)

noncomputable abbrev graphicalLipschitzModulus (S : E → Set F) (x : E) (u : F) : ℝ≥0∞ :=
  graphicalLipschitzModulusWithin S univ x u

variable {S : E → Set F} {X : Set E} {x : E} {u : F} {k l : ℝ≥0}

theorem AubinEstimate.mono (h : AubinEstimate S X x u k) (hkl : k ≤ l) : AubinEstimate S X x u l := by
  obtain ⟨V,hV,W,hW,h⟩ := h
  refine ⟨V,hV,W,hW,fun a ha b hb v hv ↦ ?_⟩
  obtain ⟨z,hz,hd⟩ := h a ha b hb v hv
  exact ⟨z,hz,hd.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 hkl) dist_nonneg)⟩

theorem AubinEstimate.modulus_le (h : AubinEstimate S X x u k) :
    graphicalLipschitzModulusWithin S X x u ≤ (k : ℝ≥0∞) :=
  iInf_le (fun a : {a : ℝ≥0 // AubinEstimate S X x u a} ↦ ((a : ℝ≥0) : ℝ≥0∞)) ⟨k,h⟩

theorem aubinEstimate_of_modulus_lt (h : graphicalLipschitzModulusWithin S X x u < (k : ℝ≥0∞)) :
    AubinEstimate S X x u k := by
  obtain ⟨l,hl⟩ := iInf_lt_iff.1 h
  exact l.2.mono (ENNReal.coe_le_coe.1 hl.le)

theorem hasAubinPropertyWithinAt_iff_modulus_lt_top :
    HasAubinPropertyWithinAt S X x u ↔ x ∈ X ∧ u ∈ S x ∧ IsLocallyClosedAt (svGraph S) (x,u) ∧
      graphicalLipschitzModulusWithin S X x u < ⊤ := by
  simp only [HasAubinPropertyWithinAt,graphicalLipschitzModulusWithin,ENNReal.iInf_coe_lt_top,nonempty_subtype]

/-- A witnessed graphical estimate continues to hold at nearby graph points.
The same neighborhoods in its definition work at each of their interior points. -/
theorem AubinEstimate.eventually (h : AubinEstimate S X x u k) :
    ∀ᶠ p : E × F in 𝓝 (x,u), AubinEstimate S X p.1 p.2 k := by
  obtain ⟨V,hV,W,hW,h⟩ := h
  filter_upwards [prod_mem_nhds (IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.2 hV))
    (IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.2 hW))] with p hp
  exact ⟨V,mem_interior_iff_mem_nhds.1 hp.1,W,mem_interior_iff_mem_nhds.1 hp.2,h⟩

/-- The graphical modulus is upper semicontinuous, also when its value is infinite. -/
theorem upperSemicontinuous_graphicalLipschitzModulusWithin (S : E → Set F) (X : Set E) :
    UpperSemicontinuous (fun p : E × F ↦ graphicalLipschitzModulusWithin S X p.1 p.2) := by
  intro p a ha
  obtain ⟨k,hk⟩ := iInf_lt_iff.1 ha
  exact k.2.eventually.mono fun q hq ↦ hq.modulus_le.trans_lt hk

/-- As remarked following Definition 9.36, the relative Aubin property persists
at nearby graph points whose inputs belong to `X`. -/
theorem HasAubinPropertyWithinAt.eventually (h : HasAubinPropertyWithinAt S X x u) :
    ∀ᶠ p : E × F in 𝓝 (x,u), p.1 ∈ X → p.2 ∈ S p.1 → HasAubinPropertyWithinAt S X p.1 p.2 := by
  obtain ⟨_,_,⟨U,hU,hUc,hCU⟩,k,hk⟩ := h
  filter_upwards [hk.eventually,isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hU)] with p hEst hp
  exact fun hx hu ↦ ⟨hx,hu,⟨U,mem_interior_iff_mem_nhds.1 hp,hUc,hCU⟩,k,hEst⟩

end RW
