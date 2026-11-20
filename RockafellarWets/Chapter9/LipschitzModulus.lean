/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Lipschitz moduli and strict continuity
-/

import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- **Definition 9.1.** The exact local Lipschitz modulus, relative to the
set on which the points vary. The infimum of an empty family is infinity. -/
noncomputable def lipschitzModulusWithin (f : E → F) (X : Set E) (x : E) : ℝ≥0∞ :=
  ⨅ k : {k : ℝ≥0 // ∃ U ∈ 𝓝[X] x, LipschitzOnWith k f U}, ((k : ℝ≥0) : ℝ≥0∞)

noncomputable abbrev lipschitzModulus (f : E → F) (x : E) : ℝ≥0∞ := lipschitzModulusWithin f univ x

def StrictlyContinuousWithinAt (f : E → F) (X : Set E) (x : E) : Prop :=
  x ∈ X ∧ lipschitzModulusWithin f X x < ⊤

def StrictlyContinuousAt (f : E → F) (x : E) : Prop := lipschitzModulus f x < ⊤

theorem lipschitzModulusWithin_le {f : E → F} {X U : Set E} {x : E} {k : ℝ≥0}
    (hU : U ∈ 𝓝[X] x) (hf : LipschitzOnWith k f U) : lipschitzModulusWithin f X x ≤ (k : ℝ≥0∞) :=
  iInf_le (fun k : {k : ℝ≥0 // ∃ U ∈ 𝓝[X] x, LipschitzOnWith k f U} ↦ ((k : ℝ≥0) : ℝ≥0∞)) ⟨k, U, hU, hf⟩

theorem lipschitzModulus_le {f : E → F} {U : Set E} {x : E} {k : ℝ≥0}
    (hU : U ∈ 𝓝 x) (hf : LipschitzOnWith k f U) : lipschitzModulus f x ≤ (k : ℝ≥0∞) :=
  lipschitzModulusWithin_le (nhdsWithin_univ x ▸ hU) hf

theorem exists_lipschitzOnWith_of_modulusWithin_lt {f : E → F} {X : Set E} {x : E} {k : ℝ≥0}
    (hk : lipschitzModulusWithin f X x < (k : ℝ≥0∞)) :
    ∃ U ∈ 𝓝[X] x, LipschitzOnWith k f U := by
  obtain ⟨a, ha⟩ := iInf_lt_iff.mp hk
  obtain ⟨U, hU, h⟩ := a.property
  exact ⟨U, hU, fun _ hy _ hz ↦ (h hy hz).trans (mul_le_mul_left ha.le _)⟩

theorem exists_lipschitzOnWith_of_modulus_lt {f : E → F} {x : E} {k : ℝ≥0}
    (hk : lipschitzModulus f x < (k : ℝ≥0∞)) : ∃ U ∈ 𝓝 x, LipschitzOnWith k f U := by
  simpa only [nhdsWithin_univ] using exists_lipschitzOnWith_of_modulusWithin_lt hk

theorem strictlyContinuousWithinAt_iff {f : E → F} {X : Set E} {x : E} :
    StrictlyContinuousWithinAt f X x ↔ x ∈ X ∧ ∃ k : ℝ≥0, ∃ U ∈ 𝓝[X] x, LipschitzOnWith k f U := by
  unfold StrictlyContinuousWithinAt lipschitzModulusWithin
  rw [ENNReal.iInf_coe_lt_top, nonempty_subtype]

theorem strictlyContinuousAt_iff {f : E → F} {x : E} :
    StrictlyContinuousAt f x ↔ ∃ k : ℝ≥0, ∃ U ∈ 𝓝 x, LipschitzOnWith k f U := by
  simpa [StrictlyContinuousAt, StrictlyContinuousWithinAt] using
    (strictlyContinuousWithinAt_iff (f := f) (X := univ) (x := x))

theorem strictlyContinuousWithinAt_iff_locallyLipschitzOn {f : E → F} {X : Set E} :
    (∀ x ∈ X, StrictlyContinuousWithinAt f X x) ↔ LocallyLipschitzOn X f :=
  ⟨fun h x hx ↦ (strictlyContinuousWithinAt_iff.mp (h x hx)).2,
    fun h _ hx ↦ strictlyContinuousWithinAt_iff.mpr ⟨hx, h hx⟩⟩

theorem StrictlyContinuousAt.continuousAt {f : E → F} {x : E} (h : StrictlyContinuousAt f x) :
    ContinuousAt f x := by
  obtain ⟨k, U, hU, hf⟩ := strictlyContinuousAt_iff.mp h
  exact hf.continuousOn.continuousAt hU

theorem lipschitzModulusWithin_mono {f : E → F} {X Y : Set E} (hXY : X ⊆ Y) (x : E) :
    lipschitzModulusWithin f X x ≤ lipschitzModulusWithin f Y x := by
  refine le_iInf fun k ↦ ?_
  obtain ⟨U, hU, h⟩ := k.property
  exact lipschitzModulusWithin_le (nhdsWithin_mono x hXY hU) h

/-- The two-point limsup formula printed in Definition 9.1. Distinct points
are enforced on the product filter. At isolated points this gives zero. -/
theorem lipschitzModulusWithin_eq_limsup (f : E → F) (X : Set E) (x : E) :
    lipschitzModulusWithin f X x =
      limsup (fun p : E × E ↦ edist (f p.1) (f p.2) / edist p.1 p.2)
        ((𝓝[X] x ×ˢ 𝓝[X] x) ⊓ 𝓟 {p : E × E | p.1 ≠ p.2}) := by
  let L := (𝓝[X] x ×ˢ 𝓝[X] x) ⊓ 𝓟 {p : E × E | p.1 ≠ p.2}
  let q := fun p : E × E ↦ edist (f p.1) (f p.2) / edist p.1 p.2
  apply le_antisymm
  · by_contra! h
    obtain ⟨k, hk, hk'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    have hb : ∀ᶠ p in L, q p < (k : ℝ≥0∞) := eventually_lt_of_limsup_lt hk
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.mp (eventually_inf_principal.mp hb)
    apply hk'.not_ge (lipschitzModulusWithin_le (inter_mem hU hV) ?_)
    intro y hy z hz
    rcases eq_or_ne y z with rfl | hyz
    · simp
    · exact (ENNReal.div_le_iff (edist_eq_zero.not.mpr hyz) (edist_ne_top y z)).mp
        ((hUV (a := (y,z)) ⟨hy.1,hz.2⟩ hyz).le)
  · refine le_iInf fun k ↦ ?_
    obtain ⟨U, hU, h⟩ := k.property
    apply limsup_le_of_le (by isBoundedDefault)
    apply eventually_inf_principal.mpr
    filter_upwards [tendsto_fst.eventually hU, tendsto_snd.eventually hU] with p h1 h2 _
    exact ENNReal.div_le_of_le_mul (h h1 h2)

/-- The modulus is the infimum of the constants on positive-radius closed balls. -/
theorem lipschitzModulusWithin_eq_iInf_closedBall (f : E → F) (X : Set E) (x : E) :
    lipschitzModulusWithin f X x =
      ⨅ k : {k : ℝ≥0 // ∃ r > 0, LipschitzOnWith k f (closedBall x r ∩ X)}, ((k : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · refine le_iInf fun k ↦ ?_
    obtain ⟨r, hr, h⟩ := k.property
    exact lipschitzModulusWithin_le (inter_mem (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds _ hr)) self_mem_nhdsWithin) h
  · refine le_iInf fun k ↦ ?_
    obtain ⟨U, hU, h⟩ := k.property
    obtain ⟨r, hr, hsub⟩ := (nhdsWithin_hasBasis Metric.nhds_basis_closedBall X).mem_iff.mp hU
    exact iInf_le (fun a : {k : ℝ≥0 // ∃ r > 0, LipschitzOnWith k f (closedBall x r ∩ X)} ↦ ((a : ℝ≥0) : ℝ≥0∞)) ⟨k, r, hr, h.mono hsub⟩

/-- **Theorem 9.2**, local part. The modulus is upper semicontinuous.
This holds throughout a metric space and for a fixed relative set as well. -/
theorem upperSemicontinuous_lipschitzModulusWithin (f : E → F) (X : Set E) :
    UpperSemicontinuous (lipschitzModulusWithin f X) := by
  intro x a ha
  obtain ⟨k, hk⟩ := iInf_lt_iff.mp ha
  obtain ⟨U, hU, h⟩ := k.property
  obtain ⟨V, hV, hVX⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hU
  filter_upwards [eventually_mem_nhds_iff.mpr hV] with y hy
  exact (lipschitzModulusWithin_le (inter_mem (mem_nhdsWithin_of_mem_nhds hy) self_mem_nhdsWithin)
    (h.mono hVX)).trans_lt hk

theorem isOpen_setOf_strictlyContinuousAt (f : E → F) : IsOpen {x | StrictlyContinuousAt f x} :=
  (upperSemicontinuous_lipschitzModulusWithin f univ).isOpen_preimage _

end RW
