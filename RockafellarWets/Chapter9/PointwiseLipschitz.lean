/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lipschitz moduli of pointwise suprema and infima
-/

import RockafellarWets.Chapter9.BoundedLipschitzModulus
import RockafellarWets.Chapter9.LipschitzModulusCalculus
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Analysis.Normed.Module.Convex

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {ι E : Type*} [Nonempty ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite-valued supremum preserves a common Lipschitz constant. -/
theorem lipschitzOnWith_ciSup {F : ι → E → ℝ} {U : Set E} {k : ℝ≥0}
    (hb : ∀ x ∈ U, BddAbove (range fun i ↦ F i x)) (h : ∀ i, LipschitzOnWith k (F i) U) :
    LipschitzOnWith k (fun x ↦ ⨆ i, F i x) U := by
  apply LipschitzOnWith.of_le_add_mul
  intro x hx y hy
  apply ciSup_le
  intro i
  exact ((h i).le_add_mul hx hy).trans (add_le_add (le_ciSup (hb y hy) i) le_rfl)

/-- A finite-valued infimum preserves a common Lipschitz constant. -/
theorem lipschitzOnWith_ciInf {F : ι → E → ℝ} {U : Set E} {k : ℝ≥0}
    (hb : ∀ x ∈ U, BddBelow (range fun i ↦ F i x)) (h : ∀ i, LipschitzOnWith k (F i) U) :
    LipschitzOnWith k (fun x ↦ ⨅ i, F i x) U := by
  apply LipschitzOnWith.of_le_add_mul
  intro x hx y hy
  rw [← sub_le_iff_le_add]
  apply le_ciInf
  intro i
  exact (sub_le_iff_le_add.mpr (((ciInf_le (hb x hx) i).trans ((h i).le_add_mul hx hy))))

/-- **Proposition 9.10**, an upper semicontinuous common modulus bounds
a pointwise supremum wherever that supremum is finite. -/
theorem lipschitzModulus_ciSup_le_of_common_bound {F : ι → E → ℝ} {O : Set E} {x : E}
    {K : E → ℝ≥0∞} (hO : O ∈ 𝓝 x) (hK : UpperSemicontinuousAt K x)
    (hb : BddAbove (range fun i ↦ F i x))
    (h : ∀ z ∈ O, ∀ i, lipschitzModulus (F i) z ≤ K z) :
    lipschitzModulus (fun z ↦ ⨆ i, F i z) x ≤ K x := by
  by_contra! hlt
  obtain ⟨k,hk,hkl⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hO (hK _ hk))
  have hfi (i : ι) : LipschitzOnWith k (F i) (ball x r) :=
    lipschitzOnWith_of_modulus_le_of_convex (convex_ball _ _)
      (fun z hz ↦ (h z (hball hz).1 i).trans (hball hz).2.le)
  obtain ⟨B,hB⟩ := hb
  have hb' (z : E) (hz : z ∈ ball x r) : BddAbove (range fun i ↦ F i z) := by
    refine ⟨B+k*dist z x,?_⟩
    rintro _ ⟨i,rfl⟩
    exact ((hfi i).le_add_mul hz (mem_ball_self hr)).trans
      (add_le_add (hB (mem_range_self i)) le_rfl)
  have hs := lipschitzOnWith_ciSup hb' hfi
  exact hkl.not_ge (lipschitzModulus_le (ball_mem_nhds x hr) hs)

/-- **Proposition 9.10**, the corresponding infimum estimate. -/
theorem lipschitzModulus_ciInf_le_of_common_bound {F : ι → E → ℝ} {O : Set E} {x : E}
    {K : E → ℝ≥0∞} (hO : O ∈ 𝓝 x) (hK : UpperSemicontinuousAt K x)
    (hb : BddBelow (range fun i ↦ F i x))
    (h : ∀ z ∈ O, ∀ i, lipschitzModulus (F i) z ≤ K z) :
    lipschitzModulus (fun z ↦ ⨅ i, F i z) x ≤ K x := by
  by_contra! hlt
  obtain ⟨k,hk,hkl⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hO (hK _ hk))
  have hfi (i : ι) : LipschitzOnWith k (F i) (ball x r) :=
    lipschitzOnWith_of_modulus_le_of_convex (convex_ball _ _)
      (fun z hz ↦ (h z (hball hz).1 i).trans (hball hz).2.le)
  obtain ⟨B,hB⟩ := hb
  have hb' (z : E) (hz : z ∈ ball x r) : BddBelow (range fun i ↦ F i z) := by
    refine ⟨B-k*dist x z,?_⟩
    rintro _ ⟨i,rfl⟩
    have hle := ((hB (mem_range_self i)).trans ((hfi i).le_add_mul (mem_ball_self hr) hz))
    linarith
  have hs := lipschitzOnWith_ciInf hb' hfi
  exact hkl.not_ge (lipschitzModulus_le (ball_mem_nhds x hr) hs)

variable [Finite ι]

private theorem upperSemicontinuousAt_finite_moduli (F : ι → E → ℝ) (x : E) :
    UpperSemicontinuousAt (fun z ↦ ⨆ i, lipschitzModulus (F i) z) x := by
  intro a ha
  have he (i : ι) : ∀ᶠ z in 𝓝 x, lipschitzModulus (F i) z < a :=
    upperSemicontinuous_lipschitzModulusWithin (F i) univ x a ((le_iSup _ i).trans_lt ha)
  filter_upwards [Filter.eventually_all.mpr he] with z hz
  obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ lipschitzModulus (F i) z)
  rw [← hi]
  exact hz i

/-- **Proposition 9.10**, the bound for a finite maximum. -/
theorem lipschitzModulus_ciSup_le (F : ι → E → ℝ) (x : E) :
    lipschitzModulus (fun z ↦ ⨆ i, F i z) x ≤ ⨆ i, lipschitzModulus (F i) x :=
  lipschitzModulus_ciSup_le_of_common_bound univ_mem (upperSemicontinuousAt_finite_moduli F x)
    ((finite_range _).bddAbove) (fun z _ i ↦ le_iSup (fun j ↦ lipschitzModulus (F j) z) i)

/-- **Proposition 9.10**, the bound for a finite minimum. -/
theorem lipschitzModulus_ciInf_le (F : ι → E → ℝ) (x : E) :
    lipschitzModulus (fun z ↦ ⨅ i, F i z) x ≤ ⨆ i, lipschitzModulus (F i) x :=
  lipschitzModulus_ciInf_le_of_common_bound univ_mem (upperSemicontinuousAt_finite_moduli F x)
    ((finite_range _).bddBelow) (fun z _ i ↦ le_iSup (fun j ↦ lipschitzModulus (F j) z) i)

theorem strictlyContinuousAt_ciSup (F : ι → E → ℝ) {x : E}
    (h : ∀ i, StrictlyContinuousAt (F i) x) : StrictlyContinuousAt (fun z ↦ ⨆ i, F i z) x := by
  obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ lipschitzModulus (F i) x)
  exact (lipschitzModulus_ciSup_le F x).trans_lt (hi ▸ h i)

theorem strictlyContinuousAt_ciInf (F : ι → E → ℝ) {x : E}
    (h : ∀ i, StrictlyContinuousAt (F i) x) : StrictlyContinuousAt (fun z ↦ ⨅ i, F i z) x := by
  obtain ⟨i,hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ lipschitzModulus (F i) x)
  exact (lipschitzModulus_ciInf_le F x).trans_lt (hi ▸ h i)

end RW
