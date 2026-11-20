/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pasch–Hausdorff envelopes and Lipschitz minorants
-/

import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneConvergence
import RockafellarWets.Chapter3.ERealInfimum
import RockafellarWets.Chapter7.EpiLimitProperties

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] {f : E → EReal}

/-- **Example 9.11.** The Pasch–Hausdorff envelope with nonnegative constant. -/
noncomputable def paschHausdorffEnvelope (f : E → EReal) (k : ℝ≥0) (x : E) : EReal :=
  ⨅ y, f y + ((k * dist y x : ℝ) : EReal)

theorem paschHausdorffEnvelope_le (f : E → EReal) (k : ℝ≥0) (x : E) :
    paschHausdorffEnvelope f k x ≤ f x := by
  simpa [paschHausdorffEnvelope] using
    (iInf_le (fun y ↦ f y + ((k * dist y x : ℝ) : EReal)) x)

theorem paschHausdorffEnvelope_mono (f : E → EReal) :
    Monotone (paschHausdorffEnvelope f) := by
  intro k l hkl x
  apply iInf_mono
  intro y
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr
    (mul_le_mul_of_nonneg_right (show (k:ℝ) ≤ l from hkl) (dist_nonneg (x := y) (y := x))))

/-- Translation between two base points costs at most the Lipschitz penalty. -/
theorem paschHausdorffEnvelope_le_add (f : E → EReal) (k : ℝ≥0) (x z : E) :
    paschHausdorffEnvelope f k x ≤ paschHausdorffEnvelope f k z + ((k * dist x z : ℝ) : EReal) := by
  unfold paschHausdorffEnvelope
  rw [iInf_add_coe]
  apply le_iInf
  intro y
  apply (iInf_le _ y).trans
  rw [add_assoc,← EReal.coe_add]
  apply add_le_add le_rfl
  apply EReal.coe_le_coe_iff.mpr
  calc
    _ ≤ k * (dist y z + dist z x) := mul_le_mul_of_nonneg_left (dist_triangle y z x) k.coe_nonneg
    _ = _ := by rw [mul_add,dist_comm z x]

/-- A finite upper value of the input bounds every envelope value above. -/
theorem paschHausdorffEnvelope_ne_top (hp : IsProper f) (k : ℝ≥0) (x : E) :
    paschHausdorffEnvelope f k x ≠ ⊤ := by
  obtain ⟨y,hy⟩ := hp.1
  have hfin := EReal.coe_toReal hy.ne (hp.2 y).ne'
  have hbound := iInf_le (fun y ↦ f y + ((k * dist y x : ℝ) : EReal)) y
  rw [← hfin,← EReal.coe_add] at hbound
  exact (hbound.trans_lt (EReal.coe_lt_top _)).ne

theorem paschHausdorffEnvelope_eq_bot_of_eq_bot {k : ℝ≥0} {x : E}
    (hx : paschHausdorffEnvelope f k x = ⊥) :
    ∀ y, paschHausdorffEnvelope f k y = ⊥ := by
  intro y
  apply bot_unique
  simpa [hx] using paschHausdorffEnvelope_le_add f k y x

/-- **Example 9.11**, the finite alternative has the asserted global constant. -/
theorem paschHausdorffEnvelope_lipschitz (hp : IsProper f) {k : ℝ≥0} {x : E}
    (hx : paschHausdorffEnvelope f k x ≠ ⊥) :
    (∀ y, paschHausdorffEnvelope f k y = ((paschHausdorffEnvelope f k y).toReal : EReal)) ∧
      LipschitzWith k (fun y ↦ (paschHausdorffEnvelope f k y).toReal) := by
  have hfin (y : E) : paschHausdorffEnvelope f k y = ((paschHausdorffEnvelope f k y).toReal : EReal) :=
    (EReal.coe_toReal (paschHausdorffEnvelope_ne_top hp k y)
      (fun hy ↦ hx (paschHausdorffEnvelope_eq_bot_of_eq_bot hy x))).symm
  refine ⟨hfin,LipschitzWith.of_le_add_mul k fun y z ↦ ?_⟩
  have h := paschHausdorffEnvelope_le_add f k y z
  rwa [hfin y,hfin z,← EReal.coe_add,EReal.coe_le_coe_iff] at h

/-- **Example 9.11**, the envelope dominates every minorant with that constant. -/
theorem le_paschHausdorffEnvelope_of_lipschitz {g : E → ℝ} {k : ℝ≥0}
    (hg : LipschitzWith k g) (hle : ∀ x, (g x : EReal) ≤ f x) (x : E) :
    (g x : EReal) ≤ paschHausdorffEnvelope f k x := by
  apply le_iInf
  intro y
  have hreal : g x ≤ g y + k * dist y x := by simpa only [dist_comm] using hg.le_add_mul x y
  exact (EReal.coe_le_coe_iff.mpr hreal).trans
    (by rw [EReal.coe_add]; exact add_le_add (hle y) le_rfl)

/-- The envelope is nontrivial exactly when a finite Lipschitz minorant exists. -/
theorem paschHausdorffEnvelope_ne_bot_iff_lipschitz_minorant (hp : IsProper f) (k : ℝ≥0) (x : E) :
    paschHausdorffEnvelope f k x ≠ ⊥ ↔ ∃ g : E → ℝ, LipschitzWith k g ∧ ∀ y, (g y : EReal) ≤ f y := by
  constructor
  · intro hx
    obtain ⟨hfin,hL⟩ := paschHausdorffEnvelope_lipschitz hp hx
    exact ⟨_,hL,fun y ↦ (hfin y).symm.trans_le (paschHausdorffEnvelope_le f k y)⟩
  · rintro ⟨g,hg,hle⟩
    exact ((EReal.bot_lt_coe (g x)).trans_le (le_paschHausdorffEnvelope_of_lipschitz hg hle x)).ne'

/-- A fixed Lipschitz minorant and lower semicontinuity recover the function
as the supremum over all penalty constants. -/
theorem iSup_paschHausdorffEnvelope (hl : LowerSemicontinuous f) {k₀ : ℝ≥0} {x₀ : E}
    (hproper : IsProper f) (hbase : paschHausdorffEnvelope f k₀ x₀ ≠ ⊥) (x : E) :
    (⨆ k : ℝ≥0, paschHausdorffEnvelope f k x) = f x := by
  apply le_antisymm (iSup_le fun k ↦ paschHausdorffEnvelope_le f k x)
  apply le_of_forall_lt_imp_le_of_dense
  intro a ha
  obtain ⟨b,hab,hbf⟩ := EReal.exists_between_coe_real ha
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp (hl x b hbf)
  have hfin := (paschHausdorffEnvelope_lipschitz hproper hbase).1 x
  let m := (paschHausdorffEnvelope f k₀ x).toReal
  let k : ℝ≥0 := k₀ + (max 0 ((b-m)/δ)).toNNReal
  have hkk : (k₀:ℝ) ≤ k := by dsimp [k]; simp
  have hkco : (k:ℝ) = (k₀:ℝ) + max 0 ((b-m)/δ) := by
    simp only [k,NNReal.coe_add,Real.coe_toNNReal _ (le_max_left ..)]
  have hlarge : b-m ≤ ((k:ℝ)-k₀)*δ := by
    rw [hkco,add_sub_cancel_left]
    have h := le_max_right 0 ((b-m)/δ)
    exact (div_le_iff₀ hδ).mp (by simpa using h)
  apply hab.le.trans
  apply (le_iSup _ k).trans'
  apply le_iInf
  intro y
  by_cases hy : dist y x < δ
  · exact (hball hy).le.trans (le_add_of_nonneg_right (EReal.coe_nonneg.mpr (mul_nonneg k.coe_nonneg dist_nonneg)))
  · have hdist : δ ≤ dist y x := le_of_not_gt hy
    have hbound := iInf_le (fun z ↦ f z + ((k₀*dist z x:ℝ):EReal)) y
    change paschHausdorffEnvelope f k₀ x ≤ _ at hbound
    rw [hfin] at hbound
    have hs := add_le_add hbound (le_refl ((((k:ℝ)-k₀)*dist y x : ℝ) : EReal))
    have he : (k₀:ℝ)*dist y x + ((k:ℝ)-k₀)*dist y x = k*dist y x := by ring
    rw [← EReal.coe_add,add_assoc,← EReal.coe_add,he] at hs
    apply (EReal.coe_le_coe_iff.mpr ?_).trans hs
    dsimp [m] at hlarge
    linarith [mul_le_mul_of_nonneg_left hdist (sub_nonneg.mpr hkk)]

/-- **Example 9.11**, increasing-penalty pointwise convergence. -/
theorem tendsto_paschHausdorffEnvelope (hl : LowerSemicontinuous f) (hp : IsProper f)
    {k₀ : ℝ≥0} {x₀ : E} (hbase : paschHausdorffEnvelope f k₀ x₀ ≠ ⊥) (x : E) :
    Tendsto (fun k : ℝ≥0 ↦ paschHausdorffEnvelope f k x) atTop (𝓝 (f x)) := by
  rw [← iSup_paschHausdorffEnvelope hl hp hbase x]
  exact tendsto_atTop_iSup (fun k l hkl ↦ paschHausdorffEnvelope_mono f hkl x)

/-- Every envelope of a proper function is lower semicontinuous, including
the identically negative-infinite alternative. -/
theorem lowerSemicontinuous_paschHausdorffEnvelope (hp : IsProper f) (k : ℝ≥0) :
    LowerSemicontinuous (paschHausdorffEnvelope f k) := by
  by_cases h : paschHausdorffEnvelope f k 0 = ⊥
  · have he : paschHausdorffEnvelope f k = fun _ ↦ ⊥ :=
      funext (paschHausdorffEnvelope_eq_bot_of_eq_bot h)
    rw [he]
    exact continuous_const.lowerSemicontinuous
  · obtain ⟨hfin,hL⟩ := paschHausdorffEnvelope_lipschitz hp h
    have he : paschHausdorffEnvelope f k =
        fun x ↦ ((paschHausdorffEnvelope f k x).toReal : EReal) := funext hfin
    rw [he]
    exact (continuous_coe_real_ereal.comp hL.continuous).lowerSemicontinuous

/-- **Example 9.11**, epi-convergence along any increasing sequence of
penalties tending to infinity. -/
theorem epiConverges_paschHausdorffEnvelope (hl : LowerSemicontinuous f) (hp : IsProper f)
    {k₀ : ℝ≥0} {x₀ : E} (hbase : paschHausdorffEnvelope f k₀ x₀ ≠ ⊥)
    {k : ℕ → ℝ≥0} (hm : Monotone k) (hk : Tendsto k atTop atTop) :
    EpiConverges (fun n ↦ paschHausdorffEnvelope f (k n)) f := by
  have he := epiConverges_of_monotone ((paschHausdorffEnvelope_mono f).comp hm)
  have hclosure (n : ℕ) : epiClosure (paschHausdorffEnvelope f (k n)) =
      paschHausdorffEnvelope f (k n) :=
    epiClosure_eq_of_lowerSemicontinuous (lowerSemicontinuous_paschHausdorffEnvelope hp _)
  have hs : (fun x ↦ ⨆ n, epiClosure (paschHausdorffEnvelope f (k n)) x) = f := by
    funext x
    simp only [hclosure]
    exact tendsto_nhds_unique
      (tendsto_atTop_iSup (fun i j hij ↦ paschHausdorffEnvelope_mono f (hm hij) x))
      ((tendsto_paschHausdorffEnvelope hl hp hbase x).comp hk)
  change EpiConverges (fun n ↦ paschHausdorffEnvelope f (k n))
    (fun x ↦ ⨆ n, epiClosure (paschHausdorffEnvelope f (k n)) x) at he
  rwa [hs] at he

end RW
