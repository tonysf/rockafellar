/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Horizon epi-limits

Taking epi-limits of the positive-scale perspectives makes the scalar
formulas valid even for empty epigraphs. The set horizon conventions from
Chapter 4 insert the origin unconditionally.
-/

import RockafellarWets.Chapter4.HorizonLimitSubsequences
import RockafellarWets.Chapter7.EpiLimitCharacterization
import RockafellarWets.Chapter7.HorizonScaleSelections

open Filter Function Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The perspective at positive scale, extended by infinity at every other scale. -/
noncomputable def positiveScalePerspective (f : E → EReal) (p : ℝ × E) : EReal :=
  if 0 < p.1 then (p.1 : EReal) * f (p.1⁻¹ • p.2) else ⊤

/-- **Definition 7.49**, the lower horizon epi-limit. -/
noncomputable def lowerHorizonEpiLimit (f : ℕ → E → EReal) (x : E) : EReal :=
  epiLowerLimit (fun n ↦ positiveScalePerspective (f n)) (0, x)

/-- **Definition 7.49**, the upper horizon epi-limit. -/
noncomputable def upperHorizonEpiLimit (f : ℕ → E → EReal) (x : E) : EReal :=
  epiUpperLimit (fun n ↦ positiveScalePerspective (f n)) (0, x)

/-- The horizon epi-limit exists with value `g` when the two bounds agree with it. -/
def HorizonEpiConverges (f : ℕ → E → EReal) (g : E → EReal) : Prop :=
  lowerHorizonEpiLimit f = g ∧ upperHorizonEpiLimit f = g

theorem positiveScalePerspective_smul (f : E → EReal) {s : ℝ} (hs : 0 < s) (x : E) :
    positiveScalePerspective f (s, s • x) = (s : EReal) * f x := by
  simp [positiveScalePerspective, hs, smul_smul, hs.ne']

private theorem scaled_le_coe_iff (v : EReal) (a : ℝ) {s : ℝ} (hs : 0 < s) :
    (s : EReal) * v ≤ (a : EReal) ↔ v ≤ ((s⁻¹ * a : ℝ) : EReal) := by
  induction v using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos hs]
  | top => simp only [EReal.coe_mul_top_of_pos hs, top_le_iff, EReal.coe_ne_top]
  | coe b =>
    simp only [← EReal.coe_mul, EReal.coe_le_coe_iff]
    rw [inv_mul_eq_div, le_div_iff₀ hs, mul_comm]

theorem mem_epigraph_positiveScalePerspective {f : E → EReal} {s : ℝ} {x : E} {a : ℝ} :
    ((s, x), a) ∈ epigraph (positiveScalePerspective f) ↔
      0 < s ∧ s⁻¹ • (x, a) ∈ epigraph f := by
  by_cases hs : 0 < s
  · simp only [mem_epigraph_iff, positiveScalePerspective, hs, if_true, true_and,
      Prod.smul_mk, smul_eq_mul, scaled_le_coe_iff _ _ hs]
  · simp [mem_epigraph_iff, positiveScalePerspective, hs]

private theorem mem_lowerHorizonEpiLimit_iff_scaling {f : ℕ → E → EReal} {w : E × ℝ} :
    w ∈ epigraph (lowerHorizonEpiLimit f) ↔
      ∃ (φ : ℕ → ℕ) (z : ℕ → E × ℝ) (s : ℕ → ℝ), StrictMono φ ∧
        (∀ n, z n ∈ epigraph (f (φ n))) ∧ (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
        Tendsto (fun n ↦ s n • z n) atTop (𝓝 w) := by
  change (((0 : ℝ), w.1), w.2) ∈ epigraph (epiLowerLimit _) ↔ _
  rw [epigraph_epiLowerLimit, mem_outerSetLimit_iff_exists_subsequence]
  constructor
  · rintro ⟨φ, p, hφ, hp, ht⟩
    let s := fun n ↦ (p n).1.1
    let y := fun n ↦ ((p n).1.2, (p n).2)
    have hm (n : ℕ) : 0 < s n ∧ (s n)⁻¹ • y n ∈ epigraph (f (φ n)) :=
      mem_epigraph_positiveScalePerspective.mp (hp n)
    refine ⟨φ, fun n ↦ (s n)⁻¹ • y n, s, hφ, fun n ↦ (hm n).2, fun n ↦ (hm n).1,
      (continuous_fst.tendsto _).comp ((continuous_fst.tendsto _).comp ht), ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ (hm _).1.ne', one_smul]
    exact ((continuous_snd.tendsto _).comp ((continuous_fst.tendsto _).comp ht)).prodMk_nhds
      ((continuous_snd.tendsto _).comp ht)
  · rintro ⟨φ, z, s, hφ, hz, hs, hs0, hst⟩
    refine ⟨φ, fun n ↦ ((s n, (s n • z n).1), (s n • z n).2), hφ, ?_, ?_⟩
    · intro n
      apply mem_epigraph_positiveScalePerspective.mpr
      refine ⟨hs n, ?_⟩
      simpa only [Prod.mk.eta, smul_smul, inv_mul_cancel₀ (hs n).ne', one_smul] using hz n
    · exact (hs0.prodMk_nhds ((continuous_fst.tendsto _).comp hst)).prodMk_nhds
        ((continuous_snd.tendsto _).comp hst)

/-- For arbitrary sequences the only extra point in the outer set horizon can be zero. -/
theorem horizonOuterSetLimit_epigraph_eq_insert (f : ℕ → E → EReal) :
    horizonOuterSetLimit (fun n ↦ epigraph (f n)) = insert 0 (epigraph (lowerHorizonEpiLimit f)) := by
  ext w
  rw [mem_horizonOuterSetLimit_iff_zero_or_scaling, mem_insert_iff, mem_lowerHorizonEpiLimit_iff_scaling]

/-- The exact outer epigraph identity of 7.49 requires nonempty epigraphs
on an infinite set of indices. -/
theorem epigraph_lowerHorizonEpiLimit {f : ℕ → E → EReal}
    (hf : ∃ᶠ n in atTop, (epigraph (f n)).Nonempty) :
    epigraph (lowerHorizonEpiLimit f) = horizonOuterSetLimit (fun n ↦ epigraph (f n)) := by
  rw [horizonOuterSetLimit_epigraph_eq_insert, eq_comm, insert_eq_of_mem]
  obtain ⟨φ, hφ, hm⟩ := extraction_of_frequently_atTop hf
  choose z hz using hm
  obtain ⟨s, hs, hs0, hst⟩ := exists_positive_scale_to_zero z
  exact mem_lowerHorizonEpiLimit_iff_scaling.mpr ⟨φ, z, s, hφ, hz, hs, hs0, hst⟩

private theorem upperHorizonEpiLimit_mem_iff {f : ℕ → E → EReal} {w : E × ℝ} :
    w ∈ epigraph (upperHorizonEpiLimit f) ↔
      ∀ φ : ℕ → ℕ, StrictMono φ → w ∈ epigraph (lowerHorizonEpiLimit (f ∘ φ)) := by
  change (((0 : ℝ), w.1), w.2) ∈ epigraph (epiUpperLimit _) ↔ _
  rw [epigraph_epiUpperLimit, mem_innerSetLimit_iff_forall_subsequence_outerSetLimit]
  exact forall_congr' fun φ ↦ imp_congr_right fun _ ↦ by
    change _ ↔ (((0 : ℝ), w.1), w.2) ∈ epigraph (epiLowerLimit _)
    rw [epigraph_epiLowerLimit]
    rfl

theorem horizonInnerSetLimit_epigraph_eq_insert (f : ℕ → E → EReal) :
    horizonInnerSetLimit (fun n ↦ epigraph (f n)) = insert 0 (epigraph (upperHorizonEpiLimit f)) := by
  ext w
  rw [horizonInnerSetLimit_eq_iInter_subsequence_outer]
  simp only [mem_iInter, mem_insert_iff, upperHorizonEpiLimit_mem_iff]
  by_cases hw : w = 0
  · simp [hw, (isCone_horizonOuterSetLimit _).1]
  · simp only [hw, false_or]
    apply forall_congr' fun φ ↦ imp_congr_right fun _ ↦ ?_
    change w ∈ horizonOuterSetLimit (fun n ↦ epigraph ((f ∘ φ) n)) ↔ _
    simp only [horizonOuterSetLimit_epigraph_eq_insert, mem_insert_iff, hw, false_or]

/-- The exact inner epigraph identity of 7.49 holds when the epigraphs
are eventually nonempty, regardless of the initial terms. -/
theorem epigraph_upperHorizonEpiLimit {f : ℕ → E → EReal}
    (hf : ∀ᶠ n in atTop, (epigraph (f n)).Nonempty) :
    epigraph (upperHorizonEpiLimit f) = horizonInnerSetLimit (fun n ↦ epigraph (f n)) := by
  rw [horizonInnerSetLimit_epigraph_eq_insert, eq_comm, insert_eq_of_mem]
  apply upperHorizonEpiLimit_mem_iff.mpr
  intro φ hφ
  change 0 ∈ epigraph (lowerHorizonEpiLimit (fun n ↦ f (φ n)))
  rw [epigraph_lowerHorizonEpiLimit (hφ.tendsto_atTop.eventually hf).frequently]
  exact (isCone_horizonOuterSetLimit _).1

end RW
