/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Epi-limits under inf-addition
-/

import RockafellarWets.Chapter7.EpiOperations
import RockafellarWets.Chapter7.EpigraphAddition

open Filter Topology

namespace RW

variable {E : Type*} [PseudoMetricSpace E]

/-- Functions constant in space epi-converge whenever their values converge. -/
theorem epiConverges_const_values {v : ℕ → EReal} {a : EReal}
    (h : Tendsto v atTop (𝓝 a)) :
    EpiConverges (fun n (_ : E) ↦ v n) (fun _ ↦ a) := by
  apply epiConverges_iff_liminf_limsup.mpr
  exact fun x ↦ ⟨fun _ _ ↦ h.liminf_eq.ge, fun _ ↦ x, tendsto_const_nhds, h.limsup_eq.le⟩

/-- The unconditional lower estimate with Mathlib addition on the left
and the book's inf-addition on the right. It also gives the book's lower
estimate at every point where the limiting heights have compatible signs. -/
theorem add_epiLowerLimit_le_infAddition (f h : ℕ → E → EReal) :
    epiLowerLimit f + epiLowerLimit h ≤ epiLowerLimit (fun n x ↦ infAddition (f n x) (h n x)) := by
  refine (add_epiLowerLimit_le f h).trans ?_
  apply epigraph_subset_epigraph_iff.mp
  rw [epigraph_epiLowerLimit, epigraph_epiLowerLimit]
  exact outerSetLimit_mono fun n ↦ epigraph_subset_epigraph_iff.mpr
    fun x ↦ add_le_infAddition _ _

private theorem epiConverges_infAddition_of_joint_recovery
    {f h : ℕ → E → EReal} {g k : E → EReal}
    (hf : EpiConverges f g) (hh : EpiConverges h k) (hg : IsProper g) (hk : IsProper k)
    (hr : ∀ x, ∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧ Tendsto (fun n ↦ f n (y n)) atTop (𝓝 (g x)) ∧
      Tendsto (fun n ↦ h n (y n)) atTop (𝓝 (k x))) :
    EpiConverges (fun n x ↦ infAddition (f n x) (h n x)) (fun x ↦ infAddition (g x) (k x)) := by
  apply epiConverges_iff_liminf_limsup.mpr
  intro x
  rw [infAddition_eq_add_of_ne_bot (hg.2 x).ne' (hk.2 x).ne']
  constructor
  · intro y hy
    exact (add_le_add ((epiConverges_iff_liminf_limsup.mp hf x).1 y hy)
      ((epiConverges_iff_liminf_limsup.mp hh x).1 y hy)).trans
      (EReal.le_liminf_add.trans (liminf_le_liminf (.of_forall fun n ↦ add_le_infAddition _ _)))
  · obtain ⟨y, hy, hv, hw⟩ := hr x
    refine ⟨y, hy, ?_⟩
    have ht := (EReal.continuousAt_add (p := (g x, k x)) (.inr (hk.2 x).ne')
      (.inl (hg.2 x).ne')).tendsto.comp (hv.prodMk_nhds hw)
    have heq : (fun n ↦ f n (y n) + h n (y n)) =ᶠ[atTop]
        fun n ↦ infAddition (f n (y n)) (h n (y n)) := by
      filter_upwards [hv.eventually_const_lt (hg.2 x), hw.eventually_const_lt (hk.2 x)] with n hv' hw'
      exact (infAddition_eq_add_of_ne_bot hv'.ne' hw'.ne').symm
    exact (ht.congr' heq).limsup_eq.le

/-- **Theorem 7.46(a,b)** for the book's inf-addition, including both choices
of continuously converging summand. -/
theorem epiConverges_infAddition {f h : ℕ → E → EReal} {g k : E → EReal}
    (hf : EpiConverges f g) (hh : EpiConverges h k) (hg : IsProper g) (hk : IsProper k)
    (hconv : ((∀ x, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) ∧
        (∀ x, Tendsto (fun n ↦ h n x) atTop (𝓝 (k x)))) ∨
      (∀ x (y : ℕ → E), Tendsto y atTop (𝓝 x) → Tendsto (fun n ↦ f n (y n)) atTop (𝓝 (g x))) ∨
      (∀ x (y : ℕ → E), Tendsto y atTop (𝓝 x) → Tendsto (fun n ↦ h n (y n)) atTop (𝓝 (k x)))) :
    EpiConverges (fun n x ↦ infAddition (f n x) (h n x)) (fun x ↦ infAddition (g x) (k x)) := by
  apply epiConverges_infAddition_of_joint_recovery hf hh hg hk
  intro x
  rcases hconv with ⟨hp, hq⟩ | hc | hc
  · exact ⟨fun _ ↦ x, tendsto_const_nhds, hp x, hq x⟩
  · obtain ⟨y, hy, hw⟩ := hh.exists_tendsto_values x
    exact ⟨y, hy, hc x y hy, hw⟩
  · obtain ⟨y, hy, hv⟩ := hf.exists_tendsto_values x
    exact ⟨y, hy, hv, hc x y hy⟩

/-- **Obstruction to the unconditional inf-addition inequality in 7.46.**
The constant-in-space sequences with values `n` and `-n` cancel exactly;
their limiting values are opposite infinities. -/
theorem infAddition_epiLowerLimit_counterexample :
    ∃ f h : ℕ → ℝ → EReal, ¬ (fun x ↦ infAddition (epiLowerLimit f x) (epiLowerLimit h x)) ≤
        epiLowerLimit (fun n x ↦ infAddition (f n x) (h n x)) := by
  let f (n : ℕ) (_ : ℝ) : EReal := ((n : ℝ) : EReal)
  let h (n : ℕ) (_ : ℝ) : EReal := ((-(n : ℝ) : ℝ) : EReal)
  have hp : Tendsto (fun n : ℕ ↦ ((n : ℝ) : EReal)) atTop (𝓝 ⊤) :=
    EReal.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop
  have hn : Tendsto (fun n : ℕ ↦ ((-(n : ℝ) : ℝ) : EReal)) atTop (𝓝 ⊥) := by simpa using hp.neg
  have hf : epiLowerLimit f = fun _ ↦ ⊤ := (epiConverges_iff_epiLimits_eq.mp
    (epiConverges_const_values (E := ℝ) hp)).1
  have hh : epiLowerLimit h = fun _ ↦ ⊥ := (epiConverges_iff_epiLimits_eq.mp
    (epiConverges_const_values (E := ℝ) hn)).1
  have hsum (n : ℕ) (x : ℝ) : infAddition (f n x) (h n x) = 0 := by
    rw [infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)]
    rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  have hz : epiLowerLimit (fun n x ↦ infAddition (f n x) (h n x)) = fun _ ↦ 0 := by
    simp only [hsum]
    exact (epiConverges_iff_epiLimits_eq.mp (epiConverges_const_values (E := ℝ)
      (tendsto_const_nhds (x := (0 : EReal))))).1
  refine ⟨f, h, ?_⟩
  intro hle
  have h0 := hle 0
  change infAddition (epiLowerLimit f 0) (epiLowerLimit h 0) ≤ _ at h0
  rw [hf, hh, hz] at h0
  simp [infAddition] at h0

end RW
