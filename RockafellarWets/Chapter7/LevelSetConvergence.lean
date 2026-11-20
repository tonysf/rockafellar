/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Level sets of epi-convergent functions
-/

import RockafellarWets.Chapter7.EpiLimits
import RockafellarWets.Chapter5.GraphicalLimitFormulas

open Filter Function Set Topology

namespace RW

section Outer

variable {E : Type*} [PseudoMetricSpace E]

/-- **Proposition 7.7(a).** Every converging sequence of levels tests the
lower epi-limit. -/
theorem le_epiLowerLimit_iff_outer_levelSet_subset {f : ℕ → E → EReal} {g : E → EReal} :
    g ≤ epiLowerLimit f ↔ ∀ (a : ℝ) (b : ℕ → ℝ), Tendsto b atTop (𝓝 a) →
      outerSetLimit (fun n ↦ levelSet (f n) (b n)) ⊆ levelSet g a := by
  rw [← epigraph_subset_epigraph_iff, epigraph_epiLowerLimit_eq_svGraph]
  have hgraph (x : E) (a : ℝ) :
      (x, a) ∈ svGraph (graphicalOuterLimit (fun n ↦ epiProfile (f n))) ↔
        ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 a) ∧
          x ∈ outerSetLimit (fun n ↦ levelSet (f n) (b n)) := by
    change x ∈ svInv (graphicalOuterLimit (fun n ↦ epiProfile (f n))) a ↔ _
    rw [← graphicalOuterLimit_svInv, graphicalOuterLimit_eq_iUnion]
    simp only [mem_iUnion₂, mem_setOf_eq, svInv_epiProfile, exists_prop]
  constructor
  · intro h a b hb x hx
    exact h ((hgraph x a).mpr ⟨b, hb, hx⟩)
  · rintro h ⟨x, a⟩ hx
    obtain ⟨b, hb, hxb⟩ := (hgraph x a).mp hx
    exact h a b hb hxb

end Outer

section Inner

variable {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]

/-- Simultaneously meet countably many eventual requirements, with the
number of requirements honored increasing to infinity. -/
theorem exists_diagonal_stage (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ q : ℕ → ℕ, Monotone q ∧ Tendsto q atTop atTop ∧ ∀ᶠ n in atTop, P (q n) n := by
  classical
  choose N hN using fun k ↦ eventually_atTop.mp (h k)
  let q (n : ℕ) := Nat.findGreatest (fun k ↦ N k ≤ n) n
  refine ⟨q, fun _ _ hab ↦ Nat.findGreatest_mono (fun _ hk ↦ hk.trans hab) hab, ?_, ?_⟩
  · apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k, eventually_ge_atTop (N k)] with n hn hn'
    exact Nat.le_findGreatest hn hn'
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    exact hN _ _ (Nat.findGreatest_spec (P := fun k ↦ N k ≤ n) (Nat.zero_le n) hn)

/-- A single decreasing sequence of heights works for the entire level set.
Enumerating a countable topological basis lets us choose the heights
independently of the point being recovered. -/
private theorem exists_antitone_level_of_inner {f : ℕ → E → EReal} {g : E → EReal}
    (h : epigraph g ⊆ innerSetLimit (fun n ↦ epigraph (f n))) (a : ℝ) :
    ∃ b : ℕ → ℝ, Antitone b ∧ Tendsto b atTop (𝓝 a) ∧
      levelSet g a ⊆ innerSetLimit (fun n ↦ levelSet (f n) (b n)) := by
  classical
  let δ (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hδ (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  let P (k n : ℕ) := ∀ U : TopologicalSpace.countableBasis E, Encodable.encode U ≤ k →
    ((U : Set E) ∩ levelSet g a).Nonempty →
      (levelSet (f n) (a + δ k) ∩ (U : Set E)).Nonempty
  have hevent (k : ℕ) : ∀ᶠ n in atTop, P k n := by
    let B := {U : TopologicalSpace.countableBasis E // Encodable.encode U ≤ k}
    let enc (U : B) : Fin (k + 1) := ⟨Encodable.encode U.val, Nat.lt_succ_of_le U.property⟩
    letI : Finite B := Finite.of_injective enc (fun x y heq ↦
      Subtype.ext (Encodable.encode_injective (congrArg Fin.val heq)))
    have hB (U : B) : ∀ᶠ n in atTop, ((U.val : Set E) ∩ levelSet g a).Nonempty →
        (levelSet (f n) (a + δ k) ∩ (U.val : Set E)).Nonempty := by
      by_cases hit : ((U.val : Set E) ∩ levelSet g a).Nonempty
      · obtain ⟨x, hxU, hxg⟩ := hit
        have hU := (TopologicalSpace.isOpen_of_mem_countableBasis U.val.property).mem_nhds hxU
        have ha : Iio (a + δ k) ∈ 𝓝 a := Iio_mem_nhds (lt_add_of_pos_right _ (hδ k))
        have hx := h (a := (x, a)) hxg
        filter_upwards [hx _ (prod_mem_nhds hU ha)] with n hn _
        obtain ⟨⟨y, r⟩, hyr, hyU, hr⟩ := hn
        exact ⟨y, hyr.trans (EReal.coe_le_coe_iff.mpr hr.le), hyU⟩
      · exact Eventually.of_forall fun _ ha ↦ (hit ha).elim
    filter_upwards [eventually_all.mpr hB] with n hn U hUk
    exact hn ⟨U, hUk⟩
  obtain ⟨q, hqmono, hq, hP⟩ := exists_diagonal_stage P hevent
  refine ⟨fun n ↦ a + δ (q n), ?_, ?_, ?_⟩
  · intro i j hij
    change a + 1 / ((q j : ℝ) + 1) ≤ a + 1 / ((q i : ℝ) + 1)
    gcongr
    exact hqmono hij
  · simpa [δ, Function.comp_def] using (tendsto_const_nhds (x := a)).add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hq)
  · intro x hx V hV
    obtain ⟨O, hOV, ho, hxo⟩ := mem_nhds_iff.mp hV
    obtain ⟨U, hUB, hxU, hUO⟩ := (TopologicalSpace.isBasis_countableBasis E).exists_subset_of_mem_open hxo ho
    let u : TopologicalSpace.countableBasis E := ⟨U, hUB⟩
    filter_upwards [hP, hq.eventually_ge_atTop (Encodable.encode u)] with n hn hnu
    obtain ⟨y, hy, hyU⟩ := hn u hnu ⟨x, hxU, hx⟩
    exact ⟨y, hy, hOV (hUO hyU)⟩

omit [SecondCountableTopology E] in
/-- Any common recovery sequence of heights gives the upper epi-limit
inequality. Only the forward construction needs countability. -/
private theorem epiUpperLimit_le_of_level_sequences {f : ℕ → E → EReal} {g : E → EReal}
    (h : ∀ a : ℝ, ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 a) ∧
      levelSet g a ⊆ innerSetLimit (fun n ↦ levelSet (f n) (b n))) :
    epiUpperLimit f ≤ g := by
  apply epigraph_subset_epigraph_iff.mp
  rw [epigraph_epiUpperLimit]
  rintro ⟨x, a⟩ hx W hW
  obtain ⟨b, hb, hinner⟩ := h a
  obtain ⟨U, hU, V, hV, hsub⟩ := mem_nhds_prod_iff.mp hW
  filter_upwards [hinner hx U hU, hb.eventually_mem hV] with n hn hbn
  obtain ⟨y, hy, hyU⟩ := hn
  exact ⟨(y, b n), hy, hsub ⟨hyU, hbn⟩⟩

/-- **Proposition 7.7(b).** A common recovery height sequence can be chosen
antitone at each real level. -/
theorem epiUpperLimit_le_iff_exists_antitone_level {f : ℕ → E → EReal} {g : E → EReal} :
    epiUpperLimit f ≤ g ↔ ∀ a : ℝ, ∃ b : ℕ → ℝ, Antitone b ∧ Tendsto b atTop (𝓝 a) ∧
      levelSet g a ⊆ innerSetLimit (fun n ↦ levelSet (f n) (b n)) := by
  constructor
  · rw [← epigraph_subset_epigraph_iff, epigraph_epiUpperLimit]
    exact exists_antitone_level_of_inner
  · intro h
    apply epiUpperLimit_le_of_level_sequences
    intro a
    obtain ⟨b, _, hb, hinner⟩ := h a
    exact ⟨b, hb, hinner⟩

theorem epiUpperLimit_le_iff_exists_level {f : ℕ → E → EReal} {g : E → EReal} :
    epiUpperLimit f ≤ g ↔ ∀ a : ℝ, ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 a) ∧
      levelSet g a ⊆ innerSetLimit (fun n ↦ levelSet (f n) (b n)) := by
  refine ⟨fun h a ↦ ?_, epiUpperLimit_le_of_level_sequences⟩
  obtain ⟨b, _, hb, hinner⟩ := epiUpperLimit_le_iff_exists_antitone_level.mp h a
  exact ⟨b, hb, hinner⟩

end Inner

/-- **Proposition 7.7(c).** Combining the outer and inner level-set tests
characterizes epi-convergence. -/
theorem epiConverges_iff_levelSets {E : Type*} [PseudoMetricSpace E] [SecondCountableTopology E]
    {f : ℕ → E → EReal} {g : E → EReal} :
    EpiConverges f g ↔
      (∀ (a : ℝ) (b : ℕ → ℝ), Tendsto b atTop (𝓝 a) →
        outerSetLimit (fun n ↦ levelSet (f n) (b n)) ⊆ levelSet g a) ∧
      (∀ a : ℝ, ∃ b : ℕ → ℝ, Antitone b ∧ Tendsto b atTop (𝓝 a) ∧
        levelSet g a ⊆ innerSetLimit (fun n ↦ levelSet (f n) (b n))) := by
  rw [← le_epiLowerLimit_iff_outer_levelSet_subset, ← epiUpperLimit_le_iff_exists_antitone_level,
    epiConverges_iff_epiLimits_eq]
  have hlu := epiLowerLimit_le_epiUpperLimit f
  exact ⟨fun ⟨hl, hu⟩ ↦ ⟨hl.ge, hu.le⟩,
    fun ⟨hl, hu⟩ ↦ ⟨(hlu.trans hu).antisymm hl, hu.antisymm (hl.trans hlu)⟩⟩

end RW
