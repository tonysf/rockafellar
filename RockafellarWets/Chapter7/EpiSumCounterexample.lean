/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vertical cancellation in Proposition 7.56
-/

import RockafellarWets.Chapter7.HorizonLevelBoundedness
import RockafellarWets.Chapter7.TotalEpiSums
import RockafellarWets.Chapter7.EpiLimitCharacterization

open Filter Set Topology

namespace RW

private noncomputable def fallingHeight (n : ℕ) (x : ℝ) : EReal :=
  if x = 0 then ((-(n : ℝ) : ℝ) : EReal) else ⊤

private noncomputable def risingHeight (n : ℕ) (x : ℝ) : EReal :=
  if x = 0 then 0 else if x = 1 then ((n : ℝ) : EReal) else ⊤

private noncomputable def negativeFiber (x : ℝ) : EReal :=
  if x = 0 then ⊥ else ⊤

private theorem epigraph_fallingHeight (n : ℕ) :
    epigraph (fallingHeight n) = ({0} : Set ℝ) ×ˢ Ici (-(n : ℝ)) := by
  ext ⟨x, a⟩
  by_cases hx : x = 0 <;>
    simp only [mem_epigraph_iff, fallingHeight, hx, if_true, if_false, mem_prod,
      mem_singleton_iff, mem_Ici, true_and, false_and, top_le_iff, EReal.coe_ne_top,
      EReal.coe_le_coe_iff]

private theorem epigraph_risingHeight (n : ℕ) :
    epigraph (risingHeight n) =
      ({0} : Set ℝ) ×ˢ Ici 0 ∪ ({1} : Set ℝ) ×ˢ Ici (n : ℝ) := by
  ext ⟨x, a⟩
  by_cases h0 : x = 0
  · subst x
    simp [risingHeight, mem_epigraph_iff]
  · by_cases h1 : x = 1 <;> simp [risingHeight, mem_epigraph_iff, h0, h1]
    exact EReal.coe_le_coe_iff

private theorem epigraph_negativeFiber : epigraph negativeFiber = ({0} : Set ℝ) ×ˢ univ := by
  ext ⟨x, a⟩
  by_cases h : x = 0 <;> simp [negativeFiber, mem_epigraph_iff, h]

private theorem total_fallingHeight : TotalEpiConverges fallingHeight negativeFiber := by
  have hne : (epigraph negativeFiber).Nonempty := ⟨(0, 0), by simp [negativeFiber, mem_epigraph_iff]⟩
  apply EpiConverges.total_of_convex _ hne (fun n ↦ epigraph_fallingHeight n ▸
    (convex_singleton (0 : ℝ)).prod (convex_Ici _))
  unfold EpiConverges
  simp only [epigraph_negativeFiber, epigraph_fallingHeight]
  have hm : Monotone (fun n : ℕ ↦ ({0} : Set ℝ) ×ˢ Ici (-(n : ℝ))) := by
    intro i j hij
    exact prod_mono Subset.rfl (Ici_subset_Ici.mpr (neg_le_neg (by exact_mod_cast hij)))
  have he : (⋃ n : ℕ, ({0} : Set ℝ) ×ˢ Ici (-(n : ℝ))) = {0} ×ˢ univ := by
    ext ⟨x, a⟩
    simp only [mem_iUnion, mem_prod, mem_singleton_iff, mem_Ici, mem_univ, and_true]
    constructor
    · rintro ⟨_, hx, _⟩
      exact hx
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt (-a)
      exact ⟨n, hx, by linarith⟩
  simpa only [he, (isClosed_singleton.prod isClosed_univ).closure_eq] using pkConverges_of_monotone hm

private theorem total_risingHeight : TotalEpiConverges risingHeight (indicatorVA ({0} : Set ℝ)) := by
  let k : ℝ → EReal := indicatorVA {0, 1}
  have hbound (n : ℕ) : k ≤ risingHeight n := by
    intro x
    by_cases h0 : x = 0
    · simp [k, risingHeight, h0]
    by_cases h1 : x = 1 <;> simp [k, risingHeight, h0, h1]
  have hco : IsCoercive k := by
    intro γ hγ
    refine ⟨-γ, ?_⟩
    intro x
    by_cases h0 : x = 0
    · simp [k, h0, hγ.le]
    by_cases h1 : x = 1 <;> simp [k, h0, h1]
  apply EpiConverges.total_of_equiCoercive _ ⟨(0, 0), by simp [mem_epigraph_iff]⟩ hco
    (Eventually.of_forall hbound)
  unfold EpiConverges
  simp only [epigraph_risingHeight, epigraph_indicatorVA]
  let A := ({0} : Set ℝ) ×ˢ Ici (0 : ℝ)
  let B := fun n : ℕ ↦ ({1} : Set ℝ) ×ˢ Ici (n : ℝ)
  have hm : Antitone (fun n ↦ A ∪ B n) := fun _ _ hij ↦ union_subset_union_right _
    (prod_mono Subset.rfl (Ici_subset_Ici.mpr (by exact_mod_cast hij)))
  have he : (⋂ n, A ∪ B n) = A := by
    ext p
    simp only [mem_iInter, mem_union]
    constructor
    · intro hh
      obtain ⟨n, hn⟩ := exists_nat_gt p.2
      exact (hh n).resolve_right fun h ↦ hn.not_ge h.2
    · exact fun hh _ ↦ Or.inl hh
  simpa only [he] using pkConverges_of_antitone_isClosed hm
    (fun _ ↦ (isClosed_singleton.prod isClosed_Ici).union (isClosed_singleton.prod isClosed_Ici))

/-- **Proposition 7.56**, obstruction to both unqualified scalar claims.
The scalar horizon condition excludes every nonzero horizontal tuple,
and the convex limit epigraphs satisfy the product-horizon identity.
Opposite vertical directions still prevent convergence of the epi-sum. -/
theorem infAddEpiSum_vertical_cancellation_counterexample :
    ∃ (f h : ℕ → ℝ → EReal) (g k : ℝ → EReal),
      (∀ n, IsProper (f n) ∧ LowerSemicontinuous (f n) ∧
        IsProper (h n) ∧ LowerSemicontinuous (h n)) ∧
      TotalEpiConverges f g ∧ TotalEpiConverges h k ∧
      (∀ x y : ℝ, infAddition (horizonFunction g x) (horizonFunction k y) ≤ 0 → x = 0 ∧ y = 0) ∧
      horizonCone (epigraph g ×ˢ epigraph k) = horizonCone (epigraph g) ×ˢ horizonCone (epigraph k) ∧
      ¬ EpiConverges (fun n ↦ infAddEpiSum (f n) (h n)) (infAddEpiSum g k) := by
  let k := indicatorVA ({0} : Set ℝ)
  have hgne : (epigraph negativeFiber).Nonempty := ⟨(0, 0), by simp [mem_epigraph_iff, negativeFiber]⟩
  have hkne : (epigraph k).Nonempty := ⟨(0, 0), by simp [mem_epigraph_iff, k]⟩
  have hphg : PositivelyHomogeneous negativeFiber := by
    apply positivelyHomogeneous_of_isCone_epigraph
    rw [epigraph_negativeFiber]
    refine ⟨⟨rfl, mem_univ _⟩, fun {p} hp s _ ↦ ⟨?_, mem_univ _⟩⟩
    change s * p.1 = 0
    rw [show p.1 = 0 from hp.1, mul_zero]
  have hphk : PositivelyHomogeneous k := positivelyHomogeneous_indicatorVA_iff.mpr
    ⟨rfl, fun {x} hx s _ ↦ by simp [show x = 0 from hx]⟩
  have hg := horizonFunction_eq_self_of_lowerSemicontinuous_of_positivelyHomogeneous
    total_fallingHeight.epiConverges.lowerSemicontinuous hphg
  have hk := horizonFunction_eq_self_of_lowerSemicontinuous_of_positivelyHomogeneous
    total_risingHeight.epiConverges.lowerSemicontinuous hphk
  refine ⟨fallingHeight, risingHeight, negativeFiber, k, ?_, total_fallingHeight, total_risingHeight, ?_, ?_, ?_⟩
  · intro n
    refine ⟨⟨⟨0, by simpa only [fallingHeight, if_pos rfl] using EReal.coe_lt_top (-(n : ℝ))⟩, fun x ↦ ?_⟩, ?_, ⟨⟨0, by simp [risingHeight]⟩, fun x ↦ ?_⟩, ?_⟩
    · by_cases h : x = 0
      · simpa only [fallingHeight, if_pos h] using EReal.bot_lt_coe (-(n : ℝ))
      · simp [fallingHeight, h]
    · apply lowerSemicontinuous_of_isClosed_epigraph_ereal
      rw [epigraph_fallingHeight]
      exact isClosed_singleton.prod isClosed_Ici
    · by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> simp [risingHeight, h0, h1]
      exact EReal.bot_lt_coe (n : ℝ)
    · apply lowerSemicontinuous_of_isClosed_epigraph_ereal
      rw [epigraph_risingHeight]
      exact (isClosed_singleton.prod isClosed_Ici).union (isClosed_singleton.prod isClosed_Ici)
  · intro x y
    rw [hg, hk]
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [negativeFiber, indicatorVA, infAddition, hx, hy]
  · apply horizonCone_prod_eq_of_convex_nonempty _ _ hgne hkne
    · rw [epigraph_negativeFiber]
      exact (convex_singleton _).prod convex_univ
    · rw [show epigraph k = ({0} : Set ℝ) ×ˢ Ici 0 from epigraph_indicatorVA _]
      exact (convex_singleton _).prod (convex_Ici _)
  · intro hc
    have hle (n : ℕ) : infAddEpiSum (fallingHeight n) (risingHeight n) 1 ≤ 0 :=
      iInf_le_of_le (1 : ℝ) (by
        simp only [sub_self, fallingHeight, risingHeight, if_true, if_neg one_ne_zero, infAddition,
          EReal.coe_ne_top, or_self, if_false, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, le_refl])
    have htop : infAddEpiSum negativeFiber k 1 = ⊤ := by
      apply top_unique
      refine le_iInf fun y ↦ ?_
      by_cases h : y = 0 <;> simp [infAddition, negativeFiber, k, h]
    have h := ((epiConverges_iff_liminf_limsup.mp hc) 1).1 (fun _ ↦ 1) tendsto_const_nhds
    rw [htop] at h
    have hl := (liminf_le_liminf (Eventually.of_forall hle) : _ ≤ liminf (fun _ : ℕ ↦ (0 : EReal)) atTop)
    simpa using h.trans hl

end RW
