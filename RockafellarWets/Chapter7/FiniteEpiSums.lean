/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Finite epi-sums and epigraph sums
-/

import RockafellarWets.Chapter3.EpiAddition
import RockafellarWets.Chapter4.FiniteSums
import RockafellarWets.Chapter4.FiniteSumConvergence
import RockafellarWets.Chapter7.EpigraphAddition
import RockafellarWets.Chapter7.EpiLimits

open Filter Function Set Topology
open scoped Pointwise

namespace RW

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- Finite inf-addition is the infimum of the sums of finite real upper
bounds. In particular a positive-infinite summand makes it positive infinity
even when another summand is negative infinity. -/
noncomputable def finiteInfAddition (a : ι → EReal) : EReal :=
  ⨅ r : {r : ι → ℝ // ∀ i, a i ≤ (r i : EReal)}, ((∑ i, r.1 i : ℝ) : EReal)

theorem finiteInfAddition_le_sum {a : ι → EReal} {r : ι → ℝ} (h : ∀ i, a i ≤ (r i : EReal)) :
    finiteInfAddition a ≤ ((∑ i, r i : ℝ) : EReal) := iInf_le _ (⟨r, h⟩ : Subtype _)

theorem finiteInfAddition_fin_two (a b : EReal) :
    finiteInfAddition (![a, b] : Fin 2 → EReal) = infAddition a b := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨t, ht, ht'⟩ := EReal.exists_between_coe_real h
    obtain ⟨r, s, hr, hs, rfl⟩ := (infAddition_le_coe_iff ..).mp ht.le
    apply ht'.not_ge
    have hbound : ∀ i : Fin 2, (![a, b] : Fin 2 → EReal) i ≤
        (((![r, s] : Fin 2 → ℝ) i : ℝ) : EReal) := by
      intro i
      fin_cases i
      · exact hr
      · exact hs
    simpa [Fin.sum_univ_two] using finiteInfAddition_le_sum hbound
  · refine le_iInf fun r ↦ ?_
    apply (infAddition_le_coe_iff ..).mpr
    exact ⟨r.1 0, r.1 1, r.2 0, r.2 1, (Fin.sum_univ_two r.1).symm⟩

/-- The finite infimal convolution in 7.56 minimizes over decompositions
of the argument, using inf-addition on the component function values. -/
noncomputable def finiteEpiSum (f : ι → E → EReal) (x : E) : EReal :=
  ⨅ z : {z : ι → E // ∑ i, z i = x}, finiteInfAddition (fun i ↦ f i (z.1 i))

theorem finiteEpiSum_eq_epiBoundary (f : ι → E → EReal) :
    finiteEpiSum f = epiBoundary (finiteSetSum (fun i ↦ epigraph (f i))) := by
  funext x
  apply le_antisymm
  · refine le_iInf fun a ↦ ?_
    obtain ⟨z, hz, he⟩ := a.property
    have hx : ∑ i, (z i).1 = x := by simpa only [Prod.fst_sum] using congrArg Prod.fst he
    have ha : ∑ i, (z i).2 = a.1 := by simpa only [Prod.snd_sum] using congrArg Prod.snd he
    exact (iInf_le _ (⟨fun i ↦ (z i).1, hx⟩ : {u : ι → E // ∑ i, u i = x})).trans
      ((finiteInfAddition_le_sum hz).trans_eq (congrArg ((↑) : ℝ → EReal) ha))
  · refine le_iInf fun z ↦ le_iInf fun r ↦ ?_
    apply iInf_le_of_le (⟨∑ i, r.1 i, ?_⟩ : {a : ℝ // (x, a) ∈ finiteSetSum (fun i ↦ epigraph (f i))})
    · exact le_rfl
    · exact ⟨fun i ↦ (z.1 i, r.1 i), r.2, by simp [Prod.fst_sum, Prod.snd_sum, Prod.ext_iff, z.2]⟩

/-- A sum of epigraphs of a nonempty finite family is upward closed in height. -/
theorem finiteSetSum_epigraph_upward [Nonempty ι] {f : ι → E → EReal} {x : E} {a b : ℝ}
    (h : (x, a) ∈ finiteSetSum (fun i ↦ epigraph (f i))) (hab : a ≤ b) :
    (x, b) ∈ finiteSetSum (fun i ↦ epigraph (f i)) := by
  classical
  obtain ⟨p, hp, hsum⟩ := h
  let j := Classical.arbitrary ι
  refine ⟨fun i ↦ p i + if i = j then (0, b - a) else 0, ?_, ?_⟩
  · intro i
    change p i + (if i = j then (0, b - a) else 0) ∈ epigraph (f i)
    by_cases hij : i = j
    · rw [if_pos hij]
      change f i ((p i).1 + 0) ≤ (((p i).2 + (b - a) : ℝ) : EReal)
      rw [add_zero]
      exact (hp i).trans (EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_right (sub_nonneg.mpr hab)))
    · simpa only [if_neg hij, add_zero] using hp i
  · simp [Finset.sum_add_distrib, hsum]

theorem finiteSetSum_epigraph_subset_epigraph_finiteEpiSum (f : ι → E → EReal) :
    finiteSetSum (fun i ↦ epigraph (f i)) ⊆ epigraph (finiteEpiSum f) := by
  rintro ⟨x, a⟩ h
  rw [finiteEpiSum_eq_epiBoundary]
  change epiBoundary _ x ≤ (a : EReal)
  exact iInf_le _ (⟨a, h⟩ : {t : ℝ // (x, t) ∈ finiteSetSum (fun i ↦ epigraph (f i))})

theorem closure_epigraph_finiteEpiSum [Nonempty ι] (f : ι → E → EReal) :
    closure (epigraph (finiteEpiSum f)) = closure (finiteSetSum (fun i ↦ epigraph (f i))) := by
  apply le_antisymm _ (closure_mono (finiteSetSum_epigraph_subset_epigraph_finiteEpiSum f))
  apply closure_minimal _ isClosed_closure
  rintro ⟨x, a⟩ ha
  have hsub : Ioi a ⊆ Prod.mk x ⁻¹' closure (finiteSetSum (fun i ↦ epigraph (f i))) := by
    intro b hab
    have hlt := lt_of_le_of_lt ha (EReal.coe_lt_coe_iff.mpr hab)
    change finiteEpiSum f x < (b : EReal) at hlt
    rw [finiteEpiSum_eq_epiBoundary] at hlt
    obtain ⟨t, ht⟩ := iInf_lt_iff.mp hlt
    exact subset_closure (finiteSetSum_epigraph_upward t.property (EReal.coe_lt_coe_iff.mp ht).le)
  exact closure_minimal hsub (isClosed_closure.preimage (continuous_const.prodMk continuous_id))
    (by simp [closure_Ioi])

theorem epigraph_finiteEpiSum_of_isClosed [Nonempty ι] (f : ι → E → EReal)
    (h : IsClosed (finiteSetSum (fun i ↦ epigraph (f i)))) :
    epigraph (finiteEpiSum f) = finiteSetSum (fun i ↦ epigraph (f i)) := by
  rw [finiteEpiSum_eq_epiBoundary]
  exact epigraph_epiBoundary h fun _ _ _ ↦ finiteSetSum_epigraph_upward

/-- **Proposition 7.56**, the unconditional upper epi-limit inequality,
with arbitrary infinite component values. -/
theorem epiUpperLimit_finiteEpiSum_le (f : ι → ℕ → E → EReal) :
    epiUpperLimit (fun n ↦ finiteEpiSum (fun i ↦ f i n)) ≤ finiteEpiSum (fun i ↦ epiUpperLimit (f i)) := by
  rw [finiteEpiSum_eq_epiBoundary (fun i ↦ epiUpperLimit (f i))]
  intro x
  refine le_iInf fun a ↦ ?_
  have ha := a.property
  simp only [epigraph_epiUpperLimit] at ha
  have hm := finiteSetSum_innerSetLimit_subset (fun i n ↦ epigraph (f i n)) ha
  have h := innerSetLimit_mono (fun n ↦ finiteSetSum_epigraph_subset_epigraph_finiteEpiSum
    (fun i ↦ f i n)) hm
  rwa [← epigraph_epiUpperLimit] at h


/-- Binary infimal convolution using the book's inf-addition at opposite infinities. -/
noncomputable def infAddEpiSum (g h : E → EReal) (x : E) : EReal :=
  ⨅ z : E, infAddition (g (x - z)) (h z)

theorem finiteEpiSum_fin_two (g h : E → EReal) :
    finiteEpiSum (![g, h] : Fin 2 → E → EReal) = infAddEpiSum g h := by
  funext x
  apply le_antisymm
  · refine le_iInf fun y ↦ ?_
    let z : {z : Fin 2 → E // ∑ i, z i = x} := ⟨![x - y, y], by simp [Fin.sum_univ_two]⟩
    apply (iInf_le (fun z : {z : Fin 2 → E // ∑ i, z i = x} ↦
      finiteInfAddition (fun i ↦ (![g, h] : Fin 2 → E → EReal) i (z.1 i))) z).trans
    have he : (fun i ↦ (![g, h] : Fin 2 → E → EReal) i (z.1 i)) = ![g (x - y), h y] := by
      funext i
      fin_cases i <;> rfl
    rw [he, finiteInfAddition_fin_two]
  · refine le_iInf fun z ↦ ?_
    have hx : z.1 0 + z.1 1 = x := by simpa [Fin.sum_univ_two] using z.2
    have he : (fun i ↦ (![g, h] : Fin 2 → E → EReal) i (z.1 i)) = ![g (z.1 0), h (z.1 1)] := by
      funext i
      fin_cases i <;> rfl
    rw [he, finiteInfAddition_fin_two]
    simpa [← hx, infAddEpiSum] using iInf_le (fun y ↦ infAddition (g (x - y)) (h y)) (z.1 1)

theorem infAddEpiSum_eq_epiSum_of_ne_bot [NormedSpace ℝ E]
    {g h : E → EReal} (hg : ∀ x, g x ≠ ⊥) (hh : ∀ x, h x ≠ ⊥) : infAddEpiSum g h = epiSum g h := by
  funext x
  simp only [infAddEpiSum, epiSum_apply, infAddition_eq_add_of_ne_bot (hg _) (hh _)]

end RW
