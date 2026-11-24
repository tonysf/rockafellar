/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1G–H: Pointwise max and min, epi-addition, epi-multiplication, epi-composition

* **Proposition 1.26**: semicontinuity under pointwise max and min.
* **Proposition 1.27**: lower semicontinuity, properness and continuity of epi-sums, via
  Theorem 1.17 applied to the epi-sum integrand of Chapter 3.
* **Exercise 1.28**: epigraphs of epi-sums (inf-addition, `infEpiSum` of Chapter 14) and
  epi-multiples.
* **Exercise 1.29**: calculus of indicators, distances and envelopes.
* **Example 1.30**: vector-max and log-exponential functions.
* **Exercise 1.31** and **Proposition 1.32**: epi-composition.
-/

import RockafellarWets.Chapter1.ProximalBehavior
import RockafellarWets.Chapter1.AuxiliaryFacts
import RockafellarWets.Chapter3.Pointwise
import RockafellarWets.Chapter14.EpiOperations
import RockafellarWets.Chapter8.SupportExamples
import RockafellarWets.Chapter11.EntropyConjugacy

open Set Filter Topology Metric Bornology
open scoped Pointwise

noncomputable section

namespace RW

variable {α E : Type*}

/-! ## Proposition 1.26 -/

section PointwiseMaxMin

variable [TopologicalSpace α]

/-- **Proposition 1.26(a)**: the pointwise supremum of lsc functions is lsc. -/
theorem lowerSemicontinuous_iSup_ereal {ι : Type*} {f : ι → α → EReal}
    (hf : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous (fun x ↦ ⨆ i, f i x) :=
  _root_.lowerSemicontinuous_iSup hf

/-- **Proposition 1.26(b)**: the pointwise infimum of finitely many lsc functions is lsc. -/
theorem lowerSemicontinuous_iInf_finite_ereal {ι : Type*} [Finite ι] {f : ι → α → EReal}
    (hf : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous (fun x ↦ ⨅ i, f i x) := by
  rw [lowerSemicontinuous_iff_isClosed_levelSet]
  intro a
  have heq : levelSet (fun x ↦ ⨅ i, f i x) a = ⋃ i, levelSet (f i) a := by
    ext x
    simp only [levelSet, mem_setOf_eq, mem_iUnion]
    constructor
    · intro h
      rcases isEmpty_or_nonempty ι with hι | hι
      · rw [iInf_of_empty] at h
        exact absurd h (by simp)
      · obtain ⟨i, hi⟩ := Finite.exists_min (fun i ↦ f i x)
        refine ⟨i, le_trans ?_ h⟩
        exact le_iInf hi
    · rintro ⟨i, hi⟩
      exact (iInf_le _ i).trans hi
  rw [heq]
  exact isClosed_iUnion_of_finite fun i ↦ lowerSemicontinuous_iff_isClosed_levelSet.1 (hf i) a

/-- The upper counterpart of 1.26(b): the pointwise supremum of finitely many usc functions is
usc. -/
theorem upperSemicontinuous_iSup_finite_ereal {ι : Type*} [Finite ι] {f : ι → α → EReal}
    (hf : ∀ i, UpperSemicontinuous (f i)) : UpperSemicontinuous (fun x ↦ ⨆ i, f i x) := by
  have hneg : ∀ i, LowerSemicontinuous (fun x ↦ -f i x) := fun i ↦
    continuous_neg.comp_upperSemicontinuous_antitone (hf i) fun _ _ h ↦ EReal.neg_le_neg_iff.2 h
  have h := lowerSemicontinuous_iInf_finite_ereal hneg
  have hsup : (fun x ↦ ⨆ i, f i x) = fun x ↦ -⨅ i, -f i x := by
    funext x
    rw [neg_iInf_ereal]
    simp
  rw [hsup]
  exact continuous_neg.comp_lowerSemicontinuous_antitone h fun _ _ h ↦ EReal.neg_le_neg_iff.2 h

/-- **Proposition 1.26(c)**: for finitely many continuous `fᵢ`, the pointwise supremum and the
pointwise infimum are continuous. -/
theorem continuous_iSup_iInf_finite_ereal {ι : Type*} [Finite ι] {f : ι → α → EReal}
    (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x ↦ ⨆ i, f i x) ∧ Continuous (fun x ↦ ⨅ i, f i x) := by
  have hl : ∀ i, LowerSemicontinuous (f i) := fun i ↦ (hf i).lowerSemicontinuous
  have hu : ∀ i, UpperSemicontinuous (f i) := fun i ↦ (hf i).upperSemicontinuous
  rw [continuous_iff_lowerSemicontinuous_and_upperSemicontinuous,
    continuous_iff_lowerSemicontinuous_and_upperSemicontinuous]
  exact ⟨⟨_root_.lowerSemicontinuous_iSup hl, upperSemicontinuous_iSup_finite_ereal hu⟩,
    ⟨lowerSemicontinuous_iInf_finite_ereal hl, _root_.upperSemicontinuous_iInf hu⟩⟩

end PointwiseMaxMin

/-! ## Proposition 1.27 -/

section EpiAddition

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- For functions never equal to `-∞`, the book's inf-addition epi-sum `infEpiSum` (Chapter 14)
agrees with the epi-sum `epiSum` of Chapter 3. -/
theorem infEpiSum_eq_epiSum {f₁ f₂ : E → EReal} (h₁ : ∀ x, f₁ x ≠ ⊥) (h₂ : ∀ x, f₂ x ≠ ⊥) :
    infEpiSum f₁ f₂ = epiSum f₁ f₂ := by
  funext x
  simp only [infEpiSum, epiSum_apply]
  exact iInf_congr fun w ↦ infAddition_eq_add_of_ne_bot (h₁ _) (h₂ _)

omit [NormedSpace ℝ E] in
theorem epiSum_swap (f₁ f₂ : E → EReal) : epiSum f₁ f₂ = epiSum f₂ f₁ := by
  funext x
  simp only [epiSum_apply]
  apply le_antisymm <;> refine le_iInf fun w ↦ ?_
  · simpa only [sub_sub_cancel, add_comm] using iInf_le (fun y ↦ f₁ (x - y) + f₂ y) (x - w)
  · simpa only [sub_sub_cancel, add_comm] using iInf_le (fun y ↦ f₂ (x - y) + f₁ y) (x - w)

/-- The boundedness hypothesis of Proposition 1.27: for each bounded `B` and `α ∈ ℝ`, the set
`{(x₁, x₂) | f₁(x₁) + f₂(x₂) ≤ α, x₁ + x₂ ∈ B}` is bounded. -/
def EpiSumBounded (f₁ f₂ : E → EReal) : Prop :=
  ∀ B : Set E, IsBounded B → ∀ a : ℝ,
    IsBounded {p : E × E | f₁ p.1 + f₂ p.2 ≤ a ∧ p.1 + p.2 ∈ B}

omit [NormedSpace ℝ E] in
theorem EpiSumBounded.swap {f₁ f₂ : E → EReal} (h : EpiSumBounded f₁ f₂) :
    EpiSumBounded f₂ f₁ := by
  intro B hB a
  have hb := h B hB a
  refine (hb.image_snd.prod hb.image_fst).subset fun p hp ↦ ?_
  have hmem : (p.2, p.1) ∈ {q : E × E | f₁ q.1 + f₂ q.2 ≤ a ∧ q.1 + q.2 ∈ B} :=
    ⟨by rw [add_comm]; exact hp.1, by rw [add_comm]; exact hp.2⟩
  exact ⟨⟨(p.2, p.1), hmem, rfl⟩, ⟨(p.2, p.1), hmem, rfl⟩⟩

omit [NormedSpace ℝ E] in
/-- The parenthetical case of Proposition 1.27: `f₁` level-bounded and `f₂` bounded below. -/
theorem epiSumBounded_of_isLevelBounded {f₁ f₂ : E → EReal} (h₁ : IsLevelBounded f₁)
    (h₂ : ∃ m : ℝ, ∀ x, (m : EReal) ≤ f₂ x) : EpiSumBounded f₁ f₂ := by
  obtain ⟨m, hm⟩ := h₂
  intro B hB a
  refine ((h₁ (a - m)).prod (hB.sub (h₁ (a - m)))).subset fun p hp ↦ ⟨?_, ?_⟩
  · exact le_coe_sub_of_add_coe_le ((add_le_add le_rfl (hm p.2)).trans hp.1)
  · refine ⟨p.1 + p.2, hp.2, p.1, ?_, add_sub_cancel_left _ _⟩
    exact le_coe_sub_of_add_coe_le ((add_le_add le_rfl (hm p.2)).trans hp.1)

omit [NormedSpace ℝ E] in
theorem isLevelBoundedInXLocallyUniformly_epiSumIntegrand {f₁ f₂ : E → EReal}
    (h : EpiSumBounded f₁ f₂) : IsLevelBoundedInXLocallyUniformly (epiSumIntegrand f₁ f₂) := by
  intro x a
  refine ⟨1, one_pos, (((h (closedBall x 1) isBounded_closedBall a).image_snd).prod
    (isBounded_closedBall (x := x) (r := 1))).subset ?_⟩
  rintro ⟨w, y⟩ ⟨⟨-, hy⟩, hlev⟩
  refine ⟨⟨(y - w, w), ⟨hlev, by rw [sub_add_cancel]; exact hy⟩, rfl⟩, hy⟩

variable [FiniteDimensional ℝ E]

/-- **Proposition 1.27**: for lsc proper `f₁`, `f₂` satisfying the boundedness hypothesis, the
epi-sum `f₁ □ f₂` is lsc and proper. -/
theorem epiSum_lowerSemicontinuous_isProper {f₁ f₂ : E → EReal}
    (hl₁ : LowerSemicontinuous f₁) (hl₂ : LowerSemicontinuous f₂) (hp₁ : IsProper f₁)
    (hp₂ : IsProper f₂) (h : EpiSumBounded f₁ f₂) :
    LowerSemicontinuous (epiSum f₁ f₂) ∧ IsProper (epiSum f₁ f₂) := by
  obtain ⟨hp, hl, -, -⟩ := parametric_minimization_a
    (lowerSemicontinuous_epiSumIntegrand hl₁ hl₂ hp₁ hp₂) (isProper_epiSumIntegrand hp₁ hp₂)
    (isLevelBoundedInXLocallyUniformly_epiSumIntegrand h)
  exact ⟨hl, hp⟩

theorem epiSum_continuousAt_of_left {f₁ f₂ : E → EReal}
    (hl₁ : LowerSemicontinuous f₁) (hl₂ : LowerSemicontinuous f₂) (hp₁ : IsProper f₁)
    (hp₂ : IsProper f₂) (h : EpiSumBounded f₁ f₂) {x x₁ x₂ : E} (hx : x₁ + x₂ = x)
    (hval : epiSum f₁ f₂ x = f₁ x₁ + f₂ x₂) (hfin : epiSum f₁ f₂ x ≠ ⊤)
    (hc : ContinuousAt f₁ x₁) : ContinuousAt (epiSum f₁ f₂) x := by
  have hint : epiSumIntegrand f₁ f₂ (x₂, x) = f₁ x₁ + f₂ x₂ := by
    rw [epiSumIntegrand_apply, ← hx, add_sub_cancel_right]
  have hmem : x₂ ∈ paramArgmin (epiSumIntegrand f₁ f₂) x :=
    (mem_paramArgmin_iff _ _ _).2 ⟨hint.trans hval.symm, lt_top_iff_ne_top.2 hfin⟩
  have h₂top : f₂ x₂ ≠ ⊤ := by
    intro h2; rw [hval, h2, EReal.add_top_of_ne_bot (hp₁.2 x₁).ne'] at hfin; exact hfin rfl
  have hcont : ContinuousWithinAt (fun v ↦ epiSumIntegrand f₁ f₂ (x₂, v)) univ x := by
    refine ContinuousAt.continuousWithinAt ?_
    have hc' : ContinuousAt (fun v ↦ f₁ (v - x₂)) x := by
      have h1 : ContinuousAt (fun v : E ↦ v - x₂) x := continuousAt_id.sub continuousAt_const
      have h2 : ContinuousAt f₁ (x - x₂) := by
        rw [show x - x₂ = x₁ by rw [← hx, add_sub_cancel_right]]; exact hc
      exact ContinuousAt.comp (f := fun v : E ↦ v - x₂) h2 h1
    have hadd := EReal.continuousAt_add (p := (f₁ (x - x₂), f₂ x₂))
      (Or.inr (hp₂.2 x₂).ne') (Or.inr h₂top)
    have hpair : ContinuousAt (fun v ↦ (f₁ (v - x₂), f₂ x₂)) x := hc'.prodMk continuousAt_const
    exact ContinuousAt.comp (g := fun p : EReal × EReal ↦ p.1 + p.2)
      (f := fun v ↦ (f₁ (v - x₂), f₂ x₂)) (x := x) hadd hpair
  have := parametric_minimization_c (lowerSemicontinuous_epiSumIntegrand hl₁ hl₂ hp₁ hp₂)
    (isProper_epiSumIntegrand hp₁ hp₂) (isLevelBoundedInXLocallyUniformly_epiSumIntegrand h)
    hmem hcont
  exact continuousWithinAt_univ _ _ |>.1 this

/-- **Proposition 1.27**, continuity: `f₁ □ f₂` is continuous at any `x̄` where its value is finite
and equals `f₁(x̄₁) + f₂(x̄₂)` with `x̄₁ + x̄₂ = x̄`, `f₁` continuous at `x̄₁` or `f₂` continuous at
`x̄₂`. -/
theorem epiSum_continuousAt {f₁ f₂ : E → EReal}
    (hl₁ : LowerSemicontinuous f₁) (hl₂ : LowerSemicontinuous f₂) (hp₁ : IsProper f₁)
    (hp₂ : IsProper f₂) (h : EpiSumBounded f₁ f₂) {x x₁ x₂ : E} (hx : x₁ + x₂ = x)
    (hval : epiSum f₁ f₂ x = f₁ x₁ + f₂ x₂) (hfin : epiSum f₁ f₂ x ≠ ⊤)
    (hc : ContinuousAt f₁ x₁ ∨ ContinuousAt f₂ x₂) : ContinuousAt (epiSum f₁ f₂) x := by
  rcases hc with hc | hc
  · exact epiSum_continuousAt_of_left hl₁ hl₂ hp₁ hp₂ h hx hval hfin hc
  · rw [epiSum_swap] at hval hfin ⊢
    exact epiSum_continuousAt_of_left hl₂ hl₁ hp₂ hp₁ h.swap (by rw [add_comm]; exact hx)
      (by rw [add_comm]; exact hval) hfin hc

end EpiAddition

/-! ## Exercise 1.28 -/

section EpigraphSums

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- **Exercise 1.28(a)**, regardless of attainment:
`{(x, α) | (f₁ □ f₂)(x) < α} = {(x₁, α₁) | f₁(x₁) < α₁} + {(x₂, α₂) | f₂(x₂) < α₂}`, with the
book's inf-addition epi-sum `infEpiSum`. -/
theorem setOf_infEpiSum_lt_eq_add (f₁ f₂ : E → EReal) :
    {p : E × ℝ | infEpiSum f₁ f₂ p.1 < p.2} =
      {p : E × ℝ | f₁ p.1 < p.2} + {p : E × ℝ | f₂ p.1 < p.2} := by
  ext ⟨x, a⟩
  simp only [mem_setOf_eq]
  constructor
  · intro h
    obtain ⟨w, hw⟩ := iInf_lt_iff.1 h
    obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.1 hw
    obtain ⟨r, s, hr, hs, hrs⟩ := (infAddition_le_coe_iff _ _ b).1 hb1.le
    have hba : b < a := EReal.coe_lt_coe_iff.1 hb2
    refine ⟨(x - w, r + (a - b) / 2), ?_, (w, s + (a - b) / 2), ?_, ?_⟩
    · exact lt_of_le_of_lt hr (EReal.coe_lt_coe_iff.2 (by linarith))
    · exact lt_of_le_of_lt hs (EReal.coe_lt_coe_iff.2 (by linarith))
    · simp only [Prod.mk_add_mk, sub_add_cancel, Prod.mk.injEq, true_and]
      linarith
  · rintro ⟨⟨x₁, a₁⟩, h₁, ⟨x₂, a₂⟩, h₂, heq⟩
    simp only [mem_setOf_eq] at h₁ h₂
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine lt_of_le_of_lt (iInf_le _ x₂) ?_
    rw [add_sub_cancel_right, infAddition,
      if_neg (by push_neg; exact ⟨ne_top_of_lt h₁, ne_top_of_lt h₂⟩), EReal.coe_add]
    exact EReal.add_lt_add h₁ h₂

omit [NormedSpace ℝ E] in
/-- **Exercise 1.28(a)**: `epi (f₁ □ f₂) = epi f₁ + epi f₂` as long as the infimum defining
`(f₁ □ f₂)(x)` is attained when finite. -/
theorem epigraph_infEpiSum_of_attained {f₁ f₂ : E → EReal}
    (h : ∀ x, (∃ r : ℝ, infEpiSum f₁ f₂ x = r) →
      ∃ w, infEpiSum f₁ f₂ x = infAddition (f₁ (x - w)) (f₂ w)) :
    epigraph (infEpiSum f₁ f₂) = epigraph f₁ + epigraph f₂ := by
  apply subset_antisymm
  · rintro ⟨x, a⟩ hxa
    have hle : infEpiSum f₁ f₂ x ≤ a := hxa
    induction hv : infEpiSum f₁ f₂ x using EReal.rec with
    | bot =>
      have hstrict : (x, a - 1) ∈ {p : E × ℝ | infEpiSum f₁ f₂ p.1 < p.2} := by
        change infEpiSum f₁ f₂ x < ((a - 1 : ℝ) : EReal)
        rw [hv]; exact EReal.bot_lt_coe _
      rw [setOf_infEpiSum_lt_eq_add] at hstrict
      obtain ⟨⟨x₁, a₁⟩, h₁, ⟨x₂, a₂⟩, h₂, heq⟩ := hstrict
      simp only [Prod.mk_add_mk, Prod.mk.injEq] at heq
      refine Set.mem_add.2 ⟨(x₁, a₁ + 1), (mem_epigraph_iff _ _ _).2 ?_, (x₂, a₂),
        (mem_epigraph_iff _ _ _).2 h₂.le, ?_⟩
      · exact (le_of_lt h₁).trans (EReal.coe_le_coe_iff.2 (by linarith))
      · simp only [Prod.mk_add_mk, Prod.mk.injEq]
        exact ⟨heq.1, by linarith [heq.2]⟩
    | top =>
      rw [hv] at hle
      exact absurd hle (by simp)
    | coe r =>
      obtain ⟨w, hw⟩ := h x ⟨r, hv⟩
      obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := (infAddition_le_coe_iff _ _ a).1 (hw ▸ hle)
      exact Set.mem_add.2 ⟨(x - w, r₁), hr₁, (w, r₂), hr₂, by simp [hr]⟩
  · rintro _ ⟨⟨x₁, a₁⟩, h₁, ⟨x₂, a₂⟩, h₂, rfl⟩
    change infEpiSum f₁ f₂ (x₁ + x₂) ≤ ((a₁ + a₂ : ℝ) : EReal)
    refine (iInf_le _ x₂).trans ?_
    rw [add_sub_cancel_right]
    exact (infAddition_le_coe_iff _ _ _).2 ⟨a₁, a₂, h₁, h₂, rfl⟩

end EpigraphSums

/-! ## Exercise 1.29 -/

section Calculus

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- **Exercise 1.29(a)**: `δ_{C+D} = δ_C □ δ_D`. -/
theorem indicatorVA_add_eq_infEpiSum (C D : Set E) :
    indicatorVA (C + D) = infEpiSum (indicatorVA C) (indicatorVA D) := by
  funext x
  by_cases hx : x ∈ C + D
  · obtain ⟨c, hc, d, hd, rfl⟩ := hx
    rw [indicatorVA_apply_mem (Set.add_mem_add hc hd)]
    refine le_antisymm (le_iInf fun w ↦ ?_) ((iInf_le _ d).trans ?_)
    · unfold infAddition
      split_ifs
      · exact le_top
      · exact add_nonneg (by unfold indicatorVA; split_ifs <;> simp)
          (by unfold indicatorVA; split_ifs <;> simp)
    · rw [add_sub_cancel_right, indicatorVA_apply_mem hc, indicatorVA_apply_mem hd,
        infAddition_zero]
  · rw [indicatorVA_apply_not_mem hx]
    refine (top_le_iff.1 (le_iInf fun w ↦ ?_)).symm
    have : x - w ∉ C ∨ w ∉ D := by
      by_contra h
      push_neg at h
      exact hx ⟨x - w, h.1, w, h.2, sub_add_cancel x w⟩
    rcases this with h | h
    · rw [infAddition, if_pos (Or.inl (indicatorVA_apply_not_mem h))]
    · rw [infAddition, if_pos (Or.inr (indicatorVA_apply_not_mem h))]

/-- **Exercise 1.29(a)**: `δ_{λC} = λ ⋆ δ_C` for `λ > 0`. -/
theorem indicatorVA_smul_eq_epiMultiplication {lam : ℝ} (hlam : 0 < lam) (C : Set E) :
    indicatorVA (lam • C) = epiMultiplication lam (indicatorVA C) := by
  funext x
  simp only [epiMultiplication, if_pos hlam]
  by_cases hx : lam⁻¹ • x ∈ C
  · rw [indicatorVA_apply_mem ((mem_smul_set_iff_inv_smul_mem₀ hlam.ne' _ _).2 hx),
      indicatorVA_apply_mem hx, mul_zero]
  · rw [indicatorVA_apply_not_mem (fun h ↦ hx ((mem_smul_set_iff_inv_smul_mem₀ hlam.ne' _ _).1 h)),
      indicatorVA_apply_not_mem hx, EReal.coe_mul_top_of_pos hlam]

/-- The distance function `d_C` of 1.20 and 1.29 as an extended-real function, with the
convention `d_∅ = ∞` (infimum over the empty set). -/
def distanceEReal (C : Set E) (x : E) : EReal := ⨅ c ∈ C, ((‖x - c‖ : ℝ) : EReal)

omit [NormedSpace ℝ E] in
theorem distanceEReal_eq_infDist {C : Set E} (hC : C.Nonempty) (x : E) :
    distanceEReal C x = infDist x C := by
  apply le_antisymm
  · refine ereal_le_coe_of_forall_pos fun ε hε ↦ ?_
    obtain ⟨c, hc, hdc⟩ := (infDist_lt_iff hC).1 (show infDist x C < infDist x C + ε by linarith)
    exact (biInf_le _ hc).trans (EReal.coe_le_coe_iff.2 (by rw [← dist_eq_norm]; exact hdc.le))
  · exact le_iInf₂ fun c hc ↦ EReal.coe_le_coe_iff.2
      (by rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hc)

omit [NormedSpace ℝ E] in
theorem distanceEReal_empty (x : E) : distanceEReal (∅ : Set E) x = ⊤ := by
  simp [distanceEReal]

omit [NormedSpace ℝ E] in
/-- **Exercise 1.29(b)**: `d_{C+D} = d_C □ d_D`. -/
theorem distanceEReal_add_eq_infEpiSum (C D : Set E) :
    distanceEReal (C + D) = infEpiSum (distanceEReal C) (distanceEReal D) := by
  funext x
  apply le_antisymm
  · refine le_iInf fun w ↦ ?_
    simp only [distanceEReal]
    rw [← iInf_prod_infAddition]
    refine le_iInf₂ fun p hp ↦ (biInf_le _ (Set.add_mem_add hp.1 hp.2)).trans ?_
    rw [infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _), ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    calc ‖x - (p.1 + p.2)‖ = ‖(x - w - p.1) + (w - p.2)‖ := by congr 1; abel
      _ ≤ ‖x - w - p.1‖ + ‖w - p.2‖ := norm_add_le _ _
  · simp only [distanceEReal]
    refine le_iInf₂ fun y hy ↦ ?_
    obtain ⟨c, hc, d, hd, rfl⟩ := hy
    refine (iInf_le _ (x - c)).trans ((infAddition_mono (biInf_le _ hc) (biInf_le _ hd)).trans ?_)
    rw [infAddition_eq_add_of_ne_bot (EReal.coe_ne_bot _) (EReal.coe_ne_bot _), ← EReal.coe_add,
      EReal.coe_le_coe_iff, show x - (x - c) - c = 0 by abel, norm_zero, zero_add,
      show x - c - d = x - (c + d) by abel]

/-- **Exercise 1.29(b)**: `d_{λC} = λ ⋆ d_C` for `λ > 0`. -/
theorem distanceEReal_smul_eq_epiMultiplication {lam : ℝ} (hlam : 0 < lam) (C : Set E) :
    distanceEReal (lam • C) = epiMultiplication lam (distanceEReal C) := by
  funext x
  simp only [epiMultiplication, if_pos hlam, distanceEReal]
  rw [← iInf_coe_mul_of_pos C _ hlam, ← Set.image_smul, iInf_image]
  refine iInf_congr fun c ↦ iInf_congr fun _ ↦ ?_
  rw [← EReal.coe_mul, EReal.coe_eq_coe_iff]
  have : x - lam • c = lam • (lam⁻¹ • x - c) := by
    rw [smul_sub, smul_inv_smul₀ hlam.ne']
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]

omit [NormedSpace ℝ E] in
/-- The quadratic inequality behind 1.29(c):
`(ab/(a+b))|w - x|² ≤ a|w - z|² + b|z - x|²`. -/
theorem quadratic_split_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w z x : E) :
    a * b / (a + b) * ‖w - x‖ ^ 2 ≤ a * ‖w - z‖ ^ 2 + b * ‖z - x‖ ^ 2 := by
  have hD : ‖w - x‖ ≤ ‖w - z‖ + ‖z - x‖ := norm_sub_le_norm_sub_add_norm_sub w z x
  have hD2 : ‖w - x‖ ^ 2 ≤ (‖w - z‖ + ‖z - x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hD2 (by positivity : (0 : ℝ) ≤ a * b),
    sq_nonneg (a * ‖w - z‖ - b * ‖z - x‖)]

/-- Equality holds in `quadratic_split_le` at `z = (a w + b x)/(a + b)`. -/
theorem quadratic_split_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w x : E) :
    a * ‖w - (a + b)⁻¹ • (a • w + b • x)‖ ^ 2 + b * ‖(a + b)⁻¹ • (a • w + b • x) - x‖ ^ 2 =
      a * b / (a + b) * ‖w - x‖ ^ 2 := by
  have hab : 0 < a + b := by positivity
  have h1 : w - (a + b)⁻¹ • (a • w + b • x) = (b / (a + b)) • (w - x) := by
    match_scalars
    · field_simp; ring
    · field_simp
  have h2 : (a + b)⁻¹ • (a • w + b • x) - x = (a / (a + b)) • (w - x) := by
    match_scalars
    · field_simp
    · field_simp; ring
  rw [h1, h2, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < b / (a + b)), abs_of_pos (by positivity : 0 < a / (a + b))]
  field_simp
  ring

/-- **Exercise 1.29(c)**: `e_{λ₁+λ₂} f = e_{λ₁}(e_{λ₂} f)` for `λ₁ > 0`, `λ₂ > 0`, and any `f`. -/
theorem moreauEnvelopeEReal_moreauEnvelopeEReal (f : E → EReal) {l₁ l₂ : ℝ} (h₁ : 0 < l₁)
    (h₂ : 0 < l₂) :
    moreauEnvelopeEReal (moreauEnvelopeEReal f l₂) l₁ = moreauEnvelopeEReal f (l₁ + l₂) := by
  funext x
  have ha : 0 < 1 / (2 * l₂) := by positivity
  have hb : 0 < 1 / (2 * l₁) := by positivity
  have hab : 1 / (2 * l₂) * (1 / (2 * l₁)) / (1 / (2 * l₂) + 1 / (2 * l₁)) =
      1 / (2 * (l₁ + l₂)) := by
    field_simp
  simp only [moreauEnvelopeEReal]
  simp_rw [iInf_add_coe]
  rw [iInf_comm]
  refine iInf_congr fun w ↦ le_antisymm ?_ (le_iInf fun z ↦ ?_)
  · refine (iInf_le _ ((1 / (2 * l₂) + 1 / (2 * l₁))⁻¹ •
      ((1 / (2 * l₂)) • w + (1 / (2 * l₁)) • x))).trans (le_of_eq ?_)
    rw [add_assoc, ← EReal.coe_add, quadratic_split_eq ha hb, hab]
  · rw [add_assoc, ← EReal.coe_add]
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.2 ?_)
    have := quadratic_split_le ha hb w z x
    rwa [hab] at this

end Calculus

/-! ## Example 1.30 -/

section VecMaxLogExp

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **Example 1.30**, estimate 1(16): `ε logexp − ε log n ≤ vecmax ≤ ε logexp` for every `ε > 0`,
where `(ε logexp)(x) = ε logexp(x/ε)` is the epi-multiple of `logexp` (`logSumExp`, Chapter 11)
and `vecmax` is `vecMax` (Chapter 8). -/
theorem vecMax_logSumExp_bounds {ε : ℝ} (hε : 0 < ε) (x : EuclideanSpace ℝ ι) :
    ε * logSumExp (ε⁻¹ • x) - ε * Real.log (Fintype.card ι) ≤ vecMax x ∧
      vecMax x ≤ ε * logSumExp (ε⁻¹ • x) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) fun i ↦ x i
  have hμ : vecMax x = x j := hj
  have hle : ∀ i, x i ≤ vecMax x := fun i ↦ le_finiteMax (fun i (x : EuclideanSpace ℝ ι) ↦ x i) x i
  set S := ∑ i, Real.exp ((ε⁻¹ • x) i) with hS
  have hSi : ∀ i, Real.exp ((ε⁻¹ • x) i) = Real.exp (ε⁻¹ * x i) := fun i ↦ by
    simp [PiLp.smul_apply, smul_eq_mul]
  have hlow : Real.exp (ε⁻¹ * vecMax x) ≤ S := by
    rw [hμ, ← hSi j]
    exact Finset.single_le_sum (fun i _ ↦ (Real.exp_pos _).le) (Finset.mem_univ j)
  have hup : S ≤ (Fintype.card ι : ℝ) * Real.exp (ε⁻¹ * vecMax x) := by
    rw [← Finset.card_univ, ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ ?_
    rw [hSi]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hle i) (inv_nonneg.2 hε.le))
  have hSpos : 0 < S := lt_of_lt_of_le (Real.exp_pos _) hlow
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hlog1 : ε⁻¹ * vecMax x ≤ Real.log S := by
    rw [← Real.log_exp (ε⁻¹ * vecMax x)]
    exact Real.log_le_log (Real.exp_pos _) hlow
  have hlog2 : Real.log S ≤ Real.log (Fintype.card ι) + ε⁻¹ * vecMax x := by
    rw [← Real.log_exp (ε⁻¹ * vecMax x), ← Real.log_mul hn.ne' (Real.exp_pos _).ne']
    exact Real.log_le_log hSpos hup
  have hlse : logSumExp (ε⁻¹ • x) = Real.log S := rfl
  rw [hlse]
  constructor
  · have := mul_le_mul_of_nonneg_left hlog2 hε.le
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at this
    linarith
  · have := mul_le_mul_of_nonneg_left hlog1 hε.le
    rwa [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at this

/-- **Example 1.30**: `ε logexp` converges uniformly to `vecmax` as `ε ↘ 0`. -/
theorem tendstoUniformly_logSumExp_vecMax :
    TendstoUniformly (fun ε (x : EuclideanSpace ℝ ι) ↦ ε * logSumExp (ε⁻¹ • x)) vecMax
      (𝓝[>] 0) := by
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  have hn : 0 ≤ Real.log (Fintype.card ι) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε * (Real.log (Fintype.card ι) + 1) < δ := by
    have hc : Tendsto (fun ε : ℝ ↦ ε * (Real.log (Fintype.card ι) + 1)) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ ↦ ε * (Real.log (Fintype.card ι) + 1)) (𝓝 0)
          (𝓝 (0 * (Real.log (Fintype.card ι) + 1))) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    exact eventually_mem_nhdsWithin.and (hc.eventually (gt_mem_nhds hδ))
  filter_upwards [hev] with ε ⟨hε, hεδ⟩ x
  obtain ⟨h1, h2⟩ := vecMax_logSumExp_bounds hε x
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
  nlinarith

/-- **Example 1.30**: for `F = (f₁, …, f_m)`, the smooth functions
`f_ε(x) = ε log (e^{f₁(x)/ε} + ⋯ + e^{f_m(x)/ε})` approximate `max {f₁(x), …, f_m(x)}` uniformly
as `ε ↘ 0`. -/
theorem tendstoUniformly_logSumExp_comp {β : Type*} (F : β → EuclideanSpace ℝ ι) :
    TendstoUniformly (fun ε x ↦ ε * logSumExp (ε⁻¹ • F x)) (fun x ↦ vecMax (F x)) (𝓝[>] 0) :=
  (tendstoUniformly_logSumExp_vecMax (ι := ι)).comp F

/-- **Example 1.30**: `f_ε` is as smooth as the `fᵢ`. -/
theorem contDiff_logSumExp_comp {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {n : WithTop ℕ∞} {F : β → EuclideanSpace ℝ ι} (hF : ∀ i, ContDiff ℝ n (fun x ↦ F x i))
    (ε : ℝ) : ContDiff ℝ n (fun x ↦ ε * logSumExp (ε⁻¹ • F x)) := by
  have hsum : ContDiff ℝ n (fun x ↦ ∑ i, Real.exp (ε⁻¹ * F x i)) :=
    ContDiff.sum fun i _ ↦ (contDiff_const.mul (hF i)).exp
  have hpos : ∀ x, ∑ i, Real.exp (ε⁻¹ * F x i) ≠ 0 := fun x ↦
    (Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty).ne'
  have heq : (fun x ↦ ε * logSumExp (ε⁻¹ • F x)) =
      fun x ↦ ε * Real.log (∑ i, Real.exp (ε⁻¹ * F x i)) := by
    funext x
    simp [logSumExp, PiLp.smul_apply, smul_eq_mul]
  rw [heq]
  exact contDiff_const.mul (hsum.log hpos)

end VecMaxLogExp

/-! ## Exercise 1.31 and Proposition 1.32 -/

section EpiComposition

variable {G : Type*}

/-- Epi-composition, formula 1(17): `(F ▷ f)(u) = inf {f(x) | F(x) = u}`. -/
def epiComposite (F : E → G) (f : E → EReal) (u : G) : EReal := ⨅ (x : E) (_ : F x = u), f x

theorem epiComposite_le (F : E → G) (f : E → EReal) (x : E) : epiComposite F f (F x) ≤ f x :=
  iInf₂_le (f := fun y (_ : F y = F x) ↦ f y) x rfl

/-- **Exercise 1.31**, regardless of attainment:
`{(u, α) | (F ▷ f)(u) < α} = {(F(x), α) | f(x) < α}`. -/
theorem setOf_epiComposite_lt_eq_image (F : E → G) (f : E → EReal) :
    {p : G × ℝ | epiComposite F f p.1 < p.2} =
      (fun p : E × ℝ ↦ (F p.1, p.2)) '' {p : E × ℝ | f p.1 < p.2} := by
  ext ⟨u, a⟩
  simp only [mem_setOf_eq, mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := iInf_lt_iff.1 h
    obtain ⟨hxu, hxa⟩ := iInf_lt_iff.1 hx
    exact ⟨x, a, hxa, hxu, rfl⟩
  · rintro ⟨x, b, hxb, rfl, rfl⟩
    exact lt_of_le_of_lt (epiComposite_le F f x) hxb

/-- **Exercise 1.31**: `epi (F ▷ f) = {(F(x), α) | (x, α) ∈ epi f}` as long as the infimum defining
`(F ▷ f)(u)` is attained when finite. -/
theorem epigraph_epiComposite_of_attained {F : E → G} {f : E → EReal}
    (h : ∀ u, (∃ r : ℝ, epiComposite F f u = r) → ∃ x, F x = u ∧ f x = epiComposite F f u) :
    epigraph (epiComposite F f) = (fun p : E × ℝ ↦ (F p.1, p.2)) '' epigraph f := by
  apply subset_antisymm
  · rintro ⟨u, a⟩ hua
    have hle : epiComposite F f u ≤ a := hua
    induction hv : epiComposite F f u using EReal.rec with
    | bot =>
      have hstrict : (u, a) ∈ {p : G × ℝ | epiComposite F f p.1 < p.2} := by
        change epiComposite F f u < (a : EReal)
        rw [hv]; exact EReal.bot_lt_coe _
      rw [setOf_epiComposite_lt_eq_image] at hstrict
      obtain ⟨⟨x, b⟩, hxb, heq⟩ := hstrict
      exact ⟨(x, b), (mem_epigraph_iff _ _ _).2 (le_of_lt hxb), heq⟩
    | top =>
      rw [hv] at hle
      exact absurd hle (by simp)
    | coe r =>
      obtain ⟨x, hxu, hx⟩ := h u ⟨r, hv⟩
      exact ⟨(x, a), (mem_epigraph_iff _ _ _).2 (hx ▸ hle), by simp [hxu]⟩
  · rintro _ ⟨⟨x, a⟩, hxa, rfl⟩
    exact (epiComposite_le F f x).trans hxa

/-- The parametric integrand `f̄(x, u) = f(x)` if `F(x) = u`, `∞` otherwise, of the proof of
Proposition 1.32. -/
def epiCompositeIntegrand (F : E → G) (f : E → EReal) (q : E × G) : EReal :=
  by classical exact if F q.1 = q.2 then f q.1 else ⊤

theorem valueFunction_epiCompositeIntegrand (F : E → G) (f : E → EReal) :
    valueFunction (epiCompositeIntegrand F f) = epiComposite F f := by
  classical
  funext u
  simp only [valueFunction, epiComposite, epiCompositeIntegrand]
  refine iInf_congr fun x ↦ ?_
  by_cases hx : F x = u
  · simp [hx]
  · simp [hx]

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Proposition 1.32** (properties of epi-composition): for `f` proper and lsc, `F` continuous,
and each `{x | f(x) ≤ α, F(x) ∈ IB(u, ε)}` bounded for some `ε > 0`, the epi-composite `F ▷ f` is
proper and lsc, and the infimum defining `(F ▷ f)(u)` is attained whenever it is finite. -/
theorem epiComposite_properties {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    {F : E → G} (hF : Continuous F)
    (hb : ∀ (a : ℝ) (u : G), ∃ ε > 0, IsBounded {x | f x ≤ a ∧ F x ∈ closedBall u ε}) :
    IsProper (epiComposite F f) ∧ LowerSemicontinuous (epiComposite F f) ∧
      ∀ u, (∃ r : ℝ, epiComposite F f u = r) → ∃ x, F x = u ∧ f x = epiComposite F f u := by
  classical
  set g := epiCompositeIntegrand F f with hgdef
  have hgeq : ∀ q : E × G, g q = if F q.1 = q.2 then f q.1 else ⊤ := fun q ↦ rfl
  have hglsc : LowerSemicontinuous g := by
    refine lowerSemicontinuous_iff_isClosed_levelSet.2 fun a ↦ ?_
    have heq : levelSet g a = {q : E × G | F q.1 = q.2} ∩ Prod.fst ⁻¹' levelSet f a := by
      ext q
      simp only [levelSet, mem_setOf_eq, mem_inter_iff, mem_preimage, hgeq]
      by_cases hq : F q.1 = q.2
      · simp [hq]
      · simp [hq]
    rw [heq]
    exact (isClosed_eq (hF.comp continuous_fst) continuous_snd).inter
      ((lowerSemicontinuous_iff_isClosed_levelSet.1 hl a).preimage continuous_fst)
  have hgp : IsProper g := by
    obtain ⟨x, hx⟩ := hp.1
    refine ⟨⟨(x, F x), by rw [hgeq, if_pos rfl]; exact hx⟩, fun q ↦ ?_⟩
    rw [hgeq]
    split_ifs
    · exact hp.2 _
    · exact bot_lt_top
  have hgb : IsLevelBoundedInXLocallyUniformly g := by
    intro u a
    obtain ⟨ε, hε, hS⟩ := hb a u
    refine ⟨ε, hε, (hS.prod (isBounded_closedBall (x := u) (r := ε))).subset ?_⟩
    rintro ⟨x, v⟩ ⟨⟨-, hv⟩, hlev⟩
    have hlev' : g (x, v) ≤ a := hlev
    rw [hgeq] at hlev'
    by_cases hxv : F x = v
    · rw [if_pos hxv] at hlev'
      exact ⟨⟨hlev', hxv ▸ hv⟩, hv⟩
    · rw [if_neg hxv] at hlev'
      exact absurd hlev' (by simp)
  obtain ⟨hpp, hpl, hP, -⟩ := parametric_minimization_a hglsc hgp hgb
  rw [valueFunction_epiCompositeIntegrand] at hpp hpl hP
  refine ⟨hpp, hpl, fun u ⟨r, hr⟩ ↦ ?_⟩
  obtain ⟨x, hx⟩ := (hP u (by rw [mem_effectiveDomain_iff, hr]; exact EReal.coe_lt_top r)).1
  have hx' := (mem_paramArgmin_iff g u x).1 hx
  rw [valueFunction_epiCompositeIntegrand, hgeq] at hx'
  by_cases hxu : F x = u
  · rw [if_pos hxu] at hx'
    exact ⟨x, hxu, hx'.1⟩
  · rw [if_neg hxu] at hx'
    exact absurd hx'.1.symm (ne_of_lt hx'.2)

end EpiComposition

end RW
