/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The finite epi-sum as a parametric minimum

The decomposition constraint is included explicitly. In the subsequent
subgradient formulas each decomposition contributes an intersection of the
component subdifferentials, correcting the unions printed in Exercise 10.18.
-/

import RockafellarWets.Chapter10.FiniteSeparableSubgradients
import RockafellarWets.Chapter10.FiniteInfAdditionProper
import RockafellarWets.Chapter10.PerturbedCompositeObjectives
import RockafellarWets.Chapter10.ConvexParametricSubgradients

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Sum of the coordinates of a Euclidean product. -/
def l2CoordinateSum : PiLp 2 (fun _ : ι ↦ E) →L[ℝ] E := ∑ i, PiLp.proj 2 (fun _ : ι ↦ E) i

@[simp] theorem l2CoordinateSum_apply (x : PiLp 2 (fun _ : ι ↦ E)) :
    l2CoordinateSum x = ∑ i, x i := by simp [l2CoordinateSum]

@[simp] theorem l2CoordinateSum_adjoint (v : E) :
    (l2CoordinateSum (ι := ι)).adjoint v = WithLp.toLp 2 (fun _ : ι ↦ v) := by
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left,l2CoordinateSum_apply,inner_sum]
  simp [l2Pi_inner_apply]

theorem separablePi_finite_components {f : ι → E → EReal} {x : PiLp 2 (fun _ : ι ↦ E)}
    {a : ℝ} (ha : separablePi f x = a) : ∃ c : ι → ℝ, ∀ i, f i (x i) = c i := by
  classical
  have h (i : ι) : ∃ c : ℝ, f i (x i) = c := by
    have he : f i (x i)+(∑ j ∈ Finset.univ.erase i, f j (x j)) = (a:EReal) := by
      rw [Finset.add_sum_erase (Finset.univ) (fun j ↦ f j (x j)) (Finset.mem_univ i)]
      exact ha
    obtain ⟨c,d,hc,_⟩ := exists_coe_components_of_add_eq_coe he
    exact ⟨c,hc⟩
  exact Classical.axiomOfChoice h

/-- The extended-real objective enforcing that the coordinates add to u. -/
def finiteEpiSumIntegrand (f : ι → E → EReal) : WithLp 2 (PiLp 2 (fun _ : ι ↦ E) × E) → EReal :=
  separableSum (separablePi f) (indicatorVA ({0} : Set E)) ∘
    parameterShift (-(l2CoordinateSum (ι := ι) (E := E)))

/-- Finite epi-addition. -/
def finiteEpiSumValue (f : ι → E → EReal) : E → EReal := parametricValue (finiteEpiSumIntegrand f)

/-- The optimal decomposition set includes its sum constraint. -/
def epiSumDecompositions (f : ι → E → EReal) (x : E) : Set (PiLp 2 (fun _ : ι ↦ E)) :=
  {a | (∑ i, a i) = x ∧ separablePi f a = finiteEpiSumValue f x ∧ finiteEpiSumValue f x < ⊤}

/-- The boundedness assumption of Exercise 10.18. -/
def HasBoundedEpiSumDecompositions (f : ι → E → EReal) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → Bornology.IsBounded
    {a : PiLp 2 (fun _ : ι ↦ E) | ‖∑ i, a i‖ ≤ ρ ∧ separablePi f a ≤ (ρ:EReal)}

theorem finiteEpiSumIntegrand_apply (f : ι → E → EReal)
    (a : PiLp 2 (fun _ : ι ↦ E)) (u : E) :
    finiteEpiSumIntegrand f (WithLp.toLp 2 (a,u)) =
      separablePi f a+indicatorVA ({0} : Set E) (u-∑ i, a i) := by
  simp only [finiteEpiSumIntegrand,Function.comp_apply,separableSum,parameterShift,
    WithLp.toLp_fst,WithLp.toLp_snd,Pi.neg_apply,l2CoordinateSum_apply]
  rw [neg_add_eq_sub]

theorem finiteEpiSumIntegrand_le_iff {f : ι → E → EReal} (hp : ∀ i, IsProper (f i))
    (a : PiLp 2 (fun _ : ι ↦ E)) (u : E) (r : ℝ) :
    finiteEpiSumIntegrand f (WithLp.toLp 2 (a,u)) ≤ r ↔
      (∑ i, a i) = u ∧ separablePi f a ≤ r := by
  rw [finiteEpiSumIntegrand_apply]
  by_cases h : (∑ i, a i) = u
  · simp [h]
  · have hz : u-∑ i, a i ∉ ({0} : Set E) := by simpa [sub_eq_zero] using Ne.symm h
    rw [indicatorVA_apply_not_mem hz,EReal.add_top_of_ne_bot (bot_lt_separablePi (fun i ↦ (hp i).2) a).ne']
    simp [h]

theorem lowerSemicontinuous_finiteEpiSumIntegrand {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (finiteEpiSumIntegrand f) :=
  (lowerSemicontinuous_separableSum (lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2))
    (lowerSemicontinuous_indicatorVA isClosed_singleton) (isProper_separablePi hp)
    ((indicatorVA_isProper_iff _).mpr (singleton_nonempty 0))).comp
      (contDiff_parameterShift (-(l2CoordinateSum (ι := ι) (E := E))).contDiff).continuous

theorem isProper_finiteEpiSumIntegrand {f : ι → E → EReal} (hp : ∀ i, IsProper (f i)) :
    IsProper (finiteEpiSumIntegrand f) := by
  have hps := isProper_separablePi hp
  constructor
  · obtain ⟨a,ha⟩ := hps.1
    refine ⟨WithLp.toLp 2 (a,∑ i, a i),?_⟩
    simpa [finiteEpiSumIntegrand_apply] using ha
  · intro q
    change ⊥ < separablePi f q.fst+indicatorVA ({0} : Set E) _
    exact EReal.bot_lt_add_iff.mpr ⟨hps.2 _,((indicatorVA_isProper_iff _).mpr (singleton_nonempty 0)).2 _⟩

theorem isParametricallyLevelBounded_finiteEpiSumIntegrand {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hb : HasBoundedEpiSumDecompositions f) :
    IsParametricallyLevelBounded (finiteEpiSumIntegrand f) := by
  intro u α
  let ρ : ℝ := max (‖u‖+1) α+1
  have hρ : 0 < ρ := by dsimp [ρ]; have := norm_nonneg u; linarith [le_max_left (‖u‖+1) α]
  refine ⟨1,by norm_num,(hb ρ hρ).prod (isBounded_closedBall (x := u) (r := (1:ℝ))) |>.subset ?_⟩
  rintro ⟨a,v⟩ hq
  have hqv : v ∈ closedBall u 1 := hq.1.2
  have hφ : finiteEpiSumIntegrand f (WithLp.toLp 2 (a,v)) ≤ (α:EReal) := hq.2
  obtain ⟨he,hs⟩ := (finiteEpiSumIntegrand_le_iff hp a v α).mp hφ
  refine ⟨⟨?_,hs.trans (EReal.coe_le_coe_iff.mpr ?_)⟩,hqv⟩
  · rw [he]
    have hv : ‖v‖ ≤ ‖u‖+1 := norm_le_of_mem_closedBall hqv
    dsimp [ρ]
    linarith [le_max_left (‖u‖+1) α]
  · dsimp [ρ]
    linarith [le_max_right (‖u‖+1) α]

theorem parametricMinimizers_finiteEpiSumIntegrand {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (u : E) :
    parametricMinimizers (finiteEpiSumIntegrand f) u = epiSumDecompositions f u := by
  ext a
  rw [mem_parametricMinimizers]
  constructor
  · rintro ⟨ha,hu⟩
    have hpu : finiteEpiSumValue f u ≠ ⊥ := by
      change parametricValue (finiteEpiSumIntegrand f) u ≠ ⊥
      rw [← ha]
      exact ((isProper_finiteEpiSumIntegrand hp).2 _).ne'
    have hc : finiteEpiSumValue f u = ((finiteEpiSumValue f u).toReal:EReal) := (EReal.coe_toReal hu.ne hpu).symm
    have hle := (finiteEpiSumIntegrand_le_iff hp a u _).mp (ha.trans hc).le
    refine ⟨hle.1,?_,hu⟩
    simpa [finiteEpiSumIntegrand_apply,hle.1] using ha
  · rintro ⟨he,ha,hu⟩
    refine ⟨?_,hu⟩
    simpa [finiteEpiSumIntegrand_apply,he] using ha

/-- The parametric representation agrees with Chapter 7's inf-addition
convention for proper summands. -/
theorem finiteEpiSumValue_eq_finiteEpiSum {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) : finiteEpiSumValue f = finiteEpiSum f := by
  funext u
  change (⨅ a : PiLp 2 (fun _ : ι ↦ E), finiteEpiSumIntegrand f (WithLp.toLp 2 (a,u))) =
    ⨅ z : {z : ι → E // ∑ i, z i = u}, finiteInfAddition (fun i ↦ f i (z.1 i))
  apply le_antisymm
  · apply le_iInf
    intro z
    apply iInf_le_of_le (WithLp.toLp 2 z.1)
    rw [finiteEpiSumIntegrand_apply,finiteInfAddition_eq_sum_of_ne_bot _ (fun i ↦ (hp i).2 (z.1 i) |>.ne')]
    simp [z.2,separablePi]
  · apply le_iInf
    intro a
    by_cases hs : (∑ i, a i) = u
    · apply iInf_le_of_le (⟨fun i ↦ a i,hs⟩ : {z : ι → E // ∑ i, z i = u})
      rw [finiteEpiSumIntegrand_apply,finiteInfAddition_eq_sum_of_ne_bot _ (fun i ↦ ((hp i).2 (a i)).ne')]
      simp [hs,separablePi]
    · rw [finiteEpiSumIntegrand_apply,indicatorVA_apply_not_mem (by simpa [sub_eq_zero] using Ne.symm hs),
        EReal.add_top_of_ne_bot (bot_lt_separablePi (fun i ↦ (hp i).2) a).ne']
      exact le_top

end

end RW
