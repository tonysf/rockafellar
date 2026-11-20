/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite sum subderivatives and corrected regularity
-/

import RockafellarWets.Chapter10.FiniteSumSubgradients
import RockafellarWets.Chapter10.FiniteSeparableRegularity
import RockafellarWets.Chapter10.FiniteInfAdditionProper

open Set
open scoped InnerProductSpace

namespace RW

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : ι → E → EReal} {x : E} {c : ι → ℝ}

/-- The regular-subderivative upper bound with the book's inf-addition
convention. No calmness assumption is needed for this inequality. -/
theorem regularSubderivative_separablePi_le_finiteInfAddition
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x w : PiLp 2 (fun _ : ι ↦ E)) (c : ι → ℝ) (hx : ∀ i, f i (x i) = c i) :
    regularSubderivative (separablePi f) x w ≤
      finiteInfAddition (fun i ↦ regularSubderivative (f i) (x i) (w i)) := by
  apply le_iInf
  intro r
  have hxi := separablePi_eq_coe hx
  apply (regularSubderivative_le_coe_iff_support_polar hxi
    (locallyLscAt_of_lowerSemicontinuous_finite
      (lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2)) hxi)).mpr
  have hi (i : ι) := (regularSubderivative_le_coe_iff_support_polar (hx i)
    (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hx i))).mp (r.2 i)
  constructor
  · apply (supportFunction_le_iff _ _ _).mpr
    intro v hv
    have hvi := (mem_subdifferential_separablePi_iff f hp hf x v c hx).mp hv
    apply EReal.coe_le_coe_iff.mpr
    rw [l2Pi_inner_apply]
    exact Finset.sum_le_sum (fun i _ ↦ EReal.coe_le_coe_iff.mp ((supportFunction_le_iff _ _ _).mp (hi i).1 _ (hvi i)))
  · intro v hv
    have hvi := horizonSubdifferential_separablePi_subset f hp hf x c hx hv
    rw [l2Pi_inner_apply]
    exact Finset.sum_nonpos (fun i _ ↦ (hi i).2 _ (hvi i))

/-- The unconditional lower bound uses the ordinary `EReal` addition,
which resolves mixed infinite values downward. -/
theorem subderivative_finiteSum_ge (hx : ∀ i, f i x = c i) (w : E) :
    (∑ i, subderivative (f i) x w) ≤ subderivative (fun z ↦ ∑ i, f i z) x w := by
  have h1 := subderivative_separablePi_ge f (finiteDiagonal x) (finiteDiagonal w) c (by simpa using hx)
  have h2 := subderivative_comp_ge (finiteDiagonal (ι := ι) (E := E)).hasFDerivAt
    (separablePi_eq_coe (x := finiteDiagonal x) (by simpa using hx)) w
  simpa only [finiteDiagonal_apply,Function.comp_def,separablePi] using h1.trans h2

/-- **Corollary 10.9**, the qualified upper bound, including mixed infinite
component derivatives via finite inf-addition. -/
theorem regularSubderivative_finiteSum_le_finiteInfAddition
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hx : ∀ i, f i x = c i)
    (hQ : ∀ v : ι → E, (∀ i, v i ∈ horizonSubdifferential (f i) x) →
      ∑ i, v i = 0 → ∀ i, v i = 0) (w : E) :
    regularSubderivative (fun z ↦ ∑ i, f i z) x w ≤
      finiteInfAddition (fun i ↦ regularSubderivative (f i) x w) := by
  have hval := separablePi_eq_coe (x := finiteDiagonal x) (by simpa using hx)
  have hl : LowerSemicontinuous (fun z ↦ ∑ i, f i z) := by
    simpa only [Function.comp_def,separablePi,finiteDiagonal_apply] using
      (lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2)).comp (finiteDiagonal (ι := ι) (E := E)).continuous
  have hxsum : (∑ i, f i x) = ((∑ i, c i:ℝ):EReal) := by simpa only [separablePi,finiteDiagonal_apply] using hval
  apply le_iInf
  intro r
  apply (regularSubderivative_le_coe_iff_support_polar (f := fun z : E ↦ ∑ i, f i z) (x := x) hxsum
    (locallyLscAt_of_lowerSemicontinuous_finite (g := fun z : E ↦ ∑ i, f i z) (z := x) hl hxsum)).mpr
  have hi (i : ι) := (regularSubderivative_le_coe_iff_support_polar (hx i)
    (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (hx i))).mp (r.2 i)
  constructor
  · apply (supportFunction_le_iff _ _ _).mpr
    intro v hv
    obtain ⟨u,hu,rfl⟩ := subdifferential_finiteSum_subset hp hf hx hQ hv
    apply EReal.coe_le_coe_iff.mpr
    rw [sum_inner]
    exact Finset.sum_le_sum (fun i _ ↦ EReal.coe_le_coe_iff.mp ((supportFunction_le_iff _ _ _).mp (hi i).1 _ (hu i)))
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := horizonSubdifferential_finiteSum_subset hp hf hx hQ hv
    rw [inner_sum]
    exact Finset.sum_nonpos (fun i _ ↦ (hi i).2 _ (hu i))

/-- The exact limiting subgradient formula only needs regularity of the
summands; it does not assert regularity of their sum. -/
theorem subdifferential_finiteSum_eq_of_regular
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hr : ∀ i, IsSubdifferentiallyRegularAt (f i) x)
    (hQ : ∀ v : ι → E, (∀ i, v i ∈ horizonSubdifferential (f i) x) →
      ∑ i, v i = 0 → ∀ i, v i = 0) :
    subdifferential (fun z ↦ ∑ i, f i z) x = finiteSetSum (fun i ↦ subdifferential (f i) x) := by
  have hx (i : ι) : f i x = ((f i x).toReal:EReal) := (EReal.coe_toReal (hr i).2.1 (hr i).1).symm
  apply Subset.antisymm (subdifferential_finiteSum_subset hp hf hx hQ)
  simp_rw [(hr _).subdifferential_eq_regularSubdifferential]
  exact (regularSubdifferential_finiteSum_superset hx).trans (regularSubdifferential_subset_subdifferential _ _)

/-- Corrected regularity and exact directional formula in **Corollary 10.9**:
retain the zero-direction assumptions from Proposition 10.5. -/
theorem finiteSum_regularity_of_calm
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hr : ∀ i, IsSubdifferentiallyRegularAt (f i) x) (h0 : ∀ i, subderivative (f i) x 0 = 0)
    (hQ : ∀ v : ι → E, (∀ i, v i ∈ horizonSubdifferential (f i) x) →
      ∑ i, v i = 0 → ∀ i, v i = 0) :
    IsSubdifferentiallyRegularAt (fun z ↦ ∑ i, f i z) x ∧
      ∀ w, subderivative (fun z ↦ ∑ i, f i z) x w = ∑ i, subderivative (f i) x w := by
  have hx (i : ι) : f i x = ((f i x).toReal:EReal) := (EReal.coe_toReal (hr i).2.1 (hr i).1).symm
  have hval : (∑ i, f i x) = ((∑ i, (f i x).toReal:ℝ):EReal) := by
    simpa only [separablePi,finiteDiagonal_apply] using separablePi_eq_coe (x := finiteDiagonal x) (by simpa using hx)
  have hl : LowerSemicontinuous (fun z ↦ ∑ i, f i z) := by
    simpa only [Function.comp_def,separablePi,finiteDiagonal_apply] using
      (lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2)).comp (finiteDiagonal (ι := ι) (E := E)).continuous
  have hu (w : E) : regularSubderivative (fun z ↦ ∑ i, f i z) x w ≤ ∑ i, subderivative (f i) x w := by
    have hh := regularSubderivative_finiteSum_le_finiteInfAddition hp hf hx hQ w
    have hei (i : ι) := (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mp (hr i)).2
    simp_rw [← hei] at hh
    rwa [finiteInfAddition_eq_sum_of_ne_bot _ (fun i ↦ ((hr i).isProper_subderivative (by rw [h0 i]; norm_num)).2 w |>.ne')] at hh
  have he : subderivative (fun z ↦ ∑ i, f i z) x = regularSubderivative (fun z ↦ ∑ i, f i z) x := by
    funext w
    exact le_antisymm (subderivative_le_regularSubderivative (f := fun z : E ↦ ∑ i, f i z) (x := x) hval w) ((hu w).trans (subderivative_finiteSum_ge hx w))
  exact ⟨isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mpr
    ⟨locallyLscAt_of_lowerSemicontinuous_finite (g := fun z : E ↦ ∑ i, f i z) (z := x) hl hval,he⟩,fun w ↦ le_antisymm
      ((subderivative_le_regularSubderivative (f := fun z : E ↦ ∑ i, f i z) (x := x) hval w).trans (hu w)) (subderivative_finiteSum_ge hx w)⟩

/-- The horizon equality under the same corrected calmness hypotheses. -/
theorem horizonSubdifferential_finiteSum_eq_of_regular_calm
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hr : ∀ i, IsSubdifferentiallyRegularAt (f i) x) (h0 : ∀ i, subderivative (f i) x 0 = 0)
    (hQ : ∀ v : ι → E, (∀ i, v i ∈ horizonSubdifferential (f i) x) →
      ∑ i, v i = 0 → ∀ i, v i = 0) :
    horizonSubdifferential (fun z ↦ ∑ i, f i z) x =
      finiteSetSum (fun i ↦ horizonSubdifferential (f i) x) := by
  have hx (i : ι) : f i x = ((f i x).toReal:EReal) := (EReal.coe_toReal (hr i).2.1 (hr i).1).symm
  have hrsep := (separablePi_regularity f hp hf (finiteDiagonal x)
    (by simpa using hr) (by simpa using h0)).1
  have he := horizonSubdifferential_comp_eq_of_regular (G := finiteDiagonal (ι := ι)) (x := x)
    (finiteDiagonal (ι := ι) (E := E)).contDiff
    (lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2)) hrsep
    (finiteSum_horizon_qualification hp hf hx hQ)
  rw [ContinuousLinearMap.fderiv,finiteDiagonal_adjoint,
    horizonSubdifferential_separablePi_eq_of_regular f hp hf (finiteDiagonal x)
      (by simpa using hr) (by simpa using h0)] at he
  simp only [finiteDiagonal_apply] at he
  change horizonSubdifferential (separablePi f ∘ finiteDiagonal) x =
    l2PiSum '' l2PiSet (fun i ↦ horizonSubdifferential (f i) x) at he
  rw [← finiteSetSum_eq_l2PiSum_image] at he
  simpa only [Function.comp_def,separablePi,finiteDiagonal_apply] using he

end RW
