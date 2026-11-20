/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Finite sum subgradient rules
-/

import RockafellarWets.Chapter10.FiniteSeparableSubgradients
import RockafellarWets.Chapter10.BasicChainSubderivatives
import RockafellarWets.Chapter6.SetAdditionCones

open Set
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : ι → E → EReal} {x : E} {c : ι → ℝ}

/-- The diagonal embedding is the adjoint of coordinate addition. -/
def finiteDiagonal : E →L[ℝ] PiLp 2 (fun _ : ι ↦ E) := l2PiSum.adjoint

@[simp] theorem finiteDiagonal_apply (x : E) :
    finiteDiagonal (ι := ι) x = WithLp.toLp 2 (fun _ ↦ x) := l2PiSum_adjoint_apply x

@[simp] theorem finiteDiagonal_adjoint :
    (finiteDiagonal (ι := ι) (E := E)).adjoint = l2PiSum := ContinuousLinearMap.adjoint_adjoint _

theorem finiteSum_horizon_qualification (hp : ∀ i, IsProper (f i))
    (hf : ∀ i, LowerSemicontinuous (f i)) (hx : ∀ i, f i x = c i)
    (hQ : ∀ v : ι → E, (∀ i, v i ∈ horizonSubdifferential (f i) x) →
      ∑ i, v i = 0 → ∀ i, v i = 0) :
    ∀ q ∈ horizonSubdifferential (separablePi f) (finiteDiagonal x),
      (fderiv ℝ (finiteDiagonal (ι := ι)) x).adjoint q = 0 → q = 0 := by
  intro q hq he
  have hm := horizonSubdifferential_separablePi_subset f hp hf (finiteDiagonal x) c
    (by simpa using hx) hq
  rw [ContinuousLinearMap.fderiv,finiteDiagonal_adjoint,l2PiSum_apply] at he
  have hz := hQ (fun i ↦ q i) (by simpa only [finiteDiagonal_apply] using hm) he
  apply WithLp.ofLp_injective
  funext i
  exact hz i

/-- **Corollary 10.9**, regular subgradients of any finite sum. -/
theorem regularSubdifferential_finiteSum_superset (hx : ∀ i, f i x = c i) :
    finiteSetSum (fun i ↦ regularSubdifferential (f i) x) ⊆
      regularSubdifferential (fun z ↦ ∑ i, f i z) x := by
  rw [finiteSetSum_eq_l2PiSum_image]
  have he : l2PiSet (fun i ↦ regularSubdifferential (f i) x) =
      regularSubdifferential (separablePi f) (finiteDiagonal x) := by
    ext q
    simpa only [mem_l2PiSet,finiteDiagonal_apply] using (mem_regularSubdifferential_separablePi_iff f (finiteDiagonal x) q c (by simpa using hx)).symm
  rw [he,← finiteDiagonal_adjoint]
  have hh := adjoint_regularSubdifferential_subset_comp (finiteDiagonal (ι := ι) (E := E)).hasFDerivAt
    (separablePi_eq_coe (x := finiteDiagonal x) (by simpa using hx))
  simpa only [Function.comp_def,separablePi,finiteDiagonal_apply] using hh

/-- **Corollary 10.9**, limiting subgradients of any finite sum under its
horizon-vector qualification. -/
theorem subdifferential_finiteSum_subset (hp : ∀ i, IsProper (f i))
    (hf : ∀ i, LowerSemicontinuous (f i)) (hx : ∀ i, f i x = c i)
    (hQ : ∀ v : ι → E, (∀ i, v i ∈ horizonSubdifferential (f i) x) →
      ∑ i, v i = 0 → ∀ i, v i = 0) :
    subdifferential (fun z ↦ ∑ i, f i z) x ⊆ finiteSetSum (fun i ↦ subdifferential (f i) x) := by
  have hh := subdifferential_comp_subset (G := finiteDiagonal (ι := ι)) (x := x)
    (finiteDiagonal (ι := ι) (E := E)).contDiff
    (lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2))
    (separablePi_eq_coe (x := finiteDiagonal x) (by simpa using hx)) (finiteSum_horizon_qualification hp hf hx hQ)
  have he : subdifferential (separablePi f) (finiteDiagonal x) =
      l2PiSet (fun i ↦ subdifferential (f i) x) := by
    ext q
    simpa only [mem_l2PiSet,finiteDiagonal_apply] using mem_subdifferential_separablePi_iff f hp hf (finiteDiagonal x) q c (by simpa using hx)
  rw [ContinuousLinearMap.fderiv,finiteDiagonal_adjoint,he,← finiteSetSum_eq_l2PiSum_image] at hh
  simpa only [Function.comp_def,separablePi,finiteDiagonal_apply] using hh

/-- **Corollary 10.9**, horizon subgradients of any finite sum. -/
theorem horizonSubdifferential_finiteSum_subset (hp : ∀ i, IsProper (f i))
    (hf : ∀ i, LowerSemicontinuous (f i)) (hx : ∀ i, f i x = c i)
    (hQ : ∀ v : ι → E, (∀ i, v i ∈ horizonSubdifferential (f i) x) →
      ∑ i, v i = 0 → ∀ i, v i = 0) :
    horizonSubdifferential (fun z ↦ ∑ i, f i z) x ⊆
      finiteSetSum (fun i ↦ horizonSubdifferential (f i) x) := by
  have hh := horizonSubdifferential_comp_subset (G := finiteDiagonal (ι := ι)) (x := x)
    (finiteDiagonal (ι := ι) (E := E)).contDiff
    (lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2))
    (separablePi_eq_coe (x := finiteDiagonal x) (by simpa using hx)) (finiteSum_horizon_qualification hp hf hx hQ)
  rw [ContinuousLinearMap.fderiv,finiteDiagonal_adjoint] at hh
  have hs := hh.trans (image_mono (horizonSubdifferential_separablePi_subset f hp hf
    (finiteDiagonal x) c (by simpa using hx)))
  simp only [finiteDiagonal_apply] at hs
  change horizonSubdifferential (separablePi f ∘ ⇑finiteDiagonal) x ⊆
    l2PiSum '' l2PiSet (fun i ↦ horizonSubdifferential (f i) x) at hs
  rw [← finiteSetSum_eq_l2PiSum_image] at hs
  simpa only [Function.comp_def,separablePi,finiteDiagonal_apply] using hs

end
end RW
