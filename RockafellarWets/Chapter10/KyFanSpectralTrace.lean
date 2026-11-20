/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectral trace weights
-/
import RockafellarWets.Chapter10.KyFanVariational
import RockafellarWets.Chapter10.KyFanWeights

open Set
open scoped InnerProductSpace BigOperators

namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def spectralTraceWeights (k : ℕ)
    (e b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (j : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ i ∈ spectralInitialIndices (Module.finrank ℝ E) k, ⟪e j,b i⟫_ℝ ^ 2

theorem spectralTraceWeights_nonneg (k : ℕ)
    (e b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (j : Fin (Module.finrank ℝ E)) :
    0 ≤ spectralTraceWeights k e b j := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem spectralTraceWeights_le_one (k : ℕ)
    (e b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) (j : Fin (Module.finrank ℝ E)) :
    spectralTraceWeights k e b j ≤ 1 := by
  have h := b.orthonormal.sum_inner_products_le (x := e j)
    (s := spectralInitialIndices (Module.finrank ℝ E) k)
  simpa only [spectralTraceWeights,Real.norm_eq_abs,sq_abs,real_inner_comm (b _) (e j),
    e.orthonormal.norm_eq_one,one_pow] using h

theorem sum_spectralTraceWeights (k : ℕ)
    (e b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) :
    (∑ j, spectralTraceWeights k e b j) = (spectralInitialIndices (Module.finrank ℝ E) k).card := by
  unfold spectralTraceWeights
  rw [Finset.sum_comm]
  simp only [e.sum_sq_inner_right,b.orthonormal.norm_eq_one,one_pow,Finset.sum_const,
    nsmul_eq_mul,mul_one]

theorem inner_self_eq_spectral_sum (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (x : E) :
    ⟪x,A x⟫_ℝ = ∑ j, hA.eigenvalues rfl j * ⟪hA.eigenvectorBasis rfl j,x⟫_ℝ ^ 2 := by
  rw [← (hA.eigenvectorBasis rfl).repr.inner_map_map x (A x),PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  have ha : (hA.eigenvectorBasis rfl).repr (A x) j =
      hA.eigenvalues rfl j * (hA.eigenvectorBasis rfl).repr x j :=
    hA.eigenvectorBasis_apply_self_apply rfl x j
  rw [ha]
  simp [RCLike.inner_apply,OrthonormalBasis.repr_apply_apply,pow_two,mul_assoc]

theorem orthonormalPartialTrace_eq_weighted_eigenvalues (k : ℕ)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) :
    orthonormalPartialTrace k b A =
      ∑ j, hA.eigenvalues rfl j * spectralTraceWeights k (hA.eigenvectorBasis rfl) b j := by
  unfold orthonormalPartialTrace
  simp_rw [inner_self_eq_spectral_sum A hA]
  rw [Finset.sum_comm]
  simp only [spectralTraceWeights,Finset.mul_sum]

@[simp] theorem card_spectralInitialIndices {n k : ℕ} (hk : k ≤ n) :
    (spectralInitialIndices n k).card = k := by
  rcases lt_or_eq_of_le hk with h | rfl
  · have he : spectralInitialIndices n k = Finset.Iio (⟨k,h⟩ : Fin n) := by
      ext i
      simp [spectralInitialIndices,Fin.lt_def]
    rw [he,Fin.card_Iio]
  · simp [spectralInitialIndices,Fin.isLt]

theorem orthonormalPartialTrace_le_eigenvalue_sum {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) :
    orthonormalPartialTrace k b A ≤
      ∑ j ∈ spectralInitialIndices (Module.finrank ℝ E) k, hA.eigenvalues rfl j := by
  rw [orthonormalPartialTrace_eq_weighted_eigenvalues k b A hA]
  exact sum_mul_weights_le_sum_initial hk (hA.eigenvalues_antitone rfl)
    (spectralTraceWeights_nonneg k _ b) (spectralTraceWeights_le_one k _ b)
    (by rw [sum_spectralTraceWeights,card_spectralInitialIndices hk])

/-- The Ky Fan variational formula, including multiplicities. -/
theorem kyFanValue_eq_eigenvalue_sum {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) :
    kyFanValue k A = ∑ j ∈ spectralInitialIndices (Module.finrank ℝ E) k, hA.eigenvalues rfl j := by
  letI : Nonempty (OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) := ⟨stdOrthonormalBasis ℝ E⟩
  apply le_antisymm
  · exact ciSup_le (fun b ↦ orthonormalPartialTrace_le_eigenvalue_sum hk b A hA)
  · have h := orthonormalPartialTrace_le_kyFanValue k (hA.eigenvectorBasis rfl) A
    convert h using 1
    unfold orthonormalPartialTrace
    apply Finset.sum_congr rfl
    intro i _
    have ha : A (hA.eigenvectorBasis rfl i) = hA.eigenvalues rfl i • hA.eigenvectorBasis rfl i :=
      hA.apply_eigenvectorBasis rfl i
    rw [ha,real_inner_smul_right]
    simp only [real_inner_self_eq_norm_sq,(hA.eigenvectorBasis rfl).orthonormal.norm_eq_one,one_pow,mul_one]

/-- Each ordered eigenvalue is a difference of consecutive finite convex
Ky Fan functions. -/
theorem eigenvalue_eq_kyFan_difference (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) :
    hA.eigenvalues rfl i = kyFanValue (i.val+1) A-kyFanValue i.val A := by
  rw [kyFanValue_eq_eigenvalue_sum (Nat.succ_le_iff.mpr i.isLt) A hA,
    kyFanValue_eq_eigenvalue_sum i.isLt.le A hA]
  have hi : i ∉ spectralInitialIndices (Module.finrank ℝ E) i.val := by simp [spectralInitialIndices]
  have he : spectralInitialIndices (Module.finrank ℝ E) (i.val+1) =
      insert i (spectralInitialIndices (Module.finrank ℝ E) i.val) := by
    ext j
    simp only [spectralInitialIndices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h) <;> omega
  rw [he,Finset.sum_insert hi]
  ring

end
end RW
