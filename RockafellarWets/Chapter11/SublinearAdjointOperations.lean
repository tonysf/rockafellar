/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Elementary calculus for upper and lower adjoints
-/
import RockafellarWets.Chapter11.SublinearAdjoints
import RockafellarWets.Chapter5.MappingOperations
import RockafellarWets.Chapter5.PerturbedMappings

open Set
open scoped InnerProductSpace Pointwise
namespace RW

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- Exercise 11.31(c), upper adjoints and positive output scaling. -/
theorem svUpperAdjoint_smul (H : E → Set F) {c : ℝ} (hc : 0<c) :
    svUpperAdjoint (fun w ↦ c • H w) = fun y ↦ c • svUpperAdjoint H y := by
  funext y
  ext v
  constructor
  · intro hv
    refine ⟨c⁻¹ • v, ?_, smul_inv_smul₀ hc.ne' _⟩
    intro w z hz
    have h := hv w (c • z) ⟨z,hz,rfl⟩
    rw [real_inner_smul_right] at h
    rw [real_inner_smul_left]
    exact (inv_mul_le_iff₀ hc).mpr h
  · rintro ⟨u,hu,rfl⟩ w _ ⟨z,hz,rfl⟩
    rw [real_inner_smul_left,real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hu w z hz) hc.le

/-- Exercise 11.31(c), lower adjoints and positive output scaling. -/
theorem svLowerAdjoint_smul (H : E → Set F) {c : ℝ} (hc : 0<c) :
    svLowerAdjoint (fun w ↦ c • H w) = fun y ↦ c • svLowerAdjoint H y := by
  funext y
  ext v
  constructor
  · intro hv
    refine ⟨c⁻¹ • v, ?_, smul_inv_smul₀ hc.ne' _⟩
    intro w z hz
    have h := hv w (c • z) ⟨z,hz,rfl⟩
    rw [real_inner_smul_right] at h
    rw [real_inner_smul_left]
    exact (le_inv_mul_iff₀ hc).mpr h
  · rintro ⟨u,hu,rfl⟩ w _ ⟨z,hz,rfl⟩
    rw [real_inner_smul_left,real_inner_smul_right]
    exact mul_le_mul_of_nonneg_left (hu w z hz) hc.le

theorem svComp_upperAdjoints_subset (H : E → Set F) (K : F → Set G) :
    svComp (svUpperAdjoint H) (svUpperAdjoint K) ≤ svUpperAdjoint (svComp K H) := by
  intro y v hv
  obtain ⟨z,hz,hv⟩ := mem_svImage.mp hv
  intro w u hu
  obtain ⟨q,hq,hu⟩ := mem_svImage.mp hu
  exact (hv w q hq).trans (hz q u hu)

theorem svComp_lowerAdjoints_subset (H : E → Set F) (K : F → Set G) :
    svComp (svLowerAdjoint H) (svLowerAdjoint K) ≤ svLowerAdjoint (svComp K H) := by
  intro y v hv
  obtain ⟨z,hz,hv⟩ := mem_svImage.mp hv
  intro w u hu
  obtain ⟨q,hq,hu⟩ := mem_svImage.mp hu
  exact (hz q u hu).trans (hv w q hq)

theorem svAdd_upperAdjoints_subset (H K : E → Set F) :
    svAdd (svUpperAdjoint H) (svUpperAdjoint K) ≤ svUpperAdjoint (svAdd H K) := by
  intro y v hv
  obtain ⟨a,ha,b,hb,rfl⟩ := hv
  intro w z hz
  obtain ⟨p,hp,q,hq,rfl⟩ := hz
  rw [inner_add_left,inner_add_right]
  exact add_le_add (ha w p hp) (hb w q hq)

theorem svAdd_lowerAdjoints_subset (H K : E → Set F) :
    svAdd (svLowerAdjoint H) (svLowerAdjoint K) ≤ svLowerAdjoint (svAdd H K) := by
  intro y v hv
  obtain ⟨a,ha,b,hb,rfl⟩ := hv
  intro w z hz
  obtain ⟨p,hp,q,hq,rfl⟩ := hz
  rw [inner_add_left,inner_add_right]
  exact add_le_add (ha w p hp) (hb w q hq)

end RW
