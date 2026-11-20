/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Global Lipschitz continuity of polyhedral multifunctions

For each active set, a nonzero projection residual in the polar of the feasible
directions must violate an active inequality. Compactness on the unit sphere
gives a uniform bound for the residual. There are only finitely many active sets.
-/

import RockafellarWets.Chapter9.SetValuedLipschitz
import RockafellarWets.Chapter6.PolyhedralCones
import RockafellarWets.Chapter6.TangentNormalPolarity
import RockafellarWets.Chapter6.ProximalNormals

open Set Metric
open scoped BigOperators NNReal InnerProductSpace

namespace RW

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {m : ℕ}

/-- A direction normal to an active tangent cone is controlled by the sum
of the violations of its active inequalities, uniformly over all active sets. -/
private theorem exists_active_violation_bound (B : Fin m → F) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ (J : Finset (Fin m)) (v : F), v ∈ polarCone {d | ∀ i ∈ J, ⟪B i,d⟫_ℝ ≤ 0} →
      ‖v‖ ≤ k * ∑ i ∈ J, max (⟪B i,v⟫_ℝ) 0 := by
  classical
  let q := fun (J : Finset (Fin m)) (v : F) ↦ ∑ i ∈ J, max (⟪B i,v⟫_ℝ) 0
  have hnn (J : Finset (Fin m)) (v : F) : 0 ≤ q J v := Finset.sum_nonneg fun _ _ ↦ le_max_right ..
  have hJ (J : Finset (Fin m)) : ∃ k : ℝ, 0 ≤ k ∧ ∀ v ∈ polarCone {d | ∀ i ∈ J, ⟪B i,d⟫_ℝ ≤ 0},
      ‖v‖ = 1 → 1 ≤ k * q J v := by
    let K := {d : F | ∀ i ∈ J, ⟪B i,d⟫_ℝ ≤ 0}
    let D := polarCone K ∩ sphere (0:F) 1
    have hcompact : IsCompact D := (isCompact_sphere (0:F) 1).inter_left (isClosed_polarCone K)
    rcases D.eq_empty_or_nonempty with he | hn
    · exact ⟨0,le_rfl,fun v hv heq ↦ (notMem_empty v (he ▸ (show v ∈ D from ⟨hv,mem_sphere_zero_iff_norm.2 heq⟩))).elim⟩
    have hc : Continuous (q J) := by dsimp only [q]; fun_prop
    obtain ⟨w,hw,hmin⟩ := hcompact.exists_isMinOn hn hc.continuousOn
    have hpos : 0 < q J w := by
      by_contra! hzero
      have hmem : w ∈ K := by
        intro i hi
        have hsingle := Finset.single_le_sum (f := fun j ↦ max (⟪B j,w⟫_ℝ) 0) (fun _ _ ↦ le_max_right ..) hi
        exact ((le_max_left ..).trans hsingle).trans hzero
      have hi := hw.1 w hmem
      rw [real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.1 hw.2] at hi
      norm_num at hi
    refine ⟨(q J w)⁻¹,(inv_pos.2 hpos).le,fun v hv hnorm ↦ ?_⟩
    calc
      1 = (q J w)⁻¹ * q J w := (inv_mul_cancel₀ hpos.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmin (show v ∈ D from ⟨hv,mem_sphere_zero_iff_norm.2 hnorm⟩)) (inv_pos.2 hpos).le
  choose ks hks hbound using hJ
  let k := ∑ J, ks J
  refine ⟨k,Finset.sum_nonneg (fun j _ ↦ hks j),fun J v hv ↦ ?_⟩
  change ‖v‖ ≤ k * q J v
  rcases eq_or_ne v 0 with rfl | hne
  · exact (norm_zero.le.trans (mul_nonneg (Finset.sum_nonneg fun j _ ↦ hks j) (hnn _ _)))
  have hnorm := norm_pos_iff.2 hne
  let u := ‖v‖⁻¹ • v
  have hu := (isCone_polarCone _).2 hv (inv_pos.2 hnorm)
  have hunit : ‖u‖ = 1 := norm_smul_inv_norm hne
  have hscaled := hbound J u hu hunit
  have hkJ : ks J ≤ k := Finset.single_le_sum (fun j _ ↦ hks j) (Finset.mem_univ J)
  have he : q J v = ‖v‖ * q J u := by
    have hsv : ‖v‖ • u = v := by simp [u,smul_smul,hnorm.ne']
    conv_lhs => rw [← hsv]
    simp only [q,real_inner_smul_right,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_max_of_nonneg _ _ hnorm.le,mul_zero]
  rw [he]
  have hm := mul_le_mul_of_nonneg_left (hscaled.trans (mul_le_mul_of_nonneg_right hkJ (hnn J u))) hnorm.le
  linarith only [hm]

/-- **Example 9.35.** A mapping with polyhedral graph is globally Lipschitz on
its entire domain, with no boundedness requirement on its values. -/
theorem svLipschitzOn_of_isPolyhedral_graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : E → Set F} (hp : IsPolyhedral (svGraph S)) :
    SvLipschitzOn S (svDom S) := by
  classical
  letI := FiniteDimensional.complete ℝ F
  obtain ⟨m,L,b,hG⟩ := hp.isHPolyhedral
  let A (i : Fin m) := (L i).comp (ContinuousLinearMap.inl ℝ E F)
  let B (i : Fin m) := (InnerProductSpace.toDual ℝ F).symm ((L i).comp (ContinuousLinearMap.inr ℝ E F))
  have hsplit (i : Fin m) (a : E) (z : F) : L i (a,z) = A i a + ⟪B i,z⟫_ℝ := by
    have he : (a,z) = (a,0) + (0,z) := by simp
    rw [he,map_add]
    simp [A,B]
  have hfiber (a : E) : S a = {z | ∀ i, ⟪B i,z⟫_ℝ ≤ b i - A i a} := by
    ext z
    change (a,z) ∈ svGraph S ↔ _
    simp only [hG,mem_linearInequalitySet,hsplit,mem_setOf_eq]
    exact forall_congr' fun i ↦ by constructor <;> intro h <;> linarith
  have hS : NonemptyClosedValuedOn S (svDom S) := fun a ha ↦ ⟨ha,by
    rw [hfiber]; exact (isHPolyhedral_setOf_inner_le _ _).isClosed⟩
  obtain ⟨k,hk,hbound⟩ := exists_active_violation_bound B
  let Lsum := ∑ i, ‖A i‖
  have hsum : 0 ≤ Lsum := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine ⟨⟨k*Lsum,mul_nonneg hk hsum⟩,(svLipschitzOnWith_iff_transport hS).2 ?_⟩
  intro a ha x hx u hu
  obtain ⟨z,hz⟩ := projMapping_nonempty (hS x hx).2 (hS x hx).1 u
  have hz' := hz.1
  let J := Finset.univ.filter (fun i ↦ ⟪B i,z⟫_ℝ = b i - A i x)
  have hJ (i : Fin m) : i ∈ J ↔ ⟪B i,z⟫_ℝ = b i - A i x := by simp [J]
  have hd := sub_mem_regularNormalCone_of_mem_projMapping hz
  have hzx : ∀ i, ⟪B i,z⟫_ℝ ≤ b i - A i x := by simpa only [hfiber x,mem_setOf_eq] using hz'
  rw [regularNormalCone_eq_polarCone_tangentCone hz',hfiber x,tangentCone_setOf_inner_le hzx] at hd
  have hnorm := hbound J (u-z) (by simpa only [hJ] using hd)
  have hupper (i : Fin m) (hi : i ∈ J) : max (⟪B i,u-z⟫_ℝ) 0 ≤ ‖A i‖*dist a x := by
    have hua : ∀ j, ⟪B j,u⟫_ℝ ≤ b j - A j a := by simpa only [hfiber a,mem_setOf_eq] using hu
    have hu' := hua i
    have hzval := (hJ i).1 hi
    have hop := (A i).le_opNorm (x-a)
    rw [map_sub,Real.norm_eq_abs] at hop
    apply max_le _ (mul_nonneg (norm_nonneg _) dist_nonneg)
    rw [inner_sub_right,dist_comm,dist_eq_norm]
    linarith [le_abs_self (A i x-A i a)]
  have hsumJ : ∑ i ∈ J, max (⟪B i,u-z⟫_ℝ) 0 ≤ Lsum*dist a x := by
    calc
      _ ≤ ∑ i ∈ J, ‖A i‖*dist a x := Finset.sum_le_sum hupper
      _ = (∑ i ∈ J, ‖A i‖)*dist a x := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ ↦ norm_nonneg _)) dist_nonneg
  exact ⟨z,hz',by rw [dist_eq_norm]; change ‖u-z‖ ≤ k*Lsum*dist a x; rw [mul_assoc]; exact hnorm.trans (mul_le_mul_of_nonneg_left hsumJ hk)⟩

end RW
