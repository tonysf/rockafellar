/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The absolute-value example for level-set boundaries
-/

import RockafellarWets.Chapter10.EpiLipschitzLevelSets
import RockafellarWets.Chapter10.SeparableSubgradients
import RockafellarWets.Chapter8.NormAndMaxSubgradients
import RockafellarWets.Chapter8.NegativeNorm
import RockafellarWets.Chapter9.ImplicitGraphPermutations
import RockafellarWets.Chapter9.NormalsFromAubinFailure
import RockafellarWets.Chapter6.BoundaryNormals

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

/-- The Lipschitz function in Example 10.4. -/
def absoluteDifference (p : WithLp 2 (ℝ × ℝ)) : ℝ := |p.fst|-|p.snd|

theorem absoluteDifference_separable :
    (fun p ↦ (absoluteDifference p:EReal)) = separableSum (fun a : ℝ ↦ (‖a‖:EReal)) negNorm := by
  ext p
  simp [absoluteDifference,separableSum,negNorm,Real.norm_eq_abs,sub_eq_add_neg,EReal.coe_add,EReal.coe_neg]

theorem continuous_absoluteDifference : Continuous absoluteDifference :=
  (WithLp.continuous_fst 2 ℝ ℝ).abs.sub (WithLp.continuous_snd 2 ℝ ℝ).abs

theorem lipschitzWith_absoluteDifference :
    LipschitzWith (‖WithLp.fstL 2 ℝ ℝ ℝ‖₊+‖WithLp.sndL 2 ℝ ℝ ℝ‖₊) absoluteDifference := by
  simpa only [Function.comp_def,Real.norm_eq_abs,one_mul] using
    (lipschitzWith_one_norm.comp (WithLp.fstL 2 ℝ ℝ ℝ).lipschitz).sub
      (lipschitzWith_one_norm.comp (WithLp.sndL 2 ℝ ℝ ℝ).lipschitz)

theorem absoluteDifference_zero_level :
    {p | absoluteDifference p ≤ 0} =
      {p : WithLp 2 (ℝ × ℝ) | |p.fst| ≤ p.snd} ∪ {p | |p.fst| ≤ -p.snd} := by
  ext p
  simp only [mem_setOf_eq,absoluteDifference,sub_nonpos,mem_union,abs_eq_max_neg,max_le_iff]
  constructor
  · intro hp
    by_cases hs : 0 ≤ p.snd
    · left
      simpa only [max_eq_left (by linarith : -p.snd ≤ p.snd)] using hp
    · right
      simpa only [max_eq_right (by linarith : p.snd ≤ -p.snd)] using hp
  · rintro (hp | hp)
    · exact ⟨hp.1.trans (le_max_left _ _),hp.2.trans (le_max_left _ _)⟩
    · exact ⟨hp.1.trans (le_max_right _ _),hp.2.trans (le_max_right _ _)⟩

/-- The limiting subgradients are exactly the two horizontal unit segments. -/
theorem subdifferential_absoluteDifference_zero :
    subdifferential (fun p ↦ (absoluteDifference p:EReal)) 0 =
      l2ProdSet (Icc (-1:ℝ) 1) ({-1,1}:Set ℝ) := by
  rw [absoluteDifference_separable]
  have hf : LowerSemicontinuousAt (fun a : ℝ ↦ (‖a‖:EReal)) 0 :=
    (continuous_coe_real_ereal.comp continuous_norm).lowerSemicontinuous 0
  have hg : LowerSemicontinuousAt (negNorm (E := ℝ)) 0 :=
    (continuous_coe_real_ereal.comp continuous_norm.neg).lowerSemicontinuous 0
  ext v
  change v ∈ subdifferential (separableSum (fun a : ℝ ↦ (‖a‖:EReal)) negNorm)
    (WithLp.toLp 2 ((0:ℝ),(0:ℝ))) ↔ v ∈ l2ProdSet (Icc (-1:ℝ) 1) ({-1,1}:Set ℝ)
  rw [mem_subdifferential_separableSum_iff hf hg (c := 0) (d := 0) (by simp) (by simp [negNorm]),
    subdifferential_norm,if_pos rfl,subdifferential_negNorm_zero,frontier_closedBall _ one_ne_zero]
  simp only [mem_l2ProdSet,mem_closedBall_zero_iff,mem_sphere_zero_iff_norm,Real.norm_eq_abs,
    abs_le,mem_Icc,mem_insert_iff,mem_singleton_iff]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨ha,(abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hb |>.symm⟩
  · rintro ⟨ha,hb | hb⟩ <;> simp [ha,hb]

/-- The convexified subdifferential fills the entire square. -/
theorem convexHull_subdifferential_absoluteDifference_zero :
    convexHull ℝ (subdifferential (fun p ↦ (absoluteDifference p:EReal)) 0) =
      l2ProdSet (Icc (-1:ℝ) 1) (Icc (-1:ℝ) 1) := by
  let L := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm
  have he (A B : Set ℝ) : l2ProdSet A B = L '' (A ×ˢ B) := by
    ext p
    constructor
    · intro hp
      exact ⟨WithLp.ofLp p,hp,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact hq
  have hL (A : Set (ℝ × ℝ)) : L '' convexHull ℝ A = convexHull ℝ (L '' A) :=
    L.toLinearEquiv.toLinearMap.image_convexHull A
  rw [subdifferential_absoluteDifference_zero,he,← hL,
    convexHull_prod,(convex_Icc (-1:ℝ) 1).convexHull_eq,convexHull_pair,
    segment_eq_Icc (by norm_num : (-1:ℝ) ≤ 1),← he]

theorem zero_not_mem_subdifferential_absoluteDifference :
    (0:WithLp 2 (ℝ × ℝ)) ∉ subdifferential (fun p ↦ (absoluteDifference p:EReal)) 0 := by
  rw [subdifferential_absoluteDifference_zero]
  simp [l2ProdSet]

theorem zero_mem_convexHull_subdifferential_absoluteDifference :
    (0:WithLp 2 (ℝ × ℝ)) ∈ convexHull ℝ (subdifferential (fun p ↦ (absoluteDifference p:EReal)) 0) := by
  rw [convexHull_subdifferential_absoluteDifference_zero]
  norm_num [l2ProdSet]

/-- A closed centrally symmetric set with zero on its boundary cannot have
a pointed limiting normal cone there. -/
theorem not_isPointed_normalCone_of_symmetric_boundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} (hc : IsClosed C) (hs : ∀ y, -y ∈ C ↔ y ∈ C) (hb : (0:E) ∈ frontier C) :
    ¬ IsPointed (normalCone C 0) := by
  obtain ⟨v,hv,hv0⟩ := (mem_frontier_iff_exists_nonzero_normal hc).mp hb
  have he : (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E) ⁻¹' C = C := by
    ext y
    exact hs y
  have hn := normalCone_preimage_linearIsometryEquiv (LinearIsometryEquiv.neg ℝ) C (0:E)
  rw [he] at hn
  have hneg : -v ∈ normalCone C 0 := by
    rw [hn] at hv
    simpa using hv
  intro hp
  have hz := hp 2 ![v,-v] (by intro i; fin_cases i <;> simp [hv,hneg]) (by simp) (0:Fin 2)
  exact hv0 (by simpa using hz)

/-- **Example 10.4**, the two-wedge zero-level set has no Lipschitz epigraph
boundary at the origin. -/
theorem absoluteDifference_levelSet_not_epiLipschitz :
    ¬ IsEpiLipschitzAt {p | absoluteDifference p ≤ 0} (0:WithLp 2 (ℝ × ℝ)) := by
  let C := {p | absoluteDifference p ≤ 0}
  have hc : IsClosed C := isClosed_le continuous_absoluteDifference continuous_const
  have hb : (0:WithLp 2 (ℝ × ℝ)) ∈ frontier C := by
    rw [hc.frontier_eq]
    refine ⟨by simp [C,absoluteDifference],?_⟩
    intro hi
    have hp : Tendsto (fun t : ℝ ↦ WithLp.toLp 2 (t,(0:ℝ))) (𝓝[>] 0)
        (𝓝 (0:WithLp 2 (ℝ × ℝ))) := by
      exact ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.continuous.continuousAt.tendsto.comp
        (tendsto_id.prodMk_nhds tendsto_const_nhds)).mono_left nhdsWithin_le_nhds
    have hn := hp.eventually (mem_interior_iff_mem_nhds.mp hi)
    have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    obtain ⟨t,ht,hC⟩ := (ht.and hn).exists
    have hle : |t| ≤ 0 := by simpa [C,absoluteDifference] using hC
    exact (abs_pos.mpr ht.ne').not_ge hle
  have hs (p : WithLp 2 (ℝ × ℝ)) : -p ∈ C ↔ p ∈ C := by
    simp [C,absoluteDifference]
  intro h
  exact not_isPointed_normalCone_of_symmetric_boundary hc hs hb
    ((isEpiLipschitzAt_iff_at_frontier hb).mp h).2

/-- In contrast, the level-set mapping still has the Aubin property. -/
theorem absoluteDifference_levelMapping_hasAubinProperty :
    HasAubinPropertyAt (fun a : ℝ ↦ levelSet (fun p ↦ (absoluteDifference p:EReal)) a) 0 0 := by
  have hl : IsLocallyLscAt (fun p ↦ (absoluteDifference p:EReal)) 0 :=
    locallyLscAt_of_lowerSemicontinuous_finite
      (continuous_coe_real_ereal.comp continuous_absoluteDifference).lowerSemicontinuous
      (c := 0) (by simp [absoluteDifference])
  exact not_not.mp (fun hn ↦ zero_not_mem_subdifferential_absoluteDifference
    ((zero_subgradient_iff_not_aubin_levelSet (c := 0) (by simp [absoluteDifference]) hl).mpr hn))

end RW
