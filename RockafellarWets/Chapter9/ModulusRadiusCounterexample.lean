/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Failure of the weak radius boundary in formula 9(14)
-/

import RockafellarWets.Chapter9.GraphConvexModulus
import RockafellarWets.Chapter9.BoundedSetValuedMappings
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

noncomputable section

abbrev RadiusBoundaryPlane := WithLp 2 (ℝ × ℝ)

def radiusBoundaryPoint (a b : ℝ) : RadiusBoundaryPlane := WithLp.toLp 2 (a,b)

/-- A positive homogeneous Lipschitz bump, between one quarter and one half
of the norm, with slope one on a sector. -/
def radiusBoundaryBump (p : RadiusBoundaryPlane) : ℝ :=
  max (‖p‖/4) (min (‖p‖/2) p.snd)

def radiusBoundaryMap (p : RadiusBoundaryPlane) : Set ℝ :=
  {-1-‖p‖/2,3+radiusBoundaryBump p}

private theorem radiusBoundaryBump_bounds (p : RadiusBoundaryPlane) :
    ‖p‖/4 ≤ radiusBoundaryBump p ∧ radiusBoundaryBump p ≤ ‖p‖/2 :=
  ⟨le_max_left _ _,max_le (by nlinarith [norm_nonneg p]) (min_le_left _ _)⟩

private theorem radiusBoundaryBump_nonneg (p : RadiusBoundaryPlane) : 0 ≤ radiusBoundaryBump p :=
  (by positivity : 0 ≤ ‖p‖/4).trans (radiusBoundaryBump_bounds p).1

private theorem norm_div_lipschitz {c : ℝ} (hc : 1 ≤ c) :
    LipschitzWith 1 (fun p : RadiusBoundaryPlane ↦ ‖p‖/c) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Real.dist_eq,← sub_div,abs_div,abs_of_pos (by linarith : 0 < c),NNReal.coe_one,one_mul]
  exact (div_le_self (abs_nonneg _) hc).trans (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le p q)

private theorem radiusBoundaryBump_lipschitz : LipschitzWith 1 radiusBoundaryBump := by
  have hsnd : LipschitzWith 1 (fun p : RadiusBoundaryPlane ↦ p.snd) :=
    LipschitzWith.of_dist_le_mul fun p q ↦ by simpa using WithLp.dist_snd_le p q
  simpa only [radiusBoundaryBump,max_self] using
    (norm_div_lipschitz (by norm_num : (1:ℝ) ≤ 4)).max
      ((norm_div_lipschitz (by norm_num : (1:ℝ) ≤ 2)).min hsnd)

private theorem radiusBoundary_first_dist (p q : RadiusBoundaryPlane) :
    dist (-1-‖p‖/2) (-1-‖q‖/2) ≤ (1/2:ℝ)*dist p q := by
  rw [Real.dist_eq,show -1-‖p‖/2-(-1-‖q‖/2) = -(‖p‖-‖q‖)/2 by ring,
    abs_div,abs_neg]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h := abs_norm_sub_norm_le p q
  rw [← dist_eq_norm] at h
  linarith

private theorem radiusBoundary_nonempty_closed : NonemptyClosedValuedOn radiusBoundaryMap univ := by
  intro p _
  exact ⟨⟨-1-‖p‖/2,by simp [radiusBoundaryMap]⟩,by
    change IsClosed ({-1-‖p‖/2} ∪ {3+radiusBoundaryBump p})
    exact isClosed_singleton.union isClosed_singleton⟩

/-- The example is globally Hausdorff-Lipschitz, hence strictly continuous. -/
theorem radiusBoundaryMap_lipschitz : SvLipschitzOnWith 1 radiusBoundaryMap univ := by
  apply (svLipschitzOnWith_iff_transport radiusBoundary_nonempty_closed).mpr
  intro p _ q _ v hv
  rcases mem_insert_iff.mp hv with rfl | hv
  · exact ⟨-1-‖q‖/2,by simp [radiusBoundaryMap],
      (radiusBoundary_first_dist p q).trans (by simp only [NNReal.coe_one,one_mul]; nlinarith [dist_nonneg (x := p) (y := q)])⟩
  · have he : v = 3+radiusBoundaryBump p := mem_singleton_iff.mp hv
    subst v
    refine ⟨3+radiusBoundaryBump q,by simp [radiusBoundaryMap],?_⟩
    simpa only [dist_add_left] using radiusBoundaryBump_lipschitz.dist_le_mul p q

/-- At radius three, only the lower branch is visible away from the origin.
The upper branch at the origin is transported with the half-norm bound. -/
theorem radiusBoundaryMap_transport : RhoTransport (1/2) 3 radiusBoundaryMap univ := by
  intro p _ q _ v hv
  rcases mem_insert_iff.mp hv.1 with rfl | hvp
  · exact ⟨-1-‖q‖/2,by simp [radiusBoundaryMap],by simpa using radiusBoundary_first_dist p q⟩
  · have he : v = 3+radiusBoundaryBump p := mem_singleton_iff.mp hvp
    have hnorm : |3+radiusBoundaryBump p| ≤ 3 := by simpa only [he,mem_closedBall,Real.dist_eq,sub_zero] using hv.2
    rw [abs_of_nonneg (by linarith [radiusBoundaryBump_nonneg p])] at hnorm
    have hp0 : p = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg p,(radiusBoundaryBump_bounds p).1])
    subst p
    have he0 : v = 3 := by simpa [radiusBoundaryBump] using he
    rw [he0]
    refine ⟨3+radiusBoundaryBump q,by simp [radiusBoundaryMap],?_⟩
    simp only [dist_zero_left,Real.dist_eq,show (3:ℝ)-(3+radiusBoundaryBump q) = -radiusBoundaryBump q by ring,
      abs_neg,abs_of_nonneg (radiusBoundaryBump_nonneg q)]
    norm_num only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
    linarith [(radiusBoundaryBump_bounds q).2]

/-- The profile at output center one is exactly the upper-branch distance. -/
theorem radiusBoundaryMap_distance_one (p : RadiusBoundaryPlane) :
    infDist 1 (radiusBoundaryMap p) = 2+radiusBoundaryBump p := by
  apply le_antisymm
  · have h := infDist_le_dist_of_mem (x := (1:ℝ))
      (show 3+radiusBoundaryBump p ∈ radiusBoundaryMap p by simp [radiusBoundaryMap])
    rw [Real.dist_eq,abs_of_nonpos (by linarith [radiusBoundaryBump_nonneg p])] at h
    linarith
  · apply (le_infDist (radiusBoundary_nonempty_closed p (mem_univ _)).1).mpr
    intro y hy
    rcases mem_insert_iff.mp hy with rfl | hy
    · rw [Real.dist_eq,abs_of_nonneg (by nlinarith [norm_nonneg p])]
      linarith [(radiusBoundaryBump_bounds p).2]
    · rw [mem_singleton_iff.mp hy,Real.dist_eq,abs_of_nonpos (by linarith [radiusBoundaryBump_nonneg p])]
      nlinarith

private theorem norm_point_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖radiusBoundaryPoint a b‖ ≤ a+b := by
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (radiusBoundaryPoint a b)
  change ‖radiusBoundaryPoint a b‖^2 = |a|^2+|b|^2 at hsq
  rw [abs_of_nonneg ha,abs_of_nonneg hb] at hsq
  nlinarith [norm_nonneg (radiusBoundaryPoint a b)]

private theorem radiusBoundary_probes {t : ℝ} (ht : 0 < t) :
    ‖radiusBoundaryPoint t (t/3)‖ ≤ 4*t/3 ∧ ‖radiusBoundaryPoint t (5*t/12)‖ ≤ 17*t/12 ∧
      radiusBoundaryBump (radiusBoundaryPoint t (t/3)) = t/3 ∧
      radiusBoundaryBump (radiusBoundaryPoint t (5*t/12)) = 5*t/12 ∧
      dist (radiusBoundaryPoint t (t/3)) (radiusBoundaryPoint t (5*t/12)) = t/12 := by
  have hp : ‖radiusBoundaryPoint t (t/3)‖ ≤ 4*t/3 := by
    have h := norm_point_le_add ht.le (show 0 ≤ t/3 by positivity)
    linarith
  have hq : ‖radiusBoundaryPoint t (5*t/12)‖ ≤ 17*t/12 := by
    have h := norm_point_le_add ht.le (show 0 ≤ 5*t/12 by positivity)
    linarith
  have hpLower : t ≤ ‖radiusBoundaryPoint t (t/3)‖ := by
    simpa [radiusBoundaryPoint,Real.norm_eq_abs,abs_of_pos ht] using
      WithLp.norm_fst_le ℝ (radiusBoundaryPoint t (t/3))
  have hqLower : t ≤ ‖radiusBoundaryPoint t (5*t/12)‖ := by
    simpa [radiusBoundaryPoint,Real.norm_eq_abs,abs_of_pos ht] using
      WithLp.norm_fst_le ℝ (radiusBoundaryPoint t (5*t/12))
  refine ⟨hp,hq,?_,?_,?_⟩
  · change max (‖radiusBoundaryPoint t (t/3)‖/4) (min (‖radiusBoundaryPoint t (t/3)‖/2) (t/3)) = t/3
    rw [min_eq_right (by linarith),max_eq_right (by linarith)]
  · change max (‖radiusBoundaryPoint t (5*t/12)‖/4) (min (‖radiusBoundaryPoint t (5*t/12)‖/2) (5*t/12)) = 5*t/12
    rw [min_eq_right (by linarith),max_eq_right (by linarith)]
  · rw [WithLp.prod_dist_eq_of_L2]
    change Real.sqrt ((dist t t)^2+(dist (t/3) (5*t/12))^2) = t/12
    rw [dist_self,zero_pow (by decide),zero_add,Real.sqrt_sq (dist_nonneg),
      Real.dist_eq,abs_of_nonpos (by linarith)]
    ring

/-- The center-one profile has local Lipschitz modulus at least one. -/
theorem radiusBoundaryMap_profile_modulus :
    (1:ℝ≥0∞) ≤ svLipschitzModulus radiusBoundaryMap 1 0 := by
  apply le_iInf
  intro k
  obtain ⟨U,hU,hLip⟩ := k.property
  rw [nhdsWithin_univ] at hU
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hdist := (svRhoLipschitzOnWith_iff_distance_functions.mp hLip)
    1 (by norm_num [mem_closedBall,Real.dist_eq])
  have ht : 0 < ε/2 := half_pos hε
  obtain ⟨hp,hq,hgp,hgq,hd⟩ := radiusBoundary_probes ht
  have hpU : (radiusBoundaryPoint (ε/2) ((ε/2)/3)) ∈ U := hεU (by
    rw [mem_ball,dist_zero_right]
    linarith)
  have hqU : (radiusBoundaryPoint (ε/2) (5*(ε/2)/12)) ∈ U := hεU (by
    rw [mem_ball,dist_zero_right]
    linarith)
  have h := hdist.dist_le_mul _ hpU _ hqU
  rw [radiusBoundaryMap_distance_one,radiusBoundaryMap_distance_one,hgp,hgq,hd,
    Real.dist_eq,abs_of_nonpos (by linarith)] at h
  have hk : (1:ℝ) ≤ (k.val:ℝ) := by nlinarith
  exact ENNReal.coe_le_coe.mpr (by exact_mod_cast hk)

/-- The boundary radius in 9(14) is exactly three for this example. -/
theorem radiusBoundaryMap_distance_zero : infDist 0 (radiusBoundaryMap 0) = 1 := by
  apply le_antisymm
  · have h := infDist_le_dist_of_mem (x := (0:ℝ))
      (show (-1:ℝ) ∈ radiusBoundaryMap 0 by simp [radiusBoundaryMap])
    simpa [Real.dist_eq] using h
  · apply (le_infDist (radiusBoundary_nonempty_closed 0 (mem_univ _)).1).mpr
    intro y hy
    simp only [radiusBoundaryMap,radiusBoundaryBump,norm_zero,zero_div,min_self,max_self,
      sub_zero,add_zero,mem_insert_iff,mem_singleton_iff] at hy
    rcases hy with rfl | rfl <;> norm_num [Real.dist_eq]

/-- Formula 9(14) fails at its printed weak radius boundary, even for a
globally Hausdorff-Lipschitz mapping with nonempty finite fibers. -/
theorem modulus_radius_boundary_counterexample :
    SvStrictlyContinuousAt radiusBoundaryMap 0 ∧
      2*(1:ℝ)+infDist 0 (radiusBoundaryMap 0) = 3 ∧
      svRhoHatLipschitzModulus radiusBoundaryMap 3 0 <
        svLipschitzModulus radiusBoundaryMap 1 0 := by
  refine ⟨svStrictlyContinuousWithinAt_of_locally_svSubLipschitzOn (mem_univ _) ?_,?_,?_⟩
  · exact ⟨univ,univ_mem,(show SvLipschitzOn radiusBoundaryMap univ from
      ⟨1,radiusBoundaryMap_lipschitz⟩).svSubLipschitzOn⟩
  · rw [radiusBoundaryMap_distance_zero]
    norm_num
  · have hhat : svRhoHatLipschitzModulus radiusBoundaryMap 3 0 ≤ ((1/2:ℝ≥0):ℝ≥0∞) :=
      radiusBoundaryMap_transport.svRhoHatModulus_le univ_mem
    exact lt_of_le_of_lt hhat (lt_of_lt_of_le (by norm_num) radiusBoundaryMap_profile_modulus)

end
end RW
