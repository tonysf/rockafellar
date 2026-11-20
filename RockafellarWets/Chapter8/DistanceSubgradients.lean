/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Regular and limiting subgradients of distance functions
-/

import RockafellarWets.Chapter8.DistanceSubderivatives
import RockafellarWets.Chapter8.RegularSubderivativeSupport
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {C : Set E} {x p v : E}

/-- The outward unit direction of a projection at a point outside the set. -/
noncomputable def projectionDirection (C : Set E) (x p : E) : E := (infDist x C)⁻¹ • (x-p)

omit [FiniteDimensional ℝ E] in
theorem inner_projectionDirection (C : Set E) (x p w : E) :
    ⟪projectionDirection C x p,w⟫_ℝ = ⟪x-p,w⟫_ℝ / infDist x C := by
  rw [projectionDirection,real_inner_smul_left,div_eq_inv_mul]

omit [FiniteDimensional ℝ E] in
theorem norm_projectionDirection (hx : x ∉ C) (hp : p ∈ projMapping C x) :
    ‖projectionDirection C x p‖ = 1 := by
  have ha : 0 < ‖x-p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun he ↦ hx (he ▸ hp.1)))
  rw [projectionDirection, ← norm_sub_eq_infDist hp,norm_smul_of_nonneg (inv_nonneg.mpr ha.le),
    inv_mul_cancel₀ ha.ne']

/-- **Example 8.53.** Within the set, the regular subgradients of the
distance are its regular normals of norm at most one. -/
theorem regularSubdifferential_distanceVA_of_mem (hC : IsClosed C) (hx : x ∈ C) :
    regularSubdifferential (distanceVA C) x = regularNormalCone C x ∩ closedBall 0 1 := by
  ext v
  rw [mem_regularSubdifferential_iff_inner_le_subderivative
    (show distanceVA C x = ((infDist x C : ℝ):EReal) from rfl),
    subderivative_distanceVA_of_mem hC hx,mem_inter_iff,mem_closedBall_zero_iff,
    mem_regularNormalCone_iff_inner_nonpos hx]
  simp only [distanceVA,EReal.coe_le_coe_iff]
  constructor
  · intro h
    refine ⟨fun w hw ↦ by simpa only [infDist_zero_of_mem hw] using h w,?_⟩
    have hh := (h v).trans (infDist_le_dist_of_mem (x := v) (isCone_tangentCone hx).1)
    rw [real_inner_self_eq_norm_sq,dist_zero_right] at hh
    nlinarith [sq_nonneg (‖v‖-1)]
  · rintro ⟨h,hv⟩ w
    obtain ⟨q,hq⟩ := projMapping_nonempty (isClosed_tangentCone C x) ⟨0,(isCone_tangentCone hx).1⟩ w
    calc
      ⟪v,w⟫_ℝ = ⟪v,w-q⟫_ℝ + ⟪v,q⟫_ℝ := by rw [inner_sub_right]; ring
      _ ≤ ‖v‖*‖w-q‖ := by linarith [h q hq.1,real_inner_le_norm v (w-q)]
      _ ≤ 1 * ‖w-q‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg _)
      _ = _ := by rw [one_mul,norm_sub_eq_infDist hq]

/-- Outside the set, regularity requires agreement of the unit directions
of every projection. -/
theorem mem_regularSubdifferential_distanceVA_of_notMem_iff (hC : IsClosed C)
    (hne : C.Nonempty) (hx : x ∉ C) :
    v ∈ regularSubdifferential (distanceVA C) x ↔ ∀ p ∈ projMapping C x, v = projectionDirection C x p := by
  rw [mem_regularSubdifferential_iff_inner_le_subderivative
    (show distanceVA C x = ((infDist x C : ℝ):EReal) from rfl)]
  constructor
  · intro h p hp
    have he (w : E) := EReal.coe_le_coe_iff.mp ((h w).trans (distance_subderivative_le_projection hx hp w))
    have hh := he (v-projectionDirection C x p)
    rw [← inner_projectionDirection] at hh
    have hzero := sub_nonpos.mpr hh
    rw [← inner_sub_left,real_inner_self_eq_norm_sq,sq_nonpos_iff,norm_eq_zero,sub_eq_zero] at hzero
    exact hzero
  · intro h w
    obtain ⟨p,hp,he,_⟩ := subderivative_distanceVA_of_notMem hC hne hx w
    rw [h p hp,inner_projectionDirection,he]

theorem regularSubdifferential_distanceVA_of_proj_singleton (hC : IsClosed C)
    (hne : C.Nonempty) (hx : x ∉ C) (hp : projMapping C x = {p}) :
    regularSubdifferential (distanceVA C) x = {projectionDirection C x p} := by
  ext v
  rw [mem_regularSubdifferential_distanceVA_of_notMem_iff hC hne hx,hp]
  simp

theorem regularSubdifferential_distanceVA_of_proj_not_singleton (hC : IsClosed C)
    (hne : C.Nonempty) (hx : x ∉ C) (hp : ∀ p, projMapping C x ≠ {p}) :
    regularSubdifferential (distanceVA C) x = ∅ := by
  apply eq_empty_of_forall_notMem
  intro v hv
  have H := (mem_regularSubdifferential_distanceVA_of_notMem_iff hC hne hx).mp hv
  obtain ⟨p,hp'⟩ := projMapping_nonempty hC hne x
  apply hp p
  apply eq_singleton_iff_unique_mem.mpr
  refine ⟨hp',fun q hq ↦ ?_⟩
  have he := (H q hq).symm.trans (H p hp')
  have hpos := (hC.notMem_iff_infDist_pos hne).mp hx
  have hh := congrArg (fun a : E ↦ (infDist x C) • a) he
  simpa [projectionDirection,smul_inv_smul₀ hpos.ne'] using hh

private theorem regular_distanceVA_projection (hC : IsClosed C) (hne : C.Nonempty)
    (hv : v ∈ regularSubdifferential (distanceVA C) x) :
    ∃ p ∈ projMapping C x, v ∈ regularNormalCone C p ∧ ‖v‖ ≤ 1 := by
  by_cases hx : x ∈ C
  · rw [regularSubdifferential_distanceVA_of_mem hC hx] at hv
    exact ⟨x,mem_projMapping_self hx,hv.1,mem_closedBall_zero_iff.mp hv.2⟩
  · obtain ⟨p,hp⟩ := projMapping_nonempty hC hne x
    rw [(mem_regularSubdifferential_distanceVA_of_notMem_iff hC hne hx).mp hv p hp]
    exact ⟨p,hp,nonneg_smul_sub_mem_regularNormalCone_of_mem_projMapping hp
      (inv_nonneg.mpr infDist_nonneg),(norm_projectionDirection hx hp).le⟩

/-- **Example 8.53.** The limiting subgradients at a feasible point are the
limiting normals clipped to the closed unit ball. -/
theorem subdifferential_distanceVA_of_mem (hC : IsClosed C) (hx : x ∈ C) :
    subdifferential (distanceVA C) x = normalCone C x ∩ closedBall 0 1 := by
  ext v
  constructor
  · intro hv
    obtain ⟨_,y,s,hy,_,hs,hs₀⟩ := mem_subdifferential_iff_exists_seq.mp hv
    choose p hp hn hb using fun n ↦ regular_distanceVA_projection hC ⟨x,hx⟩ (hs n)
    obtain ⟨p₀,hp₀,φ,hφ,hp'⟩ := exists_tendsto_subseq_projMapping hC ⟨x,hx⟩ hy hp
    have he := (mem_projMapping_iff_dist.mp hp₀).2
    rw [infDist_zero_of_mem hx,dist_eq_zero] at he
    subst p₀
    exact ⟨mem_normalCone_of_forall hx hp' (fun n ↦ hn (φ n)) (hs₀.comp hφ.tendsto_atTop),
      mem_closedBall_zero_iff.mpr (le_of_tendsto hs₀.norm (.of_forall hb))⟩
  · rintro ⟨⟨_,y,s,hyC,hy,hs,hs₀⟩,hv⟩
    let a (n : ℕ) := (max 1 ‖s n‖)⁻¹
    have ha (n : ℕ) : 0 < max 1 ‖s n‖ := lt_of_lt_of_le zero_lt_one (le_max_left ..)
    have h₀ := (tendsto_const_nhds (x := (1:ℝ))).max hs₀.norm
    rw [max_eq_left (mem_closedBall_zero_iff.mp hv)] at h₀
    have hlim : Tendsto a atTop (𝓝 1) := by simpa [a] using h₀.inv₀ one_ne_zero
    apply mem_subdifferential_iff_exists_seq.mpr
    refine ⟨⟨_,rfl⟩,y,fun n ↦ a n • s n,hy,((continuous_distanceVA C).tendsto _).comp hy,
      fun n ↦ ?_,by simpa using hlim.smul hs₀⟩
    rw [regularSubdifferential_distanceVA_of_mem hC (hyC n)]
    refine ⟨(isCone_regularNormalCone (hyC n)).2 (hs n) (inv_pos.mpr (ha n)),
      mem_closedBall_zero_iff.mpr ?_⟩
    rw [norm_smul_of_nonneg (inv_pos.mpr (ha n)).le]
    change (max 1 ‖s n‖)⁻¹ * ‖s n‖ ≤ 1
    rw [← div_eq_inv_mul,div_le_one (ha n)]
    exact le_max_right ..

/-- Moving inwards along a projection segment preserves its direction and
makes its endpoint the unique projection. -/
private theorem projectionDirection_mem_subdifferential_distanceVA (hC : IsClosed C)
    (hne : C.Nonempty) (hx : x ∉ C) (hp : p ∈ projMapping C x) :
    projectionDirection C x p ∈ subdifferential (distanceVA C) x := by
  let r (n : ℕ) := 1 - (1 / ((n:ℝ)+1))/2
  have hr (n : ℕ) : 0 < r n := by
    have hle : 1/((n:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [r]
    linarith
  have hr' (n : ℕ) : r n < 1 := sub_lt_self _ (by positivity)
  have hr₀ : Tendsto r atTop (𝓝 1) := by
    simpa [r] using (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat.div_const 2)
  let y n := p+r n • (x-p)
  have hy : Tendsto y atTop (𝓝 x) := by simpa [y] using (tendsto_const_nhds (x := p)).add (hr₀.smul_const (x-p))
  have hbase : p ∈ projMapping C (p+(1:ℝ) • (x-p)) := by simpa using hp
  have hP (n : ℕ) : projMapping C (y n) = {p} := projMapping_add_smul_eq_singleton_of_lt hbase (hr n) (hr' n)
  have hp' (n : ℕ) : p ∈ projMapping C (y n) := hP n ▸ mem_singleton _
  have hd₀ := (hC.notMem_iff_infDist_pos hne).mp hx
  have hd (n : ℕ) : infDist (y n) C = r n * infDist x C := by
    rw [← norm_sub_eq_infDist (hp' n)]
    simp only [y,add_sub_cancel_left,norm_smul_of_nonneg (hr n).le,norm_sub_eq_infDist hp]
  have he (n : ℕ) : projectionDirection C (y n) p = projectionDirection C x p := by
    simp only [projectionDirection,hd,y,add_sub_cancel_left,smul_smul,mul_inv_rev]
    rw [mul_assoc,inv_mul_cancel₀ (hr n).ne',mul_one]
  apply mem_subdifferential_iff_exists_seq.mpr
  refine ⟨⟨_,rfl⟩,y,fun _ ↦ projectionDirection C x p,hy,((continuous_distanceVA C).tendsto _).comp hy,
    fun n ↦ ?_,tendsto_const_nhds⟩
  have hout : y n ∉ C := (hC.notMem_iff_infDist_pos hne).mpr ((hd n) ▸ mul_pos (hr n) hd₀)
  rw [regularSubdifferential_distanceVA_of_proj_singleton hC hne hout (hP n),he]
  exact mem_singleton _

/-- **Example 8.53.** Outside a closed set, the limiting distance subgradients
are precisely the normalized displacements from its projections. -/
theorem subdifferential_distanceVA_of_notMem (hC : IsClosed C) (hne : C.Nonempty) (hx : x ∉ C) :
    subdifferential (distanceVA C) x = projectionDirection C x '' projMapping C x := by
  ext v
  constructor
  · intro hv
    obtain ⟨_,y,s,hy,_,hs,hs₀⟩ := mem_subdifferential_iff_exists_seq.mp hv
    choose p hp using fun n ↦ projMapping_nonempty hC hne (y n)
    obtain ⟨p₀,hp₀,φ,hφ,hp'⟩ := exists_tendsto_subseq_projMapping hC hne hy hp
    refine ⟨p₀,hp₀,?_⟩
    have hy' := hy.comp hφ.tendsto_atTop
    have hd := ((continuous_infDist_pt C).tendsto x).comp hy'
    have H := (hd.inv₀ ((hC.notMem_iff_infDist_pos hne).mp hx).ne').smul (hy'.sub hp')
    apply tendsto_nhds_unique H ((hs₀.comp hφ.tendsto_atTop).congr' ?_)
    filter_upwards [hy'.eventually (hC.isOpen_compl.mem_nhds hx)] with n hn
    exact (mem_regularSubdifferential_distanceVA_of_notMem_iff hC hne hn).mp (hs (φ n)) _ (hp _)
  · rintro ⟨p,hp,rfl⟩
    exact projectionDirection_mem_subdifferential_distanceVA hC hne hx hp

private theorem norm_le_one_of_mem_subdifferential_distanceVA (hC : IsClosed C) (hne : C.Nonempty)
    (hv : v ∈ subdifferential (distanceVA C) x) : ‖v‖ ≤ 1 := by
  obtain ⟨_,_,s,_,_,hs,hs₀⟩ := mem_subdifferential_iff_exists_seq.mp hv
  apply le_of_tendsto hs₀.norm (.of_forall fun n ↦ ?_)
  obtain ⟨_,_,_,hb⟩ := regular_distanceVA_projection hC hne (hs n)
  exact hb

/-- **Example 8.53.** Both horizon cones associated with the limiting
subgradients of a distance function are trivial at every point. -/
theorem horizonSubdifferential_distanceVA (hC : IsClosed C) (hne : C.Nonempty) (x : E) :
    horizonSubdifferential (distanceVA C) x = {0} ∧
      horizonCone (subdifferential (distanceVA C) x) = {0} := by
  constructor
  · ext v
    rw [mem_horizonSubdifferential_iff_zero_or_scaledSeq
      (show distanceVA C x = ((infDist x C : ℝ):EReal) from rfl),mem_singleton_iff]
    refine ⟨?_,Or.inl⟩
    rintro (h | ⟨y,s,t,_,hs,ht,ht₀,hlim⟩)
    · exact h
    · apply norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg v))
      apply le_of_tendsto_of_tendsto hlim.norm ht₀ (.of_forall fun n ↦ ?_)
      change ‖t n • s n‖ ≤ t n
      rw [norm_smul_of_nonneg (ht n).le]
      obtain ⟨_,_,_,hb⟩ := regular_distanceVA_projection hC hne (hs n)
      exact mul_le_of_le_one_right (ht n).le hb
  · apply isBounded_iff_horizonCone_eq_singleton_zero.mp
    exact (isBounded_closedBall (x := (0:E)) (r := 1)).subset fun v hv ↦
      mem_closedBall_zero_iff.mpr (norm_le_one_of_mem_subdifferential_distanceVA hC hne hv)

private theorem exists_distanceSubgradient_max (hC : IsClosed C) (hne : C.Nonempty) (x w : E) :
    ∃ v ∈ subdifferential (distanceVA C) x,
      regularSubderivative (distanceVA C) x w = (⟪v,w⟫_ℝ : EReal) ∧
      ∀ z ∈ subdifferential (distanceVA C) x, ⟪z,w⟫_ℝ ≤ ⟪v,w⟫_ℝ := by
  have hxc : distanceVA C x = ((infDist x C : ℝ):EReal) := rfl
  have hcomp : IsCompact (subdifferential (distanceVA C) x) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨(subdifferential_properties hxc).2.2.1,
      isBounded_iff_horizonCone_eq_singleton_zero.mpr (horizonSubdifferential_distanceVA hC hne x).2⟩
  have hnon : (subdifferential (distanceVA C) x).Nonempty := by
    by_cases hx : x ∈ C
    · rw [subdifferential_distanceVA_of_mem hC hx]
      exact ⟨0,(isCone_normalCone hx).1,by simp⟩
    · rw [subdifferential_distanceVA_of_notMem hC hne hx]
      exact (projMapping_nonempty hC hne x).image _
  obtain ⟨v,hv,hmax⟩ := hcomp.exists_isMaxOn hnon (continuous_id.inner continuous_const :
    Continuous (fun z : E ↦ ⟪z,w⟫_ℝ)).continuousOn
  have hl := isLocallyLscAt_of_isLocallyClosedAt_epigraph hxc (RW.IsClosed.isLocallyClosedAt
    (isClosed_epigraph_of_lsc_ereal _ (continuous_distanceVA C).lowerSemicontinuous) _)
  rw [regularSubderivative_eq_supportFunction_of_mem_polar hxc hl (by
    rw [(horizonSubdifferential_distanceVA hC hne x).1,polarCone_singleton_zero]; trivial)]
  exact ⟨v,hv,le_antisymm ((supportFunction_le_iff _ _ _).mpr fun z hz ↦
    EReal.coe_le_coe_iff.mpr (isMaxOn_iff.mp hmax z hz)) (inner_le_supportFunction hv w),isMaxOn_iff.mp hmax⟩

/-- **Example 8.53.** The regular subderivative at a point in the set is the
attained maximum over its unit limiting normals. -/
theorem regularSubderivative_distanceVA_of_mem (hC : IsClosed C) (hx : x ∈ C) (w : E) :
    ∃ v ∈ normalCone C x ∩ closedBall 0 1,
      regularSubderivative (distanceVA C) x w = (⟪v,w⟫_ℝ : EReal) ∧
      ∀ z ∈ normalCone C x ∩ closedBall 0 1, ⟪z,w⟫_ℝ ≤ ⟪v,w⟫_ℝ := by
  simpa only [subdifferential_distanceVA_of_mem hC hx] using exists_distanceSubgradient_max hC ⟨x,hx⟩ x w

/-- **Example 8.53.** Exterior projections realize the maximum for the
regular subderivative as well as the minimum for the ordinary one. -/
theorem regularSubderivative_distanceVA_of_notMem (hC : IsClosed C) (hne : C.Nonempty)
    (hx : x ∉ C) (w : E) : ∃ p ∈ projMapping C x,
      regularSubderivative (distanceVA C) x w = ((⟪x-p,w⟫_ℝ / infDist x C : ℝ):EReal) ∧
      ∀ q ∈ projMapping C x, ⟪x-q,w⟫_ℝ ≤ ⟪x-p,w⟫_ℝ := by
  obtain ⟨v,hv,he,hmax⟩ := exists_distanceSubgradient_max hC hne x w
  rw [subdifferential_distanceVA_of_notMem hC hne hx] at hv hmax
  obtain ⟨p,hp,rfl⟩ := hv
  refine ⟨p,hp,he.trans (congrArg ((↑) : ℝ → EReal) (inner_projectionDirection ..)),fun q hq ↦ ?_⟩
  have hh := hmax _ (mem_image_of_mem _ hq)
  simp only [inner_projectionDirection] at hh
  exact (div_le_div_iff_of_pos_right ((hC.notMem_iff_infDist_pos hne).mp hx)).mp hh

end RW
