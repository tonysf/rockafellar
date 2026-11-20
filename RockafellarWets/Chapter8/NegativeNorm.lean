/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: The negative Euclidean norm at its cusp
-/

import RockafellarWets.Chapter8.SupportFunctions
import RockafellarWets.Chapter8.RegularSubgradientBridge
import RockafellarWets.Chapter8.SubgradientRelationships
import RockafellarWets.Chapter7.SubdifferentialRegularity
import RockafellarWets.Chapter3.CosmicSetClosure

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The negative norm in Exercise 8.27, with its extended-real codomain. -/
noncomputable def negNorm (x : E) : EReal := ((-‖x‖ : ℝ) : EReal)

theorem positivelyHomogeneous_negNorm : PositivelyHomogeneous (negNorm (E := E)) := by
  refine ⟨by simp [negNorm], fun {x t} ht ↦ ?_⟩
  rw [negNorm, negNorm, ← EReal.coe_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_neg]

theorem not_sublinear_negNorm [Nontrivial E] : ¬ Sublinear (negNorm (E := E)) := by
  obtain ⟨u,hu⟩ := exists_ne (0:E)
  intro hs
  have h := hs.2 u (-u)
  simp only [add_neg_cancel, negNorm, norm_zero, neg_zero, norm_neg, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h
  linarith [norm_pos_iff.2 hu]

theorem negNorm_not_supportFunction [Nontrivial E] (C : Set E) : negNorm ≠ supportFunction C :=
  fun he ↦ not_sublinear_negNorm (he ▸ sublinear_supportFunction C)

theorem subderivative_negNorm_zero (w : E) : subderivative negNorm 0 w = negNorm w := by
  apply HasSemiderivative.subderivative_eq
  refine ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _, ?_⟩
  have hc : Continuous (negNorm (E := E)) := continuous_coe_real_ereal.comp continuous_norm.neg
  apply ((hc.tendsto w).comp tendsto_snd).congr'
  filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t)] with p hp
  rw [differenceQuotient_eq_coe (f := negNorm) rfl rfl]
  simp [negNorm, norm_smul, Real.norm_eq_abs, abs_of_pos hp, hp.ne']

private theorem subderivative_negNorm_of_ne_zero {x : E} (hx : x ≠ 0) (w : E) :
    subderivative negNorm x w = (⟪-(‖x‖⁻¹ • x),w⟫_ℝ : EReal) := by
  apply HasSemiderivative.subderivative_eq
  refine ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _, ?_⟩
  let q := fun p : ℝ × E ↦ -(2*⟪x,p.2⟫_ℝ + p.1*‖p.2‖^2)/(‖x+p.1 • p.2‖+‖x‖)
  have hn := norm_pos_iff.2 hx
  have hcont : ContinuousAt q (0,w) := by
    dsimp [q]
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simpa using (show ‖x‖ + ‖x‖ ≠ 0 by linarith)
  have hlim : Tendsto q (𝓝[>] (0:ℝ) ×ˢ 𝓝 w) (𝓝 (q (0,w))) :=
    hcont.tendsto.mono_left (by rw [nhds_prod_eq]; exact prod_mono nhdsWithin_le_nhds le_rfl)
  have he : q (0,w) = ⟪-(‖x‖⁻¹ • x),w⟫_ℝ := by
    dsimp [q]; simp [inner_neg_left, real_inner_smul_left]; field_simp; ring
  rw [← he]
  apply (EReal.tendsto_coe.2 hlim).congr'
  filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t)] with p hp
  rw [differenceQuotient_eq_coe (f := negNorm) rfl rfl]
  apply congrArg ((↑) : ℝ → EReal)
  have hden : ‖x+p.1 • p.2‖+‖x‖ ≠ 0 := by positivity
  have hsq := norm_add_sq_real x (p.1 • p.2)
  rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hp] at hsq
  dsimp [q]
  field_simp [hden, hp.ne']
  nlinarith only [hsq]

variable [FiniteDimensional ℝ E]

theorem negNorm_not_regular_zero [Nontrivial E] :
    ¬IsSubdifferentiallyRegularAt (negNorm (E := E)) 0 := by
  intro hr
  have he := funext (subderivative_negNorm_zero (E := E))
  exact not_sublinear_negNorm (he ▸ hr.sublinear_subderivative (fun w ↦ by rw [he]; exact EReal.coe_ne_bot _))

omit [FiniteDimensional ℝ E] in
private theorem regularSubdifferential_negNorm_zero [Nontrivial E] :
    regularSubdifferential (negNorm (E := E)) 0 = ∅ := by
  apply eq_empty_of_forall_notMem
  intro v hv
  obtain ⟨w,hw⟩ := exists_ne (0:E)
  have h (u : E) := EReal.coe_le_coe_iff.1
    ((inner_le_subderivative_of_mem_regularSubdifferential hv u).trans_eq (subderivative_negNorm_zero u))
  have h₁ := h w
  have h₂ := h (-w)
  rw [inner_neg_right, norm_neg] at h₂
  linarith [norm_pos_iff.2 hw]

private theorem regularSubdifferential_negNorm_ne_zero {x : E} (hx : x ≠ 0) :
    regularSubdifferential negNorm x = {-(‖x‖⁻¹ • x)} := by
  ext v
  rw [mem_regularSubdifferential_iff_inner_le_subderivative (f := negNorm) rfl]
  simp only [subderivative_negNorm_of_ne_zero hx, EReal.coe_le_coe_iff, mem_singleton_iff]
  refine ⟨fun h ↦ ext_inner_right ℝ fun w ↦ le_antisymm (h w) ?_, fun he _ ↦ he ▸ le_rfl⟩
  simpa only [inner_neg_right, neg_le_neg_iff] using h (-w)

private theorem regularSubdifferential_negNorm_subset_sphere [Nontrivial E] (x : E) :
    regularSubdifferential negNorm x ⊆ sphere 0 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [regularSubdifferential_negNorm_zero]; exact empty_subset _
  · rw [regularSubdifferential_negNorm_ne_zero hx, singleton_subset_iff, mem_sphere_zero_iff_norm]
    simp [norm_smul, norm_ne_zero_iff.2 hx]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem attentiveNhds_negNorm (x : E) : attentiveNhds negNorm x = 𝓝 x := by
  apply inf_eq_left.2
  rw [← map_le_iff_le_comap]
  exact (continuous_coe_real_ereal.comp continuous_norm.neg).tendsto x

/-- **Exercise 8.27.** At nonzero points the negative norm has its classical
gradient as its unique limiting subgradient. -/
theorem subdifferential_negNorm_ne_zero {x : E} (hx : x ≠ 0) :
    subdifferential negNorm x = {-(‖x‖⁻¹ • x)} := by
  refine Subset.antisymm ?_ ((regularSubdifferential_negNorm_ne_zero hx) ▸
    regularSubdifferential_subset_subdifferential negNorm x)
  rw [subdifferential_of_finite (f := negNorm) rfl, attentiveNhds_negNorm]
  let p := fun y : E ↦ -(‖y‖⁻¹ • y)
  have hcont : ContinuousAt p x := ((continuous_norm.continuousAt.inv₀
    (norm_ne_zero_iff.2 hx)).smul continuousAt_id).neg
  intro v hv
  by_contra hnot
  obtain ⟨U,V,hU,hV,hvU,hpV,hdisj⟩ := t2_separation (show v ≠ p x from hnot)
  apply (hv U (hU.mem_nhds hvU))
  filter_upwards [hcont (hV.mem_nhds hpV), isOpen_ne.mem_nhds hx] with y hy hy0
  rintro ⟨z,hz,hzU⟩
  rw [regularSubdifferential_negNorm_ne_zero hy0, mem_singleton_iff] at hz
  exact (disjoint_left.1 hdisj hzU) (hz ▸ hy)

/-- **Exercise 8.27.** At the origin the limiting subdifferential of the
negative norm is exactly the boundary of the unit ball. -/
theorem subdifferential_negNorm_zero [Nontrivial E] :
    subdifferential (negNorm (E := E)) 0 = frontier (closedBall 0 1) := by
  rw [frontier_closedBall _ one_ne_zero, subdifferential_of_finite (f := negNorm) rfl, attentiveNhds_negNorm]
  refine Subset.antisymm (outerSetLimitAlong_subset_of_eventually_subset isClosed_sphere
    (.of_forall regularSubdifferential_negNorm_subset_sphere)) ?_
  intro v hv U hU
  have hnorm := mem_sphere_zero_iff_norm.1 hv
  have hv0 : v ≠ 0 := by intro he; simp [he] at hnorm
  have hlim : Tendsto (fun t : ℝ ↦ -(t • v)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (((continuous_id.smul continuous_const).neg.tendsto 0).mono_left nhdsWithin_le_nhds :
      Tendsto (fun t : ℝ ↦ -(t • v)) _ _)
  apply hlim.frequently
  apply Filter.Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  have hy : -(t • v) ≠ 0 := neg_ne_zero.2 (smul_ne_zero ht'.ne' hv0)
  refine ⟨v, ?_, mem_of_mem_nhds hU⟩
  rw [regularSubdifferential_negNorm_ne_zero hy, mem_singleton_iff]
  simp [norm_smul, hnorm, abs_of_pos ht', ht'.ne', smul_smul]

/-- **Exercise 8.27.** All horizon subgradients of the negative norm vanish. -/
theorem horizonSubdifferential_negNorm (x : E) : horizonSubdifferential negNorm x = {0} := by
  rw [horizonSubdifferential_of_finite (f := negNorm) rfl]
  refine Subset.antisymm ?_ (singleton_subset_iff.2 (isCone_horizonOuterSetLimitAlong _ _).1)
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact fun v _ ↦ Subsingleton.elim v 0
  letI := hE
  let B := sphere (0:E) 1
  have hc := closure_cosmicSet_zero_of_isBounded (isBounded_sphere (x := (0:E)) (r := 1))
  have hZ : IsClosed (cosmicSet B ({0} : Set E)) := by
    rw [← closure_eq_iff_isClosed, hc, isClosed_sphere.closure_eq]
  have hsub := outerSetLimitAlong_subset_of_eventually_subset (l := attentiveNhds negNorm x) hZ
    (Filter.Eventually.of_forall (fun y ↦ cosmicSet_mono (regularSubdifferential_negNorm_subset_sphere y)
      (Subset.rfl : ({0}:Set E) ⊆ {0})))
  exact (cosmicDirectionCone_mono hsub).trans_eq (cosmicDirectionCone_cosmicSet ⟨by simp, by simp⟩)

end RW
