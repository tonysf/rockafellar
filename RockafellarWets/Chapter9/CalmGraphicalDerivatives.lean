/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Graphical derivatives under calmness

Proposition 9.24(a), including the sharp one-point modulus.
-/

import RockafellarWets.Chapter9.AubinGraphicalDerivatives
import RockafellarWets.Chapter9.HomogeneousMappingNorms
import RockafellarWets.Chapter8.SingleValuedSemiderivatives

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}

/-- A one-point local Lipschitz estimate. -/
def CalmAtWith (k : ℝ≥0) (f : E → F) (x : E) : Prop :=
  ∀ᶠ y in nhds x, dist (f y) (f x) ≤ k * dist y x

def CalmAt (f : E → F) (x : E) : Prop := ∃ k : ℝ≥0, CalmAtWith k f x

/-- The exact one-point modulus, with value infinity when no calmness
constant exists. -/
noncomputable def calmnessModulus (f : E → F) (x : E) : ℝ≥0∞ :=
  ⨅ k : {k : ℝ≥0 // CalmAtWith k f x}, ((k:ℝ≥0):ℝ≥0∞)

theorem calmnessModulus_le {k : ℝ≥0} (h : CalmAtWith k f x) :
    calmnessModulus f x ≤ (k:ℝ≥0∞) :=
  iInf_le (fun k : {k : ℝ≥0 // CalmAtWith k f x} ↦ ((k:ℝ≥0):ℝ≥0∞)) ⟨k,h⟩

theorem calmnessModulus_eq_limsup (f : E → F) (x : E) :
    calmnessModulus f x = limsup (fun y ↦ edist (f y) (f x) / edist y x) (𝓝[≠] x) := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨k,hk,hk'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    have he := eventually_nhdsWithin_iff.mp (eventually_lt_of_limsup_lt hk)
    apply hk'.not_ge (calmnessModulus_le (k := k) ?_)
    filter_upwards [he] with y hy
    by_cases hyx : y = x
    · simp [hyx]
    · have hh := (ENNReal.div_le_iff (edist_eq_zero.not.mpr hyx) (edist_ne_top y x)).mp (hy hyx).le
      have hh' : ENNReal.ofReal (dist (f y) (f x)) ≤ ENNReal.ofReal (k * dist y x) := by
        simpa [edist_dist,ENNReal.ofReal_mul] using hh
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg k.2 dist_nonneg)).mp hh'
  · apply le_iInf
    intro k
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [mem_nhdsWithin_of_mem_nhds k.property] with y hy
    apply ENNReal.div_le_of_le_mul
    simpa [edist_dist,ENNReal.ofReal_mul] using ENNReal.ofReal_le_ofReal hy

theorem calmnessModulus_le_lipschitzModulus (f : E → F) (x : E) :
    calmnessModulus f x ≤ lipschitzModulus f x := by
  apply le_iInf
  intro k
  obtain ⟨U,hU,hL⟩ := k.property
  rw [nhdsWithin_univ] at hU
  apply calmnessModulus_le (k := k.val)
  filter_upwards [hU] with y hy
  exact hL.dist_le_mul y hy x (mem_of_mem_nhds hU)

theorem StrictlyContinuousAt.calmAt (h : StrictlyContinuousAt f x) : CalmAt f x := by
  obtain ⟨k,U,hU,hL⟩ := strictlyContinuousAt_iff.mp h
  exact ⟨k,Filter.mem_of_superset hU (fun y hy ↦ hL.dist_le_mul y hy x (mem_of_mem_nhds hU))⟩

theorem calmAt_iff_mappingLinearGrowth :
    CalmAt f x ↔ HasMappingLinearGrowth (svSingleton f) x (f x) := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,k.2,?_⟩
    filter_upwards [hk] with y hy
    exact ⟨singleton_nonempty _,fun v hv ↦ by simpa [show v = f y from hv,dist_eq_norm] using hy⟩
  · rintro ⟨k,hk,h⟩
    refine ⟨⟨k,hk⟩,?_⟩
    filter_upwards [h] with y hy
    simpa only [dist_eq_norm] using hy.2 (f y) rfl

/-- One-point bounds pass to the whole graphical derivative. -/
theorem CalmAtWith.graphicalDerivative_norm_le {k : ℝ≥0} (h : CalmAtWith k f x)
    {w : E} {z : F} (hz : z ∈ graphicalDerivative (svSingleton f) x (f x) w) :
    ‖z‖ ≤ k * ‖w‖ := by
  have hz' : (w,z) ∈ tangentCone (svGraph (svSingleton f)) (x,f x) := by
    change (w,z) ∈ svGraph (graphicalDerivative (svSingleton f) x (f x)) at hz
    rwa [svGraph_graphicalDerivative] at hz
  obtain ⟨p,t,hp,hpt,ht,htt,hq⟩ := hz'
  have he : ∀ᶠ n in atTop,
      ‖(t n)⁻¹ • ((p n).2-f x)‖ ≤ k*‖(t n)⁻¹ • ((p n).1-x)‖ := by
    filter_upwards [hpt.fst_nhds.eventually h] with n hn
    have he := mem_singleton_iff.mp (hp n)
    rw [he,norm_smul_of_nonneg (inv_pos.mpr (ht n)).le,
      norm_smul_of_nonneg (inv_pos.mpr (ht n)).le]
    simp only [dist_eq_norm] at hn
    nlinarith [mul_le_mul_of_nonneg_left hn (inv_pos.mpr (ht n)).le]
  exact le_of_tendsto_of_tendsto hq.snd_nhds.norm (hq.fst_nhds.norm.const_mul (k:ℝ)) he

theorem svOsc_graphicalDerivative_singleton (f : E → F) (x : E) :
    SvOsc (graphicalDerivative (svSingleton f) x (f x)) := by
  apply isClosed_svGraph_iff_svOsc.mp
  rw [svGraph_graphicalDerivative]
  exact isClosed_tangentCone _ _

theorem svPositivelyHomogeneous_graphicalDerivative {S : E → Set F} {x : E} {u : F}
    (hu : u ∈ S x) : SvPositivelyHomogeneous (graphicalDerivative S x u) :=
  svPositivelyHomogeneous_iff_isCone_svGraph.mpr ((svGraph_graphicalDerivative S x u) ▸
    isCone_tangentCone (show (x,u) ∈ svGraph S from hu))

variable [FiniteDimensional ℝ F]

/-- **Proposition 9.24(a)**: every derivative fiber is nonempty under calmness. -/
theorem CalmAt.graphicalDerivative_nonempty (h : CalmAt f x) (w : E) :
    (graphicalDerivative (svSingleton f) x (f x) w).Nonempty := by
  obtain ⟨k,hk⟩ := h
  let q := fun t : ℝ ↦ t⁻¹ • (f (x+t•w)-f x)
  have ht : Tendsto (fun t : ℝ ↦ x+t•w) (𝓝[>] (0:ℝ)) (nhds x) := by
    simpa using (tendsto_const_nhds (x := x)).add (((tendsto_id : Tendsto (fun t : ℝ ↦ t) (nhds 0) (nhds 0)).mono_left nhdsWithin_le_nhds).smul_const w)
  have hb : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖q t‖ ≤ k*‖w‖ := by
    filter_upwards [ht.eventually hk,self_mem_nhdsWithin] with t ht htpos
    have htpos' : 0 < t := htpos
    rw [dist_eq_norm,dist_eq_norm,add_sub_cancel_left,norm_smul_of_nonneg htpos'.le] at ht
    dsimp [q]
    rw [norm_smul_of_nonneg (inv_pos.mpr htpos').le,inv_mul_le_iff₀ htpos']
    nlinarith only [ht]
  have hfreq : ∃ᶠ t in 𝓝[>] (0:ℝ),
      (mappingDifferenceQuotient (svSingleton f) x (f x) t w ∩ closedBall 0 (k*‖w‖)).Nonempty :=
    (hb.mono fun t ht ↦ ⟨q t,⟨f (x+t•w),rfl,rfl⟩,mem_closedBall_zero_iff.mpr ht⟩).frequently
  obtain ⟨z,hz,-⟩ := outerSetLimitAlong_inter_nonempty_of_frequently (isCompact_closedBall _ _) hfreq
  exact ⟨z,quotient_outer_fixed_subset_graphicalDerivative _ _ _ _ hz⟩

/-- **Proposition 9.24(a)**: calmness makes the graphical derivative locally
bounded everywhere. -/
theorem CalmAt.graphicalDerivative_locallyBounded (h : CalmAt f x) :
    SvLocallyBounded (graphicalDerivative (svSingleton f) x (f x)) := by
  obtain ⟨k,hk⟩ := h
  have hhom := svPositivelyHomogeneous_graphicalDerivative (S := svSingleton f) (x := x) (show f x ∈ svSingleton f x from rfl)
  apply hhom.svLocallyBounded_of_svOuterNorm_lt_top
  exact (hhom.svOuterNorm_le_iff.mpr (fun _ _ hz ↦ hk.graphicalDerivative_norm_le hz)).trans_lt ENNReal.coe_lt_top

variable [FiniteDimensional ℝ E]

private theorem calmAtWith_of_graphical_bound (h : CalmAt f x) {k l : ℝ≥0} (hkl : k < l)
    (hb : ∀ w z, z ∈ graphicalDerivative (svSingleton f) x (f x) w → ‖z‖ ≤ k*‖w‖) :
    CalmAtWith l f x := by
  classical
  obtain ⟨K,hK⟩ := h
  by_contra hno
  have hpick (n : ℕ) : ∃ y : E, dist y x < 1/((n:ℝ)+1) ∧
      dist (f y) (f x) ≤ K*dist y x ∧ l*dist y x < dist (f y) (f x) := by
    obtain ⟨y,hy⟩ := ((not_eventually.mp hno).and_eventually
      (hK.and (ball_mem_nhds x (show 0 < 1/((n:ℝ)+1) by positivity)))).exists
    exact ⟨y,hy.2.2,hy.2.1,lt_of_not_ge hy.1⟩
  choose y hsmall hbound hbad using hpick
  have hy : Tendsto y atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hsmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  let t := fun n ↦ ‖y n-x‖
  have ht (n : ℕ) : 0 < t n := by
    apply norm_pos_iff.mpr
    intro he
    have hyx := sub_eq_zero.mp he
    simpa [hyx] using hbad n
  have htt : Tendsto t atTop (nhds 0) := by simpa only [sub_self,norm_zero] using (hy.sub (tendsto_const_nhds (x := x))).norm
  let v := fun n ↦ (t n)⁻¹ • (y n-x)
  let z := fun n ↦ (t n)⁻¹ • (f (y n)-f x)
  have hv (n : ℕ) : ‖v n‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp (ht n))
  have hz (n : ℕ) : ‖z n‖ ≤ K := by
    dsimp [z]
    rw [norm_smul_of_nonneg (inv_pos.mpr (ht n)).le,inv_mul_le_iff₀ (ht n)]
    simpa only [t,dist_eq_norm,mul_comm] using hbound n
  have hzl (n : ℕ) : (l:ℝ) < ‖z n‖ := by
    dsimp [z]
    rw [norm_smul_of_nonneg (inv_pos.mpr (ht n)).le,lt_inv_mul_iff₀ (ht n)]
    simpa only [t,dist_eq_norm,mul_comm] using hbad n
  have hmem (n : ℕ) : (v n,z n) ∈ sphere (0:E) 1 ×ˢ closedBall (0:F) (K:ℝ) :=
    ⟨mem_sphere_zero_iff_norm.mpr (hv n),mem_closedBall_zero_iff.mpr (hz n)⟩
  obtain ⟨⟨w,b⟩,hwb,φ,hφ,hlim⟩ :=
    ((isCompact_sphere (0:E) 1).prod (isCompact_closedBall (0:F) (K:ℝ))).tendsto_subseq hmem
  have hD : b ∈ graphicalDerivative (svSingleton f) x (f x) w := by
    change (w,b) ∈ svGraph (graphicalDerivative (svSingleton f) x (f x))
    rw [svGraph_graphicalDerivative]
    exact mem_tangentCone_of_forall (xs := fun n ↦ (y (φ n),f (y (φ n))))
      (τs := t ∘ φ) (fun _ ↦ rfl) (fun n ↦ ht _) (htt.comp hφ.tendsto_atTop) hlim
  have hlo : (l:ℝ) ≤ ‖b‖ := le_of_tendsto_of_tendsto tendsto_const_nhds hlim.snd_nhds.norm
    (.of_forall fun n ↦ (hzl (φ n)).le)
  have hhi := hb w b hD
  rw [mem_sphere_zero_iff_norm.mp hwb.1,mul_one] at hhi
  exact (not_le_of_gt (show (k:ℝ) < l from hkl)) (hlo.trans hhi)

/-- **Proposition 9.24(a)**, the exact outer norm. -/
theorem CalmAt.svOuterNorm_graphicalDerivative (h : CalmAt f x) :
    svOuterNorm (graphicalDerivative (svSingleton f) x (f x)) = calmnessModulus f x := by
  have hhom := svPositivelyHomogeneous_graphicalDerivative (S := svSingleton f) (x := x) (show f x ∈ svSingleton f x from rfl)
  apply le_antisymm
  · apply le_iInf
    intro k
    exact hhom.svOuterNorm_le_iff.mpr (fun _ _ hz ↦ k.property.graphicalDerivative_norm_le hz)
  · by_contra hno
    obtain ⟨l,hNl,hlM⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hno)
    let k := (svOuterNorm (graphicalDerivative (svSingleton f) x (f x))).toNNReal
    have hk : (k:ℝ≥0∞) = svOuterNorm (graphicalDerivative (svSingleton f) x (f x)) :=
      ENNReal.coe_toNNReal (ne_top_of_lt hNl)
    have hkl : k < l := ENNReal.coe_lt_coe.mp (hk.symm ▸ hNl)
    have hb := hhom.svOuterNorm_le_iff.mp (show svOuterNorm _ ≤ (k:ℝ≥0∞) from hk.symm.le)
    have hc := calmAtWith_of_graphical_bound h hkl hb
    exact hlM.not_ge (calmnessModulus_le hc)

end RW
