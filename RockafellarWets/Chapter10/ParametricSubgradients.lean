/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subgradients in parametric minimization

The multiplier sets and the three subgradient inclusions of Theorem 10.13.
-/

import RockafellarWets.Chapter10.ParametricEpigraphProjection
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion
import RockafellarWets.Chapter7.EpiDistances

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {E P : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The intersection of regular multiplier sets at all minimizers. -/
def regularParametricMultipliers (f : WithLp 2 (E × P) → EReal) (u : P) : Set P :=
  {y | ∀ x ∈ parametricMinimizers f u,
    WithLp.toLp 2 ((0:E),y) ∈ regularSubdifferential f (WithLp.toLp 2 (x,u))}

/-- The union of limiting multiplier sets at all minimizers. -/
def parametricMultipliers (f : WithLp 2 (E × P) → EReal) (u : P) : Set P :=
  {y | ∃ x ∈ parametricMinimizers f u,
    WithLp.toLp 2 ((0:E),y) ∈ subdifferential f (WithLp.toLp 2 (x,u))}

/-- The union of horizon multiplier sets at all minimizers. -/
def horizonParametricMultipliers (f : WithLp 2 (E × P) → EReal) (u : P) : Set P :=
  {y | ∃ x ∈ parametricMinimizers f u,
    WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,u))}

/-- The closed cone of epigraph multipliers, simultaneously encoding
ordinary and horizon multiplier vectors. -/
def parametricNormalMultipliers (f : WithLp 2 (E × P) → EReal) (u : P) (a : ℝ) :
    Set (WithLp 2 (P × ℝ)) :=
  {q | ∃ x ∈ parametricMinimizers f u,
    parametricEpigraphProjection.adjoint q ∈
      normalCone (euclideanEpigraph f) (WithLp.toLp 2 (WithLp.toLp 2 (x,u),a))}

theorem parametricNormalMultipliers_eq_fiber_union {f : WithLp 2 (E × P) → EReal}
    {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    parametricNormalMultipliers f u a =
      ⋃ q ∈ euclideanEpigraph f ∩ parametricEpigraphProjection ⁻¹' {WithLp.toLp 2 (u,a)},
        (parametricEpigraphProjection (E := E) (P := P)).adjoint ⁻¹'
          normalCone (euclideanEpigraph f) q := by
  rw [parametricEpigraphProjection_fiber hu]
  ext v
  simp only [parametricNormalMultipliers,mem_setOf_eq,mem_iUnion,mem_image,mem_preimage]
  constructor
  · rintro ⟨x,hx,hv⟩
    exact ⟨_,⟨x,hx,rfl⟩,hv⟩
  · rintro ⟨q,⟨x,hx,rfl⟩,hv⟩
    exact ⟨x,hx,hv⟩

theorem isClosed_parametricNormalMultipliers {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    IsClosed (parametricNormalMultipliers f u a) := by
  rw [parametricNormalMultipliers_eq_fiber_union hu]
  simpa only [ContinuousLinearMap.fderiv] using
    isClosed_iUnion_adjoint_preimage_normalCone (isClosed_euclideanEpigraph hl)
      (parametricEpigraphProjection (E := E) (P := P)).contDiff
      (parametricEpigraphProjection_locally_bounded_inverse hb u a)

theorem isCone_parametricNormalMultipliers {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    IsCone (parametricNormalMultipliers f u a) := by
  rw [parametricNormalMultipliers_eq_fiber_union hu]
  have hm : WithLp.toLp 2 (u,a) ∈ parametricEpigraphProjection '' euclideanEpigraph f := by
    rw [← euclideanEpigraph_parametricValue hl hb]
    exact hu.le
  simpa only [ContinuousLinearMap.fderiv] using
    isCone_iUnion_adjoint_preimage_normalCone
      (F := parametricEpigraphProjection (E := E) (P := P)) hm

theorem mem_parametricNormalMultipliers_neg_one {f : WithLp 2 (E × P) → EReal}
    {u y : P} {a : ℝ} (hu : parametricValue f u = a) :
    WithLp.toLp 2 (y,(-1:ℝ)) ∈ parametricNormalMultipliers f u a ↔
      y ∈ parametricMultipliers f u := by
  constructor <;> rintro ⟨x,hx,h⟩ <;> refine ⟨x,hx,?_⟩
  · rw [parametricEpigraphProjection_adjoint] at h
    exact (mem_subdifferential_iff_epigraph_normal ((mem_parametricMinimizers.mp hx).1.trans hu)).mpr h
  · rw [parametricEpigraphProjection_adjoint]
    exact (mem_subdifferential_iff_epigraph_normal ((mem_parametricMinimizers.mp hx).1.trans hu)).mp h

theorem mem_parametricNormalMultipliers_zero {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) {u y : P} {a : ℝ} (hu : parametricValue f u = a) :
    WithLp.toLp 2 (y,(0:ℝ)) ∈ parametricNormalMultipliers f u a ↔
      y ∈ horizonParametricMultipliers f u := by
  have hlocal (x : E) (hx : x ∈ parametricMinimizers f u) :
      IsLocallyLscAt f (WithLp.toLp 2 (x,u)) :=
    isLocallyLscAt_of_isLocallyClosedAt_epigraph ((mem_parametricMinimizers.mp hx).1.trans hu)
      (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal f hl) _)
  constructor <;> rintro ⟨x,hx,h⟩ <;> refine ⟨x,hx,?_⟩
  · rw [parametricEpigraphProjection_adjoint] at h
    exact (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc (hlocal x hx)
      ((mem_parametricMinimizers.mp hx).1.trans hu)).mpr h
  · rw [parametricEpigraphProjection_adjoint]
    exact horizontal_normal_of_mem_horizonSubdifferential ((mem_parametricMinimizers.mp hx).1.trans hu) h

/-- **Theorem 10.13**: the ordinary and horizon multiplier unions are closed. -/
theorem isClosed_parametricMultipliers {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    IsClosed (parametricMultipliers f u) ∧ IsClosed (horizonParametricMultipliers f u) := by
  have hc := isClosed_parametricNormalMultipliers hl hb hu
  constructor
  · have he : parametricMultipliers f u =
        (fun y : P ↦ WithLp.toLp 2 (y,(-1:ℝ))) ⁻¹' parametricNormalMultipliers f u a := by
      ext y
      exact (mem_parametricNormalMultipliers_neg_one hu).symm
    rw [he]
    exact hc.preimage ((l2ProdEquiv P).symm.continuous.comp (continuous_id.prodMk continuous_const))
  · have he : horizonParametricMultipliers f u =
        (fun y : P ↦ WithLp.toLp 2 (y,(0:ℝ))) ⁻¹' parametricNormalMultipliers f u a := by
      ext y
      exact (mem_parametricNormalMultipliers_zero hl hu).symm
    rw [he]
    exact hc.preimage ((l2ProdEquiv P).symm.continuous.comp (continuous_id.prodMk continuous_const))

/-- **Theorem 10.13**, the regular multiplier intersection is closed and convex. -/
theorem regularParametricMultipliers_closed_convex {f : WithLp 2 (E × P) → EReal}
    {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    IsClosed (regularParametricMultipliers f u) ∧ Convex ℝ (regularParametricMultipliers f u) := by
  let A : P →L[ℝ] WithLp 2 (E × P) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ E P)
  have he : regularParametricMultipliers f u =
      ⋂ x ∈ parametricMinimizers f u, A ⁻¹' regularSubdifferential f (WithLp.toLp 2 (x,u)) := by
    ext y
    simp only [regularParametricMultipliers,mem_setOf_eq,mem_iInter,mem_preimage]
    rfl
  rw [he]
  constructor
  · exact isClosed_biInter fun x hx ↦ ((subdifferential_properties
      ((mem_parametricMinimizers.mp hx).1.trans hu)).1).preimage A.continuous
  · exact convex_iInter fun x ↦ convex_iInter fun hx ↦
      ((subdifferential_properties ((mem_parametricMinimizers.mp hx).1.trans hu)).2.1).linear_preimage A.toLinearMap

/-- The regular multiplier intersection lies in the limiting union. -/
theorem regularParametricMultipliers_subset {f : WithLp 2 (E × P) → EReal}
    {u : P} (hne : (parametricMinimizers f u).Nonempty) :
    regularParametricMultipliers f u ⊆ parametricMultipliers f u := by
  obtain ⟨x,hx⟩ := hne
  intro y hy
  exact ⟨x,hx,regularSubdifferential_subset_subdifferential _ _ (hy x hx)⟩

/-- **Theorem 10.13**, regular subgradients are multipliers at every minimizer. -/
theorem regularSubdifferential_parametricValue_subset {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    regularSubdifferential (parametricValue f) u ⊆ regularParametricMultipliers f u := by
  intro y hy x hx
  have hxval := (mem_parametricMinimizers.mp hx).1.trans hu
  have hn := (mem_regularSubdifferential_iff_epigraph_normal hu).mp hy
  rw [euclideanEpigraph_parametricValue hl hb] at hn
  have hback := adjoint_mem_regularNormalCone_of_mem_image
    (parametricEpigraphProjection (E := E) (P := P)).hasFDerivAt
    (show WithLp.toLp 2 (WithLp.toLp 2 (x,u),a) ∈ euclideanEpigraph f from hxval.le) hn
  rw [parametricEpigraphProjection_adjoint] at hback
  exact (mem_regularSubdifferential_iff_epigraph_normal hxval).mpr hback

/-- The limiting epigraph normal lifts to some optimal decision. -/
theorem normalCone_parametricValue_subset {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    normalCone (euclideanEpigraph (parametricValue f)) (WithLp.toLp 2 (u,a)) ⊆
      parametricNormalMultipliers f u a := by
  rw [euclideanEpigraph_parametricValue hl hb,parametricNormalMultipliers_eq_fiber_union hu]
  simpa only [ContinuousLinearMap.fderiv] using normalCone_image_subset_iUnion
    (isClosed_euclideanEpigraph hl) (parametricEpigraphProjection (E := E) (P := P)).contDiff
    (parametricEpigraphProjection_locally_bounded_inverse hb u a)

/-- **Theorem 10.13**, limiting subgradients occur at some optimal decision. -/
theorem subdifferential_parametricValue_subset {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    subdifferential (parametricValue f) u ⊆ parametricMultipliers f u := by
  intro y hy
  exact (mem_parametricNormalMultipliers_neg_one hu).mp
    (normalCone_parametricValue_subset hl hb hu ((mem_subdifferential_iff_epigraph_normal hu).mp hy))

/-- **Theorem 10.13**, horizon subgradients occur at some optimal decision. -/
theorem horizonSubdifferential_parametricValue_subset {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    horizonSubdifferential (parametricValue f) u ⊆ horizonParametricMultipliers f u := by
  intro y hy
  exact (mem_parametricNormalMultipliers_zero hl hu).mp
    (normalCone_parametricValue_subset hl hb hu (horizontal_normal_of_mem_horizonSubdifferential hu hy))

/-- **Theorem 10.13**, the horizon of the limiting multiplier set is
contained in the horizon multiplier set. -/
theorem horizonCone_parametricMultipliers_subset {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) :
    horizonCone (parametricMultipliers f u) ⊆ horizonParametricMultipliers f u := by
  have hc := isClosed_parametricNormalMultipliers hl hb hu
  have hk := isCone_parametricNormalMultipliers hl hb hu
  intro y hy
  apply (mem_parametricNormalMultipliers_zero hl hu).mp
  by_cases hy0 : y = 0
  · subst y
    exact hk.1
  have has : y ∈ asymptoticCone ℝ (parametricMultipliers f u) := by
    simpa only [horizonCone,mem_insert_iff,hy0,false_or] using hy
  obtain ⟨cs,vs,hcs,hvs,hpos,hmem⟩ := exists_seq_pos_smul_of_mem_asymptoticCone has
  have hN (n : ℕ) : WithLp.toLp 2 (vs n,-(cs n)⁻¹) ∈ parametricNormalMultipliers f u a := by
    have hn := hk.2 ((mem_parametricNormalMultipliers_neg_one hu).mpr (hmem n))
      (inv_pos.mpr (hpos n))
    convert hn using 1
    apply WithLp.ofLp_injective
    ext <;> simp [smul_smul,smul_eq_mul,(hpos n).ne']
  have ht : Tendsto (fun n ↦ WithLp.toLp 2 (vs n,-(cs n)⁻¹)) atTop
      (𝓝 (WithLp.toLp 2 (y,(0:ℝ)))) := by
    apply (l2ProdEquiv P).symm.continuous.continuousAt.tendsto.comp
    exact hvs.prodMk_nhds (by simpa using hcs.inv_tendsto_atTop.neg)
  exact hc.mem_of_tendsto ht (Eventually.of_forall hN)

end

end RW
