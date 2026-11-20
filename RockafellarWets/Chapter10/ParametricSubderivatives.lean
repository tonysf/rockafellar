/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subderivative bounds in parametric minimization
-/

import RockafellarWets.Chapter10.ParametricSubgradients
import RockafellarWets.Chapter8.CalmSubgradients
import RockafellarWets.Chapter8.RegularSubderivativeSupport
import RockafellarWets.Chapter7.TotalEpiProjection

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {E P : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- Epigraph projection commutes with closure even without attainment. -/
theorem closure_euclideanEpigraph_parametricValue (f : WithLp 2 (E × P) → EReal) :
    closure (euclideanEpigraph (parametricValue f)) =
      closure (parametricEpigraphProjection '' euclideanEpigraph f) := by
  change closure ((l2ProdEquiv P) ⁻¹' epigraph (valueFunction (fun q ↦ f (WithLp.toLp 2 q)))) = _
  have hcl (S : Set (P × ℝ)) :
      (l2ProdEquiv P) ⁻¹' closure S = closure ((l2ProdEquiv P) ⁻¹' S) :=
    (l2ProdEquiv P).toHomeomorph.preimage_closure S
  rw [← hcl,closure_epigraph_valueFunction,hcl]
  congr 1
  ext q
  constructor
  · rintro ⟨⟨⟨x,u⟩,a⟩,hx,heq⟩
    exact ⟨WithLp.toLp 2 (WithLp.toLp 2 (x,u),a),hx,congrArg (WithLp.toLp 2) heq⟩
  · rintro ⟨q,hq,rfl⟩
    exact ⟨parametricEpigraphCoordinates q,hq,rfl⟩

/-- Euclidean form of the regular subderivative epigraph identity. -/
theorem euclideanEpigraph_regularSubderivative {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {g : F → EReal} {x : F} {a : ℝ}
    (hx : g x = a) (hl : LowerSemicontinuousAt g x) :
    euclideanEpigraph (regularSubderivative g x) =
      regularTangentCone (euclideanEpigraph g) (WithLp.toLp 2 (x,a)) := by
  change (l2ProdEquiv F) ⁻¹' epigraph (regularSubderivative g x) =
    regularTangentCone ((l2ProdEquiv F) ⁻¹' epigraph g) _
  have ht : regularTangentCone ((l2ProdEquiv F) ⁻¹' epigraph g) (WithLp.toLp 2 (x,a)) =
      (l2ProdEquiv F) ⁻¹' regularTangentCone (epigraph g) (x,a) :=
    regularTangentCone_preimage (Φ' := l2ProdEquiv F)
      (l2ProdEquiv F).toContinuousLinearMap.hasStrictFDerivAt (epigraph g) hx.le
  rw [ht,epigraph_regularSubderivative_eq_regularTangentCone hx hl]

/-- **Theorem 10.13**, the ordinary subderivative is bounded by that at each
optimal decision and each lifted direction. -/
theorem subderivative_parametricValue_le {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a)
    {x : E} (hx : x ∈ parametricMinimizers f u) (w : E) (z : P) :
    subderivative (parametricValue f) u z ≤
      subderivative f (WithLp.toLp 2 (x,u)) (WithLp.toLp 2 (w,z)) := by
  by_contra! h
  obtain ⟨b,hfb,hbp⟩ := EReal.exists_between_coe_real h
  have ht : WithLp.toLp 2 (WithLp.toLp 2 (w,z),b) ∈
      tangentCone (euclideanEpigraph f) (WithLp.toLp 2 (WithLp.toLp 2 (x,u),a)) := by
    rw [← euclideanEpigraph_subderivative ((mem_parametricMinimizers.mp hx).1.trans hu)]
    exact hfb.le
  have him := image_tangentCone_subset (parametricEpigraphProjection (E := E) (P := P)).hasFDerivAt
    (euclideanEpigraph f) ⟨_,ht,rfl⟩
  rw [← euclideanEpigraph_parametricValue hl hb] at him
  change WithLp.toLp 2 (z,b) ∈ tangentCone (euclideanEpigraph (parametricValue f))
    (WithLp.toLp 2 (u,a)) at him
  rw [← euclideanEpigraph_subderivative hu] at him
  exact hbp.not_ge him

theorem subderivative_parametricValue_le_iInf {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) (z : P) :
    subderivative (parametricValue f) u z ≤
      ⨅ x ∈ parametricMinimizers f u, ⨅ w : E,
        subderivative f (WithLp.toLp 2 (x,u)) (WithLp.toLp 2 (w,z)) :=
  le_iInf fun x ↦ le_iInf fun hx ↦ le_iInf fun w ↦ subderivative_parametricValue_le hl hb hu hx w z

/-- The support expression in 10.13, written piecewise to keep all
extended-real degeneracies explicit. -/
def parametricMultiplierSupport (f : WithLp 2 (E × P) → EReal) (u z : P) : EReal := by
  classical
  exact if z ∈ polarCone (horizonParametricMultipliers f u)
    then supportFunction (parametricMultipliers f u) z else ⊤

/-- **Theorem 10.13**, the first regular subderivative estimate. -/
theorem regularSubderivative_parametricValue_le_support {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) (z : P) :
    regularSubderivative (parametricValue f) u z ≤ parametricMultiplierSupport f u z := by
  have hlp := lowerSemicontinuous_parametricValue hl hp hb
  have hlocal := isLocallyLscAt_of_isLocallyClosedAt_epigraph hu
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal _ hlp) _)
  dsimp [parametricMultiplierSupport]
  split_ifs with hz
  · rw [regularSubderivative_eq_supportFunction_of_mem_polar hu hlocal
      (polarCone_antitone (horizonSubdifferential_parametricValue_subset hl hb hu) hz)]
    exact supportFunction_mono (subdifferential_parametricValue_subset hl hb hu) z
  · exact le_top

/-- **Theorem 10.13**, the second regular subderivative estimate. -/
theorem regularSubderivative_parametricValue_le_iSup_iInf {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) (hb : IsParametricallyLevelBounded f)
    {u : P} {a : ℝ} (hu : parametricValue f u = a) (z : P) :
    regularSubderivative (parametricValue f) u z ≤
      ⨆ x ∈ parametricMinimizers f u, ⨅ w : E,
        regularSubderivative f (WithLp.toLp 2 (x,u)) (WithLp.toLp 2 (w,z)) := by
  by_contra! h
  obtain ⟨b,hsb,hbp⟩ := EReal.exists_between_coe_real h
  have hmem : WithLp.toLp 2 (z,b) ∈
      ⋂ q ∈ euclideanEpigraph f ∩ parametricEpigraphProjection ⁻¹' {WithLp.toLp 2 (u,a)},
        (fderiv ℝ parametricEpigraphProjection q) '' regularTangentCone (euclideanEpigraph f) q := by
    apply mem_iInter₂.mpr
    intro q hq
    rw [parametricEpigraphProjection_fiber hu] at hq
    obtain ⟨x,hx,rfl⟩ := hq
    have hi : (⨅ w : E, regularSubderivative f (WithLp.toLp 2 (x,u)) (WithLp.toLp 2 (w,z))) <
        (b:EReal) := (le_iSup₂ x hx).trans_lt hsb
    obtain ⟨w,hw⟩ := iInf_lt_iff.mp hi
    refine ⟨WithLp.toLp 2 (WithLp.toLp 2 (w,z),b),?_,by simp only [ContinuousLinearMap.fderiv]; rfl⟩
    rw [← euclideanEpigraph_regularSubderivative ((mem_parametricMinimizers.mp hx).1.trans hu) (hl _)]
    exact hw.le
  have him := iInter_image_regularTangentCone_subset (isClosed_euclideanEpigraph hl)
    (parametricEpigraphProjection (E := E) (P := P)).contDiff
    (show WithLp.toLp 2 (u,a) ∈ parametricEpigraphProjection '' euclideanEpigraph f from
      (euclideanEpigraph_parametricValue hl hb) ▸ hu.le)
    (parametricEpigraphProjection_locally_bounded_inverse hb u a) hmem
  rw [← euclideanEpigraph_parametricValue hl hb,
    ← euclideanEpigraph_regularSubderivative hu ((lowerSemicontinuous_parametricValue hl hp hb) u)] at him
  exact hbp.not_ge him

/-- **Theorem 10.13**, the multiplier support itself is bounded by the
supremum of the infima of the lifted regular subderivatives. -/
theorem parametricMultiplierSupport_le_iSup_iInf {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) {u : P} {a : ℝ} (hu : parametricValue f u = a) (z : P) :
    parametricMultiplierSupport f u z ≤
      ⨆ x ∈ parametricMinimizers f u, ⨅ w : E,
        regularSubderivative f (WithLp.toLp 2 (x,u)) (WithLp.toLp 2 (w,z)) := by
  have hlocal (x : E) (hx : x ∈ parametricMinimizers f u) :
      IsLocallyLscAt f (WithLp.toLp 2 (x,u)) :=
    isLocallyLscAt_of_isLocallyClosedAt_epigraph ((mem_parametricMinimizers.mp hx).1.trans hu)
      (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal f hl) _)
  dsimp [parametricMultiplierSupport]
  split_ifs with hz
  · apply (supportFunction_le_iff _ _ _).mpr
    rintro y ⟨x,hx,hy⟩
    apply le_trans _ (le_iSup₂ x hx)
    apply le_iInf
    intro w
    by_contra! h
    obtain ⟨b,hfb,hby⟩ := EReal.exists_between_coe_real h
    have hsup := ((regularSubderivative_le_coe_iff_support_polar
      ((mem_parametricMinimizers.mp hx).1.trans hu) (hlocal x hx)).mp hfb.le).1
    have hle := (inner_le_supportFunction hy (WithLp.toLp 2 (w,z))).trans hsup
    have he : ⟪WithLp.toLp 2 ((0:E),y),WithLp.toLp 2 (w,z)⟫_ℝ = ⟪y,z⟫_ℝ := by
      simp [WithLp.prod_inner_apply]
    rw [he] at hle
    exact hby.not_ge hle
  · have hbad : ∃ y ∈ horizonParametricMultipliers f u, 0 < ⟪z,y⟫_ℝ := by
      change ¬ ∀ y ∈ horizonParametricMultipliers f u, ⟪z,y⟫_ℝ ≤ 0 at hz
      push_neg at hz
      exact hz
    obtain ⟨y,⟨x,hx,hy⟩,hpos⟩ := hbad
    have htop (w : E) : regularSubderivative f (WithLp.toLp 2 (x,u))
        (WithLp.toLp 2 (w,z)) = ⊤ := by
      apply regularSubderivative_eq_top_of_not_mem_polar
        ((mem_parametricMinimizers.mp hx).1.trans hu) (hlocal x hx)
      intro hpolar
      have hle := hpolar _ hy
      have he : ⟪WithLp.toLp 2 (w,z),WithLp.toLp 2 ((0:E),y)⟫_ℝ = ⟪z,y⟫_ℝ := by
        simp [WithLp.prod_inner_apply]
      rw [he] at hle
      exact hpos.not_ge hle
    have hi : (⨅ w : E, regularSubderivative f (WithLp.toLp 2 (x,u))
        (WithLp.toLp 2 (w,z))) = ⊤ := by simp only [htop,iInf_top]
    rw [← hi]
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)

end

end RW
