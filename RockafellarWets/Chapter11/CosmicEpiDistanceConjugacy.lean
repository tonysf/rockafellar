/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugation as an isometry for the cosmic epi-metric of Theorem 7.59

The cone form of formula 7(28) used in `ConjugateCosmicIsometry` agrees with
the cosmic epi-distance of Chapter 7, which is built from unit-ball truncations
of the ray-space cones of closed epigraphs.
-/
import RockafellarWets.Chapter11.ConjugateCosmicIsometry
import RockafellarWets.Chapter7.CosmicEpiDistance
import RockafellarWets.Chapter4.CosmicMetricCompletion

open Metric Set
open scoped InnerProductSpace NNReal

namespace RW
noncomputable section

section Truncation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The ray-space cone `pos(C,-1) ∪ (K,0)` inside the Euclidean ambient of `csm V`. -/
def rayAmbientCone (C K : Set V) : Set (CosmicRayAmbient V) :=
  {z | WithLp.ofLp z ∈ raySpaceCone C K}

omit [FiniteDimensional ℝ V] in
theorem isCone_rayAmbientCone (C : Set V) {K : Set V} (hK : IsCone K) :
    IsCone (rayAmbientCone C K) := by
  have h := isCone_raySpaceCone (C := C) hK
  exact ⟨h.1, fun _ hp _ hc ↦ h.2 hp hc⟩

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem norm_toLp_prod_sq (x : V) (r : ℝ) :
    ‖(WithLp.toLp 2 (x, r) : WithLp 2 (V × ℝ))‖ ^ 2 = ‖x‖ ^ 2 + r ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp

/-- The unit-ball truncation used by the cosmic set metric is the ray-space
cone cut by the unit ball. -/
theorem coe_cosmicConeTruncation_eq {C K : Set V} (hK : IsCone K)
    (S : TopologicalSpace.Closeds (CosmicSpace V))
    (hS : (S : Set (CosmicSpace V)) = cosmicSet C K) :
    (cosmicConeTruncation S : Set (CosmicRayAmbient V)) = rayAmbientCone C K ∩ closedBall 0 1 := by
  ext z
  change z ∈ cosmicConeTruncation S ↔ _
  rw [mem_cosmicConeTruncation_iff]
  constructor
  · rintro (rfl | ⟨p, hp, t, ⟨ht0, ht1⟩, rfl⟩)
    · exact ⟨Or.inr ⟨hK.1, rfl⟩, by simp⟩
    · refine ⟨?_, ?_⟩
      · have hp' : p ∈ cosmicSet C K := hS ▸ hp
        rcases mem_cosmicSet.mp hp' with ⟨x, hx, rfl⟩ | ⟨u, hu, rfl⟩
        · rw [cosmicRayRepresentative_cosmicEmbed]
          rcases eq_or_lt_of_le ht0 with h0 | hpos
          · subst h0
            exact Or.inr ⟨by simpa using hK.1, by simp⟩
          · refine Or.inl ⟨x, hx, t * cosmicScale x, mul_pos hpos (cosmicScale_pos x), ?_⟩
            simp [smul_smul]
        · rw [cosmicRayRepresentative_cosmicDirection_eq_directionRay, directionCosmicRay]
          refine Or.inr ⟨?_, by simp⟩
          change t • (u : V) ∈ K
          rcases eq_or_lt_of_le ht0 with h0 | hpos
          · subst h0
            simpa using hK.1
          · exact hK.2 hu hpos
      · rw [mem_closedBall, dist_zero_right, norm_smul, norm_cosmicRayRepresentative, mul_one,
          Real.norm_eq_abs, abs_of_nonneg ht0]
        exact ht1
  · rintro ⟨hz, hzn⟩
    rw [mem_closedBall, dist_zero_right] at hzn
    rcases hz with ⟨x, hx, a, ha, hEq⟩ | ⟨hw, hz2⟩
    · right
      have hs := cosmicScale_pos x
      have hsq := cosmicScale_sq_add_norm_sq x
      rw [norm_smul_of_nonneg hs.le] at hsq
      have hz : z = WithLp.toLp 2 (a • x, -a) := by
        rw [← hEq]
      have hnorm : ‖z‖ = a / cosmicScale x := by
        have h1 : ‖z‖ ^ 2 = (a / cosmicScale x) ^ 2 := by
          rw [hz, norm_toLp_prod_sq, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
          field_simp
          nlinarith
        have h2 : 0 ≤ a / cosmicScale x := div_nonneg ha.le hs.le
        nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - a / cosmicScale x),
          sq_nonneg (‖z‖ + a / cosmicScale x)]
      have hmem : cosmicEmbed x ∈ S := by
        rw [← SetLike.mem_coe, hS]
        exact cosmicEmbed_mem_cosmicSet_iff.mpr hx
      refine ⟨cosmicEmbed x, hmem, a / cosmicScale x,
        ⟨div_nonneg ha.le hs.le, hnorm ▸ hzn⟩, ?_⟩
      rw [cosmicRayRepresentative_cosmicEmbed, hz, ← WithLp.toLp_smul]
      congr 1
      ext
      · simp only [Prod.smul_fst, smul_smul]
        rw [div_mul_cancel₀ _ hs.ne']
      · simp only [Prod.smul_snd, smul_eq_mul, mul_neg]
        rw [div_mul_cancel₀ _ hs.ne']
    · have hz2' : (WithLp.ofLp z).2 = 0 := hz2
      by_cases hw0 : (WithLp.ofLp z).1 = 0
      · left
        apply WithLp.ofLp_injective
        exact Prod.ext hw0 hz2'
      · right
        set w := (WithLp.ofLp z).1 with hw_def
        have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
        have hz : z = WithLp.toLp 2 (w, 0) := by
          apply WithLp.ofLp_injective
          exact Prod.ext rfl hz2'
        have hnorm : ‖z‖ = ‖w‖ := by
          have h1 : ‖z‖ ^ 2 = ‖w‖ ^ 2 := by rw [hz, norm_toLp_prod_sq]; ring
          nlinarith [norm_nonneg z, norm_nonneg w, sq_nonneg (‖z‖ - ‖w‖), sq_nonneg (‖z‖ + ‖w‖)]
        let u : CosmicBoundary V := ⟨‖w‖⁻¹ • w, by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']⟩
        have hu : (u : V) ∈ K := hK.2 hw (inv_pos.mpr hwpos)
        have hmem : cosmicDirection u ∈ S := by
          rw [← SetLike.mem_coe, hS]
          exact mem_cosmicSet.mpr (Or.inr ⟨u, hu, rfl⟩)
        refine ⟨cosmicDirection u, hmem, ‖w‖,
          ⟨norm_nonneg w, hnorm ▸ hzn⟩, ?_⟩
        rw [cosmicRayRepresentative_cosmicDirection_eq_directionRay, directionCosmicRay, hz,
          ← WithLp.toLp_smul]
        congr 1
        ext
        · change w = ‖w‖ • (‖w‖⁻¹ • w)
          rw [smul_smul, mul_inv_cancel₀ hwpos.ne', one_smul]
        · simp

/-- The truncated cone of a closed set in the total cosmic embedding. -/
theorem coe_cosmicConeTruncation_totalCosmicEmbedding (C : TopologicalSpace.Closeds V) :
    (cosmicConeTruncation (totalCosmicEmbedding C) : Set (CosmicRayAmbient V)) =
      closure (rayAmbientCone (C : Set V) {0}) ∩ closedBall 0 1 := by
  have hK : IsCone (horizonCone (C : Set V)) := isCone_horizonCone _
  have hS : ((totalCosmicEmbedding C : TopologicalSpace.Closeds (CosmicSpace V)) :
      Set (CosmicSpace V)) = cosmicSet (C : Set V) (horizonCone (C : Set V)) := by
    change closure (cosmicSet (C : Set V) {0}) = _
    rw [closure_cosmicSet isCone_singleton_zero, C.isClosed.closure_eq, closure_singleton,
      union_eq_left.mpr (singleton_subset_iff.mpr (zero_mem_horizonCone _))]
  rw [coe_cosmicConeTruncation_eq hK _ hS]
  congr 1
  have hcl := closure_raySpaceCone (C := (C : Set V)) (K := ({0} : Set V)) isCone_singleton_zero
  rw [C.isClosed.closure_eq, closure_singleton,
    union_eq_left.mpr (singleton_subset_iff.mpr (zero_mem_horizonCone _))] at hcl
  change WithLp.ofLp ⁻¹' raySpaceCone (C : Set V) (horizonCone (C : Set V)) =
    closure (WithLp.ofLp ⁻¹' raySpaceCone (C : Set V) {0})
  rw [← hcl]
  exact (WithLp.homeomorphProd 2 V ℝ).preimage_closure _

/-- The restricted cosmic set distance of 4.47 between closed sets is the
integrated distance of their ray-space cones. -/
theorem totalSetDistance_eq_integratedSetDistance (C D : TopologicalSpace.Closeds V) :
    totalSetDistance C D =
      integratedSetDistance (rayAmbientCone (C : Set V) {0}) (rayAmbientCone (D : Set V) {0}) := by
  have hKc : IsCone (closure (rayAmbientCone (C : Set V) {0})) :=
    (isCone_rayAmbientCone _ isCone_singleton_zero).closure
  have hKd : IsCone (closure (rayAmbientCone (D : Set V) {0})) :=
    (isCone_rayAmbientCone _ isCone_singleton_zero).closure
  rw [totalSetDistance, cosmicSetDistance, Metric.NonemptyCompacts.dist_eq,
    coe_cosmicConeTruncation_totalCosmicEmbedding, coe_cosmicConeTruncation_totalCosmicEmbedding,
    hausdorffDist, ← rhoHatEDistance_one_eq_hausdorffEDist_inter_closedBall hKc hKd]
  change rhoHatDistance 1 _ _ = _
  rw [rhoHatDistance_eq_rhoDistance_of_isCone 1 isClosed_closure isClosed_closure hKc hKd,
    ← integratedSetDistance_isCone_eq hKc hKd, integratedSetDistance_closure]

end Truncation

section Functions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The coordinate change `((x,α),β) ↦ (x,α,β)` from the ray ambient of `csm ℝⁿ⁺¹`
to `ℝⁿ⁺²`, a linear isometry. -/
def rayAmbientConjugacyIsometry :
    CosmicRayAmbient (WithLp 2 (E × ℝ)) ≃ₗᵢ[ℝ] ConjugacySpace E where
  toFun z := conjugacyPoint (WithLp.ofLp (WithLp.ofLp z).1).1 (WithLp.ofLp (WithLp.ofLp z).1).2
    (WithLp.ofLp z).2
  invFun p := WithLp.toLp 2 (WithLp.toLp 2 (p.fst, p.snd.fst), p.snd.snd)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' z := by
    have key : ‖conjugacyPoint (WithLp.ofLp (WithLp.ofLp z).1).1 (WithLp.ofLp (WithLp.ofLp z).1).2
        (WithLp.ofLp z).2‖ ^ 2 = ‖z‖ ^ 2 := by
      simp only [conjugacyPoint, WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd,
        Real.norm_eq_abs, sq_abs]
      simp only [WithLp.fst, WithLp.snd]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp key

omit [FiniteDimensional ℝ E] in
/-- The ray-space cone of the Euclidean epigraph is the cone `pos(epi f, -1)` in
the coordinates of `ℝⁿ⁺²`. -/
theorem rayAmbientCone_euclideanEpigraph (f : E → EReal) :
    rayAmbientCone (euclideanEpigraph f) {0} =
      (rayAmbientConjugacyIsometry (E := E)) ⁻¹' epiRayCone f := by
  ext z
  change WithLp.ofLp z ∈ raySpaceCone (euclideanEpigraph f) {0} ↔
    (((WithLp.ofLp (WithLp.ofLp z).1).1, (WithLp.ofLp (WithLp.ofLp z).1).2), (WithLp.ofLp z).2) ∈
      raySpaceCone (epigraph f) {0}
  constructor
  · rintro (⟨c, hc, a, ha, hEq⟩ | ⟨h1, h2⟩)
    · refine Or.inl ⟨WithLp.ofLp c, hc, a, ha, ?_⟩
      rw [hEq]
      rfl
    · refine Or.inr ⟨?_, h2⟩
      rw [mem_singleton_iff] at h1 ⊢
      rw [h1]
      rfl
  · rintro (⟨p, hp, a, ha, hEq⟩ | ⟨h1, h2⟩)
    · refine Or.inl ⟨WithLp.toLp 2 p, hp, a, ha, ?_⟩
      apply Prod.ext
      · apply WithLp.ofLp_injective
        exact congrArg Prod.fst hEq
      · have h2 : (WithLp.ofLp z).2 = -a := congrArg Prod.snd hEq
        exact h2
    · refine Or.inr ⟨?_, h2⟩
      rw [mem_singleton_iff] at h1 ⊢
      apply WithLp.ofLp_injective
      exact h1

/-- The cosmic epi-distance of Theorem 7.59 coincides with the cone form of
formula 7(28) used in Corollary 11.37. -/
theorem LscFunctionModel.cosmicEpiDistance_eq_cosmicEpiConeDistance (f g : LscFunctionModel E) :
    LscFunctionModel.cosmicEpiDistance f g = cosmicEpiConeDistance f.toFun g.toFun := by
  rw [LscFunctionModel.cosmicEpiDistance, totalSetDistance_eq_integratedSetDistance]
  change integratedSetDistance (rayAmbientCone (euclideanEpigraph f.toFun) {0})
    (rayAmbientCone (euclideanEpigraph g.toFun) {0}) = _
  rw [rayAmbientCone_euclideanEpigraph, rayAmbientCone_euclideanEpigraph,
    integratedSetDistance_preimage_linearIsometryEquiv]
  rfl

/-- The conjugate of a proper convex element of `lsc-fcns(ℝⁿ)`, again in `lsc-fcns(ℝⁿ)`. -/
def LscFunctionModel.conjugate (f : LscFunctionModel E) (hp : IsProper f.toFun)
    (hc : Convex ℝ (epigraph f.toFun)) : LscFunctionModel E :=
  ⟨fenchelConjugate f.toFun, lowerSemicontinuous_fenchelConjugate _,
    (isProper_fenchelConjugate_of_convex hp hc).1⟩

/-- **Corollary 11.37** for the cosmic epi-metric `dlcsm` of Theorem 7.59:
conjugation preserves the cosmic epi-distance between proper convex functions in
`lsc-fcns(ℝⁿ)`. -/
theorem LscFunctionModel.cosmicEpiDistance_conjugate (f g : LscFunctionModel E)
    (hf : IsProper f.toFun) (hfc : Convex ℝ (epigraph f.toFun))
    (hg : IsProper g.toFun) (hgc : Convex ℝ (epigraph g.toFun)) :
    LscFunctionModel.cosmicEpiDistance (f.conjugate hf hfc) (g.conjugate hg hgc) =
      LscFunctionModel.cosmicEpiDistance f g := by
  rw [LscFunctionModel.cosmicEpiDistance_eq_cosmicEpiConeDistance,
    LscFunctionModel.cosmicEpiDistance_eq_cosmicEpiConeDistance]
  exact cosmicEpiConeDistance_fenchelConjugate hf hfc hg hgc

end Functions

end
end RW
