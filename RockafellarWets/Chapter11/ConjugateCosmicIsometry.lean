/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Legendre–Fenchel transform as an isometry for the cosmic epi-distance
-/
import RockafellarWets.Chapter11.ConjugacyAsPolarity
import RockafellarWets.Chapter11.PolarConeMetric
import RockafellarWets.Chapter11.ConvexMarginalGeometry
import RockafellarWets.Chapter5.GraphMetric

open Metric Set
open scoped InnerProductSpace NNReal
namespace RW
noncomputable section

section IsometryInvariance

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
theorem infDist_preimage_linearIsometryEquiv {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F]
    (T : F ≃ₗᵢ[𝕜] F) (x : F) (C : Set F) :
    infDist x (T ⁻¹' C) = infDist (T x) C := by
  calc infDist x (T ⁻¹' C) = infDist (T x) (T '' (T ⁻¹' C)) := (infDist_image T.isometry).symm
    _ = infDist (T x) C := by rw [T.surjective.image_preimage]

/-- Localized set distances are invariant under linear isometries. -/
theorem rhoDistance_preimage_linearIsometryEquiv (T : F ≃ₗᵢ[ℝ] F) (ρ : ℝ≥0) (C D : Set F) :
    rhoDistance ρ (T ⁻¹' C) (T ⁻¹' D) = rhoDistance ρ C D := by
  have key (S : F ≃ₗᵢ[ℝ] F) (A B : Set F) :
      rhoDistance ρ (S ⁻¹' A) (S ⁻¹' B) ≤ rhoDistance ρ A B := by
    apply (rhoDistance_le_iff (rhoDistance_nonneg ρ A B) ρ _ _).mpr
    intro x hx
    rw [infDist_preimage_linearIsometryEquiv, infDist_preimage_linearIsometryEquiv]
    apply abs_infDist_sub_infDist_le_rhoDistance
    simpa only [mem_closedBall, dist_zero_right, S.norm_map] using hx
  apply le_antisymm (key T C D)
  have h := key T.symm (T ⁻¹' C) (T ⁻¹' D)
  simpa only [preimage_preimage, LinearIsometryEquiv.apply_symm_apply, preimage_id'] using h

/-- The integrated set distance 4(12) is invariant under linear isometries. -/
theorem integratedSetDistance_preimage_linearIsometryEquiv (T : F ≃ₗᵢ[ℝ] F) (C D : Set F) :
    integratedSetDistance (T ⁻¹' C) (T ⁻¹' D) = integratedSetDistance C D := by
  simp only [integratedSetDistance, rhoDistanceReal, rhoDistance_preimage_linearIsometryEquiv]

end IsometryInvariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The interchange of the last two coordinates of `ℝⁿ⁺²` is a linear isometry. -/
def conjugacySwapIsometry : ConjugacySpace E ≃ₗᵢ[ℝ] ConjugacySpace E where
  toFun := conjugacySwap
  invFun := conjugacySwap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := conjugacySwap_involutive
  right_inv := conjugacySwap_involutive
  norm_map' p := by
    have h : ‖conjugacySwap p‖ ^ 2 = ‖p‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_conjugacySwap,
        conjugacySwap_involutive]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The coordinates `((x,α),β)` of a point `(x,α,β)` of `ℝⁿ⁺²`. -/
def conjugacyCoordinates : ConjugacySpace E ≃ₜ (E × ℝ) × ℝ where
  toFun p := ((p.fst,p.snd.fst),p.snd.snd)
  invFun r := conjugacyPoint r.1.1 r.1.2 r.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h1 : Continuous (fun p : ConjugacySpace E ↦ WithLp.ofLp p) :=
      WithLp.prod_continuous_ofLp 2 E (WithLp 2 (ℝ × ℝ))
    have h2 : Continuous (fun q : WithLp 2 (ℝ × ℝ) ↦ WithLp.ofLp q) :=
      WithLp.prod_continuous_ofLp 2 ℝ ℝ
    have hs : Continuous (fun p : ConjugacySpace E ↦ WithLp.ofLp (WithLp.ofLp p).2) :=
      h2.comp (continuous_snd.comp h1)
    exact ((continuous_fst.comp h1).prodMk (continuous_fst.comp hs)).prodMk (continuous_snd.comp hs)
  continuous_invFun := by
    exact (WithLp.prod_continuous_toLp 2 E (WithLp 2 (ℝ × ℝ))).comp
      ((continuous_fst.comp continuous_fst).prodMk ((WithLp.prod_continuous_toLp 2 ℝ ℝ).comp
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

/-- The cone `pos(epi f, -1)` of formula 7(28) in `ℝⁿ⁺²`, with coordinates
`(x,α,β)`, together with the origin. It is the cone representing `epi f` in the
ray-space model of `csm ℝⁿ⁺¹`. -/
def epiRayCone (f : E → EReal) : Set (ConjugacySpace E) :=
  {p | ((p.fst,p.snd.fst),p.snd.snd) ∈ raySpaceCone (epigraph f) ({0} : Set (E × ℝ))}

/-- **Formula 7(28)**: the cosmic epi-distance of two arbitrary functions is the
integrated set distance between the cones `pos(epi f, -1)` and `pos(epi g, -1)`
of the Euclidean space `ℝⁿ⁺²`. -/
def cosmicEpiConeDistance (f g : E → EReal) : ℝ :=
  integratedSetDistance (epiRayCone f) (epiRayCone g)

theorem cosmicEpiConeDistance_comm (f g : E → EReal) :
    cosmicEpiConeDistance f g = cosmicEpiConeDistance g f :=
  integratedSetDistance_comm _ _

theorem cosmicEpiConeDistance_triangle (f g h : E → EReal) :
    cosmicEpiConeDistance f h ≤ cosmicEpiConeDistance f g + cosmicEpiConeDistance g h :=
  integratedSetDistance_triangle _ _ _

omit [FiniteDimensional ℝ E] in
theorem epiRayCone_subset_conjugacyPrimalCone (f : E → EReal) :
    epiRayCone f ⊆ conjugacyPrimalCone f := fun _ hp ↦
  raySpaceCone_mono subset_rfl (singleton_subset_iff.mpr (zero_mem_horizonCone _)) hp

theorem conjugacyPrimalCone_subset_closure_epiRayCone (f : E → EReal) :
    conjugacyPrimalCone f ⊆ closure (epiRayCone f) := by
  intro p hp
  have hcl : ((p.fst,p.snd.fst),p.snd.snd) ∈
      closure (raySpaceCone (epigraph f) ({0} : Set (E × ℝ))) := by
    rcases hp with hp | ⟨hw,hz⟩
    · exact subset_closure (Or.inl hp)
    · have hh := mem_closure_raySpaceCone_of_mem_horizonCone (C := epigraph f)
        (K := ({0} : Set (E × ℝ))) isCone_singleton_zero hw
      have hz' : p.snd.snd = 0 := hz
      simpa only [hz'] using hh
  have hpre : epiRayCone f =
      (conjugacyCoordinates (E := E)) ⁻¹' raySpaceCone (epigraph f) ({0} : Set (E × ℝ)) := rfl
  rw [hpre, ← Homeomorph.preimage_closure]
  exact hcl

theorem closure_conjugacyPrimalCone (f : E → EReal) :
    closure (conjugacyPrimalCone f) = closure (epiRayCone f) :=
  le_antisymm (closure_minimal (conjugacyPrimalCone_subset_closure_epiRayCone f) isClosed_closure)
    (closure_mono (epiRayCone_subset_conjugacyPrimalCone f))

theorem polarCone_conjugacyPrimalCone_eq_polarCone_epiRayCone (f : E → EReal) :
    polarCone (conjugacyPrimalCone f) = polarCone (epiRayCone f) := by
  rw [← polarCone_closure, closure_conjugacyPrimalCone, polarCone_closure]

/-- The cone `K_f` of Exercise 11.7 has the same cosmic distances as the cone
`pos(epi f, -1)`, since both have the same closure. -/
theorem integratedSetDistance_conjugacyPrimalCone (f g : E → EReal) :
    integratedSetDistance (conjugacyPrimalCone f) (conjugacyPrimalCone g) =
      cosmicEpiConeDistance f g := by
  rw [← integratedSetDistance_closure, closure_conjugacyPrimalCone, closure_conjugacyPrimalCone,
    integratedSetDistance_closure]
  rfl

omit [FiniteDimensional ℝ E] in
theorem isCone_epiRayCone (f : E → EReal) : IsCone (epiRayCone f) := by
  have h := isCone_raySpaceCone (C := epigraph f) (isCone_singleton_zero (E := E × ℝ))
  exact ⟨h.1, fun _ hp _ hc ↦ h.2 hp hc⟩

omit [FiniteDimensional ℝ E] in
theorem convex_epiRayCone {f : E → EReal} (hc : Convex ℝ (epigraph f)) :
    Convex ℝ (epiRayCone f) := by
  have h := (cosmicConvex_iff_convex_raySpaceCone (C := epigraph f)
    (isCone_singleton_zero (E := E × ℝ))).mp ⟨hc, convex_singleton 0, by rw [add_singleton]; simp⟩
  exact fun _ hp _ hq _ _ ha hb hab ↦ h hp hq ha hb hab

/-- **Corollary 11.37**: for proper convex functions, which need not be lower
semicontinuous, conjugation preserves the cosmic epi-distance of 7(28). -/
theorem cosmicEpiConeDistance_fenchelConjugate {f g : E → EReal}
    (hf : IsProper f) (hfc : Convex ℝ (epigraph f))
    (hg : IsProper g) (hgc : Convex ℝ (epigraph g)) :
    cosmicEpiConeDistance (fenchelConjugate f) (fenchelConjugate g) = cosmicEpiConeDistance f g := by
  have hfs := isProper_fenchelConjugate_of_convex hf hfc
  have hgs := isProper_fenchelConjugate_of_convex hg hgc
  rw [← integratedSetDistance_conjugacyPrimalCone (fenchelConjugate f),
    ← integratedSetDistance_preimage_linearIsometryEquiv (conjugacySwapIsometry (E := E))]
  change integratedSetDistance (conjugacyDualCone (fenchelConjugate f))
    (conjugacyDualCone (fenchelConjugate g)) = _
  rw [← polarCone_conjugacyPrimalCone hf hfs, ← polarCone_conjugacyPrimalCone hg hgs,
    polarCone_conjugacyPrimalCone_eq_polarCone_epiRayCone,
    polarCone_conjugacyPrimalCone_eq_polarCone_epiRayCone,
    integratedSetDistance_polarCone (isCone_epiRayCone f) (convex_epiRayCone hfc)
      (isCone_epiRayCone g) (convex_epiRayCone hgc)]
  rfl

end
end RW
