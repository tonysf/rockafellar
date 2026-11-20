/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Metrics for epi-convergence
-/

import RockafellarWets.Chapter4.IntegratedSetDistance
import RockafellarWets.Chapter7.AuxEpiComparison
import RockafellarWets.Chapter7.EpiCompactness
import RockafellarWets.Chapter7.EpiLimitProperties

open Filter Metric Set Topology
open scoped NNReal

namespace RW

section Homeomorph

variable {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]

theorem innerSetLimit_preimage_homeomorph (h : P ≃ₜ Q) (C : ℕ → Set Q) :
    innerSetLimit (fun n ↦ h ⁻¹' C n) = h ⁻¹' innerSetLimit C := by
  ext x
  constructor
  · intro hx U hU
    exact (hx _ (h.continuous.continuousAt hU)).mono fun _ ⟨y, hy, hV⟩ ↦ ⟨h y, hy, hV⟩
  · intro hx U hU
    have hV : h.symm ⁻¹' U ∈ 𝓝 (h x) := h.symm.continuous.continuousAt (by simpa using hU)
    exact (hx _ hV).mono fun _ ⟨y, hy, hyU⟩ ↦ ⟨h.symm y, by simpa using hy, hyU⟩

theorem outerSetLimit_preimage_homeomorph (h : P ≃ₜ Q) (C : ℕ → Set Q) :
    outerSetLimit (fun n ↦ h ⁻¹' C n) = h ⁻¹' outerSetLimit C := by
  ext x
  constructor
  · intro hx U hU
    exact (hx _ (h.continuous.continuousAt hU)).mono fun _ ⟨y, hy, hV⟩ ↦ ⟨h y, hy, hV⟩
  · intro hx U hU
    have hV : h.symm ⁻¹' U ∈ 𝓝 (h x) := h.symm.continuous.continuousAt (by simpa using hU)
    exact (hx _ hV).mono fun _ ⟨y, hy, hyU⟩ ↦ ⟨h.symm y, by simpa using hy, hyU⟩

theorem pkConverges_preimage_homeomorph_iff (h : P ≃ₜ Q) {C : ℕ → Set Q} {D : Set Q} :
    PKConverges (fun n ↦ h ⁻¹' C n) (h ⁻¹' D) ↔ PKConverges C D := by
  simp only [PKConverges, innerSetLimit_preimage_homeomorph, outerSetLimit_preimage_homeomorph,
    h.surjective.preimage_injective.eq_iff]

end Homeomorph

variable {E : Type*} [NormedAddCommGroup E]

theorem isClosed_euclideanEpigraph {f : E → EReal} (hf : LowerSemicontinuous f) :
    IsClosed (euclideanEpigraph f) :=
  (isClosed_epigraph_of_lsc_ereal _ hf).preimage (WithLp.homeomorphProd 2 E ℝ).continuous

theorem epiConverges_iff_pkConverges_euclideanEpigraph {f : ℕ → E → EReal} {g : E → EReal} :
    EpiConverges f g ↔ PKConverges (fun n ↦ euclideanEpigraph (f n)) (euclideanEpigraph g) :=
  (pkConverges_preimage_homeomorph_iff (WithLp.homeomorphProd 2 E ℝ)).symm

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Formula 7(27), the integrated distance of Euclidean epigraphs. -/
noncomputable def epiDistance (f g : E → EReal) : ℝ :=
  integratedSetDistance (euclideanEpigraph f) (euclideanEpigraph g)

/-- The distance of the epigraph distance functions restricted to a ball. -/
noncomputable def rhoEpiDistance (r : ℝ≥0) (f g : E → EReal) : ℝ :=
  rhoDistance r (euclideanEpigraph f) (euclideanEpigraph g)

/-- The maximum of the two localized excesses of the epigraphs. -/
noncomputable def rhoHatEpiDistance (r : ℝ≥0) (f g : E → EReal) : ℝ :=
  rhoHatDistance r (euclideanEpigraph f) (euclideanEpigraph g)

/-- **Theorem 7.58**. The localized uniform distances characterize epi-convergence. -/
theorem epiConverges_iff_tendsto_rhoEpiDistance {f : ℕ → E → EReal} {g : E → EReal}
    (hg : LowerSemicontinuous g) (hne : (effectiveDomain g).Nonempty)
    (hf : ∀ n, (effectiveDomain (f n)).Nonempty) (r₀ : ℝ≥0) :
    EpiConverges f g ↔ ∀ r ≥ r₀, Tendsto (fun n ↦ rhoEpiDistance r (f n) g) atTop (𝓝 0) :=
  epiConverges_iff_pkConverges_euclideanEpigraph.trans
    (pkConverges_iff_tendsto_rhoDistance_from (isClosed_euclideanEpigraph hg)
      (euclideanEpigraph_nonempty hne) (fun n ↦ euclideanEpigraph_nonempty (hf n)) r₀)

/-- **Theorem 7.58**, localized excess criterion. -/
theorem epiConverges_iff_tendsto_rhoHatEpiDistance {f : ℕ → E → EReal} {g : E → EReal}
    (hg : LowerSemicontinuous g) (hne : (effectiveDomain g).Nonempty)
    (hf : ∀ n, (effectiveDomain (f n)).Nonempty) (r₀ : ℝ≥0) :
    EpiConverges f g ↔ ∀ r ≥ r₀, Tendsto (fun n ↦ rhoHatEpiDistance r (f n) g) atTop (𝓝 0) :=
  epiConverges_iff_pkConverges_euclideanEpigraph.trans
    (pkConverges_iff_tendsto_rhoHatDistance_from (isClosed_euclideanEpigraph hg)
      (euclideanEpigraph_nonempty hne) (fun n ↦ euclideanEpigraph_nonempty (hf n)) r₀)

/-- **Theorem 7.58**, integrated distance criterion. -/
theorem epiConverges_iff_tendsto_epiDistance {f : ℕ → E → EReal} {g : E → EReal}
    (hg : LowerSemicontinuous g) (hne : (effectiveDomain g).Nonempty)
    (hf : ∀ n, (effectiveDomain (f n)).Nonempty) :
    EpiConverges f g ↔ Tendsto (fun n ↦ epiDistance (f n) g) atTop (𝓝 0) :=
  epiConverges_iff_pkConverges_euclideanEpigraph.trans
    (pkConverges_iff_tendsto_integratedSetDistance (isClosed_euclideanEpigraph hg)
      (euclideanEpigraph_nonempty hne) (fun n ↦ euclideanEpigraph_nonempty (hf n)))

/-- **Theorem 7.58**, escape to the horizon relative to any fixed reference function. -/
theorem epiConverges_top_iff_tendsto_epiDistance_atTop {f : ℕ → E → EReal}
    (hf : ∀ n, (effectiveDomain (f n)).Nonempty) (g : E → EReal) :
    EpiConverges f (fun _ ↦ ⊤) ↔ Tendsto (fun n ↦ epiDistance (f n) g) atTop atTop := by
  rw [epiConverges_top_iff_epiLowerLimit_eq_top, epiLowerLimit_eq_top_iff]
  change _ ↔ Tendsto (fun n ↦ integratedSetDistance (euclideanEpigraph (f n))
    (euclideanEpigraph g)) atTop atTop
  rw [← outerSetLimit_eq_empty_iff_tendsto_integratedSetDistance_atTop
    (fun n ↦ euclideanEpigraph_nonempty (hf n))]
  let h := WithLp.homeomorphProd 2 E ℝ
  change _ ↔ outerSetLimit (fun n ↦ h ⁻¹' epigraph (f n)) = ∅
  rw [outerSetLimit_preimage_homeomorph]
  exact h.surjective.preimage_injective.eq_iff.symm

/-- The space of lsc extended-real functions with nonempty effective domain. -/
@[ext]
structure LscFunctionModel (E : Type*) [TopologicalSpace E] where
  toFun : E → EReal
  lowerSemicontinuous : LowerSemicontinuous toFun
  domain_nonempty : (effectiveDomain toFun).Nonempty

namespace LscFunctionModel

def toSetMetricModel (f : LscFunctionModel E) : SetMetricModel (WithLp 2 (E × ℝ)) :=
  ⟨⟨euclideanEpigraph f.toFun, isClosed_euclideanEpigraph f.lowerSemicontinuous,
    euclideanEpigraph_nonempty f.domain_nonempty⟩⟩

theorem toSetMetricModel_injective : Function.Injective (toSetMetricModel (E := E)) := by
  intro f g h
  apply LscFunctionModel.ext
  apply eq_of_epigraph_eq
  apply (WithLp.homeomorphProd 2 E ℝ).surjective.preimage_injective
  exact congrArg SetMetricModel.carrier h

/-- The integrated epi-distance is the metric of Theorem 7.58. -/
noncomputable instance : MetricSpace (LscFunctionModel E) :=
  MetricSpace.induced toSetMetricModel toSetMetricModel_injective inferInstance

@[simp] theorem dist_eq (f g : LscFunctionModel E) :
    dist f g = epiDistance f.toFun g.toFun := rfl

theorem tendsto_iff_epiConverges {f : ℕ → LscFunctionModel E} {g : LscFunctionModel E} :
    Tendsto f atTop (𝓝 g) ↔ EpiConverges (fun n ↦ (f n).toFun) g.toFun := by
  rw [tendsto_iff_dist_tendsto_zero, epiConverges_iff_tendsto_epiDistance
    g.lowerSemicontinuous g.domain_nonempty (fun n ↦ (f n).domain_nonempty)]
  rfl

/-- Closed balls of the integrated epi-metric are compact. -/
instance : ProperSpace (LscFunctionModel E) where
  isCompact_closedBall g r := by
    apply IsSeqCompact.isCompact
    intro f hf
    obtain ⟨D, hD, φ, hφ, hlim⟩ :=
      (isCompact_closedBall g.toSetMetricModel r).isSeqCompact
        (x := fun n ↦ (f n).toSetMetricModel) hf
    let F := fun n ↦ (f (φ n)).toFun
    let u := epiLowerLimit F
    have hepi : euclideanEpigraph u = D.carrier := by
      have houter := (SetMetricModel.tendsto_iff_pkConverges.mp hlim).outer_eq
      change outerSetLimit (fun n ↦ (WithLp.homeomorphProd 2 E ℝ) ⁻¹' epigraph (F n)) =
        D.carrier at houter
      rw [outerSetLimit_preimage_homeomorph, ← epigraph_epiLowerLimit] at houter
      exact houter
    obtain ⟨p, hp⟩ := D.nonempty_carrier
    rw [← hepi] at hp
    let v : LscFunctionModel E := ⟨u, lowerSemicontinuous_epiLowerLimit _,
      ⟨p.fst, lt_of_le_of_lt hp (EReal.coe_lt_top _)⟩⟩
    have hVD : v.toSetMetricModel = D := SetMetricModel.carrier_injective hepi
    refine ⟨v, ?_, φ, hφ, ?_⟩
    · change dist v.toSetMetricModel g.toSetMetricModel ≤ r
      simpa only [hVD] using hD
    · rw [tendsto_iff_dist_tendsto_zero]
      change Tendsto (fun n ↦ dist (f (φ n)).toSetMetricModel v.toSetMetricModel) atTop (𝓝 0)
      rw [hVD]
      exact tendsto_iff_dist_tendsto_zero.mp hlim

theorem completeSpace : CompleteSpace (LscFunctionModel E) := inferInstance

/-- The local epigraph distance satisfies all pseudometric axioms. -/
noncomputable def rhoPseudoMetric (r : ℝ≥0) : PseudoMetric (LscFunctionModel E) ℝ where
  toFun f g := rhoEpiDistance r f.toFun g.toFun
  refl' _ := rhoDistance_self _ _
  symm' _ _ := rhoDistance_comm _ _ _
  triangle' _ _ _ := rhoDistance_triangle _ _ _ _

end LscFunctionModel
end RW
