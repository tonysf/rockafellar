/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Clarke subgradients

Formula 8(32) and the initial assertions of Theorem 8.49: for `f` locally lsc
and finite at `x̄`, the Clarke subgradients
`∂̄f(x̄) = {v | (v, -1) ∈ N̄_{epi f}(x̄, f(x̄))}` form a closed convex set, the
Clarke horizon subgradients `∂̄^∞f(x̄) = {v | (v, 0) ∈ N̄_{epi f}(x̄, f(x̄))}` a
closed convex cone, and

* `∂̄f(x̄) = {v | ⟪v, w⟫ ≤ d̂f(x̄)(w) for all w}`,
* `∂̄^∞f(x̄) = {v | ⟪v, w⟫ ≤ 0 for all w ∈ dom d̂f(x̄)}`.

As in the book these come from `N̄_{epi f} = T̂_{epi f}^*` (6.38) and
`epi d̂f(x̄) = T̂_{epi f}(x̄, f(x̄))` (8.17(a), `regularSubderivative`).  The
convexified normal cone lives in the Euclidean product `WithLp 2 (E × ℝ)`
(`euclideanEpigraph`), while 8.17(a) is stated in `E × ℝ`; regular tangent
cones are transferred along the linear homeomorphism between the two.

The remaining assertions of 8.49 (the support-function formula, the
recession-cone identity and the convex-hull representations in the pointed
case) are not formalized here.
-/

import RockafellarWets.Chapter8.ProximalApproximation
import RockafellarWets.Chapter8.SubderivativeRelationships
import RockafellarWets.Chapter6.ConvexifiedCones

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

/-! ### Regular tangent cones under continuous linear equivalences -/

section Transfer

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem regularTangentCone_preimage_continuousLinearEquiv (L : F ≃L[ℝ] G) {C : Set G} {x : F}
    (hx : L x ∈ C) :
    regularTangentCone (L ⁻¹' C) x = L ⁻¹' regularTangentCone C (L x) := by
  ext w
  rw [mem_preimage, mem_regularTangentCone_iff_forall_sequences (C := L ⁻¹' C) (x := x) hx,
    mem_regularTangentCone_iff_forall_sequences (C := C) (x := L x) hx]
  constructor
  · intro h τs ybars hτ hτ0 hyC hyto
    obtain ⟨xs, hxsC, hxsto, hq⟩ := h τs (fun n ↦ L.symm (ybars n)) hτ hτ0
      (fun n ↦ by show L (L.symm (ybars n)) ∈ C; rw [L.apply_symm_apply]; exact hyC n)
      (by simpa using (L.symm.continuous.tendsto (L x)).comp hyto)
    refine ⟨fun n ↦ L (xs n), hxsC, (L.continuous.tendsto x).comp hxsto, ?_⟩
    refine ((L.continuous.tendsto w).comp hq).congr fun n ↦ ?_
    simp only [Function.comp_apply, map_smul, map_sub, L.apply_symm_apply]
  · intro h τs xbars hτ hτ0 hxC hxto
    obtain ⟨ys, hysC, hysto, hq⟩ := h τs (fun n ↦ L (xbars n)) hτ hτ0 hxC
      ((L.continuous.tendsto x).comp hxto)
    refine ⟨fun n ↦ L.symm (ys n), fun n ↦ ?_, ?_, ?_⟩
    · show L (L.symm (ys n)) ∈ C
      rw [L.apply_symm_apply]
      exact hysC n
    · simpa using (L.symm.continuous.tendsto (L x)).comp hysto
    · have h1 := (L.symm.continuous.tendsto (L w)).comp hq
      rw [L.symm_apply_apply] at h1
      refine h1.congr fun n ↦ ?_
      simp only [Function.comp_apply, map_smul, map_sub, L.symm_apply_apply]

end Transfer

/-! ### Formula 8(32) -/

section Clarke

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Formula 8(32): the Clarke subgradients of `f` at `x̄`. -/
def clarkeSubdifferential (f : E → EReal) (x : E) : Set E :=
  {v | ∃ c : ℝ, f x = c ∧
    WithLp.toLp 2 (v, (-1 : ℝ)) ∈ convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))}

/-- Formula 8(32): the Clarke horizon subgradients of `f` at `x̄`. -/
def clarkeHorizonSubdifferential (f : E → EReal) (x : E) : Set E :=
  {v | ∃ c : ℝ, f x = c ∧
    WithLp.toLp 2 (v, (0 : ℝ)) ∈ convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))}

theorem clarkeSubdifferential_of_finite {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c) :
    clarkeSubdifferential f x = (fun v : E ↦ WithLp.toLp 2 (v, (-1 : ℝ))) ⁻¹'
      convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) := by
  ext v
  constructor
  · rintro ⟨c', hc', hv⟩
    have : c' = c := by rw [hxc] at hc'; exact (EReal.coe_injective hc').symm
    subst this
    exact hv
  · exact fun hv ↦ ⟨c, hxc, hv⟩

theorem clarkeHorizonSubdifferential_of_finite {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c) :
    clarkeHorizonSubdifferential f x = (fun v : E ↦ WithLp.toLp 2 (v, (0 : ℝ))) ⁻¹'
      convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) := by
  ext v
  constructor
  · rintro ⟨c', hc', hv⟩
    have : c' = c := by rw [hxc] at hc'; exact (EReal.coe_injective hc').symm
    subst this
    exact hv
  · exact fun hv ↦ ⟨c, hxc, hv⟩

/-- **Theorem 8.49**: `∂̄f(x̄)` is closed. -/
theorem isClosed_clarkeSubdifferential {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c) :
    IsClosed (clarkeSubdifferential f x) := by
  rw [clarkeSubdifferential_of_finite hxc]
  exact (isClosed_convexifiedNormalCone _ _).preimage
    ((WithLp.prod_continuous_toLp 2 E ℝ).comp (continuous_id.prodMk continuous_const))

/-- **Theorem 8.49**: `∂̄f(x̄)` is convex. -/
theorem convex_clarkeSubdifferential {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c) :
    Convex ℝ (clarkeSubdifferential f x) := by
  rw [clarkeSubdifferential_of_finite hxc]
  intro v₁ hv₁ v₂ hv₂ a b ha hb hab
  have h := convex_convexifiedNormalCone _ _ hv₁ hv₂ ha hb hab
  show WithLp.toLp 2 (a • v₁ + b • v₂, (-1 : ℝ)) ∈ convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))
  convert h using 1
  rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add, Prod.smul_mk, Prod.smul_mk,
    Prod.mk_add_mk, smul_eq_mul, smul_eq_mul]
  congr 2
  linear_combination hab

/-- **Theorem 8.49**: `∂̄^∞f(x̄)` is closed. -/
theorem isClosed_clarkeHorizonSubdifferential {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c) :
    IsClosed (clarkeHorizonSubdifferential f x) := by
  rw [clarkeHorizonSubdifferential_of_finite hxc]
  exact (isClosed_convexifiedNormalCone _ _).preimage
    ((WithLp.prod_continuous_toLp 2 E ℝ).comp (continuous_id.prodMk continuous_const))

/-- **Theorem 8.49**: `∂̄^∞f(x̄)` is convex. -/
theorem convex_clarkeHorizonSubdifferential {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c) :
    Convex ℝ (clarkeHorizonSubdifferential f x) := by
  rw [clarkeHorizonSubdifferential_of_finite hxc]
  intro v₁ hv₁ v₂ hv₂ a b ha hb hab
  have h := convex_convexifiedNormalCone _ _ hv₁ hv₂ ha hb hab
  show WithLp.toLp 2 (a • v₁ + b • v₂, (0 : ℝ)) ∈ convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))
  convert h using 1
  rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add, Prod.smul_mk, Prod.smul_mk,
    Prod.mk_add_mk, smul_eq_mul, smul_eq_mul]
  simp

/-- **Theorem 8.49**: `∂̄^∞f(x̄)` is a cone. -/
theorem isCone_clarkeHorizonSubdifferential [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    {c : ℝ} (hxc : f x = c) :
    IsCone (clarkeHorizonSubdifferential f x) := by
  have hz : WithLp.toLp 2 (x, c) ∈ euclideanEpigraph f := by
    show f x ≤ (c : EReal)
    rw [hxc]
  have hK := isCone_convexifiedNormalCone (C := euclideanEpigraph f) hz
  rw [clarkeHorizonSubdifferential_of_finite hxc]
  refine ⟨?_, fun v hv t ht ↦ ?_⟩
  · simpa using hK.1
  · have := hK.2 hv ht
    show WithLp.toLp 2 (t • v, (0 : ℝ)) ∈ convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))
    convert this using 1
    rw [← WithLp.toLp_smul, Prod.smul_mk, smul_zero]

/-! ### Theorem 8.49: the formulas through `d̂f(x̄)` -/

theorem inner_toLp_neg_one (v w : E) (β : ℝ) :
    ⟪WithLp.toLp 2 (v, (-1 : ℝ)), WithLp.toLp 2 (w, β)⟫_ℝ = ⟪v, w⟫_ℝ - β := by
  rw [WithLp.prod_inner_apply]
  have h1 : ⟪(-1 : ℝ), β⟫_ℝ = -β := by simp
  simp only [h1]
  ring

theorem inner_toLp_zero (v w : E) (β : ℝ) :
    ⟪WithLp.toLp 2 (v, (0 : ℝ)), WithLp.toLp 2 (w, β)⟫_ℝ = ⟪v, w⟫_ℝ := by
  rw [WithLp.prod_inner_apply]
  simp

variable [FiniteDimensional ℝ E]

/-- The polar of `T̂_{epi f}` read through `d̂f(x̄)`. -/
theorem mem_convexifiedNormalCone_euclideanEpigraph_iff {f : E → EReal} {x : E} {c : ℝ}
    (hxc : f x = c) (hlsc : IsLocallyLscAt f x) (v : E) (β : ℝ) :
    WithLp.toLp 2 (v, β) ∈ convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) ↔
      ∀ w (r : ℝ), regularSubderivative f x w ≤ (r : EReal) → ⟪v, w⟫_ℝ + β * r ≤ 0 := by
  have hz : WithLp.toLp 2 (x, c) ∈ euclideanEpigraph f := by
    show f x ≤ (c : EReal)
    rw [hxc]
  have hcx : (f x).toReal = c := by rw [hxc, EReal.toReal_coe]
  have hlc : IsLocallyClosedAt (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) := by
    have := IsLocallyClosedAt.preimage_continuousLinearEquiv (l2ProdEquiv E)
      (x := WithLp.toLp 2 (x, (f x).toReal)) hlsc.isLocallyClosedAt_epigraph
    rw [hcx] at this
    exact this
  have hT : regularTangentCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) =
      l2ProdEquiv E ⁻¹' epigraph (regularSubderivative f x) := by
    rw [epigraph_regularSubderivative_eq_regularTangentCone hxc hlsc.lowerSemicontinuousAt]
    exact regularTangentCone_preimage_continuousLinearEquiv (l2ProdEquiv E)
      (C := epigraph f) (x := WithLp.toLp 2 (x, c)) hz
  rw [convexifiedNormalCone_eq_polarCone_regularTangentCone hz hlc, hT]
  constructor
  · intro h w r hr
    have := h (WithLp.toLp 2 (w, r)) hr
    rw [WithLp.prod_inner_apply] at this
    simpa [mul_comm] using this
  · intro h q hq
    obtain ⟨⟨w, r⟩, rfl⟩ : ∃ p : E × ℝ, WithLp.toLp 2 p = q := ⟨WithLp.ofLp q, by simp⟩
    have := h w r hq
    rw [WithLp.prod_inner_apply]
    simpa [mul_comm] using this

/-- **Theorem 8.49**: `∂̄f(x̄) = {v | ⟪v, w⟫ ≤ d̂f(x̄)(w) for all w}`. -/
theorem clarkeSubdifferential_eq_setOf_inner_le_regularSubderivative {f : E → EReal} {x : E}
    {c : ℝ} (hxc : f x = c) (hlsc : IsLocallyLscAt f x) :
    clarkeSubdifferential f x =
      {v | ∀ w, ((⟪v, w⟫_ℝ : ℝ) : EReal) ≤ regularSubderivative f x w} := by
  rw [clarkeSubdifferential_of_finite hxc]
  ext v
  rw [mem_preimage, mem_convexifiedNormalCone_euclideanEpigraph_iff hxc hlsc]
  constructor
  · intro h w
    by_contra hlt
    push_neg at hlt
    obtain ⟨r, hr1, hr2⟩ := EReal.exists_between_coe_real hlt
    have := h w r hr1.le
    have hr2' := EReal.coe_lt_coe_iff.1 hr2
    linarith
  · intro h w r hr
    have := EReal.coe_le_coe_iff.1 ((h w).trans hr)
    linarith

/-- **Theorem 8.49**:
`∂̄^∞f(x̄) = {v | ⟪v, w⟫ ≤ 0 for all w ∈ dom d̂f(x̄)}`. -/
theorem clarkeHorizonSubdifferential_eq {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c)
    (hlsc : IsLocallyLscAt f x) :
    clarkeHorizonSubdifferential f x =
      {v | ∀ w, regularSubderivative f x w < ⊤ → ⟪v, w⟫_ℝ ≤ 0} := by
  rw [clarkeHorizonSubdifferential_of_finite hxc]
  ext v
  rw [mem_preimage, mem_convexifiedNormalCone_euclideanEpigraph_iff hxc hlsc]
  constructor
  · intro h w hw
    obtain ⟨r, hr, -⟩ := EReal.exists_between_coe_real hw
    simpa using h w r hr.le
  · intro h w r hr
    have := h w (lt_of_le_of_lt hr (EReal.coe_lt_top r))
    simpa using this

end Clarke

end RW
