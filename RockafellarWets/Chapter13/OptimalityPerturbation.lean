/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Perturbation of optimality conditions

Theorem 13.47 (`perturbation_of_optimality_conditions`).  For `f` on `ℝⁿ × ℝᵐ`
(`WithLp 2 (E × F)`), the mapping `S(u, v) = {(x, y) ∣ (v, y) ∈ ∂f(x, u)}` (`optimalityMapping`)
has graph corresponding to `gph ∂f` under `((u, v), (x, y)) ↦ ((x, u), (v, y))`, a linear isometry
(`optimalityGraphIsometry`; `optimalityGraphEquiv` on the plain product).  So proto-
differentiability, graphical derivatives (13.40), the graphically Lipschitzian structure (13.46)
and coderivatives transfer, and the Mordukhovich criterion 9.40 gives the Aubin property test.

General tools: `IsC1CoordinateChangeAt.comp`, `GraphicallyLipschitzianAt.of_coordinateChange`
(graphically Lipschitzian structure is invariant under `C¹` changes of coordinates of the graph
space), `GraphicallyLipschitzianAt.isLocallyClosedAt`.
-/

import RockafellarWets.Chapter13.SubgradientProtoDifferentiability
import RockafellarWets.Chapter9.ImplicitGraphPermutations
import RockafellarWets.Chapter9.GraphicallyLipschitzianMappings
import RockafellarWets.Chapter12.MonotoneProtoDerivatives

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace NNReal

namespace RW

/-! ### Changes of coordinates of graphs -/

section CoordinateChange

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Composition of `C¹` changes of coordinates. -/
theorem IsC1CoordinateChangeAt.comp {Θ : X → Y} {Θ' : Y → X} {Φ : Y → Z} {Ψ : Z → Y} {z : X}
    (hΘ : IsC1CoordinateChangeAt Θ Θ' z) (hΦ : IsC1CoordinateChangeAt Φ Ψ (Θ z)) :
    IsC1CoordinateChangeAt (Φ ∘ Θ) (Θ' ∘ Ψ) z := by
  obtain ⟨hΘ1, hΘ2, hΘ3, hΘ4, hΘ5⟩ := hΘ
  obtain ⟨hΦ1, hΦ2, hΦ3, hΦ4, hΦ5⟩ := hΦ
  have hΘc : Tendsto Θ (𝓝 z) (𝓝 (Θ z)) := hΘ1.continuousAt.tendsto
  have hΨc : Tendsto Ψ (𝓝 (Φ (Θ z))) (𝓝 (Θ z)) := by
    have := hΦ2.continuousAt.tendsto; rwa [hΦ3] at this
  refine ⟨hΦ1.comp z hΘ1, ?_, ?_, ?_, ?_⟩
  · change ContDiffAt ℝ 1 (Θ' ∘ Ψ) (Φ (Θ z))
    have h2 : ContDiffAt ℝ 1 Θ' (Ψ (Φ (Θ z))) := by rw [hΦ3]; exact hΘ2
    exact h2.comp _ hΦ2
  · simp only [Function.comp, hΦ3, hΘ3]
  · filter_upwards [hΘ4, hΘc.eventually hΦ4] with y hy1 hy2
    simp only [Function.comp, hy2, hy1]
  · filter_upwards [hΦ5, hΨc.eventually hΘ5] with w hw1 hw2
    simp only [Function.comp, hw2, hw1]

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- Graphically Lipschitzian structure is invariant under `C¹` changes of coordinates of the graph
space that match the graphs near the base points. -/
theorem GraphicallyLipschitzianAt.of_coordinateChange {X' Y' : Type*} [NormedAddCommGroup X']
    [NormedSpace ℝ X'] [FiniteDimensional ℝ X'] [NormedAddCommGroup Y'] [NormedSpace ℝ Y']
    [FiniteDimensional ℝ Y'] {S : X → Set Y} {S' : X' → Set Y'} {x : X} {u : Y} {x' : X'}
    {u' : Y'} {d : ℕ} (hS : GraphicallyLipschitzianAt S x u d)
    {Θ : X' × Y' → X × Y} {Θ' : X × Y → X' × Y'} (hΘ : IsC1CoordinateChangeAt Θ Θ' (x', u'))
    (hΘx : Θ (x', u') = (x, u))
    (hdim : Module.finrank ℝ X' + Module.finrank ℝ Y' = Module.finrank ℝ X + Module.finrank ℝ Y)
    (hgraph : ∀ᶠ z in 𝓝 (x', u'), z ∈ svGraph S' ↔ Θ z ∈ svGraph S) (hu' : u' ∈ S' x') :
    GraphicallyLipschitzianAt S' x' u' d := by
  obtain ⟨-, e, he, Φ, Ψ, g, hΦ, hg, hgr⟩ := hS
  have hΦ' : IsC1CoordinateChangeAt Φ Ψ (Θ (x', u')) := by rw [hΘx]; exact hΦ
  have hΘc : Tendsto Θ (𝓝 (x', u')) (𝓝 (x, u)) := by
    have := hΘ.1.continuousAt.tendsto; rwa [hΘx] at this
  refine ⟨hu', e, by omega, Φ ∘ Θ, Θ' ∘ Ψ, g, hΘ.comp hΦ', ?_, ?_⟩
  · simp only [Function.comp, hΘx]; exact hg
  · filter_upwards [hgraph, hΘc.eventually hgr] with z h1 h2
    rw [h1, h2]; rfl

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
/-- A graphically Lipschitzian mapping has a locally closed graph. -/
theorem GraphicallyLipschitzianAt.isLocallyClosedAt {S : X → Set Y} {x : X} {u : Y} {d : ℕ}
    (h : GraphicallyLipschitzianAt S x u d) : IsLocallyClosedAt (svGraph S) (x, u) := by
  obtain ⟨-, e, -, Φ, Ψ, g, hΦ, hg, hgr⟩ := h
  obtain ⟨k, W, hW, hgW⟩ := strictlyContinuousAt_iff.1 hg
  have hΦev : ∀ᶠ z in 𝓝 (x, u), ContinuousAt Φ z :=
    (hΦ.1.eventually (by simp)).mono fun z hz ↦ hz.continuousAt
  have hΦW : ∀ᶠ z in 𝓝 (x, u), (Φ z).1 ∈ W :=
    (continuous_fst.continuousAt.tendsto.comp hΦ.1.continuousAt.tendsto).eventually hW
  have hgWo : ∀ᶠ z in 𝓝 (x, u), (Φ z).1 ∈ interior W :=
    (continuous_fst.continuousAt.tendsto.comp hΦ.1.continuousAt.tendsto).eventually
      (interior_mem_nhds.2 hW)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hgr.and (hΦev.and hgWo))
  refine ⟨closedBall (x, u) (r / 2), closedBall_mem_nhds _ (by positivity), isClosed_closedBall, ?_⟩
  have hsub : closedBall (x, u) (r / 2) ⊆ ball (x, u) r := closedBall_subset_ball (by linarith)
  have hcont : ContinuousOn (fun z ↦ ((Φ z).2, g (Φ z).1)) (closedBall (x, u) (r / 2)) := by
    intro z hz
    obtain ⟨-, hcz, hWz⟩ := hball (hsub hz)
    have hgc : ContinuousAt g (Φ z).1 :=
      hgW.continuousOn.continuousAt (mem_interior_iff_mem_nhds.1 hWz)
    have h1 : ContinuousAt (fun w ↦ (Φ w).1) z := continuous_fst.continuousAt.comp hcz
    have h2 : ContinuousAt (fun w ↦ (Φ w).2) z := continuous_snd.continuousAt.comp hcz
    have h3 : ContinuousAt (fun w ↦ g (Φ w).1) z := ContinuousAt.comp (x := z) hgc h1
    exact (h2.prodMk h3).continuousWithinAt
  have hclosed := hcont.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_diagonal
  convert hclosed using 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_diagonal_iff]
  constructor
  · rintro ⟨hz, hzb⟩
    exact ⟨hzb, ((hball (hsub hzb)).1).1 hz⟩
  · rintro ⟨hzb, hz⟩
    exact ⟨((hball (hsub hzb)).1).2 hz, hzb⟩

end CoordinateChange

/-! ### The graph of the optimality mapping -/

section Optimality

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The mapping `S : (u, v) ↦ {(x, y) ∣ (v, y) ∈ ∂f(x, u)}` of Theorem 13.47, for a function
`f` of `(x, u) ∈ ℝⁿ × ℝᵐ`. -/
def optimalityMapping (g : WithLp 2 (E × F) → Set (WithLp 2 (E × F))) (q : WithLp 2 (F × E)) :
    Set (WithLp 2 (E × F)) :=
  {p | WithLp.toLp 2 (q.snd, p.snd) ∈ g (WithLp.toLp 2 (p.fst, q.fst))}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
@[simp] theorem mem_optimalityMapping {g : WithLp 2 (E × F) → Set (WithLp 2 (E × F))}
    {q : WithLp 2 (F × E)} {p : WithLp 2 (E × F)} :
    p ∈ optimalityMapping g q ↔ WithLp.toLp 2 (q.snd, p.snd) ∈ g (WithLp.toLp 2 (p.fst, q.fst)) :=
  Iff.rfl

/-- The graph permutation `((u, v), (x, y)) ↦ ((x, u), (v, y))`, a linear isometry. -/
noncomputable def optimalityGraphIsometry :
    WithLp 2 (WithLp 2 (F × E) × WithLp 2 (E × F)) ≃ₗᵢ[ℝ]
      WithLp 2 (WithLp 2 (E × F) × WithLp 2 (E × F)) :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ (WithLp 2 (F × E)) (WithLp 2 (E × F))).trans
    ((LinearIsometryEquiv.withLpProdAssoc 2 ℝ E F (WithLp 2 (F × E))).trans
      ((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ E)
        (LinearIsometryEquiv.withLpProdComm 2 ℝ F (WithLp 2 (F × E)))).trans
        ((LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ E)
          (LinearIsometryEquiv.withLpProdAssoc 2 ℝ F E F)).trans
          (LinearIsometryEquiv.withLpProdAssoc 2 ℝ E F (WithLp 2 (E × F))).symm)))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem optimalityGraphIsometry_apply (q : WithLp 2 (WithLp 2 (F × E) × WithLp 2 (E × F))) :
    optimalityGraphIsometry q = WithLp.toLp 2 (WithLp.toLp 2 (q.snd.fst, q.fst.fst),
      WithLp.toLp 2 (q.fst.snd, q.snd.snd)) := rfl

/-- The same permutation on the plain product of the input and output spaces. -/
noncomputable def optimalityGraphEquiv :
    (WithLp 2 (F × E) × WithLp 2 (E × F)) ≃L[ℝ] (WithLp 2 (E × F) × WithLp 2 (E × F)) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (F × E)) (WithLp 2 (E × F))).symm.trans
    (optimalityGraphIsometry (E := E) (F := F)).toContinuousLinearEquiv).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (E × F)) (WithLp 2 (E × F)))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem optimalityGraphEquiv_apply (z : WithLp 2 (F × E) × WithLp 2 (E × F)) :
    optimalityGraphEquiv z = (WithLp.toLp 2 (z.2.fst, z.1.fst), WithLp.toLp 2 (z.1.snd, z.2.snd)) :=
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem svGraph_optimalityMapping (g : WithLp 2 (E × F) → Set (WithLp 2 (E × F))) :
    svGraph (optimalityMapping g) = optimalityGraphEquiv ⁻¹' svGraph g := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem euclideanSvGraph_optimalityMapping (g : WithLp 2 (E × F) → Set (WithLp 2 (E × F))) :
    euclideanSvGraph (optimalityMapping g) = optimalityGraphIsometry ⁻¹' euclideanSvGraph g := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Graphical derivatives of the optimality mapping. -/
theorem graphicalDerivative_optimalityMapping (g : WithLp 2 (E × F) → Set (WithLp 2 (E × F)))
    (x : E) (u : F) (v : E) (y : F) :
    graphicalDerivative (optimalityMapping g) (WithLp.toLp 2 (u, v)) (WithLp.toLp 2 (x, y)) =
      optimalityMapping (graphicalDerivative g (WithLp.toLp 2 (x, u)) (WithLp.toLp 2 (v, y))) := by
  apply svGraph_injective
  rw [svGraph_graphicalDerivative, svGraph_optimalityMapping,
    tangentCone_preimage_continuousLinearEquiv, svGraph_optimalityMapping,
    svGraph_graphicalDerivative]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Proto-differentiability of the optimality mapping. -/
theorem isProtoDifferentiableAt_optimalityMapping_iff
    {g : WithLp 2 (E × F) → Set (WithLp 2 (E × F))} {x : E} {u : F} {v : E} {y : F}
    (hm : WithLp.toLp 2 (v, y) ∈ g (WithLp.toLp 2 (x, u))) :
    IsProtoDifferentiableAt (optimalityMapping g) (WithLp.toLp 2 (u, v)) (WithLp.toLp 2 (x, y)) ↔
      IsProtoDifferentiableAt g (WithLp.toLp 2 (x, u)) (WithLp.toLp 2 (v, y)) := by
  rw [isProtoDifferentiableAt_iff_isGeometricallyDerivable_svGraph (show
      WithLp.toLp 2 (x, y) ∈ optimalityMapping g (WithLp.toLp 2 (u, v)) from hm),
    isProtoDifferentiableAt_iff_isGeometricallyDerivable_svGraph hm, svGraph_optimalityMapping,
    isGeometricallyDerivable_preimage_continuousLinearEquiv]
  rfl

/-- Coderivatives of the optimality mapping: `(u', v') ∈ D*S(ū, v̄ ∣ x̄, ȳ)(x', y')` exactly when
`(-x', u') ∈ D*g(x̄, ū ∣ v̄, ȳ)(-v', y')`. -/
theorem mem_coderivative_optimalityMapping_iff
    {g : WithLp 2 (E × F) → Set (WithLp 2 (E × F))} {x : E} {u : F} {v : E} {y : F}
    {q : WithLp 2 (F × E)} {w : WithLp 2 (E × F)} :
    q ∈ coderivative (optimalityMapping g) (WithLp.toLp 2 (u, v)) (WithLp.toLp 2 (x, y)) w ↔
      WithLp.toLp 2 (-w.fst, q.fst) ∈ coderivative g (WithLp.toLp 2 (x, u)) (WithLp.toLp 2 (v, y))
        (WithLp.toLp 2 (-q.snd, w.snd)) := by
  change WithLp.toLp 2 (q, -w) ∈ normalCone (euclideanSvGraph (optimalityMapping g))
    (WithLp.toLp 2 (WithLp.toLp 2 (u, v), WithLp.toLp 2 (x, y))) ↔ _
  rw [euclideanSvGraph_optimalityMapping, normalCone_preimage_linearIsometryEquiv, mem_preimage,
    optimalityGraphIsometry_apply, optimalityGraphIsometry_apply]
  simp only [coderivative, svOfEuclideanNormals, mem_setOf_eq, ← WithLp.toLp_neg, Prod.neg_mk,
    neg_neg]
  rfl

end Optimality

/-! ### Theorem 13.47 -/

section Theorem

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem finrank_withLp_prod :
    Module.finrank ℝ (WithLp 2 (E × F)) = Module.finrank ℝ E + Module.finrank ℝ F := by
  rw [(WithLp.linearEquiv 2 ℝ (E × F)).finrank_eq, Module.finrank_prod]

/-- **Theorem 13.47** (perturbation of optimality conditions).  Let `f` on `ℝⁿ × ℝᵐ` be
prox-regular and subdifferentially continuous at `(x̄, ū)` for `(v̄, ȳ)`, and
`S(u, v) = {(x, y) ∣ (v, y) ∈ ∂f(x, u)}` (`optimalityMapping (∂f)`).  Then `S` is
proto-differentiable at `(ū, v̄)` for `(x̄, ȳ)` if and only if `f` is twice epi-differentiable at
`(x̄, ū)` for `(v̄, ȳ)`, and then `DS(ū, v̄ ∣ x̄, ȳ)(u', v') = {(x', y') ∣ (v', y') ∈ ∂h(x', u')}`
for `h = ½d²f(x̄, ū ∣ v̄, ȳ)`.  Moreover `S` is graphically Lipschitzian of dimension `n + m`
around `(ū, v̄; x̄, ȳ)`, and it has the Aubin property at `(ū, v̄)` for `(x̄, ȳ)` if and only if
`(0, y') ∈ D*(∂f)(x̄, ū ∣ v̄, ȳ)(x', 0)` implies `x' = 0`, `y' = 0`. -/
theorem perturbation_of_optimality_conditions {f : WithLp 2 (E × F) → EReal} {x : E} {u : F}
    {v : E} {y : F} (hpr : IsProxRegularAt f (WithLp.toLp 2 (x, u)) (WithLp.toLp 2 (v, y)))
    (hsc : IsSubdifferentiallyContinuousAt f (WithLp.toLp 2 (x, u)) (WithLp.toLp 2 (v, y))) :
    (IsProtoDifferentiableAt (optimalityMapping (subdifferential f)) (WithLp.toLp 2 (u, v))
        (WithLp.toLp 2 (x, y)) ↔
      TwiceEpiDifferentiableAt f (WithLp.toLp 2 (x, u)) (WithLp.toLp 2 (v, y))) ∧
    (TwiceEpiDifferentiableAt f (WithLp.toLp 2 (x, u)) (WithLp.toLp 2 (v, y)) →
      graphicalDerivative (optimalityMapping (subdifferential f)) (WithLp.toLp 2 (u, v))
          (WithLp.toLp 2 (x, y)) =
        optimalityMapping (subdifferential (fun w ↦ ((1 / 2 : ℝ) : EReal) *
          secondSubderivative f (WithLp.toLp 2 (x, u)) (WithLp.toLp 2 (v, y)) w))) ∧
    GraphicallyLipschitzianAt (optimalityMapping (subdifferential f)) (WithLp.toLp 2 (u, v))
      (WithLp.toLp 2 (x, y)) (Module.finrank ℝ E + Module.finrank ℝ F) ∧
    (HasAubinPropertyAt (optimalityMapping (subdifferential f)) (WithLp.toLp 2 (u, v))
        (WithLp.toLp 2 (x, y)) ↔
      ∀ (x' : E) (y' : F), WithLp.toLp 2 (0, y') ∈ coderivative (subdifferential f)
        (WithLp.toLp 2 (x, u)) (WithLp.toLp 2 (v, y)) (WithLp.toLp 2 (x', 0)) →
          x' = 0 ∧ y' = 0) := by
  have hm : WithLp.toLp 2 (v, y) ∈ subdifferential f (WithLp.toLp 2 (x, u)) := hpr.2.1
  have hmS : WithLp.toLp 2 (x, y) ∈ optimalityMapping (subdifferential f) (WithLp.toLp 2 (u, v)) :=
    hm
  obtain ⟨h40, -, -⟩ := proto_differentiability_of_subgradient_mappings hpr
  obtain ⟨hiff, hform⟩ := h40 hsc
  -- 13.46 and the transport of the graphically Lipschitzian structure
  have hgl := (lipschitzian_geometry_of_subgradient_mappings hpr).2 hsc
  rw [finrank_withLp_prod] at hgl
  have hglS : GraphicallyLipschitzianAt (optimalityMapping (subdifferential f))
      (WithLp.toLp 2 (u, v)) (WithLp.toLp 2 (x, y)) (Module.finrank ℝ E + Module.finrank ℝ F) := by
    refine hgl.of_coordinateChange (isC1CoordinateChangeAt_continuousLinearEquiv
      optimalityGraphEquiv _) rfl ?_ (Eventually.of_forall fun z ↦ Iff.rfl) hmS
    rw [finrank_withLp_prod, finrank_withLp_prod]
    ring
  refine ⟨(isProtoDifferentiableAt_optimalityMapping_iff hm).trans hiff, fun h ↦ ?_, hglS, ?_⟩
  · rw [graphicalDerivative_optimalityMapping, hform h]
  · rw [hasAubinPropertyAt_iff_coderivative_zero hmS hglS.isLocallyClosedAt]
    constructor
    · intro h0 x' y' hc
      have hq : WithLp.toLp 2 (y', -x') ∈ coderivative (optimalityMapping (subdifferential f))
          (WithLp.toLp 2 (u, v)) (WithLp.toLp 2 (x, y)) 0 := by
        rw [mem_coderivative_optimalityMapping_iff]
        simpa using hc
      rw [h0, mem_singleton_iff] at hq
      have h1 := congrArg WithLp.fst hq
      have h2 := congrArg WithLp.snd hq
      simp only [WithLp.zero_fst, WithLp.zero_snd] at h1 h2
      exact ⟨neg_eq_zero.1 h2, h1⟩
    · intro h
      refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun q hq ↦ ?_⟩
      · change WithLp.toLp 2 (0, -0) ∈ normalCone (euclideanSvGraph
          (optimalityMapping (subdifferential f)))
          (WithLp.toLp 2 (WithLp.toLp 2 (u, v), WithLp.toLp 2 (x, y)))
        rw [neg_zero]
        exact (isCone_normalCone (show WithLp.toLp 2 (WithLp.toLp 2 (u, v), WithLp.toLp 2 (x, y)) ∈
          euclideanSvGraph (optimalityMapping (subdifferential f)) from hmS)).1
      rw [mem_coderivative_optimalityMapping_iff] at hq
      simp only [WithLp.zero_fst, WithLp.zero_snd, neg_zero] at hq
      obtain ⟨h1, h2⟩ := h (-q.snd) q.fst hq
      refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_)
      · simpa using h2
      · simpa using neg_eq_zero.1 h1

end Theorem

end RW
