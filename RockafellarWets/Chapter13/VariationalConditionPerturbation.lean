/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Perturbation of solutions to variational conditions

Theorem 13.48 (`perturbation_of_solutions_to_variational_conditions`), with two misprints
corrected.

General tools: derivable cones push forward under differentiable maps
(`image_derivableCone_subset`); tangent cones and geometric derivability transfer through a map
with a global inverse, both differentiable at the base points (`tangentCone_preimage_of_inverse`);
`D × univ` is geometrically derivable when `D` is (`isGeometricallyDerivable_prod_univ`); and the
graphically Lipschitzian property survives adding a free variable to the domain
(`GraphicallyLipschitzianAt.comp_snd`).
-/

import RockafellarWets.Chapter13.OptimalityPerturbation
import RockafellarWets.Chapter13.AmenableProtoDifferentiability

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace NNReal

namespace RW

/-! ### Transport of tangent cones and derivability -/

section Transport

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- Derivable tangent vectors push forward under a differentiable map. -/
theorem image_derivableCone_subset {H : X → Y} {H' : X →L[ℝ] Y} {a : X}
    (hH : HasFDerivAt H H' a) (A : Set X) :
    H' '' derivableCone A a ⊆ derivableCone (H '' A) (H a) := by
  rintro _ ⟨w, ⟨ε, hε, ξ, h0, hA, hlim⟩, rfl⟩
  refine ⟨ε, hε, H ∘ ξ, by simp [h0], fun t ht ↦ ⟨ξ t, hA t ht, rfl⟩, ?_⟩
  have hd : HasDerivWithinAt ξ w (Ioi 0) 0 := by
    rw [hasDerivWithinAt_iff_tendsto_slope, show Ioi (0 : ℝ) \ {0} = Ioi 0 by
      ext t; simp only [mem_diff, mem_Ioi, mem_singleton_iff]; constructor
      · rintro ⟨h, -⟩; exact h
      · intro h; exact ⟨h, ne_of_gt h⟩]
    refine hlim.congr fun t ↦ ?_
    rw [slope_def_module, h0, sub_zero]
  have hH' : HasFDerivAt H H' (ξ 0) := by rw [h0]; exact hH
  have hc := hH'.comp_hasDerivWithinAt (0 : ℝ) hd
  rw [hasDerivWithinAt_iff_tendsto_slope, show Ioi (0 : ℝ) \ {0} = Ioi 0 by
    ext t; simp only [mem_diff, mem_Ioi, mem_singleton_iff]; constructor
    · rintro ⟨h, -⟩; exact h
    · intro h; exact ⟨h, ne_of_gt h⟩] at hc
  refine hc.congr fun t ↦ ?_
  rw [slope_def_module, Function.comp_apply, Function.comp_apply, h0, sub_zero]

/-- Tangent cones and geometric derivability transfer through a map with a global inverse, both
differentiable at the base points with mutually inverse derivatives. -/
theorem tangentCone_preimage_of_inverse {Θ : X → Y} {Θ' : Y → X} (h1 : ∀ x, Θ' (Θ x) = x)
    (h2 : ∀ y, Θ (Θ' y) = y) {a : X} {L : X →L[ℝ] Y} {L' : Y →L[ℝ] X}
    (hΘ : HasFDerivAt Θ L a) (hΘ' : HasFDerivAt Θ' L' (Θ a)) (hLL : ∀ v, L' (L v) = v)
    (D : Set Y) :
    tangentCone (Θ ⁻¹' D) a = L ⁻¹' tangentCone D (Θ a) ∧
      (IsGeometricallyDerivable D (Θ a) → IsGeometricallyDerivable (Θ ⁻¹' D) a) := by
  have himg : Θ' '' D = Θ ⁻¹' D := by
    ext y
    constructor
    · rintro ⟨d, hd, rfl⟩; rw [mem_preimage, h2]; exact hd
    · intro hy; exact ⟨Θ y, hy, h1 y⟩
  have himg2 : Θ '' (Θ ⁻¹' D) ⊆ D := image_preimage_subset Θ D
  have hpush : ∀ ξ ∈ tangentCone (Θ ⁻¹' D) a, L ξ ∈ tangentCone D (Θ a) := fun ξ hξ ↦
    tangentCone_mono himg2 (Θ a) (image_tangentCone_subset hΘ (Θ ⁻¹' D) ⟨ξ, hξ, rfl⟩)
  refine ⟨Subset.antisymm (fun ξ hξ ↦ hpush ξ hξ) (fun ξ hξ ↦ ?_), fun hD ξ hξ ↦ ?_⟩
  · have := image_tangentCone_subset hΘ' D ⟨L ξ, hξ, rfl⟩
    rwa [hLL, himg, h1] at this
  · have h3 : L ξ ∈ derivableCone D (Θ a) := hD (hpush ξ hξ)
    have := image_derivableCone_subset hΘ' D ⟨L ξ, h3, rfl⟩
    rwa [hLL, himg, h1] at this

/-- `D × univ` is geometrically derivable at `(a, b)` when `D` is at `a`. -/
theorem isGeometricallyDerivable_prod_univ {D : Set X} {a : X} (b : Y)
    (hD : IsGeometricallyDerivable D a) :
    IsGeometricallyDerivable (D ×ˢ (univ : Set Y)) (a, b) := by
  rintro ⟨w₁, w₂⟩ hw
  rw [tangentCone_prod_univ] at hw
  obtain ⟨ε, hε, ξ, h0, hA, hlim⟩ := hD hw.1
  refine ⟨ε, hε, fun t ↦ (ξ t, b + t • w₂), by simp [h0], fun t ht ↦ ⟨hA t ht, mem_univ _⟩, ?_⟩
  have h2 : Tendsto (fun t : ℝ ↦ t⁻¹ • (b + t • w₂ - b)) (𝓝[>] (0 : ℝ)) (𝓝 w₂) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (ne_of_gt ht), one_smul]
  have := hlim.prodMk_nhds h2
  refine this.congr fun t ↦ ?_
  simp only [Prod.smul_mk, Prod.mk_sub_mk]

end Transport

/-! ### Graphically Lipschitzian mappings with a free variable -/

section FreeVariable

variable {W E F : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- If `T` is graphically Lipschitzian of dimension `n` at `(x̄, v̄)`, then `(w, x) ↦ T(x)` is
graphically Lipschitzian of dimension `dim W + n` at `((w̄, x̄), v̄)`. -/
theorem GraphicallyLipschitzianAt.comp_snd {T : E → Set F} {x : E} {v : F} {n : ℕ}
    (hT : GraphicallyLipschitzianAt T x v n) (w : W) :
    GraphicallyLipschitzianAt (fun q : WithLp 2 (W × E) ↦ T q.snd) (WithLp.toLp 2 (w, x)) v
      (Module.finrank ℝ W + n) := by
  obtain ⟨hv, e, he, Φ, Ψ, g, hΦ, hg, hgr⟩ := hT
  have hdim : Module.finrank ℝ (W × EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ W + n))) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  set K := ContinuousLinearEquiv.ofFinrankEq hdim with hK
  set π : WithLp 2 (W × E) × F → E × F := fun p ↦ (p.1.snd, p.2) with hπ
  have hπl : Continuous π := by fun_prop
  set Φ' : WithLp 2 (W × E) × F →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ W + n)) × EuclideanSpace ℝ (Fin e) :=
    fun p ↦ (K (p.1.fst, (Φ (π p)).1), (Φ (π p)).2) with hΦ'
  set Ψ' : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + n)) × EuclideanSpace ℝ (Fin e) →
      WithLp 2 (W × E) × F :=
    fun ζ ↦ (WithLp.toLp 2 ((K.symm ζ.1).1, (Ψ ((K.symm ζ.1).2, ζ.2)).1),
      (Ψ ((K.symm ζ.1).2, ζ.2)).2) with hΨ'
  set g' : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + n)) → EuclideanSpace ℝ (Fin e) :=
    fun ξ ↦ g (K.symm ξ).2 with hg'
  set p₀ : WithLp 2 (W × E) × F := (WithLp.toLp 2 (w, x), v) with hp₀
  have hπp : π p₀ = (x, v) := rfl
  obtain ⟨hC1, hC2, hC3, hC4, hC5⟩ := hΦ
  -- smoothness of `π` and its partner
  have hπd : ContDiff ℝ 1 π := by
    have : π = fun p : WithLp 2 (W × E) × F ↦
        ((WithLp.sndL 2 ℝ W E) p.1, p.2) := rfl
    rw [this]
    exact ((WithLp.sndL 2 ℝ W E).contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hΦπ : ContDiffAt ℝ 1 (fun p ↦ Φ (π p)) p₀ := by
    have : ContDiffAt ℝ 1 Φ (π p₀) := by rw [hπp]; exact hC1
    exact this.comp p₀ hπd.contDiffAt
  have hΦ'd : ContDiffAt ℝ 1 Φ' p₀ := by
    have h1 : ContDiffAt ℝ 1 (fun p : WithLp 2 (W × E) × F ↦ (p.1.fst, (Φ (π p)).1)) p₀ :=
      (((WithLp.fstL 2 ℝ W E).contDiff.comp contDiff_fst).contDiffAt).prodMk
        (contDiffAt_fst.comp p₀ hΦπ)
    exact (K.contDiff.contDiffAt.comp p₀ h1).prodMk (contDiffAt_snd.comp p₀ hΦπ)
  have hΦ'p : Φ' p₀ = (K (w, (Φ (x, v)).1), (Φ (x, v)).2) := rfl
  have hKs : ∀ a b, K.symm (K (a, b)) = (a, b) := fun a b ↦ K.symm_apply_apply _
  have hΨ'p : Ψ' (Φ' p₀) = p₀ := by
    rw [hΦ'p]
    simp only [hΨ', hKs]
    rw [show ((Φ (x, v)).1, (Φ (x, v)).2) = Φ (x, v) from rfl, hC3]
  have hΨd : ContDiffAt ℝ 1 Ψ' (Φ' p₀) := by
    set σ : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + n)) × EuclideanSpace ℝ (Fin e) →
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin e) := fun ζ ↦ ((K.symm ζ.1).2, ζ.2)
      with hσ
    have hσd : ContDiff ℝ 1 σ :=
      (contDiff_snd.comp (K.symm.contDiff.comp contDiff_fst)).prodMk contDiff_snd
    have hσp : σ (Φ' p₀) = Φ (x, v) := by rw [hΦ'p]; simp only [hσ, hKs]
    have hΨσ : ContDiffAt ℝ 1 (fun ζ ↦ Ψ (σ ζ)) (Φ' p₀) := by
      have : ContDiffAt ℝ 1 Ψ (σ (Φ' p₀)) := by rw [hσp]; exact hC2
      exact this.comp _ hσd.contDiffAt
    have h1 : ContDiffAt ℝ 1 (fun ζ ↦ ((K.symm ζ.1).1, (Ψ (σ ζ)).1)) (Φ' p₀) :=
      ((contDiff_fst.comp (K.symm.contDiff.comp contDiff_fst)).contDiffAt).prodMk
        (contDiffAt_fst.comp _ hΨσ)
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ W E).symm.contDiff.contDiffAt.comp _ h1).prodMk
      (contDiffAt_snd.comp _ hΨσ)
  have hπt : Tendsto π (𝓝 p₀) (𝓝 (x, v)) := by
    have := hπl.tendsto p₀; rwa [hπp] at this
  have hσt : Tendsto (fun ζ : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + n)) ×
      EuclideanSpace ℝ (Fin e) ↦ ((K.symm ζ.1).2, ζ.2)) (𝓝 (Φ' p₀)) (𝓝 (Φ (x, v))) := by
    have hc : Continuous (fun ζ : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + n)) ×
        EuclideanSpace ℝ (Fin e) ↦ ((K.symm ζ.1).2, ζ.2)) := by fun_prop
    have := hc.tendsto (Φ' p₀)
    rw [hΦ'p] at this
    simpa [hKs] using this
  refine ⟨hv, e, by rw [finrank_withLp_prod]; omega, Φ', Ψ', g', ⟨hΦ'd, hΨd, hΨ'p, ?_, ?_⟩, ?_, ?_⟩
  · filter_upwards [hπt.eventually hC4] with p hp
    obtain ⟨q, z⟩ := p
    simp only [hΨ', hΦ', hKs]
    rw [show ((Φ (π (q, z))).1, (Φ (π (q, z))).2) = Φ (π (q, z)) from rfl, hp]
    rfl
  · filter_upwards [hσt.eventually hC5] with ζ hζ
    obtain ⟨ξ, η⟩ := ζ
    simp only at hζ
    simp only [hΦ', hΨ', hπ, WithLp.toLp_fst, WithLp.toLp_snd]
    rw [show ((Ψ ((K.symm ξ).2, η)).1, (Ψ ((K.symm ξ).2, η)).2) = Ψ ((K.symm ξ).2, η) from rfl,
      hζ]
    simp only [Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply]
  · -- strict continuity of `g'`
    obtain ⟨k, U, hU, hL⟩ := strictlyContinuousAt_iff.1 hg
    have hpt : (K.symm (Φ' p₀).1).2 = (Φ (x, v)).1 := by
      rw [hΦ'p]; simp only [hKs]
    set M : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      (ContinuousLinearMap.snd ℝ W (EuclideanSpace ℝ (Fin n))).comp K.symm.toContinuousLinearMap
      with hM
    have hMap : ∀ ξ, M ξ = (K.symm ξ).2 := fun ξ ↦ rfl
    have hV : M ⁻¹' U ∈ 𝓝 (Φ' p₀).1 := by
      apply M.continuous.continuousAt.preimage_mem_nhds
      rw [hMap, hpt]; exact hU
    refine strictlyContinuousAt_iff.2 ⟨k * ‖M‖₊, M ⁻¹' U, hV, ?_⟩
    have := hL.comp (M.lipschitz.lipschitzOnWith (s := M ⁻¹' U)) (fun _ ha ↦ ha)
    simpa [hg', hMap, Function.comp] using this
  · filter_upwards [hπt.eventually hgr] with p hp
    obtain ⟨q, z⟩ := p
    change z ∈ T q.snd ↔ (Φ (q.snd, z)).2 = g (K.symm (K (q.fst, (Φ (q.snd, z)).1))).2
    rw [hKs]
    exact hp

end FreeVariable

/-! ### Theorem 13.48 -/

section Theorem1348

universe u

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The solution mapping `S(w, u) = {x ∣ F(w, x) + ∂f(x) ∋ u}` of Theorem 13.48. -/
def variationalSolutionMapping (F : WithLp 2 (W × E) → E) (f : E → EReal)
    (p : WithLp 2 (W × E)) : Set E :=
  {y | p.snd - F (WithLp.toLp 2 (p.fst, y)) ∈ subdifferential f y}

/-- The embedding `x ↦ (0, x)` of `ℝⁿ` into `ℝᵈ × ℝⁿ`. -/
noncomputable def embedSnd : E →L[ℝ] WithLp 2 (W × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ W E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ W E)

/-- The embedding `w ↦ (w, 0)` of `ℝᵈ` into `ℝᵈ × ℝⁿ`. -/
noncomputable def embedFst : W →L[ℝ] WithLp 2 (W × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ W E).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ W E)

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
@[simp] theorem embedSnd_apply (y : E) : (embedSnd (W := W) y) = WithLp.toLp 2 (0, y) := rfl

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
@[simp] theorem embedFst_apply (w : W) : (embedFst (E := E) w) = WithLp.toLp 2 (w, 0) := rfl

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
theorem toLp_eq_embedFst_add_embedSnd (w : W) (y : E) :
    WithLp.toLp 2 (w, y) = embedFst w + embedSnd y := by
  refine WithLp.ofLp_injective 2 (Prod.ext ?_ ?_) <;> simp

/-- The linear map `(p, y) ↦ (p.1, y)`. -/
noncomputable def pairFstL : WithLp 2 (W × E) × E →L[ℝ] WithLp 2 (W × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ W E).symm.toContinuousLinearMap.comp
    (((WithLp.fstL 2 ℝ W E).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      (ContinuousLinearMap.snd ℝ _ _))

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
@[simp] theorem pairFstL_apply (q : WithLp 2 (W × E) × E) :
    pairFstL q = WithLp.toLp 2 (q.1.fst, q.2) := rfl

/-- The linear map `((y, z), w) ↦ (w, y)`. -/
noncomputable def pairBackL : (E × E) × W →L[ℝ] WithLp 2 (W × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ W E).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.snd ℝ _ _).prod
      ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ _ _)))

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
@[simp] theorem pairBackL_apply (r : (E × E) × W) :
    pairBackL r = WithLp.toLp 2 (r.2, r.1.1) := rfl

/-- The graph change of coordinates `((w, u), x) ↦ ((x, u - F(w, x)), w)`. -/
noncomputable def variationalGraphMap (F : WithLp 2 (W × E) → E)
    (q : WithLp 2 (W × E) × E) : (E × E) × W :=
  ((q.2, q.1.snd - F (WithLp.toLp 2 (q.1.fst, q.2))), q.1.fst)

/-- Its inverse `((x, z), w) ↦ ((w, z + F(w, x)), x)`. -/
noncomputable def variationalGraphInv (F : WithLp 2 (W × E) → E) (r : (E × E) × W) :
    WithLp 2 (W × E) × E :=
  (WithLp.toLp 2 (r.2, r.1.2 + F (WithLp.toLp 2 (r.2, r.1.1))), r.1.1)

omit [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem variationalGraphInv_map (F : WithLp 2 (W × E) → E) (q : WithLp 2 (W × E) × E) :
    variationalGraphInv F (variationalGraphMap F q) = q := by
  obtain ⟨p, y⟩ := q
  simp only [variationalGraphInv, variationalGraphMap, sub_add_cancel]
  rfl

omit [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem variationalGraphMap_inv (F : WithLp 2 (W × E) → E) (r : (E × E) × W) :
    variationalGraphMap F (variationalGraphInv F r) = r := by
  obtain ⟨⟨y, z⟩, w⟩ := r
  simp only [variationalGraphInv, variationalGraphMap, WithLp.toLp_fst, WithLp.toLp_snd,
    add_sub_cancel_right]

omit [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [FiniteDimensional ℝ E] in
theorem svGraph_variationalSolutionMapping (F : WithLp 2 (W × E) → E) (f : E → EReal) :
    svGraph (variationalSolutionMapping F f) =
      variationalGraphMap F ⁻¹' (svGraph (subdifferential f) ×ˢ (univ : Set W)) := by
  ext ⟨p, y⟩
  simp only [mem_preimage, variationalGraphMap, mem_prod, mem_univ, and_true]
  rfl

/-- The derivative of the change of coordinates. -/
noncomputable def variationalGraphMapDeriv (A : WithLp 2 (W × E) →L[ℝ] E) :
    WithLp 2 (W × E) × E →L[ℝ] (E × E) × W :=
  ((ContinuousLinearMap.snd ℝ _ _).prod
    ((WithLp.sndL 2 ℝ W E).comp (ContinuousLinearMap.fst ℝ _ _) - A.comp pairFstL)).prod
    ((WithLp.fstL 2 ℝ W E).comp (ContinuousLinearMap.fst ℝ _ _))

/-- The derivative of the inverse change of coordinates. -/
noncomputable def variationalGraphInvDeriv (A : WithLp 2 (W × E) →L[ℝ] E) :
    (E × E) × W →L[ℝ] WithLp 2 (W × E) × E :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ W E).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.snd ℝ _ _).prod
      ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ _ _) +
        A.comp pairBackL))).prod
    ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ _ _))

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
theorem variationalGraphMapDeriv_apply (A : WithLp 2 (W × E) →L[ℝ] E)
    (q : WithLp 2 (W × E) × E) :
    variationalGraphMapDeriv A q = ((q.2, q.1.snd - A (pairFstL q)), q.1.fst) := rfl

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
theorem variationalGraphInvDeriv_map (A : WithLp 2 (W × E) →L[ℝ] E) (q : WithLp 2 (W × E) × E) :
    variationalGraphInvDeriv A (variationalGraphMapDeriv A q) = q := by
  obtain ⟨p, y⟩ := q
  simp only [variationalGraphInvDeriv, variationalGraphMapDeriv_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.add_apply, pairBackL_apply, pairFstL_apply, sub_add_cancel,
    ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply]
  rfl

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
theorem hasFDerivAt_variationalGraphMap {F : WithLp 2 (W × E) → E} {q : WithLp 2 (W × E) × E}
    {a : WithLp 2 (W × E)} (ha : WithLp.toLp 2 (q.1.fst, q.2) = a) (hF : DifferentiableAt ℝ F a) :
    HasFDerivAt (variationalGraphMap F) (variationalGraphMapDeriv (fderiv ℝ F a)) q := by
  have h0 : HasFDerivAt (F ∘ pairFstL) ((fderiv ℝ F a).comp pairFstL) q := by
    have hF' : HasFDerivAt F (fderiv ℝ F a) (pairFstL q) := by
      rw [pairFstL_apply, ha]; exact hF.hasFDerivAt
    exact hF'.comp q (pairFstL (W := W) (E := E)).hasFDerivAt
  have e : (F ∘ pairFstL) = fun q : WithLp 2 (W × E) × E ↦ F (WithLp.toLp 2 (q.1.fst, q.2)) :=
    funext fun q ↦ by simp only [Function.comp_apply, pairFstL_apply]
  have h1 : HasFDerivAt (fun q : WithLp 2 (W × E) × E ↦ F (WithLp.toLp 2 (q.1.fst, q.2)))
      ((fderiv ℝ F a).comp pairFstL) q := by rw [← e]; exact h0
  have h2 : HasFDerivAt (fun q : WithLp 2 (W × E) × E ↦ q.1.snd)
      ((WithLp.sndL 2 ℝ W E).comp (ContinuousLinearMap.fst ℝ _ _)) q :=
    ((WithLp.sndL 2 ℝ W E).comp (ContinuousLinearMap.fst ℝ _ E)).hasFDerivAt
  have h3 : HasFDerivAt (fun q : WithLp 2 (W × E) × E ↦ q.1.fst)
      ((WithLp.fstL 2 ℝ W E).comp (ContinuousLinearMap.fst ℝ _ _)) q :=
    ((WithLp.fstL 2 ℝ W E).comp (ContinuousLinearMap.fst ℝ _ E)).hasFDerivAt
  exact (hasFDerivAt_snd.prodMk (h2.sub h1)).prodMk h3

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
theorem hasFDerivAt_variationalGraphInv {F : WithLp 2 (W × E) → E} {r : (E × E) × W}
    {a : WithLp 2 (W × E)} (ha : WithLp.toLp 2 (r.2, r.1.1) = a) (hF : DifferentiableAt ℝ F a) :
    HasFDerivAt (variationalGraphInv F) (variationalGraphInvDeriv (fderiv ℝ F a)) r := by
  have h0 : HasFDerivAt (F ∘ pairBackL) ((fderiv ℝ F a).comp pairBackL) r := by
    have hF' : HasFDerivAt F (fderiv ℝ F a) (pairBackL r) := by
      rw [pairBackL_apply, ha]; exact hF.hasFDerivAt
    exact hF'.comp r (pairBackL (W := W) (E := E)).hasFDerivAt
  have e : (F ∘ pairBackL) = fun r : (E × E) × W ↦ F (WithLp.toLp 2 (r.2, r.1.1)) :=
    funext fun r ↦ by simp only [Function.comp_apply, pairBackL_apply]
  have h1 : HasFDerivAt (fun r : (E × E) × W ↦ F (WithLp.toLp 2 (r.2, r.1.1)))
      ((fderiv ℝ F a).comp pairBackL) r := by rw [← e]; exact h0
  have h2 : HasFDerivAt (fun r : (E × E) × W ↦ r.1.2)
      ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ _ _)) r :=
    ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ _ W)).hasFDerivAt
  have h3 : HasFDerivAt (fun r : (E × E) × W ↦ r.1.1)
      ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ _ _)) r :=
    ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ _ W)).hasFDerivAt
  have h4 := (hasFDerivAt_snd.prodMk (h2.add h1))
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ W E).symm.hasFDerivAt.comp r h4).prodMk h3

/-- The first three clauses of **Theorem 13.48**: proto-differentiability with the derivative
formula, and the graphically Lipschitzian property. -/
theorem variationalSolutionMapping_proto {F : WithLp 2 (W × E) → E} (hF : ContDiff ℝ 1 F)
    {f : E → EReal} {w : W} {u x : E}
    (hx : x ∈ variationalSolutionMapping F f (WithLp.toLp 2 (w, u))) (hf : FullyAmenableAt f x) :
    IsProtoDifferentiableAt (variationalSolutionMapping F f) (WithLp.toLp 2 (w, u)) x ∧
    (∀ (w' : W) (u' : E), graphicalDerivative (variationalSolutionMapping F f)
        (WithLp.toLp 2 (w, u)) x (WithLp.toLp 2 (w', u')) =
      {x' | u' - fderiv ℝ F (WithLp.toLp 2 (w, x)) (WithLp.toLp 2 (w', x')) ∈
        subdifferential (fun z ↦ ((1 / 2 : ℝ) : EReal) *
          secondSubderivative f x (u - F (WithLp.toLp 2 (w, x))) z) x'}) ∧
    GraphicallyLipschitzianAt (variationalSolutionMapping F f) (WithLp.toLp 2 (w, u)) x
      (Module.finrank ℝ W + Module.finrank ℝ E) := by
  set v := u - F (WithLp.toLp 2 (w, x)) with hv_def
  have hv : v ∈ subdifferential f x := hx
  obtain ⟨hpr, hsc⟩ := hf.stronglyAmenableAt.isProxRegularAt hv
  obtain ⟨hproto, hD⟩ := hf.isProtoDifferentiableAt hv
  have hgl := (lipschitzian_geometry_of_subgradient_mappings hpr).2 hsc
  set p₀ : WithLp 2 (W × E) := WithLp.toLp 2 (w, u) with hp₀
  set A := fderiv ℝ F (WithLp.toLp 2 (w, x)) with hA
  have hdiff : DifferentiableAt ℝ F (WithLp.toLp 2 (w, x)) := hF.differentiable one_ne_zero _
  have hΘ : HasFDerivAt (variationalGraphMap F) (variationalGraphMapDeriv A) (p₀, x) :=
    hasFDerivAt_variationalGraphMap (by rw [hp₀]; rfl) hdiff
  have hmap : variationalGraphMap F (p₀, x) = ((x, v), w) := by
    simp only [variationalGraphMap, hp₀, WithLp.toLp_fst, WithLp.toLp_snd, hv_def]
  have hΘ' : HasFDerivAt (variationalGraphInv F) (variationalGraphInvDeriv A)
      (variationalGraphMap F (p₀, x)) := by
    rw [hmap]; exact hasFDerivAt_variationalGraphInv rfl hdiff
  obtain ⟨htan, hder⟩ := tangentCone_preimage_of_inverse (variationalGraphInv_map F)
    (variationalGraphMap_inv F) hΘ hΘ' (variationalGraphInvDeriv_map A)
    (svGraph (subdifferential f) ×ˢ (univ : Set W))
  rw [← svGraph_variationalSolutionMapping, hmap, tangentCone_prod_univ] at htan
  rw [← svGraph_variationalSolutionMapping, hmap] at hder
  have hgd : IsGeometricallyDerivable (svGraph (subdifferential f)) (x, v) :=
    (isProtoDifferentiableAt_iff_isGeometricallyDerivable_svGraph hv).1 hproto
  refine ⟨(isProtoDifferentiableAt_iff_isGeometricallyDerivable_svGraph hx).2
      (hder (isGeometricallyDerivable_prod_univ w hgd)), fun w' u' ↦ ?_, ?_⟩
  · ext x'
    have h1 := Set.ext_iff.1 (svGraph_graphicalDerivative (variationalSolutionMapping F f) p₀ x)
      (WithLp.toLp 2 (w', u'), x')
    rw [htan] at h1
    change x' ∈ graphicalDerivative _ p₀ x _ ↔ _
    rw [show x' ∈ graphicalDerivative (variationalSolutionMapping F f) p₀ x
        (WithLp.toLp 2 (w', u')) ↔
      (WithLp.toLp 2 (w', u'), x') ∈ svGraph (graphicalDerivative (variationalSolutionMapping F f)
        p₀ x) from Iff.rfl, h1]
    simp only [mem_preimage, variationalGraphMapDeriv_apply, mem_prod, mem_univ, and_true,
      pairFstL_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    rw [← svGraph_graphicalDerivative, hD]
    rfl
  · -- the graphically Lipschitzian property
    have hgl' := hgl.comp_snd w
    set Θ₁ : WithLp 2 (W × E) × E → WithLp 2 (W × E) × E :=
      fun q ↦ (WithLp.toLp 2 (q.1.fst, q.2), q.1.snd - F (WithLp.toLp 2 (q.1.fst, q.2))) with hΘ₁
    set Θ₁' : WithLp 2 (W × E) × E → WithLp 2 (W × E) × E :=
      fun r ↦ (WithLp.toLp 2 (r.1.fst, r.2 + F r.1), r.1.snd) with hΘ₁'
    have hι : ContDiff ℝ 1 (fun q : WithLp 2 (W × E) × E ↦ WithLp.toLp 2 (q.1.fst, q.2)) := by
      have e : ⇑(pairFstL (W := W) (E := E)) = fun q ↦ WithLp.toLp 2 (q.1.fst, q.2) :=
        funext pairFstL_apply
      rw [← e]; exact (pairFstL (W := W) (E := E)).contDiff
    have hc1 : ContDiff ℝ 1 Θ₁ :=
      hι.prodMk (((WithLp.sndL 2 ℝ W E).contDiff.comp contDiff_fst).sub (hF.comp hι))
    have hc2 : ContDiff ℝ 1 Θ₁' := by
      have h := hF.comp (contDiff_fst (𝕜 := ℝ) (E := WithLp 2 (W × E)) (F := E))
      have h2 : ContDiff ℝ 1 (fun r : WithLp 2 (W × E) × E ↦ (r.1.fst, r.2 + F r.1)) :=
        ((WithLp.fstL 2 ℝ W E).contDiff.comp contDiff_fst).prodMk (contDiff_snd.add h)
      exact ((WithLp.prodContinuousLinearEquiv 2 ℝ W E).symm.contDiff.comp h2).prodMk
        ((WithLp.sndL 2 ℝ W E).contDiff.comp contDiff_fst)
    have hinv1 : ∀ q, Θ₁' (Θ₁ q) = q := by
      rintro ⟨p, y⟩
      simp only [hΘ₁, hΘ₁', WithLp.toLp_fst, WithLp.toLp_snd, sub_add_cancel]
      rfl
    have hinv2 : ∀ r, Θ₁ (Θ₁' r) = r := by
      rintro ⟨q, z⟩
      simp only [hΘ₁, hΘ₁', WithLp.toLp_fst, WithLp.toLp_snd]
      rw [show WithLp.toLp 2 (q.fst, q.snd) = q from rfl, add_sub_cancel_right]
    have hcc : IsC1CoordinateChangeAt Θ₁ Θ₁' (p₀, x) :=
      ⟨hc1.contDiffAt, hc2.contDiffAt, hinv1 _, Eventually.of_forall hinv1,
        Eventually.of_forall hinv2⟩
    have hΘp : Θ₁ (p₀, x) = (WithLp.toLp 2 (w, x), v) := by
      simp only [hΘ₁, hp₀, WithLp.toLp_fst, WithLp.toLp_snd, hv_def]
    exact hgl'.of_coordinateChange hcc hΘp rfl (Eventually.of_forall fun z ↦ Iff.rfl) hx

/-- The Euclidean form `((w, u), x) ↦ (x, u - F(w, x))` of the graph map, a submersion. -/
noncomputable def variationalSubmersion (F : WithLp 2 (W × E) → E)
    (q : WithLp 2 (WithLp 2 (W × E) × E)) : WithLp 2 (E × E) :=
  WithLp.toLp 2 (q.snd, q.fst.snd - F (WithLp.toLp 2 (q.fst.fst, q.snd)))

omit [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [FiniteDimensional ℝ E] in
theorem euclideanSvGraph_variationalSolutionMapping (F : WithLp 2 (W × E) → E) (f : E → EReal) :
    euclideanSvGraph (variationalSolutionMapping F f) =
      variationalSubmersion F ⁻¹' euclideanSvGraph (subdifferential f) := rfl

/-- The linear map `q ↦ (q.1.1, q.2)` on the Euclidean graph space. -/
noncomputable def pairFstE : WithLp 2 (WithLp 2 (W × E) × E) →L[ℝ] WithLp 2 (W × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ W E).symm.toContinuousLinearMap.comp
    (((WithLp.fstL 2 ℝ W E).comp (WithLp.fstL 2 ℝ (WithLp 2 (W × E)) E)).prod
      (WithLp.sndL 2 ℝ (WithLp 2 (W × E)) E))

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
@[simp] theorem pairFstE_apply (q : WithLp 2 (WithLp 2 (W × E) × E)) :
    pairFstE q = WithLp.toLp 2 (q.fst.fst, q.snd) := rfl

/-- The derivative of `variationalSubmersion`. -/
noncomputable def variationalSubmersionDeriv (A : WithLp 2 (W × E) →L[ℝ] E) :
    WithLp 2 (WithLp 2 (W × E) × E) →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
    ((WithLp.sndL 2 ℝ (WithLp 2 (W × E)) E).prod
      ((WithLp.sndL 2 ℝ W E).comp (WithLp.fstL 2 ℝ (WithLp 2 (W × E)) E) - A.comp pairFstE))

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
theorem variationalSubmersionDeriv_apply (A : WithLp 2 (W × E) →L[ℝ] E)
    (q : WithLp 2 (WithLp 2 (W × E) × E)) :
    variationalSubmersionDeriv A q =
      WithLp.toLp 2 (q.snd, q.fst.snd - A (WithLp.toLp 2 (q.fst.fst, q.snd))) := rfl

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ E] in
theorem hasFDerivAt_variationalSubmersion {F : WithLp 2 (W × E) → E}
    {q : WithLp 2 (WithLp 2 (W × E) × E)} {a : WithLp 2 (W × E)}
    (ha : WithLp.toLp 2 (q.fst.fst, q.snd) = a) (hF : DifferentiableAt ℝ F a) :
    HasFDerivAt (variationalSubmersion F) (variationalSubmersionDeriv (fderiv ℝ F a)) q := by
  have h0 : HasFDerivAt (F ∘ pairFstE) ((fderiv ℝ F a).comp pairFstE) q := by
    have hF' : HasFDerivAt F (fderiv ℝ F a) (pairFstE q) := by
      rw [pairFstE_apply, ha]; exact hF.hasFDerivAt
    exact hF'.comp q (pairFstE (W := W) (E := E)).hasFDerivAt
  have e : (F ∘ pairFstE) = fun q : WithLp 2 (WithLp 2 (W × E) × E) ↦
      F (WithLp.toLp 2 (q.fst.fst, q.snd)) :=
    funext fun q ↦ by simp only [Function.comp_apply, pairFstE_apply]
  have h1 : HasFDerivAt (fun q : WithLp 2 (WithLp 2 (W × E) × E) ↦
      F (WithLp.toLp 2 (q.fst.fst, q.snd))) ((fderiv ℝ F a).comp pairFstE) q := by
    rw [← e]; exact h0
  have h2 : HasFDerivAt (fun q : WithLp 2 (WithLp 2 (W × E) × E) ↦ q.fst.snd)
      ((WithLp.sndL 2 ℝ W E).comp (WithLp.fstL 2 ℝ (WithLp 2 (W × E)) E)) q :=
    ((WithLp.sndL 2 ℝ W E).comp (WithLp.fstL 2 ℝ (WithLp 2 (W × E)) E)).hasFDerivAt
  have h3 : HasFDerivAt (fun q : WithLp 2 (WithLp 2 (W × E) × E) ↦ q.snd)
      (WithLp.sndL 2 ℝ (WithLp 2 (W × E)) E) q :=
    (WithLp.sndL 2 ℝ (WithLp 2 (W × E)) E).hasFDerivAt
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.hasFDerivAt.comp q (h3.prodMk (h2.sub h1))

/-- The adjoint of the derivative: `(a, b) ↦ ((-∇_wF* b, b), a - ∇_xF* b)`. -/
theorem variationalSubmersionDeriv_adjoint (A : WithLp 2 (W × E) →L[ℝ] E) (a b : E) :
    (variationalSubmersionDeriv A).adjoint (WithLp.toLp 2 (a, b)) =
      WithLp.toLp 2 (WithLp.toLp 2 (-(A.comp embedFst).adjoint b, b),
        a - (A.comp embedSnd).adjoint b) := by
  refine ext_inner_right ℝ fun q ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left, variationalSubmersionDeriv_apply,
    toLp_eq_embedFst_add_embedSnd q.fst.fst q.snd]
  simp only [WithLp.prod_inner_apply, map_add, inner_sub_left, inner_sub_right, inner_add_right,
    inner_neg_left]
  rw [← ContinuousLinearMap.comp_apply A embedFst, ← ContinuousLinearMap.comp_apply A embedSnd,
    ← ContinuousLinearMap.adjoint_inner_left (A.comp embedFst),
    ← ContinuousLinearMap.adjoint_inner_left (A.comp embedSnd)]
  have e1 : q.ofLp.1.ofLp.1 = q.fst.fst := rfl
  have e2 : q.ofLp.1.ofLp.2 = q.fst.snd := rfl
  have e3 : q.ofLp.2 = q.snd := rfl
  rw [e1, e2, e3]
  ring

/-- **Theorem 13.48** (perturbation of solutions to variational conditions), with two misprints
corrected.  For `f : ℝⁿ → ℝ̄` fully amenable at `x̄`, a `C¹` mapping `F : ℝᵈ × ℝⁿ → ℝⁿ` and
`S(w, u) = {x ∣ F(w, x) + ∂f(x) ∋ u}` with `x̄ ∈ S(w̄, ū)` and `v̄ = ū - F(w̄, x̄)`: `S` is
proto-differentiable at `(w̄, ū)` for `x̄` with
`DS(w̄, ū ∣ x̄)(w', u') = {x' ∣ Φ(w', x') + ∂φ(x') ∋ u'}`, `Φ = ∇F(w̄, x̄)`, `φ = ½d²f(x̄ ∣ v̄)`;
`S` is graphically Lipschitzian of dimension `d + n` around `(w̄, ū, x̄)`; and `S` has the Aubin
property at `(w̄, ū)` for `x̄` if and only if `-∇ₓF(w̄, x̄)* z ∈ D*(∂f)(x̄ ∣ v̄)(z)` implies
`z = 0`.
Corrections, both of misprints (no hypothesis is added and no conclusion weakened): the book writes
"proto-differentiable at `(w̄, v̄)`" for `(w̄, ū)`, and "dimension `d + 2n`" — the graph lies in
`ℝᵈ × ℝⁿ × ℝⁿ` but is a Lipschitzian manifold of dimension `d + n` (the graph of `∂f` has
dimension `n` in `ℝⁿ × ℝⁿ`, 13.46, and `w` is free); dimension `d + 2n` (complementary dimension
`0` in 9.66) would make `gph S` a neighborhood of `(w̄, ū, x̄)`
(`svGraph_mem_nhds_of_graphicallyLipschitzianAt_full`), which fails already for `f = 0`,
`F(w, x) = x`, where `S(w, u) = {u}`
(`VariationalConditionPerturbationCounterexample.not_graphicallyLipschitzianAt_full_variational`).
-/
theorem perturbation_of_solutions_to_variational_conditions {F : WithLp 2 (W × E) → E}
    (hF : ContDiff ℝ 1 F) {f : E → EReal} {w : W} {u x : E}
    (hx : x ∈ variationalSolutionMapping F f (WithLp.toLp 2 (w, u))) (hf : FullyAmenableAt f x) :
    IsProtoDifferentiableAt (variationalSolutionMapping F f) (WithLp.toLp 2 (w, u)) x ∧
    (∀ (w' : W) (u' : E), graphicalDerivative (variationalSolutionMapping F f)
        (WithLp.toLp 2 (w, u)) x (WithLp.toLp 2 (w', u')) =
      {x' | u' - fderiv ℝ F (WithLp.toLp 2 (w, x)) (WithLp.toLp 2 (w', x')) ∈
        subdifferential (fun z ↦ ((1 / 2 : ℝ) : EReal) *
          secondSubderivative f x (u - F (WithLp.toLp 2 (w, x))) z) x'}) ∧
    GraphicallyLipschitzianAt (variationalSolutionMapping F f) (WithLp.toLp 2 (w, u)) x
      (Module.finrank ℝ W + Module.finrank ℝ E) ∧
    (HasAubinPropertyAt (variationalSolutionMapping F f) (WithLp.toLp 2 (w, u)) x ↔
      ∀ z : E, -((fderiv ℝ F (WithLp.toLp 2 (w, x))).comp embedSnd).adjoint z ∈
        coderivative (subdifferential f) x (u - F (WithLp.toLp 2 (w, x))) z → z = 0) := by
  obtain ⟨hproto, hform, hgl⟩ := variationalSolutionMapping_proto hF hx hf
  refine ⟨hproto, hform, hgl, ?_⟩
  rw [hasAubinPropertyAt_iff_coderivative_zero hx hgl.isLocallyClosedAt]
  set v := u - F (WithLp.toLp 2 (w, x)) with hv_def
  set A := fderiv ℝ F (WithLp.toLp 2 (w, x)) with hA
  set q₀ : WithLp 2 (WithLp 2 (W × E) × E) :=
    WithLp.toLp 2 ((WithLp.toLp 2 (w, u) : WithLp 2 (W × E)), x) with hq₀
  have hdiff : DifferentiableAt ℝ F (WithLp.toLp 2 (w, x)) := hF.differentiable one_ne_zero _
  have hD : HasFDerivAt (variationalSubmersion F) (variationalSubmersionDeriv A) q₀ :=
    hasFDerivAt_variationalSubmersion (by rw [hq₀]; rfl) hdiff
  have hGc : ContDiffAt ℝ 1 (variationalSubmersion F) q₀ := by
    have hι : ContDiff ℝ 1 (fun q : WithLp 2 (WithLp 2 (W × E) × E) ↦
        WithLp.toLp 2 (q.fst.fst, q.snd)) := by
      have e : ⇑(pairFstE (W := W) (E := E)) = fun q ↦ WithLp.toLp 2 (q.fst.fst, q.snd) :=
        funext pairFstE_apply
      rw [← e]; exact (pairFstE (W := W) (E := E)).contDiff
    have h1 : ContDiff ℝ 1 (fun q : WithLp 2 (WithLp 2 (W × E) × E) ↦
        (q.snd, q.fst.snd - F (WithLp.toLp 2 (q.fst.fst, q.snd)))) :=
      (WithLp.sndL 2 ℝ (WithLp 2 (W × E)) E).contDiff.prodMk
        (((WithLp.sndL 2 ℝ W E).comp (WithLp.fstL 2 ℝ (WithLp 2 (W × E)) E)).contDiff.sub
          (hF.comp hι))
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.contDiff.comp h1).contDiffAt
  have hsurj : Function.Surjective (fderiv ℝ (variationalSubmersion F) q₀) := by
    rw [hD.fderiv]
    intro t
    refine ⟨WithLp.toLp 2 (WithLp.toLp 2 (0, t.snd + A (WithLp.toLp 2 (0, t.fst))), t.fst), ?_⟩
    rw [variationalSubmersionDeriv_apply]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, add_sub_cancel_right]
    rfl
  have hN := normalCone_preimage_of_surjective hGc hsurj (euclideanSvGraph (subdifferential f))
  rw [← euclideanSvGraph_variationalSolutionMapping, hD.fderiv] at hN
  have hGq : variationalSubmersion F q₀ = WithLp.toLp 2 (x, v) := by
    simp only [variationalSubmersion, hq₀, WithLp.toLp_fst, WithLp.toLp_snd, hv_def]
  rw [hGq] at hN
  have hmem0 : ∀ q' : WithLp 2 (W × E), q' ∈ coderivative (variationalSolutionMapping F f)
      (WithLp.toLp 2 (w, u)) x 0 ↔ ∃ n ∈ normalCone (euclideanSvGraph (subdifferential f))
        (WithLp.toLp 2 (x, v)),
        (variationalSubmersionDeriv A).adjoint n = WithLp.toLp 2 (q', 0) := by
    intro q'
    change WithLp.toLp 2 (q', -0) ∈ normalCone (euclideanSvGraph (variationalSolutionMapping F f))
      q₀ ↔ _
    rw [neg_zero, hN]
    rfl
  constructor
  · intro h0 z hz
    have hq : WithLp.toLp 2 ((A.comp embedFst).adjoint z, -z) ∈
        coderivative (variationalSolutionMapping F f) (WithLp.toLp 2 (w, u)) x 0 := by
      rw [hmem0]
      refine ⟨WithLp.toLp 2 (-(A.comp embedSnd).adjoint z, -z), hz, ?_⟩
      rw [variationalSubmersionDeriv_adjoint, map_neg, map_neg, neg_neg, sub_neg_eq_add,
        neg_add_cancel]
    rw [h0, mem_singleton_iff] at hq
    have := congrArg WithLp.snd hq
    simp only [WithLp.toLp_snd, WithLp.zero_snd, neg_eq_zero] at this
    exact this
  · intro h
    refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun q' hq' ↦ ?_⟩
    · rw [hmem0]
      refine ⟨0, (isCone_normalCone (show WithLp.toLp 2 (x, v) ∈
        euclideanSvGraph (subdifferential f) from hx)).1, ?_⟩
      rw [map_zero]; rfl
    obtain ⟨n, hn, hnq⟩ := (hmem0 q').1 hq'
    have hn' : n = WithLp.toLp 2 (n.fst, n.snd) := rfl
    rw [hn', variationalSubmersionDeriv_adjoint] at hnq
    have h1 := congrArg WithLp.fst hnq
    have h2 := congrArg WithLp.snd hnq
    simp only [WithLp.toLp_fst, WithLp.toLp_snd] at h1 h2
    have hzero : -n.snd = 0 := by
      refine h (-n.snd) ?_
      change WithLp.toLp 2 (-(A.comp embedSnd).adjoint (-n.snd), -(-n.snd)) ∈
        normalCone (euclideanSvGraph (subdifferential f)) (WithLp.toLp 2 (x, v))
      rw [map_neg, neg_neg, neg_neg, ← sub_eq_zero.1 h2]
      exact hn
    have hb : n.snd = 0 := neg_eq_zero.1 hzero
    rw [← h1, hb, map_zero, neg_zero]
    rfl

end Theorem1348

end RW
