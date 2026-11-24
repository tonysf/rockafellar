/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2E*: Simplex technology (Exercise 2.28)

This file formalizes Exercise 2.28 of Rockafellar and Wets, *Variational
Analysis*, in a finite-dimensional real inner product space `E` with
`n = finrank ℝ E`.  A `p`-simplex is `con {a₀, …, a_p}` for an affinely
independent family `a : Fin (p + 1) → E`.

* (a) `simplex_isPolyhedralSet`: simplices are polyhedral (2.10), closed and
  convex.
* (b) `existsUnique_barycentric`: barycentric coordinates relative to `n + 1`
  affinely independent points exist and are unique.
* (c) `simplex_homeomorph_stdSimplex`: the points of a `p`-simplex correspond
  homeomorphically to the standard simplex of weights.
* (d) `simplex_interior`: an `n`-simplex has nonempty interior, consisting of
  the points with positive barycentric coordinates.
* (e) `exists_simplex_nhds`: simplices form a neighborhood base.
* (f) `simplex_perturbation`: perturbed `n`-simplices are eventually
  `n`-simplices, and barycentric coordinates depend continuously on the
  vertices and the point.

Barycentric coordinates are computed through `baryMatrix`, the matrix with
columns `(1, coordinates of aⱼ)`, which is nonsingular exactly for affinely
independent families (`affineIndependent_iff_det_baryMatrix_ne_zero`).
-/

import RockafellarWets.Chapter2.LevelSetsAffine
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Set Filter Topology Matrix Module

namespace RW

/-! ### Barycentric matrices -/

section Barycentric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The `(n + 1) × (n + 1)` matrix whose `j`-th column is `(1, coordinates of
aⱼ)` in the basis `Module.finBasis ℝ E`. -/
noncomputable def baryMatrix (a : Fin (finrank ℝ E + 1) → E) :
    Matrix (Fin (finrank ℝ E + 1)) (Fin (finrank ℝ E + 1)) ℝ :=
  Matrix.of fun r j ↦ (Fin.cons (1 : ℝ) ((finBasis ℝ E).equivFun (a j)) :
    Fin (finrank ℝ E + 1) → ℝ) r

/-- The right-hand side `(1, coordinates of x)` of the barycentric system. -/
noncomputable def baryVec (x : E) : Fin (finrank ℝ E + 1) → ℝ :=
  Fin.cons (1 : ℝ) ((finBasis ℝ E).equivFun x)

theorem baryMatrix_mulVec (a : Fin (finrank ℝ E + 1) → E) (w : Fin (finrank ℝ E + 1) → ℝ) :
    baryMatrix a *ᵥ w = (Fin.cons (∑ j, w j) ((finBasis ℝ E).equivFun (∑ j, w j • a j)) :
      Fin (finrank ℝ E + 1) → ℝ) := by
  ext r
  refine Fin.cases ?_ (fun k ↦ ?_) r
  · simp [baryMatrix, mulVec, dotProduct]
  · simp [baryMatrix, mulVec, dotProduct, map_sum, mul_comm]

/-- `w` solves the barycentric system for `x` iff it gives barycentric weights
of `x`. -/
theorem baryMatrix_mulVec_eq_baryVec_iff {a : Fin (finrank ℝ E + 1) → E}
    {w : Fin (finrank ℝ E + 1) → ℝ} {x : E} :
    baryMatrix a *ᵥ w = baryVec x ↔ ∑ j, w j = 1 ∧ ∑ j, w j • a j = x := by
  rw [baryMatrix_mulVec, baryVec, Fin.cons_inj, (finBasis ℝ E).equivFun.injective.eq_iff]

theorem baryMatrix_mulVec_eq_zero_iff {a : Fin (finrank ℝ E + 1) → E}
    {w : Fin (finrank ℝ E + 1) → ℝ} :
    baryMatrix a *ᵥ w = 0 ↔ ∑ j, w j = 0 ∧ ∑ j, w j • a j = 0 := by
  have h0 : (0 : Fin (finrank ℝ E + 1) → ℝ) =
      Fin.cons (0 : ℝ) ((finBasis ℝ E).equivFun (0 : E)) := by
    ext r
    refine Fin.cases ?_ (fun k ↦ ?_) r <;> simp
  rw [baryMatrix_mulVec, h0, Fin.cons_inj, (finBasis ℝ E).equivFun.injective.eq_iff]

/-- A family of `n + 1` points is affinely independent iff its barycentric
matrix is nonsingular. -/
theorem affineIndependent_iff_det_baryMatrix_ne_zero (a : Fin (finrank ℝ E + 1) → E) :
    AffineIndependent ℝ a ↔ (baryMatrix a).det ≠ 0 := by
  rw [Ne, ← exists_mulVec_eq_zero_iff, affineIndependent_iff_of_fintype]
  constructor
  · rintro h ⟨w, hw0, hw⟩
    rw [baryMatrix_mulVec_eq_zero_iff] at hw
    refine hw0 (funext fun i ↦ h w hw.1 ?_ i)
    rw [Finset.weightedVSub_eq_linear_combination _ hw.1]
    exact hw.2
  · intro h w hw hvs
    rw [Finset.weightedVSub_eq_linear_combination _ hw] at hvs
    by_contra hne
    push_neg at hne
    obtain ⟨i, hi⟩ := hne
    exact h ⟨w, fun h' ↦ hi (congrFun h' i), baryMatrix_mulVec_eq_zero_iff.mpr ⟨hw, hvs⟩⟩

/-- Barycentric weights solve the barycentric system. -/
theorem eq_inv_mulVec_of_barycentric {a : Fin (finrank ℝ E + 1) → E}
    (hdet : (baryMatrix a).det ≠ 0) {w : Fin (finrank ℝ E + 1) → ℝ} {x : E}
    (hw : ∑ j, w j = 1) (hwx : ∑ j, w j • a j = x) :
    w = (baryMatrix a)⁻¹ *ᵥ baryVec x := by
  rw [← baryMatrix_mulVec_eq_baryVec_iff.mpr ⟨hw, hwx⟩, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]

theorem continuous_baryMatrix :
    Continuous (fun a : Fin (finrank ℝ E + 1) → E ↦ baryMatrix a) := by
  have hc : Continuous ((finBasis ℝ E).equivFun : E → Fin (finrank ℝ E) → ℝ) :=
    LinearMap.continuous_of_finiteDimensional (finBasis ℝ E).equivFun.toLinearMap
  refine continuous_pi fun r ↦ continuous_pi fun j ↦ ?_
  refine Fin.cases ?_ (fun k ↦ ?_) r
  · simp only [baryMatrix, of_apply, Fin.cons_zero]
    exact continuous_const
  · simp only [baryMatrix, of_apply, Fin.cons_succ]
    exact (continuous_apply k).comp (hc.comp (continuous_apply j))

theorem continuous_baryVec : Continuous (baryVec : E → Fin (finrank ℝ E + 1) → ℝ) := by
  have hc : Continuous ((finBasis ℝ E).equivFun : E → Fin (finrank ℝ E) → ℝ) :=
    LinearMap.continuous_of_finiteDimensional (finBasis ℝ E).equivFun.toLinearMap
  refine continuous_pi fun r ↦ ?_
  refine Fin.cases ?_ (fun k ↦ ?_) r
  · simp only [baryVec, Fin.cons_zero]
    exact continuous_const
  · simp only [baryVec, Fin.cons_succ]
    exact (continuous_apply k).comp hc

/-- **Exercise 2.28(b)**: for `n + 1` affinely independent points of `E`, every
point has unique barycentric coordinates. -/
theorem existsUnique_barycentric {a : Fin (finrank ℝ E + 1) → E} (ha : AffineIndependent ℝ a)
    (x : E) : ∃! w : Fin (finrank ℝ E + 1) → ℝ, ∑ i, w i = 1 ∧ ∑ i, w i • a i = x := by
  have hdet := (affineIndependent_iff_det_baryMatrix_ne_zero a).mp ha
  refine ⟨(baryMatrix a)⁻¹ *ᵥ baryVec x, baryMatrix_mulVec_eq_baryVec_iff.mp ?_,
    fun w hw ↦ eq_inv_mulVec_of_barycentric hdet hw.1 hw.2⟩
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]

/-- **Exercise 2.28(f)**: if `aν → a` and `a` is an `n`-simplex, then `aν` is
eventually an `n`-simplex; barycentric coordinates `λν` of points `xν → x`
relative to `aν` converge to the barycentric coordinates `λ` of `x` relative
to `a`. -/
theorem simplex_perturbation {α : Type*} {L : Filter α} {a : Fin (finrank ℝ E + 1) → E}
    (ha : AffineIndependent ℝ a) {aν : α → Fin (finrank ℝ E + 1) → E}
    (hconv : Tendsto aν L (𝓝 a)) :
    (∀ᶠ ν in L, AffineIndependent ℝ (aν ν)) ∧
    ∀ {xν : α → E} {x : E} {lν : α → Fin (finrank ℝ E + 1) → ℝ}
      {l : Fin (finrank ℝ E + 1) → ℝ},
      Tendsto xν L (𝓝 x) →
      (∀ᶠ ν in L, ∑ i, lν ν i = 1 ∧ ∑ i, lν ν i • aν ν i = xν ν) →
      ∑ i, l i = 1 → ∑ i, l i • a i = x → Tendsto lν L (𝓝 l) := by
  have hdet := (affineIndependent_iff_det_baryMatrix_ne_zero a).mp ha
  have hM : Tendsto (fun ν ↦ baryMatrix (aν ν)) L (𝓝 (baryMatrix a)) :=
    (continuous_baryMatrix.tendsto a).comp hconv
  have hd : Tendsto (fun ν ↦ (baryMatrix (aν ν)).det) L (𝓝 (baryMatrix a).det) :=
    (continuous_id.matrix_det.tendsto _).comp hM
  have hdetν : ∀ᶠ ν in L, (baryMatrix (aν ν)).det ≠ 0 := hd.eventually_ne hdet
  refine ⟨hdetν.mono fun ν h ↦ (affineIndependent_iff_det_baryMatrix_ne_zero _).mpr h,
    fun {xν x lν l} hx hrep hl hlx ↦ ?_⟩
  have hinv : ContinuousAt Inv.inv (baryMatrix a) :=
    continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
  have h1 : Tendsto (fun ν ↦ (baryMatrix (aν ν))⁻¹) L (𝓝 (baryMatrix a)⁻¹) :=
    hinv.tendsto.comp hM
  have h2 : Tendsto (fun ν ↦ baryVec (xν ν)) L (𝓝 (baryVec x)) :=
    (continuous_baryVec.tendsto x).comp hx
  have hcont : Continuous (fun p : Matrix (Fin (finrank ℝ E + 1)) (Fin (finrank ℝ E + 1)) ℝ ×
      (Fin (finrank ℝ E + 1) → ℝ) ↦ p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hlim : Tendsto (fun ν ↦ (baryMatrix (aν ν))⁻¹ *ᵥ baryVec (xν ν)) L
      (𝓝 ((baryMatrix a)⁻¹ *ᵥ baryVec x)) :=
    (hcont.tendsto _).comp (h1.prodMk_nhds h2)
  rw [eq_inv_mulVec_of_barycentric hdet hl hlx]
  refine hlim.congr' ?_
  filter_upwards [hdetν, hrep] with ν hν hr
  exact (eq_inv_mulVec_of_barycentric hν hr.1 hr.2).symm

end Barycentric

/-! ### Simplices as convex hulls -/

section Simplices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Combinations with weights in the standard simplex lie in the convex hull. -/
theorem sum_smul_mem_convexHull_range {p : ℕ} (a : Fin (p + 1) → E) {w : Fin (p + 1) → ℝ}
    (hw : w ∈ stdSimplex ℝ (Fin (p + 1))) : ∑ i, w i • a i ∈ convexHull ℝ (range a) :=
  (convex_convexHull ℝ _).sum_mem (fun i _ ↦ hw.1 i) hw.2
    (fun i _ ↦ subset_convexHull ℝ _ (mem_range_self i))

/-- Every point of `con {a₀, …, a_p}` is a convex combination of the `aᵢ` with
weights in the standard simplex. -/
theorem exists_stdSimplex_of_mem_convexHull {p : ℕ} {a : Fin (p + 1) → E} {x : E}
    (hx : x ∈ convexHull ℝ (range a)) :
    ∃ w ∈ stdSimplex ℝ (Fin (p + 1)), ∑ i, w i • a i = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s, w, hw0, hw1, hwx⟩ := hx
  have hsum : ∑ i, (↑s : Set (Fin (p + 1))).indicator w i = 1 := by
    rw [Finset.sum_indicator_subset w (Finset.subset_univ s), hw1]
  refine ⟨(↑s : Set (Fin (p + 1))).indicator w, ⟨fun i ↦ ?_, hsum⟩, ?_⟩
  · by_cases hi : i ∈ s
    · rw [Set.indicator_of_mem (Finset.mem_coe.mpr hi)]
      exact hw0 i hi
    · rw [Set.indicator_of_notMem (by simpa using hi)]
  · rw [← Finset.affineCombination_eq_linear_combination _ _ _ hsum,
      ← Finset.affineCombination_indicator_subset w a (Finset.subset_univ s), hwx]

/-- Barycentric weights relative to affinely independent points are unique. -/
theorem eq_of_sum_smul_eq {p : ℕ} {a : Fin (p + 1) → E} (ha : AffineIndependent ℝ a)
    {w₁ w₂ : Fin (p + 1) → ℝ} (h₁ : ∑ i, w₁ i = 1) (h₂ : ∑ i, w₂ i = 1)
    (h : ∑ i, w₁ i • a i = ∑ i, w₂ i • a i) : w₁ = w₂ := by
  refine (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ a).mp ha w₁ w₂ h₁ h₂ ?_
  rw [Finset.affineCombination_eq_linear_combination _ _ _ h₁,
    Finset.affineCombination_eq_linear_combination _ _ _ h₂, h]

/-- **Exercise 2.28(c)**: each point of a `p`-simplex `con {a₀, …, a_p}` is a
unique convex combination of the vertices, and `λ ↦ ∑ λᵢ aᵢ` is a
homeomorphism from the standard simplex onto the simplex. -/
theorem simplex_homeomorph_stdSimplex {p : ℕ} {a : Fin (p + 1) → E}
    (ha : AffineIndependent ℝ a) :
    (∀ x ∈ convexHull ℝ (range a),
      ∃! w, w ∈ stdSimplex ℝ (Fin (p + 1)) ∧ ∑ i, w i • a i = x) ∧
    ∃ e : stdSimplex ℝ (Fin (p + 1)) ≃ₜ convexHull ℝ (range a),
      ∀ w, (e w : E) = ∑ i, (w : Fin (p + 1) → ℝ) i • a i := by
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · obtain ⟨w, hw, hwx⟩ := exists_stdSimplex_of_mem_convexHull hx
    exact ⟨w, ⟨hw, hwx⟩, fun w' hw' ↦ eq_of_sum_smul_eq ha hw'.1.2 hw.2 (hw'.2.trans hwx.symm)⟩
  let F : stdSimplex ℝ (Fin (p + 1)) → convexHull ℝ (range a) :=
    fun w ↦ ⟨∑ i, (w : Fin (p + 1) → ℝ) i • a i, sum_smul_mem_convexHull_range a w.2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun w₁ w₂ h ↦ Subtype.ext (eq_of_sum_smul_eq ha w₁.2.2 w₂.2.2
      (congrArg Subtype.val h)), fun x ↦ ?_⟩
    obtain ⟨w, hw, hwx⟩ := exists_stdSimplex_of_mem_convexHull x.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwx⟩
  have hcont : Continuous F :=
    Continuous.subtype_mk (continuous_finset_sum _ fun i _ ↦
      ((continuous_apply i).comp continuous_subtype_val).smul continuous_const) _
  haveI : CompactSpace (stdSimplex ℝ (Fin (p + 1))) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex _)
  exact ⟨(show Continuous (Equiv.ofBijective F hF) from hcont).homeoOfEquivCompactToT2,
    fun w ↦ rfl⟩

variable [FiniteDimensional ℝ E]

/-- `n + 1` affinely independent points of `E` form an affine basis. -/
noncomputable def simplexAffineBasis {a : Fin (finrank ℝ E + 1) → E}
    (ha : AffineIndependent ℝ a) : AffineBasis (Fin (finrank ℝ E + 1)) ℝ E :=
  ⟨a, ha, ha.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)⟩

omit [FiniteDimensional ℝ E] in
theorem sum_inv_card_eq_one :
    ∑ _i : Fin (finrank ℝ E + 1), ((finrank ℝ E : ℝ) + 1)⁻¹ = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

/-- **Exercise 2.28(d)**: an `n`-simplex has nonempty interior, and its
interior consists of the combinations `∑ λᵢ aᵢ` with all `λᵢ > 0`,
`∑ λᵢ = 1`. -/
theorem simplex_interior {a : Fin (finrank ℝ E + 1) → E} (ha : AffineIndependent ℝ a) :
    (interior (convexHull ℝ (range a))).Nonempty ∧
    ∀ x, x ∈ interior (convexHull ℝ (range a)) ↔
      ∃ w : Fin (finrank ℝ E + 1) → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • a i = x := by
  set b := simplexAffineBasis ha
  have hb : ⇑b = a := rfl
  have hint : interior (convexHull ℝ (range a)) = {x | ∀ i, 0 < b.coord i x} := by
    rw [← hb]
    exact b.interior_convexHull
  have key : ∀ x, x ∈ interior (convexHull ℝ (range a)) ↔
      ∃ w : Fin (finrank ℝ E + 1) → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
        ∑ i, w i • a i = x := by
    intro x
    rw [hint, mem_setOf_eq]
    constructor
    · intro h
      refine ⟨fun i ↦ b.coord i x, h, b.sum_coord_apply_eq_one x, ?_⟩
      rw [← hb]
      exact b.linear_combination_coord_eq_self x
    · rintro ⟨w, hw0, hw1, hwx⟩ i
      have hc : b.coord i x = w i := by
        rw [← hwx, ← Finset.affineCombination_eq_linear_combination _ _ _ hw1, ← hb]
        exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw1
      rw [hc]
      exact hw0 i
  refine ⟨⟨_, (key _).mpr ⟨fun _ ↦ ((finrank ℝ E : ℝ) + 1)⁻¹, fun _ ↦ by positivity,
    sum_inv_card_eq_one, rfl⟩⟩, key⟩

/-- **Exercise 2.28(e)**: simplices form a neighborhood base: every
neighborhood of `x` contains an `n`-simplex having `x` in its interior. -/
theorem exists_simplex_nhds {x : E} {V : Set E} (hV : V ∈ 𝓝 x) :
    ∃ a : Fin (finrank ℝ E + 1) → E, AffineIndependent ℝ a ∧ convexHull ℝ (range a) ⊆ V ∧
      x ∈ interior (convexHull ℝ (range a)) := by
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (finrank ℝ E + 1)) (k := ℝ) (V := E) (P := E) (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  set N : ℝ := (finrank ℝ E : ℝ) + 1
  set c : E := ∑ i, N⁻¹ • b i with hc
  set R : ℝ := ∑ i, ‖b i - c‖ + 1
  have hR : 0 < R := by positivity
  have hRi : ∀ i, ‖b i - c‖ < R := fun i ↦ by
    have := Finset.single_le_sum (f := fun j ↦ ‖b j - c‖) (fun j _ ↦ norm_nonneg _)
      (Finset.mem_univ i)
    simp only at this
    linarith
  set δ : ℝ := ε / R
  have hδ : 0 < δ := div_pos hε hR
  let g : E →ᵃ[ℝ] E := ⟨fun y ↦ x + δ • (y - c), δ • LinearMap.id, fun p v ↦ by
    simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_apply, smul_add, smul_sub]
    abel⟩
  have hgapp : ∀ y, g y = x + δ • (y - c) := fun _ ↦ rfl
  have hg : Function.Injective g := fun y₁ y₂ h ↦ by
    rw [hgapp, hgapp] at h
    have := smul_right_injective E hδ.ne' (add_left_cancel h)
    simpa using this
  have hai : AffineIndependent ℝ (g ∘ b) := b.ind.map' g hg
  refine ⟨g ∘ b, hai, ?_, ?_⟩
  · refine (convexHull_min ?_ (convex_ball x ε)).trans hball
    rintro _ ⟨i, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, Function.comp_apply, hgapp, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    calc δ * ‖b i - c‖ < δ * R := mul_lt_mul_of_pos_left (hRi i) hδ
      _ = ε := div_mul_cancel₀ ε hR.ne'
  · rw [(simplex_interior hai).2]
    refine ⟨fun _ ↦ N⁻¹, fun _ ↦ by positivity, sum_inv_card_eq_one, ?_⟩
    have h1 : ∑ _i : Fin (finrank ℝ E + 1), N⁻¹ • x = x := by
      rw [← Finset.sum_smul, sum_inv_card_eq_one, one_smul]
    have h2 : ∑ _i : Fin (finrank ℝ E + 1), N⁻¹ • c = c := by
      rw [← Finset.sum_smul, sum_inv_card_eq_one, one_smul]
    have h3 : ∑ i, N⁻¹ • (δ • (b i - c)) = 0 := by
      have : ∑ i, N⁻¹ • (δ • (b i - c)) =
          δ • (∑ i, N⁻¹ • b i - ∑ _i : Fin (finrank ℝ E + 1), N⁻¹ • c) := by
        rw [← Finset.sum_sub_distrib, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [smul_comm, smul_sub]
      rw [this, h2, ← hc, sub_self, smul_zero]
    simp only [Function.comp_apply, hgapp, smul_add, Finset.sum_add_distrib, h1, h3, add_zero]

end Simplices

/-! ### Polyhedrality (Exercise 2.28(a)) -/

section Polyhedral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 2.28(a)**: a simplex `con {a₀, …, a_p}` (indeed the convex hull
of any finitely many points) is a polyhedral set in the sense of 2.10, in
particular closed and convex. -/
theorem simplex_isPolyhedralSet {p : ℕ} (a : Fin (p + 1) → E) :
    IsPolyhedralSet (convexHull ℝ (range a)) ∧ IsClosed (convexHull ℝ (range a)) ∧
      Convex ℝ (convexHull ℝ (range a)) := by
  classical
  refine ⟨?_, (finite_range a).isCompact_convexHull.isClosed, convex_convexHull ℝ _⟩
  rcases subsingleton_or_nontrivial E with hE | hE
  · have huniv : convexHull ℝ (range a) = univ :=
      eq_univ_of_forall fun y ↦ (Subsingleton.elim (a 0) y) ▸
        subset_convexHull ℝ _ (mem_range_self 0)
    rw [huniv]
    exact ⟨∅, finite_empty, by simp, by simp⟩
  · refine isPolyhedralSet_iff_isPolyhedral.mpr ?_
    have h := IsExtendedFinitelyGenerated.convexHull_finset (Finset.univ.image a)
    rwa [Finset.coe_image, Finset.coe_univ, image_univ] at h

end Polyhedral

end RW
