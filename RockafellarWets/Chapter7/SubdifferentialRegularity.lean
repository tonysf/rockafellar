/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Subdifferential regularity

Definition 7.25, Theorem 7.26 and Example 7.27.

Clarke regularity (Definition 6.4) is a property of subsets of a Euclidean
space, so in Definition 7.25 the epigraph is regarded in the Euclidean product
`WithLp 2 (E × ℝ)`; the plain product `E × ℝ` of Mathlib carries the sup norm
and no inner product.  The two products are linearly homeomorphic, and tangent
cones, derivable cones, blow-ups, interiors and local closedness transfer
along any continuous linear equivalence (`*_preimage_continuousLinearEquiv`).

Theorem 7.26 is proved as in the book: geometric derivability (6.30) and 7.24
give epi-differentiability; the epigraph of `df(x̄)` is the convex cone
`T_{epi f}(x̄, f(x̄))`, so `df(x̄)` is sublinear in the sense of 3.19 and lower
semicontinuous; at a point `w̄ ∈ int D` the convex function `df(x̄)` is upper
semicontinuous (the step 2.35 of the book), so a compact box
`IB(w̄, δ) × {β}` lies in the interior of the tangent cone, and Corollary 6.37
bounds the difference quotients uniformly.

The last clause of 7.26 is proved in the corrected form
`(∃ β < ∞, HasSemiderivative f x̄ w β) ↔ w ∈ int D`: Definition 7.20 admits
infinite semiderivatives, and the indicator of `[0, ∞)` at `0` is regular and
semidifferentiable for `w = -1` with semiderivative `∞`, although
`-1 ∉ int D` (`not_forall_semidifferentiableFor_iff_mem_interior`).

Sublinearity is stated as "the epigraph is a convex cone", which is the
book's sublinearity (3.19, with the convention `∞ - ∞ = ∞`).  The repository's
`Sublinear` uses Mathlib's `EReal` addition, where `⊥ + ⊤ = ⊥`; it is derived
when `df(x̄)` does not take the value `-∞`.

Example 7.27 uses local lower semicontinuity, Definition 1.33, which is
formalized here together with the half of Exercise 1.34(a) that is needed.
-/

import RockafellarWets.Chapter7.EpiDerivatives
import RockafellarWets.Chapter6.TangentNormalPolarity
import RockafellarWets.Chapter6.InteriorTangents
import RockafellarWets.Chapter6.ConvexSets
import RockafellarWets.Chapter3.PositiveHomogeneity
import RockafellarWets.Chapter1.Semicontinuity
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Convex.Continuous

open Filter Set Topology Metric

namespace RW

/-! ### Transfer along continuous linear equivalences -/

section Transfer

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem blowUp_preimage_continuousLinearEquiv (L : F ≃L[ℝ] G) (C : Set G) (x : F) (τ : ℝ) :
    blowUp (L ⁻¹' C) x τ = L ⁻¹' blowUp C (L x) τ := by
  ext u
  simp only [mem_blowUp, mem_preimage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨L y, hy, by rw [map_smul, map_sub]⟩
  · rintro ⟨y', hy', hu⟩
    refine ⟨L.symm y', by simpa using hy', ?_⟩
    apply L.injective
    rw [map_smul, map_sub, L.apply_symm_apply]
    exact hu

theorem tangentCone_preimage_continuousLinearEquiv (L : F ≃L[ℝ] G) (C : Set G) (x : F) :
    tangentCone (L ⁻¹' C) x = L ⁻¹' tangentCone C (L x) := by
  ext w
  constructor
  · rintro ⟨xs, τs, hxC, hxto, hτ, hτ0, hq⟩
    refine ⟨fun n ↦ L (xs n), τs, hxC, (L.continuous.tendsto x).comp hxto, hτ, hτ0, ?_⟩
    refine ((L.continuous.tendsto w).comp hq).congr fun n ↦ ?_
    simp only [Function.comp_apply, map_smul, map_sub]
  · rintro ⟨xs, τs, hxC, hxto, hτ, hτ0, hq⟩
    refine ⟨fun n ↦ L.symm (xs n), τs, fun n ↦ ?_, ?_, hτ, hτ0, ?_⟩
    · show L (L.symm (xs n)) ∈ C
      rw [L.apply_symm_apply]
      exact hxC n
    · have h1 := (L.symm.continuous.tendsto (L x)).comp hxto
      rwa [L.symm_apply_apply] at h1
    · have h1 := (L.symm.continuous.tendsto (L w)).comp hq
      rw [L.symm_apply_apply] at h1
      refine h1.congr fun n ↦ ?_
      simp only [Function.comp_apply, map_smul, map_sub, L.symm_apply_apply]

theorem derivableCone_preimage_continuousLinearEquiv (L : F ≃L[ℝ] G) (C : Set G) (x : F) :
    derivableCone (L ⁻¹' C) x = L ⁻¹' derivableCone C (L x) := by
  ext w
  constructor
  · rintro ⟨ε, hε, ξ, hξ0, hξC, hξt⟩
    refine ⟨ε, hε, fun t ↦ L (ξ t), congrArg L hξ0, hξC, ?_⟩
    refine ((L.continuous.tendsto w).comp hξt).congr fun t ↦ ?_
    simp only [Function.comp_apply, map_smul, map_sub]
  · rintro ⟨ε, hε, ξ, hξ0, hξC, hξt⟩
    refine ⟨ε, hε, fun t ↦ L.symm (ξ t), ?_, fun t ht ↦ ?_, ?_⟩
    · show L.symm (ξ 0) = x
      rw [hξ0, L.symm_apply_apply]
    · show L (L.symm (ξ t)) ∈ C
      rw [L.apply_symm_apply]
      exact hξC t ht
    · have h1 := (L.symm.continuous.tendsto (L w)).comp hξt
      rw [L.symm_apply_apply] at h1
      refine h1.congr fun t ↦ ?_
      simp only [Function.comp_apply, map_smul, map_sub, L.symm_apply_apply]

theorem isGeometricallyDerivable_preimage_continuousLinearEquiv (L : F ≃L[ℝ] G) (C : Set G)
    (x : F) :
    IsGeometricallyDerivable (L ⁻¹' C) x ↔ IsGeometricallyDerivable C (L x) := by
  unfold IsGeometricallyDerivable
  rw [tangentCone_preimage_continuousLinearEquiv, derivableCone_preimage_continuousLinearEquiv]
  exact L.surjective.preimage_subset_preimage_iff

theorem IsLocallyClosedAt.preimage_continuousLinearEquiv (L : F ≃L[ℝ] G) {C : Set G} {x : F}
    (h : IsLocallyClosedAt C (L x)) : IsLocallyClosedAt (L ⁻¹' C) x := by
  obtain ⟨V, hV, hVc, hCV⟩ := h
  refine ⟨L ⁻¹' V, L.continuous.continuousAt.preimage_mem_nhds hV, hVc.preimage L.continuous, ?_⟩
  rw [← preimage_inter]
  exact hCV.preimage L.continuous

theorem convex_of_convex_preimage_continuousLinearEquiv (L : F ≃L[ℝ] G) {S : Set G}
    (h : Convex ℝ (L ⁻¹' S)) : Convex ℝ S := by
  intro y hy z hz a b ha hb hab
  have := h (show L.symm y ∈ L ⁻¹' S by simpa using hy)
    (show L.symm z ∈ L ⁻¹' S by simpa using hz) ha hb hab
  simpa using this

theorem convex_preimage_continuousLinearEquiv (L : F ≃L[ℝ] G) {S : Set G}
    (h : Convex ℝ S) : Convex ℝ (L ⁻¹' S) := by
  intro y hy z hz a b ha hb hab
  have := h hy hz ha hb hab
  simpa using this

end Transfer

/-! ### Convex functions are upper semicontinuous on the interior of the domain -/

section ConvexUpper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The effective domain of a function with convex epigraph is convex. -/
theorem convex_setOf_lt_top_of_convex_epigraph {h : E → EReal}
    (hconv : Convex ℝ (epigraph h)) : Convex ℝ {w | h w < ⊤} := by
  intro u hu v hv a b ha hb hab
  obtain ⟨p, hp, -⟩ := EReal.exists_between_coe_real hu
  obtain ⟨q, hq, -⟩ := EReal.exists_between_coe_real hv
  have hmem := hconv ((mem_epigraph_iff h u p).2 hp.le) ((mem_epigraph_iff h v q).2 hq.le) ha hb hab
  rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, mem_epigraph_iff] at hmem
  exact lt_of_le_of_lt hmem (EReal.coe_lt_top _)

/-- The step 2.35 used in the proof of 7.26: a function with convex epigraph
on a finite-dimensional space is upper semicontinuous at every interior point
of its effective domain, including where it takes the value `-∞`.  The proof
applies the continuity of real convex functions on open sets to the finite
truncation `max h (-M)`. -/
theorem eventually_lt_of_convex_epigraph [FiniteDimensional ℝ E] {h : E → EReal}
    (hconv : Convex ℝ (epigraph h)) {w₀ : E} (hw₀ : w₀ ∈ interior {w | h w < ⊤}) {β : ℝ}
    (hβ : h w₀ < β) : ∀ᶠ w in 𝓝 w₀, h w < β := by
  set M : ℝ := |β| + 1 with hM_def
  have hMβ : -M < β := by rw [hM_def]; linarith [neg_abs_le β]
  set U := interior {w | h w < ⊤} with hU_def
  set G : E → ℝ := fun w ↦ (max (h w) ((-M : ℝ) : EReal)).toReal with hG_def
  have hfin : ∀ w ∈ U, max (h w) ((-M : ℝ) : EReal) = ((G w : ℝ) : EReal) := by
    intro w hw
    have hmemw := interior_subset hw
    have hlt : h w < ⊤ := hmemw
    apply (EReal.coe_toReal _ _).symm
    · exact (max_lt hlt (EReal.coe_lt_top _)).ne
    · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
  have hGM : ∀ w ∈ U, -M ≤ G w := by
    intro w hw
    have := le_max_right (h w) ((-M : ℝ) : EReal)
    rw [hfin w hw] at this
    exact EReal.coe_le_coe_iff.1 this
  have hhG : ∀ w ∈ U, h w ≤ ((G w : ℝ) : EReal) := fun w hw ↦ by
    rw [← hfin w hw]
    exact le_max_left _ _
  have hUconv : Convex ℝ U := (convex_setOf_lt_top_of_convex_epigraph hconv).interior
  have hGconv : ConvexOn ℝ U G := by
    refine ⟨hUconv, fun u hu v hv a b ha hb hab ↦ ?_⟩
    have hmem := hconv ((mem_epigraph_iff h u (G u)).2 (hhG u hu))
      ((mem_epigraph_iff h v (G v)).2 (hhG v hv)) ha hb hab
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, mem_epigraph_iff] at hmem
    have hlow : ((-M : ℝ) : EReal) ≤ ((a • G u + b • G v : ℝ) : EReal) := by
      apply EReal.coe_le_coe_iff.2
      simp only [smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left (hGM u hu) ha
      have h2 := mul_le_mul_of_nonneg_left (hGM v hv) hb
      have h3 : a * -M + b * -M = -M := by rw [← add_mul, hab, one_mul]
      linarith
    have huv : a • u + b • v ∈ U := hUconv hu hv ha hb hab
    have := max_le hmem hlow
    rw [hfin _ huv] at this
    exact EReal.coe_le_coe_iff.1 this
  have hGcont : ContinuousAt G w₀ :=
    (hGconv.continuousOn isOpen_interior).continuousAt (isOpen_interior.mem_nhds hw₀)
  have hG0 : G w₀ < β := by
    have : ((G w₀ : ℝ) : EReal) < β := by
      rw [← hfin w₀ hw₀]
      exact max_lt hβ (EReal.coe_lt_coe_iff.2 hMβ)
    exact EReal.coe_lt_coe_iff.1 this
  filter_upwards [hGcont.eventually (gt_mem_nhds hG0), isOpen_interior.mem_nhds hw₀] with w hw hwU
  exact lt_of_le_of_lt (hhG w hwU) (EReal.coe_lt_coe_iff.2 hw)

end ConvexUpper

/-! ### Definition 1.33 -/

section LocalLsc

variable {E : Type*} [PseudoMetricSpace E]


/-- **Definition 1.33**: `f` is locally lower semicontinuous at `x̄`, a point
where `f(x̄)` is finite, if for some `ε > 0` all the sets
`{x ∈ IB(x̄, ε) | f(x) ≤ α}` with `α ≤ f(x̄) + ε` are closed. -/
def IsLocallyLscAt (f : E → EReal) (x : E) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∃ ε > 0, ∀ α : ℝ, α ≤ (f x).toReal + ε →
    IsClosed (closedBall x ε ∩ {y | f y ≤ α})

/-- **Exercise 1.34(a)**, the direction used in 7.27: local lower
semicontinuity makes the epigraph locally closed at `(x̄, f(x̄))`. -/
theorem IsLocallyLscAt.isLocallyClosedAt_epigraph {f : E → EReal} {x : E}
    (h : IsLocallyLscAt f x) : IsLocallyClosedAt (epigraph f) (x, (f x).toReal) := by
  obtain ⟨-, -, ε, hε, hclosed⟩ := h
  set c := (f x).toReal
  refine ⟨closedBall x ε ×ˢ Icc (c - ε) (c + ε),
    prod_mem_nhds (closedBall_mem_nhds x hε) (Icc_mem_nhds (by linarith) (by linarith)),
    isClosed_closedBall.prod isClosed_Icc, ?_⟩
  refine isClosed_of_closure_subset fun p hp ↦ ?_
  obtain ⟨ps, hps, hpto⟩ := mem_closure_iff_seq_limit.1 hp
  have hV : p ∈ closedBall x ε ×ˢ Icc (c - ε) (c + ε) :=
    (isClosed_closedBall.prod isClosed_Icc).mem_of_tendsto hpto
      (Eventually.of_forall fun n ↦ (hps n).2)
  refine ⟨?_, hV⟩
  have h1 : Tendsto (fun n ↦ (ps n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hpto
  have h2 : Tendsto (fun n ↦ (ps n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hpto
  have hlev : ∀ s : ℝ, p.2 < s → s ≤ c + ε → f p.1 ≤ s := by
    intro s hs hsc
    have hmem : ∀ᶠ n in atTop, (ps n).1 ∈ closedBall x ε ∩ {y | f y ≤ s} := by
      filter_upwards [h2.eventually (gt_mem_nhds hs)] with n hn
      exact ⟨(hps n).2.1, ((hps n).1 : f (ps n).1 ≤ ((ps n).2 : EReal)).trans
        (EReal.coe_le_coe_iff.2 hn.le)⟩
    exact ((hclosed s hsc).mem_of_tendsto h1 hmem).2
  have htop : f p.1 ≤ ((c + ε : ℝ) : EReal) := by
    have hmem : ∀ n, (ps n).1 ∈ closedBall x ε ∩ {y | f y ≤ ((c + ε : ℝ) : EReal)} := fun n ↦
      ⟨(hps n).2.1, ((hps n).1 : f (ps n).1 ≤ ((ps n).2 : EReal)).trans
        (EReal.coe_le_coe_iff.2 (hps n).2.2.2)⟩
    exact ((hclosed (c + ε) le_rfl).mem_of_tendsto h1 (Eventually.of_forall hmem)).2
  show f p.1 ≤ (p.2 : EReal)
  by_contra hlt
  push_neg at hlt
  obtain ⟨s, hs1, hs2⟩ := EReal.exists_between_coe_real hlt
  have hp2 : p.2 < s := EReal.coe_lt_coe_iff.1 hs1
  rcases le_or_gt s (c + ε) with hsc | hsc
  · exact absurd (hlev s hp2 hsc) (not_le.2 hs2)
  · exact absurd htop (not_le.2 (lt_trans (EReal.coe_lt_coe_iff.2 hsc) hs2))

end LocalLsc

/-! ### Definition 7.25 -/

section Regularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean coordinates of `E × ℝ`. -/
noncomputable abbrev l2ProdEquiv (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    WithLp 2 (E × ℝ) ≃L[ℝ] E × ℝ :=
  WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ

@[simp]
theorem l2ProdEquiv_toLp (p : E × ℝ) : l2ProdEquiv E (WithLp.toLp 2 p) = p := rfl

/-- The epigraph of `f`, regarded in the Euclidean product `ℝⁿ × ℝ`. -/
def l2Epigraph (f : E → EReal) : Set (WithLp 2 (E × ℝ)) :=
  l2ProdEquiv E ⁻¹' epigraph f

/-- **Definition 7.25**: `f` is subdifferentially regular at `x̄` when `f(x̄)`
is finite and `epi f` is Clarke regular at `(x̄, f(x̄))` as a subset of the
Euclidean space `ℝⁿ × ℝ`. -/
def IsSubdifferentiallyRegularAt (f : E → EReal) (x : E) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ IsClarkeRegularAt (l2Epigraph f) (WithLp.toLp 2 (x, (f x).toReal))

theorem toLp_mem_l2Epigraph {f : E → EReal} {x : E} (hx : f x ≠ ⊥) (hx' : f x ≠ ⊤) :
    WithLp.toLp 2 (x, (f x).toReal) ∈ l2Epigraph f := by
  show (x, (f x).toReal) ∈ epigraph f
  rw [mem_epigraph_iff, EReal.coe_toReal hx' hx]

variable [FiniteDimensional ℝ E]

/-! ### Theorem 7.26 -/

/-- **Theorem 7.26**, via 6.30: at a point of subdifferential regularity the
epigraph is geometrically derivable. -/
theorem IsSubdifferentiallyRegularAt.isGeometricallyDerivable {f : E → EReal} {x : E}
    (hreg : IsSubdifferentiallyRegularAt f x) :
    IsGeometricallyDerivable (epigraph f) (x, (f x).toReal) := by
  obtain ⟨hx1, hx2, hC⟩ := hreg
  have h := isGeometricallyDerivable_of_isClarkeRegularAt (toLp_mem_l2Epigraph hx1 hx2) hC
  rw [l2Epigraph, isGeometricallyDerivable_preimage_continuousLinearEquiv] at h
  simpa using h

/-- **Theorem 7.26**: a subdifferentially regular function is
epi-differentiable. -/
theorem IsSubdifferentiallyRegularAt.epiDifferentiableAt {f : E → EReal} {x : E}
    (hreg : IsSubdifferentiallyRegularAt f x) : EpiDifferentiableAt f x :=
  (epiDifferentiableAt_iff_isGeometricallyDerivable
    (EReal.coe_toReal hreg.2.1 hreg.1).symm).2 hreg.isGeometricallyDerivable

/-- **Theorem 7.26**, via 6.30: the tangent cone to the epigraph is convex. -/
theorem IsSubdifferentiallyRegularAt.convex_tangentCone {f : E → EReal} {x : E}
    (hreg : IsSubdifferentiallyRegularAt f x) :
    Convex ℝ (tangentCone (epigraph f) (x, (f x).toReal)) := by
  obtain ⟨hx1, hx2, hC⟩ := hreg
  have h := convex_tangentCone_of_isClarkeRegularAt (toLp_mem_l2Epigraph hx1 hx2) hC
  rw [l2Epigraph, tangentCone_preimage_continuousLinearEquiv, l2ProdEquiv_toLp] at h
  exact convex_of_convex_preimage_continuousLinearEquiv (l2ProdEquiv E) h

/-- **Theorem 7.26**: the epi-derivative `df(x̄)` depends sublinearly on `w`
(its epigraph is a convex cone, the sublinearity of 3.19), positively
homogeneously and lower semicontinuously. -/
theorem IsSubdifferentiallyRegularAt.subderivative_properties {f : E → EReal} {x : E}
    (hreg : IsSubdifferentiallyRegularAt f x) :
    Convex ℝ (epigraph (subderivative f x)) ∧ IsCone (epigraph (subderivative f x)) ∧
      PositivelyHomogeneous (subderivative f x) ∧ LowerSemicontinuous (subderivative f x) := by
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hreg.2.1 hreg.1).symm
  have hT := epigraph_subderivative_eq_tangentCone hxc
  have hmem : (x, (f x).toReal) ∈ epigraph f := (mem_epigraph_iff f x _).2 (le_of_eq hxc)
  have hcone : IsCone (epigraph (subderivative f x)) := by
    rw [hT]
    exact isCone_tangentCone hmem
  refine ⟨hT ▸ hreg.convex_tangentCone, hcone, positivelyHomogeneous_of_isCone_epigraph hcone,
    lowerSemicontinuous_of_isClosed_epigraph_ereal _ ?_⟩
  rw [hT]
  exact isClosed_tangentCone _ _

/-- **Theorem 7.26**: when `df(x̄)` does not take the value `-∞`, it is
sublinear also in the sense of Mathlib's `EReal` addition. -/
theorem IsSubdifferentiallyRegularAt.sublinear_subderivative {f : E → EReal} {x : E}
    (hreg : IsSubdifferentiallyRegularAt f x) (hbot : ∀ w, subderivative f x w ≠ ⊥) :
    Sublinear (subderivative f x) := by
  obtain ⟨hconv, hcone, -, -⟩ := hreg.subderivative_properties
  exact (sublinear_iff_convex_isCone_epigraph_of_ne_bot hbot).2 ⟨hconv, hcone⟩

omit [FiniteDimensional ℝ E] in
/-- A finite semiderivative below `∞` forces the direction into the interior
of `D = {w | df(x̄)(w) < ∞}`; regularity is not needed here. -/
theorem mem_interior_of_hasSemiderivative {f : E → EReal} {x w : E} {β : EReal}
    (h : HasSemiderivative f x w β) (hβ : β < ⊤) :
    w ∈ interior {w | subderivative f x w < ⊤} := by
  obtain ⟨M, hβM, -⟩ := EReal.exists_between_coe_real hβ
  have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, differenceQuotient f x p.1 p.2 < M :=
    h.2.2.eventually (gt_mem_nhds hβM)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hev
  rw [mem_interior]
  refine ⟨interior V, fun w' hw' ↦ ?_, isOpen_interior, mem_interior_iff_mem_nhds.2 hV⟩
  have hV' : V ∈ 𝓝 w' := mem_interior_iff_mem_nhds.1 hw'
  have hev' : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w', differenceQuotient f x p.1 p.2 < M :=
    Filter.mem_of_superset (prod_mem_prod hU hV') hUV
  have hle : subderivative f x w' ≤ M :=
    liminf_le_of_frequently_le' (hev'.frequently.mono fun _ hp ↦ hp.le)
  exact lt_of_le_of_lt hle (EReal.coe_lt_top M)

/-- **Theorem 7.26**: at a regular point, `f` is semidifferentiable for every
`w ∈ int D`, `D = {w | df(x̄)(w) < ∞}`, with semiderivative `df(x̄)(w)`. -/
theorem IsSubdifferentiallyRegularAt.hasSemiderivative_of_mem_interior {f : E → EReal} {x : E}
    (hreg : IsSubdifferentiallyRegularAt f x) {w₀ : E}
    (hw₀ : w₀ ∈ interior {w | subderivative f x w < ⊤}) :
    HasSemiderivative f x w₀ (subderivative f x w₀) := by
  have hconvT : Convex ℝ (epigraph (subderivative f x)) := hreg.subderivative_properties.1
  obtain ⟨hx1, hx2, hC⟩ := hreg
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hx2 hx1).symm
  have hT := epigraph_subderivative_eq_tangentCone hxc
  have hz := toLp_mem_l2Epigraph hx1 hx2
  -- the upper limit of the quotients is at most every real height above `df(x̄)(w₀)`
  have key : ∀ β : ℝ, subderivative f x w₀ < β → upperSemiderivative f x w₀ ≤ β := by
    intro β hβ
    obtain ⟨β₁, hβ₁, hβ₁β⟩ := EReal.exists_between_coe_real hβ
    obtain ⟨δ₂, hδ₂, hball⟩ := Metric.mem_nhds_iff.1
      (eventually_lt_of_convex_epigraph hconvT hw₀ hβ₁)
    obtain ⟨δ, hδ, hδδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < δ₂ := ⟨δ₂ / 2, half_pos hδ₂, half_lt_self hδ₂⟩
    have hBc : IsCompact (closedBall w₀ δ ×ˢ ({β} : Set ℝ)) :=
      (isCompact_closedBall w₀ δ).prod isCompact_singleton
    have hBint : closedBall w₀ δ ×ˢ ({β} : Set ℝ) ⊆
        interior (tangentCone (epigraph f) (x, (f x).toReal)) := by
      rw [← hT]
      have hO : ball w₀ δ₂ ×ˢ Ioi β₁ ⊆ epigraph (subderivative f x) := by
        rintro ⟨w, t⟩ ⟨hw, ht⟩
        rw [mem_epigraph_iff]
        exact (hball hw).le.trans (EReal.coe_le_coe_iff.2 (le_of_lt ht))
      refine Subset.trans ?_ (interior_maximal hO (isOpen_ball.prod isOpen_Ioi))
      rintro ⟨w, t⟩ ⟨hw, ht⟩
      refine ⟨lt_of_le_of_lt (mem_closedBall.1 hw) hδδ₂, ?_⟩
      rw [mem_singleton_iff.1 ht]
      exact EReal.coe_lt_coe_iff.1 hβ₁β
    have hB'c : IsCompact (l2ProdEquiv E ⁻¹' (closedBall w₀ δ ×ˢ ({β} : Set ℝ))) :=
      (l2ProdEquiv E).toHomeomorph.isCompact_preimage.2 hBc
    have hB'int : l2ProdEquiv E ⁻¹' (closedBall w₀ δ ×ˢ ({β} : Set ℝ)) ⊆
        interior (tangentCone (l2Epigraph f) (WithLp.toLp 2 (x, (f x).toReal))) := by
      rw [l2Epigraph, tangentCone_preimage_continuousLinearEquiv, l2ProdEquiv_toLp]
      have hpi : l2ProdEquiv E ⁻¹' interior (tangentCone (epigraph f) (x, (f x).toReal)) =
          interior (l2ProdEquiv E ⁻¹' tangentCone (epigraph f) (x, (f x).toReal)) :=
        (l2ProdEquiv E).toHomeomorph.preimage_interior _
      rw [← hpi]
      exact preimage_mono hBint
    obtain ⟨ε, hε, V, hV, hblow⟩ :=
      exists_nhds_forall_subset_blowUp_of_isCompact_of_isClarkeRegularAt hz hC hB'c hB'int
    have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w₀, differenceQuotient f x p.1 p.2 ≤ β := by
      filter_upwards [prod_mem_prod (Ioo_mem_nhdsGT hε) (closedBall_mem_nhds w₀ hδ)]
        with p hp
      have hsub := hblow _ ⟨hz, mem_of_mem_nhds hV⟩ p.1 hp.1
      rw [l2Epigraph, blowUp_preimage_continuousLinearEquiv, l2ProdEquiv_toLp] at hsub
      have hpB : (l2ProdEquiv E).symm (p.2, β) ∈
          l2ProdEquiv E ⁻¹' (closedBall w₀ δ ×ˢ ({β} : Set ℝ)) := by
        show l2ProdEquiv E ((l2ProdEquiv E).symm (p.2, β)) ∈ closedBall w₀ δ ×ˢ ({β} : Set ℝ)
        rw [ContinuousLinearEquiv.apply_symm_apply]
        exact ⟨hp.2, rfl⟩
      have h1 := hsub hpB
      rw [mem_preimage, ContinuousLinearEquiv.apply_symm_apply,
        ← epigraph_differenceQuotient hxc hp.1.1, mem_epigraph_iff] at h1
      exact h1
    exact limsup_le_of_le (h := hev)
  have hup : upperSemiderivative f x w₀ ≤ subderivative f x w₀ := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨β, hβl, hβu⟩ := EReal.exists_between_coe_real hlt
    exact absurd (key β hβl) (not_le.2 hβu)
  have hsemi : SemidifferentiableFor f x w₀ :=
    (semidifferentiableFor_iff_subderivative_eq_limsup hx1 hx2).2
      (le_antisymm (subderivative_le_upperSemiderivative f x w₀) hup)
  exact hsemi.hasSemiderivative

/-- **Theorem 7.26**, last clause in corrected form: at a regular point, `f`
has a semiderivative below `∞` for `w` exactly when `w ∈ int D`. -/
theorem IsSubdifferentiallyRegularAt.exists_hasSemiderivative_lt_top_iff {f : E → EReal}
    {x : E} (hreg : IsSubdifferentiallyRegularAt f x) {w : E} :
    (∃ β < ⊤, HasSemiderivative f x w β) ↔ w ∈ interior {w | subderivative f x w < ⊤} := by
  constructor
  · rintro ⟨β, hβ, h⟩
    exact mem_interior_of_hasSemiderivative h hβ
  · intro hw
    have hmemw := interior_subset hw
    exact ⟨_, hmemw, hreg.hasSemiderivative_of_mem_interior hw⟩

/-- **Theorem 7.26**: a subdifferentially regular `f` is semidifferentiable
at `x̄` if and only if `df(x̄)(w) < ∞` for all `w`. -/
theorem IsSubdifferentiallyRegularAt.semidifferentiableAt_iff {f : E → EReal} {x : E}
    (hreg : IsSubdifferentiallyRegularAt f x) :
    SemidifferentiableAt f x ↔ ∀ w, subderivative f x w < ⊤ := by
  constructor
  · intro hs w
    obtain ⟨g, -, -, hall⟩ := hs.exists_semiderivative
    rw [(hall w).2.1]
    exact EReal.coe_lt_top _
  · intro hall w
    have huniv : {w | subderivative f x w < ⊤} = univ := eq_univ_of_forall hall
    have hw : w ∈ interior {w | subderivative f x w < ⊤} := by
      rw [huniv, interior_univ]
      exact mem_univ w
    exact ⟨_, hreg.hasSemiderivative_of_mem_interior hw⟩

/-! ### Example 7.27 -/

/-- **Example 7.27**: a proper convex function is subdifferentially regular,
and epi-differentiable, at every point of its domain where it is locally lower
semicontinuous. -/
theorem isSubdifferentiallyRegularAt_of_convex {f : E → EReal}
    (hconv : Convex ℝ (epigraph f)) {x : E} (hlsc : IsLocallyLscAt f x) :
    IsSubdifferentiallyRegularAt f x ∧ EpiDifferentiableAt f x := by
  have hreg : IsSubdifferentiallyRegularAt f x := by
    refine ⟨hlsc.1, hlsc.2.1, isClarkeRegularAt_of_convex ?_ (toLp_mem_l2Epigraph hlsc.1 hlsc.2.1)
      ?_⟩
    · exact convex_preimage_continuousLinearEquiv (l2ProdEquiv E) hconv
    · exact IsLocallyClosedAt.preimage_continuousLinearEquiv (l2ProdEquiv E)
        hlsc.isLocallyClosedAt_epigraph
  exact ⟨hreg, hreg.epiDifferentiableAt⟩

/-- **Example 7.27**: at a point in the interior of the domain of a proper
convex function, the function is locally lower semicontinuous, so the previous
conclusions hold, and it is moreover semidifferentiable. -/
theorem semidifferentiableAt_of_convex_of_mem_interior {f : E → EReal} (hproper : IsProper f)
    (hconv : Convex ℝ (epigraph f)) {x : E} (hx : x ∈ interior (effectiveDomain f)) :
    IsLocallyLscAt f x ∧ IsSubdifferentiallyRegularAt f x ∧ EpiDifferentiableAt f x ∧
      SemidifferentiableAt f x := by
  set U := interior (effectiveDomain f) with hU_def
  have hdomU : ∀ y ∈ U, f y < ⊤ := fun y hy ↦ by
    have hmem := interior_subset hy
    exact hmem
  have hfinU : ∀ y ∈ U, f y = (((f y).toReal : ℝ) : EReal) := fun y hy ↦
    (EReal.coe_toReal (hdomU y hy).ne (hproper.2 y).ne').symm
  set G : E → ℝ := fun y ↦ (f y).toReal with hG_def
  have hUconv : Convex ℝ U := (convex_setOf_lt_top_of_convex_epigraph hconv).interior
  have hGconv : ConvexOn ℝ U G := by
    refine ⟨hUconv, fun u hu v hv a b ha hb hab ↦ ?_⟩
    have hmem := hconv ((mem_epigraph_iff f u (G u)).2 (le_of_eq (hfinU u hu)))
      ((mem_epigraph_iff f v (G v)).2 (le_of_eq (hfinU v hv))) ha hb hab
    rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, mem_epigraph_iff,
      hfinU _ (hUconv hu hv ha hb hab)] at hmem
    exact EReal.coe_le_coe_iff.1 hmem
  have hGcont : ContinuousOn G U := hGconv.continuousOn isOpen_interior
  have hUx : U ∈ 𝓝 x := isOpen_interior.mem_nhds hx
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 hUx
  have hlsc : IsLocallyLscAt f x := by
    refine ⟨(hproper.2 x).ne', (hdomU x hx).ne, ε₀ / 2, half_pos hε₀, fun α _ ↦ ?_⟩
    have hsub : closedBall x (ε₀ / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hε₀)).trans hball
    have hset : closedBall x (ε₀ / 2) ∩ {y | f y ≤ α} =
        closedBall x (ε₀ / 2) ∩ G ⁻¹' Iic α := by
      ext y
      constructor
      · rintro ⟨hy, hfy⟩
        refine ⟨hy, ?_⟩
        have hfy' : f y ≤ α := hfy
        rw [hfinU y (hsub hy)] at hfy'
        exact EReal.coe_le_coe_iff.1 hfy'
      · rintro ⟨hy, hGy⟩
        refine ⟨hy, ?_⟩
        show f y ≤ α
        rw [hfinU y (hsub hy)]
        exact EReal.coe_le_coe_iff.2 hGy
    rw [hset]
    exact (hGcont.mono hsub).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
  obtain ⟨hreg, hepi⟩ := isSubdifferentiallyRegularAt_of_convex hconv hlsc
  refine ⟨hlsc, hreg, hepi, hreg.semidifferentiableAt_iff.2 fun w ↦ ?_⟩
  -- a point `x + t₀ w` of `U` bounds the difference quotients through convexity
  have hpath : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝 0) (𝓝 x) := by
    have h0 : Tendsto (fun t : ℝ ↦ x + t • w) (𝓝 0) (𝓝 (x + (0 : ℝ) • w)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rwa [zero_smul, add_zero] at h0
  obtain ⟨δ, hδ, hδU⟩ := Metric.eventually_nhds_iff.1 (hpath.eventually hUx)
  obtain ⟨t₀, ht₀, ht₀δ⟩ : ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ < δ := ⟨δ / 2, half_pos hδ, half_lt_self hδ⟩
  have hxt₀ : x + t₀ • w ∈ U := hδU (by rwa [Real.dist_eq, sub_zero, abs_of_pos ht₀])
  have hbound : ∀ τ ∈ Ioo (0 : ℝ) t₀,
      differenceQuotient f x τ w ≤ (((G (x + t₀ • w) - G x) / t₀ : ℝ) : EReal) := by
    intro τ hτ
    have hτpos : 0 < τ := hτ.1
    have hb : 0 ≤ τ / t₀ := div_nonneg hτpos.le ht₀.le
    have ha : 0 ≤ 1 - τ / t₀ := by
      rw [sub_nonneg, div_le_one ht₀]
      exact hτ.2.le
    have hab : 1 - τ / t₀ + τ / t₀ = 1 := sub_add_cancel 1 (τ / t₀)
    have hdiv : τ / t₀ * t₀ = τ := div_mul_cancel₀ τ ht₀.ne'
    have hcomb : (1 - τ / t₀) • x + (τ / t₀) • (x + t₀ • w) = x + τ • w := by
      rw [smul_add, smul_smul, hdiv, ← add_assoc, ← add_smul, hab, one_smul]
    have hxτU : x + τ • w ∈ U := by
      rw [← hcomb]
      exact hUconv hx hxt₀ ha hb hab
    have hineq := hGconv.2 hx hxt₀ ha hb hab
    rw [hcomb] at hineq
    simp only [smul_eq_mul] at hineq
    rw [differenceQuotient_eq_coe (hfinU x hx) (hfinU _ hxτU)]
    apply EReal.coe_le_coe_iff.2
    have hkey : G (x + τ • w) - G x ≤ τ / t₀ * (G (x + t₀ • w) - G x) := by linarith
    rw [le_div_iff₀ ht₀]
    have h4 : τ / t₀ * (t₀ / τ) = 1 := by
      rw [div_mul_div_comm, mul_comm τ t₀, div_self (mul_ne_zero ht₀.ne' hτpos.ne')]
    calc τ⁻¹ * (G (x + τ • w) - G x) * t₀ = (G (x + τ • w) - G x) * (t₀ / τ) := by ring
      _ ≤ τ / t₀ * (G (x + t₀ • w) - G x) * (t₀ / τ) :=
          mul_le_mul_of_nonneg_right hkey (div_nonneg ht₀.le hτpos.le)
      _ = (G (x + t₀ • w) - G x) * (τ / t₀ * (t₀ / τ)) := by ring
      _ = G (x + t₀ • w) - G x := by rw [h4, mul_one]
  have hfreq : ∃ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      differenceQuotient f x p.1 p.2 ≤ (((G (x + t₀ • w) - G x) / t₀ : ℝ) : EReal) := by
    have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        differenceQuotient f x τ w ≤ (((G (x + t₀ • w) - G x) / t₀ : ℝ) : EReal) :=
      Filter.mem_of_superset (Ioo_mem_nhdsGT ht₀) fun τ hτ ↦ hbound τ hτ
    exact (tendsto_pair_const w).frequently hev.frequently
  exact lt_of_le_of_lt (liminf_le_of_frequently_le' hfreq) (EReal.coe_lt_top _)

/-! ### The last clause of 7.26 as printed fails for infinite semiderivatives -/

theorem epigraph_indicatorVA_Ici_zero :
    epigraph (indicatorVA (Ici (0 : ℝ))) = Ici 0 ×ˢ Ici 0 := by
  ext ⟨y, t⟩
  rw [mem_epigraph_iff, mem_prod, mem_Ici, mem_Ici]
  by_cases hy : 0 ≤ y
  · rw [indicatorVA_apply_mem (show y ∈ Ici (0 : ℝ) from hy)]
    simp [hy]
  · rw [indicatorVA_apply_not_mem (show y ∉ Ici (0 : ℝ) from hy)]
    simp [hy]

/-- The last clause of **Theorem 7.26** as printed ("semidifferentiable at `x̄`
for `w` if and only if `w ∈ int D`") fails once the infinite semiderivatives
allowed by Definition 7.20 are taken into account: the indicator of `[0, ∞)`
is subdifferentially regular at `0` and semidifferentiable there for `w = -1`
(with semiderivative `∞`), yet `-1 ∉ int D`.  The corrected statement is
`IsSubdifferentiallyRegularAt.exists_hasSemiderivative_lt_top_iff`. -/
theorem not_forall_semidifferentiableFor_iff_mem_interior :
    IsSubdifferentiallyRegularAt (indicatorVA (Ici (0 : ℝ))) 0 ∧
      HasSemiderivative (indicatorVA (Ici (0 : ℝ))) 0 (-1) ⊤ ∧
      (-1 : ℝ) ∉ interior {w | subderivative (indicatorVA (Ici (0 : ℝ))) 0 w < ⊤} := by
  have hf0 : indicatorVA (Ici (0 : ℝ)) 0 = ((0 : ℝ) : EReal) := by
    rw [indicatorVA_apply_mem (self_mem_Ici : (0 : ℝ) ∈ Ici (0 : ℝ)), EReal.coe_zero]
  have hx1 : indicatorVA (Ici (0 : ℝ)) 0 ≠ ⊥ := by rw [hf0]; exact EReal.coe_ne_bot 0
  have hx2 : indicatorVA (Ici (0 : ℝ)) 0 ≠ ⊤ := by rw [hf0]; exact EReal.coe_ne_top 0
  have hepi := epigraph_indicatorVA_Ici_zero
  have hreg : IsSubdifferentiallyRegularAt (indicatorVA (Ici (0 : ℝ))) 0 := by
    refine ⟨hx1, hx2, isClarkeRegularAt_of_convex ?_ (toLp_mem_l2Epigraph hx1 hx2) ?_⟩
    · apply convex_preimage_continuousLinearEquiv
      rw [hepi]
      exact (convex_Ici 0).prod (convex_Ici 0)
    · apply IsClosed.isLocallyClosedAt
      apply IsClosed.preimage (l2ProdEquiv ℝ).continuous
      rw [hepi]
      exact isClosed_Ici.prod isClosed_Ici
  have hsemi : HasSemiderivative (indicatorVA (Ici (0 : ℝ))) 0 (-1) ⊤ := by
    refine ⟨hx1, hx2, tendsto_nhds_of_eventually_eq ?_⟩
    filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0),
      tendsto_snd.eventually (Iio_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with p hp1 hp2
    apply differenceQuotient_eq_top hp1 hf0
    rw [zero_add, smul_eq_mul]
    exact indicatorVA_apply_not_mem (show p.1 * p.2 ∉ Ici (0 : ℝ) from
      not_le.2 (mul_neg_of_pos_of_neg hp1 hp2))
  refine ⟨hreg, hsemi, fun hmem ↦ ?_⟩
  have hmem' := interior_subset hmem
  have hlt : subderivative (indicatorVA (Ici (0 : ℝ))) 0 (-1) < ⊤ := hmem'
  rw [hsemi.subderivative_eq] at hlt
  exact lt_irrefl _ hlt

end Regularity

end RW
