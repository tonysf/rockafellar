/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: subgradients of piecewise linear-quadratic functions

This file formalizes Proposition 12.30 and Example 12.31.

For a proper lsc convex `f` and `λ > 0` the book argues:
* (b) ⇔ (d) by 12.29, since `Pλf = (I + λ∂f)⁻¹`;
* (d) ⇔ (c) through `∇eλf = λ⁻¹(I - Pλf)` (2.26, here 12.23), since a smooth
  function is piecewise linear-quadratic exactly when its gradient is piecewise
  linear;
* (c) ⇔ (a) by 11.14(b), because `(eλf)* = f* + (λ/2)‖·‖²` (11.24(b)).

The smooth-function fact is proved here in both directions for a
differentiable `φ : E → ℝ` with continuous gradient.  If `φ` is piecewise
linear-quadratic, the pieces with nonempty interior already cover the space
(Baire), and on each such piece the gradient of the quadratic agrees with `∇φ`
on the interior, hence on the piece, which is the closure of its interior.
Conversely, if `∇φ(x) = Ax + a` on a convex piece, `φ` is the quadratic with the
symmetrized matrix `½(A + A*)` there, by the mean value theorem along segments.

Example 12.31 is 12.30 for `f = δ_C` and `λ = ½`: `δ_C` is piecewise
linear-quadratic exactly when the convex set `C` is polyhedral, `∂δ_C = N_C`,
`e_{1/2}δ_C = d_C²` and `P_{1/2}δ_C = P_C`.
-/

import RockafellarWets.Chapter12.PiecewisePolyhedralMonotonicity
import RockafellarWets.Chapter12.MoreauYosida
import RockafellarWets.Chapter12.ProjectionMonotonicity
import RockafellarWets.Chapter11.PiecewiseLinearQuadraticEnvelopes
import RockafellarWets.Chapter11.PiecewiseLinearConjugacy
import RockafellarWets.Chapter10.ConvexPolyhedralUnions
import RockafellarWets.Chapter10.PLQOperations

open Set Filter Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Quadratics

omit [FiniteDimensional ℝ E] in
theorem QuadraticPiece.eval_add_sub (q : QuadraticPiece E) (x d : E) :
    q.eval (x + d) - q.eval x - ⟪q.matrix x + q.linear, d⟫_ℝ = 1 / 2 * ⟪d, q.matrix d⟫_ℝ := by
  simp only [QuadraticPiece.eval, map_add, inner_add_left, inner_add_right]
  have h1 := q.symmetric x d
  have h2 := real_inner_comm (q.matrix x) d
  linarith

/-- The gradient of a quadratic piece is `Qx + b`. -/
theorem QuadraticPiece.hasGradientAt (q : QuadraticPiece E) (x : E) :
    HasGradientAt q.eval (q.matrix x + q.linear) x := by
  refine hasGradientAt_of_abs_sub_inner_le (C := ‖q.matrix‖) fun x' ↦ ?_
  have h := q.eval_add_sub x (x' - x)
  rw [add_sub_cancel] at h
  rw [h]
  have h1 := abs_real_inner_le_norm (x' - x) (q.matrix (x' - x))
  have h2 := q.matrix.le_opNorm (x' - x)
  have h3 : ‖x' - x‖ * ‖q.matrix (x' - x)‖ ≤ ‖x' - x‖ * (‖q.matrix‖ * ‖x' - x‖) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [abs_nonneg ⟪x' - x, q.matrix (x' - x)⟫_ℝ, norm_nonneg (x' - x), norm_nonneg q.matrix,
    mul_nonneg (norm_nonneg q.matrix) (sq_nonneg ‖x' - x‖)]

omit [FiniteDimensional ℝ E] in
/-- A quadratic piece with prescribed symmetric matrix, slope and value at a base point. -/
theorem exists_quadraticPiece_eval_eq (S : E →L[ℝ] E) (hS : ∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ)
    (w x₀ : E) (c : ℝ) : ∃ q : QuadraticPiece E, ∀ x,
      q.eval x = c + ⟪w, x - x₀⟫_ℝ + 1 / 2 * ⟪x - x₀, S (x - x₀)⟫_ℝ := by
  refine ⟨⟨S, hS, w - S x₀, c - ⟪w, x₀⟫_ℝ + 1 / 2 * ⟪x₀, S x₀⟫_ℝ⟩, fun x ↦ ?_⟩
  simp only [QuadraticPiece.eval, map_sub, inner_sub_left, inner_sub_right]
  have h1 := hS x₀ x
  have h2 := real_inner_comm (S x₀) x
  linarith

end Quadratics

section PiecewiseLinearGradients

omit [FiniteDimensional ℝ E] in
/-- Affine combinations of the identity and a piecewise linear mapping are
piecewise linear on the same set. -/
theorem IsPiecewiseLinearOn.smul_add_smul {F : E → E} {D : Set E}
    (h : IsPiecewiseLinearOn F D) (α β : ℝ) :
    IsPiecewiseLinearOn (fun x ↦ α • x + β • F x) D := by
  obtain ⟨m, C, A, a, hC, hD, hF⟩ := h
  refine ⟨m, C, fun i ↦ α • ContinuousLinearMap.id ℝ E + β • A i, fun i ↦ β • a i, hC, hD,
    fun i x hx ↦ ?_⟩
  change α • x + β • F x = (α • ContinuousLinearMap.id ℝ E + β • A i) x + β • a i
  rw [hF i x hx]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_add]
  abel

/-- A piecewise linear-quadratic function with a continuous gradient has a
piecewise linear gradient. -/
theorem isPiecewiseLinearOn_of_isPiecewiseLinearQuadratic {φ : E → ℝ} {G : E → E}
    (hd : ∀ x, HasGradientAt φ (G x) x) (hG : Continuous G)
    (hplq : IsPiecewiseLinearQuadratic fun x ↦ (φ x : EReal)) : IsPiecewiseLinearOn G univ := by
  classical
  obtain ⟨m, C, q, hC, hdom, hq⟩ := hplq
  have hdom' : ⋃ i, C i = univ := by
    rw [← hdom]
    exact eq_univ_of_forall fun x ↦ EReal.coe_lt_top _
  have hφq : ∀ i, ∀ x ∈ C i, φ x = (q i).eval x := fun i x hx ↦
    EReal.coe_injective (hq i x hx)
  set C' : Fin m → Set E := fun i ↦ if (interior (C i)).Nonempty then C i else ∅ with hC'
  refine ⟨m, C', fun i ↦ (q i).matrix, fun i ↦ (q i).linear, fun i ↦ ?_, ?_, fun i x hx ↦ ?_⟩
  · simp only [hC']
    split_ifs
    · exact hC i
    · exact IsPolyhedral.empty
  · have hdense := dense_iUnion_interior_of_closed (fun i ↦ (hC i).isClosed) hdom'
    have hsub : (⋃ i, interior (C i)) ⊆ ⋃ i, C' i := by
      refine iUnion_mono fun i y hy ↦ ?_
      simp only [hC']
      split_ifs with hint
      · exact interior_subset hy
      · exact absurd ⟨y, hy⟩ hint
    have hclosed : IsClosed (⋃ i, C' i) := isClosed_iUnion_of_finite fun i ↦ by
      simp only [hC']
      split_ifs
      · exact (hC i).isClosed
      · exact isClosed_empty
    refine (eq_univ_of_univ_subset ?_).symm
    rw [← hdense.closure_eq]
    exact closure_minimal hsub hclosed
  · simp only [hC'] at hx
    split_ifs at hx with hint
    · have heq : EqOn G (fun y ↦ (q i).matrix y + (q i).linear) (interior (C i)) := by
        intro y hy
        have hev : φ =ᶠ[𝓝 y] (q i).eval := by
          filter_upwards [isOpen_interior.mem_nhds hy] with z hz using hφq i z (interior_subset hz)
        exact (hd y).unique (((q i).hasGradientAt y).congr_of_eventuallyEq hev)
      have hcl := heq.closure hG ((q i).matrix.continuous.add continuous_const)
      rw [(hC i).convex.closure_interior_eq_closure_of_nonempty_interior hint,
        (hC i).isClosed.closure_eq] at hcl
      exact hcl hx
    · exact absurd hx (notMem_empty x)

/-- If `∇φ(y) = Ay + a` on a convex set containing `x₀` and `x`, then `φ` is
the corresponding quadratic along the segment, by the mean value theorem. -/
theorem eq_quadratic_of_hasGradientAt_affine {φ : E → ℝ} {G : E → E}
    (hd : ∀ x, HasGradientAt φ (G x) x) {C : Set E} (hC : Convex ℝ C) {A : E →L[ℝ] E} {a : E}
    (hGA : ∀ y ∈ C, G y = A y + a) {x₀ x : E} (hx₀ : x₀ ∈ C) (hx : x ∈ C) :
    φ x = φ x₀ + ⟪A x₀ + a, x - x₀⟫_ℝ + 1 / 2 * ⟪x - x₀, A (x - x₀)⟫_ℝ := by
  set d := x - x₀ with hd_def
  set c₁ := ⟪A x₀ + a, d⟫_ℝ
  set c₂ := ⟪d, A d⟫_ℝ
  let ψ : ℝ → ℝ := fun t ↦ φ (x₀ + t • d) - (t * c₁ + t ^ 2 / 2 * c₂)
  have hderiv : ∀ t, HasDerivAt ψ (⟪G (x₀ + t • d), d⟫_ℝ - (c₁ + t * c₂)) t := by
    intro t
    have hγ : HasDerivAt (fun s : ℝ ↦ x₀ + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x₀
    have h1 := (hd (x₀ + t • d)).hasFDerivAt.comp_hasDerivAt t hγ
    rw [InnerProductSpace.toDual_apply_apply] at h1
    have h2 : HasDerivAt (fun s : ℝ ↦ s * c₁ + s ^ 2 / 2 * c₂) (c₁ + t * c₂) t := by
      have := ((hasDerivAt_id t).mul_const c₁).add
        (((hasDerivAt_pow 2 t).div_const 2).mul_const c₂)
      convert this using 1
      norm_num
    exact h1.sub h2
  have hzero : ∀ t ∈ Icc (0 : ℝ) 1, ⟪G (x₀ + t • d), d⟫_ℝ - (c₁ + t * c₂) = 0 := by
    intro t ht
    have hmem : x₀ + t • d ∈ C := hC.add_smul_sub_mem hx₀ hx ht
    rw [hGA _ hmem, map_add, map_smul, inner_add_left, inner_add_left, real_inner_smul_left]
    have e1 : c₁ = ⟪A x₀, d⟫_ℝ + ⟪a, d⟫_ℝ := inner_add_left _ _ _
    have e2 : c₂ = ⟪A d, d⟫_ℝ := real_inner_comm (A d) d
    rw [e1, e2]
    ring
  have hconst := constant_of_has_deriv_right_zero (f := ψ) (a := 0) (b := 1)
    (fun t _ ↦ (hderiv t).continuousAt.continuousWithinAt)
    (fun t ht ↦ by
      have := (hderiv t).hasDerivWithinAt (s := Ici t)
      rwa [hzero t (Ico_subset_Icc_self ht)] at this) 1 ⟨zero_le_one, le_rfl⟩
  simp only [ψ, one_smul, zero_smul, add_zero, one_pow, zero_mul, zero_pow two_ne_zero,
    zero_div, sub_zero] at hconst
  rw [show x₀ + d = x by rw [hd_def]; abel] at hconst
  linarith

/-- A differentiable function with a piecewise linear gradient is piecewise
linear-quadratic. -/
theorem isPiecewiseLinearQuadratic_of_isPiecewiseLinearOn_gradient {φ : E → ℝ} {G : E → E}
    (hd : ∀ x, HasGradientAt φ (G x) x) (hG : IsPiecewiseLinearOn G univ) :
    IsPiecewiseLinearQuadratic fun x ↦ (φ x : EReal) := by
  classical
  obtain ⟨m, C, A, a, hC, hU, hGA⟩ := hG
  have hpiece : ∀ i, ∃ q : QuadraticPiece E, ∀ x ∈ C i, φ x = q.eval x := by
    intro i
    rcases (C i).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · exact ⟨⟨0, by simp, 0, 0⟩, fun x hx ↦ by rw [he] at hx; exact absurd hx (notMem_empty x)⟩
    set S : E →L[ℝ] E := (1 / 2 : ℝ) • (A i + ContinuousLinearMap.adjoint (A i)) with hS
    have hSsym : ∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ := by
      intro x y
      simp only [hS, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
        ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
      ring
    have hSd : ∀ d, ⟪d, S d⟫_ℝ = ⟪d, A i d⟫_ℝ := by
      intro d
      simp only [hS, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        real_inner_smul_right, inner_add_right, ContinuousLinearMap.adjoint_inner_right]
      rw [real_inner_comm (A i d) d]
      ring
    obtain ⟨q, hq⟩ := exists_quadraticPiece_eval_eq S hSsym (A i x₀ + a i) x₀ (φ x₀)
    refine ⟨q, fun x hx ↦ ?_⟩
    rw [hq, hSd, eq_quadratic_of_hasGradientAt_affine hd (hC i).convex (hGA i) hx₀ hx]
  choose q hq using hpiece
  refine ⟨m, C, q, hC, ?_, fun i x hx ↦ congrArg (fun r : ℝ ↦ (r : EReal)) (hq i x hx)⟩
  rw [← hU]
  exact eq_univ_of_forall fun x ↦ EReal.coe_lt_top _

end PiecewiseLinearGradients

section Proposition

/-- In the convex case, `(c) ⇒ (a)` of 12.30: `(eλf)* = f* + (λ/2)‖·‖²`. -/
theorem isPiecewiseLinearQuadratic_of_moreauEnvelopeEReal {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam)
    (h : IsPiecewiseLinearQuadratic (moreauEnvelopeEReal f lam)) :
    IsPiecewiseLinearQuadratic f := by
  have hfin := fun x ↦ (moreauEnvelopeReal_eq_of_convex hp hl hc hlam x).1
  set g : E → EReal := fun v ↦ fenchelConjugate f v + (moreauQuadratic lam⁻¹ v : EReal)
  have hpc := isProper_fenchelConjugate hp hl hc
  have he : moreauEnvelopeEReal f lam = fenchelConjugate g := by
    rw [fenchelConjugate_regularized_dual hp hl hc hlam]
  have hep : IsProper (moreauEnvelopeEReal f lam) :=
    ⟨⟨0, by rw [hfin 0]; exact EReal.coe_lt_top _⟩, fun x ↦ by
      rw [hfin x]; exact EReal.bot_lt_coe _⟩
  have hel : LowerSemicontinuous (moreauEnvelopeEReal f lam) := by
    rw [he]; exact lowerSemicontinuous_fenchelConjugate _
  have hec : Convex ℝ (epigraph (moreauEnvelopeEReal f lam)) := by
    rw [he]; exact convex_epigraph_fenchelConjugate _
  have hg : IsPiecewiseLinearQuadratic g := by
    have := h.isPiecewiseLinearQuadratic_fenchelConjugate hep hel hec
    rwa [fenchelConjugate_moreauEnvelopeEReal hp hlam] at this
  have hf' : IsPiecewiseLinearQuadratic (fenchelConjugate f) := by
    have hsum := hg.add (isPiecewiseLinearQuadratic_moreauQuadratic (-lam⁻¹))
    convert hsum using 1
    funext v
    have hq : moreauQuadratic (-lam⁻¹) v = -moreauQuadratic lam⁻¹ v := by
      simp only [moreauQuadratic]
      ring
    have hb := (hpc.2 v).ne'
    simp only [g, hq, EReal.coe_neg]
    induction h' : fenchelConjugate f v using EReal.rec with
    | bot => exact absurd h' hb
    | top => simp
    | coe r =>
      rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_add]
      congr 1
      ring
  exact (isPiecewiseLinearQuadratic_fenchelConjugate_iff hp hl hc).1 hf'

/-- **Proposition 12.30 (subgradients of piecewise linear-quadratic functions).**
For a proper lsc convex `f` and `λ > 0`, the following are equivalent:
(a) `f` is piecewise linear-quadratic; (b) `∂f` is piecewise polyhedral;
(c) `eλf` is piecewise linear-quadratic; (d) `Pλf` is piecewise linear. -/
theorem subgradients_of_piecewise_linear_quadratic_functions {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {lam : ℝ} (hlam : 0 < lam) :
    List.TFAE [IsPiecewiseLinearQuadratic f, SvPiecewisePolyhedral (subdifferential f),
      IsPiecewiseLinearQuadratic (moreauEnvelopeEReal f lam),
      ∃ P : E → E, (∀ z, proximalMappingEReal f lam z = {P z}) ∧ IsPiecewiseLinearOn P univ] := by
  have hT := svMaximalMonotone_subdifferential_of_convex hp hl hc
  set R := resolventMap (subdifferential f) lam with hR
  have hPR : ∀ z, proximalMappingEReal f lam z = {R z} :=
    proximalMappingEReal_eq_singleton_of_convex hp hl hc hlam
  have hd : ∀ P : E → E, (∀ z, proximalMappingEReal f lam z = {P z}) → P = R := fun P hP ↦
    funext fun z ↦ singleton_eq_singleton_iff.1 ((hP z).symm.trans (hPR z))
  have hfin := fun x ↦ (moreauEnvelopeReal_eq_of_convex hp hl hc hlam x).1
  have he : moreauEnvelopeEReal f lam = fun x ↦ (moreauEnvelopeReal f lam x : EReal) := funext hfin
  obtain ⟨-, hgrad, -, -, hlip, -⟩ := moreauEnvelope_yosida hp hl hc hlam
  have hY : ∀ x, yosidaMap (subdifferential f) lam x = lam⁻¹ • x + (-lam⁻¹) • R x := by
    intro x
    rw [hT.yosidaMap_eq hlam, smul_sub, neg_smul, ← sub_eq_add_neg]
  have hRY : ∀ x, R x = (1 : ℝ) • x + (-lam) • yosidaMap (subdifferential f) lam x := by
    intro x
    have hne : lam ≠ 0 := hlam.ne'
    rw [hY, smul_add, smul_smul, smul_smul, one_smul]
    have h1 : -lam * lam⁻¹ = -1 := by field_simp
    have h2 : -lam * -lam⁻¹ = 1 := by field_simp
    rw [h1, h2, neg_one_smul, one_smul]
    abel
  have hGcont : Continuous (yosidaMap (subdifferential f) lam) :=
    (hT.lipschitzWith_yosidaMap hlam).continuous
  tfae_have 1 → 3 := fun h ↦ h.isPiecewiseLinearQuadratic_moreauEnvelopeEReal hp hc hlam
  tfae_have 3 → 1 := isPiecewiseLinearQuadratic_of_moreauEnvelopeEReal hp hl hc hlam
  tfae_have 2 ↔ 4 := by
    rw [svPiecewisePolyhedral_iff_isPiecewiseLinearOn_resolventMap hT hlam]
    constructor
    · exact fun h ↦ ⟨R, hPR, h⟩
    · rintro ⟨P, hP, h⟩
      rwa [hd P hP] at h
  tfae_have 3 → 4 := by
    intro h
    rw [he] at h
    have hG := isPiecewiseLinearOn_of_isPiecewiseLinearQuadratic hgrad hGcont h
    refine ⟨R, hPR, ?_⟩
    have := hG.smul_add_smul 1 (-lam)
    convert this using 1
    exact funext hRY
  tfae_have 4 → 3 := by
    rintro ⟨P, hP, h⟩
    rw [hd P hP] at h
    rw [he]
    refine isPiecewiseLinearQuadratic_of_isPiecewiseLinearOn_gradient hgrad ?_
    have := h.smul_add_smul lam⁻¹ (-lam⁻¹)
    convert this using 1
    exact funext hY
  tfae_finish

/-- The indicator of a convex set is piecewise linear-quadratic exactly when the
set is polyhedral. -/
theorem isPiecewiseLinearQuadratic_indicatorVA_iff {C : Set E} (hconv : Convex ℝ C) :
    IsPiecewiseLinearQuadratic (indicatorVA C) ↔ IsPolyhedral C := by
  constructor
  · rintro ⟨m, D, q, hD, hdom, -⟩
    rw [effectiveDomain_indicatorVA] at hdom
    rw [hdom] at hconv ⊢
    exact isPolyhedral_iUnion_of_convex hD hconv
  · exact fun h ↦ ((isPiecewiseLinear_indicatorVA_iff hconv).2 h).isPiecewiseLinearQuadratic

/-- **Example 12.31 (piecewise linear projections).**  For a nonempty closed
convex `C`, the following are equivalent: (a) `C` is polyhedral; (b) `N_C` is
piecewise polyhedral; (c) `d_C²` is piecewise linear-quadratic; (d) `P_C` is
piecewise linear. -/
theorem piecewise_linear_projections {C : Set E} (hC : IsClosed C) (hconv : Convex ℝ C)
    (hne : C.Nonempty) :
    List.TFAE [IsPolyhedral C, SvPiecewisePolyhedral (normalCone C),
      IsPiecewiseLinearQuadratic (fun x ↦ ((infDist x C ^ 2 : ℝ) : EReal)),
      ∃ P : E → E, (∀ z, projMapping C z = {P z}) ∧ IsPiecewiseLinearOn P univ] := by
  obtain ⟨hp, hl, hc⟩ := indicatorVA_proper_lsc_convex hC hconv hne
  have h := subgradients_of_piecewise_linear_quadratic_functions hp hl hc
    (by norm_num : (0 : ℝ) < 1 / 2)
  rw [isPiecewiseLinearQuadratic_indicatorVA_iff hconv, subdifferential_indicatorVA_eq_normalCone,
    proximalMappingEReal_indicatorVA C (by norm_num : (0 : ℝ) < 1 / 2)] at h
  have he : moreauEnvelopeEReal (indicatorVA C) (1 / 2) =
      fun x ↦ ((infDist x C ^ 2 : ℝ) : EReal) :=
    funext fun x ↦ moreauEnvelopeEReal_indicatorVA_half hC hne x
  rwa [he] at h

end Proposition

end RW
