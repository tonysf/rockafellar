/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lagrangians in the Fenchel scheme

Example 11.47, including the extended linear-quadratic case of 11.43.
-/
import RockafellarWets.Chapter11.FenchelDuality
import RockafellarWets.Chapter8.IndicatorSubgradients
import RockafellarWets.Chapter8.SubgradientsAndGradients

open Set Filter Topology
open scoped InnerProductSpace Pointwise
namespace RW
noncomputable section

theorem ereal_coe_add_coe_add_sub_coe (m κ s t : ℝ) (H : EReal) :
    ((m : EReal) + κ + H) - ((t - s : ℝ) : EReal) = ((m + κ + s : ℝ) : EReal) + (H - (t : EReal)) := by
  induction H using EReal.rec with
  | bot => simp
  | top => rw [← EReal.coe_add, EReal.coe_add_top, EReal.top_sub_coe, EReal.top_sub_coe,
      EReal.coe_add_top]
  | coe H =>
    norm_cast
    ring

theorem ereal_coe_add_neg_eq {m κ s β α : ℝ} (H : EReal) (hs : s = β - α) :
    ((m + κ + s : ℝ) : EReal) + -H = (m : EReal) + κ + β - H - α := by
  induction H using EReal.rec with
  | bot => simp
  | top => simp
  | coe H =>
    norm_cast
    rw [hs]
    ring

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The Lagrangian of **11.47**, `l(x,y) = ⟨c,x⟩ + k(x) + ⟨b,y⟩ - h*(y) - ⟨y,Ax⟩`
with the convention `∞ - ∞ = ∞`. -/
def fenchelLagrangian (k : E → EReal) (h : P → EReal) (A : E →L[ℝ] P) (b : P) (c : E)
    (x : E) (y : P) : EReal :=
  if k x = ⊤ then ⊤ else
    (⟪c, x⟫_ℝ : EReal) + k x + (⟪b, y⟫_ℝ : EReal) - fenchelConjugate h y - (⟪y, A x⟫_ℝ : EReal)

section General
variable {k : E → EReal} {h : P → EReal} (A : E →L[ℝ] P) (b : P) (c : E)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- **Example 11.47**: the Lagrangian of the Fenchel parameterization. -/
theorem lagrangian_fenchelIntegrand (hkb : ∀ x, k x ≠ ⊥) (hhb : ∀ w, h w ≠ ⊥) :
    lagrangian (fenchelIntegrand k h A b c) = fenchelLagrangian k h A b c := by
  funext x y
  unfold lagrangian fenchelLagrangian
  split_ifs with hkx
  · refine iInf_eq_top.mpr fun u ↦ ?_
    change (⟪c, x⟫_ℝ : EReal) + k x + h (b - A x + u) - (⟪y, u⟫_ℝ : EReal) = ⊤
    rw [hkx, EReal.coe_add_top, EReal.top_add_of_ne_bot (hhb _), EReal.top_sub_coe]
  · obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, k x = κ := ⟨_, (EReal.coe_toReal hkx (hkb x)).symm⟩
    have hshift : (⨅ u : P, fenchelIntegrand k h A b c (WithLp.toLp 2 (x, u)) -
          (⟪y, u⟫_ℝ : EReal)) =
        ⨅ w : P, ((⟪c, x⟫_ℝ + κ + ⟪y, b - A x⟫_ℝ : ℝ) : EReal) + (h w - (⟪y, w⟫_ℝ : EReal)) := by
      refine (Equiv.subRight (b - A x)).iInf_comp.symm.trans (iInf_congr fun w ↦ ?_)
      change (⟪c, x⟫_ℝ : EReal) + k x + h (b - A x + (w - (b - A x))) -
        (⟪y, w - (b - A x)⟫_ℝ : EReal) = _
      rw [show b - A x + (w - (b - A x)) = w by abel, inner_sub_right, hκ]
      exact ereal_coe_add_coe_add_sub_coe _ _ _ _ _
    rw [hshift, ← coe_add_iInf, iInf_sub_inner_eq_neg_fenchelConjugate, hκ]
    exact ereal_coe_add_neg_eq _ (by rw [inner_sub_right, real_inner_comm b y])

/-- **Example 11.47**: the optimality conditions of **11.41** are the
Lagrangian conditions `0 ∈ ∂ₓl(x̄,ȳ)` and `0 ∈ ∂_y[-l](x̄,ȳ)`. -/
theorem fenchel_lagrangian_optimality (hk : IsProper k) (hkl : LowerSemicontinuous k)
    (hkc : Convex ℝ (epigraph k)) (hh : IsProper h) (hhl : LowerSemicontinuous h)
    (hhc : Convex ℝ (epigraph h)) (x₀ : E) (y₀ : P) :
    ((0 : E) ∈ subdifferential (fun x ↦ fenchelLagrangian k h A b c x y₀) x₀ ∧
        (0 : P) ∈ subdifferential (fun y ↦ -fenchelLagrangian k h A b c x₀ y) y₀) ↔
      (y₀ ∈ subdifferential h (b - A x₀) ∧ A.adjoint y₀ - c ∈ subdifferential k x₀) := by
  obtain ⟨hfp, hfl, hfc, hφ, hψ, -, -⟩ := fenchel_scheme_fits_duality A b c hk hkl hkc hh hhl hhc
  have hf := isDualizingParameterization_of_convex hfp hfl hfc
  have hl := fun y ↦ convex_epigraph_lagrangian_of_convex hfc y
  rw [← lagrangian_fenchelIntegrand A b c (fun x ↦ (hk.2 x).ne') (fun w ↦ (hh.2 w).ne'),
    ← (hf.mem_argminimax_iff_subgradient_condition hl x₀ y₀).1, ← (hf.minimax_relations x₀ y₀).1,
    ← (fenchel_optimality A b c hk hkl hkc hh hhl hhc x₀ y₀).1, hφ, hψ]

end General

section ELQP

section Quadratic
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `j_C(x) = ½⟨x,Cx⟩`. -/
def halfQuadratic (C : F →L[ℝ] F) (x : F) : ℝ := 1 / 2 * ⟪x, C x⟫_ℝ

/-- `δ_X + j_C`, the function `k` of 11.43. -/
def indicatorQuadratic (X : Set F) (C : F →L[ℝ] F) (x : F) : EReal :=
  indicatorVA X x + (halfQuadratic C x : EReal)

/-- `θ_{Y,B}(u) = sup_{y ∈ Y} {⟨y,u⟩ - ½⟨y,By⟩}` as in 11.18 and 11.43. -/
def quadraticSupport (Y : Set F) (B : F →L[ℝ] F) (u : F) : EReal :=
  ⨆ y ∈ Y, ((⟪y, u⟫_ℝ - halfQuadratic B y : ℝ) : EReal)

variable {C : F →L[ℝ] F}

omit [FiniteDimensional ℝ F] in
theorem convexOn_halfQuadratic (hCs : ∀ x z, ⟪C x, z⟫_ℝ = ⟪x, C z⟫_ℝ)
    (hCp : ∀ x, 0 ≤ ⟪x, C x⟫_ℝ) : ConvexOn ℝ univ (halfQuadratic C) := by
  refine ⟨convex_univ, fun x _ z _ t s ht hs hts ↦ ?_⟩
  have hsym : ⟪z, C x⟫_ℝ = ⟪x, C z⟫_ℝ := by rw [← hCs, real_inner_comm]
  have hq := hCp (x - z)
  simp only [map_sub, inner_sub_left, inner_sub_right, hsym] at hq
  simp only [halfQuadratic, smul_eq_mul, map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real, hsym]
  have hst : s = 1 - t := by linarith
  subst hst
  nlinarith [mul_nonneg ht hs]

omit [FiniteDimensional ℝ F] in
theorem contDiff_halfQuadratic : ContDiff ℝ 1 (halfQuadratic C) :=
  contDiff_const.mul ((contDiff_inner (𝕜 := ℝ)).comp (contDiff_id.prodMk C.contDiff))

theorem hasGradientAt_halfQuadratic (hCs : ∀ x z, ⟪C x, z⟫_ℝ = ⟪x, C z⟫_ℝ) (x : F) :
    HasGradientAt (halfQuadratic C) (C x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := ((hasFDerivAt_id x).inner ℝ C.hasFDerivAt).const_mul (1 / 2 : ℝ)
  refine hd.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, id_eq, ContinuousLinearMap.coe_id',
    InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  rw [real_inner_comm (C v) x, hCs v x, real_inner_comm v (C x)]
  ring

omit [FiniteDimensional ℝ F] in
theorem isProper_indicatorQuadratic {X : Set F} (hX : X.Nonempty) :
    IsProper (indicatorQuadratic X C) := by
  obtain ⟨x, hx⟩ := hX
  refine ⟨⟨x, by simp [indicatorQuadratic, indicatorVA, hx]⟩, fun z ↦ ?_⟩
  unfold indicatorQuadratic indicatorVA
  split_ifs <;> simp

omit [FiniteDimensional ℝ F] in
theorem lowerSemicontinuous_indicatorQuadratic {X : Set F} (hX : IsClosed X) :
    LowerSemicontinuous (indicatorQuadratic X C) :=
  lowerSemicontinuous_add_coe (lowerSemicontinuous_indicatorVA hX)
    contDiff_halfQuadratic.continuous

theorem convex_epigraph_indicatorQuadratic {X : Set F} (hX : Convex ℝ X)
    (hCs : ∀ x z, ⟪C x, z⟫_ℝ = ⟪x, C z⟫_ℝ) (hCp : ∀ x, 0 ≤ ⟪x, C x⟫_ℝ) :
    Convex ℝ (epigraph (indicatorQuadratic X C)) := by
  have hi : Convex ℝ (epigraph (indicatorVA X)) := by
    rw [epigraph_indicatorVA]
    exact hX.prod (convex_Ici _)
  have hq : Convex ℝ (epigraph (fun x : F ↦ (halfQuadratic C x : EReal))) := by
    have he : epigraph (fun x : F ↦ (halfQuadratic C x : EReal)) =
        {p : F × ℝ | p.1 ∈ univ ∧ halfQuadratic C p.1 ≤ p.2} := by
      ext p
      simp [epigraph]
    rw [he]
    exact (convexOn_halfQuadratic hCs hCp).convex_epigraph
  exact convex_epigraph_add_of_ne_bot hi hq
    (fun x ↦ by unfold indicatorVA; split_ifs <;> simp) (fun _ ↦ EReal.coe_ne_bot _)

/-- Subgradients of `δ_X + j_C` (8.8(c) with 8.14). -/
theorem mem_subdifferential_indicatorQuadratic {X : Set F}
    (hCs : ∀ x z, ⟪C x, z⟫_ℝ = ⟪x, C z⟫_ℝ) (x v : F) :
    v ∈ subdifferential (indicatorQuadratic X C) x ↔ v - C x ∈ normalCone X x := by
  by_cases hx : x ∈ X
  · have hval : indicatorVA X x = ((0 : ℝ) : EReal) := by simp [indicatorVA, hx]
    have hs := (subdifferentials_add_smooth hval (contDiff_halfQuadratic (C := C)).contDiffAt).2.1
    change v ∈ subdifferential (fun z ↦ indicatorVA X z + (halfQuadratic C z : EReal)) x ↔ _
    rw [hs, subdifferential_indicatorVA, (hasGradientAt_halfQuadratic hCs x).gradient]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro hv
      exact ⟨v - C x, hv, by abel⟩
  · rw [normalCone_eq_empty hx]
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨⟨a, ha⟩, -⟩
    simp [indicatorQuadratic, indicatorVA, hx] at ha

omit [FiniteDimensional ℝ F] in
/-- `θ_{Y,B} = (δ_Y + j_B)*`, as in 11.18. -/
theorem quadraticSupport_eq_fenchelConjugate (Y : Set F) :
    quadraticSupport Y C = fenchelConjugate (indicatorQuadratic Y C) := by
  funext u
  unfold quadraticSupport fenchelConjugate
  refine iSup_congr fun y ↦ ?_
  by_cases hy : y ∈ Y
  · rw [iSup_pos hy]
    simp only [indicatorQuadratic, indicatorVA, hy, if_true, zero_add, ← EReal.coe_sub,
      real_inner_comm u y]
  · rw [iSup_neg hy]
    simp [indicatorQuadratic, indicatorVA, hy]

end Quadratic

/-- The extended linear-quadratic kernel
`L(x,y) = ⟨c,x⟩ + ½⟨x,Cx⟩ + ⟨b,y⟩ - ½⟨y,By⟩ - ⟨y,Ax⟩` of **11.47**. -/
def elqpKernel (C : E →L[ℝ] E) (B : P →L[ℝ] P) (A : E →L[ℝ] P) (b : P) (c : E) (x : E) (y : P) :
    ℝ :=
  ⟪c, x⟫_ℝ + halfQuadratic C x + ⟪b, y⟫_ℝ - halfQuadratic B y - ⟪y, A x⟫_ℝ

open Classical in
/-- `l = δ_X + L - δ_Y` with `∞ - ∞ = ∞`. -/
def elqpLagrangian (X : Set E) (Y : Set P) (C : E →L[ℝ] E) (B : P →L[ℝ] P) (A : E →L[ℝ] P)
    (b : P) (c : E) (x : E) (y : P) : EReal :=
  if x ∈ X then (if y ∈ Y then (elqpKernel C B A b c x y : EReal) else ⊥) else ⊤

variable {X : Set E} {Y : Set P} {C : E →L[ℝ] E} {B : P →L[ℝ] P} (A : E →L[ℝ] P) (b : P) (c : E)

omit [FiniteDimensional ℝ E] in
/-- The extended linear-quadratic Lagrangian in **11.47**: `l = δ_X + L - δ_Y`. -/
theorem fenchelLagrangian_elqp (hYn : Y.Nonempty) (hYc : IsClosed Y) (hYcv : Convex ℝ Y)
    (hBs : ∀ y z, ⟪B y, z⟫_ℝ = ⟪y, B z⟫_ℝ) (hBp : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ) :
    fenchelLagrangian (indicatorQuadratic X C) (quadraticSupport Y B) A b c =
      elqpLagrangian X Y C B A b c := by
  have hθ : fenchelConjugate (quadraticSupport Y B) = indicatorQuadratic Y B := by
    rw [quadraticSupport_eq_fenchelConjugate]
    exact fenchelConjugate_fenchelConjugate_eq (isProper_indicatorQuadratic hYn)
      (lowerSemicontinuous_indicatorQuadratic hYc)
      (convex_epigraph_indicatorQuadratic hYcv hBs hBp)
  funext x y
  unfold fenchelLagrangian elqpLagrangian
  rw [hθ]
  by_cases hx : x ∈ X
  · have hkx : indicatorQuadratic X C x = (halfQuadratic C x : EReal) := by
      simp [indicatorQuadratic, indicatorVA, hx]
    rw [if_neg (by rw [hkx]; exact EReal.coe_ne_top _), if_pos hx, hkx]
    by_cases hy : y ∈ Y
    · rw [if_pos hy]
      simp only [indicatorQuadratic, indicatorVA, hy, if_true, zero_add, elqpKernel]
      norm_cast
    · rw [if_neg hy]
      simp [indicatorQuadratic, indicatorVA, hy]
  · rw [if_pos (by simp [indicatorQuadratic, indicatorVA, hx]), if_neg hx]

theorem hasGradientAt_elqpKernel_fst (hCs : ∀ x z, ⟪C x, z⟫_ℝ = ⟪x, C z⟫_ℝ) (x₀ : E) (y₀ : P) :
    HasGradientAt (fun x ↦ elqpKernel C B A b c x y₀) (c + C x₀ - A.adjoint y₀) x₀ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h₁ : HasFDerivAt (fun x : E ↦ ⟪c, x⟫_ℝ) (innerSL ℝ c) x₀ := (innerSL ℝ c).hasFDerivAt
  have h₂ := (hasGradientAt_halfQuadratic hCs x₀).hasFDerivAt
  have h₃ : HasFDerivAt (fun x : E ↦ ⟪y₀, A x⟫_ℝ) (innerSL ℝ (A.adjoint y₀)) x₀ := by
    have he : (fun x : E ↦ ⟪y₀, A x⟫_ℝ) = fun x ↦ innerSL ℝ (A.adjoint y₀) x := by
      funext x
      rw [innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left]
    rw [he]
    exact (innerSL ℝ (A.adjoint y₀)).hasFDerivAt
  have hsum := (((h₁.add h₂).add_const (⟪b, y₀⟫_ℝ)).sub_const (halfQuadratic B y₀)).sub h₃
  refine hsum.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, innerSL_apply_apply,
    InnerProductSpace.toDual_apply_apply, inner_add_left, inner_sub_left]

omit [FiniteDimensional ℝ E] in
theorem hasGradientAt_elqpKernel_snd (hBs : ∀ y z, ⟪B y, z⟫_ℝ = ⟪y, B z⟫_ℝ) (x₀ : E) (y₀ : P) :
    HasGradientAt (fun y ↦ elqpKernel C B A b c x₀ y) (b - B y₀ - A x₀) y₀ := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h₁ : HasFDerivAt (fun y : P ↦ ⟪b, y⟫_ℝ) (innerSL ℝ b) y₀ := (innerSL ℝ b).hasFDerivAt
  have h₂ := (hasGradientAt_halfQuadratic hBs y₀).hasFDerivAt
  have h₃ : HasFDerivAt (fun y : P ↦ ⟪y, A x₀⟫_ℝ) (innerSL ℝ (A x₀)) y₀ := by
    have he : (fun y : P ↦ ⟪y, A x₀⟫_ℝ) = fun y ↦ innerSL ℝ (A x₀) y := by
      funext y
      rw [innerSL_apply_apply, real_inner_comm]
    rw [he]
    exact (innerSL ℝ (A x₀)).hasFDerivAt
  have hsum := ((h₁.const_add (⟪c, x₀⟫_ℝ + halfQuadratic C x₀)).sub h₂).sub h₃
  refine hsum.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.sub_apply, innerSL_apply_apply,
    InnerProductSpace.toDual_apply_apply, inner_sub_left]

/-- **Example 11.47**, extended linear-quadratic programming: the Lagrangian is
`δ_X + L - δ_Y`, and the Lagrangian optimality conditions are
`-∇ₓL(x̄,ȳ) ∈ N_X(x̄)`, `∇_yL(x̄,ȳ) ∈ N_Y(ȳ)`, that is,
`-c - Cx̄ + A*ȳ ∈ N_X(x̄)` and `b - Ax̄ - Bȳ ∈ N_Y(ȳ)`. -/
theorem elqp_lagrangian_optimality (hXn : X.Nonempty) (hXc : IsClosed X) (hXcv : Convex ℝ X)
    (hYn : Y.Nonempty) (hYc : IsClosed Y) (hYcv : Convex ℝ Y)
    (hCs : ∀ x z, ⟪C x, z⟫_ℝ = ⟪x, C z⟫_ℝ) (hCp : ∀ x, 0 ≤ ⟪x, C x⟫_ℝ)
    (hBs : ∀ y z, ⟪B y, z⟫_ℝ = ⟪y, B z⟫_ℝ) (hBp : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ) (x₀ : E) (y₀ : P) :
    lagrangian (fenchelIntegrand (indicatorQuadratic X C) (quadraticSupport Y B) A b c) =
        elqpLagrangian X Y C B A b c ∧
    (((0 : E) ∈ subdifferential (fun x ↦ elqpLagrangian X Y C B A b c x y₀) x₀ ∧
        (0 : P) ∈ subdifferential (fun y ↦ -elqpLagrangian X Y C B A b c x₀ y) y₀) ↔
      (-gradient (fun x ↦ elqpKernel C B A b c x y₀) x₀ ∈ normalCone X x₀ ∧
        gradient (fun y ↦ elqpKernel C B A b c x₀ y) y₀ ∈ normalCone Y y₀)) ∧
    ((-gradient (fun x ↦ elqpKernel C B A b c x y₀) x₀ ∈ normalCone X x₀ ∧
        gradient (fun y ↦ elqpKernel C B A b c x₀ y) y₀ ∈ normalCone Y y₀) ↔
      (-c - C x₀ + A.adjoint y₀ ∈ normalCone X x₀ ∧ b - A x₀ - B y₀ ∈ normalCone Y y₀)) := by
  have hkp : IsProper (indicatorQuadratic X C) := isProper_indicatorQuadratic hXn
  have hkl : LowerSemicontinuous (indicatorQuadratic X C) :=
    lowerSemicontinuous_indicatorQuadratic hXc
  have hkc := convex_epigraph_indicatorQuadratic hXcv hCs hCp
  have hjp : IsProper (indicatorQuadratic Y B) := isProper_indicatorQuadratic hYn
  have hjl : LowerSemicontinuous (indicatorQuadratic Y B) :=
    lowerSemicontinuous_indicatorQuadratic hYc
  have hjc := convex_epigraph_indicatorQuadratic hYcv hBs hBp
  have hθ : quadraticSupport Y B = fenchelConjugate (indicatorQuadratic Y B) :=
    quadraticSupport_eq_fenchelConjugate Y
  have hθp : IsProper (quadraticSupport Y B) := hθ ▸ isProper_fenchelConjugate hjp hjl hjc
  have hθl : LowerSemicontinuous (quadraticSupport Y B) :=
    hθ ▸ lowerSemicontinuous_fenchelConjugate _
  have hθc : Convex ℝ (epigraph (quadraticSupport Y B)) :=
    hθ ▸ convex_epigraph_fenchelConjugate _
  have hθθ : fenchelConjugate (quadraticSupport Y B) = indicatorQuadratic Y B := by
    rw [hθ]
    exact fenchelConjugate_fenchelConjugate_eq hjp hjl hjc
  have hgx : gradient (fun x ↦ elqpKernel C B A b c x y₀) x₀ = c + C x₀ - A.adjoint y₀ :=
    (hasGradientAt_elqpKernel_fst A b c hCs x₀ y₀).gradient
  have hgy : gradient (fun y ↦ elqpKernel C B A b c x₀ y) y₀ = b - B y₀ - A x₀ :=
    (hasGradientAt_elqpKernel_snd A b c hBs x₀ y₀).gradient
  have hlag := fenchelLagrangian_elqp (X := X) (C := C) A b c hYn hYc hYcv hBs hBp
  refine ⟨(lagrangian_fenchelIntegrand A b c (fun x ↦ (hkp.2 x).ne')
    (fun w ↦ (hθp.2 w).ne')).trans hlag, ?_, ?_⟩
  · rw [← hlag, fenchel_lagrangian_optimality A b c hkp hkl hkc hθp hθl hθc x₀ y₀,
      ← mem_subdifferential_fenchelConjugate_iff hθp hθl hθc, hθθ,
      mem_subdifferential_indicatorQuadratic hBs, mem_subdifferential_indicatorQuadratic hCs,
      hgx, hgy, and_comm]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨by convert h₁ using 1; abel, by convert h₂ using 1; abel⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨by convert h₁ using 1; abel, by convert h₂ using 1; abel⟩
  · rw [hgx, hgy]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨by convert h₁ using 1; abel, by convert h₂ using 1; abel⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨by convert h₁ using 1; abel, by convert h₂ using 1; abel⟩

end ELQP

end
end RW
