/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Perturbations in extended linear-quadratic programming

Example 11.54.
-/
import RockafellarWets.Chapter11.SaddlePerturbation
import RockafellarWets.Chapter11.FenchelLagrangians

open Set Filter Topology Bornology Metric Classical
open scoped InnerProductSpace
namespace RW
noncomputable section

theorem tendsto_clm_apply {α F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {l : Filter α} {f : α → F →L[ℝ] G} {g : α → F}
    {f₀ : F →L[ℝ] G} {g₀ : F} (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 g₀)) :
    Tendsto (fun a ↦ f a (g a)) l (𝓝 (f₀ g₀)) :=
  ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := F) (F := G)).continuous.tendsto (f₀, g₀)).comp
    (hf.prodMk_nhds hg)

theorem ereal_iInf_coe_sub {ι : Sort*} (r : ℝ) (g : ι → EReal) :
    (⨅ i, (r : EReal) - g i) = (r : EReal) - ⨆ i, g i := by
  simp only [sub_eq_add_neg]
  rw [← coe_add_iInf, ereal_iInf_neg]

theorem tendsto_slope_fst_of_hasDerivWithinAt {α G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {l : Filter α} {f : ℝ → G} {f₀ : G} (hf : HasDerivWithinAt f f₀ (Ici 0) 0) :
    Tendsto (fun p : ℝ × α ↦ slope f 0 p.1) (𝓝[>] 0 ×ˢ l) (𝓝 f₀) := by
  have h₁ := hasDerivWithinAt_iff_tendsto_slope.mp hf
  rw [Ici_diff_left] at h₁
  exact h₁.comp tendsto_fst

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

section Static
variable {X : Set E} {Y : Set P} {C : E →L[ℝ] E} {B : P →L[ℝ] P} {A : E →L[ℝ] P} {b : P} {c : E}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem elqpKernel_eq_primal_split (x : E) (y : P) :
    elqpKernel C B A b c x y = (⟪c, x⟫_ℝ + halfQuadratic C x) + (⟪y, b - A x⟫_ℝ - halfQuadratic B y) := by
  unfold elqpKernel
  rw [inner_sub_right]
  linarith [real_inner_comm b y]

theorem elqpKernel_eq_dual_split (x : E) (y : P) :
    elqpKernel C B A b c x y =
      (⟪b, y⟫_ℝ - halfQuadratic B y) - (⟪x, A.adjoint y - c⟫_ℝ - halfQuadratic C x) := by
  unfold elqpKernel
  rw [inner_sub_right]
  linarith [real_inner_comm x (A.adjoint y), ContinuousLinearMap.adjoint_inner_left A x y,
    real_inner_comm x c]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- The primal problem of the minimax formulation is the ELQP primal problem:
`⟨c,x⟩ + ½⟨x,Cx⟩ + θ_{Y,B}(b - Ax)` over `x ∈ X`. -/
theorem minimaxPrimal_elqpKernel (x : E) :
    minimaxPrimal (elqpKernel C B A b c) X Y x =
      if x ∈ X then ((⟪c, x⟫_ℝ + halfQuadratic C x : ℝ) : EReal) + quadraticSupport Y B (b - A x)
      else ⊤ := by
  unfold minimaxPrimal quadraticSupport
  split_ifs with hx
  · rw [ereal_add_iSup]
    refine iSup_congr fun y ↦ ?_
    rw [ereal_add_iSup]
    refine iSup_congr fun _ ↦ ?_
    rw [elqpKernel_eq_primal_split, EReal.coe_add]
  · rfl

/-- The dual problem of the minimax formulation is the ELQP dual problem:
`⟨b,y⟩ - ½⟨y,By⟩ - θ_{X,C}(A*y - c)` over `y ∈ Y`. -/
theorem minimaxDual_elqpKernel (y : P) :
    minimaxDual (elqpKernel C B A b c) X Y y =
      if y ∈ Y then ((⟪b, y⟫_ℝ - halfQuadratic B y : ℝ) : EReal) -
        quadraticSupport X C (A.adjoint y - c) else ⊥ := by
  unfold minimaxDual quadraticSupport
  split_ifs with hy
  · rw [← ereal_iInf_coe_sub]
    refine iInf_congr fun x ↦ ?_
    rw [← ereal_iInf_coe_sub]
    refine iInf_congr fun _ ↦ ?_
    rw [elqpKernel_eq_dual_split, EReal.coe_sub]
  · rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- The ELQP primal problem in the Fenchel form of **11.43** coincides with the
minimax primal problem of the kernel. -/
theorem fenchelPrimal_elqp_eq_minimaxPrimal (hYn : Y.Nonempty) :
    fenchelPrimal (indicatorQuadratic X C) (quadraticSupport Y B) A b c =
      minimaxPrimal (elqpKernel C B A b c) X Y := by
  funext x
  rw [minimaxPrimal_elqpKernel]
  obtain ⟨y₀, hy₀⟩ := hYn
  have hθb : quadraticSupport Y B (b - A x) ≠ ⊥ :=
    ((EReal.bot_lt_coe _).trans_le (le_iSup₂_of_le y₀ hy₀ le_rfl)).ne'
  unfold fenchelPrimal indicatorQuadratic indicatorVA
  split_ifs with hx
  · rw [zero_add, ← EReal.coe_add]
  · rw [EReal.top_add_coe, EReal.coe_add_top, EReal.top_add_of_ne_bot hθb]

/-- The ELQP dual problem in the Fenchel form of **11.43** coincides with the
minimax dual problem of the kernel. -/
theorem fenchelDual_elqp_eq_minimaxDual (hXn : X.Nonempty) (hYn : Y.Nonempty) (hYc : IsClosed Y)
    (hYv : Convex ℝ Y) (hBs : ∀ y z, ⟪B y, z⟫_ℝ = ⟪y, B z⟫_ℝ) (hBp : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ) :
    fenchelDual (indicatorQuadratic X C) (quadraticSupport Y B) A b c =
      minimaxDual (elqpKernel C B A b c) X Y := by
  have hθθ : fenchelConjugate (quadraticSupport Y B) = indicatorQuadratic Y B := by
    rw [quadraticSupport_eq_fenchelConjugate]
    exact fenchelConjugate_fenchelConjugate_eq (isProper_indicatorQuadratic hYn)
      (lowerSemicontinuous_indicatorQuadratic hYc) (convex_epigraph_indicatorQuadratic hYv hBs hBp)
  have hk : fenchelConjugate (indicatorQuadratic X C) = quadraticSupport X C :=
    (quadraticSupport_eq_fenchelConjugate X).symm
  funext y
  rw [minimaxDual_elqpKernel]
  unfold fenchelDual
  rw [hθθ, hk]
  obtain ⟨x₀, hx₀⟩ := hXn
  have hθb : quadraticSupport X C (A.adjoint y - c) ≠ ⊥ :=
    ((EReal.bot_lt_coe _).trans_le (le_iSup₂_of_le x₀ hx₀ le_rfl)).ne'
  unfold indicatorQuadratic indicatorVA
  split_ifs with hy
  · rw [zero_add, ← EReal.coe_sub]
  · rw [EReal.top_add_coe, EReal.sub_top, EReal.bot_sub]

end Static

section Perturbation
variable {T : ℝ} {X : Set E} {Y : Set P} {c : ℝ → E} {C : ℝ → E →L[ℝ] E} {b : ℝ → P}
  {B : ℝ → P →L[ℝ] P} {A : ℝ → E →L[ℝ] P}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem continuousOn_elqpKernel {S : Set (ℝ × E × P)} (hS : ∀ p ∈ S, p.1 ∈ Icc 0 T)
    (hc : ContinuousOn c (Icc 0 T)) (hC : ContinuousOn C (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hB : ContinuousOn B (Icc 0 T)) (hA : ContinuousOn A (Icc 0 T)) :
    ContinuousOn (fun p : ℝ × E × P ↦
      elqpKernel (C p.1) (B p.1) (A p.1) (b p.1) (c p.1) p.2.1 p.2.2) S := by
  have ht : ContinuousOn (fun p : ℝ × E × P ↦ p.1) S := continuous_fst.continuousOn
  have hx : ContinuousOn (fun p : ℝ × E × P ↦ p.2.1) S := (continuous_fst.comp continuous_snd).continuousOn
  have hy : ContinuousOn (fun p : ℝ × E × P ↦ p.2.2) S := (continuous_snd.comp continuous_snd).continuousOn
  have hc' : ContinuousOn (fun p : ℝ × E × P ↦ c p.1) S := hc.comp ht hS
  have hC' : ContinuousOn (fun p : ℝ × E × P ↦ C p.1) S := hC.comp ht hS
  have hb' : ContinuousOn (fun p : ℝ × E × P ↦ b p.1) S := hb.comp ht hS
  have hB' : ContinuousOn (fun p : ℝ × E × P ↦ B p.1) S := hB.comp ht hS
  have hA' : ContinuousOn (fun p : ℝ × E × P ↦ A p.1) S := hA.comp ht hS
  unfold elqpKernel halfQuadratic
  exact ((((hc'.inner hx).add (continuousOn_const.mul (hx.inner (hC'.clm_apply hx)))).add
    (hb'.inner hy)).sub (continuousOn_const.mul (hy.inner (hB'.clm_apply hy)))).sub
    (hy.inner (hA'.clm_apply hx))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem convexOn_elqpKernel (hXv : Convex ℝ X) {C₁ : E →L[ℝ] E} {B₁ : P →L[ℝ] P}
    {A₁ : E →L[ℝ] P} {b₁ : P} {c₁ : E} (hCs : ∀ x z, ⟪C₁ x, z⟫_ℝ = ⟪x, C₁ z⟫_ℝ)
    (hCp : ∀ x, 0 ≤ ⟪x, C₁ x⟫_ℝ) (y : P) : ConvexOn ℝ X (fun x ↦ elqpKernel C₁ B₁ A₁ b₁ c₁ x y) := by
  have hlin : ConvexOn ℝ X (fun x ↦ (innerSL ℝ c₁ - (innerSL ℝ y).comp A₁) x) :=
    (innerSL ℝ c₁ - (innerSL ℝ y).comp A₁).toLinearMap.convexOn hXv
  refine (((convexOn_halfQuadratic hCs hCp).subset (subset_univ X) hXv).add hlin).add_const
    (⟪b₁, y⟫_ℝ - halfQuadratic B₁ y) |>.congr fun x _ ↦ ?_
  simp only [elqpKernel, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Pi.add_apply]
  ring

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem concaveOn_elqpKernel (hYv : Convex ℝ Y) {C₁ : E →L[ℝ] E} {B₁ : P →L[ℝ] P}
    {A₁ : E →L[ℝ] P} {b₁ : P} {c₁ : E} (hBs : ∀ y z, ⟪B₁ y, z⟫_ℝ = ⟪y, B₁ z⟫_ℝ)
    (hBp : ∀ y, 0 ≤ ⟪y, B₁ y⟫_ℝ) (x : E) : ConcaveOn ℝ Y (fun y ↦ elqpKernel C₁ B₁ A₁ b₁ c₁ x y) := by
  have hlin : ConcaveOn ℝ Y (fun y ↦ (innerSL ℝ b₁ - innerSL ℝ (A₁ x)) y) :=
    (innerSL ℝ b₁ - innerSL ℝ (A₁ x)).toLinearMap.concaveOn hYv
  refine (((convexOn_halfQuadratic hBs hBp).subset (subset_univ Y) hYv).neg.add hlin).add_const
    (⟪c₁, x⟫_ℝ + halfQuadratic C₁ x) |>.congr fun y _ ↦ ?_
  simp only [elqpKernel, ContinuousLinearMap.sub_apply, innerSL_apply_apply, Pi.add_apply,
    Pi.neg_apply, real_inner_comm (A₁ x) y]
  ring

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- The hypotheses of **11.54** produce the setting of **11.53**. -/
theorem isSaddlePerturbation_elqp (hT : 0 < T) (hXn : X.Nonempty) (hXc : IsClosed X)
    (hXv : Convex ℝ X) (hYn : Y.Nonempty) (hYc : IsClosed Y) (hYv : Convex ℝ Y)
    (hCs : ∀ t ∈ Icc 0 T, ∀ x z, ⟪C t x, z⟫_ℝ = ⟪x, C t z⟫_ℝ)
    (hCp : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ ⟪x, C t x⟫_ℝ)
    (hBs : ∀ t ∈ Icc 0 T, ∀ y z, ⟪B t y, z⟫_ℝ = ⟪y, B t z⟫_ℝ)
    (hBp : ∀ t ∈ Icc 0 T, ∀ y, 0 ≤ ⟪y, B t y⟫_ℝ)
    (hc : ContinuousOn c (Icc 0 T)) (hC : ContinuousOn C (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hB : ContinuousOn B (Icc 0 T)) (hA : ContinuousOn A (Icc 0 T)) :
    IsSaddlePerturbation (fun t ↦ elqpKernel (C t) (B t) (A t) (b t) (c t)) T X Y :=
  ⟨hT, hXn, hXc, hXv, hYn, hYc, hYv,
    continuousOn_elqpKernel (fun _ hp ↦ hp.1) hc hC hb hB hA,
    fun t ht y _ ↦ convexOn_elqpKernel hXv (hCs t ht) (hCp t ht) y,
    fun t ht x _ ↦ concaveOn_elqpKernel hYv (hBs t ht) (hBp t ht) x⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- The difference quotient of the kernel is the kernel of the difference quotients. -/
theorem elqpKernel_slope {t : ℝ} (ht : t ≠ 0) (x : E) (y : P) :
    (elqpKernel (C t) (B t) (A t) (b t) (c t) x y - elqpKernel (C 0) (B 0) (A 0) (b 0) (c 0) x y) / t =
      elqpKernel (slope C 0 t) (slope B 0 t) (slope A 0 t) (slope b 0 t) (slope c 0 t) x y := by
  simp only [slope_def_module, sub_zero, elqpKernel, halfQuadratic,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, RCLike.conj_to_real]
  field_simp
  ring

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- With right derivatives of the data, the joint limit `L₊(0,x,y)` of **11.53**
exists and is the kernel of the derivative data. -/
theorem tendsto_elqpKernel_slope {c₀ : E} {C₀ : E →L[ℝ] E} {b₀ : P} {B₀ : P →L[ℝ] P}
    {A₀ : E →L[ℝ] P} (hc : HasDerivWithinAt c c₀ (Ici 0) 0) (hC : HasDerivWithinAt C C₀ (Ici 0) 0)
    (hb : HasDerivWithinAt b b₀ (Ici 0) 0) (hB : HasDerivWithinAt B B₀ (Ici 0) 0)
    (hA : HasDerivWithinAt A A₀ (Ici 0) 0) (x : E) (y : P) :
    Tendsto (fun p : ℝ × (E × P) ↦ (elqpKernel (C p.1) (B p.1) (A p.1) (b p.1) (c p.1) p.2.1 p.2.2 -
        elqpKernel (C 0) (B 0) (A 0) (b 0) (c 0) p.2.1 p.2.2) / p.1)
      (𝓝[>] 0 ×ˢ 𝓝[X ×ˢ Y] (x, y)) (𝓝 (elqpKernel C₀ B₀ A₀ b₀ c₀ x y)) := by
  have hxy : Tendsto (fun p : ℝ × (E × P) ↦ p.2) (𝓝[>] 0 ×ˢ 𝓝[X ×ˢ Y] (x, y)) (𝓝 (x, y)) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  have hx : Tendsto (fun p : ℝ × (E × P) ↦ p.2.1) (𝓝[>] 0 ×ˢ 𝓝[X ×ˢ Y] (x, y)) (𝓝 x) :=
    (continuous_fst.tendsto _).comp hxy
  have hy : Tendsto (fun p : ℝ × (E × P) ↦ p.2.2) (𝓝[>] 0 ×ˢ 𝓝[X ×ˢ Y] (x, y)) (𝓝 y) :=
    (continuous_snd.tendsto _).comp hxy
  have hlim : Tendsto (fun p : ℝ × (E × P) ↦ elqpKernel (slope C 0 p.1) (slope B 0 p.1)
      (slope A 0 p.1) (slope b 0 p.1) (slope c 0 p.1) p.2.1 p.2.2)
      (𝓝[>] 0 ×ˢ 𝓝[X ×ˢ Y] (x, y)) (𝓝 (elqpKernel C₀ B₀ A₀ b₀ c₀ x y)) := by
    have h₁ := tendsto_slope_fst_of_hasDerivWithinAt (l := 𝓝[X ×ˢ Y] (x, y)) hc
    have h₂ := tendsto_slope_fst_of_hasDerivWithinAt (l := 𝓝[X ×ˢ Y] (x, y)) hC
    have h₃ := tendsto_slope_fst_of_hasDerivWithinAt (l := 𝓝[X ×ˢ Y] (x, y)) hb
    have h₄ := tendsto_slope_fst_of_hasDerivWithinAt (l := 𝓝[X ×ˢ Y] (x, y)) hB
    have h₅ := tendsto_slope_fst_of_hasDerivWithinAt (l := 𝓝[X ×ˢ Y] (x, y)) hA
    have hhalf : Tendsto (fun _ : ℝ × (E × P) ↦ (1 / 2 : ℝ)) (𝓝[>] 0 ×ˢ 𝓝[X ×ˢ Y] (x, y))
        (𝓝 (1 / 2)) := tendsto_const_nhds
    have t₁ := h₁.inner (𝕜 := ℝ) hx
    have t₂ := hhalf.mul (hx.inner (𝕜 := ℝ) (tendsto_clm_apply h₂ hx))
    have t₃ := h₃.inner (𝕜 := ℝ) hy
    have t₄ := hhalf.mul (hy.inner (𝕜 := ℝ) (tendsto_clm_apply h₄ hy))
    have t₅ := hy.inner (𝕜 := ℝ) (tendsto_clm_apply h₅ hx)
    unfold elqpKernel halfQuadratic
    exact (((t₁.add t₂).add t₃).sub t₄).sub t₅
  refine hlim.congr' ?_
  have hpos : ∀ᶠ p : ℝ × (E × P) in 𝓝[>] 0 ×ˢ 𝓝[X ×ˢ Y] (x, y), p.1 ≠ 0 :=
    (tendsto_fst.eventually self_mem_nhdsWithin).mono fun p hp ↦ (ne_of_gt hp)
  filter_upwards [hpos] with p hp
  exact (elqpKernel_slope hp p.2.1 p.2.2).symm

/-- The optimal solution sets `X_t` of the ELQP primal problems of **11.54**. -/
def elqpPrimalSolutions (X : Set E) (Y : Set P) (C : ℝ → E →L[ℝ] E) (B : ℝ → P →L[ℝ] P)
    (A : ℝ → E →L[ℝ] P) (b : ℝ → P) (c : ℝ → E) (t : ℝ) : Set E :=
  argmin (fenchelPrimal (indicatorQuadratic X (C t)) (quadraticSupport Y (B t)) (A t) (b t) (c t))

/-- The optimal solution sets `Y_t` of the ELQP dual problems of **11.54**. -/
def elqpDualSolutions (X : Set E) (Y : Set P) (C : ℝ → E →L[ℝ] E) (B : ℝ → P →L[ℝ] P)
    (A : ℝ → E →L[ℝ] P) (b : ℝ → P) (c : ℝ → E) (t : ℝ) : Set P :=
  argmax (fenchelDual (indicatorQuadratic X (C t)) (quadraticSupport Y (B t)) (A t) (b t) (c t))

/-- **Example 11.54** (perturbations in extended linear-quadratic programming). For
nonempty closed convex `X`, `Y` (in particular polyhedral sets) and symmetric
positive-semidefinite `C(t)`, `B(t)`, with data continuous on `[0,T]` and nonempty
bounded optimal sets `X₀`, `Y₀`: on some `[0,ε]` the mappings `t ↦ X_t` and `t ↦ Y_t`
are nonempty-valued and osc and locally bounded at `0`, the common optimal value
`λ(t)` is continuous at `0`, and when the data have right derivatives at `0`,
`λ₊(0)` exists and is the common optimal value of the derivative problems over
`X₀` and `Y₀`. -/
theorem elqp_perturbation (hT : 0 < T) (hXn : X.Nonempty) (hXc : IsClosed X) (hXv : Convex ℝ X)
    (hYn : Y.Nonempty) (hYc : IsClosed Y) (hYv : Convex ℝ Y)
    (hCs : ∀ t ∈ Icc 0 T, ∀ x z, ⟪C t x, z⟫_ℝ = ⟪x, C t z⟫_ℝ)
    (hCp : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ ⟪x, C t x⟫_ℝ)
    (hBs : ∀ t ∈ Icc 0 T, ∀ y z, ⟪B t y, z⟫_ℝ = ⟪y, B t z⟫_ℝ)
    (hBp : ∀ t ∈ Icc 0 T, ∀ y, 0 ≤ ⟪y, B t y⟫_ℝ)
    (hc : ContinuousOn c (Icc 0 T)) (hC : ContinuousOn C (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hB : ContinuousOn B (Icc 0 T)) (hA : ContinuousOn A (Icc 0 T))
    (hX0 : (elqpPrimalSolutions X Y C B A b c 0).Nonempty)
    (hX0b : IsBounded (elqpPrimalSolutions X Y C B A b c 0))
    (hY0 : (elqpDualSolutions X Y C B A b c 0).Nonempty)
    (hY0b : IsBounded (elqpDualSolutions X Y C B A b c 0)) :
    let L := fun t ↦ elqpKernel (C t) (B t) (A t) (b t) (c t)
    ∃ ε > 0, ε ≤ T ∧
      (∀ t ∈ Icc 0 ε, (elqpPrimalSolutions X Y C B A b c t).Nonempty ∧
        (elqpDualSolutions X Y C B A b c t).Nonempty ∧
        (⨅ x, fenchelPrimal (indicatorQuadratic X (C t)) (quadraticSupport Y (B t)) (A t) (b t)
          (c t) x) = (saddleValue L X Y t : EReal) ∧
        (⨆ y, fenchelDual (indicatorQuadratic X (C t)) (quadraticSupport Y (B t)) (A t) (b t)
          (c t) y) = (saddleValue L X Y t : EReal)) ∧
      SvOscWithinAt (elqpPrimalSolutions X Y C B A b c) (Icc 0 ε) 0 ∧
      SvLocallyBoundedWithinAt (elqpPrimalSolutions X Y C B A b c) (Icc 0 ε) 0 ∧
      SvOscWithinAt (elqpDualSolutions X Y C B A b c) (Icc 0 ε) 0 ∧
      SvLocallyBoundedWithinAt (elqpDualSolutions X Y C B A b c) (Icc 0 ε) 0 ∧
      Tendsto (saddleValue L X Y) (𝓝[Icc 0 ε] 0) (𝓝 (saddleValue L X Y 0)) ∧
      ∀ (c₀ : E) (C₀ : E →L[ℝ] E) (b₀ : P) (B₀ : P →L[ℝ] P) (A₀ : E →L[ℝ] P),
        HasDerivWithinAt c c₀ (Ici 0) 0 → HasDerivWithinAt C C₀ (Ici 0) 0 →
        HasDerivWithinAt b b₀ (Ici 0) 0 → HasDerivWithinAt B B₀ (Ici 0) 0 →
        HasDerivWithinAt A A₀ (Ici 0) 0 →
        ∃ μ : ℝ, Tendsto (fun t ↦ (saddleValue L X Y t - saddleValue L X Y 0) / t) (𝓝[>] 0)
            (𝓝 μ) ∧
          (⨅ x ∈ elqpPrimalSolutions X Y C B A b c 0,
            ((⟪c₀, x⟫_ℝ + halfQuadratic C₀ x : ℝ) : EReal) +
              quadraticSupport (elqpDualSolutions X Y C B A b c 0) B₀ (b₀ - A₀ x)) = (μ : EReal) ∧
          (⨆ y ∈ elqpDualSolutions X Y C B A b c 0,
            ((⟪b₀, y⟫_ℝ - halfQuadratic B₀ y : ℝ) : EReal) -
              quadraticSupport (elqpPrimalSolutions X Y C B A b c 0) C₀ (A₀.adjoint y - c₀)) =
            (μ : EReal) := by
  intro L
  have h := isSaddlePerturbation_elqp hT hXn hXc hXv hYn hYc hYv hCs hCp hBs hBp hc hC hb hB hA
  have hTm {t : ℝ} (ht : t ∈ Icc 0 T) := h.minimax ht
  have hprim {t : ℝ} (ht : t ∈ Icc 0 T) : elqpPrimalSolutions X Y C B A b c t =
      argmin (minimaxPrimal (L t) X Y) := by
    unfold elqpPrimalSolutions
    rw [fenchelPrimal_elqp_eq_minimaxPrimal hYn]
  have hdual {t : ℝ} (ht : t ∈ Icc 0 T) : elqpDualSolutions X Y C B A b c t =
      argmax (minimaxDual (L t) X Y) := by
    unfold elqpDualSolutions
    rw [fenchelDual_elqp_eq_minimaxDual hXn hYn hYc hYv (hBs t ht) (hBp t ht)]
  have h0m : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hS0 := ((hTm h0m).argminimaxOn_nonempty_bounded_iff.1).mpr
    ⟨⟨hprim h0m ▸ hX0, hprim h0m ▸ hX0b⟩, ⟨hdual h0m ▸ hY0, hdual h0m ▸ hY0b⟩⟩
  obtain ⟨ε, hε, hεT, hne, hosc, hlb, hlim⟩ := h.golshtein_saddle_sets hS0.1 hS0.2
  have hεT' {t : ℝ} (ht : t ∈ Icc 0 ε) : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hεT⟩
  have hprod {t : ℝ} (ht : t ∈ Icc 0 ε) : argminimaxOn (L t) X Y =
      elqpPrimalSolutions X Y C B A b c t ×ˢ elqpDualSolutions X Y C B A b c t := by
    rw [hprim (hεT' ht), hdual (hεT' ht)]
    exact (hTm (hεT' ht)).argminimaxOn_eq_prod
      ((hTm (hεT' ht)).iInf_eq_iSup_of_nonempty (hne t ht).1)
  have hfac {t : ℝ} (ht : t ∈ Icc 0 ε) : (elqpPrimalSolutions X Y C B A b c t).Nonempty ∧
      (elqpDualSolutions X Y C B A b c t).Nonempty := by
    obtain ⟨p, hp⟩ := (hne t ht).1
    rw [hprod ht] at hp
    exact ⟨⟨_, hp.1⟩, ⟨_, hp.2⟩⟩
  obtain ⟨V, hV, hVb⟩ := hlb
  have hbd {t : ℝ} (ht : t ∈ Icc 0 ε ∩ V) {p : E × P} (hp : p ∈ argminimaxOn (L t) X Y) :
      p ∈ svImage (fun t ↦ argminimaxOn (L t) X Y) (Icc 0 ε ∩ V) :=
    mem_svImage.mpr ⟨t, ht, hp⟩
  refine ⟨ε, hε, hεT, fun t ht ↦ ⟨(hfac ht).1, (hfac ht).2, ?_, ?_⟩, ?_, ?_, ?_, ?_, hlim, ?_⟩
  · obtain ⟨p, hp⟩ := (hne t ht).1
    rw [fenchelPrimal_elqp_eq_minimaxPrimal hYn]
    rw [← h.apply_eq_saddleValue (hεT' ht) hp]
    exact ((hTm (hεT' ht)).saddle_value hp).1.symm
  · obtain ⟨p, hp⟩ := (hne t ht).1
    rw [fenchelDual_elqp_eq_minimaxDual hXn hYn hYc hYv (hBs t (hεT' ht)) (hBp t (hεT' ht))]
    rw [← h.apply_eq_saddleValue (hεT' ht) hp]
    exact ((hTm (hεT' ht)).saddle_value hp).2.symm
  · -- osc of `t ↦ X_t`
    intro x hx
    rw [svOuterLimitWithin, mem_outerSetLimitAlong_iff_exists_seq] at hx
    obtain ⟨ts, xs, hts, hxs, hxlim⟩ := hx
    have hts' := tendsto_nhdsWithin_iff.mp hts
    have hev : ∀ᶠ n in atTop, ts n ∈ Icc 0 ε ∩ V :=
      (hts'.2.and (hts'.1.eventually hV)).mono fun n hn ↦ hn
    let ys : ℕ → P := fun n ↦ if hn : ts n ∈ Icc 0 ε then (hfac hn).2.some else hY0.some
    have hyS : ∀ᶠ n in atTop, (xs n, ys n) ∈ argminimaxOn (L (ts n)) X Y := by
      filter_upwards [hev] with n hn
      rw [hprod hn.1]
      simp only [ys, hn.1, dite_true]
      exact ⟨hxs n, (hfac hn.1).2.some_mem⟩
    have hyB : ∀ᶠ n in atTop,
        ys n ∈ Prod.snd '' svImage (fun t ↦ argminimaxOn (L t) X Y) (Icc 0 ε ∩ V) := by
      filter_upwards [hev, hyS] with n hn hS
      exact ⟨(xs n, ys n), hbd hn hS, rfl⟩
    obtain ⟨y', -, φ, hφ, hylim⟩ :=
      tendsto_subseq_of_frequently_bounded hVb.image_snd hyB.frequently
    have hpair : Tendsto (fun n ↦ (xs (φ n), ys (φ n))) atTop (𝓝 (x, y')) :=
      (hxlim.comp hφ.tendsto_atTop).prodMk_nhds hylim
    have hmem := h.mem_argminimaxOn_of_tendsto subset_rfl subset_rfl hXc hYc
      ((hφ.tendsto_atTop.eventually hev).mono fun n hn ↦ hεT' hn.1)
      (hφ.tendsto_atTop.eventually hyS) h0m (hts'.1.comp hφ.tendsto_atTop) hpair
    rw [hprod ⟨le_rfl, hε.le⟩] at hmem
    exact hmem.1
  · refine ⟨V, hV, hVb.image_fst.subset ?_⟩
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_svImage.mp hx
    obtain ⟨y, hy⟩ := (hfac ht.1).2
    exact ⟨(x, y), hbd ht (by rw [hprod ht.1]; exact ⟨hxt, hy⟩), rfl⟩
  · -- osc of `t ↦ Y_t`
    intro y hy
    rw [svOuterLimitWithin, mem_outerSetLimitAlong_iff_exists_seq] at hy
    obtain ⟨ts, ys, hts, hys, hylim⟩ := hy
    have hts' := tendsto_nhdsWithin_iff.mp hts
    have hev : ∀ᶠ n in atTop, ts n ∈ Icc 0 ε ∩ V :=
      (hts'.2.and (hts'.1.eventually hV)).mono fun n hn ↦ hn
    let xs : ℕ → E := fun n ↦ if hn : ts n ∈ Icc 0 ε then (hfac hn).1.some else hX0.some
    have hxS : ∀ᶠ n in atTop, (xs n, ys n) ∈ argminimaxOn (L (ts n)) X Y := by
      filter_upwards [hev] with n hn
      rw [hprod hn.1]
      simp only [xs, hn.1, dite_true]
      exact ⟨(hfac hn.1).1.some_mem, hys n⟩
    have hxB : ∀ᶠ n in atTop,
        xs n ∈ Prod.fst '' svImage (fun t ↦ argminimaxOn (L t) X Y) (Icc 0 ε ∩ V) := by
      filter_upwards [hev, hxS] with n hn hS
      exact ⟨(xs n, ys n), hbd hn hS, rfl⟩
    obtain ⟨x', -, φ, hφ, hxlim⟩ :=
      tendsto_subseq_of_frequently_bounded hVb.image_fst hxB.frequently
    have hpair : Tendsto (fun n ↦ (xs (φ n), ys (φ n))) atTop (𝓝 (x', y)) :=
      hxlim.prodMk_nhds (hylim.comp hφ.tendsto_atTop)
    have hmem := h.mem_argminimaxOn_of_tendsto subset_rfl subset_rfl hXc hYc
      ((hφ.tendsto_atTop.eventually hev).mono fun n hn ↦ hεT' hn.1)
      (hφ.tendsto_atTop.eventually hxS) h0m (hts'.1.comp hφ.tendsto_atTop) hpair
    rw [hprod ⟨le_rfl, hε.le⟩] at hmem
    exact hmem.2
  · refine ⟨V, hV, hVb.image_snd.subset ?_⟩
    intro y hy
    obtain ⟨t, ht, hyt⟩ := mem_svImage.mp hy
    obtain ⟨x, hx⟩ := (hfac ht.1).1
    exact ⟨(x, y), hbd ht (by rw [hprod ht.1]; exact ⟨hx, hyt⟩), rfl⟩
  · -- the right derivative of the common optimal value
    intro c₀ C₀ b₀ B₀ A₀ hc₀ hC₀ hb₀ hB₀ hA₀
    have hLp : ∀ x ∈ argmin (minimaxPrimal (L 0) X Y), ∀ y ∈ argmax (minimaxDual (L 0) X Y),
        Tendsto (fun p : ℝ × (E × P) ↦ (L p.1 p.2.1 p.2.2 - L 0 p.2.1 p.2.2) / p.1)
          (𝓝[>] 0 ×ˢ 𝓝[X ×ˢ Y] (x, y)) (𝓝 (elqpKernel C₀ B₀ A₀ b₀ c₀ x y)) :=
      fun x _ y _ ↦ tendsto_elqpKernel_slope hc₀ hC₀ hb₀ hB₀ hA₀ x y
    obtain ⟨hLc, hLx, hLy, ⟨q, hq⟩, hder⟩ := h.golshtein_derivative hS0.1 hS0.2 hLp
    obtain ⟨-, hX₀n, hY₀n, -, -, hX₀c, hY₀c, hX₀v, hY₀v, -, -, -⟩ :=
      h.zero_structure hS0.1 hS0.2
    have hLpm : IsMinimaxProblem (elqpKernel C₀ B₀ A₀ b₀ c₀) (argmin (minimaxPrimal (L 0) X Y))
        (argmax (minimaxDual (L 0) X Y)) :=
      ⟨hX₀n, hX₀c, hX₀v, hY₀n, hY₀c, hY₀v, hLc, hLx, hLy⟩
    obtain ⟨hv₁, hv₂⟩ := hLpm.saddle_value (x₀ := q.1) (y₀ := q.2) hq
    refine ⟨elqpKernel C₀ B₀ A₀ b₀ c₀ q.1 q.2, hder q hq, ?_, ?_⟩
    · rw [hprim h0m, hdual h0m, hv₁]
      refine iInf_congr fun x ↦ ?_
      rw [minimaxPrimal_elqpKernel]
      by_cases hx : x ∈ argmin (minimaxPrimal (L 0) X Y)
      · rw [iInf_pos hx, if_pos hx]
      · rw [iInf_neg hx, if_neg hx]
    · rw [hprim h0m, hdual h0m, hv₂]
      refine iSup_congr fun y ↦ ?_
      rw [minimaxDual_elqpKernel]
      by_cases hy : y ∈ argmax (minimaxDual (L 0) X Y)
      · rw [iSup_pos hy, if_pos hy]
      · rw [iSup_neg hy, if_neg hy]

end Perturbation

end
end RW
