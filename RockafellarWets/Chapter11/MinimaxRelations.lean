/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Saddle points and minimax relations

Definition 11.49, Theorem 11.50, and the saddle-point product structure 11(25).
-/
import RockafellarWets.Chapter11.Lagrangians
import RockafellarWets.Chapter10.FermatRule

open Set Filter Topology
open scoped InnerProductSpace
namespace RW
noncomputable section

section Saddle
variable {α β γ : Type*}

/-- **Definition 11.49**, formula 11(18): saddle points of `l` in the minimax
sense, minimizing in the first argument and maximizing in the second. -/
def argminimax [Preorder γ] (l : α → β → γ) : Set (α × β) :=
  {p | ∀ x y, l p.1 p.2 ≤ l x p.2 ∧ l p.1 y ≤ l p.1 p.2}

/-- **Definition 11.49**, formula 11(19): saddle points relative to `X × Y`. -/
def argminimaxOn [Preorder γ] (L : α → β → γ) (X : Set α) (Y : Set β) : Set (α × β) :=
  {p | p.1 ∈ X ∧ p.2 ∈ Y ∧ ∀ x ∈ X, ∀ y ∈ Y, L p.1 p.2 ≤ L x p.2 ∧ L p.1 y ≤ L p.1 p.2}

/-- The two formulations in **Definition 11.49** agree:
`inf_x l(x,y₀) = l(x₀,y₀) = sup_y l(x₀,y)`. -/
theorem mem_argminimax_iff_iInf_eq_iSup [CompleteLattice γ] (l : α → β → γ) (x₀ : α) (y₀ : β) :
    (x₀, y₀) ∈ argminimax l ↔ (⨅ x, l x y₀) = l x₀ y₀ ∧ l x₀ y₀ = ⨆ y, l x₀ y := by
  constructor
  · intro h
    exact ⟨le_antisymm (iInf_le _ x₀) (le_iInf fun x ↦ (h x y₀).1),
      le_antisymm (le_iSup _ y₀) (iSup_le fun y ↦ (h x₀ y).2)⟩
  · rintro ⟨h₁, h₂⟩ x y
    exact ⟨h₁.symm.le.trans (iInf_le _ x), (le_iSup _ y).trans h₂.symm.le⟩

end Saddle

/-- Subtracting a finite constant commutes with every infimum in `EReal`. -/
theorem ereal_iInf_sub_coe {ι : Sort*} (g : ι → EReal) (r : ℝ) :
    (⨅ i, g i) - (r : EReal) = ⨅ i, g i - (r : EReal) := by
  simpa only [sub_eq_add_neg, ← EReal.coe_neg] using iInf_add_coe g (-r)

theorem ereal_sub_coe_add (a : EReal) (r s : ℝ) :
    a - ((r + s : ℝ) : EReal) = a - (s : EReal) - (r : EReal) := by
  cases a with
  | bot => simp
  | top => rw [EReal.top_sub_coe, EReal.top_sub_coe, EReal.top_sub_coe]
  | coe a =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1
    ring

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- Formula **11(24)**: `-f*(v,y) = inf_x {l(x,y) - ⟨v,x⟩}`, for every `f`. -/
theorem neg_fenchelConjugate_eq_iInf_lagrangian (f : WithLp 2 (E × P) → EReal) (v : E) (y : P) :
    -fenchelConjugate f (WithLp.toLp 2 (v, y)) = ⨅ x, lagrangian f x y - (⟪v, x⟫_ℝ : EReal) := by
  rw [← iInf_sub_inner_eq_neg_fenchelConjugate, ← (WithLp.toLp_surjective 2).iInf_comp, iInf_prod]
  refine iInf_congr fun x ↦ ?_
  rw [lagrangian, ereal_iInf_sub_coe]
  refine iInf_congr fun u ↦ ?_
  have hi : ⟪WithLp.toLp 2 (v, y), WithLp.toLp 2 (x, u)⟫_ℝ = ⟪v, x⟫_ℝ + ⟪y, u⟫_ℝ := by
    rw [WithLp.prod_inner_apply]
  change f (WithLp.toLp 2 (x, u)) - (⟪WithLp.toLp 2 (v, y), WithLp.toLp 2 (x, u)⟫_ℝ : EReal) =
    f (WithLp.toLp 2 (x, u)) - (⟪y, u⟫_ℝ : EReal) - (⟪v, x⟫_ℝ : EReal)
  rw [hi, ereal_sub_coe_add]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- Formula **11(20)**, dual half: `ψ(y) = inf_x l(x,y)` for every `f`. -/
theorem dualObjective_eq_iInf_lagrangian (f : WithLp 2 (E × P) → EReal) (y : P) :
    dualObjective f y = ⨅ x, lagrangian f x y := by
  rw [dualObjective, neg_fenchelConjugate_eq_iInf_lagrangian]
  simp only [inner_zero_left, EReal.coe_zero, sub_zero]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Formula **11(20)**, primal half: `φ(x) = sup_y l(x,y)`. -/
theorem IsDualizingParameterization.eq_iSup_lagrangian_zero {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) (x : E) :
    φ x = ⨆ y, lagrangian f x y := by
  rw [hf.eq_primalObjective]
  change f (WithLp.toLp 2 (x, 0)) = _
  rw [hf.eq_iSup_lagrangian x 0]
  simp only [inner_zero_right, EReal.coe_zero, add_zero]

omit [FiniteDimensional ℝ E] in
/-- Formula **11(21)**: `inf φ = inf_x sup_y l ≥ sup_y inf_x l = sup ψ`. -/
theorem IsDualizingParameterization.minimax_inequality {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) :
    (⨅ x, φ x) = (⨅ x, ⨆ y, lagrangian f x y) ∧
      (⨆ y, ⨅ x, lagrangian f x y) ≤ (⨅ x, ⨆ y, lagrangian f x y) ∧
      (⨆ y, ⨅ x, lagrangian f x y) = ⨆ y, dualObjective f y :=
  ⟨iInf_congr hf.eq_iSup_lagrangian_zero, iSup_iInf_le_iInf_iSup (fun y x ↦ lagrangian f x y),
    iSup_congr fun y ↦ (dualObjective_eq_iInf_lagrangian f y).symm⟩

/-- Weak duality and the value characterization of joint optimality, needing
only properness of `f` (the conjugate may be identically `∞`). -/
theorem primal_dual_optimality_iff_values_equal_of_isProper {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (x : E) (y : P) :
    (x ∈ argmin (primalObjective f) ∧ y ∈ argmax (dualObjective f) ∧
      (⨅ z, primalObjective f z) = (⨆ v, dualObjective f v)) ↔
      primalObjective f x = dualObjective f y := by
  constructor
  · rintro ⟨hx, hy, he⟩
    exact hx.1.trans (he.trans hy.1.symm)
  · intro he
    have hx : primalObjective f x = ⨅ z, primalObjective f z := by
      apply le_antisymm _ (iInf_le _ x)
      apply le_iInf
      intro z
      rw [he]
      exact dualObjective_le_primalObjective f z y
    have hy : dualObjective f y = ⨆ v, dualObjective f v := by
      apply le_antisymm (le_iSup _ y)
      apply iSup_le
      intro v
      rw [← he]
      exact dualObjective_le_primalObjective f x v
    have hfin : primalObjective f x < ⊤ := by
      rw [he]
      change -fenchelConjugate f (WithLp.toLp 2 (0, y)) < ⊤
      rw [EReal.neg_lt_comm, EReal.neg_top]
      obtain ⟨q, hq⟩ := hp.1
      exact bot_lt_fenchelConjugate_of_finite (EReal.coe_toReal hq.ne (hp.2 q).ne').symm _
    have hbot : ⊥ < dualObjective f y := by
      rw [← he]
      exact hp.2 _
    exact ⟨⟨hx, hx ▸ hfin⟩, ⟨hy, hy ▸ hbot⟩, hx.symm.trans (he.trans hy)⟩

omit [FiniteDimensional ℝ E] in
/-- **Theorem 11.50**: saddle points are exactly the pairs with `φ(x₀) = ψ(y₀)`,
in which case `l(x₀,y₀)` is that common value. -/
theorem IsDualizingParameterization.mem_argminimax_iff {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) (x₀ : E) (y₀ : P) :
    (x₀, y₀) ∈ argminimax (lagrangian f) ↔
      φ x₀ = dualObjective f y₀ ∧ dualObjective f y₀ = lagrangian f x₀ y₀ := by
  have h₁ : dualObjective f y₀ ≤ lagrangian f x₀ y₀ :=
    (dualObjective_eq_iInf_lagrangian f y₀).trans_le (iInf_le _ x₀)
  have h₂ : lagrangian f x₀ y₀ ≤ φ x₀ :=
    (le_iSup (lagrangian f x₀) y₀).trans (hf.eq_iSup_lagrangian_zero x₀).symm.le
  constructor
  · intro h
    have hψ : lagrangian f x₀ y₀ ≤ dualObjective f y₀ := by
      rw [dualObjective_eq_iInf_lagrangian]
      exact le_iInf fun x ↦ (h x y₀).1
    have hφ : φ x₀ ≤ lagrangian f x₀ y₀ := by
      rw [hf.eq_iSup_lagrangian_zero]
      exact iSup_le fun y ↦ (h x₀ y).2
    exact ⟨le_antisymm (hφ.trans hψ) (h₁.trans h₂), le_antisymm h₁ hψ⟩
  · rintro ⟨he, -⟩ x y
    constructor
    · calc lagrangian f x₀ y₀ ≤ φ x₀ := h₂
        _ = dualObjective f y₀ := he
        _ = ⨅ x, lagrangian f x y₀ := dualObjective_eq_iInf_lagrangian f y₀
        _ ≤ lagrangian f x y₀ := iInf_le _ x
    · calc lagrangian f x₀ y ≤ ⨆ y, lagrangian f x₀ y := le_iSup _ y
        _ = φ x₀ := (hf.eq_iSup_lagrangian_zero x₀).symm
        _ = dualObjective f y₀ := he
        _ ≤ lagrangian f x₀ y₀ := h₁

/-- **Theorem 11.50**, formula 11(22): joint optimality with equal optimal
values is the same as being a saddle point of the Lagrangian, and the same as
`φ(x₀) = ψ(y₀) = l(x₀,y₀)`. -/
theorem IsDualizingParameterization.minimax_relations {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) (x₀ : E) (y₀ : P) :
    ((x₀ ∈ argmin φ ∧ y₀ ∈ argmax (dualObjective f) ∧ (⨅ x, φ x) = ⨆ y, dualObjective f y) ↔
      (x₀, y₀) ∈ argminimax (lagrangian f)) ∧
    ((x₀, y₀) ∈ argminimax (lagrangian f) ↔
      φ x₀ = dualObjective f y₀ ∧ dualObjective f y₀ = lagrangian f x₀ y₀) := by
  refine ⟨?_, hf.mem_argminimax_iff x₀ y₀⟩
  have hopt := primal_dual_optimality_iff_values_equal_of_isProper hf.isProper x₀ y₀
  rw [← hf.eq_primalObjective] at hopt
  rw [hf.mem_argminimax_iff, hopt]
  refine ⟨fun he ↦ ⟨he, ?_⟩, And.left⟩
  have h₁ : dualObjective f y₀ ≤ lagrangian f x₀ y₀ :=
    (dualObjective_eq_iInf_lagrangian f y₀).trans_le (iInf_le _ x₀)
  have h₂ : lagrangian f x₀ y₀ ≤ φ x₀ :=
    (le_iSup (lagrangian f x₀) y₀).trans (hf.eq_iSup_lagrangian_zero x₀).symm.le
  exact le_antisymm h₁ (h₂.trans he.le)

omit [FiniteDimensional ℝ E] in
/-- At a saddle point the Lagrangian value is finite. -/
theorem IsDualizingParameterization.lagrangian_finite_of_mem_argminimax {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) {x₀ : E} {y₀ : P}
    (h : (x₀, y₀) ∈ argminimax (lagrangian f)) : ∃ c : ℝ, lagrangian f x₀ y₀ = c := by
  obtain ⟨hφψ, hψl⟩ := (hf.mem_argminimax_iff x₀ y₀).mp h
  have hb : ⊥ < lagrangian f x₀ y₀ := by
    rw [← hψl, ← hφψ, hf.eq_primalObjective]
    exact hf.isProper.2 _
  have ht : lagrangian f x₀ y₀ < ⊤ := by
    rw [← hψl]
    change -fenchelConjugate f (WithLp.toLp 2 (0, y₀)) < ⊤
    rw [EReal.neg_lt_comm, EReal.neg_top]
    obtain ⟨q, hq⟩ := hf.isProper.1
    exact bot_lt_fenchelConjugate_of_finite (EReal.coe_toReal hq.ne (hf.isProper.2 q).ne').symm _
  exact ⟨_, (EReal.coe_toReal ht.ne hb.ne').symm⟩

omit [FiniteDimensional ℝ E] in
/-- **Theorem 11.50**: every saddle point satisfies the subgradient condition
**11(23)**, `0 ∈ ∂ₓl(x₀,y₀)` and `0 ∈ ∂_y[-l](x₀,y₀)`. -/
theorem IsDualizingParameterization.subgradient_condition_of_mem_argminimax {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) {x₀ : E} {y₀ : P}
    (h : (x₀, y₀) ∈ argminimax (lagrangian f)) :
    (0 : E) ∈ subdifferential (fun x ↦ lagrangian f x y₀) x₀ ∧
      (0 : P) ∈ subdifferential (fun y ↦ -lagrangian f x₀ y) y₀ := by
  obtain ⟨c, hc⟩ := hf.lagrangian_finite_of_mem_argminimax h
  refine ⟨RW.IsLocalMin.zero_mem_subdifferential (Eventually.of_forall fun x ↦ (h x y₀).1) hc,
    RW.IsLocalMin.zero_mem_subdifferential (Eventually.of_forall fun y ↦ ?_)
      (show -lagrangian f x₀ y₀ = ((-c : ℝ) : EReal) by rw [hc, EReal.coe_neg])⟩
  exact EReal.neg_le_neg_iff.mpr (h x₀ y).2

/-- **Theorem 11.50**: when `l(x,y)` is convex in `x` (it is always concave in
`y` by 11.48), the subgradient condition **11(23)** characterizes saddle
points, and both are equivalent to `(0,y₀) ∈ ∂f(x₀,0)`. -/
theorem IsDualizingParameterization.mem_argminimax_iff_subgradient_condition {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f)
    (hl : ∀ y, Convex ℝ (epigraph (fun x ↦ lagrangian f x y))) (x₀ : E) (y₀ : P) :
    ((x₀, y₀) ∈ argminimax (lagrangian f) ↔
      (0 : E) ∈ subdifferential (fun x ↦ lagrangian f x y₀) x₀ ∧
        (0 : P) ∈ subdifferential (fun y ↦ -lagrangian f x₀ y) y₀) ∧
    ((x₀, y₀) ∈ argminimax (lagrangian f) ↔
      WithLp.toLp 2 ((0 : E), y₀) ∈ subdifferential f (WithLp.toLp 2 (x₀, (0 : P)))) := by
  have hsub : (x₀, y₀) ∈ argminimax (lagrangian f) ↔
      (0 : E) ∈ subdifferential (fun x ↦ lagrangian f x y₀) x₀ ∧
        (0 : P) ∈ subdifferential (fun y ↦ -lagrangian f x₀ y) y₀ := by
    refine ⟨hf.subgradient_condition_of_mem_argminimax, fun ⟨h0x, h0y⟩ x y ↦ ⟨?_, ?_⟩⟩
    · obtain ⟨c, hc⟩ := h0x.1
      have hx := forall_le_of_mem_subdifferential_of_convex (hl y₀) hc h0x x
      simp only [inner_zero_left, add_zero] at hx
      exact (show lagrangian f x₀ y₀ = c from hc).trans_le hx
    · obtain ⟨d, hd⟩ := h0y.1
      have hy := forall_le_of_mem_subdifferential_of_convex (lagrangian_usc_concave f x₀).2 hd h0y y
      simp only [inner_zero_left, add_zero] at hy
      exact EReal.neg_le_neg_iff.mp ((show -lagrangian f x₀ y₀ = d from hd).trans_le hy)
  refine ⟨hsub, hsub.trans ?_⟩
  exact (hf.mem_subdifferential_iff_lagrangian (hf.convex_lagrangian_iff.mp hl) x₀ 0 0 y₀).symm

/-- The product structure **11(25)** when the optimal values agree. -/
theorem IsDualizingParameterization.argminimax_eq_prod {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f)
    (he : (⨅ x, φ x) = ⨆ y, dualObjective f y) :
    argminimax (lagrangian f) = argmin φ ×ˢ argmax (dualObjective f) := by
  ext ⟨x₀, y₀⟩
  rw [← (hf.minimax_relations x₀ y₀).1]
  simp [he]

/-- The empty case of **11(25)**, when there is a duality gap. -/
theorem IsDualizingParameterization.argminimax_eq_empty {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f)
    (hlt : (⨆ y, dualObjective f y) < ⨅ x, φ x) : argminimax (lagrangian f) = ∅ := by
  ext ⟨x₀, y₀⟩
  rw [← (hf.minimax_relations x₀ y₀).1]
  simp only [mem_empty_iff_false, iff_false, not_and]
  exact fun _ _ he ↦ hlt.ne' he

/-- The Lagrangian is constant on its saddle-point set; this constant is the
saddle value `minimax l = inf φ = sup ψ`. -/
theorem IsDualizingParameterization.lagrangian_eq_of_mem_argminimax {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) {x₀ : E} {y₀ : P}
    (h : (x₀, y₀) ∈ argminimax (lagrangian f)) :
    lagrangian f x₀ y₀ = ⨅ x, φ x ∧ lagrangian f x₀ y₀ = ⨆ y, dualObjective f y := by
  obtain ⟨hx, hy, he⟩ := (hf.minimax_relations x₀ y₀).1.mpr h
  obtain ⟨hφψ, hψl⟩ := (hf.minimax_relations x₀ y₀).2.mp h
  exact ⟨hψl.symm.trans (hφψ.symm.trans hx.1), hψl.symm.trans hy.1⟩

end
end RW
