/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Duality without convexity and exact penalty representations

Theorem 11.59, Definition 11.60 and Theorem 11.61. The integrand is assumed
lower semicontinuous jointly, as the appeal to Theorem 1.17 in the book's
proof requires: lower semicontinuity in `u` alone does not keep the marginal
function lsc and allows a duality gap. In the saddle-point characterization
the common value must be finite, since an infeasible problem has no
minimizers under the book's `argmin` convention. The proofs replace the
epi-convergence argument by the linear growth of augmenting functions away
from the origin.
-/
import RockafellarWets.Chapter11.AugmentedLagrangians

open Set Filter Topology Metric
open scoped InnerProductSpace
namespace RW
noncomputable section

/-- With both summands above `-∞`, an augmented term is identically `∞` on
`r > 0` or has finite data. -/
theorem augmentedTerm_cases_of_ne_bot {A B : EReal} (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    (∀ r : ℝ, 0 < r → ∀ t : ℝ, A + (r : EReal) * B - (t : EReal) = ⊤) ∨
      ∃ a b : ℝ, A = a ∧ B = b := by
  induction A using EReal.rec with
  | bot => exact absurd rfl hA
  | top =>
    left
    intro r hr t
    induction B using EReal.rec with
    | bot => exact absurd rfl hB
    | coe b => rw [← EReal.coe_mul, EReal.top_add_coe]; simp
    | top => rw [EReal.coe_mul_top_of_pos hr]; simp
  | coe a =>
    induction B using EReal.rec with
    | bot => exact absurd rfl hB
    | coe b => exact .inr ⟨a, b, rfl, rfl⟩
    | top => left; intro r hr t; rw [EReal.coe_mul_top_of_pos hr]; simp

theorem augmentedTerm_coe (a b r t : ℝ) :
    (a : EReal) + (r : EReal) * (b : EReal) - (t : EReal) = ((a + r * b - t : ℝ) : EReal) := by
  norm_cast

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  {f : WithLp 2 (E × P) → EReal} {σ : P → EReal}

/-- `(yb, rb)` maximizes the augmented dual objective over `r > 0`. -/
def IsAugmentedDualMaximizer (f : WithLp 2 (E × P) → EReal) (σ : P → EReal) (yb : P)
    (rb : ℝ) : Prop :=
  0 < rb ∧ ∀ (y : P) (r : ℝ), 0 < r →
    augmentedDualObjective f σ y r ≤ augmentedDualObjective f σ yb rb

/-- The augmented slice `u ↦ f(x,u) + rσ(u)`. -/
def augmentedSlice (f : WithLp 2 (E × P) → EReal) (σ : P → EReal) (r : ℝ) (x : E) :
    P → EReal :=
  fun u ↦ f (WithLp.toLp 2 (x, u)) + (r : EReal) * σ u

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P] in
theorem augmentedLagrangian_eq_neg_fenchelConjugate (x : E) (y : P) (r : ℝ) :
    augmentedLagrangian f σ x y r = -fenchelConjugate (augmentedSlice f σ r x) y :=
  iInf_sub_inner_eq_neg_fenchelConjugate (augmentedSlice f σ r x) y

omit [FiniteDimensional ℝ P] in
theorem IsAugmentingFunction.coe_mul_nonneg (hσ : IsAugmentingFunction σ) {r : ℝ} (hr : 0 ≤ r)
    (u : P) : 0 ≤ (r : EReal) * σ u :=
  EReal.mul_nonneg (EReal.coe_nonneg.mpr hr) (hσ.nonneg u)

omit [FiniteDimensional ℝ P] in
theorem IsAugmentingFunction.coe_mul_ne_bot (hσ : IsAugmentingFunction σ) {r : ℝ} (hr : 0 ≤ r)
    (u : P) : (r : EReal) * σ u ≠ ⊥ :=
  ne_bot_of_le_ne_bot EReal.zero_ne_bot (hσ.coe_mul_nonneg hr u)

omit [FiniteDimensional ℝ P] in
theorem add_coe_mul_ne_bot {A : EReal} (hA : A ≠ ⊥) (hσ : IsAugmentingFunction σ) {r : ℝ}
    (hr : 0 ≤ r) (u : P) : A + (r : EReal) * σ u ≠ ⊥ := by
  intro h
  rw [EReal.add_eq_bot_iff] at h
  exact h.elim hA (hσ.coe_mul_ne_bot hr u)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Each augmented slice of a dualizing parameterization is its own biconjugate. -/
theorem IsDualizingParameterization.biconjugate_augmentedSlice
    (hf : IsDualizingParameterization (primalObjective f) f) (hσ : IsAugmentingFunction σ)
    {r : ℝ} (hr : 0 < r) (x : E) :
    fenchelConjugate (fenchelConjugate (augmentedSlice f σ r x)) = augmentedSlice f σ r x := by
  have hfb : ∀ u, f (WithLp.toLp 2 (x, u)) ≠ ⊥ := fun u ↦ (hf.isProper.2 _).ne'
  have hgb : ∀ u, augmentedSlice f σ r x u ≠ ⊥ := fun u ↦ add_coe_mul_ne_bot (hfb u) hσ hr.le u
  by_cases h : ∃ u, augmentedSlice f σ r x u < ⊤
  · have hp : IsProper (augmentedSlice f σ r x) := ⟨h, fun u ↦ bot_lt_iff_ne_bot.mpr (hgb u)⟩
    have hl : LowerSemicontinuous (augmentedSlice f σ r x) := by
      change LowerSemicontinuous (fun u ↦ parameterSlice f x u + (r : EReal) * σ u)
      refine (hf.lowerSemicontinuous_slice x).add'
        (lowerSemicontinuous_const_mul hσ.lowerSemicontinuous hr) fun u ↦ ?_
      exact EReal.continuousAt_add (Or.inr (hσ.coe_mul_ne_bot hr.le u)) (Or.inl (hfb u))
    have hc : Convex ℝ (epigraph (augmentedSlice f σ r x)) :=
      convex_epigraph_add_of_ne_bot (hf.convex_slice x) (convex_epigraph_coe_mul hσ.convex hr)
        hfb (hσ.coe_mul_ne_bot hr.le)
    exact fenchelConjugate_fenchelConjugate_eq hp hl hc
  · push_neg at h
    have he : augmentedSlice f σ r x = fun _ ↦ ⊤ := funext fun u ↦ top_le_iff.mp (h u)
    rw [he]
    exact identically_top_conjugates.2

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Theorem 11.59**: `φ(x) = sup_y l̄(x,y,r)` for every `r > 0`. -/
theorem IsDualizingParameterization.iSup_augmentedLagrangian
    (hf : IsDualizingParameterization (primalObjective f) f) (hσ : IsAugmentingFunction σ)
    {r : ℝ} (hr : 0 < r) (x : E) :
    (⨆ y, augmentedLagrangian f σ x y r) = primalObjective f x := by
  have h := congrFun (hf.biconjugate_augmentedSlice hσ hr x) 0
  have hg0 : augmentedSlice f σ r x 0 = primalObjective f x := by
    change f (WithLp.toLp 2 (x, 0)) + (r : EReal) * σ 0 = f (WithLp.toLp 2 (x, 0))
    rw [hσ.zero, mul_zero, add_zero]
  rw [hg0] at h
  rw [← h]
  simp only [fenchelConjugate, inner_zero_left, EReal.coe_zero, zero_sub,
    augmentedLagrangian_eq_neg_fenchelConjugate]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Theorem 11.59**: `φ(x) = sup_{y,r} l̄(x,y,r)`. -/
theorem IsDualizingParameterization.iSup_iSup_augmentedLagrangian
    (hf : IsDualizingParameterization (primalObjective f) f) (hσ : IsAugmentingFunction σ)
    (x : E) :
    (⨆ (y : P) (r : ℝ) (_ : 0 < r), augmentedLagrangian f σ x y r) = primalObjective f x := by
  apply le_antisymm
  · refine iSup_le fun y ↦ iSup₂_le fun r hr ↦ ?_
    exact (le_iSup (fun y ↦ augmentedLagrangian f σ x y r) y).trans
      (hf.iSup_augmentedLagrangian hσ hr x).le
  · rw [← hf.iSup_augmentedLagrangian hσ one_pos x]
    exact iSup_mono fun y ↦ le_iSup₂_of_le (f := fun (r : ℝ) (_ : 0 < r) ↦
      augmentedLagrangian f σ x y r) 1 one_pos le_rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P] in
/-- Weak duality for the augmented dual problem. -/
theorem augmentedDualObjective_le_primalObjective (hσ0 : σ 0 = 0) (x : E) (y : P) (r : ℝ) :
    augmentedDualObjective f σ y r ≤ primalObjective f x := by
  refine (iInf_le _ x).trans ((iInf_le _ 0).trans ?_)
  rw [hσ0, mul_zero, add_zero, inner_zero_right, EReal.coe_zero, sub_zero]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P] in
theorem iSup_augmentedDualObjective_le (hσ0 : σ 0 = 0) :
    (⨆ (y : P) (r : ℝ) (_ : 0 < r), augmentedDualObjective f σ y r) ≤
      ⨅ x, primalObjective f x :=
  iSup_le fun y ↦ iSup₂_le fun r _ ↦ le_iInf fun x ↦
    augmentedDualObjective_le_primalObjective hσ0 x y r

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [InnerProductSpace ℝ P] [FiniteDimensional ℝ P] in
theorem parametricValue_zero_eq (f : WithLp 2 (E × P) → EReal) :
    parametricValue f 0 = ⨅ x, primalObjective f x := rfl

/-- **Theorem 11.59**, the middle equality in 11(30): the augmented dual
problem has no duality gap. -/
theorem iInf_primalObjective_eq_iSup_augmentedDualObjective
    (hf : IsDualizingParameterization (primalObjective f) f) (hl : LowerSemicontinuous f)
    (hb : IsParametricallyLevelBounded f) (hσ : IsAugmentingFunction σ)
    (hψ : ∃ (y : P) (r : ℝ), 0 < r ∧ ⊥ < augmentedDualObjective f σ y r) :
    (⨅ x, primalObjective f x) = ⨆ (y : P) (r : ℝ) (_ : 0 < r), augmentedDualObjective f σ y r := by
  refine le_antisymm ?_ (iSup_augmentedDualObjective_le hσ.zero)
  obtain ⟨yt, rt, hrt, hα⟩ := hψ
  rw [← parametricValue_zero_eq]
  set S := ⨆ (y : P) (r : ℝ) (_ : 0 < r), augmentedDualObjective f σ y r with hS
  have hmem : ∀ r : ℝ, 0 < r → augmentedDualObjective f σ yt r ≤ S := fun r hr ↦
    le_iSup_of_le yt (le_iSup₂_of_le (f := fun (r : ℝ) (_ : 0 < r) ↦
      augmentedDualObjective f σ yt r) r hr le_rfl)
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro β hβ
  by_cases hαt : augmentedDualObjective f σ yt rt = ⊤
  · exact (le_top.trans_eq hαt.symm).trans (hmem rt hrt)
  obtain ⟨α, hα'⟩ : ∃ α : ℝ, augmentedDualObjective f σ yt rt = α :=
    ⟨_, (EReal.coe_toReal hαt hα.ne').symm⟩
  obtain ⟨β', hββ', hβ'⟩ := EReal.exists_between_coe_real hβ
  obtain ⟨β'', hβ'β'', hβ''⟩ := EReal.exists_between_coe_real hβ'
  have hββ'r : β < β' := EReal.coe_lt_coe_iff.mp hββ'
  have hβ'β''r : β' < β'' := EReal.coe_lt_coe_iff.mp hβ'β''
  have hpl := lowerSemicontinuous_parametricValue hl hf.isProper hb
  have hev : ∀ᶠ u in 𝓝 (0 : P), (β'' : EReal) < parametricValue f u := hpl 0 β'' hβ''
  have hev2 : ∀ᶠ u in 𝓝 (0 : P), ⟪yt, u⟫_ℝ < β'' - β' := by
    have hc : Continuous fun u : P ↦ ⟪yt, u⟫_ℝ := continuous_const.inner continuous_id
    have h0 : ⟪yt, (0 : P)⟫_ℝ < β'' - β' := by rw [inner_zero_right]; linarith
    exact hc.continuousAt.eventually (Iio_mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hev2)
  obtain ⟨c, hc, hgrowth⟩ := hσ.exists_linear_growth hε
  set s := max 0 ((β' - α) / (c * ε)) with hsdef
  have hs0 : 0 ≤ s := le_max_left _ _
  have hs : β' - α ≤ s * (c * ε) := by
    have h := le_max_right 0 ((β' - α) / (c * ε))
    rwa [div_le_iff₀ (mul_pos hc hε)] at h
  have hrs : 0 < rt + s := add_pos_of_pos_of_nonneg hrt hs0
  refine (EReal.coe_le_coe_iff.mpr hββ'r.le).trans
    ((?_ : (β' : EReal) ≤ augmentedDualObjective f σ yt (rt + s)).trans (hmem _ hrs))
  refine le_iInf fun x ↦ le_iInf fun u ↦ ?_
  have hfb : f (WithLp.toLp 2 (x, u)) ≠ ⊥ := (hf.isProper.2 _).ne'
  have hσb : σ u ≠ ⊥ := (hσ.isProper.2 u).ne'
  rcases augmentedTerm_cases_of_ne_bot hfb hσb with htop | ⟨a, b, ha, hb'⟩
  · rw [htop _ hrs]
    exact le_top
  rw [ha, hb', augmentedTerm_coe, EReal.coe_le_coe_iff]
  have hb0 : 0 ≤ b := by
    have h := hσ.nonneg u
    rw [hb'] at h
    exact_mod_cast h
  have hαle : α ≤ a + rt * b - ⟪yt, u⟫_ℝ := by
    have h : augmentedDualObjective f σ yt rt ≤
        f (WithLp.toLp 2 (x, u)) + (rt : EReal) * σ u - (⟪yt, u⟫_ℝ : EReal) :=
      (iInf_le _ x).trans (iInf_le _ u)
    rwa [hα', ha, hb', augmentedTerm_coe, EReal.coe_le_coe_iff] at h
  have hexp : (rt + s) * b = rt * b + s * b := by ring
  by_cases hu : ‖u‖ < ε
  · obtain ⟨h1, h2⟩ := hball (show dist u 0 < ε by rwa [dist_zero_right])
    have hpa : parametricValue f u ≤ (a : EReal) := by
      rw [← ha]
      exact iInf_le (fun x ↦ f (WithLp.toLp 2 (x, u))) x
    have hβa : β'' < a := EReal.coe_lt_coe_iff.mp (h1.trans_le hpa)
    nlinarith [mul_nonneg hs0 hb0, mul_nonneg hrt.le hb0]
  · push_neg at hu
    have hgb := hgrowth u hu
    rw [hb', EReal.coe_le_coe_iff] at hgb
    have hcb : c * ε ≤ b := le_trans (mul_le_mul_of_nonneg_left hu hc.le) hgb
    nlinarith [mul_le_mul_of_nonneg_left hcb hs0]


omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P] in
/-- An inequality of the form 11(32), with an arbitrary left-hand constant,
says exactly that `ψ̄(ȳ,r̄)` reaches that constant. -/
theorem le_augmentedDualObjective_iff (hσ : IsAugmentingFunction σ)
    (hpb : ∀ u, parametricValue f u ≠ ⊥) (c : EReal) {yb : P} {rb : ℝ} (hrb : 0 < rb) :
    c ≤ augmentedDualObjective f σ yb rb ↔
      ∀ u, c + (⟪yb, u⟫_ℝ : EReal) ≤ parametricValue f u + (rb : EReal) * σ u := by
  constructor
  · intro h u
    have hx : ∀ x, c + (⟪yb, u⟫_ℝ : EReal) ≤ f (WithLp.toLp 2 (x, u)) + (rb : EReal) * σ u := by
      intro x
      have h' : c ≤ f (WithLp.toLp 2 (x, u)) + (rb : EReal) * σ u - (⟪yb, u⟫_ℝ : EReal) :=
        h.trans ((iInf_le _ x).trans (iInf_le _ u))
      exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))).mp h'
    induction hσu : σ u using EReal.rec with
    | bot => exact absurd hσu (hσ.isProper.2 u).ne'
    | top =>
      rw [EReal.coe_mul_top_of_pos hrb, EReal.add_top_of_ne_bot (hpb u)]
      exact le_top
    | coe b =>
      rw [← EReal.coe_mul, ← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))]
      refine le_iInf fun x ↦ ?_
      rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
        EReal.coe_mul, ← hσu]
      exact hx x
  · intro h
    refine le_iInf fun x ↦ le_iInf fun u ↦ ?_
    rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    exact (h u).trans (add_le_add_left (iInf_le (fun x ↦ f (WithLp.toLp 2 (x, u))) x) _)

section Duality

variable (hf : IsDualizingParameterization (primalObjective f) f) (hl : LowerSemicontinuous f)
  (hb : IsParametricallyLevelBounded f) (hσ : IsAugmentingFunction σ)
  (hψ : ∃ (y : P) (r : ℝ), 0 < r ∧ ⊥ < augmentedDualObjective f σ y r)
include hf hl hb hσ hψ

/-- The maximizing pairs of the augmented dual are those reaching `p(0) = inf φ`. -/
theorem isAugmentedDualMaximizer_iff_le {yb : P} {rb : ℝ} (hrb : 0 < rb) :
    IsAugmentedDualMaximizer f σ yb rb ↔
      parametricValue f 0 ≤ augmentedDualObjective f σ yb rb := by
  rw [parametricValue_zero_eq, iInf_primalObjective_eq_iSup_augmentedDualObjective hf hl hb hσ hψ]
  constructor
  · rintro ⟨-, hmax⟩
    exact iSup_le fun y ↦ iSup₂_le fun r hr ↦ hmax y r hr
  · intro h
    exact ⟨hrb, fun y r hr ↦ (le_iSup_of_le y (le_iSup₂_of_le (f := fun (r : ℝ) (_ : 0 < r) ↦
      augmentedDualObjective f σ y r) r hr le_rfl)).trans h⟩

/-- **Theorem 11.59**, 11(32): the maximizing pairs of the augmented dual
problem are those with `p(u) ≥ p(0) + ⟨ȳ,u⟩ - r̄σ(u)` for all `u`. -/
theorem isAugmentedDualMaximizer_iff {yb : P} {rb : ℝ} (hrb : 0 < rb) :
    IsAugmentedDualMaximizer f σ yb rb ↔
      ∀ u, parametricValue f 0 + (⟪yb, u⟫_ℝ : EReal) ≤ parametricValue f u + (rb : EReal) * σ u := by
  rw [isAugmentedDualMaximizer_iff_le hf hl hb hσ hψ hrb]
  exact le_augmentedDualObjective_iff hσ
    (fun u ↦ ((isProper_parametricValue hl hf.isProper hb).2 u).ne') _ hrb

/-- **Theorem 11.59**, 11(31): optimal primal and augmented dual solutions are
the saddle points of the augmented Lagrangian with a finite saddle value. -/
theorem mem_argmin_and_isAugmentedDualMaximizer_iff {xb : E} {yb : P} {rb : ℝ} (hrb : 0 < rb) :
    (xb ∈ argmin (primalObjective f) ∧ IsAugmentedDualMaximizer f σ yb rb) ↔
      ((⨅ x, augmentedLagrangian f σ x yb rb) = augmentedLagrangian f σ xb yb rb ∧
        augmentedLagrangian f σ xb yb rb =
          ⨆ (y : P) (r : ℝ) (_ : 0 < r), augmentedLagrangian f σ xb y r ∧
        augmentedLagrangian f σ xb yb rb < ⊤) := by
  have hsd := iInf_primalObjective_eq_iSup_augmentedDualObjective hf hl hb hσ hψ
  have hsup := hf.iSup_iSup_augmentedLagrangian hσ xb
  have hψle : augmentedDualObjective f σ yb rb ≤ augmentedLagrangian f σ xb yb rb := iInf_le _ xb
  have hlle : augmentedLagrangian f σ xb yb rb ≤ primalObjective f xb := by
    rw [← hsup]
    exact le_iSup_of_le yb (le_iSup₂_of_le (f := fun (r : ℝ) (_ : 0 < r) ↦
      augmentedLagrangian f σ xb yb r) rb hrb le_rfl)
  have hdual : augmentedDualObjective f σ yb rb ≤ ⨅ x, primalObjective f x := by
    rw [hsd]
    exact le_iSup_of_le yb (le_iSup₂_of_le (f := fun (r : ℝ) (_ : 0 < r) ↦
      augmentedDualObjective f σ yb r) rb hrb le_rfl)
  rw [← augmentedDualObjective_eq_iInf_augmentedLagrangian, hsup,
    isAugmentedDualMaximizer_iff_le hf hl hb hσ hψ hrb, parametricValue_zero_eq, mem_argmin_iff]
  constructor
  · rintro ⟨⟨hx, hlt⟩, hmax⟩
    have h1 : primalObjective f xb ≤ augmentedDualObjective f σ yb rb := hx ▸ hmax
    exact ⟨le_antisymm hψle (hlle.trans h1), le_antisymm hlle (h1.trans hψle),
      hlle.trans_lt (hx ▸ hlt)⟩
  · rintro ⟨h1, h2, h3⟩
    have hϕψ : primalObjective f xb = augmentedDualObjective f σ yb rb := h2.symm.trans h1.symm
    have hinf : (⨅ x, primalObjective f x) = primalObjective f xb :=
      le_antisymm (iInf_le _ xb) (hϕψ ▸ hdual)
    refine ⟨⟨hinf.symm, ?_⟩, ?_⟩
    · rw [hinf, ← h2]
      exact h3
    · rw [hinf, hϕψ]

/-- **Theorem 11.59** (adapted): duality without convexity for a jointly lsc
dualizing parameterization that is level-bounded in `x` locally uniformly in
`u`, whenever `inf_x l̄(x,y,r) > -∞` for some `(y,r)`. -/
theorem duality_without_convexity :
    (∀ x, primalObjective f x = ⨆ (y : P) (r : ℝ) (_ : 0 < r), augmentedLagrangian f σ x y r) ∧
    (∀ x (r : ℝ), 0 < r → primalObjective f x = ⨆ y, augmentedLagrangian f σ x y r) ∧
    (∀ y r, augmentedDualObjective f σ y r = ⨅ x, augmentedLagrangian f σ x y r) ∧
    ((⨅ x, primalObjective f x) =
        ⨅ x, ⨆ (y : P) (r : ℝ) (_ : 0 < r), augmentedLagrangian f σ x y r) ∧
    ((⨅ x, primalObjective f x) =
        ⨆ (y : P) (r : ℝ) (_ : 0 < r), ⨅ x, augmentedLagrangian f σ x y r) ∧
    ((⨅ x, primalObjective f x) =
        ⨆ (y : P) (r : ℝ) (_ : 0 < r), augmentedDualObjective f σ y r) := by
  have hsd := iInf_primalObjective_eq_iSup_augmentedDualObjective hf hl hb hσ hψ
  refine ⟨fun x ↦ (hf.iSup_iSup_augmentedLagrangian hσ x).symm,
    fun x r hr ↦ (hf.iSup_augmentedLagrangian hσ hr x).symm, fun _ _ ↦ rfl, ?_, hsd, hsd⟩
  exact iInf_congr fun x ↦ (hf.iSup_iSup_augmentedLagrangian hσ x).symm

end Duality

/-- **Definition 11.60**: `r̄ > 0` is an adequate penalty threshold for `ȳ`
when, for every `r > r̄`, minimizing `l̄(·,ȳ,r)` has the same optimal value
and the same optimal solutions as minimizing `φ`. -/
def IsAdequatePenaltyThreshold (f : WithLp 2 (E × P) → EReal) (σ : P → EReal) (yb : P)
    (rb : ℝ) : Prop :=
  0 < rb ∧ ∀ r : ℝ, rb < r →
    (⨅ x, primalObjective f x) = (⨅ x, augmentedLagrangian f σ x yb r) ∧
      argmin (primalObjective f) = argmin (fun x ↦ augmentedLagrangian f σ x yb r)

/-- **Definition 11.60**: `ȳ` supports an exact penalty representation when
some `r̄ > 0` is an adequate penalty threshold. -/
def SupportsExactPenaltyRepresentation (f : WithLp 2 (E × P) → EReal) (σ : P → EReal)
    (yb : P) : Prop :=
  ∃ rb, IsAdequatePenaltyThreshold f σ yb rb

section ExactPenalty

variable (hf : IsDualizingParameterization (primalObjective f) f) (hl : LowerSemicontinuous f)
  (hb : IsParametricallyLevelBounded f) (hσ : IsAugmentingFunction σ)
  (hψ : ∃ (y : P) (r : ℝ), 0 < r ∧ ⊥ < augmentedDualObjective f σ y r)
include hf hl hb hσ hψ

/-- **Theorem 11.61**: the adequate penalty thresholds for `ȳ` are exactly the
`r̄` with `(ȳ,r̄)` maximizing the augmented dual objective. -/
theorem isAdequatePenaltyThreshold_iff {yb : P} {rb : ℝ} :
    IsAdequatePenaltyThreshold f σ yb rb ↔ IsAugmentedDualMaximizer f σ yb rb := by
  constructor
  · rintro ⟨hrb, hpen⟩
    refine (isAugmentedDualMaximizer_iff_le hf hl hb hσ hψ hrb).mpr ?_
    rw [parametricValue_zero_eq]
    by_contra hlt
    push_neg at hlt
    have husc := upperSemicontinuousOn_augmentedDualObjective f σ (yb, rb)
      (show (yb, rb) ∈ {q : P × ℝ | 0 < q.2} from hrb) _ hlt
    have ht : Tendsto (fun r : ℝ ↦ (yb, r)) (𝓝[>] rb) (𝓝[{q : P × ℝ | 0 < q.2}] (yb, rb)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact ((Continuous.prodMk_right yb).tendsto rb).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun r hr ↦ (show 0 < r from hrb.trans hr)
    obtain ⟨r, hr, hr'⟩ := ((ht.eventually husc).and self_mem_nhdsWithin).exists
    have he := (hpen r hr').1
    rw [← augmentedDualObjective_eq_iInf_augmentedLagrangian] at he
    exact absurd (he ▸ hr) (lt_irrefl _)
  · intro hmax
    have hrb := hmax.1
    have hge := (isAugmentedDualMaximizer_iff_le hf hl hb hσ hψ hrb).mp hmax
    rw [parametricValue_zero_eq] at hge
    refine ⟨hrb, fun r hr ↦ ?_⟩
    have hr0 : 0 < r := hrb.trans hr
    have hval : (⨅ x, augmentedLagrangian f σ x yb r) = ⨅ x, primalObjective f x := by
      rw [← augmentedDualObjective_eq_iInf_augmentedLagrangian]
      exact le_antisymm (le_iInf fun x ↦ augmentedDualObjective_le_primalObjective hσ.zero x yb r)
        (hge.trans (augmentedDualObjective_mono f hσ.nonneg yb hrb.le hr.le))
    refine ⟨hval.symm, ?_⟩
    ext xb
    rw [mem_argmin_iff, mem_argmin_iff, hval]
    have hlϕ : augmentedLagrangian f σ xb yb r ≤ primalObjective f xb := by
      refine (iInf_le _ (0 : P)).trans ?_
      rw [hσ.zero, mul_zero, add_zero, inner_zero_right, EReal.coe_zero, sub_zero]
      rfl
    have hinfl : (⨅ x, primalObjective f x) ≤ augmentedLagrangian f σ xb yb r := by
      rw [← hval]
      exact iInf_le _ xb
    constructor
    · rintro ⟨hx, hM⟩
      exact ⟨le_antisymm (hlϕ.trans hx.le) hinfl, hM⟩
    · rintro ⟨hx, hM⟩
      refine ⟨le_antisymm ?_ (iInf_le _ xb), hM⟩
      have hMb : (⨅ x, primalObjective f x) ≠ ⊥ := by
        rw [← parametricValue_zero_eq]
        exact ((isProper_parametricValue hl hf.isProper hb).2 0).ne'
      obtain ⟨m, hm⟩ : ∃ m : ℝ, (⨅ x, primalObjective f x) = m :=
        ⟨_, (EReal.coe_toReal hM.ne hMb).symm⟩
      rw [hm] at hx hge ⊢
      by_contra hlt
      push_neg at hlt
      obtain ⟨β, hmβ, hβ⟩ := EReal.exists_between_coe_real hlt
      have hmβr : m < β := EReal.coe_lt_coe_iff.mp hmβ
      have hev1 : ∀ᶠ u in 𝓝 (0 : P), (β : EReal) < f (WithLp.toLp 2 (xb, u)) :=
        hf.lowerSemicontinuous_slice xb 0 β hβ
      have hev2 : ∀ᶠ u in 𝓝 (0 : P), ⟪yb, u⟫_ℝ < (β - m) / 2 := by
        have hc : Continuous fun u : P ↦ ⟪yb, u⟫_ℝ := continuous_const.inner continuous_id
        have h0 : ⟪yb, (0 : P)⟫_ℝ < (β - m) / 2 := by rw [inner_zero_right]; linarith
        exact hc.continuousAt.eventually (Iio_mem_nhds h0)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev1.and hev2)
      obtain ⟨δ, hδ, hsmall⟩ := hσ.exists_lt_of_le hε
      set η := min ((β - m) / 2) (δ * (r - rb)) with hηdef
      have hη : 0 < η := lt_min (by linarith) (mul_pos hδ (by linarith))
      have hlt' : augmentedLagrangian f σ xb yb r < ((m + η : ℝ) : EReal) := by
        rw [hx]
        exact EReal.coe_lt_coe_iff.mpr (by linarith)
      obtain ⟨u, hu⟩ := iInf_lt_iff.mp hlt'
      have hfb : f (WithLp.toLp 2 (xb, u)) ≠ ⊥ := (hf.isProper.2 _).ne'
      rcases augmentedTerm_cases_of_ne_bot hfb (hσ.isProper.2 u).ne' with htop | ⟨a, b, ha, hb'⟩
      · rw [htop r hr0] at hu
        exact absurd hu not_top_lt
      rw [ha, hb', augmentedTerm_coe, EReal.coe_lt_coe_iff] at hu
      have h32 : m ≤ a + rb * b - ⟪yb, u⟫_ℝ := by
        have h : augmentedDualObjective f σ yb rb ≤
            f (WithLp.toLp 2 (xb, u)) + (rb : EReal) * σ u - (⟪yb, u⟫_ℝ : EReal) :=
          (iInf_le _ xb).trans (iInf_le _ u)
        have h' := hge.trans h
        rwa [ha, hb', augmentedTerm_coe, EReal.coe_le_coe_iff] at h'
      have hb0 : 0 ≤ b := by
        have h := hσ.nonneg u
        rw [hb'] at h
        exact_mod_cast h
      have hrr : 0 < r - rb := by linarith
      have he : (r - rb) * b = (a + r * b - ⟪yb, u⟫_ℝ) - (a + rb * b - ⟪yb, u⟫_ℝ) := by ring
      have hbδ' : (r - rb) * b < (r - rb) * δ := by
        rw [he]
        have := min_le_right ((β - m) / 2) (δ * (r - rb))
        nlinarith
      have hbδ : b < δ := lt_of_mul_lt_mul_left hbδ' hrr.le
      have hus : ‖u‖ < ε := hsmall u (by rw [hb']; exact EReal.coe_le_coe_iff.mpr hbδ.le)
      obtain ⟨h1, h2⟩ := hball (show dist u 0 < ε by rwa [dist_zero_right])
      rw [ha] at h1
      have h1' : β < a := EReal.coe_lt_coe_iff.mp h1
      have := min_le_left ((β - m) / 2) (δ * (r - rb))
      nlinarith [mul_nonneg hr0.le hb0]

/-- **Theorem 11.61**: `ȳ` supports an exact penalty representation exactly when
`(ȳ,r̄)` maximizes the augmented dual objective for some `r̄`. -/
theorem supportsExactPenaltyRepresentation_iff_exists_maximizer {yb : P} :
    SupportsExactPenaltyRepresentation f σ yb ↔ ∃ rb, IsAugmentedDualMaximizer f σ yb rb :=
  exists_congr fun _ ↦ isAdequatePenaltyThreshold_iff hf hl hb hσ hψ

/-- **Theorem 11.61** (adapted): for a feasible problem, `ȳ` supports an exact
penalty representation exactly when the local criterion 11(33) holds. -/
theorem supportsExactPenaltyRepresentation_iff
    (hfeas : (⨅ x, primalObjective f x) < ⊤) {yb : P} :
    SupportsExactPenaltyRepresentation f σ yb ↔
      ∃ W ∈ 𝓝 (0 : P), ∃ rh : ℝ, 0 < rh ∧ ∀ u ∈ W,
        parametricValue f 0 + (⟪yb, u⟫_ℝ : EReal) ≤ parametricValue f u + (rh : EReal) * σ u := by
  have hpb : ∀ u, parametricValue f u ≠ ⊥ :=
    fun u ↦ ((isProper_parametricValue hl hf.isProper hb).2 u).ne'
  constructor
  · rintro ⟨rb, hrb⟩
    have hmax := (isAdequatePenaltyThreshold_iff hf hl hb hσ hψ).mp hrb
    exact ⟨univ, univ_mem, rb, hmax.1,
      fun u _ ↦ (isAugmentedDualMaximizer_iff hf hl hb hσ hψ hmax.1).mp hmax u⟩
  · rintro ⟨W, hW, rh, hrh, hloc⟩
    obtain ⟨yt, rt, hrt, hα⟩ := hψ
    have hweak : augmentedDualObjective f σ yt rt ≤ ⨅ x, primalObjective f x :=
      le_iInf fun x ↦ augmentedDualObjective_le_primalObjective hσ.zero x yt rt
    have hMb : (⨅ x, primalObjective f x) ≠ ⊥ := by
      rw [← parametricValue_zero_eq]
      exact hpb 0
    obtain ⟨m, hm⟩ : ∃ m : ℝ, (⨅ x, primalObjective f x) = m :=
      ⟨_, (EReal.coe_toReal hfeas.ne hMb).symm⟩
    obtain ⟨α, hα'⟩ : ∃ α : ℝ, augmentedDualObjective f σ yt rt = α :=
      ⟨_, (EReal.coe_toReal (hweak.trans_lt hfeas).ne hα.ne').symm⟩
    have hαm : α ≤ m := by
      have h := hweak
      rw [hα', hm] at h
      exact EReal.coe_le_coe_iff.mp h
    have hαu := (le_augmentedDualObjective_iff hσ hpb (α : EReal) hrt).mp hα'.ge
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
    obtain ⟨c, hc, hgrowth⟩ := hσ.exists_linear_growth hε
    set K := ((m - α) / ε + ‖yb - yt‖) / c with hK
    have hK0 : 0 ≤ K := div_nonneg (add_nonneg (div_nonneg (by linarith) hε.le)
      (norm_nonneg _)) hc.le
    set rb := max rh (rt + K) with hrbdef
    have hrb : 0 < rb := hrh.trans_le (le_max_left _ _)
    refine ⟨rb, (isAdequatePenaltyThreshold_iff hf hl hb hσ ⟨yt, rt, hrt, hα⟩).mpr
      ((isAugmentedDualMaximizer_iff hf hl hb hσ ⟨yt, rt, hrt, hα⟩ hrb).mpr fun u ↦ ?_)⟩
    by_cases hu : ‖u‖ < ε
    · exact (hloc u (hball (by rwa [mem_ball, dist_zero_right]))).trans
        (add_le_add_right (ereal_coe_mul_le_coe_mul (hσ.nonneg u) hrh.le (le_max_left _ _)) _)
    push_neg at hu
    rw [parametricValue_zero_eq, hm]
    induction hσu : σ u using EReal.rec with
    | bot => exact absurd hσu (hσ.isProper.2 u).ne'
    | top =>
      rw [EReal.coe_mul_top_of_pos hrb, EReal.add_top_of_ne_bot (hpb u)]
      exact le_top
    | coe b =>
      have hαu' := hαu u
      rw [hσu] at hαu'
      induction hpu : parametricValue f u using EReal.rec with
      | bot => exact absurd hpu (hpb u)
      | top =>
        rw [← EReal.coe_mul, EReal.top_add_coe]
        exact le_top
      | coe a =>
        rw [hpu, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hαu'
        rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
        have hgb := hgrowth u hu
        rw [hσu, EReal.coe_le_coe_iff] at hgb
        have hb0 : 0 ≤ b := le_trans (by positivity) hgb
        have h1 : K * (c * ‖u‖) ≤ K * b := mul_le_mul_of_nonneg_left hgb hK0
        have h2 : K * (c * ‖u‖) = ((m - α) / ε + ‖yb - yt‖) * ‖u‖ := by
          rw [hK]
          field_simp
        have h3 : m - α ≤ (m - α) / ε * ‖u‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hε]
          nlinarith
        have h4 : ⟪yb - yt, u⟫_ℝ ≤ ‖yb - yt‖ * ‖u‖ := real_inner_le_norm _ _
        have h5 : ⟪yb, u⟫_ℝ = ⟪yt, u⟫_ℝ + ⟪yb - yt, u⟫_ℝ := by rw [inner_sub_left]; ring
        have h6 : (rt + K) * b ≤ rb * b := mul_le_mul_of_nonneg_right (le_max_right _ _) hb0
        nlinarith

end ExactPenalty

end
end RW
