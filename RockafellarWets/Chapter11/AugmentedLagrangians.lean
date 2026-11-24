/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Augmented Lagrangians

Definition 11.55 and the structural properties in Exercise 11.56. On the open
half-space `r > 0` every term `f(x,u) + rσ(u) - ⟨y,u⟩` is identically `∞`,
identically `-∞`, or a real affine function of `(y,r)`, so infima of such
terms are concave and upper semicontinuous in `(y,r)`. An augmenting function
grows at least linearly away from the origin, which drives the nonconvex
duality theory of Section 11K.
-/
import RockafellarWets.Chapter11.Lagrangians
import RockafellarWets.Chapter10.PLQCalculus

open Set Filter Topology Metric
open scoped InnerProductSpace
namespace RW
noncomputable section

variable {E P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- **Definition 11.55**, augmenting functions: proper, lsc and convex, with
minimum value `0` attained only at the origin. -/
structure IsAugmentingFunction (σ : P → EReal) : Prop where
  isProper : IsProper σ
  lowerSemicontinuous : LowerSemicontinuous σ
  convex : Convex ℝ (epigraph σ)
  zero : σ 0 = 0
  pos : ∀ u, u ≠ 0 → 0 < σ u

theorem IsAugmentingFunction.nonneg {σ : P → EReal} (hσ : IsAugmentingFunction σ) (u : P) :
    0 ≤ σ u := by
  by_cases hu : u = 0
  · rw [hu, hσ.zero]
  · exact (hσ.pos u hu).le

/-- The defining conditions `min σ = 0` and `argmin σ = {0}` of Definition 11.55. -/
theorem isAugmentingFunction_iff {σ : P → EReal} :
    IsAugmentingFunction σ ↔ IsProper σ ∧ LowerSemicontinuous σ ∧ Convex ℝ (epigraph σ) ∧
      (⨅ u, σ u) = 0 ∧ argmin σ = {0} := by
  constructor
  · intro hσ
    have hinf : (⨅ u, σ u) = 0 :=
      le_antisymm ((iInf_le σ 0).trans hσ.zero.le) (le_iInf hσ.nonneg)
    refine ⟨hσ.isProper, hσ.lowerSemicontinuous, hσ.convex, hinf, ?_⟩
    ext u
    rw [mem_argmin_iff, hinf, mem_singleton_iff]
    constructor
    · rintro ⟨hu, -⟩
      by_contra hne
      exact (hσ.pos u hne).ne' hu
    · rintro rfl
      exact ⟨hσ.zero, EReal.zero_lt_top⟩
  · rintro ⟨hp, hl, hc, hinf, harg⟩
    have h0 : (0 : P) ∈ argmin σ := harg ▸ mem_singleton 0
    rw [mem_argmin_iff, hinf] at h0
    refine ⟨hp, hl, hc, h0.1, fun u hu ↦ ?_⟩
    have hle : 0 ≤ σ u := hinf ▸ iInf_le σ u
    refine lt_of_le_of_ne hle fun he ↦ hu ?_
    have hmem : u ∈ argmin σ := by
      rw [mem_argmin_iff, hinf]
      exact ⟨he.symm, EReal.zero_lt_top⟩
    rw [harg] at hmem
    exact hmem

/-- **Definition 11.55**, the augmented Lagrangian
`l̄(x,y,r) = inf_u {f(x,u) + rσ(u) - ⟨y,u⟩}`. -/
def augmentedLagrangian (f : WithLp 2 (E × P) → EReal) (σ : P → EReal) (x : E) (y : P)
    (r : ℝ) : EReal :=
  ⨅ u : P, f (WithLp.toLp 2 (x, u)) + (r : EReal) * σ u - (⟪y, u⟫_ℝ : EReal)

/-- **Definition 11.55**, the augmented dual objective
`ψ̄(y,r) = inf_{x,u} {f(x,u) + rσ(u) - ⟨y,u⟩}`. -/
def augmentedDualObjective (f : WithLp 2 (E × P) → EReal) (σ : P → EReal) (y : P)
    (r : ℝ) : EReal :=
  ⨅ x : E, ⨅ u : P, f (WithLp.toLp 2 (x, u)) + (r : EReal) * σ u - (⟪y, u⟫_ℝ : EReal)

theorem augmentedDualObjective_eq_iInf_augmentedLagrangian (f : WithLp 2 (E × P) → EReal)
    (σ : P → EReal) (y : P) (r : ℝ) :
    augmentedDualObjective f σ y r = ⨅ x, augmentedLagrangian f σ x y r := rfl

/-- The integrand `f_{rσ}(x,u) = f(x,u) + rσ(u)` from the discussion after 11.55. -/
def augmentedIntegrand (f : WithLp 2 (E × P) → EReal) (σ : P → EReal) (r : ℝ) :
    WithLp 2 (E × P) → EReal :=
  fun q ↦ f q + (r : EReal) * σ q.snd

/-- The augmented Lagrangian is the ordinary Lagrangian of `f_{rσ}`. -/
theorem augmentedLagrangian_eq_lagrangian (f : WithLp 2 (E × P) → EReal) (σ : P → EReal)
    (x : E) (y : P) (r : ℝ) :
    augmentedLagrangian f σ x y r = lagrangian (augmentedIntegrand f σ r) x y := rfl

omit [InnerProductSpace ℝ P] in
/-- The augmented parameterization still represents the primal problem. -/
theorem primalObjective_augmentedIntegrand (f : WithLp 2 (E × P) → EReal) {σ : P → EReal}
    (h0 : σ 0 = 0) (r : ℝ) : primalObjective (augmentedIntegrand f σ r) = primalObjective f := by
  funext x
  change f (WithLp.toLp 2 (x, 0)) + (r : EReal) * σ 0 = f (WithLp.toLp 2 (x, 0))
  rw [h0, mul_zero, add_zero]

section Terms

/-- On `r > 0` an augmented term is identically `∞`, identically `-∞`, or a
real affine function of `(r,t)`. -/
theorem augmentedTerm_cases (A B : EReal) :
    (∀ r : ℝ, 0 < r → ∀ t : ℝ, A + (r : EReal) * B - (t : EReal) = ⊤) ∨
    (∀ r : ℝ, 0 < r → ∀ t : ℝ, A + (r : EReal) * B - (t : EReal) = ⊥) ∨
    ∃ a b : ℝ, ∀ r t : ℝ, A + (r : EReal) * B - (t : EReal) = ((a + r * b - t : ℝ) : EReal) := by
  induction A using EReal.rec with
  | bot => exact .inr (.inl fun r _ t ↦ by simp)
  | coe a =>
    induction B using EReal.rec with
    | bot => exact .inr (.inl fun r hr t ↦ by rw [EReal.coe_mul_bot_of_pos hr]; simp)
    | coe b => exact .inr (.inr ⟨a, b, fun r t ↦ by norm_cast⟩)
    | top => exact .inl fun r hr t ↦ by rw [EReal.coe_mul_top_of_pos hr]; simp
  | top =>
    induction B using EReal.rec with
    | bot => exact .inr (.inl fun r hr t ↦ by rw [EReal.coe_mul_bot_of_pos hr]; simp)
    | coe b => exact .inl fun r _ t ↦ by rw [← EReal.coe_mul, EReal.top_add_coe]; simp
    | top => exact .inl fun r hr t ↦ by rw [EReal.coe_mul_top_of_pos hr]; simp

private theorem convex_augmentedAffine (a b : ℝ) (u : P) :
    Convex ℝ {q : (P × ℝ) × ℝ | 0 < q.1.2 ∧ q.2 ≤ a + q.1.2 * b - ⟪q.1.1, u⟫_ℝ} := by
  rintro ⟨⟨y₁, r₁⟩, α₁⟩ ⟨h₁, h₁'⟩ ⟨⟨y₂, r₂⟩, α₂⟩ ⟨h₂, h₂'⟩ s t hs ht hst
  simp only [mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h₁ h₁' h₂ h₂' ⊢
  refine ⟨?_, ?_⟩
  · rcases hs.eq_or_lt with rfl | hs'
    · rw [zero_add] at hst
      subst hst
      simpa using h₂
    · exact add_pos_of_pos_of_nonneg (mul_pos hs' h₁) (mul_nonneg ht h₂.le)
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have e1 : s * α₁ ≤ s * (a + r₁ * b - ⟪y₁, u⟫_ℝ) := mul_le_mul_of_nonneg_left h₁' hs
    have e2 : t * α₂ ≤ t * (a + r₂ * b - ⟪y₂, u⟫_ℝ) := mul_le_mul_of_nonneg_left h₂' ht
    have e3 : a = s * a + t * a := by rw [← add_mul, hst, one_mul]
    nlinarith

private theorem convex_posHalf :
    Convex ℝ {q : (P × ℝ) × ℝ | 0 < q.1.2} := by
  rintro ⟨⟨y₁, r₁⟩, α₁⟩ h₁ ⟨⟨y₂, r₂⟩, α₂⟩ h₂ s t hs ht hst
  simp only [mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h₁ h₂ ⊢
  rcases hs.eq_or_lt with rfl | hs'
  · rw [zero_add] at hst
    subst hst
    simpa using h₂
  · exact add_pos_of_pos_of_nonneg (mul_pos hs' h₁) (mul_nonneg ht h₂.le)

/-- An infimum of augmented terms is concave in `(y,r)` on `r > 0`. -/
theorem convex_hypograph_iInf_augmentedTerms {ι : Sort*} (A B : ι → EReal) (c : ι → P) :
    Convex ℝ {q : (P × ℝ) × ℝ | 0 < q.1.2 ∧
      (q.2 : EReal) ≤ ⨅ i, A i + (q.1.2 : EReal) * B i - (⟪q.1.1, c i⟫_ℝ : EReal)} := by
  have hset : {q : (P × ℝ) × ℝ | 0 < q.1.2 ∧
      (q.2 : EReal) ≤ ⨅ i, A i + (q.1.2 : EReal) * B i - (⟪q.1.1, c i⟫_ℝ : EReal)} =
      {q : (P × ℝ) × ℝ | 0 < q.1.2} ∩ ⋂ i, {q : (P × ℝ) × ℝ | 0 < q.1.2 ∧
        (q.2 : EReal) ≤ A i + (q.1.2 : EReal) * B i - (⟪q.1.1, c i⟫_ℝ : EReal)} := by
    ext q
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter, le_iInf_iff]
    constructor
    · rintro ⟨h0, h⟩
      exact ⟨h0, fun i ↦ ⟨h0, h i⟩⟩
    · rintro ⟨h0, h⟩
      exact ⟨h0, fun i ↦ (h i).2⟩
  rw [hset]
  refine convex_posHalf.inter (convex_iInter fun i ↦ ?_)
  rcases augmentedTerm_cases (A i) (B i) with h | h | ⟨a, b, h⟩
  · convert (convex_posHalf (P := P)) using 1
    ext q
    simp only [mem_setOf_eq]
    exact ⟨fun hq ↦ hq.1, fun hq ↦ ⟨hq, by rw [h _ hq]; exact le_top⟩⟩
  · convert (convex_empty : Convex ℝ (∅ : Set ((P × ℝ) × ℝ))) using 1
    ext q
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hq hle
    rw [h _ hq] at hle
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)
  · convert convex_augmentedAffine a b (c i) using 1
    ext q
    simp only [mem_setOf_eq, h, EReal.coe_le_coe_iff]

/-- An infimum of augmented terms is upper semicontinuous in `(y,r)` on `r > 0`. -/
theorem upperSemicontinuousOn_iInf_augmentedTerms {ι : Sort*} (A B : ι → EReal) (c : ι → P) :
    UpperSemicontinuousOn
      (fun q : P × ℝ ↦ ⨅ i, A i + (q.2 : EReal) * B i - (⟪q.1, c i⟫_ℝ : EReal))
      {q | 0 < q.2} := by
  apply upperSemicontinuousOn_iInf
  intro i
  rcases augmentedTerm_cases (A i) (B i) with h | h | ⟨a, b, h⟩
  · intro q hq y hy
    dsimp only at hy
    rw [h q.2 hq] at hy
    exact absurd hy not_top_lt
  · intro q hq y hy
    dsimp only at hy
    rw [h q.2 hq] at hy
    filter_upwards [self_mem_nhdsWithin] with q' hq'
    rw [h q'.2 hq']
    exact hy
  · have he : (fun q : P × ℝ ↦ A i + (q.2 : EReal) * B i - (⟪q.1, c i⟫_ℝ : EReal)) =
        fun q ↦ ((a + q.2 * b - ⟪q.1, c i⟫_ℝ : ℝ) : EReal) := funext fun q ↦ h _ _
    rw [he]
    exact (continuous_coe_real_ereal.comp (by fun_prop)).upperSemicontinuous.upperSemicontinuousOn _

end Terms

/-- Scaling a nonnegative extended real by a larger nonnegative factor. -/
theorem ereal_coe_mul_le_coe_mul {a : EReal} (ha : 0 ≤ a) {r r' : ℝ} (hr : 0 ≤ r)
    (hrr : r ≤ r') : (r : EReal) * a ≤ (r' : EReal) * a := by
  induction a using EReal.rec with
  | bot => exact absurd ha (by simp)
  | coe a =>
    norm_cast
    exact mul_le_mul_of_nonneg_right hrr (EReal.coe_nonneg.mp ha)
  | top =>
    rcases hr.eq_or_lt with rfl | hr'
    · rw [EReal.coe_zero, zero_mul]
      exact EReal.mul_nonneg (EReal.coe_nonneg.mpr (hr.trans hrr)) le_top
    · rw [EReal.coe_mul_top_of_pos hr', EReal.coe_mul_top_of_pos (hr'.trans_le hrr)]

section Properties

variable (f : WithLp 2 (E × P) → EReal) (σ : P → EReal)

/-- **Exercise 11.56**: `l̄(x,y,r)` is concave in `(y,r)` on `r > 0`. -/
theorem convex_hypograph_augmentedLagrangian (x : E) :
    Convex ℝ {q : (P × ℝ) × ℝ | 0 < q.1.2 ∧
      (q.2 : EReal) ≤ augmentedLagrangian f σ x q.1.1 q.1.2} :=
  convex_hypograph_iInf_augmentedTerms (fun u ↦ f (WithLp.toLp 2 (x, u))) σ id

/-- **Exercise 11.56**: `l̄(x,y,r)` is upper semicontinuous in `(y,r)` on `r > 0`. -/
theorem upperSemicontinuousOn_augmentedLagrangian (x : E) :
    UpperSemicontinuousOn (fun q : P × ℝ ↦ augmentedLagrangian f σ x q.1 q.2) {q | 0 < q.2} :=
  upperSemicontinuousOn_iInf_augmentedTerms (fun u ↦ f (WithLp.toLp 2 (x, u))) σ id

/-- **Exercise 11.56**: `l̄(x,y,r)` is nondecreasing in `r ≥ 0`. -/
theorem augmentedLagrangian_mono {σ : P → EReal} (hσ : ∀ u, 0 ≤ σ u) (x : E) (y : P)
    {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') :
    augmentedLagrangian f σ x y r ≤ augmentedLagrangian f σ x y r' :=
  iInf_mono fun u ↦ EReal.sub_le_sub
    (add_le_add_right (ereal_coe_mul_le_coe_mul (hσ u) hr hrr) _) le_rfl

theorem augmentedDualObjective_eq_iInf_prod (y : P) (r : ℝ) :
    augmentedDualObjective f σ y r =
      ⨅ p : E × P, f (WithLp.toLp 2 p) + (r : EReal) * σ p.2 - (⟪y, p.2⟫_ℝ : EReal) := by
  rw [augmentedDualObjective, iInf_prod]

/-- **Exercise 11.56**: `ψ̄(y,r)` is concave in `(y,r)` on `r > 0`. -/
theorem convex_hypograph_augmentedDualObjective :
    Convex ℝ {q : (P × ℝ) × ℝ | 0 < q.1.2 ∧
      (q.2 : EReal) ≤ augmentedDualObjective f σ q.1.1 q.1.2} := by
  simp only [augmentedDualObjective_eq_iInf_prod]
  exact convex_hypograph_iInf_augmentedTerms (fun p : E × P ↦ f (WithLp.toLp 2 p))
    (fun p ↦ σ p.2) (fun p ↦ p.2)

/-- **Exercise 11.56**: `ψ̄(y,r)` is upper semicontinuous in `(y,r)` on `r > 0`. -/
theorem upperSemicontinuousOn_augmentedDualObjective :
    UpperSemicontinuousOn (fun q : P × ℝ ↦ augmentedDualObjective f σ q.1 q.2) {q | 0 < q.2} := by
  simp only [augmentedDualObjective_eq_iInf_prod]
  exact upperSemicontinuousOn_iInf_augmentedTerms (fun p : E × P ↦ f (WithLp.toLp 2 p))
    (fun p ↦ σ p.2) (fun p ↦ p.2)

/-- **Exercise 11.56**: `ψ̄(y,r)` is nondecreasing in `r ≥ 0`. -/
theorem augmentedDualObjective_mono {σ : P → EReal} (hσ : ∀ u, 0 ≤ σ u) (y : P)
    {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') :
    augmentedDualObjective f σ y r ≤ augmentedDualObjective f σ y r' :=
  iInf_mono fun x ↦ augmentedLagrangian_mono f hσ x y hr hrr

end Properties

/-- A positive multiple of a function with convex epigraph has convex epigraph. -/
theorem convex_epigraph_coe_mul {g : P → EReal} (hg : Convex ℝ (epigraph g)) {r : ℝ}
    (hr : 0 < r) : Convex ℝ (epigraph (fun u ↦ (r : EReal) * g u)) := by
  have hiff : ∀ (a : EReal) (b : ℝ), (r : EReal) * a ≤ (b : EReal) ↔ a ≤ ((b / r : ℝ) : EReal) := by
    intro a b
    induction a using EReal.rec with
    | bot => simp [EReal.coe_mul_bot_of_pos hr]
    | coe a =>
      norm_cast
      rw [le_div_iff₀ hr, mul_comm]
    | top => simp [EReal.coe_mul_top_of_pos hr]
  rintro ⟨u₁, a₁⟩ h₁ ⟨u₂, a₂⟩ h₂ s t hs ht hst
  change (r : EReal) * g u₁ ≤ (a₁ : EReal) at h₁
  change (r : EReal) * g u₂ ≤ (a₂ : EReal) at h₂
  rw [hiff] at h₁ h₂
  have hh := hg (show (u₁, a₁ / r) ∈ epigraph g from h₁) (show (u₂, a₂ / r) ∈ epigraph g from h₂)
    hs ht hst
  change g (s • u₁ + t • u₂) ≤ ((s * (a₁ / r) + t * (a₂ / r) : ℝ) : EReal) at hh
  change (r : EReal) * g (s • u₁ + t • u₂) ≤ ((s * a₁ + t * a₂ : ℝ) : EReal)
  rw [hiff]
  have he : s * (a₁ / r) + t * (a₂ / r) = (s * a₁ + t * a₂) / r := by ring
  rw [he] at hh
  exact hh

section ConvexInX

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P]

/-- Joint convexity of `f` passes to the augmented integrand. -/
theorem convex_epigraph_augmentedIntegrand {f : WithLp 2 (E × P) → EReal}
    (hfc : Convex ℝ (epigraph f)) (hfb : ∀ q, f q ≠ ⊥) {σ : P → EReal}
    (hσ : IsAugmentingFunction σ) {r : ℝ} (hr : 0 < r) :
    Convex ℝ (epigraph (augmentedIntegrand f σ r)) := by
  have hs : Convex ℝ (epigraph (fun q : WithLp 2 (E × P) ↦ (r : EReal) * σ q.snd)) := by
    have hm := convex_epigraph_coe_mul hσ.convex hr
    rintro ⟨q₁, a₁⟩ h₁ ⟨q₂, a₂⟩ h₂ s t hs ht hst
    exact hm (show (q₁.snd, a₁) ∈ epigraph _ from h₁) (show (q₂.snd, a₂) ∈ epigraph _ from h₂)
      hs ht hst
  apply convex_epigraph_add_of_ne_bot hfc hs hfb
  intro q
  have h0 := hσ.nonneg q.snd
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0)
    (by rw [EReal.coe_zero]; exact EReal.mul_nonneg (EReal.coe_nonneg.mpr hr.le) h0)

/-- **Exercise 11.56**: joint convexity of `f(x,u)` makes `l̄(x,y,r)` convex in `x`. -/
theorem convex_epigraph_augmentedLagrangian {f : WithLp 2 (E × P) → EReal}
    (hfc : Convex ℝ (epigraph f)) (hfb : ∀ q, f q ≠ ⊥) {σ : P → EReal}
    (hσ : IsAugmentingFunction σ) {r : ℝ} (hr : 0 < r) (y : P) :
    Convex ℝ (epigraph (fun x ↦ augmentedLagrangian f σ x y r)) :=
  convex_epigraph_lagrangian_of_convex (convex_epigraph_augmentedIntegrand hfc hfb hσ hr) y

end ConvexInX

section Growth

variable [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ P] in
/-- Convexity and `σ(0) = 0` give `σ(tu) ≤ tσ(u)` for `t ∈ [0,1]`. -/
theorem IsAugmentingFunction.smul_le {σ : P → EReal} (hσ : IsAugmentingFunction σ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (u : P) : σ (t • u) ≤ (t : EReal) * σ u := by
  induction h : σ u using EReal.rec with
  | bot => exact absurd h (hσ.isProper.2 u).ne'
  | top =>
    rcases ht0.eq_or_lt with rfl | ht
    · simp [hσ.zero]
    · rw [EReal.coe_mul_top_of_pos ht]
      exact le_top
  | coe a =>
    have hu : (u, a) ∈ epigraph σ := show (a : EReal) ≥ σ u from h.le
    have h0 : ((0 : P), (0 : ℝ)) ∈ epigraph σ :=
      show ((0 : ℝ) : EReal) ≥ σ 0 by rw [hσ.zero]; rfl
    have hh := hσ.convex hu h0 ht0 (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)
    change σ (t • u + (1 - t) • (0 : P)) ≤ ((t * a + (1 - t) * 0 : ℝ) : EReal) at hh
    rw [smul_zero, add_zero, mul_zero, add_zero] at hh
    rw [← EReal.coe_mul]
    exact hh

/-- An augmenting function grows at least linearly away from the origin. -/
theorem IsAugmentingFunction.exists_linear_growth {σ : P → EReal}
    (hσ : IsAugmentingFunction σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ u : P, ε ≤ ‖u‖ → ((c * ‖u‖ : ℝ) : EReal) ≤ σ u := by
  by_cases hS : (sphere (0 : P) ε).Nonempty
  · obtain ⟨v, hv, hmin⟩ := (hσ.lowerSemicontinuous.lowerSemicontinuousOn _).exists_isMinOn hS
      (isCompact_sphere 0 ε)
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [mem_sphere_zero_iff_norm, norm_zero] at hv
      exact hε.ne hv
    obtain ⟨m, hm0, hmv⟩ : ∃ m : ℝ, 0 < m ∧ (m : EReal) ≤ σ v := by
      have hpos := hσ.pos v hv0
      induction h : σ v using EReal.rec with
      | bot => rw [h] at hpos; exact absurd hpos not_lt_bot
      | coe a => exact ⟨a, by rw [h] at hpos; exact_mod_cast hpos, le_rfl⟩
      | top => exact ⟨1, one_pos, le_top⟩
    refine ⟨m / ε, div_pos hm0 hε, fun u hu ↦ ?_⟩
    have hu0 : 0 < ‖u‖ := hε.trans_le hu
    set t := ε / ‖u‖ with ht
    have ht0 : 0 < t := div_pos hε hu0
    have ht1 : t ≤ 1 := (div_le_one hu0).mpr hu
    have hw : t • u ∈ sphere (0 : P) ε := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ht,
        div_mul_cancel₀ _ hu0.ne']
    have h1 : (m : EReal) ≤ (t : EReal) * σ u :=
      hmv.trans ((isMinOn_iff.mp hmin _ hw).trans (hσ.smul_le ht0.le ht1 u))
    have hgoal : m / ε * ‖u‖ = m / t := by
      rw [ht]
      field_simp
    rw [hgoal]
    induction h : σ u using EReal.rec with
    | bot => exact absurd h (hσ.isProper.2 u).ne'
    | top => exact le_top
    | coe a =>
      rw [h, ← EReal.coe_mul, EReal.coe_le_coe_iff] at h1
      exact EReal.coe_le_coe_iff.mpr ((div_le_iff₀ ht0).mpr (by linarith))
  · refine ⟨1, one_pos, fun u hu ↦ absurd ?_ hS⟩
    have hu0 : 0 < ‖u‖ := hε.trans_le hu
    refine ⟨(ε / ‖u‖) • u, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hε hu0),
      div_mul_cancel₀ _ hu0.ne']

/-- Small values of an augmenting function occur only near the origin. -/
theorem IsAugmentingFunction.exists_lt_of_le {σ : P → EReal} (hσ : IsAugmentingFunction σ)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ u : P, σ u ≤ (δ : EReal) → ‖u‖ < ε := by
  obtain ⟨c, hc, hgrowth⟩ := hσ.exists_linear_growth hε
  refine ⟨c * ε / 2, half_pos (mul_pos hc hε), fun u hu ↦ ?_⟩
  by_contra hlt
  push_neg at hlt
  have h := (hgrowth u hlt).trans hu
  rw [EReal.coe_le_coe_iff] at h
  have : c * ε ≤ c * ‖u‖ := mul_le_mul_of_nonneg_left hlt hc.le
  linarith [mul_pos hc hε]

end Growth

end
end RW
