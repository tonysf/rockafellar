/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: convexity and calculus of subsmooth functions

* **Theorem 10.33**: a finite convex function on an open convex set is lower-`C^∞`, with a
  local representation by affine functions `x ↦ g(w) + ⟪v, x - w⟫`, `(w, v)` ranging over the
  compact set of subgradient pairs over a closed ball (`ConvexOn.isLowerCOn`); and `f` is
  lower-`C²` on `O` iff around each point `f = g - h` with `g` finite convex and `h` of class
  `C²`, where `h` may be taken to be `ρ|·|²` (`isLowerCOn_two_iff_locally_convex_sub`).
* **Exercise 10.35(a)**: nonnegative combinations of lower-`Cᵏ` functions are lower-`Cᵏ`
  (`IsLowerCOn.add`, `IsLowerCOn.const_mul`, `isLowerCOn_sum`).
* **Exercise 10.35(b)**: `g ∘ F` is lower-`C¹` on `F⁻¹(O)` when `g` is lower-`C¹` on `O` and
  `F` is `C¹` (`IsLowerCOn.comp_one`), and lower-`C²` when `g` is lower-`C²` and `F` is `C²`
  (`IsLowerCOn.comp_two`, through the quadratic representations of 10.33).
-/

import RockafellarWets.Chapter10.SubsmoothQuadratic
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter9.ConvexLipschitzBounds

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Elementary operations on representations -/

namespace LowerRepresentation

variable {k : ℕ∞}

omit [FiniteDimensional ℝ E] in
/-- A representation of `f` on `V` represents every `g` agreeing with `f` on `V`. -/
def congr {f g : E → ℝ} {V : Set E} (R : LowerRepresentation k f V) (h : ∀ x ∈ V, f x = g x) :
    LowerRepresentation k g V :=
  LowerRepresentation.mk R.T R.F R.contDiffOn R.continuousOn_iteratedFDeriv
    (fun t x hx ↦ (h x hx) ▸ R.le t x hx) (fun x hx ↦ (h x hx) ▸ R.exists_eq x hx)

omit [FiniteDimensional ℝ E] in
/-- Restriction of a representation to a smaller set. -/
def restrict {f : E → ℝ} {V W : Set E} (R : LowerRepresentation k f V) (hW : W ⊆ V) :
    LowerRepresentation k f W :=
  LowerRepresentation.mk R.T R.F (fun t ↦ (R.contDiffOn t).mono hW)
    (fun j hj ↦ (R.continuousOn_iteratedFDeriv j hj).mono (prod_mono Subset.rfl hW))
    (fun t x hx ↦ R.le t x (hW hx)) (fun x hx ↦ R.exists_eq x (hW hx))

omit [FiniteDimensional ℝ E] in
private theorem contDiffAt_of_le {f : E → ℝ} {V : Set E} (R : LowerRepresentation k f V)
    (hV : IsOpen V) (t : R.T) {x : E} (hx : x ∈ V) {j : ℕ} (hj : (j : ℕ∞) ≤ k) :
    ContDiffAt ℝ j (R.F t) x :=
  ((R.contDiffOn t).contDiffAt (hV.mem_nhds hx)).of_le (by exact_mod_cast hj)

omit [FiniteDimensional ℝ E] in
/-- Sum of two representations, indexed by the product of the index spaces. -/
def add {f₁ f₂ : E → ℝ} {V₁ V₂ : Set E} (R₁ : LowerRepresentation k f₁ V₁)
    (R₂ : LowerRepresentation k f₂ V₂) (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) :
    LowerRepresentation k (fun x ↦ f₁ x + f₂ x) (V₁ ∩ V₂) :=
  LowerRepresentation.mk (R₁.T × R₂.T) (fun s x ↦ R₁.F s.1 x + R₂.F s.2 x)
    (fun s ↦ ((R₁.contDiffOn s.1).mono inter_subset_left).add
      ((R₂.contDiffOn s.2).mono inter_subset_right))
    (fun j hj ↦ by
      have h1 : ContinuousOn (fun p : (R₁.T × R₂.T) × E ↦ iteratedFDeriv ℝ j (R₁.F p.1.1) p.2)
          (univ ×ˢ (V₁ ∩ V₂)) :=
        (R₁.continuousOn_iteratedFDeriv j hj).comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd).continuousOn
          (fun p hp ↦ ⟨trivial, hp.2.1⟩)
      have h2 : ContinuousOn (fun p : (R₁.T × R₂.T) × E ↦ iteratedFDeriv ℝ j (R₂.F p.1.2) p.2)
          (univ ×ˢ (V₁ ∩ V₂)) :=
        (R₂.continuousOn_iteratedFDeriv j hj).comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd).continuousOn
          (fun p hp ↦ ⟨trivial, hp.2.2⟩)
      refine (h1.add h2).congr fun p hp ↦ ?_
      exact iteratedFDeriv_add_apply' (R₁.contDiffAt_of_le hV₁ p.1.1 hp.2.1 hj)
        (R₂.contDiffAt_of_le hV₂ p.1.2 hp.2.2 hj))
    (fun s x hx ↦ add_le_add (R₁.le s.1 x hx.1) (R₂.le s.2 x hx.2))
    (fun x hx ↦ by
      obtain ⟨t₁, h1⟩ := R₁.exists_eq x hx.1
      obtain ⟨t₂, h2⟩ := R₂.exists_eq x hx.2
      exact ⟨(t₁, t₂), by simp only [h1, h2]⟩)

omit [FiniteDimensional ℝ E] in
/-- A nonnegative multiple of a representation. -/
def constMul {f : E → ℝ} {V : Set E} (R : LowerRepresentation k f V) (hV : IsOpen V) {c : ℝ}
    (hc : 0 ≤ c) : LowerRepresentation k (fun x ↦ c * f x) V :=
  LowerRepresentation.mk R.T (fun t x ↦ c * R.F t x)
    (fun t ↦ contDiffOn_const.mul (R.contDiffOn t))
    (fun j hj ↦ by
      refine ((R.continuousOn_iteratedFDeriv j hj).const_smul c).congr fun p hp ↦ ?_
      exact iteratedFDeriv_const_smul_apply' (a := c) (R.contDiffAt_of_le hV p.1 hp.2 hj))
    (fun t x hx ↦ mul_le_mul_of_nonneg_left (R.le t x hx) hc)
    (fun x hx ↦ by
      obtain ⟨t, ht⟩ := R.exists_eq x hx
      exact ⟨t, by simp only [ht]⟩)

omit [FiniteDimensional ℝ E] in
/-- A representation whose functions are `x ↦ Q(c t, x)` for a jointly smooth `Q` and a
continuous coefficient map `c`. -/
def ofParam {n : ℕ∞} {f : E → ℝ} {V : Set E} {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (T : Type u) [TopologicalSpace T] [CompactSpace T] (c : T → P)
    (hc : Continuous c) (Q : P × E → ℝ) (hQ : ContDiff ℝ n Q)
    (hle : ∀ t, ∀ x ∈ V, Q (c t, x) ≤ f x) (heq : ∀ x ∈ V, ∃ t, Q (c t, x) = f x) :
    LowerRepresentation n f V :=
  LowerRepresentation.mk T (fun t x ↦ Q (c t, x))
    (fun t ↦ (hQ.comp (contDiff_const.prodMk contDiff_id)).contDiffOn)
    (fun j hj ↦ ((continuous_iteratedFDeriv_param hQ (by exact_mod_cast hj)).comp
      (hc.prodMap continuous_id)).continuousOn)
    hle heq

end LowerRepresentation

omit [FiniteDimensional ℝ E] in
theorem IsLowerCOn.congr {k : ℕ∞} {f g : E → ℝ} {O : Set E} (hf : IsLowerCOn k f O)
    (h : ∀ x ∈ O, f x = g x) : IsLowerCOn k g O := by
  intro x hx
  obtain ⟨V, hV, hxV, hVO, ⟨R⟩⟩ := hf x hx
  exact ⟨V, hV, hxV, hVO, ⟨R.congr fun y hy ↦ h y (hVO hy)⟩⟩

omit [FiniteDimensional ℝ E] in
/-- Being lower-`Cᵏ` is a local property. -/
theorem isLowerCOn_of_local {k : ℕ∞} {f : E → ℝ} {O : Set E}
    (h : ∀ x ∈ O, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧ IsLowerCOn k f U) : IsLowerCOn k f O := by
  intro x hx
  obtain ⟨U, -, hxU, hUO, hU⟩ := h x hx
  obtain ⟨V, hV, hxV, hVU, hR⟩ := hU x hxU
  exact ⟨V, hV, hxV, hVU.trans hUO, hR⟩

omit [FiniteDimensional ℝ E] in
/-- **Exercise 10.35(a)**: the sum of two lower-`Cᵏ` functions is lower-`Cᵏ`. -/
theorem IsLowerCOn.add {k : ℕ∞} {f g : E → ℝ} {O : Set E} (hf : IsLowerCOn k f O)
    (hg : IsLowerCOn k g O) : IsLowerCOn k (fun x ↦ f x + g x) O := by
  intro x hx
  obtain ⟨V₁, hV₁, hx₁, hV₁O, ⟨R₁⟩⟩ := hf x hx
  obtain ⟨V₂, hV₂, hx₂, -, ⟨R₂⟩⟩ := hg x hx
  exact ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨hx₁, hx₂⟩, inter_subset_left.trans hV₁O,
    ⟨R₁.add R₂ hV₁ hV₂⟩⟩

omit [FiniteDimensional ℝ E] in
/-- **Exercise 10.35(a)**: nonnegative multiples of lower-`Cᵏ` functions are lower-`Cᵏ`. -/
theorem IsLowerCOn.const_mul {k : ℕ∞} {f : E → ℝ} {O : Set E} (hf : IsLowerCOn k f O)
    {c : ℝ} (hc : 0 ≤ c) : IsLowerCOn k (fun x ↦ c * f x) O := by
  intro x hx
  obtain ⟨V, hV, hxV, hVO, ⟨R⟩⟩ := hf x hx
  exact ⟨V, hV, hxV, hVO, ⟨R.constMul hV hc⟩⟩

omit [FiniteDimensional ℝ E] in
/-- **Exercise 10.35(a)**: `f = Σ λᵢ fᵢ` with `λᵢ ≥ 0` and `fᵢ` lower-`Cᵏ` is lower-`Cᵏ`. -/
theorem isLowerCOn_sum {k : ℕ∞} {ι : Type*} (s : Finset ι) {lam : ι → ℝ} {f : ι → E → ℝ}
    {O : Set E} (hO : IsOpen O) (hlam : ∀ i ∈ s, 0 ≤ lam i) (hf : ∀ i ∈ s, IsLowerCOn k (f i) O) :
    IsLowerCOn k (fun x ↦ ∑ i ∈ s, lam i * f i x) O := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using ContDiffOn.isLowerCOn (k := k) hO (contDiffOn_const (c := (0 : ℝ)))
  | insert i s hi ih =>
    have h1 := (hf i (Finset.mem_insert_self i s)).const_mul (hlam i (Finset.mem_insert_self i s))
    have h2 := ih (fun j hj ↦ hlam j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    refine (h1.add h2).congr fun x _ ↦ ?_
    rw [Finset.sum_insert hi]

/-! ### Theorem 10.33: convexity -/

/-- A finite convex function on an open set has a global affine minorant through each point. -/
theorem exists_subgradient_of_convexOn {f : E → ℝ} {C : Set E} (hC : IsOpen C)
    (hf : ConvexOn ℝ C f) {x : E} (hx : x ∈ C) :
    ∃ v : E, ∀ y ∈ C, f x + ⟪v, y - x⟫_ℝ ≤ f y := by
  classical
  set F : E → EReal := fun y ↦ if y ∈ C then (f y : EReal) else ⊤ with hFdef
  have hFeq : ∀ y ∈ C, F y = (f y : EReal) := fun y hy ↦ by simp [hFdef, hy]
  have hFout : ∀ y, y ∉ C → F y = ⊤ := fun y hy ↦ by simp [hFdef, hy]
  have hmemC : ∀ p ∈ epigraph F, p.1 ∈ C := fun p hp ↦ by
    by_contra h
    have h1 : F p.1 ≤ (p.2 : EReal) := hp
    rw [hFout _ h] at h1
    exact absurd h1 (not_le.2 (EReal.coe_lt_top _))
  have hFconv : Convex ℝ (epigraph F) := by
    intro p hp q hq a b ha hb hab
    have hp1 := hmemC p hp
    have hq1 := hmemC q hq
    have hp2 : f p.1 ≤ p.2 := by
      have h1 : F p.1 ≤ (p.2 : EReal) := hp
      rwa [hFeq _ hp1, EReal.coe_le_coe_iff] at h1
    have hq2 : f q.1 ≤ q.2 := by
      have h1 : F q.1 ≤ (q.2 : EReal) := hq
      rwa [hFeq _ hq1, EReal.coe_le_coe_iff] at h1
    have hmem : a • p.1 + b • q.1 ∈ C := hf.1 hp1 hq1 ha hb hab
    show F (a • p + b • q).1 ≤ (((a • p + b • q).2 : ℝ) : EReal)
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [hFeq _ (by simpa using hmem), EReal.coe_le_coe_iff]
    have h1 := hf.2 hp1 hq1 ha hb hab
    simp only [smul_eq_mul] at h1
    nlinarith [mul_le_mul_of_nonneg_left hp2 ha, mul_le_mul_of_nonneg_left hq2 hb]
  have hprop : IsProper F :=
    ⟨⟨x, by rw [hFeq x hx]; exact EReal.coe_lt_top _⟩, fun y ↦ by
      by_cases hy : y ∈ C
      · rw [hFeq y hy]; exact EReal.bot_lt_coe _
      · rw [hFout y hy]; exact bot_lt_top⟩
  have hdom : effectiveDomain F = C := by
    ext y
    simp only [effectiveDomain, mem_setOf_eq]
    by_cases hy : y ∈ C
    · simp [hFeq y hy, hy, EReal.coe_lt_top]
    · simp [hFout y hy, hy]
  have hint : x ∈ interior (effectiveDomain F) := by rw [hdom, hC.interior_eq]; exact hx
  obtain ⟨v, hv⟩ := subdifferential_nonempty_of_convex_interior hFconv hprop hint
  have hv' := (mem_subdifferential_iff_of_convex hFconv hprop (hFeq x hx)).1 hv
  refine ⟨v, fun y hy ↦ ?_⟩
  have h1 := hv' y
  rw [hFeq y hy] at h1
  exact_mod_cast h1

/-- The jointly smooth affine model `((a, v, w), x) ↦ a + ⟪v, x - w⟫`. -/
noncomputable def affineModel (q : (ℝ × E × E) × E) : ℝ := q.1.1 + ⟪q.1.2.1, q.2 - q.1.2.2⟫_ℝ

omit [FiniteDimensional ℝ E] in
theorem contDiff_affineModel {n : WithTop ℕ∞} : ContDiff ℝ n (affineModel (E := E)) := by
  unfold affineModel
  exact (contDiff_fst.comp contDiff_fst).add
    ((contDiff_fst.comp (contDiff_snd.comp contDiff_fst)).inner ℝ
      (contDiff_snd.sub (contDiff_snd.comp (contDiff_snd.comp contDiff_fst))))

/-- **Theorem 10.33**: a finite convex function on an open convex set `C` is lower-`C^∞` on `C`,
with local representations by affine functions whose coefficients depend continuously on the
index. -/
theorem ConvexOn.isLowerCOn {f : E → ℝ} {C : Set E} (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
    IsLowerCOn ⊤ f C := by
  intro x hx
  obtain ⟨r, hr, hrC⟩ := Metric.isOpen_iff.1 hC x hx
  set δ := r / 3 with hδdef
  have hδ0 : 0 < δ := by positivity
  have hB2 : closedBall x (2 * δ) ⊆ C := (closedBall_subset_ball (by linarith)).trans hrC
  have hB1 : closedBall x δ ⊆ closedBall x (2 * δ) := closedBall_subset_closedBall (by linarith)
  have hfc : ContinuousOn f C := hf.continuousOn hC
  obtain ⟨M, hM⟩ := (isCompact_closedBall x (2 * δ)).exists_bound_of_continuousOn (hfc.mono hB2)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_closedBall_self (by linarith)))
  set K : Set (E × E) := {p | p.1 ∈ closedBall x δ} with hKdef
  have hK : IsClosed K := isClosed_closedBall.preimage continuous_fst
  set S : Set (E × E) := {p | p.1 ∈ closedBall x δ ∧ ∀ y ∈ C, f p.1 + ⟪p.2, y - p.1⟫_ℝ ≤ f y}
    with hSdef
  have hgc : ∀ y, ContinuousOn (fun p : E × E ↦ f p.1 + ⟪p.2, y - p.1⟫_ℝ) K := fun y ↦
    ((hfc.mono (hB1.trans hB2)).comp continuous_fst.continuousOn fun p hp ↦ hp).add
      (continuous_snd.inner (continuous_const.sub continuous_fst)).continuousOn
  have hSeq : S = K ∩ ⋂ y ∈ C, (K ∩ (fun p : E × E ↦ f p.1 + ⟪p.2, y - p.1⟫_ℝ) ⁻¹' Iic (f y)) := by
    ext p
    simp only [hSdef, hKdef, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun y hy ↦ ⟨h1, h2 y hy⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun y hy ↦ (h2 y hy).2⟩
  have hSclosed : IsClosed S := by
    rw [hSeq]
    exact hK.inter (isClosed_biInter fun y _ ↦
      (hgc y).preimage_isClosed_of_isClosed hK isClosed_Iic)
  have hSbdd : S ⊆ closedBall x δ ×ˢ closedBall 0 (2 * M / δ) := by
    rintro ⟨w, v⟩ ⟨hw, hv⟩
    refine ⟨hw, ?_⟩
    rw [mem_closedBall_zero_iff]
    by_cases hv0 : v = 0
    · rw [hv0, norm_zero]
      positivity
    have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv0
    set y := w + (δ / ‖v‖) • v with hydef
    have hyw : y - w = (δ / ‖v‖) • v := by rw [hydef]; abel
    have hy : y ∈ closedBall x (2 * δ) := by
      rw [mem_closedBall, dist_eq_norm]
      have h1 : ‖(δ / ‖v‖) • v‖ = δ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        field_simp
      calc ‖y - x‖ = ‖(w - x) + (δ / ‖v‖) • v‖ := by rw [hydef]; congr 1; abel
        _ ≤ ‖w - x‖ + ‖(δ / ‖v‖) • v‖ := norm_add_le _ _
        _ ≤ δ + δ := add_le_add (by rwa [mem_closedBall, dist_eq_norm] at hw) h1.le
        _ = 2 * δ := by ring
    have h1 := hv y (hB2 hy)
    have h2 : ⟪v, y - w⟫_ℝ = δ * ‖v‖ := by
      rw [hyw, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have h3 := hM y hy
    have h4 := hM w (hB1 hw)
    rw [Real.norm_eq_abs, abs_le] at h3 h4
    rw [le_div_iff₀ hδ0]
    nlinarith
  have hScpt : IsCompact S := ((isCompact_closedBall x δ).prod (isCompact_closedBall 0 _)).of_isClosed_subset
    hSclosed hSbdd
  haveI : CompactSpace S := isCompact_iff_compactSpace.1 hScpt
  have hcont : Continuous fun p : S ↦ ((f p.1.1, p.1.2, p.1.1) : ℝ × E × E) := by
    have h1 : Continuous fun p : S ↦ f p.1.1 := by
      have := (hfc.mono (hB1.trans hB2)).comp_continuous (continuous_fst.comp continuous_subtype_val)
        (fun p : S ↦ p.2.1)
      exact this
    exact h1.prodMk ((continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val))
  have hball : ball x δ ⊆ C := ball_subset_closedBall.trans (hB1.trans hB2)
  refine ⟨ball x δ, isOpen_ball, mem_ball_self hδ0, hball, ⟨LowerRepresentation.ofParam S
    (fun p ↦ ((f p.1.1, p.1.2, p.1.1) : ℝ × E × E)) hcont affineModel contDiff_affineModel
    (fun p y hy ↦ p.2.2 y (hball hy)) (fun y hy ↦ ?_)⟩⟩
  obtain ⟨v, hv⟩ := exists_subgradient_of_convexOn hC hf (hball hy)
  exact ⟨⟨(y, v), ball_subset_closedBall hy, hv⟩, by simp [affineModel]⟩

/-- **Theorem 10.33**: `f` is lower-`C²` on `O` iff around each point of `O` it is a finite
convex function minus a `C²` function, which may be taken to be `ρ|·|²`. -/
theorem isLowerCOn_two_iff_locally_convex_sub {f : E → ℝ} {O : Set E} :
    IsLowerCOn 2 f O ↔ ∀ x ∈ O, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
      ∃ g h : E → ℝ, ConvexOn ℝ U g ∧ ContDiffOn ℝ 2 h U ∧ ∀ y ∈ U, f y = g y - h y := by
  constructor
  · intro hf x hx
    obtain ⟨δ, hδ, hδO, ρ, -, hconv⟩ := hf.exists_convex_sub_quadratic x hx
    refine ⟨ball x δ, isOpen_ball, mem_ball_self hδ, hδO, fun y ↦ f y + ρ * ‖y‖ ^ 2,
      fun y ↦ ρ * ‖y‖ ^ 2, hconv, ?_, fun y _ ↦ by ring⟩
    exact (contDiff_const.mul (contDiff_id.norm_sq ℝ)).contDiffOn
  · intro h
    refine isLowerCOn_of_local fun x hx ↦ ?_
    obtain ⟨U, hU, hxU, hUO, g, h, hg, hh, heq⟩ := h x hx
    have h1 : IsLowerCOn 2 g U := (ConvexOn.isLowerCOn hU hg).mono le_top
    have h2 : IsLowerCOn 2 (fun y ↦ -h y) U := ContDiffOn.isLowerCOn hU hh.neg
    exact ⟨U, hU, hxU, hUO, (h1.add h2).congr fun y hy ↦ by rw [heq y hy]; ring⟩

/-! ### Exercise 10.35(b): composition -/

section Composition

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem iteratedFDeriv_one_eq (g : E → ℝ) (x : E) :
    iteratedFDeriv ℝ 1 g x = (continuousMultilinearCurryFin1 ℝ E ℝ).symm (fderiv ℝ g x) := by
  ext m
  simp [iteratedFDeriv_one_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Exercise 10.35(b)**: if `g` is lower-`C¹` on `O` and `G` is `C¹`, then `g ∘ G` is
lower-`C¹` on `G⁻¹(O)`. -/
theorem IsLowerCOn.comp_one {g : F → ℝ} {O : Set F} (hg : IsLowerCOn 1 g O) {G : E → F}
    (hG : ContDiff ℝ 1 G) : IsLowerCOn 1 (fun x ↦ g (G x)) (G ⁻¹' O) := by
  intro x hx
  obtain ⟨V, hV, hxV, hVO, ⟨R⟩⟩ := hg (G x) hx
  have hGc : Continuous G := hG.continuous
  have hW : IsOpen (G ⁻¹' V) := hV.preimage hGc
  refine ⟨G ⁻¹' V, hW, hxV, preimage_mono hVO, ⟨LowerRepresentation.mk R.T
    (fun t y ↦ R.F t (G y)) (fun t ↦ (R.contDiffOn t).comp hG.contDiffOn fun y hy ↦ hy)
    (fun j hj ↦ ?_) (fun t y hy ↦ R.le t (G y) hy) (fun y hy ↦ R.exists_eq (G y) hy)⟩⟩
  have hj' : j = 0 ∨ j = 1 := by
    have : (j : ℕ∞) ≤ 1 := hj
    norm_cast at this
    omega
  have hmap : MapsTo (fun p : R.T × E ↦ ((p.1, G p.2) : R.T × F)) (univ ×ˢ (G ⁻¹' V)) (univ ×ˢ V) :=
    fun p hp ↦ ⟨trivial, hp.2⟩
  have hpc : Continuous fun p : R.T × E ↦ ((p.1, G p.2) : R.T × F) :=
    continuous_fst.prodMk (hGc.comp continuous_snd)
  rcases hj' with rfl | rfl
  · have h0 := R.continuousOn_val.comp hpc.continuousOn hmap
    have e : (fun p : R.T × E ↦ iteratedFDeriv ℝ 0 (fun y ↦ R.F p.1 (G y)) p.2) = fun p ↦
        (continuousMultilinearCurryFin0 ℝ E ℝ).symm (R.F p.1 (G p.2)) := by
      funext p
      ext m
      simp [iteratedFDeriv_zero_apply]
    rw [e]
    exact (continuousMultilinearCurryFin0 ℝ E ℝ).symm.continuous.comp_continuousOn h0
  · have h1 := (R.continuousOn_fderiv le_rfl).comp hpc.continuousOn hmap
    have h2 : Continuous fun y ↦ fderiv ℝ G y := hG.continuous_fderiv one_ne_zero
    have hcomp : ContinuousOn (fun p : R.T × E ↦ (fderiv ℝ (R.F p.1) (G p.2)).comp (fderiv ℝ G p.2))
        (univ ×ˢ (G ⁻¹' V)) := h1.clm_comp (h2.comp continuous_snd).continuousOn
    have e : ∀ p ∈ univ ×ˢ (G ⁻¹' V), iteratedFDeriv ℝ 1 (fun y ↦ R.F p.1 (G y)) p.2 =
        (continuousMultilinearCurryFin1 ℝ E ℝ).symm
          ((fderiv ℝ (R.F p.1) (G p.2)).comp (fderiv ℝ G p.2)) := by
      intro p hp
      rw [iteratedFDeriv_one_eq]
      congr 1
      have hd1 := (R.differentiableAt le_rfl hV p.1 hp.2).hasFDerivAt
      have hd2 := (hG.differentiable one_ne_zero p.2).hasFDerivAt
      exact (hd1.comp p.2 hd2).fderiv
    exact ((continuousMultilinearCurryFin1 ℝ E ℝ).symm.continuous.comp_continuousOn hcomp).congr e

omit [FiniteDimensional ℝ E] in
/-- The quadratic representation of a lower-`C²` function around a point, with its continuous
coefficient map. -/
theorem IsLowerCOn.exists_quadratic_param {g : F → ℝ} {O : Set F} (hg : IsLowerCOn 2 g O)
    {y₀ : F} (hy₀ : y₀ ∈ O) :
    ∃ V : Set F, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ O ∧ ∃ ρ : ℝ, ∃ (T : Type u) (_ : TopologicalSpace T)
      (_ : CompactSpace T) (c : T → ℝ × (F →L[ℝ] ℝ) × F), Continuous c ∧
        (∀ t, ∀ y ∈ V, LowerRepresentation.quadraticModel ρ (c t, y) ≤ g y) ∧
        ∀ y ∈ V, ∃ t, LowerRepresentation.quadraticModel ρ (c t, y) = g y := by
  obtain ⟨V, hV, hyV, hVO, ⟨R⟩⟩ := hg y₀ hy₀
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV y₀ hyV
  have hδV : closedBall y₀ (r / 2) ⊆ V := (closedBall_subset_ball (half_lt_self hr)).trans hrV
  obtain ⟨ρ, -, hρ⟩ := R.exists_bound_fderiv_fderiv le_rfl hδV
  haveI : CompactSpace (closedBall y₀ (r / 2)) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall y₀ (r / 2))
  have hmap : Continuous fun s : R.T × closedBall y₀ (r / 2) ↦ ((s.1, (s.2 : F)) : R.T × F) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hmem : ∀ s : R.T × closedBall y₀ (r / 2), ((s.1, (s.2 : F)) : R.T × F) ∈ univ ×ˢ V :=
    fun s ↦ ⟨trivial, hδV s.2.2⟩
  refine ⟨ball y₀ (r / 2), isOpen_ball, mem_ball_self (half_pos hr),
    ball_subset_closedBall.trans (hδV.trans hVO), ρ, R.T × closedBall y₀ (r / 2), inferInstance,
    inferInstance, fun s ↦ (R.F s.1 s.2, fderiv ℝ (R.F s.1) s.2, (s.2 : F)), ?_, ?_, ?_⟩
  · exact (R.continuousOn_val.comp_continuous hmap hmem).prodMk
      (((R.continuousOn_fderiv (le_trans (by norm_num) le_rfl)).comp_continuous hmap hmem).prodMk
        (continuous_subtype_val.comp continuous_snd))
  · intro s y hy
    have h := R.quadratic_lower_bound le_rfl hV hδV hρ s.1 (ball_subset_closedBall hy) s.2.2
    exact h.trans (R.le s.1 y (hδV (ball_subset_closedBall hy)))
  · intro y hy
    obtain ⟨t, ht⟩ := R.exists_eq y (hδV (ball_subset_closedBall hy))
    exact ⟨(t, ⟨y, ball_subset_closedBall hy⟩), by
      simp [LowerRepresentation.quadraticModel, ht]⟩

omit [FiniteDimensional ℝ E] in
/-- **Exercise 10.35(b)**: if `g` is lower-`C²` on `O` and `G` is `C²`, then `g ∘ G` is
lower-`C²` on `G⁻¹(O)`. -/
theorem IsLowerCOn.comp_two {g : F → ℝ} {O : Set F} (hg : IsLowerCOn 2 g O) {G : E → F}
    (hG : ContDiff ℝ 2 G) : IsLowerCOn 2 (fun x ↦ g (G x)) (G ⁻¹' O) := by
  intro x hx
  obtain ⟨V, hV, hyV, hVO, ρ, T, _, _, c, hc, hle, heq⟩ := hg.exists_quadratic_param hx
  have hQ : ContDiff ℝ 2 fun q : (ℝ × (F →L[ℝ] ℝ) × F) × E ↦
      LowerRepresentation.quadraticModel ρ (q.1, G q.2) :=
    (LowerRepresentation.contDiff_quadraticModel ρ).comp (contDiff_fst.prodMk (hG.comp contDiff_snd))
  exact ⟨G ⁻¹' V, hV.preimage hG.continuous, hyV, preimage_mono hVO,
    ⟨LowerRepresentation.ofParam T c hc _ hQ (fun t y hy ↦ hle t (G y) hy)
      (fun y hy ↦ heq (G y) hy)⟩⟩

end Composition

end RW
