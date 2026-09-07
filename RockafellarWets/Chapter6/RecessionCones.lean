/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Local and Global Recession Vectors

Definition 6.33 and Exercise 6.34.  A vector `w` is a *local recession vector*
for `C` at `x̄` when a whole segment `[0, ε]w` can be added to every point of
`C` near `x̄` without leaving `C`; it is *global* when that holds at every point
of `C` and for every positive multiple.

The uniform clause of 6.34(a) -- that finitely many local recession vectors
share a common neighborhood and step size for their whole convex hull -- is
what makes `R_C(x̄)` convex, so it is proved first, in the two-vector form the
convexity statement needs.  Its only content is that adding a short multiple of
`w₁` moves a point of `C` near `x̄` by an amount that can be kept inside the
neighborhood belonging to `w₂`.
-/

import RockafellarWets.Chapter6.TangentCones
import RockafellarWets.Chapter3.HorizonCones

open Filter Metric Set Topology

namespace RW

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set E} {x w : E}

/-- **Definition 6.33**: `w` is a local recession vector for `C` at `x̄` when
`x + τw ∈ C` for all `x ∈ C` near `x̄` and all small `τ ≥ 0`. -/
def localRecessionCone (C : Set E) (x : E) : Set E :=
  {w | ∃ V ∈ nhds x, ∃ ε > 0, ∀ y ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε, y + τ • w ∈ C}

/-- **Definition 6.33**: `w` is a global recession vector for `C` when
`C + τw ⊆ C` for every `τ ≥ 0`. -/
def globalRecessionCone (C : Set E) : Set E :=
  {w | ∀ y ∈ C, ∀ τ : ℝ, 0 ≤ τ → y + τ • w ∈ C}

theorem mem_localRecessionCone :
    w ∈ localRecessionCone C x ↔
      ∃ V ∈ nhds x, ∃ ε > 0, ∀ y ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε, y + τ • w ∈ C :=
  Iff.rfl

theorem mem_globalRecessionCone :
    w ∈ globalRecessionCone C ↔ ∀ y ∈ C, ∀ τ : ℝ, 0 ≤ τ → y + τ • w ∈ C :=
  Iff.rfl

/-- A global recession vector is a local recession vector at every point. -/
theorem globalRecessionCone_subset_localRecessionCone (C : Set E) (x : E) :
    globalRecessionCone C ⊆ localRecessionCone C x := fun _w hw ↦
  ⟨univ, univ_mem, 1, one_pos, fun y hy _ hτ ↦ hw y hy.1 _ hτ.1⟩

end Definitions

section ConeStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set E} {x : E}

/-- **Exercise 6.34(a)**: the local recession vectors form a cone. -/
theorem isCone_localRecessionCone (C : Set E) (x : E) :
    IsCone (localRecessionCone C x) := by
  constructor
  · exact ⟨univ, univ_mem, 1, one_pos, fun y hy _ _ ↦ by simpa using hy.1⟩
  · rintro w ⟨V, hV, ε, hε, hprop⟩ c hc
    refine ⟨V, hV, ε / c, div_pos hε hc, fun y hy τ hτ ↦ ?_⟩
    have hsmul : y + τ • c • w = y + (τ * c) • w := by
      rw [smul_smul]
    rw [hsmul]
    refine hprop y hy (τ * c) ⟨mul_nonneg hτ.1 hc.le, ?_⟩
    calc τ * c ≤ (ε / c) * c := mul_le_mul_of_nonneg_right hτ.2 hc.le
      _ = ε := by field_simp

/-- **Exercise 6.34(a)**, the uniform clause in the two-vector form: two local
recession vectors share a common neighborhood and step size along which every
convex combination of them may be added.  Shrinking the neighborhood keeps the
point displaced by the first vector inside the neighborhood belonging to the
second. -/
theorem convex_localRecessionCone (C : Set E) (x : E) :
    Convex ℝ (localRecessionCone C x) := by
  rintro w₁ ⟨V₁, hV₁, ε₁, hε₁, hp₁⟩ w₂ ⟨V₂, hV₂, ε₂, hε₂, hp₂⟩ a b ha hb hab
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV₂
  set ε : ℝ := min (min ε₁ ε₂) (δ / (2 * (‖w₁‖ + 1))) with hεdef
  have hεpos : 0 < ε := by
    have : (0 : ℝ) < δ / (2 * (‖w₁‖ + 1)) := div_pos hδ (by positivity)
    exact lt_min (lt_min hε₁ hε₂) this
  refine ⟨V₁ ∩ ball x (δ / 2), inter_mem hV₁ (ball_mem_nhds x (by linarith)),
    ε, hεpos, fun y hy τ hτ ↦ ?_⟩
  have hyC : y ∈ C := hy.1
  have hyV₁ : y ∈ V₁ := hy.2.1
  have hyball : y ∈ ball x (δ / 2) := hy.2.2
  have hτ0 : 0 ≤ τ := hτ.1
  have hτε : τ ≤ ε := hτ.2
  have hstep₁ : y + (τ * a) • w₁ ∈ C := by
    refine hp₁ y ⟨hyC, hyV₁⟩ (τ * a) ⟨mul_nonneg hτ0 ha, ?_⟩
    calc τ * a ≤ τ * 1 := mul_le_mul_of_nonneg_left (by linarith) hτ0
      _ = τ := mul_one τ
      _ ≤ ε := hτε
      _ ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hnear : y + (τ * a) • w₁ ∈ V₂ := by
    apply hball
    rw [mem_ball, dist_eq_norm]
    have hy' : ‖y - x‖ < δ / 2 := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hyball
    have hstep : ‖(τ * a) • w₁‖ ≤ ε * ‖w₁‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hτ0 ha)]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc τ * a ≤ τ * 1 := mul_le_mul_of_nonneg_left (by linarith) hτ0
        _ = τ := mul_one τ
        _ ≤ ε := hτε
    have hbound : ε * ‖w₁‖ < δ / 2 := by
      have hεle : ε ≤ δ / (2 * (‖w₁‖ + 1)) := min_le_right _ _
      have hkey : ε * ‖w₁‖ ≤ δ / (2 * (‖w₁‖ + 1)) * ‖w₁‖ :=
        mul_le_mul_of_nonneg_right hεle (norm_nonneg _)
      have hlt : δ / (2 * (‖w₁‖ + 1)) * ‖w₁‖ < δ / 2 := by
        rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [norm_nonneg w₁]
      linarith
    have hsum : y + (τ * a) • w₁ - x = (y - x) + (τ * a) • w₁ := by abel
    rw [hsum]
    calc ‖(y - x) + (τ * a) • w₁‖ ≤ ‖y - x‖ + ‖(τ * a) • w₁‖ := norm_add_le _ _
      _ < δ / 2 + δ / 2 := by linarith
      _ = δ := by ring
  have hstep₂ : (y + (τ * a) • w₁) + (τ * b) • w₂ ∈ C := by
    refine hp₂ _ ⟨hstep₁, hnear⟩ (τ * b) ⟨mul_nonneg hτ0 hb, ?_⟩
    calc τ * b ≤ τ * 1 := mul_le_mul_of_nonneg_left (by linarith) hτ0
      _ = τ := mul_one τ
      _ ≤ ε := hτε
      _ ≤ ε₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hcomb : y + τ • (a • w₁ + b • w₂) = (y + (τ * a) • w₁) + (τ * b) • w₂ := by
    rw [smul_add, smul_smul, smul_smul]
    abel
  rw [hcomb]
  exact hstep₂

/-- **Exercise 6.34(a)**, the uniform clause as printed: finitely many local
recession vectors share one neighborhood of `x̄` and one step size along which
*every* convex combination of them may be added.  The neighborhood is shrunk
so that every partial sum of the displacement stays inside the neighborhood
belonging to the next vector, which is what makes the estimate uniform. -/
theorem exists_uniform_localRecession {r : ℕ} (ws : Fin r → E)
    (hws : ∀ k, ws k ∈ localRecessionCone C x) :
    ∃ V ∈ nhds x, ∃ ε > 0, ∀ y ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε,
      ∀ a : Fin r → ℝ, (∀ k, 0 ≤ a k) → ∑ k, a k = 1 →
        y + τ • (∑ k, a k • ws k) ∈ C := by
  classical
  rcases isEmpty_or_nonempty (Fin r) with hemp | hne
  · refine ⟨univ, univ_mem, 1, one_pos, fun y hy τ _ a _ hsum ↦ ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact absurd hsum.symm one_ne_zero
  choose V hV ep hep hprop using hws
  obtain ⟨e, hepos, hele⟩ : ∃ e > 0, ∀ k, e ≤ ep k := by
    obtain ⟨k₀, -, hk₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin r)) ep
      Finset.univ_nonempty
    exact ⟨ep k₀, hep k₀, fun k ↦ hk₀ k (Finset.mem_univ k)⟩
  have hVall : (⋂ k, V k) ∈ nhds x := Filter.iInter_mem.2 hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hVall
  set M : ℝ := ∑ k, ‖ws k‖ with hMdef
  have hM : 0 ≤ M := Finset.sum_nonneg fun k _ ↦ norm_nonneg _
  set ε : ℝ := min e (δ / (2 * (M + 1))) with hεdef
  have hεpos : 0 < ε := lt_min hepos (by positivity)
  -- the displacement of any partial convex sum is small
  have hbound : ∀ (F : Finset (Fin r)) (y : E), y ∈ ball x (δ / 2) → ∀ τ ∈ Icc (0 : ℝ) ε,
      ∀ a : Fin r → ℝ, (∀ k, 0 ≤ a k) → (∀ k, a k ≤ 1) →
        y + τ • (∑ k ∈ F, a k • ws k) ∈ ball x δ := by
    intro F y hy τ hτ a ha ha1
    have hnorm : ‖∑ k ∈ F, a k • ws k‖ ≤ M := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ k ∈ F, ‖a k • ws k‖ ≤ ‖ws k‖ := by
        intro k _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha k)]
        calc a k * ‖ws k‖ ≤ 1 * ‖ws k‖ :=
              mul_le_mul_of_nonneg_right (ha1 k) (norm_nonneg _)
          _ = ‖ws k‖ := one_mul _
      refine (Finset.sum_le_sum hterm).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
        fun k _ _ ↦ norm_nonneg _
    have hscaled : ‖τ • (∑ k ∈ F, a k • ws k)‖ < δ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
      have hle : τ * ‖∑ k ∈ F, a k • ws k‖ ≤ ε * M :=
        mul_le_mul hτ.2 hnorm (norm_nonneg _) hεpos.le
      have hlt : ε * M < δ / 2 := by
        have hεle : ε ≤ δ / (2 * (M + 1)) := min_le_right _ _
        have hkey : ε * M ≤ δ / (2 * (M + 1)) * M :=
          mul_le_mul_of_nonneg_right hεle hM
        have hstrict : δ / (2 * (M + 1)) * M < δ / 2 := by
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith
      linarith
    have hy' : ‖y - x‖ < δ / 2 := by
      rw [← dist_eq_norm]
      exact mem_ball.1 hy
    rw [mem_ball, dist_eq_norm]
    have hsum : y + τ • (∑ k ∈ F, a k • ws k) - x
        = (y - x) + τ • (∑ k ∈ F, a k • ws k) := by abel
    rw [hsum]
    calc ‖(y - x) + τ • (∑ k ∈ F, a k • ws k)‖
        ≤ ‖y - x‖ + ‖τ • (∑ k ∈ F, a k • ws k)‖ := norm_add_le _ _
      _ < δ / 2 + δ / 2 := by linarith
      _ = δ := by ring
  -- the partial sums stay in `C`
  have key : ∀ F : Finset (Fin r), ∀ y ∈ C, y ∈ ball x (δ / 2) → ∀ τ ∈ Icc (0 : ℝ) ε,
      ∀ a : Fin r → ℝ, (∀ k, 0 ≤ a k) → (∀ k, a k ≤ 1) →
        y + τ • (∑ k ∈ F, a k • ws k) ∈ C := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
        intro y hy _ τ _ a _ _
        simpa using hy
    | insert j F' hj ih =>
        intro y hy hyb τ hτ a ha ha1
        have hprev := ih y hy hyb τ hτ a ha ha1
        have hprevball := hbound F' y hyb τ hτ a ha ha1
        have hsplit : y + τ • (∑ k ∈ insert j F', a k • ws k)
            = (y + τ • (∑ k ∈ F', a k • ws k)) + (τ * a j) • ws j := by
          rw [Finset.sum_insert hj, smul_add, smul_smul]
          abel
        rw [hsplit]
        refine hprop j _ ⟨hprev, mem_iInter.1 (hball hprevball) j⟩ (τ * a j)
          ⟨mul_nonneg hτ.1 (ha j), ?_⟩
        calc τ * a j ≤ τ * 1 := mul_le_mul_of_nonneg_left (ha1 j) hτ.1
          _ = τ := mul_one τ
          _ ≤ ε := hτ.2
          _ ≤ e := min_le_left _ _
          _ ≤ ep j := hele j
  refine ⟨ball x (δ / 2), ball_mem_nhds x (by linarith), ε, hεpos,
    fun y hy τ hτ a ha hsum ↦ ?_⟩
  have ha1 : ∀ k, a k ≤ 1 := by
    intro k
    rw [← hsum]
    exact Finset.single_le_sum (fun i _ ↦ ha i) (Finset.mem_univ k)
  exact key Finset.univ y hy.1 hy.2 τ hτ a ha ha1

/-- **Exercise 6.34(a)**: a local recession vector is a derivable tangent
vector; the straight path `t ↦ x̄ + tw` is the witness. -/
theorem localRecessionCone_subset_derivableCone (hx : x ∈ C) :
    localRecessionCone C x ⊆ derivableCone C x := by
  rintro w ⟨V, hV, ε, hε, hprop⟩
  refine ⟨ε, hε, fun t ↦ x + t • w, by simp, fun t ht ↦ ?_, ?_⟩
  · exact hprop x ⟨hx, mem_of_mem_nhds hV⟩ t ht
  · refine Tendsto.congr' ?_ (tendsto_const_nhds (x := w))
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := ne_of_gt ht
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htne, one_smul]

/-- **Exercise 6.34(a)**: local recession vectors are tangent vectors. -/
theorem localRecessionCone_subset_tangentCone (hx : x ∈ C) :
    localRecessionCone C x ⊆ tangentCone C x :=
  (localRecessionCone_subset_derivableCone hx).trans (derivableCone_subset_tangentCone hx)

/-- **Exercise 6.34(b)**: the global recession vectors form a convex cone; no
closedness is needed for this half. -/
theorem convex_globalRecessionCone (C : Set E) : Convex ℝ (globalRecessionCone C) := by
  intro w₁ hw₁ w₂ hw₂ a b ha hb _ y hy τ hτ
  have hstep₁ : y + (τ * a) • w₁ ∈ C := hw₁ y hy _ (mul_nonneg hτ ha)
  have hstep₂ : (y + (τ * a) • w₁) + (τ * b) • w₂ ∈ C :=
    hw₂ _ hstep₁ _ (mul_nonneg hτ hb)
  have hcomb : y + τ • (a • w₁ + b • w₂) = (y + (τ * a) • w₁) + (τ * b) • w₂ := by
    rw [smul_add, smul_smul, smul_smul]
    abel
  rw [hcomb]
  exact hstep₂

/-- **Exercise 6.34(b)**: the global recession vectors form a cone. -/
theorem isCone_globalRecessionCone (C : Set E) : IsCone (globalRecessionCone C) := by
  constructor
  · intro y hy _ _
    simpa using hy
  · intro w hw c hc y hy τ hτ
    have hsmul : y + τ • c • w = y + (τ * c) • w := by rw [smul_smul]
    rw [hsmul]
    exact hw y hy _ (mul_nonneg hτ hc.le)

/-- **Exercise 6.34(b)**: for a closed set the global recession cone is
closed. -/
theorem isClosed_globalRecessionCone (hC : IsClosed C) :
    IsClosed (globalRecessionCone C) := by
  have heq : globalRecessionCone C =
      ⋂ y ∈ C, ⋂ τ ∈ Ici (0 : ℝ), (fun w : E ↦ y + τ • w) ⁻¹' C := by
    ext w
    simp only [mem_globalRecessionCone, mem_iInter, mem_preimage, mem_Ici]
  rw [heq]
  refine isClosed_biInter fun y _ ↦ isClosed_biInter fun τ _ ↦ ?_
  exact hC.preimage (continuous_const.add (continuous_id.const_smul τ))

end ConeStructure

section GlobalFromLocal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set E}

/-- **Exercise 6.34(b)**: for a closed set the global recession vectors are
exactly the vectors that recede locally at *every* point.  A ray that leaves
`C` must leave it at a first point, and there the local recession property
fails; that is the intermediate-value form of the argument. -/
theorem globalRecessionCone_eq_iInter_localRecessionCone (hC : IsClosed C) :
    globalRecessionCone C = ⋂ x ∈ C, localRecessionCone C x := by
  refine Subset.antisymm
    (subset_iInter₂ fun x _ ↦ globalRecessionCone_subset_localRecessionCone C x) ?_
  intro w hw y hy τ hτ
  have hlocal : ∀ z ∈ C, w ∈ localRecessionCone C z := fun z hz ↦ mem_iInter₂.1 hw z hz
  set f : ℝ → E := fun t ↦ y + t • w with hfdef
  have hfcont : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hclosed : IsClosed (f ⁻¹' C ∩ Icc 0 τ) := (hC.preimage hfcont).inter isClosed_Icc
  have hzero : (0 : ℝ) ∈ f ⁻¹' C := by simpa [hfdef] using hy
  have hgt : ∀ t ∈ f ⁻¹' C ∩ Ico (0 : ℝ) τ, ∀ u ∈ Ioi t,
      (f ⁻¹' C ∩ Ioc t u).Nonempty := by
    rintro t ⟨htC, htI⟩ u hu
    obtain ⟨V, hV, ε, hε, hprop⟩ := hlocal (f t) htC
    set σ : ℝ := min ε (u - t) with hσdef
    have hσpos : 0 < σ := lt_min hε (by simpa using hu)
    have hmem : f t + σ • w ∈ C :=
      hprop (f t) ⟨htC, mem_of_mem_nhds hV⟩ σ ⟨hσpos.le, min_le_left _ _⟩
    refine ⟨t + σ, ?_, ?_, ?_⟩
    · have hsum : f (t + σ) = f t + σ • w := by
        simp only [hfdef, add_smul]
        abel
      rw [mem_preimage, hsum]
      exact hmem
    · linarith
    · have : σ ≤ u - t := min_le_right _ _
      linarith
  have hsub := hclosed.Icc_subset_of_forall_exists_gt hzero hgt
  exact hsub ⟨hτ, le_rfl⟩

/-- **Exercise 6.34(c)**: for a nonempty set the global recession vectors lie
in the horizon cone; convexity is not needed for this half. -/
theorem globalRecessionCone_subset_horizonCone (hne : C.Nonempty) :
    globalRecessionCone C ⊆ horizonCone C := by
  obtain ⟨y, hy⟩ := hne
  intro w hw
  refine mem_horizonCone_of_forall_smul_add_mem (x := y) fun τ hτ ↦ ?_
  rw [add_comm]
  exact hw y hy τ hτ

/-- **Exercise 6.34(c)**: for a closed convex set the horizon cone consists of
global recession vectors.  This is Theorem 3.6. -/
theorem horizonCone_subset_globalRecessionCone (hconv : Convex ℝ C)
    (hclosed : IsClosed C) : horizonCone C ⊆ globalRecessionCone C := by
  intro w hw y hy τ hτ
  have hray := smul_add_mem_of_mem_horizonCone hconv hclosed hy hw hτ
  rwa [add_comm] at hray

/-- **Exercise 6.34(c)**: for a nonempty closed convex set the global recession
cone is the horizon cone `C^∞`. -/
theorem globalRecessionCone_eq_horizonCone (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (hne : C.Nonempty) : globalRecessionCone C = horizonCone C :=
  Subset.antisymm (globalRecessionCone_subset_horizonCone hne)
    (horizonCone_subset_globalRecessionCone hconv hclosed)

end GlobalFromLocal

section OpenCounterexample

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set E} {x : E}

/-- At a point of an open set every vector recedes locally: a short step from a
nearby point cannot leave an open set. -/
theorem localRecessionCone_eq_univ_of_isOpen (hC : IsOpen C) (hx : x ∈ C) :
    localRecessionCone C x = univ := by
  ext w
  simp only [mem_univ, iff_true, mem_localRecessionCone]
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hC x hx
  refine ⟨ball x (ρ / 2), ball_mem_nhds x (by linarith), ρ / (2 * (‖w‖ + 1)),
    by positivity, fun y hy τ hτ ↦ ?_⟩
  refine hball ?_
  rw [mem_ball, dist_eq_norm]
  have hy' : ‖y - x‖ < ρ / 2 := by
    rw [← dist_eq_norm]
    exact mem_ball.1 hy.2
  have hstep : ‖τ • w‖ < ρ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    have hle : τ * ‖w‖ ≤ ρ / (2 * (‖w‖ + 1)) * ‖w‖ :=
      mul_le_mul_of_nonneg_right hτ.2 (norm_nonneg _)
    have hlt : ρ / (2 * (‖w‖ + 1)) * ‖w‖ < ρ / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [norm_nonneg w]
    linarith
  have hsum : y + τ • w - x = (y - x) + τ • w := by abel
  rw [hsum]
  calc ‖(y - x) + τ • w‖ ≤ ‖y - x‖ + ‖τ • w‖ := norm_add_le _ _
    _ < ρ / 2 + ρ / 2 := by linarith
    _ = ρ := by ring

/-- **A counterexample to the literal reading of 6.34(c).**  The clause is
printed for `⋂_{x ∈ C} R_C(x)`, an identification of the global recession cone
that 6.34(b) supplies only for closed `C`.  Without closedness that
intersection is not contained in `C^∞`, even for a bounded convex set: on an
open ball every vector recedes locally at every point, while the horizon cone
of a bounded set is `{0}`. -/
theorem not_iInter_localRecessionCone_subset_horizonCone
    [Nontrivial E] [FiniteDimensional ℝ E] :
    ¬ (⋂ z ∈ ball (0 : E) 1, localRecessionCone (ball (0 : E) 1) z) ⊆
      horizonCone (ball (0 : E) 1) := by
  have hall : (⋂ z ∈ ball (0 : E) 1, localRecessionCone (ball (0 : E) 1) z) = univ := by
    refine eq_univ_of_forall fun w ↦ mem_iInter₂.2 fun z hz ↦ ?_
    rw [localRecessionCone_eq_univ_of_isOpen isOpen_ball hz]
    exact mem_univ w
  have hhor : horizonCone (ball (0 : E) 1) = ({0} : Set E) :=
    isBounded_iff_horizonCone_eq_singleton_zero.1 (isBounded_ball)
  rw [hall, hhor]
  intro hsub
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  exact hu (hsub (mem_univ u))

end OpenCounterexample

end RW
