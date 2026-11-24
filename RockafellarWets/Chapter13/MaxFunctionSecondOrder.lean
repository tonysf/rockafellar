/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order behavior of max functions

Example 13.10.  For `f = max{f₁, …, f_m}` with every `fᵢ` of class `C²`, `f` is semidifferentiable
with `df(x̄)(w) = max_{i ∈ I(x̄)} ⟪∇fᵢ(x̄), w⟫` (7.28, 8.31), and the quotients `Δ²_τ f(x̄)(w)`
converge along the ray to `max_{i ∈ I'(x̄, w)} ∇²fᵢ(x̄)(w)(w)`, where `I'(x̄, w)` collects the
active indices whose directional derivative attains `df(x̄)(w)`.  Consequently twice
semidifferentiability forces `d²f(x̄)` to be this expression, which must then be continuous in `w`
(13.7).  This fails for `f(x) = max{‖x + a‖², 1}` at `x̄ = 0` with `‖a‖ = 1` as soon as some
`w ≠ 0` is orthogonal to `a`.

The second derivative `∇²fᵢ(x̄)` is Mathlib's `fderiv ℝ (fderiv ℝ fᵢ) x̄`, a bilinear map, so
`⟪w, ∇²fᵢ(x̄) w⟫` is written `fderiv ℝ (fderiv ℝ fᵢ) x̄ w w`.
-/

import RockafellarWets.Chapter13.TwiceDifferentiability
import RockafellarWets.Chapter8.FiniteMaxDerivatives

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- `df(x̄)(w) = max_{i ∈ I(x̄)} ⟪∇fᵢ(x̄), w⟫` for a finite maximum of smooth functions. -/
noncomputable def maxDirectionalDerivative (fs : ι → E → ℝ) (x w : E) : ℝ :=
  (maxActiveIndices fs x).sup' (maxActiveIndices_nonempty fs x) fun i ↦ ⟪gradient (fs i) x, w⟫_ℝ

/-- The index set `I'(x̄, w)` of Example 13.10. -/
noncomputable def maxCriticalIndices (fs : ι → E → ℝ) (x w : E) : Finset ι := by
  classical exact (maxActiveIndices fs x).filter fun i ↦
    ⟪gradient (fs i) x, w⟫_ℝ = maxDirectionalDerivative fs x w

theorem mem_maxCriticalIndices {fs : ι → E → ℝ} {x w : E} {i : ι} :
    i ∈ maxCriticalIndices fs x w ↔
      i ∈ maxActiveIndices fs x ∧ ⟪gradient (fs i) x, w⟫_ℝ = maxDirectionalDerivative fs x w := by
  classical simp [maxCriticalIndices]

theorem maxCriticalIndices_nonempty (fs : ι → E → ℝ) (x w : E) :
    (maxCriticalIndices fs x w).Nonempty := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' (maxActiveIndices_nonempty fs x)
    (fun i ↦ ⟪gradient (fs i) x, w⟫_ℝ)
  exact ⟨i, mem_maxCriticalIndices.2 ⟨hi, he.symm⟩⟩

/-- The value `max_{i ∈ I'(x̄, w)} ⟪w, ∇²fᵢ(x̄) w⟫` of Example 13.10. -/
noncomputable def maxSecondDerivative (fs : ι → E → ℝ) (x w : E) : ℝ :=
  (maxCriticalIndices fs x w).sup' (maxCriticalIndices_nonempty fs x w) fun i ↦
    fderiv ℝ (fderiv ℝ (fs i)) x w w

/-- **Example 13.10**, first-order part (7.28, 8.31): a finite maximum of smooth functions is
semidifferentiable. -/
theorem semidifferentiableAt_finiteMax {fs : ι → E → ℝ} (hs : ∀ i, ContDiff ℝ 1 (fs i)) (x : E) :
    SemidifferentiableAt (fun y ↦ (finiteMax fs y : EReal)) x := by
  have he : indicatorAddMax univ fs = fun y ↦ (finiteMax fs y : EReal) :=
    funext fun y ↦ indicatorAddMax_of_mem (mem_univ y)
  have hsem := semidifferentiableAt_indicatorAddMax (fs := fs) hs (C := univ) (x := x) (by simp)
  rwa [he] at hsem

/-- **Example 13.10**: along every ray the second-order quotients of a finite maximum of `C²`
functions converge to `max_{i ∈ I'(x̄, w)} ⟪w, ∇²fᵢ(x̄) w⟫`. -/
theorem tendsto_secondDifferenceQuotientAt_finiteMax {fs : ι → E → ℝ}
    (hs : ∀ i, ContDiff ℝ 2 (fs i)) (x w : E) :
    Tendsto (fun τ ↦ secondDifferenceQuotientAt (fun y ↦ (finiteMax fs y : EReal)) x τ w)
      (𝓝[>] 0) (𝓝 (maxSecondDerivative fs x w : EReal)) := by
  classical
  set I := maxActiveIndices fs x
  set d := maxDirectionalDerivative fs x w with hd_def
  set M := maxSecondDerivative fs x w
  have hs1 : ∀ i, ContDiff ℝ 1 (fs i) := fun i ↦ (hs i).of_le (by norm_num)
  have hd : subderivative (fun y ↦ (finiteMax fs y : EReal)) x w = (d : EReal) :=
    subderivative_finiteMax hs1 x w
  set q : ι → ℝ := fun i ↦ fderiv ℝ (fderiv ℝ (fs i)) x w w
  set Q : ι → ℝ → ℝ := fun i τ ↦
    2 / τ ^ 2 * (fs i (x + τ • w) - fs i x - τ * ⟪gradient (fs i) x, w⟫_ℝ)
  have hQ : ∀ i, Tendsto (Q i) (𝓝[>] 0) (𝓝 (q i)) := fun i ↦ by
    have h := tendsto_secondDifferenceQuotient_of_hasFDerivAt (f := fs i)
      (f' := fderiv ℝ (fs i)) (.of_forall fun y ↦ hasFDerivAt_fderiv_of_contDiff_two (hs i) y)
      (hasFDerivAt_fderiv_fderiv_of_contDiff_two (hs i) x)
      (fun u ↦ fderiv_apply_eq_inner_gradient _ x u) w
    have h2 := h.comp (tendsto_pair_const w)
    exact h2
  set Φ : ℝ → ℝ := fun τ ↦ 2 / τ ^ 2 * (finiteMax fs (x + τ • w) - finiteMax fs x - τ * d)
  refine (EReal.tendsto_coe.2 ?_).congr fun τ ↦
    (secondDifferenceQuotientAt_of_coe (f := fun y ↦ (finiteMax fs y : EReal)) rfl hd rfl).symm
  change Tendsto Φ (𝓝[>] 0) (𝓝 M)
  have hid : ∀ i ∈ I, ∀ τ : ℝ, τ ≠ 0 →
      2 / τ ^ 2 * (fs i (x + τ • w) - finiteMax fs x - τ * d) =
        Q i τ - 2 / τ * (d - ⟪gradient (fs i) x, w⟫_ℝ) := by
    intro i hi τ hτ
    simp only [Q]
    rw [← mem_maxActiveIndices.1 hi]
    field_simp
    ring
  have hgap : ∀ i ∈ I, ⟪gradient (fs i) x, w⟫_ℝ ≤ d := fun i hi ↦
    Finset.le_sup' (fun i ↦ ⟪gradient (fs i) x, w⟫_ℝ) hi
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨i, hi, hiM⟩ := Finset.exists_mem_eq_sup' (maxCriticalIndices_nonempty fs x w) q
    obtain ⟨hiI, hid'⟩ := mem_maxCriticalIndices.1 hi
    rw [← hd_def] at hid'
    have hlt : a < q i := lt_of_lt_of_eq ha hiM
    filter_upwards [(hQ i).eventually (lt_mem_nhds hlt), self_mem_nhdsWithin] with τ hτ hτpos
    have hτ0 : (0 : ℝ) < τ := hτpos
    calc a < Q i τ := hτ
      _ = 2 / τ ^ 2 * (fs i (x + τ • w) - finiteMax fs x - τ * d) := by
        rw [hid i hiI τ hτ0.ne', hid', sub_self, mul_zero, sub_zero]
      _ ≤ Φ τ := by
        have h1 : fs i (x + τ • w) ≤ finiteMax fs (x + τ • w) := le_finiteMax fs _ i
        have h2 : 0 ≤ 2 / τ ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) h2
  · intro b hb
    obtain ⟨i₀, hi₀⟩ := maxActiveIndices_nonempty fs x
    have hpath : Tendsto (fun τ : ℝ ↦ x + τ • w) (𝓝[>] 0) (𝓝 x) := by
      have hc : Continuous (fun τ : ℝ ↦ x + τ • w) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hinactive : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ j, j ∉ I → fs j (x + τ • w) < fs i₀ (x + τ • w) := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j ∈ I
      · exact .of_forall fun _ h ↦ (h hj).elim
      · have hlt : fs j x < fs i₀ x := by
          rw [mem_maxActiveIndices.1 hi₀]
          exact lt_of_le_of_ne (le_finiteMax fs x j) fun h ↦ hj (mem_maxActiveIndices.2 h)
        exact ((((hs j).continuous.tendsto x).comp hpath).eventually_lt
          (((hs i₀).continuous.tendsto x).comp hpath) hlt).mono fun _ h _ ↦ h
    have hactive : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ j, j ∈ I → Q j τ - 2 / τ * (d - ⟪gradient (fs j) x, w⟫_ℝ) < b := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j ∈ I
      · rcases (hgap j hj).eq_or_lt with heq | hlt
        · have hjc : j ∈ maxCriticalIndices fs x w := mem_maxCriticalIndices.2 ⟨hj, heq⟩
          have hqM : q j ≤ M := Finset.le_sup' q hjc
          filter_upwards [(hQ j).eventually (gt_mem_nhds (hqM.trans_lt hb))] with τ hτ _
          rw [heq, sub_self, mul_zero, sub_zero]
          exact hτ
        · have hg : 0 < d - ⟪gradient (fs j) x, w⟫_ℝ := sub_pos.2 hlt
          have hinf : Tendsto (fun τ : ℝ ↦ 2 / τ * (d - ⟪gradient (fs j) x, w⟫_ℝ)) (𝓝[>] 0)
              atTop := by
            have h1 : Tendsto (fun τ : ℝ ↦ τ⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
            refine (h1.atTop_mul_const (by positivity :
              0 < 2 * (d - ⟪gradient (fs j) x, w⟫_ℝ))).congr fun τ ↦ ?_
            ring
          filter_upwards [(hQ j).eventually (gt_mem_nhds (lt_add_one (q j))),
            hinf.eventually_gt_atTop (q j + 1 - b)] with τ h1 h2 _
          linarith
      · exact .of_forall fun _ h ↦ (hj h).elim
    filter_upwards [hinactive, hactive, self_mem_nhdsWithin] with τ hin hact hτpos
    have hτ0 : (0 : ℝ) < τ := hτpos
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty
      (fun i ↦ fs i (x + τ • w))
    change finiteMax fs (x + τ • w) = fs j (x + τ • w) at hj
    have hjI : j ∈ I := by
      by_contra h
      exact (hin j h).not_ge ((le_finiteMax fs _ i₀).trans_eq hj)
    have h1 := hact j hjI
    rw [← hid j hjI τ hτ0.ne', ← hj] at h1
    exact h1

/-- **Example 13.10**: if `f` is twice semidifferentiable at `x̄`, then
`d²f(x̄)(w) = max_{i ∈ I'(x̄, w)} ⟪w, ∇²fᵢ(x̄) w⟫`. -/
theorem TwiceSemidifferentiableAt.secondSubderivativeAt_finiteMax {fs : ι → E → ℝ}
    (hs : ∀ i, ContDiff ℝ 2 (fs i)) {x : E}
    (h : TwiceSemidifferentiableAt (fun y ↦ (finiteMax fs y : EReal)) x) (w : E) :
    secondSubderivativeAt (fun y ↦ (finiteMax fs y : EReal)) x w = maxSecondDerivative fs x w := by
  have h1 := (h.2 w).comp (tendsto_pair_const w)
  exact tendsto_nhds_unique h1 (tendsto_secondDifferenceQuotientAt_finiteMax hs x w)

/-- **Example 13.10**: twice semidifferentiability of a finite maximum of `C²` functions forces
`w ↦ max_{i ∈ I'(x̄, w)} ⟪w, ∇²fᵢ(x̄) w⟫` to be continuous, despite the dependence of `I'(x̄, w)`
on `w`. -/
theorem TwiceSemidifferentiableAt.continuous_maxSecondDerivative {fs : ι → E → ℝ}
    (hs : ∀ i, ContDiff ℝ 2 (fs i)) {x : E}
    (h : TwiceSemidifferentiableAt (fun y ↦ (finiteMax fs y : EReal)) x) :
    Continuous (maxSecondDerivative fs x) := by
  have hc := h.finite_continuous.1
  have he : secondSubderivativeAt (fun y ↦ (finiteMax fs y : EReal)) x =
      fun w ↦ (maxSecondDerivative fs x w : EReal) :=
    funext (h.secondSubderivativeAt_finiteMax hs)
  rw [he] at hc
  exact EReal.isEmbedding_coe.continuous_iff.2 hc

/-! ### The counterexample `max{‖x + a‖², 1}` -/

/-- The pair `‖x + a‖²`, `1` whose maximum is the counterexample of Example 13.10. -/
noncomputable def exampleMaxPair (a : E) : Fin 2 → E → ℝ := ![fun x ↦ ‖x + a‖ ^ 2, fun _ ↦ 1]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem finiteMax_exampleMaxPair (a x : E) :
    finiteMax (exampleMaxPair a) x = max (‖x + a‖ ^ 2) 1 := by
  refine le_antisymm (finiteMax_le_iff.2 fun i ↦ ?_)
    (max_le (le_finiteMax (exampleMaxPair a) x 0) (le_finiteMax (exampleMaxPair a) x 1))
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

omit [FiniteDimensional ℝ E] in
theorem contDiff_exampleMaxPair (a : E) (i : Fin 2) : ContDiff ℝ 1 (exampleMaxPair a i) := by
  fin_cases i
  · exact (contDiff_norm_sq ℝ).comp (contDiff_id.add contDiff_const)
  · exact contDiff_const

/-- `df(0)(w) = max{2⟪a, w⟫, 0}` for the counterexample. -/
theorem subderivative_exampleMaxPair {a : E} (ha : ‖a‖ = 1) (w : E) :
    subderivative (fun y ↦ (finiteMax (exampleMaxPair a) y : EReal)) 0 w =
      ((max (2 * ⟪a, w⟫_ℝ) 0 : ℝ) : EReal) := by
  classical
  rw [subderivative_finiteMax (contDiff_exampleMaxPair a) 0 w]
  congr 1
  have hact : maxActiveIndices (exampleMaxPair a) 0 = Finset.univ := by
    ext i
    simp only [mem_maxActiveIndices, Finset.mem_univ, iff_true, finiteMax_exampleMaxPair,
      zero_add, ha]
    fin_cases i <;> simp [exampleMaxPair, ha]
  have hg0 : ⟪gradient (exampleMaxPair a 0) 0, w⟫_ℝ = 2 * ⟪a, w⟫_ℝ := by
    have hf : HasFDerivAt (fun x : E ↦ ‖x + a‖ ^ 2)
        (2 • (innerSL ℝ ((0 : E) + a)).comp (ContinuousLinearMap.id ℝ E)) 0 :=
      ((hasFDerivAt_id (0 : E)).add_const a).norm_sq
    rw [← fderiv_apply_eq_inner_gradient]
    change fderiv ℝ (fun x : E ↦ ‖x + a‖ ^ 2) 0 w = _
    rw [hf.fderiv]
    simp
  have hg1 : ⟪gradient (exampleMaxPair a 1) 0, w⟫_ℝ = 0 := by
    rw [← fderiv_apply_eq_inner_gradient]
    change fderiv ℝ (fun _ : E ↦ (1 : ℝ)) 0 w = 0
    simp
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun i _ ↦ ?_
    fin_cases i
    · exact hg0.trans_le (le_max_left _ _)
    · exact hg1.trans_le (le_max_right _ _)
  · have h0 : (0 : Fin 2) ∈ maxActiveIndices (exampleMaxPair a) 0 := by simp [hact]
    have h1 : (1 : Fin 2) ∈ maxActiveIndices (exampleMaxPair a) 0 := by simp [hact]
    set φ : Fin 2 → ℝ := fun i ↦ ⟪gradient (exampleMaxPair a i) 0, w⟫_ℝ
    exact max_le (hg0.symm.trans_le (Finset.le_sup' φ h0)) (hg1.symm.trans_le (Finset.le_sup' φ h1))

/-- The quotients `Δ²_τ f(0)(w)` of the counterexample. -/
theorem secondDifferenceQuotientAt_exampleMaxPair {a : E} (ha : ‖a‖ = 1) (τ : ℝ) (w : E) :
    secondDifferenceQuotientAt (fun y ↦ (finiteMax (exampleMaxPair a) y : EReal)) 0 τ w =
      ((2 / τ ^ 2 * (max (τ ^ 2 * ‖w‖ ^ 2 + 2 * τ * ⟪a, w⟫_ℝ + 1) 1 - 1 -
        τ * max (2 * ⟪a, w⟫_ℝ) 0) : ℝ) : EReal) := by
  rw [secondDifferenceQuotientAt_of_coe (c := 1)
    (r := max (τ ^ 2 * ‖w‖ ^ 2 + 2 * τ * ⟪a, w⟫_ℝ + 1) 1)
    (by rw [finiteMax_exampleMaxPair, zero_add, ha]; norm_num) (subderivative_exampleMaxPair ha w)]
  rw [finiteMax_exampleMaxPair, zero_add, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, real_inner_smul_left, real_inner_comm, ha]
  congr 2
  ring_nf

/-- `d²f(0)(w) = 2‖w‖²` when `⟪a, w⟫ > 0`. -/
theorem secondSubderivativeAt_exampleMaxPair_of_pos {a w : E} (ha : ‖a‖ = 1)
    (h : TwiceSemidifferentiableAt (fun y ↦ (finiteMax (exampleMaxPair a) y : EReal)) 0)
    (hw : 0 < ⟪a, w⟫_ℝ) :
    secondSubderivativeAt (fun y ↦ (finiteMax (exampleMaxPair a) y : EReal)) 0 w =
      ((2 * ‖w‖ ^ 2 : ℝ) : EReal) := by
  have h1 := (h.2 w).comp (tendsto_pair_const w)
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ0 : (0 : ℝ) < τ := hτ
  simp only [Function.comp_apply]
  rw [secondDifferenceQuotientAt_exampleMaxPair ha,
    max_eq_left (by nlinarith [sq_nonneg (τ * ‖w‖)]),
    max_eq_left (by linarith)]
  congr 1
  field_simp
  ring

/-- `d²f(0)(w) = 0` when `⟪a, w⟫ < 0`. -/
theorem secondSubderivativeAt_exampleMaxPair_of_neg {a w : E} (ha : ‖a‖ = 1)
    (h : TwiceSemidifferentiableAt (fun y ↦ (finiteMax (exampleMaxPair a) y : EReal)) 0)
    (hw : ⟪a, w⟫_ℝ < 0) :
    secondSubderivativeAt (fun y ↦ (finiteMax (exampleMaxPair a) y : EReal)) 0 w = 0 := by
  have h1 := (h.2 w).comp (tendsto_pair_const w)
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
  have hsmall : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ * ‖w‖ ^ 2 < -(2 * ⟪a, w⟫_ℝ) := by
    have hc : Tendsto (fun τ : ℝ ↦ τ * ‖w‖ ^ 2) (𝓝[>] 0) (𝓝 (0 * ‖w‖ ^ 2)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _
    rw [zero_mul] at hc
    exact hc.eventually (gt_mem_nhds (by linarith))
  filter_upwards [self_mem_nhdsWithin, hsmall] with τ hτ hsm
  have hτ0 : (0 : ℝ) < τ := hτ
  simp only [Function.comp_apply]
  rw [secondDifferenceQuotientAt_exampleMaxPair ha, max_eq_right (by nlinarith),
    max_eq_right (by linarith)]
  simp

/-- **Example 13.10**, the counterexample: `f(x) = max{‖x + a‖², 1}` with `‖a‖ = 1` is not twice
semidifferentiable at `0` whenever some `w ≠ 0` is orthogonal to `a` (in `ℝⁿ`, `n ≥ 2`): `d²f(0)`
would equal `2‖·‖²` on `{⟪a, ·⟫ > 0}` and `0` on `{⟪a, ·⟫ < 0}`, so it could not be continuous
at `w`. -/
theorem not_twiceSemidifferentiableAt_exampleMaxPair {a w : E} (ha : ‖a‖ = 1) (hw : w ≠ 0)
    (haw : ⟪a, w⟫_ℝ = 0) :
    ¬ TwiceSemidifferentiableAt (fun y ↦ (finiteMax (exampleMaxPair a) y : EReal)) 0 := by
  intro h
  set H := secondSubderivativeAt (fun y ↦ (finiteMax (exampleMaxPair a) y : EReal)) 0
  have hc : Continuous H := h.finite_continuous.1
  have hpath : ∀ s : ℝ, Tendsto (fun t : ℝ ↦ w + (s * t) • a) (𝓝[>] 0) (𝓝 w) := fun s ↦ by
    have hcont : Continuous (fun t : ℝ ↦ w + (s * t) • a) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hinner : ∀ s t : ℝ, ⟪a, w + (s * t) • a⟫_ℝ = s * t := fun s t ↦ by
    rw [inner_add_right, haw, real_inner_smul_right, real_inner_self_eq_norm_sq, ha]
    ring
  -- along `w + t a` the values are `2‖w + t a‖²`
  have hpos : Tendsto (fun t : ℝ ↦ H (w + (1 * t) • a)) (𝓝[>] 0)
      (𝓝 ((2 * ‖w‖ ^ 2 : ℝ) : EReal)) := by
    have hlim : Tendsto (fun t : ℝ ↦ ((2 * ‖w + (1 * t) • a‖ ^ 2 : ℝ) : EReal)) (𝓝[>] 0)
        (𝓝 ((2 * ‖w‖ ^ 2 : ℝ) : EReal)) :=
      EReal.tendsto_coe.2 (((hpath 1).norm.pow 2).const_mul 2)
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    exact (secondSubderivativeAt_exampleMaxPair_of_pos ha h (by rw [hinner]; linarith)).symm
  -- along `w - t a` the values are `0`
  have hneg : Tendsto (fun t : ℝ ↦ H (w + (-1 * t) • a)) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    exact (secondSubderivativeAt_exampleMaxPair_of_neg ha h (by rw [hinner]; linarith)).symm
  have e1 := tendsto_nhds_unique ((hc.tendsto w).comp (hpath 1)) hpos
  have e2 := tendsto_nhds_unique ((hc.tendsto w).comp (hpath (-1))) hneg
  rw [e1] at e2
  have h0 : 2 * ‖w‖ ^ 2 = 0 := by exact_mod_cast e2
  exact hw (norm_eq_zero.1 (by nlinarith [norm_nonneg w]))

/-- **Example 13.10** (lack of second-order semidifferentiability of max functions). -/
theorem max_functions_second_order {fs : ι → E → ℝ} (hs : ∀ i, ContDiff ℝ 2 (fs i)) (x : E) :
    SemidifferentiableAt (fun y ↦ (finiteMax fs y : EReal)) x ∧
    (∀ w, subderivative (fun y ↦ (finiteMax fs y : EReal)) x w = maxDirectionalDerivative fs x w) ∧
    (∀ w, Tendsto (fun τ ↦ secondDifferenceQuotientAt (fun y ↦ (finiteMax fs y : EReal)) x τ w)
      (𝓝[>] 0) (𝓝 (maxSecondDerivative fs x w : EReal))) ∧
    (TwiceSemidifferentiableAt (fun y ↦ (finiteMax fs y : EReal)) x →
      (∀ w, secondSubderivativeAt (fun y ↦ (finiteMax fs y : EReal)) x w =
        maxSecondDerivative fs x w) ∧ Continuous (maxSecondDerivative fs x)) :=
  ⟨semidifferentiableAt_finiteMax (fun i ↦ (hs i).of_le (by norm_num)) x,
    fun w ↦ subderivative_finiteMax (fun i ↦ (hs i).of_le (by norm_num)) x w,
    tendsto_secondDifferenceQuotientAt_finiteMax hs x,
    fun h ↦ ⟨h.secondSubderivativeAt_finiteMax hs, h.continuous_maxSecondDerivative hs⟩⟩

end RW
