/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second subderivatives of a sum of functions

Proposition 13.19.  For `f = f₁ + ⋯ + f_m` the second-order quotients add, which gives the lower
bound for `d²f(x̄ ∣ v)` without any hypotheses.  For fully amenable summands we follow the proof in
the book: `f = g ∘ F` for the separable function `g(x₁, …, x_m) = f₁(x₁) + ⋯ + f_m(x_m)` on the
Euclidean product and the diagonal map `F(x) = (x, …, x)`; `g` is fully amenable
(`AmenableFunctionModel.separablePi`), Theorem 13.14 applies, and the second subderivatives of `g`
are bounded above by the sums of those of the `fᵢ` because each `fᵢ` is twice epi-differentiable
(`secondSubderivative_separablePi_le`).

The first-order clause recalled from Corollary 10.9, regularity of `f` with
`df(x̄) = Σ dfᵢ(x̄)`, needs the zero-direction conditions `dfᵢ(x̄)(0) = 0`; Chapter 10 refutes it
without them (`qualified_sum_regularity_counterexample`), and there `∂f(x̄) = ∅`
(`SumSecondSubderivativesCounterexample.sum_regularity_counterexample_subdifferential_empty`).
They hold when `∂f(x̄) ≠ ∅`, in particular whenever the second-order statements are not vacuous,
and for fully amenable summands.

**The convention for `∞ - ∞` in the lower bound.**  The sum `Σ d²fᵢ(x̄ ∣ vᵢ)(w)` is Mathlib's sum
in `EReal`, where `∞ + (-∞) = -∞`, so a decomposition with a term `-∞` contributes `-∞` to the
supremum (`ereal_sum_eq_bot_of_mem`).  With the book's default inf-addition `∞ + (-∞) = ∞`
(`infAddition`) the printed inequality fails: `f₁ = x₊^{3/2}` and `f₂ = -x₊^{3/2}` satisfy all
hypotheses at `x̄ = 0` with `v₁ = v₂ = 0`, and `d²f₁(0 ∣ 0)(1) = ∞`, `d²f₂(0 ∣ 0)(1) = -∞`,
`d²(f₁ + f₂)(0 ∣ 0)(1) = 0`
(`SumSecondSubderivativesCounterexample.sum_lower_bound_infAddition_counterexample`).  The two
conventions agree when no term is `-∞`, in particular in the fully amenable clause, where every
`d²fᵢ(x̄ ∣ vᵢ)` is proper.  `second_subderivatives_of_a_sum_supAddition` states 13.19 with the
convention written out: the sums are the book's sup-addition `supAdditionSum`, which is `-∞` as
soon as one term is, and in the fully amenable clause no term is `-∞`.
-/

import RockafellarWets.Chapter13.SecondOrderChainRuleAmenable
import RockafellarWets.Chapter10.FiniteSumSubderivatives
import RockafellarWets.Chapter10.AmenableFiniteSums
import RockafellarWets.Chapter10.FullyAmenableDomains
import RockafellarWets.Chapter10.AmenableSumCalculus
import RockafellarWets.Chapter10.StrictlyContinuousMaxima

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

universe u

namespace RW

/-! ### Sums in `EReal` -/

/-- Multiplication by a positive real distributes over addition in `EReal`. -/
theorem ereal_coe_pos_mul_add {k : ℝ} (hk : 0 < k) (a b : EReal) :
    ((k : ℝ) : EReal) * (a + b) = (k : EReal) * a + (k : EReal) * b := by
  induction a using EReal.rec <;> induction b using EReal.rec <;>
    simp [EReal.coe_mul_top_of_pos hk, EReal.coe_mul_bot_of_pos hk, ← EReal.coe_add,
      ← EReal.coe_mul, mul_add]

/-- Multiplication by a positive real distributes over finite sums in `EReal`. -/
theorem ereal_coe_pos_mul_sum {ι : Type*} (s : Finset ι) {k : ℝ} (hk : 0 < k) (a : ι → EReal) :
    ((k : ℝ) : EReal) * ∑ i ∈ s, a i = ∑ i ∈ s, (k : EReal) * a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ereal_coe_pos_mul_add hk, ih]

/-- The arithmetic of second-order quotients of finite sums. -/
theorem ereal_mul_sum_sub_sub {ι : Type*} (s : Finset ι) {k : ℝ} (hk : 0 < k) (a : ι → EReal)
    (c d : ι → ℝ) :
    ((k : ℝ) : EReal) * (∑ i ∈ s, a i - ((∑ i ∈ s, c i : ℝ) : EReal) -
        ((∑ i ∈ s, d i : ℝ) : EReal)) =
      ∑ i ∈ s, ((k : ℝ) : EReal) * (a i - (c i : EReal) - (d i : EReal)) := by
  have h1 : ∀ (X : EReal) (c d : ℝ),
      X - (c : EReal) - (d : EReal) = X + ((-c - d : ℝ) : EReal) := by
    intro X c d
    rw [sub_eq_add_neg, sub_eq_add_neg, ← EReal.coe_neg, ← EReal.coe_neg, add_assoc,
      ← EReal.coe_add, sub_eq_add_neg]
  simp only [h1, ereal_coe_pos_mul_add hk, ereal_coe_pos_mul_sum s hk, Finset.sum_add_distrib,
    ← EReal.coe_mul]
  congr 1
  rw [← ereal_coe_finset_sum]
  congr 1
  simp only [mul_sub, mul_neg, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_neg_distrib]

/-- Lower limits are superadditive over finite sums in `EReal`. -/
theorem ereal_sum_liminf_le_liminf_sum {α ι : Type*} {l : Filter α} [l.NeBot] (s : Finset ι)
    (u : ι → α → EReal) :
    ∑ i ∈ s, liminf (u i) l ≤ liminf (fun a ↦ ∑ i ∈ s, u i a) l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [liminf_const]
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    calc liminf (u j) l + ∑ i ∈ s, liminf (u i) l
        ≤ liminf (u j) l + liminf (fun a ↦ ∑ i ∈ s, u i a) l := add_le_add le_rfl ih
      _ ≤ liminf (u j + fun a ↦ ∑ i ∈ s, u i a) l := EReal.le_liminf_add
      _ = liminf (fun a ↦ u j a + ∑ i ∈ s, u i a) l := rfl

/-- A finite sum in `EReal` without `-∞` terms is `∞` as soon as one term is. -/
theorem ereal_sum_eq_top_of_mem {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → EReal}
    (hd : ∀ i, d i ≠ ⊥) {i₀ : ι} (hi₀ : d i₀ = ⊤) : ∑ i, d i = ⊤ := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hi₀]
  exact EReal.top_add_of_ne_bot (Finset.sum_induction _ (· ≠ ⊥)
    (fun a b ha hb ↦ EReal.add_ne_bot_iff.2 ⟨ha, hb⟩) EReal.zero_ne_bot (fun i _ ↦ hd i))

/-- A finite sum in `EReal` is `-∞` as soon as one term is: Mathlib's addition on `EReal` has
`∞ + (-∞) = -∞`, unlike the book's default inf-addition `infAddition`.  This is the convention of
the lower bound in `second_subderivatives_of_a_sum`. -/
theorem ereal_sum_eq_bot_of_mem {ι : Type*} [Fintype ι] {d : ι → EReal} {i₀ : ι}
    (hi₀ : d i₀ = ⊥) : ∑ i, d i = ⊥ := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hi₀, EReal.bot_add]

open Classical in
/-- Sup-addition of finitely many extended reals, the convention opposite to the book's default
inf-addition (Section 1.E): the sum is `-∞` as soon as one term is `-∞`, so `∞ + (-∞) = -∞`;
otherwise it is the ordinary sum, which is `∞` if some term is `∞`. -/
noncomputable def supAdditionSum {ι : Type*} [Fintype ι] (d : ι → EReal) : EReal :=
  if ∃ i, d i = ⊥ then ⊥ else ∑ i, d i

/-- Finite sums in `EReal` are sup-additions (`ereal_sum_eq_bot_of_mem`). -/
theorem supAdditionSum_eq_sum {ι : Type*} [Fintype ι] (d : ι → EReal) :
    supAdditionSum d = ∑ i, d i := by
  unfold supAdditionSum
  split_ifs with h
  · obtain ⟨i₀, hi₀⟩ := h
    exact (ereal_sum_eq_bot_of_mem hi₀).symm
  · rfl

/-! ### Quotients of sums -/

section Quotients

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quotients 13(5) of `f₁ + ⋯ + f_m` for `v = v₁ + ⋯ + v_m` are the sums of the quotients of
the `fᵢ` for the `vᵢ`. -/
theorem secondDifferenceQuotient_finiteSum {f : ι → E → EReal} {x : E} {c : ι → ℝ}
    (hx : ∀ i, f i x = c i) (vs : ι → E) {τ : ℝ} (hτ : 0 < τ) (w : E) :
    secondDifferenceQuotient (fun z ↦ ∑ i, f i z) x (∑ i, vs i) τ w =
      ∑ i, secondDifferenceQuotient (f i) x (vs i) τ w := by
  have hk : 0 < 2 / τ ^ 2 := by positivity
  simp only [secondDifferenceQuotient, hx]
  rw [sum_inner, Finset.mul_sum, ← ereal_coe_finset_sum]
  exact ereal_mul_sum_sub_sub Finset.univ hk _ c _

/-- The quotients 13(5) of a separable function are the sums of those of its terms. -/
theorem secondDifferenceQuotient_separablePi {f : ι → E → EReal}
    {z : PiLp 2 (fun _ : ι ↦ E)} {c : ι → ℝ} (hz : ∀ i, f i (z i) = c i)
    (y : PiLp 2 (fun _ : ι ↦ E)) {τ : ℝ} (hτ : 0 < τ) (w : PiLp 2 (fun _ : ι ↦ E)) :
    secondDifferenceQuotient (separablePi f) z y τ w =
      ∑ i, secondDifferenceQuotient (f i) (z i) (y i) τ (w i) := by
  have hk : 0 < 2 / τ ^ 2 := by positivity
  simp only [secondDifferenceQuotient, separablePi, PiLp.add_apply, PiLp.smul_apply, hz]
  rw [l2Pi_inner_apply, Finset.mul_sum, ← ereal_coe_finset_sum]
  exact ereal_mul_sum_sub_sub Finset.univ hk _ c _

/-- **Proposition 13.19**, the inequality: `d²f(x̄ ∣ v)(w) ≥ Σ d²fᵢ(x̄ ∣ vᵢ)(w)` whenever
`v = Σ vᵢ`, for any functions finite at `x̄`. -/
theorem sum_secondSubderivative_le_finiteSum {f : ι → E → EReal} {x : E} {c : ι → ℝ}
    (hx : ∀ i, f i x = c i) (vs : ι → E) (w : E) :
    ∑ i, secondSubderivative (f i) x (vs i) w ≤
      secondSubderivative (fun z ↦ ∑ i, f i z) x (∑ i, vs i) w := by
  unfold secondSubderivative
  refine le_trans (ereal_sum_liminf_le_liminf_sum Finset.univ _) (le_of_eq ?_)
  apply liminf_congr
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
  exact (secondDifferenceQuotient_finiteSum hx vs hp p.2).symm

/-- For twice epi-differentiable terms, the second subderivatives of a separable function are at
most the sums of those of its terms: recovery sequences can be chosen coordinatewise. -/
theorem secondSubderivative_separablePi_le {f : ι → E → EReal} {z y : PiLp 2 (fun _ : ι ↦ E)}
    {c : ι → ℝ} (hz : ∀ i, f i (z i) = c i)
    (hf : ∀ i, ProperlyTwiceEpiDifferentiableAt (f i) (z i) (y i))
    (w : PiLp 2 (fun _ : ι ↦ E)) :
    secondSubderivative (separablePi f) z y w ≤
      ∑ i, secondSubderivative (f i) (z i) (y i) (w i) := by
  classical
  have hdb : ∀ i, secondSubderivative (f i) (z i) (y i) (w i) ≠ ⊥ :=
    fun i ↦ ((hf i).2.2 (w i)).ne'
  by_cases htop : ∃ i, secondSubderivative (f i) (z i) (y i) (w i) = ⊤
  · obtain ⟨i₀, hi₀⟩ := htop
    rw [ereal_sum_eq_top_of_mem hdb hi₀]
    exact le_top
  push_neg at htop
  set α : ι → ℝ := fun i ↦ (secondSubderivative (f i) (z i) (y i) (w i)).toReal with hαdef
  have hα : ∀ i, secondSubderivative (f i) (z i) (y i) (w i) = ((α i : ℝ) : EReal) :=
    fun i ↦ (EReal.coe_toReal (htop i) (hdb i)).symm
  have hsum : ∑ i, secondSubderivative (f i) (z i) (y i) (w i) = ((∑ i, α i : ℝ) : EReal) := by
    rw [ereal_coe_finset_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hα i
  rw [hsum]
  refine le_of_forall_gt_imp_ge_of_dense fun b hb ↦ ?_
  induction b using EReal.rec with
  | bot => exact absurd hb (not_lt_bot)
  | top => exact le_top
  | coe b =>
  have hb' : ∑ i, α i < b := EReal.coe_lt_coe_iff.1 hb
  set ε : ℝ := (b - ∑ i, α i) / (Fintype.card ι + 1) with hεdef
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hlt : ∑ i, (α i + ε) < b := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card ι : ℝ) * ε < (Fintype.card ι + 1) * ε :=
      mul_lt_mul_of_pos_right (by linarith) hε
    have he : ((Fintype.card ι : ℝ) + 1) * ε = b - ∑ i, α i := by
      rw [hεdef]
      field_simp
    linarith
  apply Filter.liminf_le_of_frequently_le'
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.1 hU
  have hB' : (WithLp.toLp 2 : (ι → E) → PiLp 2 (fun _ : ι ↦ E)) ⁻¹' B ∈
      𝓝 (WithLp.ofLp w) :=
    (PiLp.continuous_toLp 2 _).continuousAt.preimage_mem_nhds (by rw [WithLp.toLp_ofLp]; exact hB)
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 hB'
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ i,
      (epigraph (secondDifferenceQuotient (f i) (z i) (y i) τ) ∩
        (ball (w i) η ×ˢ Iio (α i + ε))).Nonempty := by
    rw [Filter.eventually_all]
    intro i
    have hmem : (w i, α i) ∈ epigraph (secondSubderivative (f i) (z i) (y i)) := by
      change ((α i : ℝ) : EReal) ≥ secondSubderivative (f i) (z i) (y i) (w i)
      rw [hα i]
    rw [← (hf i).1.2.2.1] at hmem
    exact hmem _ (prod_mem_nhds (ball_mem_nhds _ hη) (Iio_mem_nhds (by linarith)))
  obtain ⟨τ, ⟨hτA, hτpos⟩, hτ⟩ :=
    Filter.nonempty_of_mem (Filter.inter_mem (Filter.inter_mem hA self_mem_nhdsWithin) hev)
  choose p hp using hτ
  refine ⟨(τ, WithLp.toLp 2 (fun i ↦ (p i).1)), hAB ⟨hτA, hball ?_⟩, ?_⟩
  · rw [mem_ball, dist_pi_lt_iff hη]
    intro i
    exact (hp i).2.1
  · change secondDifferenceQuotient (separablePi f) z y τ (WithLp.toLp 2 (fun i ↦ (p i).1)) ≤ b
    rw [secondDifferenceQuotient_separablePi hz y hτpos]
    calc ∑ i, secondDifferenceQuotient (f i) (z i) (y i) τ
          ((WithLp.toLp 2 (fun i ↦ (p i).1) : PiLp 2 (fun _ : ι ↦ E)) i)
        ≤ ∑ i, (((p i).2 : ℝ) : EReal) := Finset.sum_le_sum fun i _ ↦ (hp i).1
      _ ≤ ∑ i, ((α i + ε : ℝ) : EReal) :=
        Finset.sum_le_sum fun i _ ↦ EReal.coe_le_coe_iff.2 (le_of_lt (hp i).2.2)
      _ = ((∑ i, (α i + ε) : ℝ) : EReal) := (ereal_coe_finset_sum _ _).symm
      _ ≤ b := EReal.coe_le_coe_iff.2 (le_of_lt hlt)

end Quotients

/-! ### Amenability of separable functions -/

section Amenable

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type u} [Fintype ι]

/-- Amenable models of the terms give one of the separable function
`(x₁, …, x_m) ↦ f₁(x₁) + ⋯ + f_m(x_m)` (a case of 10.26(a)); no qualification across the terms is
needed. -/
noncomputable def AmenableFunctionModel.separablePi {f : ι → E → EReal}
    {z : PiLp 2 (fun _ : ι ↦ E)} {r : ℕ} {full : Bool}
    (M : ∀ i, AmenableFunctionModel (f i) (z i) r full) (hr : 1 ≤ r) :
    AmenableFunctionModel (RW.separablePi f) z r full where
  Target := PiLp 2 (fun i ↦ (M i).Target)
  outer := dependentSeparablePi (fun i ↦ (M i).outer)
  inner := fun y ↦ WithLp.toLp 2 (fun i ↦ (M i).inner (y i))
  neighborhood := ⋂ i, (fun y : PiLp 2 (fun _ : ι ↦ E) ↦ y i) ⁻¹' (M i).neighborhood
  isOpen := isOpen_iInter_of_finite fun i ↦ (M i).isOpen.preimage (PiLp.continuous_apply 2 _ i)
  mem := mem_iInter.mpr fun i ↦ (M i).mem
  finite := by
    have hh : RW.separablePi f z = ((∑ i, (f i (z i)).toReal : ℝ) : EReal) :=
      separablePi_eq_coe (fun i ↦ (EReal.coe_toReal (M i).finite.2 (M i).finite.1).symm)
    rw [hh]
    exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  proper := isProper_dependentSeparablePi (fun i ↦ (M i).proper)
  lsc := lowerSemicontinuous_dependentSeparablePi (fun i ↦ (M i).lsc) (fun i ↦ (M i).proper.2)
  convex := convex_epigraph_dependentSeparablePi (fun i ↦ (M i).proper) (fun i ↦ (M i).convex)
  smooth := (PiLp.continuousLinearEquiv 2 ℝ (fun i ↦ (M i).Target)).symm.contDiff.contDiffOn.comp
    (contDiffOn_pi.mpr fun i ↦ ((M i).smooth.comp
      (show ContDiffOn ℝ r (fun y : PiLp 2 (fun _ : ι ↦ E) ↦ y i) _ from
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ↦ E) i).contDiff (n := r)).contDiffOn)
      (fun y hy ↦ mem_iInter.mp hy i)))
    (fun _ _ ↦ mem_univ _)
  eqOn := by
    intro y hy
    exact Finset.sum_congr rfl fun i _ ↦ (M i).eqOn (y i) (mem_iInter.mp hy i)
  qualification := by
    intro v hv hz
    rw [effectiveDomain_dependentSeparablePi (fun i ↦ (M i).proper), closure_l2PiSet,
      normalCone_l2PiSet] at hv
    have hmd (i : ι) : DifferentiableAt ℝ (M i).inner (z i) :=
      (((M i).smooth (z i) (M i).mem).contDiffAt ((M i).isOpen.mem_nhds (M i).mem)).differentiableAt
        (by exact_mod_cast (show r ≠ 0 by omega))
    have hd := (PiLp.continuousLinearEquiv 2 ℝ (fun i ↦ (M i).Target)).symm.toContinuousLinearMap
      |>.hasFDerivAt.comp z (hasFDerivAt_pi.mpr fun i ↦
        (hmd i).hasFDerivAt.comp z (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι ↦ E) i).hasFDerivAt)
    change HasFDerivAt (fun y ↦ WithLp.toLp 2 (fun i ↦ (M i).inner (y i))) _ z at hd
    have ha : (fderiv ℝ (fun y : PiLp 2 (fun _ : ι ↦ E) ↦
        WithLp.toLp 2 (fun i ↦ (M i).inner (y i))) z).adjoint v =
        WithLp.toLp 2 (fun i ↦ (fderiv ℝ (M i).inner (z i)).adjoint (v i)) := by
      rw [hd.fderiv]
      apply ext_inner_right ℝ
      intro w
      rw [ContinuousLinearMap.adjoint_inner_left]
      change ⟪v, WithLp.toLp 2 (fun i ↦ fderiv ℝ (M i).inner (z i) (w i))⟫_ℝ = _
      simp [PiLp.inner_apply, ContinuousLinearMap.adjoint_inner_left]
    rw [ha] at hz
    ext i
    have hzi : (fderiv ℝ (M i).inner (z i)).adjoint (v i) = 0 := by
      have h := congrArg (fun q : PiLp 2 (fun _ : ι ↦ E) ↦ q i) hz
      simpa using h
    exact (M i).qualification (v i) (hv i) hzi
  plq := by
    intro hf
    apply IsPiecewiseLinearQuadratic.sum Finset.univ
    intro i _
    simpa using ((M i).plq hf).compAffine (PiLp.proj (𝕜 := ℝ) 2 (fun i ↦ (M i).Target) i) 0

/-- A separable sum of fully amenable functions is fully amenable. -/
theorem FullyAmenableAt.separablePi {f : ι → E → EReal} {z : PiLp 2 (fun _ : ι ↦ E)}
    (hf : ∀ i, FullyAmenableAt (f i) (z i)) : FullyAmenableAt (RW.separablePi f) z :=
  ⟨AmenableFunctionModel.separablePi (fun i ↦ Classical.choice (hf i)) (by norm_num)⟩

/-- **Proposition 13.19** (second subderivatives of a sum of functions), with the first-order
clause corrected.  Let `f = f₁ + ⋯ + f_m` for proper lsc `fᵢ`, all finite and regular at `x̄`,
under the qualification `vᵢ ∈ ∂^∞fᵢ(x̄), Σ vᵢ = 0 ⇒ vᵢ = 0`.  Then `∂f(x̄) = Σ ∂fᵢ(x̄)`, and if
`∂f(x̄) ≠ ∅`, `f` is regular at `x̄` with `df(x̄) = Σ dfᵢ(x̄)` (Chapter 10 shows that this needs
`∂f(x̄) ≠ ∅` or another zero-direction condition).  For every `v ∈ ∂f(x̄)`,
`d²f(x̄ ∣ v)(w) ≥ sup {Σ d²fᵢ(x̄ ∣ vᵢ)(w) ∣ vᵢ ∈ ∂fᵢ(x̄), Σ vᵢ = v}`, the sums taken in `EReal`,
where `∞ + (-∞) = -∞` (`ereal_sum_eq_bot_of_mem`; with the book's inf-addition the bound fails,
`SumSecondSubderivativesCounterexample.sum_lower_bound_infAddition_counterexample`), with equality
when every `fᵢ` is fully amenable at `x̄`; then `f` is fully amenable at `x̄` and properly twice
epi-differentiable at `x̄` for `v`. -/
theorem second_subderivatives_of_a_sum {f : ι → E → EReal} (hp : ∀ i, IsProper (f i))
    (hl : ∀ i, LowerSemicontinuous (f i)) {x : E} (hx : ∀ i, x ∈ effectiveDomain (f i))
    (hr : ∀ i, IsSubdifferentiallyRegularAt (f i) x)
    (hQ : ∀ v : ι → E, (∀ i, v i ∈ horizonSubdifferential (f i) x) →
      ∑ i, v i = 0 → ∀ i, v i = 0) :
    subdifferential (fun z ↦ ∑ i, f i z) x = finiteSetSum (fun i ↦ subdifferential (f i) x) ∧
    ((subdifferential (fun z ↦ ∑ i, f i z) x).Nonempty →
      IsSubdifferentiallyRegularAt (fun z ↦ ∑ i, f i z) x ∧
      ∀ w, subderivative (fun z ↦ ∑ i, f i z) x w = ∑ i, subderivative (f i) x w) ∧
    (∀ v ∈ subdifferential (fun z ↦ ∑ i, f i z) x, ∀ w,
      (⨆ (vs : ι → E) (_ : (∀ i, vs i ∈ subdifferential (f i) x) ∧ ∑ i, vs i = v),
        ∑ i, secondSubderivative (f i) x (vs i) w) ≤
      secondSubderivative (fun z ↦ ∑ i, f i z) x v w) ∧
    ((∀ i, FullyAmenableAt (f i) x) →
      FullyAmenableAt (fun z ↦ ∑ i, f i z) x ∧
      ∀ v ∈ subdifferential (fun z ↦ ∑ i, f i z) x,
        ProperlyTwiceEpiDifferentiableAt (fun z ↦ ∑ i, f i z) x v ∧
        ∀ w, secondSubderivative (fun z ↦ ∑ i, f i z) x v w =
          ⨆ (vs : ι → E) (_ : (∀ i, vs i ∈ subdifferential (f i) x) ∧ ∑ i, vs i = v),
            ∑ i, secondSubderivative (f i) x (vs i) w) := by
  classical
  have hc : ∀ i, f i x = ((f i x).toReal : EReal) := fun i ↦
    (EReal.coe_toReal (ne_of_lt (hx i)) ((hp i).2 x).ne').symm
  have hsub := subdifferential_finiteSum_eq_of_regular hp hl hr hQ
  have hlow : ∀ v ∈ subdifferential (fun z ↦ ∑ i, f i z) x, ∀ w,
      (⨆ (vs : ι → E) (_ : (∀ i, vs i ∈ subdifferential (f i) x) ∧ ∑ i, vs i = v),
        ∑ i, secondSubderivative (f i) x (vs i) w) ≤
      secondSubderivative (fun z ↦ ∑ i, f i z) x v w := by
    intro v _ w
    refine iSup₂_le fun vs hvs ↦ ?_
    rw [← hvs.2]
    exact sum_secondSubderivative_le_finiteSum hc vs w
  refine ⟨hsub, fun hne ↦ ?_, hlow, fun hfa ↦ ?_⟩
  · -- the zero-direction conditions come from a subgradient
    obtain ⟨v, hv⟩ := hne
    rw [hsub] at hv
    obtain ⟨vs, hvs, -⟩ := hv
    have h0 : ∀ i, subderivative (f i) x 0 = 0 := by
      intro i
      have hreg : vs i ∈ regularSubdifferential (f i) x := by
        rw [← (hr i).subdifferential_eq_regularSubdifferential]; exact hvs i
      have hle := inner_le_subderivative_of_mem_regularSubdifferential hreg 0
      rw [inner_zero_right, EReal.coe_zero] at hle
      exact (subderivative_zero_eq_zero_or_bot (hc i)).resolve_right fun hb ↦ by
        rw [hb] at hle; exact absurd hle (by simp)
    exact finiteSum_regularity_of_calm hp hl hr h0 hQ
  · -- fully amenable terms
    have hQdom : ∀ v : ι → E, (∀ i, v i ∈ normalCone (effectiveDomain (f i)) x) →
        ∑ i, v i = 0 → ∀ i, v i = 0 := fun v hv hs ↦
      hQ v (fun i ↦ by rw [(hfa i).horizon_eq_normal_domain]; exact hv i) hs
    refine ⟨FullyAmenableAt.finiteSum hfa hQdom, fun v hv ↦ ?_⟩
    have hGx : ∀ i, (finiteDiagonal (ι := ι) x) i = x := fun i ↦ by simp
    have hg : FullyAmenableAt (separablePi f) (finiteDiagonal (ι := ι) x) :=
      FullyAmenableAt.separablePi fun i ↦ by rw [hGx i]; exact hfa i
    have hcomp : separablePi f ∘ finiteDiagonal (ι := ι) = fun z ↦ ∑ i, f i z := by
      funext z
      simp [separablePi]
    have hcG : ∀ i, f i ((finiteDiagonal (ι := ι) x) i) = ((f i x).toReal : EReal) := fun i ↦ by
      rw [hGx i]; exact hc i
    have hQ₀ := finiteSum_horizon_qualification hp hl hc hQ
    have hv' : v ∈ subdifferential (separablePi f ∘ finiteDiagonal (ι := ι)) x := by
      rw [hcomp]; exact hv
    obtain ⟨hsup, hpte, -⟩ :=
      chain_rule_second_subderivatives_fullyAmenable (G := ⇑(finiteDiagonal (ι := ι) (E := E)))
        (g := RW.separablePi f) (x := x) (v := v) (finiteDiagonal (ι := ι) (E := E)).contDiff hg
        hQ₀ hv'
    rw [hcomp] at hsup hpte
    refine ⟨hpte, fun w ↦ le_antisymm ?_ (hlow v hv w)⟩
    rw [hsup w]
    refine iSup₂_le fun y hy ↦ ?_
    have hy1 : ∀ i, y i ∈ subdifferential (f i) x := by
      have h := (mem_subdifferential_separablePi_iff f hp hl _ y _ hcG).1 hy.1
      intro i
      rw [← hGx i]
      exact h i
    have hy2 : ∑ i, y i = v := by
      have h := hy.2
      rw [ContinuousLinearMap.fderiv, finiteDiagonal_adjoint, l2PiSum_apply] at h
      exact h
    have hGG : fderiv ℝ (fderiv ℝ (finiteDiagonal (ι := ι) (E := E))) x = 0 := by
      rw [show fderiv ℝ (finiteDiagonal (ι := ι) (E := E)) = fun _ ↦ finiteDiagonal from
        funext fun _ ↦ ContinuousLinearMap.fderiv _]
      exact fderiv_const_apply _
    rw [hGG, ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
      EReal.coe_zero, add_zero, ContinuousLinearMap.fderiv]
    refine le_trans (secondSubderivative_separablePi_le hcG (fun i ↦ ?_) _) ?_
    · rw [hGx i]
      exact (hfa i).properlyTwiceEpiDifferentiableAt (hy1 i)
    · refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (vs : ι → E)
        (_ : (∀ i, vs i ∈ subdifferential (f i) x) ∧ ∑ i, vs i = v) ↦
          ∑ i, secondSubderivative (f i) x (vs i) w) (fun i ↦ y i) ⟨hy1, hy2⟩)
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hGx i]
      simp

/-- **Proposition 13.19** with the convention for `∞ - ∞` in the lower bound explicit.  The
hypotheses and conclusions are those of `second_subderivatives_of_a_sum`, with each sum
`Σ d²fᵢ(x̄ ∣ vᵢ)(w)` written as the sup-addition `supAdditionSum`: a decomposition `v = Σ vᵢ` with
some `d²fᵢ(x̄ ∣ vᵢ)(w) = -∞` contributes `-∞` to the supremum, while with the book's default
inf-addition the bound fails
(`SumSecondSubderivativesCounterexample.sum_lower_bound_infAddition_counterexample`).  When
every `fᵢ` is fully amenable at `x̄`, no `d²fᵢ(x̄ ∣ vᵢ)(w)` with `vᵢ ∈ ∂fᵢ(x̄)` is `-∞`, so there
the two conventions give the same sums. -/
theorem second_subderivatives_of_a_sum_supAddition {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hl : ∀ i, LowerSemicontinuous (f i)) {x : E}
    (hx : ∀ i, x ∈ effectiveDomain (f i)) (hr : ∀ i, IsSubdifferentiallyRegularAt (f i) x)
    (hQ : ∀ v : ι → E, (∀ i, v i ∈ horizonSubdifferential (f i) x) →
      ∑ i, v i = 0 → ∀ i, v i = 0) :
    subdifferential (fun z ↦ ∑ i, f i z) x = finiteSetSum (fun i ↦ subdifferential (f i) x) ∧
    ((subdifferential (fun z ↦ ∑ i, f i z) x).Nonempty →
      IsSubdifferentiallyRegularAt (fun z ↦ ∑ i, f i z) x ∧
      ∀ w, subderivative (fun z ↦ ∑ i, f i z) x w = ∑ i, subderivative (f i) x w) ∧
    (∀ v ∈ subdifferential (fun z ↦ ∑ i, f i z) x, ∀ w,
      (⨆ (vs : ι → E) (_ : (∀ i, vs i ∈ subdifferential (f i) x) ∧ ∑ i, vs i = v),
        supAdditionSum fun i ↦ secondSubderivative (f i) x (vs i) w) ≤
      secondSubderivative (fun z ↦ ∑ i, f i z) x v w) ∧
    ((∀ i, FullyAmenableAt (f i) x) →
      FullyAmenableAt (fun z ↦ ∑ i, f i z) x ∧
      (∀ vs : ι → E, (∀ i, vs i ∈ subdifferential (f i) x) →
        ∀ i w, secondSubderivative (f i) x (vs i) w ≠ ⊥) ∧
      ∀ v ∈ subdifferential (fun z ↦ ∑ i, f i z) x,
        ProperlyTwiceEpiDifferentiableAt (fun z ↦ ∑ i, f i z) x v ∧
        ∀ w, secondSubderivative (fun z ↦ ∑ i, f i z) x v w =
          ⨆ (vs : ι → E) (_ : (∀ i, vs i ∈ subdifferential (f i) x) ∧ ∑ i, vs i = v),
            supAdditionSum fun i ↦ secondSubderivative (f i) x (vs i) w) := by
  simp only [supAdditionSum_eq_sum]
  obtain ⟨h1, h2, h3, h4⟩ := second_subderivatives_of_a_sum hp hl hx hr hQ
  refine ⟨h1, h2, h3, fun hfa ↦ ⟨(h4 hfa).1, fun vs hvs i w ↦ ?_, (h4 hfa).2⟩⟩
  exact (((hfa i).properlyTwiceEpiDifferentiableAt (hvs i)).2.2 w).ne'

end Amenable

end RW
