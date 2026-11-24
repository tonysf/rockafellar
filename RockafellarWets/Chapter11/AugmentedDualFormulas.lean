/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The augmented dual objective in the convex case

Formula 11(29) of Exercise 11.56 and its closing assertion. With `f` jointly
convex and `σ` finite, `-ψ̄(·,r)` is conjugate to `p + rσ`; adding the
continuous function `rσ` commutes with lower closure, so the interior sum
rule of 11.23(a) applies to `cl p + rσ` without any semicontinuity of `f`.
The closing assertion holds in one direction only: a maximizer of `ψ` gives
maximizers `(ȳ,r)` of `ψ̄` for every `r > 0`, but for `f(x,u) = u²/2` and the
sharp augmenting function `|u|` the pair `(1/2, 1)` maximizes `ψ̄` while `1/2`
does not maximize `ψ`.
-/
import RockafellarWets.Chapter11.ProximalSharpLagrangians
import RockafellarWets.Chapter11.ConjugateInvariance
import RockafellarWets.Chapter3.LowerClosureProperness

open Set Filter Topology Metric
open scoped InnerProductSpace Pointwise
namespace RW
noncomputable section

section Closure

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

omit [InnerProductSpace ℝ P] in
/-- Adding a continuous finite function commutes with lower closure. -/
theorem epiClosure_add_coe {g : P → EReal} {h : P → ℝ} (hh : Continuous h) :
    epiClosure (fun u ↦ g u + (h u : EReal)) = fun u ↦ epiClosure g u + (h u : EReal) := by
  let Ψ : (P × ℝ) ≃ₜ (P × ℝ) :=
    { toFun := fun q ↦ (q.1, q.2 - h q.1)
      invFun := fun q ↦ (q.1, q.2 + h q.1)
      left_inv := fun q ↦ by simp
      right_inv := fun q ↦ by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hpre : ∀ k : P → EReal,
      epigraph (fun u ↦ k u + (h u : EReal)) = Ψ ⁻¹' epigraph k := by
    intro k
    ext q
    change k q.1 + (h q.1 : EReal) ≤ (q.2 : EReal) ↔ k q.1 ≤ ((q.2 - h q.1 : ℝ) : EReal)
    exact ereal_add_coe_le_coe_iff _ _ _
  apply eq_of_epigraph_eq
  rw [epigraph_epiClosure, hpre, hpre, ← Ψ.preimage_closure, epigraph_epiClosure]

end Closure

section Formula

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  {f : WithLp 2 (E × P) → EReal} {σ : P → EReal}

omit [FiniteDimensional ℝ P] in
/-- A finite function with convex epigraph is a real convex function. -/
theorem convexOn_toReal_of_convex_epigraph {g : P → EReal} (hg : Convex ℝ (epigraph g))
    (hgt : ∀ u, g u ≠ ⊤) (hgb : ∀ u, g u ≠ ⊥) : ConvexOn ℝ univ (fun u ↦ (g u).toReal) := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab ↦ ?_⟩
  have hu : (u, (g u).toReal) ∈ epigraph g :=
    show ((g u).toReal : EReal) ≥ g u from (EReal.coe_toReal (hgt u) (hgb u)).ge
  have hv : (v, (g v).toReal) ∈ epigraph g :=
    show ((g v).toReal : EReal) ≥ g v from (EReal.coe_toReal (hgt v) (hgb v)).ge
  have h := hg hu hv ha hb hab
  change g (a • u + b • v) ≤ ((a * (g u).toReal + b * (g v).toReal : ℝ) : EReal) at h
  rw [← EReal.coe_toReal (hgt (a • u + b • v)) (hgb _), EReal.coe_le_coe_iff] at h
  simpa only [smul_eq_mul] using h

/-- **Exercise 11.56**, formula 11(29): for jointly convex `f` and a finite
augmenting function, `ψ̄(y,r) = sup_z {ψ(y-z) - rσ*(r⁻¹z)}`. -/
theorem augmentedDualObjective_eq_iSup_dualObjective (hfc : Convex ℝ (epigraph f))
    (hσ : IsAugmentingFunction σ) (hσt : ∀ u, σ u ≠ ⊤) {r : ℝ} (hr : 0 < r) (y : P) :
    augmentedDualObjective f σ y r =
      ⨆ z, dualObjective f (y - z) - (r : EReal) * fenchelConjugate σ (r⁻¹ • z) := by
  have hσb : ∀ u, σ u ≠ ⊥ := fun u ↦ (hσ.isProper.2 u).ne'
  set h : P → ℝ := fun u ↦ r * (σ u).toReal with hhdef
  have hσh : ∀ u, (r : EReal) * σ u = (h u : EReal) := fun u ↦ by
    rw [hhdef, EReal.coe_mul, EReal.coe_toReal (hσt u) (hσb u)]
  have hhc : Continuous h := by
    have hco := (convexOn_toReal_of_convex_epigraph hσ.convex hσt hσb).continuousOn_interior
    rw [interior_univ] at hco
    exact continuous_const.mul (continuousOn_univ.mp hco)
  set p := parametricValue f with hpdef
  -- the augmented dual objective through the marginal function
  have hψ : augmentedDualObjective f σ y r =
      -fenchelConjugate (fun u ↦ p u + (h u : EReal)) y := by
    rw [← iInf_sub_inner_eq_neg_fenchelConjugate, augmentedDualObjective, iInf_comm]
    refine iInf_congr fun u ↦ ?_
    have hiso := (erealAddRightOrderIso (h u - ⟪y, u⟫_ℝ)).map_iInf
      (fun x : E ↦ f (WithLp.toLp 2 (x, u)))
    simp only [erealAddRightOrderIso_apply] at hiso
    have he : ∀ a : EReal, a + (r : EReal) * σ u - (⟪y, u⟫_ℝ : EReal) =
        a + ((h u - ⟪y, u⟫_ℝ : ℝ) : EReal) := fun a ↦ by
      rw [hσh, EReal.coe_sub, sub_eq_add_neg, sub_eq_add_neg, add_assoc]
    simp only [he]
    rw [← hiso, ← he, hσh]
    rfl
  have hconjp : ∀ v, fenchelConjugate p v = -dualObjective f v := fun v ↦ by
    rw [hpdef, fenchelConjugate_parametricValue, dualObjective, neg_neg]
  have hsub : ∀ (a : EReal) (z : P),
      a - (r : EReal) * fenchelConjugate σ (r⁻¹ • z) ≤ a := fun a z ↦ by
    have h0 : 0 ≤ (r : EReal) * fenchelConjugate σ (r⁻¹ • z) :=
      EReal.mul_nonneg (EReal.coe_nonneg.mpr hr.le) (hσ.fenchelConjugate_nonneg _)
    rw [sub_eq_add_neg]
    calc a + -((r : EReal) * fenchelConjugate σ (r⁻¹ • z)) ≤ a + 0 :=
          add_le_add_right (EReal.neg_le_zero.mpr h0) a
      _ = a := add_zero a
  have hz0 : ∀ v, dualObjective f v ≤
      ⨆ z, dualObjective f (v - z) - (r : EReal) * fenchelConjugate σ (r⁻¹ • z) := fun v ↦
    le_iSup_of_le 0 (by rw [sub_zero, smul_zero, hσ.fenchelConjugate_zero, mul_zero, sub_zero])
  by_cases htop : ∀ u, p u = ⊤
  · -- empty marginal domain
    have hfun : (fun u ↦ p u + (h u : EReal)) = fun _ ↦ ⊤ := funext fun u ↦ by
      rw [htop u, EReal.top_add_coe]
    have hdual : dualObjective f y = ⊤ := by
      have := congrFun (congrArg fenchelConjugate (show p = fun _ ↦ ⊤ from funext htop)) y
      rw [identically_top_conjugates.1, hconjp] at this
      exact EReal.neg_eq_bot_iff.mp this
    rw [hψ, hfun, identically_top_conjugates.1, EReal.neg_bot]
    exact le_antisymm (hdual ▸ hz0 y) le_top
  by_cases hbot : ∃ u₀, p u₀ = ⊥
  · -- the marginal function takes `-∞`
    obtain ⟨u₀, hu₀⟩ := hbot
    have hconj : ∀ v, fenchelConjugate (fun u ↦ p u + (h u : EReal)) v = ⊤ := fun v ↦ by
      refine top_le_iff.mp ((le_fenchelConjugate _ u₀ v).trans' ?_)
      rw [hu₀, EReal.bot_add, EReal.sub_bot (EReal.coe_ne_bot _)]
    have hdual : ∀ v, dualObjective f v = ⊥ := fun v ↦ by
      have h1 : fenchelConjugate p v = ⊤ := by
        refine top_le_iff.mp ((le_fenchelConjugate _ u₀ v).trans' ?_)
        rw [hu₀, EReal.sub_bot (EReal.coe_ne_bot _)]
      rw [hconjp, EReal.neg_eq_top_iff] at h1
      exact h1
    rw [hψ, hconj, EReal.neg_top]
    refine le_antisymm bot_le (iSup_le fun z ↦ ?_)
    rw [hdual, EReal.bot_sub]
  -- the proper case
  push_neg at htop hbot
  have hpp : IsProper p := ⟨by simpa [lt_top_iff_ne_top] using htop,
    fun u ↦ bot_lt_iff_ne_bot.mpr (hbot u)⟩
  have hpc : Convex ℝ (epigraph p) := convex_epigraph_parametricValue_of_convex hfc
  have hclp : IsProper (epiClosure p) := isProper_of_isLowerClosure hpp hpc (epigraph_epiClosure p)
  have hcll : LowerSemicontinuous (epiClosure p) := by
    apply lowerSemicontinuous_of_isClosed_epigraph_ereal
    rw [epigraph_epiClosure]
    exact isClosed_closure
  have hclc : Convex ℝ (epigraph (epiClosure p)) := by
    rw [epigraph_epiClosure]
    exact hpc.closure
  have hq : IsProper (fun u ↦ (h u : EReal)) :=
    ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩
  have hk : LowerSemicontinuous (fun u ↦ (h u : EReal)) :=
    (continuous_coe_real_ereal.comp hhc).lowerSemicontinuous
  have hd : Convex ℝ (epigraph (fun u ↦ (h u : EReal))) := by
    have he : (fun u ↦ (h u : EReal)) = fun u ↦ (r : EReal) * σ u := funext fun u ↦ (hσh u).symm
    rw [he]
    exact convex_epigraph_coe_mul hσ.convex hr
  have h0 : (0 : P) ∈ interior (effectiveDomain (epiClosure p) -
      effectiveDomain (fun u ↦ (h u : EReal))) := by
    obtain ⟨u₀, hu₀⟩ := hclp.1
    have he : effectiveDomain (epiClosure p) - effectiveDomain (fun u ↦ (h u : EReal)) = univ := by
      have hdom : effectiveDomain (fun u ↦ (h u : EReal)) = univ :=
        eq_univ_of_forall fun u ↦ EReal.coe_lt_top _
      rw [hdom]
      exact eq_univ_of_forall fun v ↦ ⟨u₀, hu₀, u₀ - v, mem_univ _, sub_sub_cancel u₀ v⟩
    rw [he, interior_univ]
    exact mem_univ _
  have hsum := fenchelConjugate_add_of_interior hclp hq hcll hk hclc hd h0
  have hcl : fenchelConjugate (fun u ↦ p u + (h u : EReal)) =
      epiSum (fenchelConjugate p) (fenchelConjugate (fun u ↦ (h u : EReal))) := by
    rw [← fenchelConjugate_epiClosure (fun u ↦ p u + (h u : EReal)), epiClosure_add_coe hhc,
      hsum, fenchelConjugate_epiClosure]
  rw [hψ, hcl, epiSum_apply, show ∀ g : P → EReal, -(⨅ w, g w) = ⨆ w, -g w from
    fun g ↦ EReal.negOrderIso.map_iInf g]
  refine iSup_congr fun z ↦ ?_
  have hhσ : (fun u ↦ (h u : EReal)) = fun u ↦ (r : EReal) * σ u := funext fun u ↦ (hσh u).symm
  have hpb : fenchelConjugate p (y - z) ≠ ⊥ := by
    obtain ⟨u₀, hu₀⟩ := hpp.1
    obtain ⟨a, ha⟩ : ∃ a : ℝ, p u₀ = a := ⟨_, (EReal.coe_toReal hu₀.ne (hpp.2 u₀).ne').symm⟩
    have hle := le_fenchelConjugate p u₀ (y - z)
    rw [ha, ← EReal.coe_sub] at hle
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
  rw [hhσ, fenchelConjugate_coe_mul σ hr, EReal.neg_add (Or.inl hpb)
    (Or.inr ((EReal.mul_nonneg (EReal.coe_nonneg.mpr hr.le)
      (hσ.fenchelConjugate_nonneg _)).trans_lt' EReal.bot_lt_zero).ne'), hconjp, neg_neg]

/-- **Exercise 11.56**, closing assertion, valid direction: in the convex case a
maximizer `ȳ` of the ordinary dual objective `ψ` gives maximizers `(ȳ,r)` of the
augmented dual objective for every `r > 0`. -/
theorem isAugmentedDualMaximizer_of_forall_dualObjective_le (hfc : Convex ℝ (epigraph f))
    (hσ : IsAugmentingFunction σ) (hσt : ∀ u, σ u ≠ ⊤) {yb : P}
    (hyb : ∀ y, dualObjective f y ≤ dualObjective f yb) {r : ℝ} (hr : 0 < r) :
    IsAugmentedDualMaximizer f σ yb r := by
  refine ⟨hr, fun y r' hr' ↦ ?_⟩
  rw [augmentedDualObjective_eq_iSup_dualObjective hfc hσ hσt hr',
    augmentedDualObjective_eq_iSup_dualObjective hfc hσ hσt hr]
  refine iSup_le fun z ↦ ?_
  refine le_iSup_of_le 0 ?_
  rw [sub_zero, smul_zero, hσ.fenchelConjugate_zero, mul_zero, sub_zero]
  have h0 : 0 ≤ (r' : EReal) * fenchelConjugate σ (r'⁻¹ • z) :=
    EReal.mul_nonneg (EReal.coe_nonneg.mpr hr'.le) (hσ.fenchelConjugate_nonneg _)
  calc dualObjective f (y - z) - (r' : EReal) * fenchelConjugate σ (r'⁻¹ • z)
      ≤ dualObjective f (y - z) := by
        rw [sub_eq_add_neg]
        calc dualObjective f (y - z) + -((r' : EReal) * fenchelConjugate σ (r'⁻¹ • z))
            ≤ dualObjective f (y - z) + 0 :=
              add_le_add_right (EReal.neg_le_zero.mpr h0) _
          _ = _ := add_zero _
    _ ≤ dualObjective f yb := hyb _

end Formula

section Counterexample

/-- The integrand `f(x,u) = u²/2` on `ℝ × ℝ`. -/
def halfSquareParameterIntegrand : WithLp 2 (ℝ × ℝ) → EReal :=
  fun q ↦ ((q.snd ^ 2 / 2 : ℝ) : EReal)

/-- **Exercise 11.56**, the converse of the closing assertion fails: for
`f(x,u) = u²/2` and the sharp augmenting function `|u|`, the pair `(1/2, 1)`
maximizes the augmented dual objective, but `1/2` does not maximize the
ordinary dual objective `ψ(y) = -y²/2`. -/
theorem augmentedDualMaximizer_not_dualMaximizer :
    Convex ℝ (epigraph halfSquareParameterIntegrand) ∧
    IsDualizingParameterization (primalObjective halfSquareParameterIntegrand)
      halfSquareParameterIntegrand ∧
    IsAugmentingFunction (sharpAugmentingFunction (normSeminorm ℝ ℝ)) ∧
    (∀ u, sharpAugmentingFunction (normSeminorm ℝ ℝ) u ≠ ⊤) ∧
    IsAugmentedDualMaximizer halfSquareParameterIntegrand
      (sharpAugmentingFunction (normSeminorm ℝ ℝ)) (1 / 2) 1 ∧
    ¬ ∀ y, dualObjective halfSquareParameterIntegrand y ≤
      dualObjective halfSquareParameterIntegrand (1 / 2) := by
  set f := halfSquareParameterIntegrand with hfdef
  set σ := sharpAugmentingFunction (normSeminorm ℝ ℝ) with hσdef
  have hconvR : ConvexOn ℝ univ (fun t : ℝ ↦ t ^ 2 / 2) := by
    have h := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert h using 1
    funext t
    simp only [smul_eq_mul]
    ring
  have hfc : Convex ℝ (epigraph f) := by
    apply convex_epigraph_coe_of_convexOn_univ
    exact hconvR.comp_linearMap (WithLp.sndₗ 2 ℝ ℝ ℝ)
  have hσ : IsAugmentingFunction σ := isAugmentingFunction_sharp fun u hu ↦ by simpa using hu
  have hσt : ∀ u, σ u ≠ ⊤ := fun _ ↦ EReal.coe_ne_top _
  have hdp : IsDualizingParameterization (primalObjective f) f := by
    refine ⟨rfl, ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩, fun x ↦ ?_, fun x ↦ ?_⟩
    · exact (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous
    · exact convex_epigraph_coe_of_convexOn_univ hconvR
  refine ⟨hfc, hdp, hσ, hσt, ⟨one_pos, fun y r hr ↦ ?_⟩, fun hmax ↦ ?_⟩
  · -- `ψ̄ ≤ inf φ = 0 ≤ ψ̄(1/2, 1)`
    have hle : augmentedDualObjective f σ y r ≤ 0 := by
      have h := augmentedDualObjective_le_primalObjective (f := f) hσ.zero (0 : ℝ) y r
      refine h.trans (le_of_eq ?_)
      change ((((WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))).snd) ^ 2 / 2 : ℝ) : EReal) = 0
      norm_num
    refine hle.trans (le_iInf fun x ↦ le_iInf fun u ↦ ?_)
    change (0 : EReal) ≤ ((u ^ 2 / 2 : ℝ) : EReal) + ((1 : ℝ) : EReal) * ((‖u‖ : ℝ) : EReal) -
      (⟪(1 / 2 : ℝ), u⟫_ℝ : EReal)
    rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_zero,
      EReal.coe_le_coe_iff, Real.norm_eq_abs]
    have hin : ⟪(1 / 2 : ℝ), u⟫_ℝ = u / 2 := by simp; ring
    rw [hin]
    nlinarith [abs_nonneg u, le_abs_self u, sq_nonneg u]
  · -- `ψ(1/2) ≤ -1/8 < 0 ≤ ψ(0)`
    have h0 : (0 : EReal) ≤ dualObjective f 0 := by
      rw [dualObjective, ← neg_zero, EReal.neg_le_neg_iff, fenchelConjugate_le_iff]
      intro q
      change (⟪WithLp.toLp 2 ((0 : ℝ), (0 : ℝ)), q⟫_ℝ : EReal) - ((q.snd ^ 2 / 2 : ℝ) : EReal) ≤ 0
      rw [← EReal.coe_sub, ← EReal.coe_zero, EReal.coe_le_coe_iff, WithLp.prod_inner_apply]
      simp only [inner_zero_left, add_zero, zero_sub]
      nlinarith [sq_nonneg q.snd]
    have hc : ((1 / 8 : ℝ) : EReal) ≤ fenchelConjugate f (WithLp.toLp 2 ((0 : ℝ), (1 / 2 : ℝ))) := by
      refine le_trans (le_of_eq ?_)
        (le_fenchelConjugate f (WithLp.toLp 2 ((0 : ℝ), (1 / 2 : ℝ))) _)
      change ((1 / 8 : ℝ) : EReal) = (⟪WithLp.toLp 2 ((0 : ℝ), (1 / 2 : ℝ)),
        WithLp.toLp 2 ((0 : ℝ), (1 / 2 : ℝ))⟫_ℝ : EReal) - (((1 / 2 : ℝ) ^ 2 / 2 : ℝ) : EReal)
      rw [← EReal.coe_sub, EReal.coe_eq_coe_iff, WithLp.prod_inner_apply]
      simp only [inner_zero_left, zero_add]
      simp
      norm_num
    have h1 : dualObjective f (1 / 2) ≤ ((-1 / 8 : ℝ) : EReal) := by
      rw [dualObjective]
      calc -fenchelConjugate f (WithLp.toLp 2 ((0 : ℝ), (1 / 2 : ℝ)))
          ≤ -((1 / 8 : ℝ) : EReal) := EReal.neg_le_neg_iff.mpr hc
        _ = ((-1 / 8 : ℝ) : EReal) := by rw [← EReal.coe_neg]; norm_num
    have := (hmax 0).trans h1
    have h2 := h0.trans this
    rw [← EReal.coe_zero, EReal.coe_le_coe_iff] at h2
    norm_num at h2

end Counterexample

end
end RW
