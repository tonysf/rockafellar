/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The missing calmness hypothesis in Corollary 10.9
-/

import RockafellarWets.Chapter10.CompositeMultipliers
import RockafellarWets.Chapter10.CoordinateSubderivatives
import RockafellarWets.Chapter10.SeparableRegularSubgradients
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable def negativeRoot (x : ℝ) : EReal := if 0 ≤ x then ((-√x:ℝ):EReal) else ⊤
noncomputable def positiveRoot (x : ℝ) : EReal := ((√|x|:ℝ):EReal)

@[simp] theorem negativeRoot_zero : negativeRoot 0 = 0 := by simp [negativeRoot]
@[simp] theorem positiveRoot_zero : positiveRoot 0 = 0 := by simp [positiveRoot]

theorem negativeRoot_isProper : IsProper negativeRoot := by
  refine ⟨⟨0,by simp⟩,fun x ↦ ?_⟩
  by_cases hx : 0 ≤ x
  · rw [negativeRoot,if_pos hx]; exact EReal.bot_lt_coe _
  · rw [negativeRoot,if_neg hx]; exact bot_lt_top

theorem positiveRoot_isProper : IsProper positiveRoot :=
  ⟨⟨0,by simp⟩,fun x ↦ EReal.bot_lt_coe _⟩

theorem positiveRoot_continuous : Continuous positiveRoot :=
  continuous_coe_real_ereal.comp (Real.continuous_sqrt.comp continuous_abs)

private theorem negativeRoot_epigraph : epigraph negativeRoot =
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ -√p.1 ≤ p.2} := by
  ext p
  by_cases hp : 0 ≤ p.1
  · change (if 0 ≤ p.1 then ((-√p.1:ℝ):EReal) else ⊤) ≤ (p.2:EReal) ↔ _
    rw [if_pos hp,EReal.coe_le_coe_iff]
    exact (and_iff_right hp).symm
  · simp [epigraph,negativeRoot,hp]

theorem negativeRoot_lowerSemicontinuous : LowerSemicontinuous negativeRoot := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  rw [negativeRoot_epigraph]
  exact (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le (Real.continuous_sqrt.comp continuous_fst).neg continuous_snd)

theorem convex_epigraph_negativeRoot : Convex ℝ (epigraph negativeRoot) := by
  rw [negativeRoot_epigraph]
  exact (convex_epigraph_iff_convexOn (fun x : ℝ ↦ -√x) (Ici 0) (convex_Ici 0)).mpr
    Real.strictConcaveOn_sqrt.concaveOn.neg

theorem negativeRoot_regular : IsSubdifferentiallyRegularAt negativeRoot 0 := by
  exact (isSubdifferentiallyRegularAt_of_convex convex_epigraph_negativeRoot
    (locallyLscAt_of_lowerSemicontinuous_finite negativeRoot_lowerSemicontinuous negativeRoot_zero)).1

theorem positiveRoot_regularSubdifferential_zero : regularSubdifferential positiveRoot 0 = univ := by
  apply eq_univ_of_forall
  intro v
  refine ⟨0,positiveRoot_zero,fun ε hε ↦ ?_⟩
  have ht : Tendsto (fun z : ℝ ↦ (|v|+1)*√|z|) (𝓝 0) (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.comp continuous_abs).tendsto (0:ℝ)).const_mul (|v|+1)
  filter_upwards [ht.eventually (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))] with z hz
  change ((0+(z-0)*v-ε*‖z-0‖:ℝ):EReal) ≤ ((√|z|:ℝ):EReal)
  rw [EReal.coe_le_coe_iff,sub_zero]
  have hs := Real.sq_sqrt (abs_nonneg z)
  have hvz : z*v ≤ |v| * |z| := by simpa only [abs_mul,mul_comm] using le_abs_self (z*v)
  have hb : |v| * |z| ≤ √|z| := by
    have hm := mul_le_mul_of_nonneg_right hz.le (Real.sqrt_nonneg |z|)
    calc
      |v| * |z| = |v| * (√|z|)^2 := congrArg (fun a : ℝ ↦ |v| * a) hs.symm
      _ ≤ √|z| := by nlinarith [Real.sqrt_nonneg |z|]
  exact (sub_le_self _ (mul_nonneg hε.le (norm_nonneg _))).trans (by simpa only [zero_add] using hvz.trans hb)

theorem positiveRoot_regular : IsSubdifferentiallyRegularAt positiveRoot 0 := by
  have hsub : subdifferential positiveRoot 0 = univ := by
    apply eq_univ_of_forall
    intro v
    exact regularSubdifferential_subset_subdifferential _ _ (positiveRoot_regularSubdifferential_zero ▸ mem_univ v)
  have hcone : horizonCone (univ : Set ℝ) = univ :=
    horizonCone_eq_self_of_isClosed_isCone isClosed_univ ⟨mem_univ _,fun _ _ _ _ ↦ mem_univ _⟩
  have hhor : horizonSubdifferential positiveRoot 0 = univ := by
    apply eq_univ_of_forall
    intro v
    apply horizonCone_regularSubdifferential_subset positiveRoot_zero
    rw [positiveRoot_regularSubdifferential_zero,hcone]
    exact mem_univ _
  apply (isSubdifferentiallyRegularAt_iff_subgradients positiveRoot_zero (hsub ▸ univ_nonempty)).mpr
  exact ⟨locallyLscAt_of_lowerSemicontinuous_finite positiveRoot_continuous.lowerSemicontinuous positiveRoot_zero,
    hsub.trans positiveRoot_regularSubdifferential_zero.symm,by rw [hhor,positiveRoot_regularSubdifferential_zero,hcone]⟩

theorem negativeRoot_regularSubgradient_sq {t : ℝ} (ht : 0 < t) :
    -(2*t)⁻¹ ∈ regularSubdifferential negativeRoot (t^2) := by
  have hd := (Real.hasDerivAt_sqrt (sq_pos_of_pos ht).ne').neg
  have he : negativeRoot =ᶠ[𝓝 (t^2)] (fun z : ℝ ↦ ((-√z:ℝ):EReal)) := by
    filter_upwards [Ioi_mem_nhds (sq_pos_of_pos ht)] with z hz
    exact if_pos hz.le
  have hv : negativeRoot (t^2) = ((-t:ℝ):EReal) := by simp [negativeRoot,sq_nonneg,Real.sqrt_sq ht.le]
  rw [regularSubdifferential_congr_nhds_of_finite hv he]
  have hs := (regularSubdifferential_of_hasGradientAt hd.hasGradientAt').1
  change regularSubdifferential (fun z : ℝ ↦ ((-√z:ℝ):EReal)) (t^2) = {-(1/(2*√(t^2)))} at hs
  rw [hs]
  simp [Real.sqrt_sq ht.le,one_div]

/-- A normalized sequence of regular subgradients gives a horizontal
normal that cannot be regular at the origin. -/
theorem root_separable_horizon : WithLp.toLp 2 ((-1:ℝ),(2:ℝ)) ∈
    horizonSubdifferential (separableSum negativeRoot positiveRoot) 0 := by
  let t (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let z (n : ℕ) := WithLp.toLp 2 ((t n)^2,(0:ℝ))
  let v (n : ℕ) := WithLp.toLp 2 (-(2*t n)⁻¹,(t n)⁻¹)
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa [z] using (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.continuous.tendsto (0,0) |>.comp
      (by simpa only [zero_pow (by norm_num : 2 ≠ 0)] using ((ht0.pow 2).prodMk_nhds (tendsto_const_nhds (x := (0:ℝ)))))
  have hbase : separableSum negativeRoot positiveRoot (0 : WithLp 2 (ℝ × ℝ)) = ((0:ℝ):EReal) := by
    simp [separableSum]
  have hval (n : ℕ) : separableSum negativeRoot positiveRoot (z n) = ((-t n:ℝ):EReal) := by
    simp [separableSum,z,negativeRoot,sq_nonneg,Real.sqrt_sq (ht n).le]
  apply (mem_horizonSubdifferential_iff_zero_or_scaledSeq hbase).mpr
  refine Or.inr ⟨z,v,fun n ↦ 2*t n,tendsto_attentiveNhds_iff.mpr ⟨hz,?_⟩,?_,
    fun n ↦ mul_pos (by norm_num) (ht n),by convert ht0.const_mul 2 using 1 <;> simp only [mul_zero],?_⟩
  · simpa only [Function.comp_def,hval,hbase,neg_zero] using continuous_coe_real_ereal.continuousAt.tendsto.comp ht0.neg
  · intro n
    apply (mem_regularSubdifferential_separableSum_iff
      (show negativeRoot ((t n)^2) = ((-t n:ℝ):EReal) by simp [negativeRoot,sq_nonneg,Real.sqrt_sq (ht n).le])
      positiveRoot_zero (v n)).mpr
    exact ⟨negativeRoot_regularSubgradient_sq (ht n),positiveRoot_regularSubdifferential_zero ▸ mem_univ _⟩
  · have he (n : ℕ) : (2*t n) • v n = WithLp.toLp 2 ((-1:ℝ),(2:ℝ)) := by
      apply WithLp.ofLp_injective
      apply Prod.ext
      · change (2*t n)*(-(2*t n)⁻¹) = -1
        rw [mul_neg,mul_inv_cancel₀ (mul_ne_zero (by norm_num) (ht n).ne')]
      · change (2*t n)*(t n)⁻¹ = 2
        field_simp [(ht n).ne']
    simpa only [he] using (tendsto_const_nhds (x := WithLp.toLp 2 ((-1:ℝ),(2:ℝ))) (f := atTop))

/-- The sum of these two regular independent-coordinate functions is not
regular. Their equal-height diagonal makes the obstruction explicit. -/
theorem root_separable_not_regular :
    ¬ IsSubdifferentiallyRegularAt (separableSum negativeRoot positiveRoot) (0 : WithLp 2 (ℝ × ℝ)) := by
  intro hr
  have hbase : separableSum negativeRoot positiveRoot (0 : WithLp 2 (ℝ × ℝ)) = ((0:ℝ):EReal) := by simp [separableSum]
  have hn := (hr.mem_horizonSubdifferential_iff_regularNormal hbase).mp root_separable_horizon
  have ht : WithLp.toLp 2 (WithLp.toLp 2 ((1:ℝ),(1:ℝ)),(0:ℝ)) ∈
      tangentCone (euclideanEpigraph (separableSum negativeRoot positiveRoot)) (WithLp.toLp 2 (0,(0:ℝ))) := by
    let t (n : ℕ) : ℝ := 1/((n:ℝ)+1)
    have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
    let w := WithLp.toLp 2 (WithLp.toLp 2 ((1:ℝ),(1:ℝ)),(0:ℝ))
    have hp (n : ℕ) : t n • w ∈ euclideanEpigraph (separableSum negativeRoot positiveRoot) := by
      change negativeRoot (t n*1)+positiveRoot (t n*1) ≤ ((t n*0:ℝ):EReal)
      simp only [mul_one,mul_zero,negativeRoot,if_pos (ht n).le,positiveRoot,abs_of_nonneg (ht n).le]
      rw [← EReal.coe_add,neg_add_cancel]
    apply mem_tangentCone_of_forall hp ht tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [show WithLp.toLp 2 ((0:WithLp 2 (ℝ × ℝ)),(0:ℝ)) = 0 from rfl,
      sub_zero,smul_smul,inv_mul_cancel₀ (ht _).ne',one_smul] using (tendsto_const_nhds (x := w) (f := atTop))
  have hh := inner_nonpos_of_mem_regularNormalCone hn ht
  norm_num [WithLp.prod_inner_apply] at hh

private theorem root_fst_adjoint (a : ℝ) :
    (WithLp.fstL 2 ℝ ℝ ℝ).adjoint a = WithLp.toLp 2 (a,(0:ℝ)) := by
  apply ext_inner_right ℝ
  intro w
  simp [ContinuousLinearMap.adjoint_inner_left,WithLp.prod_inner_apply]

private theorem root_snd_adjoint (a : ℝ) :
    (WithLp.sndL 2 ℝ ℝ ℝ).adjoint a = WithLp.toLp 2 ((0:ℝ),a) := by
  apply ext_inner_right ℝ
  intro w
  simp [ContinuousLinearMap.adjoint_inner_left,WithLp.prod_inner_apply]

/-- **Counterexample to the regularity clause of Corollary 10.9.** Both
summands are proper, lsc and regular. Their horizon vectors cannot cancel,
but their sum is not regular. The zero-direction hypotheses from 10.5
cannot be dropped in that argument. -/
theorem qualified_sum_regularity_counterexample :
    ∃ f g : WithLp 2 (ℝ × ℝ) → EReal,
      IsProper f ∧ IsProper g ∧ LowerSemicontinuous f ∧ LowerSemicontinuous g ∧
      f 0 = 0 ∧ g 0 = 0 ∧ IsSubdifferentiallyRegularAt f 0 ∧ IsSubdifferentiallyRegularAt g 0 ∧
      (∀ u ∈ horizonSubdifferential f 0, ∀ v ∈ horizonSubdifferential g 0,
        u+v = 0 → u = 0 ∧ v = 0) ∧ ¬ IsSubdifferentiallyRegularAt (f+g) 0 := by
  let A := WithLp.fstL 2 ℝ ℝ ℝ
  let B := WithLp.sndL 2 ℝ ℝ ℝ
  have hA : Function.Surjective (fderiv ℝ A (0 : WithLp 2 (ℝ × ℝ))) := by
    rw [A.fderiv]
    exact fun y ↦ ⟨WithLp.toLp 2 (y,(0:ℝ)),rfl⟩
  have hB : Function.Surjective (fderiv ℝ B (0 : WithLp 2 (ℝ × ℝ))) := by
    rw [B.fderiv]
    exact fun y ↦ ⟨WithLp.toLp 2 ((0:ℝ),y),rfl⟩
  let f := negativeRoot ∘ A
  let g := positiveRoot ∘ B
  have hf0 : f 0 = ((0:ℝ):EReal) := negativeRoot_zero
  have hg0 : g 0 = ((0:ℝ):EReal) := positiveRoot_zero
  refine ⟨f,g,⟨⟨0,by rw [hf0]; exact EReal.coe_lt_top _⟩,fun z ↦ negativeRoot_isProper.2 _⟩,
    ⟨⟨0,by rw [hg0]; exact EReal.coe_lt_top _⟩,fun z ↦ positiveRoot_isProper.2 _⟩,
    negativeRoot_lowerSemicontinuous.comp A.continuous,positiveRoot_continuous.lowerSemicontinuous.comp B.continuous,
    hf0,hg0,?_,?_,?_,root_separable_not_regular⟩
  · exact (isSubdifferentiallyRegularAt_comp_iff_of_surjective A.contDiff
      negativeRoot_lowerSemicontinuous hf0 hA).mpr negativeRoot_regular
  · exact (isSubdifferentiallyRegularAt_comp_iff_of_surjective B.contDiff
      positiveRoot_continuous.lowerSemicontinuous hg0 hB).mpr positiveRoot_regular
  · intro u hu v hv he
    have ha := horizonSubdifferential_comp_eq_of_surjective A.contDiff negativeRoot_lowerSemicontinuous hf0 hA
    have hb := horizonSubdifferential_comp_eq_of_surjective B.contDiff positiveRoot_continuous.lowerSemicontinuous hg0 hB
    obtain ⟨a,_,rfl⟩ := ha ▸ hu
    obtain ⟨b,_,rfl⟩ := hb ▸ hv
    rw [A.fderiv,B.fderiv] at he ⊢
    change (WithLp.fstL 2 ℝ ℝ ℝ).adjoint a+(WithLp.sndL 2 ℝ ℝ ℝ).adjoint b = 0 at he
    rw [root_fst_adjoint,root_snd_adjoint] at he
    have ha0 : a = 0 := by simpa using congrArg WithLp.fst he
    have hb0 : b = 0 := by simpa using congrArg WithLp.snd he
    simp only [ha0,hb0,map_zero,and_self]

end RW
