/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The circular boundary in the nonexample following Definition 10.20
-/
import RockafellarWets.Chapter10.PolyhedralPieceDerivatives
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Abs

open Filter Set Topology Polynomial

namespace RW
noncomputable section

private abbrev Plane := WithLp 2 (ℝ × ℝ)
private def circleParam (t : ℝ) : Plane :=
  WithLp.toLp 2 ((1-t^2)/(1+t^2), (2*t)/(1+t^2))

private theorem circleParam_sq (t : ℝ) : (circleParam t).fst^2 + (circleParam t).snd^2 = 1 := by
  change ((1-t^2)/(1+t^2))^2 + ((2*t)/(1+t^2))^2 = 1
  field_simp [show (1+t^2) ≠ 0 by positivity]
  ring

/-- A nonconstant affine equation holds for only finitely many parameters on
this rational parametrization of the unit circle. -/
private theorem finite_circleParam_eq (L : Plane →L[ℝ] ℝ) (b : ℝ) (hL : L ≠ 0) :
    {t | L (circleParam t) = b}.Finite := by
  let e : Plane := WithLp.toLp 2 ((1:ℝ),(0:ℝ))
  let f : Plane := WithLp.toLp 2 ((0:ℝ),(1:ℝ))
  have hcoords (u : Plane) : L u = u.fst * L e + u.snd * L f := by
    have he : u = u.fst • e + u.snd • f := by
      apply WithLp.ofLp_injective
      exact Prod.ext (by simp [e,f,smul_eq_mul]) (by simp [e,f,smul_eq_mul])
    calc
      L u = L (u.fst • e + u.snd • f) := congrArg L he
      _ = _ := by rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
  let p : ℝ[X] := C (L e) * (1-X^2) + C (L f) * (2*X) - C b * (1+X^2)
  have hp : p ≠ 0 := by
    intro hz
    have H (z : ℝ) : L e * (1-z^2) + L f * (2*z) - b * (1+z^2) = 0 := by
      simpa [p] using congrArg (Polynomial.eval z) hz
    have h0 := H 0
    have h1 := H 1
    have hn := H (-1)
    norm_num at h0 h1 hn
    have he : L e = 0 := by linarith
    have hf : L f = 0 := by linarith
    apply hL
    ext u
    simp [hcoords u,he,hf]
  apply (Polynomial.finite_setOf_isRoot hp).subset
  intro t ht
  change L (circleParam t) = b at ht
  rw [hcoords] at ht
  change ((1-t^2)/(1+t^2))*L e + ((2*t)/(1+t^2))*L f = b at ht
  field_simp [show (1+t^2) ≠ 0 by positivity] at ht
  simp only [mem_setOf_eq,Polynomial.IsRoot,p,eval_sub,eval_add,eval_mul,eval_C,eval_one,eval_pow,eval_X,eval_ofNat]
  linarith

/-- **10.20**, the absolute value of the circle's quadratic equation cannot
agree with finitely many quadratic pieces on a polyhedral cover. -/
theorem not_piecewiseLinearQuadratic_abs_circle :
    ¬ IsPiecewiseLinearQuadratic (fun u : WithLp 2 (ℝ × ℝ) ↦ (|u.fst^2+u.snd^2-1| : ℝ)) := by
  classical
  rintro ⟨m,D,q,hpoly,hdom,hq⟩
  choose n A b hD using fun i ↦ (hpoly i).isHPolyhedral.exists_mem_iff
  let bad (i : Fin m) (j : Fin (n i)) : Set ℝ :=
    {t | A i j ≠ 0 ∧ A i j (circleParam t) = b i j}
  have hbad (i : Fin m) (j : Fin (n i)) : (bad i j).Finite := by
    by_cases h : A i j = 0
    · simp [bad,h]
    · exact (finite_circleParam_eq _ _ h).subset (fun t ht ↦ ht.2)
  obtain ⟨t,ht⟩ := (Set.finite_iUnion (fun i ↦ Set.finite_iUnion (hbad i))).exists_notMem
  let u := circleParam t
  have hu : u ∈ ⋃ i, D i := by rw [← hdom]; exact EReal.coe_lt_top _
  obtain ⟨i,hi⟩ := mem_iUnion.mp hu
  have hnear (j : Fin (n i)) : ∀ᶠ v in 𝓝 u, A i j v ≤ b i j := by
    have hle := (hD i u).mp hi j
    by_cases h : A i j = 0
    · simpa only [h,ContinuousLinearMap.zero_apply] using (Filter.Eventually.of_forall
        (fun _ : Plane ↦ show (0:ℝ) ≤ b i j by simpa only [h,ContinuousLinearMap.zero_apply] using hle) : ∀ᶠ _ in 𝓝 u, 0 ≤ b i j)
    · have hne : A i j u ≠ b i j := fun hEq ↦ ht (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,h,hEq⟩⟩)
      exact ((A i j).continuous.tendsto u).eventually (gt_mem_nhds (hle.lt_of_ne hne)) |>.mono fun _ h ↦ h.le
  have heq : (fun v : Plane ↦ |v.fst^2+v.snd^2-1|) =ᶠ[𝓝 u] (q i).eval := by
    filter_upwards [Filter.eventually_all.mpr hnear] with v hv
    exact EReal.coe_injective (hq i v ((hD i v).mpr hv))
  have hd := ((q i).contDiff 1).differentiable (by norm_num) u |>.congr_of_eventuallyEq heq
  let ray (s : ℝ) := √(1+s) • u
  have hr : DifferentiableAt ℝ ray 0 := by
    apply DifferentiableAt.smul_const
    apply DifferentiableAt.sqrt (f := fun s : ℝ ↦ 1+s) (by fun_prop)
    norm_num
  have hbase : ray 0 = u := by simp [ray]
  have hd' : DifferentiableAt ℝ (fun v : Plane ↦ |v.fst^2+v.snd^2-1|) (ray 0) := by rwa [hbase]
  have hcomp := hd'.comp 0 hr
  apply not_differentiableAt_abs_zero
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show (-1:ℝ) < 0 by norm_num)] with s hs
  change -1 < s at hs
  change |s| = |(√(1+s)*u.fst)^2+(√(1+s)*u.snd)^2-1|
  congr 1
  rw [mul_pow,mul_pow,← mul_add,circleParam_sq,Real.sq_sqrt (by linarith : 0 ≤ 1+s)]
  ring

end
end RW
