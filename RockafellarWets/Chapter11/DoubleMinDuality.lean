/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Double-min duality

Theorem 11.67 pairs `minimize ⟨c,x⟩ + k(x) - h(Ax - b)` with
`minimize ⟨b,y⟩ + h*(y) - k*(A*y - c)`.
-/
import RockafellarWets.Chapter11.ClassicalLegendreGradient
import RockafellarWets.Chapter11.EssentialStrictConvexity
import RockafellarWets.Chapter11.RelativeInteriorSubgradients
import RockafellarWets.Chapter11.DualMinimizationGrowth
import RockafellarWets.Chapter11.SubgradientConjugacy
import RockafellarWets.Chapter11.MoreauConjugacy
import RockafellarWets.Chapter10.AmenableSmoothAddition
import RockafellarWets.Chapter8.SubgradientsAndGradients

open Set
open scoped InnerProductSpace

namespace RW
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

section Objectives

variable (A : E →L[ℝ] F) (b : F) (c : E) (k : E → EReal) (h : F → ℝ)

/-- The primal objective `ϕ(x) = ⟨c,x⟩ + k(x) - h(Ax - b)` of Theorem 11.67. -/
def doubleMinPrimal (x : E) : EReal := (⟪c, x⟫_ℝ : EReal) + k x - (h (A x - b) : EReal)

/-- The dual objective `ψ(y) = ⟨b,y⟩ + h*(y) - k*(A*y - c)` of Theorem 11.67. -/
def doubleMinDual (y : F) : EReal :=
  (⟪b, y⟫_ℝ : EReal) + fenchelConjugate (fun u ↦ (h u : EReal)) y -
    fenchelConjugate k (ContinuousLinearMap.adjoint A y - c)

/-- The pairs `S` of Theorem 11.67, in the first description. -/
def doubleMinPairs : Set (E × F) :=
  {p | p.2 = gradient h (A p.1 - b) ∧ ContinuousLinearMap.adjoint A p.2 - c ∈ subdifferential k p.1}

/-- The pairs `S` of Theorem 11.67, in the second description. -/
def doubleMinPairsDual : Set (E × F) :=
  {p | p.1 = gradient (fun v ↦ (fenchelConjugate k v).toReal)
      (ContinuousLinearMap.adjoint A p.2 - c) ∧
    A p.1 - b ∈ subdifferential (fenchelConjugate (fun u ↦ (h u : EReal))) p.2}

end Objectives

section Regularity

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
theorem effectiveDomain_coe_real (h : F → ℝ) : effectiveDomain (fun u ↦ (h u : EReal)) = univ :=
  eq_univ_of_forall fun _ ↦ EReal.coe_lt_top _

omit [FiniteDimensional ℝ F] in
theorem convex_epigraph_coe_of_convexOn {h : F → ℝ} (hhc : ConvexOn ℝ univ h) :
    Convex ℝ (epigraph (fun u ↦ (h u : EReal))) := by
  have he : epigraph (fun u ↦ (h u : EReal)) = {p : F × ℝ | p.1 ∈ univ ∧ h p.1 ≤ p.2} := by
    ext p
    simp only [epigraph, mem_setOf_eq, mem_univ, true_and, ge_iff_le, EReal.coe_le_coe_iff]
  rw [he]
  exact hhc.convex_epigraph

omit [FiniteDimensional ℝ F] in
theorem isAlmostDifferentiable_coe_of_differentiable {h : F → ℝ} (hhd : Differentiable ℝ h) :
    IsAlmostDifferentiable (fun u ↦ (h u : EReal)) := by
  rw [IsAlmostDifferentiable, effectiveDomain_coe_real, interior_univ]
  refine ⟨univ_nonempty, fun x _ ↦ by simpa only [EReal.toReal_coe] using hhd x, fun x hx ↦ ?_⟩
  exact absurd (mem_univ x) hx.2

/-- A finite differentiable convex function is continuously differentiable. -/
theorem contDiff_of_convexOn_differentiable {h : F → ℝ} (hhc : ConvexOn ℝ univ h)
    (hhd : Differentiable ℝ h) : ContDiff ℝ 1 h := by
  have h1 := (isAlmostDifferentiable_coe_of_differentiable hhd).contDiffOn_interior
    (isProper_coe_real h) (continuous_coe_real_ereal.comp hhd.continuous).lowerSemicontinuous
    (convex_epigraph_coe_of_convexOn hhc)
  rw [effectiveDomain_coe_real, interior_univ] at h1
  simpa only [EReal.toReal_coe] using contDiffOn_univ.mp h1

/-- **Theorem 11.67**, the regularity of `h*`: it is proper, lower
semicontinuous, convex, coercive and almost strictly convex. -/
theorem fenchelConjugate_coe_regular {h : F → ℝ} (hhc : ConvexOn ℝ univ h)
    (hhd : Differentiable ℝ h) :
    IsProper (fenchelConjugate (fun u ↦ (h u : EReal))) ∧
      LowerSemicontinuous (fenchelConjugate (fun u ↦ (h u : EReal))) ∧
      Convex ℝ (epigraph (fenchelConjugate (fun u ↦ (h u : EReal)))) ∧
      IsCoercive (fenchelConjugate (fun u ↦ (h u : EReal))) ∧
      IsAlmostStrictlyConvex (fenchelConjugate (fun u ↦ (h u : EReal))) := by
  have hp := isProper_coe_real h
  have hl : LowerSemicontinuous (fun u ↦ (h u : EReal)) :=
    (continuous_coe_real_ereal.comp hhd.continuous).lowerSemicontinuous
  have hc := convex_epigraph_coe_of_convexOn hhc
  have hsp := isProper_fenchelConjugate hp hl hc
  refine ⟨hsp, lowerSemicontinuous_fenchelConjugate _, convex_epigraph_fenchelConjugate _, ?_, ?_⟩
  · apply (isCoercive_iff_conjugate_domain_eq_univ hsp (lowerSemicontinuous_fenchelConjugate _)
      (convex_epigraph_fenchelConjugate _)).mpr
    rw [fenchelConjugate_fenchelConjugate_eq hp hl hc, effectiveDomain_coe_real]
  · exact (isAlmostDifferentiable_iff_conjugate_isAlmostStrictlyConvex hp hl hc).mp
      (isAlmostDifferentiable_coe_of_differentiable hhd)

/-- **Theorem 11.67**, the conjugate of `k` is finite. -/
theorem fenchelConjugate_eq_coe_toReal_of_isCoercive {k : E → EReal} (hkp : IsProper k)
    (hkl : LowerSemicontinuous k) (hkc : Convex ℝ (epigraph k)) (hkco : IsCoercive k) (v : E) :
    fenchelConjugate k v = ((fenchelConjugate k v).toReal : EReal) := by
  have hdom := (isCoercive_iff_conjugate_domain_eq_univ hkp hkl hkc).mp hkco
  have hlt : fenchelConjugate k v < ⊤ := by
    have hv : v ∈ effectiveDomain (fenchelConjugate k) := hdom ▸ mem_univ v
    exact hv
  exact (EReal.coe_toReal hlt.ne ((isProper_fenchelConjugate hkp hkl hkc).2 v).ne').symm

/-- **Theorem 11.67**, the conjugate of `k` is continuously differentiable. -/
theorem contDiff_fenchelConjugate_toReal {k : E → EReal} (hkp : IsProper k)
    (hkl : LowerSemicontinuous k) (hkc : Convex ℝ (epigraph k)) (hkco : IsCoercive k)
    (hks : IsAlmostStrictlyConvex k) :
    ContDiff ℝ 1 (fun v ↦ (fenchelConjugate k v).toReal) := by
  have had := (isAlmostDifferentiable_conjugate_iff_isAlmostStrictlyConvex hkp hkl hkc).mpr hks
  have h1 := had.contDiffOn_interior (isProper_fenchelConjugate hkp hkl hkc)
    (lowerSemicontinuous_fenchelConjugate k) (convex_epigraph_fenchelConjugate k)
  rw [(isCoercive_iff_conjugate_domain_eq_univ hkp hkl hkc).mp hkco, interior_univ] at h1
  exact contDiffOn_univ.mp h1

end Regularity

section Calculus

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem doubleMinPrimal_eq (A : E →L[ℝ] F) (b : F) (c : E) (k : E → EReal) (h : F → ℝ) (x : E) :
    doubleMinPrimal A b c k h x = k x + ((⟪c, x⟫_ℝ - h (A x - b) : ℝ) : EReal) := by
  unfold doubleMinPrimal
  cases k x with
  | bot => simp
  | top => rw [EReal.coe_add_top, EReal.top_sub_coe, EReal.top_add_coe]
  | coe κ =>
    rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add]
    congr 1
    ring

theorem doubleMinDual_eq (A : E →L[ℝ] F) (b : F) (c : E) {k : E → EReal} (h : F → ℝ)
    (hkp : IsProper k) (hkl : LowerSemicontinuous k) (hkc : Convex ℝ (epigraph k))
    (hkco : IsCoercive k) (y : F) :
    doubleMinDual A b c k h y = fenchelConjugate (fun u ↦ (h u : EReal)) y +
      ((⟪b, y⟫_ℝ - (fenchelConjugate k (ContinuousLinearMap.adjoint A y - c)).toReal : ℝ) :
        EReal) := by
  unfold doubleMinDual
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, fenchelConjugate k (ContinuousLinearMap.adjoint A y - c) = σ :=
    ⟨_, fenchelConjugate_eq_coe_toReal_of_isCoercive hkp hkl hkc hkco _⟩
  rw [hσ, EReal.toReal_coe]
  cases fenchelConjugate (fun u ↦ (h u : EReal)) y with
  | bot => simp
  | top => rw [EReal.coe_add_top, EReal.top_sub_coe, EReal.top_add_coe]
  | coe η =>
    rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add]
    congr 1
    ring

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The gradient of the smooth part `x ↦ ⟨c,x⟩ - h(Ax - b)`. -/
theorem hasGradientAt_inner_sub_comp {h : F → ℝ} (hhd : Differentiable ℝ h) (A : E →L[ℝ] F)
    (b : F) (c : E) [CompleteSpace E] [CompleteSpace F] (x : E) :
    HasGradientAt (fun x ↦ ⟪c, x⟫_ℝ - h (A x - b))
      (c - ContinuousLinearMap.adjoint A (gradient h (A x - b))) x := by
  have hc : HasFDerivAt (fun x : E ↦ ⟪c, x⟫_ℝ) (innerSL ℝ c) x := (innerSL ℝ c).hasFDerivAt
  have hh : HasFDerivAt (fun x ↦ h (A x - b)) ((fderiv ℝ h (A x - b)).comp A) x :=
    (hhd (A x - b)).hasFDerivAt.comp x (A.hasFDerivAt.sub_const b)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hc.sub hh using 1
  ext z
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.sub_apply,
    innerSL_apply_apply, ContinuousLinearMap.comp_apply, inner_sub_left,
    ContinuousLinearMap.adjoint_inner_left, gradient, InnerProductSpace.toDual_symm_apply]

end Calculus

section MainTheorem

variable {A : E →L[ℝ] F} {b : F} {c : E} {k : E → EReal} {h : F → ℝ}
  (hkp : IsProper k) (hkl : LowerSemicontinuous k) (hkc : Convex ℝ (epigraph k))
  (hkco : IsCoercive k) (hks : IsAlmostStrictlyConvex k)
  (hhc : ConvexOn ℝ univ h) (hhd : Differentiable ℝ h)

include hkp hkl hkc hkco hks hhc hhd in
/-- **Theorem 11.67**, both descriptions of the set `S` agree. -/
theorem doubleMinPairs_eq_dual : doubleMinPairs A b c k h = doubleMinPairsDual A b c k h := by
  have hC := contDiff_of_convexOn_differentiable hhc hhd
  have hEl : LowerSemicontinuous (fun u ↦ (h u : EReal)) :=
    (continuous_coe_real_ereal.comp hhd.continuous).lowerSemicontinuous
  have hkC := contDiff_fenchelConjugate_toReal hkp hkl hkc hkco hks
  have hkfin : fenchelConjugate k = fun v ↦ ((fenchelConjugate k v).toReal : EReal) :=
    funext (fenchelConjugate_eq_coe_toReal_of_isCoercive hkp hkl hkc hkco)
  ext ⟨x, y⟩
  constructor
  · rintro ⟨hy, hx⟩
    refine ⟨?_, ?_⟩
    · have hm := (mem_subdifferential_fenchelConjugate_iff hkp hkl hkc x
        (ContinuousLinearMap.adjoint A y - c)).mpr hx
      have hs := (subdifferentials_of_smooth
        (hkC.contDiffAt (x := ContinuousLinearMap.adjoint A y - c))).1
      rw [hkfin] at hm
      rw [hs] at hm
      exact hm
    · apply (mem_subdifferential_fenchelConjugate_iff (isProper_coe_real h) hEl
        (convex_epigraph_coe_of_convexOn hhc) (A x - b) y).mpr
      rw [(subdifferentials_of_smooth (hC.contDiffAt (x := A x - b))).1]
      exact hy
  · rintro ⟨hx, hy⟩
    refine ⟨?_, ?_⟩
    · have hm := (mem_subdifferential_fenchelConjugate_iff (isProper_coe_real h) hEl
        (convex_epigraph_coe_of_convexOn hhc) (A x - b) y).mp hy
      rw [(subdifferentials_of_smooth (hC.contDiffAt (x := A x - b))).1] at hm
      exact hm
    · apply (mem_subdifferential_fenchelConjugate_iff hkp hkl hkc x
        (ContinuousLinearMap.adjoint A y - c)).mp
      rw [hkfin, (subdifferentials_of_smooth
        (hkC.contDiffAt (x := ContinuousLinearMap.adjoint A y - c))).1]
      exact hx

include hkp hhc hhd in
/-- **Theorem 11.67**, primal stationarity: `0 ∈ ∂ϕ(x̄)` exactly when some
`ȳ` has `(x̄,ȳ) ∈ S`. -/
theorem zero_mem_subdifferential_doubleMinPrimal_iff (x : E) :
    (0 : E) ∈ subdifferential (doubleMinPrimal A b c k h) x ↔
      ∃ y, (x, y) ∈ doubleMinPairs A b c k h := by
  have hC := contDiff_of_convexOn_differentiable hhc hhd
  have hφ : doubleMinPrimal A b c k h = fun z ↦ k z + ((⟪c, z⟫_ℝ - h (A z - b) : ℝ) : EReal) :=
    funext (doubleMinPrimal_eq A b c k h)
  have hq : ContDiff ℝ 1 (fun z ↦ ⟪c, z⟫_ℝ - h (A z - b)) :=
    (contDiff_const.inner ℝ contDiff_id).sub (hC.comp (A.contDiff.sub contDiff_const))
  have hg := (hasGradientAt_inner_sub_comp hhd A b c x).gradient
  by_cases hkx : k x < ⊤
  · obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, k x = κ :=
      ⟨(k x).toReal, (EReal.coe_toReal hkx.ne (hkp.2 x).ne').symm⟩
    obtain ⟨-, hsub, -⟩ := subdifferentials_add_smooth hκ (hq.contDiffAt (x := x))
    rw [hφ, hsub, hg]
    constructor
    · rintro ⟨u, hu, hu0⟩
      have hu0' : u + (c - ContinuousLinearMap.adjoint A (gradient h (A x - b))) = 0 := hu0
      refine ⟨gradient h (A x - b), rfl, ?_⟩
      have he : u = ContinuousLinearMap.adjoint A (gradient h (A x - b)) - c := by
        calc u = u + (c - ContinuousLinearMap.adjoint A (gradient h (A x - b))) -
              (c - ContinuousLinearMap.adjoint A (gradient h (A x - b))) := by abel
          _ = ContinuousLinearMap.adjoint A (gradient h (A x - b)) - c := by rw [hu0']; abel
      rw [← he]
      exact hu
    · rintro ⟨y, hy, hm⟩
      refine ⟨_, hm, ?_⟩
      change ContinuousLinearMap.adjoint A y - c +
        (c - ContinuousLinearMap.adjoint A (gradient h (A x - b))) = 0
      change y = gradient h (A x - b) at hy
      rw [hy]
      abel
  · have hkx' : k x = ⊤ := not_lt_top_iff.mp hkx
    constructor
    · rintro ⟨⟨r, hr⟩, -⟩
      rw [doubleMinPrimal_eq, hkx', EReal.top_add_coe] at hr
      exact (EReal.coe_ne_top r hr.symm).elim
    · rintro ⟨y, -, ⟨r, hr⟩, -⟩
      rw [hkx'] at hr
      exact (EReal.coe_ne_top r hr.symm).elim

include hkp hkl hkc hkco hks hhc hhd in
/-- **Theorem 11.67**, dual stationarity: `0 ∈ ∂ψ(ȳ)` exactly when some
`x̄` has `(x̄,ȳ) ∈ S`. -/
theorem zero_mem_subdifferential_doubleMinDual_iff (y : F) :
    (0 : F) ∈ subdifferential (doubleMinDual A b c k h) y ↔
      ∃ x, (x, y) ∈ doubleMinPairs A b c k h := by
  have hkC := contDiff_fenchelConjugate_toReal hkp hkl hkc hkco hks
  have hψ : doubleMinDual A b c k h = fun z ↦ fenchelConjugate (fun u ↦ (h u : EReal)) z +
      ((⟪b, z⟫_ℝ - (fenchelConjugate k (ContinuousLinearMap.adjoint A z - c)).toReal : ℝ) :
        EReal) :=
    funext (doubleMinDual_eq A b c h hkp hkl hkc hkco)
  have hq : ContDiff ℝ 1 (fun z ↦ ⟪b, z⟫_ℝ -
      (fenchelConjugate k (ContinuousLinearMap.adjoint A z - c)).toReal) :=
    (contDiff_const.inner ℝ contDiff_id).sub
      (hkC.comp ((ContinuousLinearMap.adjoint A).contDiff.sub contDiff_const))
  have hg := (hasGradientAt_inner_sub_comp (hkC.differentiable one_ne_zero)
    (ContinuousLinearMap.adjoint A) c b y).gradient
  rw [ContinuousLinearMap.adjoint_adjoint] at hg
  have hsp := (fenchelConjugate_coe_regular hhc hhd).1
  rw [doubleMinPairs_eq_dual hkp hkl hkc hkco hks hhc hhd]
  by_cases hhy : fenchelConjugate (fun u ↦ (h u : EReal)) y < ⊤
  · obtain ⟨η, hη⟩ : ∃ η : ℝ, fenchelConjugate (fun u ↦ (h u : EReal)) y = η :=
      ⟨_, (EReal.coe_toReal hhy.ne (hsp.2 y).ne').symm⟩
    obtain ⟨-, hsub, -⟩ := subdifferentials_add_smooth hη (hq.contDiffAt (x := y))
    rw [hψ, hsub, hg]
    constructor
    · rintro ⟨u, hu, hu0⟩
      have hu0' : u + (b - A (gradient (fun v ↦ (fenchelConjugate k v).toReal)
          (ContinuousLinearMap.adjoint A y - c))) = 0 := hu0
      refine ⟨gradient (fun v ↦ (fenchelConjugate k v).toReal)
        (ContinuousLinearMap.adjoint A y - c),
        rfl, ?_⟩
      have he : u = A (gradient (fun v ↦ (fenchelConjugate k v).toReal)
          (ContinuousLinearMap.adjoint A y - c)) - b := by
        calc u = u + (b - A (gradient (fun v ↦ (fenchelConjugate k v).toReal)
              (ContinuousLinearMap.adjoint A y - c))) - (b - A (gradient
              (fun v ↦ (fenchelConjugate k v).toReal) (ContinuousLinearMap.adjoint A y - c))) := by
              abel
          _ = A (gradient (fun v ↦ (fenchelConjugate k v).toReal)
              (ContinuousLinearMap.adjoint A y - c)) - b := by rw [hu0']; abel
      rw [← he]
      exact hu
    · rintro ⟨x, hx, hm⟩
      refine ⟨_, hm, ?_⟩
      change A x - b + (b - A (gradient (fun v ↦ (fenchelConjugate k v).toReal)
        (ContinuousLinearMap.adjoint A y - c))) = 0
      change x = gradient (fun v ↦ (fenchelConjugate k v).toReal)
        (ContinuousLinearMap.adjoint A y - c) at hx
      rw [hx]
      abel
  · have hhy' := not_lt_top_iff.mp hhy
    constructor
    · rintro ⟨⟨r, hr⟩, -⟩
      rw [doubleMinDual_eq A b c h hkp hkl hkc hkco, hhy', EReal.top_add_coe] at hr
      exact (EReal.coe_ne_top r hr.symm).elim
    · rintro ⟨x, -, ⟨r, hr⟩, -⟩
      rw [hhy'] at hr
      exact (EReal.coe_ne_top r hr.symm).elim

include hkp hkc hhc hhd in
/-- **Theorem 11.67**, the two objectives agree on `S`. -/
theorem doubleMinPrimal_eq_doubleMinDual_of_mem {x : E} {y : F}
    (hS : (x, y) ∈ doubleMinPairs A b c k h) :
    doubleMinPrimal A b c k h x = doubleMinDual A b c k h y := by
  obtain ⟨hy, hx⟩ := hS
  change y = gradient h (A x - b) at hy
  change ContinuousLinearMap.adjoint A y - c ∈ subdifferential k x at hx
  have hC := contDiff_of_convexOn_differentiable hhc hhd
  have hk := (mem_subdifferential_iff_fenchel_equality hkp hkc x
    (ContinuousLinearMap.adjoint A y - c)).mp hx
  have hyE : y ∈ subdifferential (fun u ↦ (h u : EReal)) (A x - b) := by
    rw [(subdifferentials_of_smooth (hC.contDiffAt (x := A x - b))).1, hy]
    rfl
  have hh := (mem_subdifferential_iff_fenchel_equality (isProper_coe_real h)
    (convex_epigraph_coe_of_convexOn hhc) (A x - b) y).mp hyE
  obtain ⟨κ, σ, hκ, hσ⟩ := exists_coe_components_of_add_eq_coe hk
  obtain ⟨-, η, -, hη⟩ := exists_coe_components_of_add_eq_coe hh
  rw [hκ, hσ, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hk
  rw [hη, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hh
  rw [doubleMinPrimal, doubleMinDual, hκ, hη, hσ, ← EReal.coe_add, ← EReal.coe_sub,
    ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
  rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left] at hk
  rw [inner_sub_right, real_inner_comm b y] at hh
  linarith

include hkp hkl hkc hhc hhd in
/-- **Theorem 11.67**, the primal objective is amenable at every point of its domain. -/
theorem amenableAt_doubleMinPrimal {x : E} (hx : doubleMinPrimal A b c k h x < ⊤) :
    AmenableAt (doubleMinPrimal A b c k h) x := by
  have hC := contDiff_of_convexOn_differentiable hhc hhd
  have hφ : doubleMinPrimal A b c k h = fun z ↦ k z + ((⟪c, z⟫_ℝ - h (A z - b) : ℝ) : EReal) :=
    funext (doubleMinPrimal_eq A b c k h)
  have hq : ContDiff ℝ 1 (fun z ↦ ⟪c, z⟫_ℝ - h (A z - b)) :=
    (contDiff_const.inner ℝ contDiff_id).sub (hC.comp (A.contDiff.sub contDiff_const))
  have hkx : x ∈ effectiveDomain k := by
    by_contra hn
    have hkx' : k x = ⊤ := not_lt_top_iff.mp hn
    rw [doubleMinPrimal_eq, hkx', EReal.top_add_coe] at hx
    exact lt_irrefl _ hx
  rw [hφ]
  exact convex_add_smooth_amenable hkp hkl hkc hkx hq

include hkp hkl hkc hkco hks hhc hhd in
/-- **Theorem 11.67**, the dual objective is amenable at every point of its domain. -/
theorem amenableAt_doubleMinDual {y : F} (hy : doubleMinDual A b c k h y < ⊤) :
    AmenableAt (doubleMinDual A b c k h) y := by
  have hkC := contDiff_fenchelConjugate_toReal hkp hkl hkc hkco hks
  obtain ⟨hsp, hsl, hsc, -, -⟩ := fenchelConjugate_coe_regular hhc hhd
  have hψ : doubleMinDual A b c k h = fun z ↦ fenchelConjugate (fun u ↦ (h u : EReal)) z +
      ((⟪b, z⟫_ℝ - (fenchelConjugate k (ContinuousLinearMap.adjoint A z - c)).toReal : ℝ) :
        EReal) :=
    funext (doubleMinDual_eq A b c h hkp hkl hkc hkco)
  have hq : ContDiff ℝ 1 (fun z ↦ ⟪b, z⟫_ℝ -
      (fenchelConjugate k (ContinuousLinearMap.adjoint A z - c)).toReal) :=
    (contDiff_const.inner ℝ contDiff_id).sub
      (hkC.comp ((ContinuousLinearMap.adjoint A).contDiff.sub contDiff_const))
  have hhy : y ∈ effectiveDomain (fenchelConjugate (fun u ↦ (h u : EReal))) := by
    by_contra hn
    have hhy' := not_lt_top_iff.mp
      (show ¬ fenchelConjugate (fun u ↦ (h u : EReal)) y < ⊤ from hn)
    rw [doubleMinDual_eq A b c h hkp hkl hkc hkco, hhy', EReal.top_add_coe] at hy
    exact lt_irrefl _ hy
  rw [hψ]
  exact convex_add_smooth_amenable hsp hsl hsc hhy hq

include hkp hkl hkc hkco hhc hhd in
/-- **Theorem 11.67**, the two optimal values always agree: `inf ϕ = inf ψ`. -/
theorem iInf_doubleMinPrimal_eq_iInf_doubleMinDual :
    ⨅ x, doubleMinPrimal A b c k h x = ⨅ y, doubleMinDual A b c k h y := by
  have hEl : LowerSemicontinuous (fun u ↦ (h u : EReal)) :=
    (continuous_coe_real_ereal.comp hhd.continuous).lowerSemicontinuous
  have hEc := convex_epigraph_coe_of_convexOn hhc
  have hsp := (fenchelConjugate_coe_regular hhc hhd).1
  have hbi := fenchelConjugate_fenchelConjugate_eq (isProper_coe_real h) hEl hEc
  apply le_antisymm
  · apply le_iInf
    intro y
    rw [doubleMinDual_eq A b c h hkp hkl hkc hkco]
    cases hhy : fenchelConjugate (fun u ↦ (h u : EReal)) y with
    | bot => exact absurd hhy (hsp.2 y).ne'
    | top => rw [EReal.top_add_coe]; exact le_top
    | coe η =>
      have hσ := fenchelConjugate_eq_coe_toReal_of_isCoercive hkp hkl hkc hkco
        (ContinuousLinearMap.adjoint A y - c)
      have hrw : ((η : ℝ) : EReal) + ((⟪b, y⟫_ℝ - (fenchelConjugate k
          (ContinuousLinearMap.adjoint A y - c)).toReal : ℝ) : EReal) =
          ((⟪b, y⟫_ℝ + η : ℝ) : EReal) -
            fenchelConjugate k (ContinuousLinearMap.adjoint A y - c) := by
        rw [hσ, EReal.toReal_coe, ← EReal.coe_add, ← EReal.coe_sub]
        congr 1
        ring
      rw [hrw, fenchelConjugate, ereal_coe_sub_iSup]
      apply iInf_mono
      intro x
      rw [doubleMinPrimal_eq]
      cases hkx : k x with
      | bot => exact absurd hkx (hkp.2 x).ne'
      | top => rw [EReal.top_add_coe, EReal.sub_top, EReal.coe_sub_bot]
      | coe κ =>
        rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        have hfy := fenchel_young (isProper_coe_real h) (A x - b) y
        rw [hhy, ← EReal.coe_add, EReal.coe_le_coe_iff] at hfy
        rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
        rw [inner_sub_right, real_inner_comm b y] at hfy
        linarith
  · apply le_iInf
    intro x
    rw [doubleMinPrimal_eq]
    cases hkx : k x with
    | bot => exact absurd hkx (hkp.2 x).ne'
    | top => rw [EReal.top_add_coe]; exact le_top
    | coe κ =>
      have hrw : ((κ : ℝ) : EReal) + ((⟪c, x⟫_ℝ - h (A x - b) : ℝ) : EReal) =
          ((⟪c, x⟫_ℝ + κ : ℝ) : EReal) - (fun u ↦ (h u : EReal)) (A x - b) := by
        rw [← EReal.coe_add, ← EReal.coe_sub]
        congr 1
        ring
      rw [hrw, ← hbi, fenchelConjugate, ereal_coe_sub_iSup]
      apply iInf_mono
      intro y
      rw [doubleMinDual_eq A b c h hkp hkl hkc hkco]
      cases hhy : fenchelConjugate (fun u ↦ (h u : EReal)) y with
      | bot => exact absurd hhy (hsp.2 y).ne'
      | top => rw [EReal.top_add_coe, EReal.sub_top, EReal.coe_sub_bot]
      | coe η =>
        rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        have hk := le_fenchelConjugate k x (ContinuousLinearMap.adjoint A y - c)
        rw [hkx, fenchelConjugate_eq_coe_toReal_of_isCoercive hkp hkl hkc hkco, ← EReal.coe_sub,
          EReal.coe_le_coe_iff] at hk
        rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left, real_inner_comm (A x) y] at hk
        rw [inner_sub_left]
        linarith

include hkp hkl hkc hkco hks hhc hhd in
/-- **Theorem 11.67** (double-min duality in optimization). For a proper, lower
semicontinuous, convex, coercive and almost strictly convex `k` and a finite,
differentiable, convex `h`:
* `h*` is proper, lower semicontinuous, convex, coercive and almost strictly
  convex, while `k*` is finite and continuously differentiable;
* the objectives `ϕ` and `ψ` are amenable at every point of their domains;
* `inf ϕ = inf ψ`;
* the two descriptions of `S` agree;
* `0 ∈ ∂ϕ(x̄)` iff `(x̄,ȳ) ∈ S` for some `ȳ`, and `0 ∈ ∂ψ(ȳ)` iff
  `(x̄,ȳ) ∈ S` for some `x̄`;
* `ϕ(x̄) = ψ(ȳ)` for every `(x̄,ȳ) ∈ S`. -/
theorem double_min_duality :
    (IsProper (fenchelConjugate (fun u ↦ (h u : EReal))) ∧
      LowerSemicontinuous (fenchelConjugate (fun u ↦ (h u : EReal))) ∧
      Convex ℝ (epigraph (fenchelConjugate (fun u ↦ (h u : EReal)))) ∧
      IsCoercive (fenchelConjugate (fun u ↦ (h u : EReal))) ∧
      IsAlmostStrictlyConvex (fenchelConjugate (fun u ↦ (h u : EReal)))) ∧
    (∀ v, fenchelConjugate k v = ((fenchelConjugate k v).toReal : EReal)) ∧
    ContDiff ℝ 1 (fun v ↦ (fenchelConjugate k v).toReal) ∧
    (∀ x, doubleMinPrimal A b c k h x < ⊤ → AmenableAt (doubleMinPrimal A b c k h) x) ∧
    (∀ y, doubleMinDual A b c k h y < ⊤ → AmenableAt (doubleMinDual A b c k h) y) ∧
    ⨅ x, doubleMinPrimal A b c k h x = ⨅ y, doubleMinDual A b c k h y ∧
    doubleMinPairs A b c k h = doubleMinPairsDual A b c k h ∧
    (∀ x, (0 : E) ∈ subdifferential (doubleMinPrimal A b c k h) x ↔
      ∃ y, (x, y) ∈ doubleMinPairs A b c k h) ∧
    (∀ y, (0 : F) ∈ subdifferential (doubleMinDual A b c k h) y ↔
      ∃ x, (x, y) ∈ doubleMinPairs A b c k h) ∧
    (∀ x y, (x, y) ∈ doubleMinPairs A b c k h →
      doubleMinPrimal A b c k h x = doubleMinDual A b c k h y) :=
  ⟨fenchelConjugate_coe_regular hhc hhd,
    fenchelConjugate_eq_coe_toReal_of_isCoercive hkp hkl hkc hkco,
    contDiff_fenchelConjugate_toReal hkp hkl hkc hkco hks,
    fun _ hx ↦ amenableAt_doubleMinPrimal hkp hkl hkc hhc hhd hx,
    fun _ hy ↦ amenableAt_doubleMinDual hkp hkl hkc hkco hks hhc hhd hy,
    iInf_doubleMinPrimal_eq_iInf_doubleMinDual hkp hkl hkc hkco hhc hhd,
    doubleMinPairs_eq_dual hkp hkl hkc hkco hks hhc hhd,
    zero_mem_subdifferential_doubleMinPrimal_iff hkp hhc hhd,
    zero_mem_subdifferential_doubleMinDual_iff hkp hkl hkc hkco hks hhc hhd,
    fun _ _ hS ↦ doubleMinPrimal_eq_doubleMinDual_of_mem hkp hkc hhc hhd hS⟩

end MainTheorem

end
end RW
