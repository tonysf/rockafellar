/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Normal Cones under a Constraint Qualification

The second and third displays of Theorem 6.14, for
`C = {x ∈ X | G(x) ∈ D}`: the limiting-normal inclusion
`N_C(x̄) ⊆ {∇G(x̄)*y + z | y ∈ N_D(G(x̄)), z ∈ N_X(x̄)}` under the printed
constraint qualification, and the Clarke regularity of `C` when `X` and `D`
are regular.  The first display, which needs no qualification, is in
[`ConstraintStructure.lean`](ConstraintStructure.lean).

Everything rests on one limit lemma, `mem_constraintNormals_of_tendsto`:
multipliers at nearby points, however large, produce a multiplier in the
limit.  The book argues by cases -- either the multipliers converge or they
are rescaled by `λⁿ ↘ 0` -- and applies the dichotomy three times.  Scaling by
`(1 + ‖y‖ + ‖z‖)⁻¹` instead merges the two cases into a single extraction from
the unit ball: the degenerate limit is exactly `λ = 0`, which the constraint
qualification excludes.  The one lemma then serves the penalty limit, the
propagation of the qualification to nearby points, and the outer
semicontinuity of the multiplier mapping.
-/

import RockafellarWets.Chapter6.ConstraintStructure
import RockafellarWets.Chapter6.SmoothGradientWitness
import RockafellarWets.Chapter6.Optimality

open Filter Metric Set Topology
open scoped InnerProductSpace

noncomputable section

namespace RW

section Defs

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The multiplier set `S(x)` of the proof of Theorem 6.14: the vectors
`∇G(x)*y + z` with `y` normal to `D` at `G(x)` and `z` normal to `X` at `x`.
By formula 6(9) this is the book's `Σ yᵢ ∇gᵢ(x) + z`. -/
def constraintNormals (X : Set E) (G : E → F) (D : Set F) (x : E) : Set E :=
  {v | ∃ y ∈ normalCone D (G x), ∃ z ∈ normalCone X x,
    ContinuousLinearMap.adjoint (fderiv ℝ G x) y + z = v}

theorem mem_constraintNormals {X : Set E} {G : E → F} {D : Set F} {x v : E} :
    v ∈ constraintNormals X G D x ↔
      ∃ y ∈ normalCone D (G x), ∃ z ∈ normalCone X x,
        ContinuousLinearMap.adjoint (fderiv ℝ G x) y + z = v :=
  Iff.rfl

/-- The constraint qualification of Theorem 6.14: the only multiplier for `D`
whose adjoint image is normal to `X` in the opposite direction is zero. -/
def ConstraintQualification (X : Set E) (G : E → F) (D : Set F) (x : E) : Prop :=
  ∀ y ∈ normalCone D (G x),
    -ContinuousLinearMap.adjoint (fderiv ℝ G x) y ∈ normalCone X x → y = 0

/-- Restated: under the qualification a multiplier pair summing to zero is the
zero pair. -/
theorem ConstraintQualification.eq_zero {X : Set E} {G : E → F} {D : Set F} {x : E}
    (hCQ : ConstraintQualification X G D x) {y : F} {z : E}
    (hy : y ∈ normalCone D (G x)) (hz : z ∈ normalCone X x)
    (hsum : ContinuousLinearMap.adjoint (fderiv ℝ G x) y + z = 0) :
    y = 0 ∧ z = 0 := by
  have hz' : -ContinuousLinearMap.adjoint (fderiv ℝ G x) y ∈ normalCone X x := by
    have hzeq : -ContinuousLinearMap.adjoint (fderiv ℝ G x) y = z := by
      rw [neg_eq_iff_add_eq_zero]
      exact hsum
    rwa [hzeq]
  have hy0 : y = 0 := hCQ y hy hz'
  refine ⟨hy0, ?_⟩
  rw [hy0, map_zero, zero_add] at hsum
  exact hsum

/-- The `C¹` hypothesis enters only here: the adjoint derivative depends
continuously on the base point. -/
theorem continuous_adjoint_fderiv {G : E → F} (hG : ContDiff ℝ 1 G) :
    Continuous fun w : E ↦ ContinuousLinearMap.adjoint (fderiv ℝ G w) :=
  ContinuousLinearMap.adjoint.continuous.comp (contDiff_one_iff_fderiv.mp hG).2

end Defs

section PenaltyGradients

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The gradient of the quadratic penalty in the primal variable.  The adjoint
appears because the gradient is the Riesz representative of
`e ↦ 2⟪G(w) - c, ∇G(w)e⟫`. -/
theorem hasGradientAt_norm_sub_const_sq {G : E → F} {G' : E →L[ℝ] F} {w : E} (c : F)
    (hGd : HasFDerivAt G G' w) :
    HasGradientAt (fun z : E ↦ ‖G z - c‖ ^ 2)
      ((2 : ℝ) • ContinuousLinearMap.adjoint G' (G w - c)) w := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hfd := (hGd.sub_const c).norm_sq
  refine hfd.congr_fderiv ?_
  ext e
  simp [ContinuousLinearMap.adjoint_inner_left]

/-- The gradient of the quadratic penalty in the dual variable. -/
theorem hasGradientAt_const_sub_norm_sq (c u : F) :
    HasGradientAt (fun w : F ↦ ‖c - w‖ ^ 2) ((2 : ℝ) • (u - c)) u := by
  have hrev : (fun w : F ↦ ‖c - w‖ ^ 2) = fun w : F ↦ ‖w - c‖ ^ 2 := by
    funext w
    rw [norm_sub_rev]
  rw [hrev, hasGradientAt_iff_hasFDerivAt]
  have hfd := ((hasFDerivAt_id u).sub_const c).norm_sq
  refine hfd.congr_fderiv ?_
  ext e
  simp

/-- The gradient of the penalized objective in the dual variable. -/
theorem hasGradientAt_penalty_dual (c u : F) {t : ℝ} (ht : t ≠ 0) (a : ℝ) :
    HasGradientAt (fun w : F ↦ a + (2 * t)⁻¹ * ‖c - w‖ ^ 2) (t⁻¹ • (u - c)) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hbase := (hasGradientAt_const_sub_norm_sq c u).hasFDerivAt
  have hfd := (hbase.const_mul (2 * t)⁻¹).const_add a
  refine hfd.congr_fderiv ?_
  ext e
  simp only [ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply_apply,
    real_inner_smul_left, smul_eq_mul]
  field_simp

/-- The gradient of the penalized objective in the primal variable. -/
theorem hasGradientAt_penalty_primal {G : E → F} {G' : E →L[ℝ] F} {w : E} {hh : E → ℝ}
    {g : E} (c : F) {t : ℝ} (ht : t ≠ 0) (hGd : HasFDerivAt G G' w)
    (hhd : HasGradientAt hh g w) :
    HasGradientAt (fun z : E ↦ -hh z + (2 * t)⁻¹ * ‖G z - c‖ ^ 2)
      (-g + t⁻¹ • ContinuousLinearMap.adjoint G' (G w - c)) w := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hbase := (hasGradientAt_norm_sub_const_sq (G := G) (G' := G') (w := w) c hGd).hasFDerivAt
  have hfd := hhd.hasFDerivAt.neg.add (hbase.const_mul (2 * t)⁻¹)
  refine hfd.congr_fderiv ?_
  ext e
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply_apply,
    inner_add_left, inner_neg_left, real_inner_smul_left, smul_eq_mul]
  field_simp

end PenaltyGradients

section LimitLemma

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {X : Set E} {D : Set F} {G : E → F} {x : E}

/-- The adjoint derivative applied to a moving vector passes to the limit.
This is the only place where the two limits interact, and it is where the
`C¹` hypothesis on `G` is used. -/
theorem tendsto_adjoint_fderiv_apply (hG : ContDiff ℝ 1 G)
    {xs : ℕ → E} {ys : ℕ → F} {y : F}
    (hxto : Tendsto xs atTop (nhds x)) (hyto : Tendsto ys atTop (nhds y)) :
    Tendsto (fun n ↦ ContinuousLinearMap.adjoint (fderiv ℝ G (xs n)) (ys n)) atTop
      (nhds (ContinuousLinearMap.adjoint (fderiv ℝ G x) y)) := by
  have hcont : Continuous fun q : E × F ↦
      ContinuousLinearMap.adjoint (fderiv ℝ G q.1) q.2 :=
    ((continuous_adjoint_fderiv hG).comp continuous_fst).clm_apply continuous_snd
  have hpair : Tendsto (fun n ↦ ((xs n, ys n) : E × F)) atTop (nhds ((x, y) : E × F)) :=
    Tendsto.prodMk_nhds hxto hyto
  have hto := (hcont.tendsto ((x, y) : E × F)).comp hpair
  exact hto

/-- **The limit lemma for multipliers.**  Under the constraint qualification at
`x̄`, a convergent sequence of vectors `∇G(xⁿ)*yⁿ + zⁿ` built from multipliers
at points approaching `x̄` has its limit of the same form at `x̄`.  No bound on
the multipliers is assumed: rescaling the triple `(1, yⁿ, zⁿ)` into the unit
ball and extracting a convergent subsequence produces a limit whose first
coordinate `λ` is either positive -- and then dividing by it gives the
representation -- or zero, in which case the qualification forces the whole
limit to vanish, contradicting that the three coordinates sum to `1`. -/
theorem mem_constraintNormals_of_tendsto
    (hG : ContDiff ℝ 1 G) (hCQ : ConstraintQualification X G D x)
    (hxX : x ∈ X) (hxD : G x ∈ D)
    {xs : ℕ → E} {us ys : ℕ → F} {zs vs : ℕ → E} {v : E}
    (hxto : Tendsto xs atTop (nhds x)) (huto : Tendsto us atTop (nhds (G x)))
    (hys : ∀ n, ys n ∈ normalCone D (us n))
    (hzs : ∀ n, zs n ∈ normalCone X (xs n))
    (hvs : ∀ n, ContinuousLinearMap.adjoint (fderiv ℝ G (xs n)) (ys n) + zs n = vs n)
    (hvto : Tendsto vs atTop (nhds v)) :
    v ∈ constraintNormals X G D x := by
  set A : E → (F →L[ℝ] E) := fun w ↦ ContinuousLinearMap.adjoint (fderiv ℝ G w) with hAdef
  set lam : ℕ → ℝ := fun n ↦ (1 + ‖ys n‖ + ‖zs n‖)⁻¹ with hlamdef
  have hden : ∀ n, (0 : ℝ) < 1 + ‖ys n‖ + ‖zs n‖ := fun n ↦ by positivity
  have hlampos : ∀ n, 0 < lam n := fun n ↦ inv_pos.2 (hden n)
  have hsum : ∀ n, lam n + ‖lam n • ys n‖ + ‖lam n • zs n‖ = 1 := by
    intro n
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (hlampos n)]
    have hne := (hden n).ne'
    simp only [hlamdef]
    field_simp
  -- the rescaled triples live in the closed unit ball of a finite-dimensional space
  set w : ℕ → ℝ × F × E := fun n ↦ (lam n, lam n • ys n, lam n • zs n) with hwdef
  have hmem : ∀ n, w n ∈ closedBall (0 : ℝ × F × E) 1 := by
    intro n
    have h1 : ‖lam n‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (hlampos n)]
      linarith [hsum n, norm_nonneg (lam n • ys n), norm_nonneg (lam n • zs n)]
    have h2 : ‖lam n • ys n‖ ≤ 1 := by
      linarith [hsum n, (hlampos n).le, norm_nonneg (lam n • zs n)]
    have h3 : ‖lam n • zs n‖ ≤ 1 := by
      linarith [hsum n, (hlampos n).le, norm_nonneg (lam n • ys n)]
    rw [mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    simp only [max_le_iff]
    exact ⟨h1, h2, h3⟩
  obtain ⟨p, -, φ, hφ, hpto⟩ := (isCompact_closedBall (0 : ℝ × F × E) 1).tendsto_subseq hmem
  have hφto : Tendsto φ atTop atTop := hφ.tendsto_atTop
  -- componentwise limits along the extraction
  have hlamto : Tendsto (fun n ↦ lam (φ n)) atTop (nhds p.1) :=
    ((continuous_fst.tendsto p).comp hpto)
  have hytilto : Tendsto (fun n ↦ lam (φ n) • ys (φ n)) atTop (nhds p.2.1) :=
    (((continuous_fst.comp continuous_snd).tendsto p).comp hpto)
  have hztilto : Tendsto (fun n ↦ lam (φ n) • zs (φ n)) atTop (nhds p.2.2) :=
    (((continuous_snd.comp continuous_snd).tendsto p).comp hpto)
  -- the limits are multipliers at the limit point, by 6.6
  have hytil : p.2.1 ∈ normalCone D (G x) :=
    mem_normalCone_of_tendsto hxD (fun n ↦ (hys (φ n)).1) (huto.comp hφto)
      (fun n ↦ (isCone_normalCone (hys (φ n)).1).2 (hys (φ n)) (hlampos (φ n))) hytilto
  have hztil : p.2.2 ∈ normalCone X x :=
    mem_normalCone_of_tendsto hxX (fun n ↦ (hzs (φ n)).1) (hxto.comp hφto)
      (fun n ↦ (isCone_normalCone (hzs (φ n)).1).2 (hzs (φ n)) (hlampos (φ n))) hztilto
  -- the rescaled relation passes to the limit
  have hrel : A x p.2.1 + p.2.2 = p.1 • v := by
    have hleft : Tendsto (fun n ↦ A (xs (φ n)) (lam (φ n) • ys (φ n)) + lam (φ n) • zs (φ n))
        atTop (nhds (A x p.2.1 + p.2.2)) :=
      (tendsto_adjoint_fderiv_apply hG (hxto.comp hφto) hytilto).add hztilto
    have hright : Tendsto (fun n ↦ lam (φ n) • vs (φ n)) atTop (nhds (p.1 • v)) :=
      hlamto.smul (hvto.comp hφto)
    refine tendsto_nhds_unique ?_ hright
    refine hleft.congr fun n ↦ ?_
    rw [map_smul, ← smul_add, hvs (φ n)]
  -- the three coordinates still sum to one
  have hnormsum : p.1 + ‖p.2.1‖ + ‖p.2.2‖ = 1 := by
    have hto : Tendsto (fun n ↦ lam (φ n) + ‖lam (φ n) • ys (φ n)‖ + ‖lam (φ n) • zs (φ n)‖)
        atTop (nhds (p.1 + ‖p.2.1‖ + ‖p.2.2‖)) :=
      (hlamto.add hytilto.norm).add hztilto.norm
    have hconst : Tendsto (fun n ↦ lam (φ n) + ‖lam (φ n) • ys (φ n)‖ + ‖lam (φ n) • zs (φ n)‖)
        atTop (nhds 1) := by
      simp only [hsum]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hto hconst
  have hlamnonneg : 0 ≤ p.1 :=
    ge_of_tendsto' hlamto fun n ↦ (hlampos (φ n)).le
  rcases hlamnonneg.eq_or_lt with hzero | hpos
  · -- the degenerate case is excluded by the constraint qualification
    exfalso
    have hsum0 : A x p.2.1 + p.2.2 = 0 := by
      rw [hrel, ← hzero, zero_smul]
    obtain ⟨hy0, hz0⟩ := hCQ.eq_zero hytil hztil hsum0
    rw [hy0, hz0, ← hzero] at hnormsum
    norm_num at hnormsum
  · refine ⟨p.1⁻¹ • p.2.1, (isCone_normalCone hxD).2 hytil (inv_pos.2 hpos),
      p.1⁻¹ • p.2.2, (isCone_normalCone hxX).2 hztil (inv_pos.2 hpos), ?_⟩
    rw [map_smul, ← smul_add, hrel, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

/-- **Outer semicontinuity of the multiplier mapping** at a point satisfying
the constraint qualification.  This is the closing step of the printed proof
of 6.14, and it is the limit lemma with `uⁿ = G(xⁿ)`. -/
theorem mem_constraintNormals_of_tendsto_constraintNormals
    (hG : ContDiff ℝ 1 G) (hCQ : ConstraintQualification X G D x)
    (hxX : x ∈ X) (hxD : G x ∈ D)
    {xs vs : ℕ → E} {v : E} (hxto : Tendsto xs atTop (nhds x))
    (hvmem : ∀ n, vs n ∈ constraintNormals X G D (xs n))
    (hvto : Tendsto vs atTop (nhds v)) :
    v ∈ constraintNormals X G D x := by
  choose ys hys zs hzs hrep using hvmem
  exact mem_constraintNormals_of_tendsto hG hCQ hxX hxD hxto
    ((hG.continuous.tendsto x).comp hxto) hys hzs hrep hvto

/-- **The constraint qualification propagates**: it holds at every point of
`C` near a point where it holds.  Were it to fail along a sequence, the
failing multipliers could be normalized to unit length, and a cluster point of
those would violate the qualification at the limit through 6.6. -/
theorem eventually_constraintQualification
    (hG : ContDiff ℝ 1 G) (hCQ : ConstraintQualification X G D x)
    (hxX : x ∈ X) (hxD : G x ∈ D) :
    ∀ᶠ z in nhdsWithin x (constrainedPreimage X G D), ConstraintQualification X G D z := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hpick : ∀ n : ℕ, ∃ z : E, ∃ y : F, z ∈ constrainedPreimage X G D ∧
      dist z x < 1 / ((n : ℝ) + 1) ∧ y ∈ normalCone D (G z) ∧
      -ContinuousLinearMap.adjoint (fderiv ℝ G z) y ∈ normalCone X z ∧ y ≠ 0 := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hev1 : ∀ᶠ z in nhdsWithin x (constrainedPreimage X G D),
        z ∈ constrainedPreimage X G D := self_mem_nhdsWithin
    have hev2 : ∀ᶠ z in nhdsWithin x (constrainedPreimage X G D),
        z ∈ ball x (1 / ((n : ℝ) + 1)) :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hpos)
    obtain ⟨z, hnot, hzC, hzball⟩ := (hcon.and_eventually (hev1.and hev2)).exists
    rw [ConstraintQualification] at hnot
    push_neg at hnot
    obtain ⟨y, hy, hyz, hyne⟩ := hnot
    exact ⟨z, y, hzC, mem_ball.1 hzball, hy, hyz, hyne⟩
  choose zs ys hzC hzd hys hyz hyne using hpick
  have hzto : Tendsto zs atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hzd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  set ws : ℕ → F := fun n ↦ ‖ys n‖⁻¹ • ys n with hwsdef
  have hinvpos : ∀ n, 0 < ‖ys n‖⁻¹ := fun n ↦ inv_pos.2 (norm_pos_iff.2 (hyne n))
  have hwsnorm : ∀ n, ‖ws n‖ = 1 := by
    intro n
    rw [hwsdef]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (hinvpos n)]
    exact inv_mul_cancel₀ (norm_pos_iff.2 (hyne n)).ne'
  have hwsD : ∀ n, ws n ∈ normalCone D (G (zs n)) := fun n ↦
    (isCone_normalCone (hys n).1).2 (hys n) (hinvpos n)
  have hwsX : ∀ n, -ContinuousLinearMap.adjoint (fderiv ℝ G (zs n)) (ws n) ∈
      normalCone X (zs n) := by
    intro n
    have hscale : -ContinuousLinearMap.adjoint (fderiv ℝ G (zs n)) (ws n) =
        ‖ys n‖⁻¹ • -ContinuousLinearMap.adjoint (fderiv ℝ G (zs n)) (ys n) := by
      rw [hwsdef]
      simp only [map_smul, smul_neg]
    rw [hscale]
    exact (isCone_normalCone (hyz n).1).2 (hyz n) (hinvpos n)
  have hmem : ∀ n, ws n ∈ closedBall (0 : F) 1 := fun n ↦ by
    rw [mem_closedBall, dist_zero_right, hwsnorm n]
  obtain ⟨y, -, φ, hφ, hyto⟩ := (isCompact_closedBall (0 : F) 1).tendsto_subseq hmem
  have hφto : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hynorm : ‖y‖ = 1 := by
    refine tendsto_nhds_unique (hyto.norm) ?_
    simp only [Function.comp_apply, hwsnorm]
    exact tendsto_const_nhds
  have hyD : y ∈ normalCone D (G x) :=
    mem_normalCone_of_tendsto hxD (fun n ↦ (hys (φ n)).1)
      ((hG.continuous.tendsto x).comp (hzto.comp hφto))
      (fun n ↦ hwsD (φ n)) hyto
  have hyX : -ContinuousLinearMap.adjoint (fderiv ℝ G x) y ∈ normalCone X x :=
    mem_normalCone_of_tendsto hxX (fun n ↦ (hzC (φ n)).1)
      (hzto.comp hφto) (fun n ↦ hwsX (φ n))
      ((tendsto_adjoint_fderiv_apply hG (hzto.comp hφto) hyto).neg)
  have hy0 : y = 0 := hCQ y hyD hyX
  rw [hy0, norm_zero] at hynorm
  norm_num at hynorm

end LimitLemma

section PenaltyArgument

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {X : Set E} {D : Set F} {G : E → F} {x : E}

/-- **Theorem 6.14** for regular normals, in the compact case the printed proof
reduces to.  A regular normal is the gradient at `x̄` of an everywhere-`C¹`
function whose maximum relative to `C` is attained at `x̄` alone, by 6.11.
Penalizing the constraint `G(x) = u` and minimizing over the compact `X × D`
produces multipliers at nearby points, and the limit lemma assembles them. -/
theorem regularNormalCone_subset_constraintNormals_of_isCompact
    (hG : ContDiff ℝ 1 G) (hX : IsCompact X) (hD : IsCompact D)
    (hCQ : ConstraintQualification X G D x) :
    regularNormalCone (constrainedPreimage X G D) x ⊆ constraintNormals X G D x := by
  intro v hv
  have hxC : x ∈ constrainedPreimage X G D := hv.1
  have hxX : x ∈ X := hxC.1
  have hxD : G x ∈ D := hxC.2
  obtain ⟨h, hhC1, hhgrad, hhmax, hhuniq⟩ :=
    exists_contDiff_one_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone hv
  have hGc : Continuous G := hG.continuous
  have hhc : Continuous h := hhC1.continuous
  have hgcont : Continuous (gradient h) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (contDiff_one_iff_fderiv.mp hhC1).2
  have hgh : ∀ w : E, HasGradientAt h (gradient h w) w := fun w ↦
    hasFDerivAt_iff_hasGradientAt.mp (hhC1.differentiable one_ne_zero w).hasFDerivAt
  have hgx : gradient h x = v := hhgrad.gradient
  obtain ⟨tau, htaupos, htauto⟩ : ∃ tau : ℕ → ℝ, (∀ n, 0 < tau n) ∧
      Tendsto tau atTop (nhds 0) :=
    ⟨fun n ↦ 1 / ((n : ℝ) + 1), fun n ↦ by positivity,
      tendsto_one_div_add_atTop_nhds_zero_nat⟩
  have hprod : IsCompact (X ×ˢ D) := hX.prod hD
  have hne : (X ×ˢ D).Nonempty := ⟨(x, G x), hxX, hxD⟩
  obtain ⟨ps, hps, hpsmin⟩ : ∃ ps : ℕ → E × F, (∀ n, ps n ∈ X ×ˢ D) ∧
      ∀ n, IsMinOn (fun q : E × F ↦ -h q.1 + (2 * tau n)⁻¹ * ‖G q.1 - q.2‖ ^ 2)
        (X ×ˢ D) (ps n) := by
    have hstep : ∀ n : ℕ, ∃ p, p ∈ X ×ˢ D ∧
        IsMinOn (fun q : E × F ↦ -h q.1 + (2 * tau n)⁻¹ * ‖G q.1 - q.2‖ ^ 2)
          (X ×ˢ D) p := by
      intro n
      have hcont : ContinuousOn
          (fun q : E × F ↦ -h q.1 + (2 * tau n)⁻¹ * ‖G q.1 - q.2‖ ^ 2) (X ×ˢ D) :=
        (((hhc.comp continuous_fst).neg).add (continuous_const.mul
          (((hGc.comp continuous_fst).sub continuous_snd).norm.pow 2))).continuousOn
      obtain ⟨p, hp, hmin⟩ := hprod.exists_isMinOn hne hcont
      exact ⟨p, hp, hmin⟩
    choose ps hps hpsmin using hstep
    exact ⟨ps, hps, hpsmin⟩
  -- comparing with the feasible point `x̄` bounds the penalty term
  have hcomp : ∀ n, -h (ps n).1 + (2 * tau n)⁻¹ * ‖G (ps n).1 - (ps n).2‖ ^ 2 ≤ -h x := by
    intro n
    have hxin : ((x, G x) : E × F) ∈ X ×ˢ D := ⟨hxX, hxD⟩
    have hle := isMinOn_iff.mp (hpsmin n) (x, G x) hxin
    simpa using hle
  have hpenalty : ∀ n, (2 * tau n)⁻¹ * ‖G (ps n).1 - (ps n).2‖ ^ 2 ≤ h (ps n).1 - h x :=
    fun n ↦ by linarith [hcomp n]
  have hhge : ∀ n, h x ≤ h (ps n).1 := by
    intro n
    have ht := htaupos n
    have hnn : 0 ≤ (2 * tau n)⁻¹ * ‖G (ps n).1 - (ps n).2‖ ^ 2 := by positivity
    linarith [hpenalty n]
  obtain ⟨xm, -, hxmmax⟩ := hX.exists_isMaxOn ⟨x, hxX⟩ hhc.continuousOn
  have hresid : ∀ n, ‖G (ps n).1 - (ps n).2‖ ^ 2 ≤ 2 * tau n * (h xm - h x) := by
    intro n
    have ht := htaupos n
    have h3 : (0 : ℝ) < 2 * tau n := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hpenalty n) h3.le
    rw [← mul_assoc, mul_inv_cancel₀ h3.ne', one_mul] at hmul
    refine hmul.trans ?_
    have h2 : h (ps n).1 ≤ h xm := isMaxOn_iff.mp hxmmax _ (hps n).1
    exact mul_le_mul_of_nonneg_left (by linarith) h3.le
  have hsq : Tendsto (fun n ↦ ‖G (ps n).1 - (ps n).2‖ ^ 2) atTop (nhds 0) := by
    refine squeeze_zero (fun n ↦ sq_nonneg _) hresid ?_
    have hlim : Tendsto (fun n ↦ 2 * tau n * (h xm - h x)) atTop
        (nhds (2 * 0 * (h xm - h x))) :=
      (tendsto_const_nhds.mul htauto).mul tendsto_const_nhds
    simpa using hlim
  have hres0 : Tendsto (fun n ↦ ‖G (ps n).1 - (ps n).2‖) atTop (nhds 0) := by
    have hc := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at hc
    exact hc.congr fun n ↦ Real.sqrt_sq (norm_nonneg _)
  -- a convergent subsequence of minimizers converges to `(x̄, G(x̄))`
  obtain ⟨q, hq, φ, hφ, hqto⟩ := hprod.tendsto_subseq hps
  have hφto : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hx1to : Tendsto (fun n ↦ (ps (φ n)).1) atTop (nhds q.1) :=
    (continuous_fst.tendsto q).comp hqto
  have hx2to : Tendsto (fun n ↦ (ps (φ n)).2) atTop (nhds q.2) :=
    (continuous_snd.tendsto q).comp hqto
  have hGq : G q.1 = q.2 := by
    have hto : Tendsto (fun n ↦ ‖G (ps (φ n)).1 - (ps (φ n)).2‖) atTop
        (nhds ‖G q.1 - q.2‖) :=
      (((hGc.tendsto q.1).comp hx1to).sub hx2to).norm
    have hzero : ‖G q.1 - q.2‖ = 0 := tendsto_nhds_unique hto (hres0.comp hφto)
    rwa [norm_sub_eq_zero_iff] at hzero
  have hqD : G q.1 ∈ D := by rw [hGq]; exact hq.2
  have hqC : q.1 ∈ constrainedPreimage X G D := ⟨hq.1, hqD⟩
  have hqge : h x ≤ h q.1 :=
    ge_of_tendsto' ((hhc.tendsto q.1).comp hx1to) fun n ↦ hhge (φ n)
  have hqle : h q.1 ≤ h x := isMaxOn_iff.mp hhmax _ hqC
  have hqeq : q.1 = x := hhuniq q.1 hqC (le_antisymm hqle hqge)
  have hxsto : Tendsto (fun n ↦ (ps (φ n)).1) atTop (nhds x) := by
    rw [← hqeq]
    exact hx1to
  have husto : Tendsto (fun n ↦ (ps (φ n)).2) atTop (nhds (G x)) := by
    have hq2 : q.2 = G x := by rw [← hGq, hqeq]
    rw [← hq2]
    exact hx2to
  -- the optimality conditions in each variable, by 6.12
  have hymem : ∀ n, (tau n)⁻¹ • (G (ps n).1 - (ps n).2) ∈ normalCone D ((ps n).2) := by
    intro n
    have hslice : IsMinOn
        (fun u : F ↦ -h (ps n).1 + (2 * tau n)⁻¹ * ‖G (ps n).1 - u‖ ^ 2) D ((ps n).2) := by
      rw [isMinOn_iff]
      intro u hu
      have hle := isMinOn_iff.mp (hpsmin n) ((ps n).1, u) ⟨(hps n).1, hu⟩
      simpa using hle
    have hgrad := hasGradientAt_penalty_dual (G (ps n).1) ((ps n).2)
      (htaupos n).ne' (-h (ps n).1)
    have hreg := IsLocalMinOn.neg_gradient_mem_regularNormalCone (hps n).2 hslice.localize hgrad
    have heq : -((tau n)⁻¹ • ((ps n).2 - G (ps n).1)) =
        (tau n)⁻¹ • (G (ps n).1 - (ps n).2) := by
      rw [← smul_neg, neg_sub]
    rw [heq] at hreg
    exact regularNormalCone_subset_normalCone D _ hreg
  have hzmem : ∀ n, gradient h (ps n).1 -
      ContinuousLinearMap.adjoint (fderiv ℝ G (ps n).1)
        ((tau n)⁻¹ • (G (ps n).1 - (ps n).2)) ∈ normalCone X ((ps n).1) := by
    intro n
    have hslice : IsMinOn
        (fun z : E ↦ -h z + (2 * tau n)⁻¹ * ‖G z - (ps n).2‖ ^ 2) X ((ps n).1) := by
      rw [isMinOn_iff]
      intro z hz
      have hle := isMinOn_iff.mp (hpsmin n) (z, (ps n).2) ⟨hz, (hps n).2⟩
      simpa using hle
    have hGd : HasFDerivAt G (fderiv ℝ G (ps n).1) ((ps n).1) :=
      (hG.differentiable one_ne_zero (ps n).1).hasFDerivAt
    have hgrad := hasGradientAt_penalty_primal ((ps n).2) (htaupos n).ne' hGd (hgh (ps n).1)
    have hreg := IsLocalMinOn.neg_gradient_mem_regularNormalCone (hps n).1 hslice.localize hgrad
    have heq : -(-gradient h (ps n).1 + (tau n)⁻¹ •
        ContinuousLinearMap.adjoint (fderiv ℝ G (ps n).1) (G (ps n).1 - (ps n).2)) =
        gradient h (ps n).1 - ContinuousLinearMap.adjoint (fderiv ℝ G (ps n).1)
          ((tau n)⁻¹ • (G (ps n).1 - (ps n).2)) := by
      rw [map_smul]
      abel
    rw [heq] at hreg
    exact regularNormalCone_subset_normalCone X _ hreg
  have hvto : Tendsto (fun n ↦ gradient h (ps (φ n)).1) atTop (nhds v) := by
    have hlim := (hgcont.tendsto x).comp hxsto
    rwa [hgx] at hlim
  refine mem_constraintNormals_of_tendsto hG hCQ hxX hxD hxsto husto
    (fun n ↦ hymem (φ n)) (fun n ↦ hzmem (φ n)) (fun n ↦ ?_) hvto
  abel

end PenaltyArgument

section SetIdentity

variable {E F : Type*}

/-- Shrinking `X` and `D` to neighborhoods shrinks the constraint set by the
corresponding neighborhood of the base point. -/
theorem constrainedPreimage_inter (X : Set E) (G : E → F) (D : Set F)
    (U : Set E) (W : Set F) :
    constrainedPreimage (X ∩ U) G (D ∩ W) =
      constrainedPreimage X G D ∩ (U ∩ G ⁻¹' W) := by
  ext z
  simp only [constrainedPreimage, mem_inter_iff, mem_preimage]
  tauto

end SetIdentity

section Localization

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {X : Set E} {D : Set F} {G : E → F} {x : E}

/-- The multiplier set is local in both constraint sets. -/
theorem constraintNormals_inter_nhds {U : Set E} {W : Set F} (hU : U ∈ nhds x)
    (hW : W ∈ nhds (G x)) :
    constraintNormals (X ∩ U) G (D ∩ W) x = constraintNormals X G D x := by
  unfold constraintNormals
  rw [normalCone_inter_nhds hU, normalCone_inter_nhds hW]

/-- The constraint qualification is local in both constraint sets. -/
theorem constraintQualification_inter_nhds {U : Set E} {W : Set F} (hU : U ∈ nhds x)
    (hW : W ∈ nhds (G x)) :
    ConstraintQualification (X ∩ U) G (D ∩ W) x ↔ ConstraintQualification X G D x := by
  unfold ConstraintQualification
  rw [normalCone_inter_nhds hU, normalCone_inter_nhds hW]

/-- **Theorem 6.14** for regular normals, with the printed hypotheses.  The
compactness the proof uses costs nothing: intersecting `X` and `D` with unit
balls changes neither side, since normal cones and the qualification are all
local. -/
theorem regularNormalCone_subset_constraintNormals
    (hG : ContDiff ℝ 1 G) (hX : IsClosed X) (hD : IsClosed D)
    (hCQ : ConstraintQualification X G D x) :
    regularNormalCone (constrainedPreimage X G D) x ⊆ constraintNormals X G D x := by
  have hU : closedBall x 1 ∈ nhds x := closedBall_mem_nhds x one_pos
  have hW : closedBall (G x) 1 ∈ nhds (G x) := closedBall_mem_nhds (G x) one_pos
  have hV : closedBall x 1 ∩ G ⁻¹' closedBall (G x) 1 ∈ nhds x :=
    inter_mem hU (hG.continuous.continuousAt.preimage_mem_nhds hW)
  have hmain := regularNormalCone_subset_constraintNormals_of_isCompact hG
    ((isCompact_closedBall x 1).inter_left hX)
    ((isCompact_closedBall (G x) 1).inter_left hD)
    ((constraintQualification_inter_nhds hU hW).mpr hCQ)
  rwa [constraintNormals_inter_nhds hU hW, constrainedPreimage_inter,
    regularNormalCone_inter_nhds hV] at hmain

/-- **Theorem 6.14**, second display: under the constraint qualification every
limiting normal to `C = {x ∈ X | G(x) ∈ D}` has a multiplier representation.
The qualification holds at all nearby points of `C`, so the regular-normal
statement applies along the sequence defining a limiting normal, and outer
semicontinuity of the multiplier mapping closes the argument. -/
theorem normalCone_subset_constraintNormals
    (hG : ContDiff ℝ 1 G) (hX : IsClosed X) (hD : IsClosed D)
    (hCQ : ConstraintQualification X G D x) :
    normalCone (constrainedPreimage X G D) x ⊆ constraintNormals X G D x := by
  intro v hv
  obtain ⟨hxC, xs, vs, hxsC, hxsto, hvs, hvto⟩ := hv
  have hev := eventually_constraintQualification hG hCQ hxC.1 hxC.2
  have hxin : Tendsto xs atTop (nhdsWithin x (constrainedPreimage X G D)) :=
    tendsto_nhdsWithin_of_forall_mem hxsC hxsto
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hxin hev)
  have hshift : Tendsto (fun n ↦ n + N) atTop atTop := tendsto_add_atTop_nat N
  refine mem_constraintNormals_of_tendsto_constraintNormals hG hCQ hxC.1 hxC.2
    (hxsto.comp hshift) (fun n ↦ ?_) (hvto.comp hshift)
  exact regularNormalCone_subset_constraintNormals hG hX hD (hN (n + N) (by omega))
    (hvs (n + N))

/-- The converse inclusion at a point where both constraint sets are Clarke
regular: this is the first display of 6.14 with `N̂` replaced by `N`. -/
theorem constraintNormals_subset_regularNormalCone
    (hGd : HasFDerivAt G (fderiv ℝ G x) x)
    (hXreg : normalCone X x = regularNormalCone X x)
    (hDreg : normalCone D (G x) = regularNormalCone D (G x)) :
    constraintNormals X G D x ⊆ regularNormalCone (constrainedPreimage X G D) x := by
  rintro v ⟨y, hy, z, hz, rfl⟩
  rw [hDreg] at hy
  rw [hXreg] at hz
  exact adjoint_add_mem_regularNormalCone_constrainedPreimage hGd hy hz

/-- **Theorem 6.14**, third display: under the constraint qualification, Clarke
regularity of `X` at `x̄` and of `D` at `G(x̄)` makes `C` Clarke regular at `x̄`,
with the multiplier representation exact. -/
theorem isClarkeRegularAt_constrainedPreimage
    (hG : ContDiff ℝ 1 G) (hX : IsClosed X) (hD : IsClosed D)
    (hCQ : ConstraintQualification X G D x)
    (hXreg : IsClarkeRegularAt X x) (hDreg : IsClarkeRegularAt D (G x)) :
    IsClarkeRegularAt (constrainedPreimage X G D) x ∧
      normalCone (constrainedPreimage X G D) x = constraintNormals X G D x := by
  have hCclosed : IsClosed (constrainedPreimage X G D) :=
    hX.inter (hD.preimage hG.continuous)
  have hGd : HasFDerivAt G (fderiv ℝ G x) x :=
    (hG.differentiable one_ne_zero x).hasFDerivAt
  have h1 := normalCone_subset_constraintNormals hG hX hD hCQ
  have h2 := constraintNormals_subset_regularNormalCone hGd hXreg.2 hDreg.2
  have h3 := regularNormalCone_subset_normalCone (constrainedPreimage X G D) x
  exact ⟨⟨RW.IsClosed.isLocallyClosedAt hCclosed x, Subset.antisymm (h1.trans h2) h3⟩,
    Subset.antisymm h1 (h2.trans h3)⟩

end Localization

end RW
