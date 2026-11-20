/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Support of strict graphical derivatives
-/

import RockafellarWets.Chapter9.CompactClusterSupport
import RockafellarWets.Chapter9.LipschitzSubderivatives
import RockafellarWets.Chapter9.CoderivativeScalarization
import RockafellarWets.Chapter9.StrictGraphicalDerivatives
import RockafellarWets.Chapter9.StrictDerivativeSequences

open Filter Metric Set Topology
open scoped NNReal InnerProductSpace

namespace RW

section Quotients

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The moving-base fixed-direction quotients of a locally Lipschitz
mapping remain uniformly bounded as the base point approaches `x` and
the positive scale tends to zero. -/
theorem StrictlyContinuousAt.eventually_norm_movingDifferenceQuotient_le
    {f : E → F} {x : E} (hf : StrictlyContinuousAt f x) (w : E) :
    ∃ k : ℝ≥0, ∀ᶠ p : E × ℝ in 𝓝 x ×ˢ 𝓝[>] (0 : ℝ),
      ‖p.2⁻¹ • (f (p.1 + p.2 • w) - f p.1)‖ ≤ k * ‖w‖ := by
  obtain ⟨k,U,hU,hL⟩ := strictlyContinuousAt_iff.mp hf
  refine ⟨k,?_⟩
  have hy : Tendsto (Prod.fst : E × ℝ → E) (𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 x) := tendsto_fst
  have ht : Tendsto (Prod.snd : E × ℝ → ℝ) (𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) (𝓝[>] 0) := tendsto_snd
  have hpath : Tendsto (fun p : E × ℝ ↦ p.1 + p.2 • w)
      (𝓝 x ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using
      hy.add ((ht.mono_right nhdsWithin_le_nhds).smul tendsto_const_nhds)
  filter_upwards [hy.eventually hU,hpath.eventually hU,ht.eventually self_mem_nhdsWithin]
    with p hp hp' ht'
  have hpos : 0 < p.2 := ht'
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),inv_mul_le_iff₀ hpos]
  have hnorm := hL.norm_sub_le hp' hp
  rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hpos.le] at hnorm
  convert hnorm using 1 <;> ring

end Quotients

section Duality

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Strict graphical derivative fibers of a strictly continuous mapping
are nonempty and compact. -/
theorem StrictlyContinuousAt.strictGraphicalDerivative_nonempty_compact
    {f : E → F} {x : E} (hf : StrictlyContinuousAt f x) (w : E) :
    (strictGraphicalDerivative (svSingleton f) x (f x) w).Nonempty ∧
      IsCompact (strictGraphicalDerivative (svSingleton f) x (f x) w) := by
  have hrep := strictGraphicalDerivative_singleton_eq_outerLimit hf w
  change strictGraphicalDerivative (svSingleton f) x (f x) w = _ at hrep
  rw [hrep]
  obtain ⟨k,hk⟩ := hf.eventually_norm_movingDifferenceQuotient_le w
  apply outerSetLimitAlong_singleton_nonempty_compact (isCompact_closedBall 0 (k * ‖w‖))
  filter_upwards [hk] with p hp
  simpa only [mem_closedBall,dist_zero_right] using hp

/-- **Theorem 9.62**, the strict-derivative half of the support identity:
the regular subderivative of a scalarization is attained on the strict
graphical derivative fiber. -/
theorem StrictlyContinuousAt.exists_max_inner_strictGraphicalDerivative
    {f : E → F} {x : E} (hf : StrictlyContinuousAt f x) (w : E) (y : F) :
    ∃ z ∈ strictGraphicalDerivative (svSingleton f) x (f x) w,
      regularSubderivative (fun a ↦ (⟪y,f a⟫_ℝ : EReal)) x w = (⟪y,z⟫_ℝ : EReal) ∧
      ∀ z' ∈ strictGraphicalDerivative (svSingleton f) x (f x) w,
        ⟪y,z'⟫_ℝ ≤ ⟪y,z⟫_ℝ := by
  have hrep := strictGraphicalDerivative_singleton_eq_outerLimit hf w
  change strictGraphicalDerivative (svSingleton f) x (f x) w = _ at hrep
  rw [hrep]
  obtain ⟨k,hk⟩ := hf.eventually_norm_movingDifferenceQuotient_le w
  have hbound : ∀ᶠ p : E × ℝ in 𝓝 x ×ˢ 𝓝[>] (0 : ℝ),
      p.2⁻¹ • (f (p.1 + p.2 • w) - f p.1) ∈ closedBall 0 (k * ‖w‖) := by
    filter_upwards [hk] with p hp
    simpa only [mem_closedBall,dist_zero_right] using hp
  obtain ⟨z,hz,he,hmax⟩ := exists_max_outerSetLimitAlong_eq_limsup
    (isCompact_closedBall 0 (k * ‖w‖)) hbound (continuous_const.inner continuous_id)
  refine ⟨z,hz,?_,hmax⟩
  have hsc : ERealStrictlyContinuousAt (fun a ↦ (⟪y,f a⟫_ℝ : EReal)) x :=
    ⟨by simp,by simpa only [EReal.toReal_coe] using hf.inner_const y⟩
  rw [hsc.regularSubderivative_eq_limsup_differenceQuotient]
  convert he using 2
  funext p
  rw [differenceQuotient_eq_coe (f := fun a ↦ (⟪y,f a⟫_ℝ : EReal)) rfl rfl]
  simp only [id_eq,inner_smul_right,inner_sub_right]

/-- **Theorem 9.62**, duality of the strict derivative and coderivative,
including attainment of both maxima. This part does not require any
choice of negligible exceptional set. -/
theorem StrictlyContinuousAt.strictGraphicalDerivative_coderivative_max_duality
    {f : E → F} {x : E} (hf : StrictlyContinuousAt f x) (w : E) (y : F) :
    ∃ z ∈ strictGraphicalDerivative (svSingleton f) x (f x) w,
      ∃ v ∈ coderivative (svSingleton f) x (f x) y,
        ⟪y,z⟫_ℝ = ⟪v,w⟫_ℝ ∧
        (∀ z' ∈ strictGraphicalDerivative (svSingleton f) x (f x) w,
          ⟪y,z'⟫_ℝ ≤ ⟪y,z⟫_ℝ) ∧
        ∀ v' ∈ coderivative (svSingleton f) x (f x) y, ⟪v',w⟫_ℝ ≤ ⟪v,w⟫_ℝ := by
  obtain ⟨z,hz,hze,hzm⟩ := hf.exists_max_inner_strictGraphicalDerivative w y
  have hsc : ERealStrictlyContinuousAt (fun a ↦ (⟪y,f a⟫_ℝ : EReal)) x :=
    ⟨by simp,by simpa only [EReal.toReal_coe] using hf.inner_const y⟩
  obtain ⟨v,hv,hve,hvm⟩ := hsc.exists_max_inner_subdifferential w
  rw [coderivative_svSingleton_eq_subdifferential hf y]
  exact ⟨z,hz,v,hv,EReal.coe_injective (hze.symm.trans hve),hzm,hvm⟩

theorem StrictlyContinuousAt.regularSubderivative_scalar_eq_support_strictGraphicalDerivative
    {f : E → F} {x : E} (hf : StrictlyContinuousAt f x) (w : E) (y : F) :
    regularSubderivative (fun a ↦ (⟪y,f a⟫_ℝ : EReal)) x w =
      supportFunction (strictGraphicalDerivative (svSingleton f) x (f x) w) y := by
  obtain ⟨z,hz,he,hmax⟩ := hf.exists_max_inner_strictGraphicalDerivative w y
  rw [he]
  apply le_antisymm
  · simpa only [real_inner_comm z y] using inner_le_supportFunction hz y
  · apply (supportFunction_le_iff _ _ _).mpr
    intro a ha
    exact EReal.coe_le_coe_iff.mpr (by simpa only [real_inner_comm a y] using hmax a ha)

end Duality

end RW
