/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Normals to sets with constraint structure

Theorem 6.14. A normalized Fritz John multiplier statement is proved first,
without a constraint qualification. The qualification rules out a zero
objective multiplier and gives the normal-cone calculus rule.
-/

import RockafellarWets.Chapter6.ConstraintPenalty
import RockafellarWets.Chapter6.ConstraintQualificationDefs
import RockafellarWets.Chapter6.RegularNormalChangeOfCoordinates
import RockafellarWets.Chapter6.TangentNormalPolarity

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Normalize an objective coefficient and a multiplier, and extract a
convergent subsequence without assuming that the multipliers are bounded. -/
theorem exists_normalized_multiplier_subsequence (τ : ℕ → ℝ) (v : ℕ → F)
    (hτ : ∀ n, 0 < τ n) :
    ∃ (a : ℝ) (y : F) (φ : ℕ → ℕ), StrictMono φ ∧ 0 ≤ a ∧ a + ‖y‖ = 1 ∧
      Tendsto (fun n ↦ τ (φ n) / (τ (φ n) + ‖v (φ n)‖)) atTop (𝓝 a) ∧
      Tendsto (fun n ↦ (τ (φ n) + ‖v (φ n)‖)⁻¹ • v (φ n)) atTop (𝓝 y) := by
  let as : ℕ → ℝ := fun n ↦ τ n / (τ n + ‖v n‖)
  let ys : ℕ → F := fun n ↦ (τ n + ‖v n‖)⁻¹ • v n
  have hden : ∀ n, 0 < τ n + ‖v n‖ := fun n ↦ add_pos_of_pos_of_nonneg (hτ n) (norm_nonneg _)
  have ha : ∀ n, as n ∈ Icc (0 : ℝ) 1 := by
    intro n
    exact ⟨div_nonneg (hτ n).le (hden n).le,
      (div_le_one (hden n)).2 (le_add_of_nonneg_right (norm_nonneg _))⟩
  have hsum : ∀ n, as n + ‖ys n‖ = 1 := by
    intro n
    dsimp [as, ys]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hden n))]
    field_simp [(hden n).ne']
  have hy : ∀ n, ys n ∈ closedBall (0 : F) 1 := by
    intro n
    rw [mem_closedBall, dist_zero_right]
    linarith [(ha n).1, hsum n]
  obtain ⟨p, hp, φ, hφ, hto⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : F) 1)).tendsto_subseq
      (fun n ↦ show (as n, ys n) ∈ Icc (0 : ℝ) 1 ×ˢ closedBall (0 : F) 1 from ⟨ha n, hy n⟩)
  refine ⟨p.1, p.2, φ, hφ, hp.1.1, ?_, hto.fst_nhds, hto.snd_nhds⟩
  exact tendsto_nhds_unique (hto.fst_nhds.add hto.snd_nhds.norm)
    (tendsto_const_nhds.congr fun n ↦ (hsum (φ n)).symm)

set_option maxHeartbeats 800000 in
-- The proof combines two compactness extractions with several derivative instances.
/-- The regular-normal Fritz John rule, with normalized multipliers. -/
theorem exists_fritzJohn_of_mem_regularNormalCone
    {X : Set E} {D : Set F} (hX : IsClosed X) (hD : IsClosed D)
    {f : E → F} (hf : ContDiff ℝ 1 f) {x v : E}
    (hv : v ∈ regularNormalCone (X ∩ f ⁻¹' D) x) :
    ∃ (a : ℝ) (y : F), 0 ≤ a ∧ a + ‖y‖ = 1 ∧
      y ∈ normalCone D (f x) ∧
      a • v - (fderiv ℝ f x).adjoint y ∈ normalCone X x := by
  have hx := mem_of_mem_regularNormalCone hv
  obtain ⟨h, hh, hgrad, hmax, hunique⟩ :=
    exists_contDiff_one_hasGradientAt_unique_isMaxOn_of_mem_regularNormalCone hv
  let Xb := X ∩ closedBall x 1
  let Db := D ∩ closedBall (f x) 1
  have hxXb : x ∈ Xb := ⟨hx.1, mem_closedBall_self (by norm_num)⟩
  have hxDb : f x ∈ Db := ⟨hx.2, mem_closedBall_self (by norm_num)⟩
  have hXb : IsCompact Xb := (isCompact_closedBall x 1).inter_left hX
  have hDb : IsCompact Db := (isCompact_closedBall (f x) 1).inter_left hD
  obtain ⟨τ, xs, us, hτpos, -, hxs, hus, hxsto, husto, hmin⟩ :=
    exists_penalty_minimizers_tendsto hXb hDb hf.continuous hh.continuous hxXb hxDb
      (fun z hz ↦ hmax ⟨hz.1.1, hz.2.1⟩)
      (fun z hz heq ↦ hunique z ⟨hz.1.1, hz.2.1⟩ heq)
  let g : E → E := fun z ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h z)
  have hg : ∀ z, HasGradientAt h (g z) z := fun z ↦
    ((hh.differentiable (by norm_num)).differentiableAt.hasFDerivAt).hasGradientAt
  have hgx : g x = v := (hg x).unique hgrad
  have hgcont : Continuous g :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hh.continuous_fderiv (by norm_num))
  let r : ℕ → F := fun n ↦ f (xs n) - us n
  obtain ⟨a, y, φ, hφ, ha, hnorm, hato, hyto⟩ :=
    exists_normalized_multiplier_subsequence τ r hτpos
  let d : ℕ → ℝ := fun n ↦ (τ n + ‖r n‖)⁻¹
  have hd : ∀ n, 0 < d n := fun n ↦
    inv_pos.2 (add_pos_of_pos_of_nonneg (hτpos n) (norm_nonneg _))
  have hnormals : ∀ n,
      d n • (τ n • g (xs n) - (fderiv ℝ f (xs n)).adjoint (r n))
        ∈ regularNormalCone Xb (xs n) ∧
      d n • r n ∈ regularNormalCone Db (us n) := by
    intro n
    obtain ⟨hxn, hun⟩ := penalty_minimizer_regular_normals (hxs n) (hus n)
      ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt) (hg (xs n)) (hmin n)
    exact ⟨(isCone_regularNormalCone (hxs n)).2 hxn (hd n),
      (isCone_regularNormalCone (hus n)).2 hun (hd n)⟩
  have hAto := ((ContinuousLinearMap.adjoint.continuous.comp
    (hf.continuous_fderiv (by norm_num))).tendsto x).comp (hxsto.comp hφ.tendsto_atTop)
  have hAyto : Tendsto (fun n ↦ (fderiv ℝ f (xs (φ n))).adjoint (d (φ n) • r (φ n)))
      atTop (𝓝 ((fderiv ℝ f x).adjoint y)) := by
    exact ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := F) (F := E)).continuous.tendsto
      ((fderiv ℝ f x).adjoint, y)).comp (hAto.prodMk_nhds hyto)
  have hgto : Tendsto (fun n ↦ g (xs (φ n))) atTop (𝓝 v) := by
    simpa only [hgx] using (hgcont.tendsto x).comp (hxsto.comp hφ.tendsto_atTop)
  have hzto : Tendsto (fun n ↦ d (φ n) •
      (τ (φ n) • g (xs (φ n)) - (fderiv ℝ f (xs (φ n))).adjoint (r (φ n))))
      atTop (𝓝 (a • v - (fderiv ℝ f x).adjoint y)) := by
    convert (hato.smul hgto).sub hAyto using 1
    ext n
    simp only [smul_sub, smul_smul, map_smul, d, div_eq_mul_inv, mul_comm]
  have hyD : y ∈ normalCone Db (f x) :=
    mem_normalCone_of_forall hxDb (husto.comp hφ.tendsto_atTop)
      (fun n ↦ (hnormals (φ n)).2) hyto
  have hzX : a • v - (fderiv ℝ f x).adjoint y ∈ normalCone Xb x :=
    mem_normalCone_of_forall hxXb (hxsto.comp hφ.tendsto_atTop)
      (fun n ↦ (hnormals (φ n)).1) hzto
  rw [normalCone_inter_nhds (closedBall_mem_nhds (f x) (by norm_num))] at hyD
  rw [normalCone_inter_nhds (closedBall_mem_nhds x (by norm_num))] at hzX
  exact ⟨a, y, ha, hnorm, hyD, hzX⟩

set_option maxHeartbeats 800000 in
-- The compactness extraction on `Icc 0 1 ×ˢ closedBall 0 1` and the varying
-- adjoint limits need the same enlarged budget as the regular-normal rule.
/-- The limiting-normal Fritz John rule, requiring no constraint qualification. -/
theorem exists_fritzJohn_of_mem_normalCone
    {X : Set E} {D : Set F} (hX : IsClosed X) (hD : IsClosed D)
    {f : E → F} (hf : ContDiff ℝ 1 f) {x v : E}
    (hv : v ∈ normalCone (X ∩ f ⁻¹' D) x) :
    ∃ (a : ℝ) (y : F), 0 ≤ a ∧ a + ‖y‖ = 1 ∧
      y ∈ normalCone D (f x) ∧
      a • v - (fderiv ℝ f x).adjoint y ∈ normalCone X x := by
  obtain ⟨hx, xs, vs, hxs, hxto, hvs, hvto⟩ := hv
  have hfj := fun n ↦ exists_fritzJohn_of_mem_regularNormalCone hX hD hf (hvs n)
  choose as ys ha hnorm hy hz using hfj
  have hm : ∀ n, (as n, ys n) ∈ Icc (0 : ℝ) 1 ×ˢ closedBall (0 : F) 1 := by
    intro n
    refine ⟨⟨ha n, ?_⟩, ?_⟩
    · linarith [norm_nonneg (ys n), hnorm n]
    · rw [mem_closedBall, dist_zero_right]
      linarith [ha n, hnorm n]
  obtain ⟨p, hp, φ, hφ, hto⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : F) 1)).tendsto_subseq hm
  have hsum : p.1 + ‖p.2‖ = 1 :=
    tendsto_nhds_unique (hto.fst_nhds.add hto.snd_nhds.norm)
      (tendsto_const_nhds.congr fun n ↦ (hnorm (φ n)).symm)
  have hyD : p.2 ∈ normalCone D (f x) :=
    mem_normalCone_of_tendsto (show f x ∈ D from hx.2)
      (fun n ↦ show f (xs (φ n)) ∈ D from (hxs (φ n)).2)
      ((hf.continuous.tendsto x).comp (hxto.comp hφ.tendsto_atTop))
      (fun n ↦ hy (φ n)) hto.snd_nhds
  have hAto := ((ContinuousLinearMap.adjoint.continuous.comp
    (hf.continuous_fderiv (by norm_num))).tendsto x).comp (hxto.comp hφ.tendsto_atTop)
  have hAyto : Tendsto (fun n ↦ (fderiv ℝ f (xs (φ n))).adjoint (ys (φ n)))
      atTop (𝓝 ((fderiv ℝ f x).adjoint p.2)) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := F) (F := E)).continuous.tendsto
      ((fderiv ℝ f x).adjoint, p.2)).comp (hAto.prodMk_nhds hto.snd_nhds)
  have hzX : p.1 • v - (fderiv ℝ f x).adjoint p.2 ∈ normalCone X x :=
    mem_normalCone_of_tendsto hx.1 (fun n ↦ (hxs (φ n)).1)
      (hxto.comp hφ.tendsto_atTop) (fun n ↦ hz (φ n))
      ((hto.fst_nhds.smul (hvto.comp hφ.tendsto_atTop)).sub hAyto)
  exact ⟨p.1, p.2, hp.1.1, hsum, hyD, hzX⟩

/-- **Theorem 6.14**, the limiting-normal multiplier representation. -/
theorem exists_normal_multipliers_of_mem_normalCone
    {X : Set E} {D : Set F} (hX : IsClosed X) (hD : IsClosed D)
    {f : E → F} (hf : ContDiff ℝ 1 f) {x v : E}
    (hCQ : NormalConstraintQualification X D (fderiv ℝ f x) x (f x))
    (hv : v ∈ normalCone (X ∩ f ⁻¹' D) x) :
    ∃ y ∈ normalCone D (f x), ∃ z ∈ normalCone X x,
      v = (fderiv ℝ f x).adjoint y + z := by
  have hx := hv.1
  obtain ⟨a, y, ha, hnorm, hy, hz⟩ := exists_fritzJohn_of_mem_normalCone hX hD hf hv
  have hapos : 0 < a := by
    apply lt_of_le_of_ne ha
    intro hzero
    have ha0 : a = 0 := hzero.symm
    have hy0 := hCQ y hy (by simpa only [ha0, zero_smul, zero_sub] using hz)
    simp only [ha0, hy0, norm_zero, add_zero] at hnorm
    norm_num at hnorm
  refine ⟨a⁻¹ • y, (isCone_normalCone (show f x ∈ D from hx.2)).2 hy (inv_pos.2 hapos),
    a⁻¹ • (a • v - (fderiv ℝ f x).adjoint y),
    (isCone_normalCone hx.1).2 hz (inv_pos.2 hapos), ?_⟩
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hapos.ne', one_smul, map_smul]
  abel

/-- **Theorem 6.14**, the limiting-normal inclusion. -/
theorem normalCone_constraints_subset
    {X : Set E} {D : Set F} (hX : IsClosed X) (hD : IsClosed D)
    {f : E → F} (hf : ContDiff ℝ 1 f) {x : E}
    (hCQ : NormalConstraintQualification X D (fderiv ℝ f x) x (f x)) :
    normalCone (X ∩ f ⁻¹' D) x ⊆
      (fderiv ℝ f x).adjoint '' normalCone D (f x) + normalCone X x := by
  intro v hv
  obtain ⟨y, hy, z, hz, heq⟩ := exists_normal_multipliers_of_mem_normalCone hX hD hf hCQ hv
  exact ⟨_, ⟨y, hy, rfl⟩, z, hz, heq.symm⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Theorem 6.31**, the unconditional tangent inclusion. -/
theorem tangentCone_constraints_subset
    {X : Set E} {D : Set F} {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f A x) :
    tangentCone (X ∩ f ⁻¹' D) x ⊆ tangentCone X x ∩ A ⁻¹' tangentCone D (f x) := by
  intro w hw
  refine ⟨tangentCone_mono inter_subset_left x hw, ?_⟩
  exact tangentCone_mono (by rintro _ ⟨z, hz, rfl⟩; exact hz.2) (f x)
    (image_tangentCone_subset hf (X ∩ f ⁻¹' D) ⟨w, hw, rfl⟩)

/-- **Theorem 6.14**, the unconditional regular-normal inclusion. -/
theorem adjoint_regularNormalCone_add_subset_constraints
    {X : Set E} {D : Set F} {f : E → F} {A : E →L[ℝ] F} {x : E}
    (hx : x ∈ X ∩ f ⁻¹' D) (hf : HasFDerivAt f A x) :
    A.adjoint '' regularNormalCone D (f x) + regularNormalCone X x ⊆
      regularNormalCone (X ∩ f ⁻¹' D) x := by
  rintro v ⟨_, ⟨y, hy, rfl⟩, z, hz, rfl⟩
  apply mem_regularNormalCone_of_forall_inner_nonpos hx
  intro w hw
  obtain ⟨hwX, hwD⟩ := tangentCone_constraints_subset hf hw
  rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  exact add_nonpos (inner_nonpos_of_mem_regularNormalCone hy hwD)
    (inner_nonpos_of_mem_regularNormalCone hz hwX)

/-- **Theorem 6.14**, regularity of the constrained set and the normal
formula when both component sets are Clarke regular. -/
theorem clarkeRegularity_constraints
    {X : Set E} {D : Set F} (hX : IsClosed X) (hD : IsClosed D)
    {f : E → F} (hf : ContDiff ℝ 1 f) {x : E} (hx : x ∈ X ∩ f ⁻¹' D)
    (hCQ : NormalConstraintQualification X D (fderiv ℝ f x) x (f x))
    (hXreg : IsClarkeRegularAt X x) (hDreg : IsClarkeRegularAt D (f x)) :
    IsClarkeRegularAt (X ∩ f ⁻¹' D) x ∧
      normalCone (X ∩ f ⁻¹' D) x =
        (fderiv ℝ f x).adjoint '' normalCone D (f x) + normalCone X x := by
  have hsub := normalCone_constraints_subset hX hD hf hCQ
  have hsup := adjoint_regularNormalCone_add_subset_constraints hx
    ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
  rw [← hXreg.2, ← hDreg.2] at hsup
  have hreg : IsClarkeRegularAt (X ∩ f ⁻¹' D) x :=
    isClarkeRegularAt_iff.2 ⟨RW.IsClosed.isLocallyClosedAt
      (hX.inter (hD.preimage hf.continuous)) x,
      hsub.trans hsup⟩
  exact ⟨hreg, Subset.antisymm hsub
    (hsup.trans (regularNormalCone_subset_normalCone _ _))⟩

end RW
