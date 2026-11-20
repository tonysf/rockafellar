/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Subgradients of Lipschitzian sums
-/

import RockafellarWets.Chapter10.SumSubgradients
import RockafellarWets.Chapter9.HilbertLipschitzExtension
import RockafellarWets.Chapter9.StrictDifferentiability

open Filter Set Topology
open scoped NNReal Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f g : E → EReal} {x : E} {c : ℝ}

/-- A strictly continuous extended-real function agrees near its finite
base point with a globally Lipschitz real function. -/
theorem ERealStrictlyContinuousAt.exists_lipschitz_representative
    (hf : ERealStrictlyContinuousAt f x) :
    ∃ (F : E → ℝ) (k : ℝ≥0), LipschitzWith k F ∧ f =ᶠ[𝓝 x] (fun z ↦ (F z:EReal)) := by
  obtain ⟨k,U,hU,hk⟩ := strictlyContinuousAt_iff.mp hf.2
  obtain ⟨F,hF,hEq⟩ := exists_lipschitz_extension_same_constant hk
  refine ⟨F,k,hF,?_⟩
  filter_upwards [hU,hf.1] with z hz hzf
  exact hzf.trans (congrArg (fun r : ℝ ↦ (r:EReal)) (hEq hz))

theorem eRealStrictlyContinuousAt_coe_of_lipschitz {F : E → ℝ} {k : ℝ≥0} (hF : LipschitzWith k F) :
    ERealStrictlyContinuousAt (fun z ↦ (F z:EReal)) x := by
  refine ⟨Eventually.of_forall (fun z ↦ by simp),?_⟩
  simp only [EReal.toReal_coe]
  exact strictlyContinuousAt_iff.mpr ⟨k,univ,univ_mem,hF.lipschitzOnWith⟩

private theorem global_lipschitz_sum_qual {F : E → ℝ} {k : ℝ≥0} (hF : LipschitzWith k F) :
    ∀ u ∈ horizonSubdifferential (fun z ↦ (F z:EReal)) x,
      ∀ v ∈ horizonSubdifferential g x, u+v = 0 → u = 0 ∧ v = 0 := by
  have hsc := eRealStrictlyContinuousAt_coe_of_lipschitz (x := x) hF
  have hh := (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero
    (f := fun z : E ↦ (F z:EReal)) (x := x) hsc.finite hsc.isLocallyLscAt).mp hsc
  intro u hu v _ huv
  have hu0 : u = 0 := by simpa only [hh,mem_singleton_iff] using hu
  exact ⟨hu0,by simpa only [hu0,zero_add] using huv⟩

/-- **Exercise 10.10**, the limiting-subgradient inclusion. -/
theorem subdifferential_add_subset_of_strictlyContinuous
    (hf : ERealStrictlyContinuousAt f x) (hg : LowerSemicontinuous g) (hpg : IsProper g)
    (hx : g x = c) :
    subdifferential (f+g) x ⊆ subdifferential f x+subdifferential g x := by
  obtain ⟨F,k,hF,he⟩ := hf.exists_lipschitz_representative
  have hFc : Continuous (fun z ↦ (F z:EReal)) := continuous_coe_real_ereal.comp hF.continuous
  have hpF : IsProper (fun z ↦ (F z:EReal)) := ⟨⟨x,EReal.coe_lt_top _⟩,fun z ↦ EReal.bot_lt_coe _⟩
  have hsum : f+g =ᶠ[𝓝 x] (fun z ↦ (F z:EReal)+g z) := by
    filter_upwards [he] with z hz
    exact congrArg (fun a ↦ a+g z) hz
  have hxsum : (f+g) x = (((f x).toReal+c:ℝ):EReal) :=
    (congrArg₂ (· + ·) hf.finite hx).trans (EReal.coe_add _ _).symm
  rw [subdifferential_congr_nhds_of_finite hxsum hsum,
    subdifferential_congr_nhds_of_finite hf.finite he]
  exact subdifferential_add_subset hFc.lowerSemicontinuous hg hpF hpg rfl hx (global_lipschitz_sum_qual hF)

/-- Local lower semicontinuity of the sum, needed to read its horizon
subgradients through the epigraph normal slice. -/
theorem isLocallyLscAt_add_of_strictlyContinuous
    (hf : ERealStrictlyContinuousAt f x) (hg : LowerSemicontinuous g) (hpg : IsProper g)
    (hx : g x = c) : IsLocallyLscAt (f+g) x := by
  obtain ⟨F,k,hF,he⟩ := hf.exists_lipschitz_representative
  have hFc : Continuous (fun z ↦ (F z:EReal)) := continuous_coe_real_ereal.comp hF.continuous
  have hpF : IsProper (fun z ↦ (F z:EReal)) := ⟨⟨x,EReal.coe_lt_top _⟩,fun z ↦ EReal.bot_lt_coe _⟩
  have hl : LowerSemicontinuous (fun z ↦ (F z:EReal)+g z) := by
    exact (lowerSemicontinuous_separableSum hFc.lowerSemicontinuous hg hpF hpg).comp
      (diagonalEmbedding (E := E)).continuous
  have hxsum : (F x:EReal)+g x = ((F x+c:ℝ):EReal) := by rw [hx,EReal.coe_add]
  apply (locallyLscAt_of_lowerSemicontinuous_finite hl hxsum).congr_nhds
  filter_upwards [he] with z hz
  exact congrArg (fun a ↦ a+g z) hz.symm

/-- **Exercise 10.10**, the horizon-subgradient inclusion. -/
theorem horizonSubdifferential_add_subset_of_strictlyContinuous
    (hf : ERealStrictlyContinuousAt f x) (hg : LowerSemicontinuous g) (hpg : IsProper g)
    (hx : g x = c) : horizonSubdifferential (f+g) x ⊆ horizonSubdifferential g x := by
  obtain ⟨F,k,hF,he⟩ := hf.exists_lipschitz_representative
  have hFc : Continuous (fun z ↦ (F z:EReal)) := continuous_coe_real_ereal.comp hF.continuous
  have hpF : IsProper (fun z ↦ (F z:EReal)) := ⟨⟨x,EReal.coe_lt_top _⟩,fun z ↦ EReal.bot_lt_coe _⟩
  have hsc := eRealStrictlyContinuousAt_coe_of_lipschitz (x := x) hF
  have hsum : f+g =ᶠ[𝓝 x] (fun z ↦ (F z:EReal)+g z) := by
    filter_upwards [he] with z hz
    exact congrArg (fun a ↦ a+g z) hz
  have hxsum : (f+g) x = (((f x).toReal+c:ℝ):EReal) :=
    (congrArg₂ (· + ·) hf.finite hx).trans (EReal.coe_add _ _).symm
  rw [horizonSubdifferential_congr_nhds_of_locallyLsc hxsum
    (isLocallyLscAt_add_of_strictlyContinuous hf hg hpg hx)
    (isLocallyLscAt_add_of_strictlyContinuous hsc hg hpg hx) hsum]
  have hh := horizonSubdifferential_add_subset hFc.lowerSemicontinuous hg hpF hpg rfl hx (global_lipschitz_sum_qual hF)
  have hzero := (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero
    (f := fun z : E ↦ (F z:EReal)) (x := x) hsc.finite hsc.isLocallyLscAt).mp hsc
  intro v hv
  obtain ⟨u,hu,z,hz,heq⟩ := hh hv
  have hu0 : u = 0 := by simpa only [hzero,mem_singleton_iff] using hu
  have hez : z = v := by simpa only [hu0,zero_add] using heq
  exact hez ▸ hz

/-- Strict gradients depend only on the germ of the function. -/
theorem HasStrictGradientAt.congr_nhds {v : E} (hf : HasStrictGradientAt f v x)
    (he : f =ᶠ[𝓝 x] g) : HasStrictGradientAt g v x := by
  refine ⟨?_,hf.2.congr_of_eventuallyEq ?_⟩
  · filter_upwards [hf.1,he] with z hz hez
    simpa only [hez] using hz
  · filter_upwards [he] with z hz
    exact congrArg EReal.toReal hz

private theorem strict_gradient_lipschitz_sum {F : E → ℝ} {k : ℝ≥0} {v : E}
    (hF : LipschitzWith k F) (hv : HasStrictGradientAt (fun z ↦ (F z:EReal)) v x)
    (hg : LowerSemicontinuous g) (hpg : IsProper g) (hx : g x = c) :
    subdifferential ((fun z ↦ (F z:EReal))+g) x = {v}+subdifferential g x ∧
    horizonSubdifferential ((fun z ↦ (F z:EReal))+g) x = horizonSubdifferential g x := by
  let H : E → EReal := (fun z ↦ (F z:EReal))+g
  let N : E → EReal := fun z ↦ (-F z:EReal)
  have hpF : IsProper (fun z ↦ (F z:EReal)) := ⟨⟨x,EReal.coe_lt_top _⟩,fun z ↦ EReal.bot_lt_coe _⟩
  have hFc : Continuous (fun z ↦ (F z:EReal)) := continuous_coe_real_ereal.comp hF.continuous
  have hlH : LowerSemicontinuous H :=
    (lowerSemicontinuous_separableSum hFc.lowerSemicontinuous hg hpF hpg).comp
      (diagonalEmbedding (E := E)).continuous
  have hxH : H x = ((F x+c:ℝ):EReal) := by change (F x:EReal)+g x = _; rw [hx,EReal.coe_add]
  have hpH : IsProper H := ⟨⟨x,hxH ▸ EReal.coe_lt_top _⟩,
    fun z ↦ EReal.bot_lt_add_iff.mpr ⟨EReal.bot_lt_coe _,hpg.2 z⟩⟩
  have hvN : HasStrictGradientAt N (-v) x := by
    refine ⟨Eventually.of_forall (fun z ↦ by simp [N]),?_⟩
    simpa only [N,EReal.toReal_coe,map_neg] using hv.2.neg
  have he : N+H = g := by
    funext z
    change ((-F z:ℝ):EReal)+((F z:EReal)+g z) = g z
    rw [← add_assoc,← EReal.coe_add,neg_add_cancel,EReal.coe_zero,zero_add]
  constructor
  · apply Subset.antisymm
    · simpa only [hv.subdifferential_eq] using
        subdifferential_add_subset_of_strictlyContinuous hv.eRealStrictlyContinuousAt hg hpg hx
    · rintro w ⟨a,ha,b,hb,rfl⟩
      have ha0 : a = v := ha
      obtain ⟨a',ha',z,hz,hez⟩ := subdifferential_add_subset_of_strictlyContinuous
        hvN.eRealStrictlyContinuousAt hlH hpH hxH (he.symm ▸ hb)
      have ha'0 : a' = -v := by simpa only [hvN.subdifferential_eq,mem_singleton_iff] using ha'
      have hw : a+b = z := by rw [ha0,← hez,ha'0]; simp
      change a+b ∈ subdifferential H x
      rw [hw]
      exact hz
  · apply Subset.antisymm
    · exact horizonSubdifferential_add_subset_of_strictlyContinuous hv.eRealStrictlyContinuousAt hg hpg hx
    · intro w hw
      exact horizonSubdifferential_add_subset_of_strictlyContinuous
        hvN.eRealStrictlyContinuousAt hlH hpH hxH (he.symm ▸ hw)

/-- **Exercise 10.10**, equality in the sum rule when the first summand is
strictly differentiable. -/
theorem HasStrictGradientAt.subdifferential_add {v : E} (hf : HasStrictGradientAt f v x)
    (hg : LowerSemicontinuous g) (hpg : IsProper g) (hx : g x = c) :
    subdifferential (f+g) x = {v}+subdifferential g x := by
  obtain ⟨F,k,hF,he⟩ := hf.eRealStrictlyContinuousAt.exists_lipschitz_representative
  have hs : f+g =ᶠ[𝓝 x] ((fun z ↦ (F z:EReal))+g) := by
    filter_upwards [he] with z hz
    exact congrArg (fun a ↦ a+g z) hz
  have hxsum : (f+g) x = (((f x).toReal+c:ℝ):EReal) :=
    (congrArg₂ (· + ·) hf.eRealStrictlyContinuousAt.finite hx).trans (EReal.coe_add _ _).symm
  rw [subdifferential_congr_nhds_of_finite hxsum hs]
  exact (strict_gradient_lipschitz_sum hF (hf.congr_nhds he) hg hpg hx).1

/-- **Exercise 10.10**, a strictly differentiable summand leaves horizon
subgradients unchanged. -/
theorem HasStrictGradientAt.horizonSubdifferential_add {v : E} (hf : HasStrictGradientAt f v x)
    (hg : LowerSemicontinuous g) (hpg : IsProper g) (hx : g x = c) :
    horizonSubdifferential (f+g) x = horizonSubdifferential g x := by
  obtain ⟨F,k,hF,he⟩ := hf.eRealStrictlyContinuousAt.exists_lipschitz_representative
  have hs : f+g =ᶠ[𝓝 x] ((fun z ↦ (F z:EReal))+g) := by
    filter_upwards [he] with z hz
    exact congrArg (fun a ↦ a+g z) hz
  have hxsum : (f+g) x = (((f x).toReal+c:ℝ):EReal) :=
    (congrArg₂ (· + ·) hf.eRealStrictlyContinuousAt.finite hx).trans (EReal.coe_add _ _).symm
  rw [horizonSubdifferential_congr_nhds_of_locallyLsc hxsum
    (isLocallyLscAt_add_of_strictlyContinuous hf.eRealStrictlyContinuousAt hg hpg hx)
    (isLocallyLscAt_add_of_strictlyContinuous (eRealStrictlyContinuousAt_coe_of_lipschitz hF) hg hpg hx) hs]
  exact (strict_gradient_lipschitz_sum hF (hf.congr_nhds he) hg hpg hx).2

end RW
