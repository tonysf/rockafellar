/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: strict differentiability

Definition 9.17 and the equivalences (a) ⇔ (b) ⇔ (c) ⇔ (f) ⇔ (g) of Theorem 9.18, with
`∂f(x̄) = {∇f(x̄)}`, `d̂f(x̄) = ⟪∇f(x̄), ·⟫` and `lip f(x̄) = |∇f(x̄)|`.

Definition 9.17 asks for `f(x') = f(x) + ⟪v, x' - x⟫ + o(|x' - x|)` as
`x, x' → x̄`.  The error term is finite, so `f` is finite on a neighborhood of
`x̄`; `HasStrictGradientAt` records this and asks for Mathlib's
`HasStrictFDerivAt` of the real representative `y ↦ (f y).toReal` with
derivative `⟪v, ·⟫`.

The proofs apply Theorem 9.13 (`ERealStrictlyContinuousAt`, the subgradient
bound for the Lipschitz modulus and its attainment) to `f - ⟪v, ·⟫`, whose
subgradients are those of `f` translated by `-v` (Exercise 8.8(c)).

Not formalized here: conditions (d) and (e) of 9.18.
-/

import RockafellarWets.Chapter9.SubgradientModulus
import RockafellarWets.Chapter9.SmoothLipschitzModulus
import RockafellarWets.Chapter8.SubgradientsAndGradients

open Filter Set Topology Metric Asymptotics
open scoped ENNReal NNReal InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Definition 9.17**: `f` is strictly differentiable at `x̄` with gradient
`v`.  It is finite around `x̄`, and `f(x') = f(x) + ⟪v, x' - x⟫ + o(|x' - x|)`
as `x, x' → x̄`. -/
def HasStrictGradientAt (f : E → EReal) (v x : E) : Prop :=
  (∀ᶠ y in 𝓝 x, f y = ((f y).toReal : EReal)) ∧
    HasStrictFDerivAt (fun y ↦ (f y).toReal) (innerSL ℝ v) x

/-- **Definition 9.17**: `f` is strictly differentiable at `x̄`. -/
def StrictlyDifferentiableAt (f : E → EReal) (x : E) : Prop := ∃ v, HasStrictGradientAt f v x

/-- A real function whose Lipschitz modulus at `x` vanishes has strict
derivative `0` there. -/
theorem hasStrictFDerivAt_zero_of_lipschitzModulus_eq_zero {φ : E → ℝ} {x : E}
    (h : lipschitzModulus φ x = 0) : HasStrictFDerivAt φ (0 : E →L[ℝ] ℝ) x := by
  refine HasStrictFDerivAt.of_isLittleO (IsLittleO.of_bound fun ε hε ↦ ?_)
  obtain ⟨U, hU, hL⟩ := exists_lipschitzOnWith_of_modulus_lt (f := φ) (x := x)
    (k := ⟨ε, hε.le⟩) (by rw [h]; exact ENNReal.coe_pos.2 (NNReal.coe_pos.1 hε))
  filter_upwards [prod_mem_nhds hU hU] with p hp
  simp only [ContinuousLinearMap.zero_apply, sub_zero]
  have h1 := hL.dist_le_mul p.1 hp.1 p.2 hp.2
  rw [dist_eq_norm, dist_eq_norm] at h1
  exact h1

/-- **Theorem 9.18**, (a) ⇒ strict continuity. -/
theorem HasStrictGradientAt.eRealStrictlyContinuousAt {f : E → EReal} {v x : E}
    (h : HasStrictGradientAt f v x) : ERealStrictlyContinuousAt f x :=
  ⟨h.1, strictlyContinuousAt_iff.2 h.2.exists_lipschitzOnWith⟩

/-- **Theorem 9.18**: `lip f(x̄) = |∇f(x̄)|`. -/
theorem HasStrictGradientAt.lipschitzModulus_eq {f : E → EReal} {v x : E}
    (h : HasStrictGradientAt f v x) :
    lipschitzModulus (fun y ↦ (f y).toReal) x = (‖v‖₊ : ℝ≥0∞) := by
  rw [lipschitzModulus_eq_of_hasStrictFDerivAt h.2]
  congr 1
  ext
  simp

private theorem hasGradientAt_inner_const [CompleteSpace E] (u x : E) :
    HasGradientAt (fun y : E ↦ ⟪u, y⟫_ℝ) u x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (innerSL ℝ u).hasFDerivAt (x := x) using 1

private theorem contDiffAt_inner_const (u x : E) : ContDiffAt ℝ 1 (fun y : E ↦ ⟪u, y⟫_ℝ) x := by
  have h := ((innerSL ℝ u).contDiff (n := 1)).contDiffAt (x := x)
  convert h using 1

/-- Exercise 8.8(c) for the linear perturbation `-⟪v, ·⟫`. -/
private theorem subdifferential_add_inner_neg [CompleteSpace E] {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c)
    (v : E) :
    subdifferential (fun y ↦ f y + ((⟪-v, y⟫_ℝ : ℝ) : EReal)) x =
      (fun u ↦ u + -v) '' subdifferential f x := by
  have h := (subdifferentials_add_smooth hxc (contDiffAt_inner_const (-v) x)).2.1
  rwa [(hasGradientAt_inner_const (-v) x).gradient] at h

private theorem toReal_add_inner {f : E → EReal} {y : E} (hy : f y = ((f y).toReal : EReal))
    (u : E) :
    f y + ((⟪u, y⟫_ℝ : ℝ) : EReal) = (((f y).toReal + ⟪u, y⟫_ℝ : ℝ) : EReal) := by
  rw [hy, ← EReal.coe_add, EReal.toReal_coe]

/-- **Theorem 9.18**, (a) ⇒ (b) with the gradient formula: `∂f(x̄) = {∇f(x̄)}`. -/
theorem HasStrictGradientAt.subdifferential_eq [FiniteDimensional ℝ E] {f : E → EReal}
    {v x : E} (h : HasStrictGradientAt f v x) : subdifferential f x = {v} := by
  have hsc := h.eRealStrictlyContinuousAt
  have hxc : f x = ((f x).toReal : EReal) := hsc.finite
  set g : E → EReal := fun y ↦ f y + ((⟪-v, y⟫_ℝ : ℝ) : EReal) with hg_def
  have hgfin : ∀ᶠ y in 𝓝 x, g y = ((g y).toReal : EReal) := h.1.mono fun y hy ↦ by
    simp only [hg_def]
    rw [toReal_add_inner hy, EReal.toReal_coe]
  have hgreal : (fun y ↦ (f y).toReal + innerSL ℝ (-v) y) =ᶠ[𝓝 x] fun y ↦ (g y).toReal :=
    h.1.mono fun y hy ↦ by
      simp only [hg_def, innerSL_apply_apply]
      rw [toReal_add_inner hy, EReal.toReal_coe]
  have hgstrict : HasStrictFDerivAt (fun y ↦ (g y).toReal) (0 : E →L[ℝ] ℝ) x := by
    have h1 := h.2.add (innerSL ℝ (-v)).hasStrictFDerivAt
    have h2 : innerSL ℝ v + innerSL ℝ (-v) = (0 : E →L[ℝ] ℝ) := by
      ext y
      simp
    rw [h2] at h1
    exact h1.congr_of_eventuallyEq hgreal
  have hg : ERealStrictlyContinuousAt g x :=
    ⟨hgfin, strictlyContinuousAt_iff.2 hgstrict.exists_lipschitzOnWith⟩
  have hmod : lipschitzModulus (fun y ↦ (g y).toReal) x = 0 := by
    rw [lipschitzModulus_eq_of_hasStrictFDerivAt hgstrict]
    simp
  have hsub : subdifferential g x ⊆ {0} := fun w hw ↦ by
    have h1 := hg.nnnorm_le_modulus_of_mem_subdifferential hw
    rw [hmod, nonpos_iff_eq_zero, ENNReal.coe_eq_zero, nnnorm_eq_zero] at h1
    exact h1
  have htrans : subdifferential g x = (fun u ↦ u + -v) '' subdifferential f x :=
    subdifferential_add_inner_neg hxc v
  have hshift : ∀ u ∈ subdifferential f x, u = v := fun u hu ↦ by
    have h1 : u + -v ∈ subdifferential g x := by
      rw [htrans]
      exact ⟨u, hu, rfl⟩
    have h0 := hsub h1
    rwa [mem_singleton_iff, add_neg_eq_zero] at h0
  obtain ⟨u₀, hu₀⟩ := hsc.subdifferential_nonempty_compact.1
  refine Subset.antisymm (fun u hu ↦ hshift u hu) (singleton_subset_iff.2 ?_)
  rw [← hshift u₀ hu₀]
  exact hu₀

/-- **Theorem 9.18**, (b) ⇒ (a): a strictly continuous `f` with `∂f(x̄) = {v}`
is strictly differentiable at `x̄` with `∇f(x̄) = v`. -/
theorem hasStrictGradientAt_of_subdifferential_eq [FiniteDimensional ℝ E] {f : E → EReal}
    {v x : E} (hsc : ERealStrictlyContinuousAt f x) (hv : subdifferential f x = {v}) :
    HasStrictGradientAt f v x := by
  have hxc : f x = ((f x).toReal : EReal) := hsc.finite
  set g : E → EReal := fun y ↦ f y + ((⟪-v, y⟫_ℝ : ℝ) : EReal) with hg_def
  have hgfin : ∀ᶠ y in 𝓝 x, g y = ((g y).toReal : EReal) := hsc.1.mono fun y hy ↦ by
    simp only [hg_def]
    rw [toReal_add_inner hy, EReal.toReal_coe]
  obtain ⟨W, hW, hWeq⟩ := hsc.1.exists_mem
  have hgW : ∀ y ∈ W, (g y).toReal = (f y).toReal + innerSL ℝ (-v) y := fun y hy ↦ by
    simp only [hg_def, innerSL_apply_apply]
    rw [toReal_add_inner (hWeq y hy), EReal.toReal_coe]
  have hg : ERealStrictlyContinuousAt g x := by
    refine ⟨hgfin, strictlyContinuousAt_iff.2 ?_⟩
    obtain ⟨k, U, hU, hL⟩ := strictlyContinuousAt_iff.1 hsc.2
    have hsum := hL.add (innerSL ℝ (-v)).lipschitz.lipschitzOnWith
    refine ⟨k + ‖innerSL ℝ (-v)‖₊, U ∩ W, inter_mem hU hW, fun y hy z hz ↦ ?_⟩
    show edist (g y).toReal (g z).toReal ≤ _
    rw [hgW y hy.2, hgW z hz.2]
    exact hsum hy.1 hz.1
  have htrans : subdifferential g x = (fun u ↦ u + -v) '' subdifferential f x :=
    subdifferential_add_inner_neg hxc v
  have hg0 : subdifferential g x = {0} := by
    rw [htrans, hv, image_singleton, add_neg_cancel]
  obtain ⟨w, hw, hmod, -⟩ := hg.exists_subgradient_norm_eq_modulus
  rw [hg0, mem_singleton_iff] at hw
  rw [hw, nnnorm_zero, ENNReal.coe_zero] at hmod
  have hgstrict := hasStrictFDerivAt_zero_of_lipschitzModulus_eq_zero hmod
  have hfreal : (fun y ↦ (g y).toReal + innerSL ℝ v y) =ᶠ[𝓝 x] fun y ↦ (f y).toReal :=
    Filter.mem_of_superset hW fun y hy ↦ by
      show (g y).toReal + innerSL ℝ v y = (f y).toReal
      rw [hgW y hy, innerSL_apply_apply, innerSL_apply_apply, inner_neg_left]
      ring
  have h1 := hgstrict.add (innerSL ℝ v).hasStrictFDerivAt
  rw [zero_add] at h1
  exact ⟨hsc.1, h1.congr_of_eventuallyEq hfreal⟩

/-- **Theorem 9.18**: `d̂f(x̄) = ⟪∇f(x̄), ·⟫`. -/
theorem HasStrictGradientAt.regularSubderivative_eq [FiniteDimensional ℝ E] {f : E → EReal}
    {v x : E} (h : HasStrictGradientAt f v x) (w : E) :
    regularSubderivative f x w = (⟪v, w⟫_ℝ : EReal) := by
  rw [h.eRealStrictlyContinuousAt.regularSubderivative_eq_supportFunction, h.subdifferential_eq,
    supportFunction_singleton]

/-- **Theorem 9.18**, (f) ⇒ (b): if `f` is locally lsc at `x̄` and `d̂f(x̄)` is the
linear function `⟪v, ·⟫`, then `f` is strictly continuous at `x̄` and
`∂f(x̄) ⊆ {v}`. -/
theorem eRealStrictlyContinuousAt_of_regularSubderivative_eq_inner [FiniteDimensional ℝ E]
    {f : E → EReal} {x v : E} {c : ℝ} (hxc : f x = c) (hl : IsLocallyLscAt f x)
    (hlin : ∀ w, regularSubderivative f x w = (⟪v, w⟫_ℝ : EReal)) :
    ERealStrictlyContinuousAt f x ∧ subdifferential f x ⊆ {v} := by
  have hsc : ERealStrictlyContinuousAt f x :=
    (eRealStrictlyContinuousAt_iff_regularSubderivative_finite hxc hl).2 fun w ↦ ⟨_, hlin w⟩
  refine ⟨hsc, fun u hu ↦ ?_⟩
  have h1 := inner_le_supportFunction hu (u - v)
  rw [← hsc.regularSubderivative_eq_supportFunction (u - v), hlin (u - v),
    EReal.coe_le_coe_iff] at h1
  have h2 : ⟪u - v, u - v⟫_ℝ ≤ 0 := by
    rw [inner_sub_left]
    linarith
  have h3 : u - v = 0 := inner_self_eq_zero.1 (le_antisymm h2 real_inner_self_nonneg)
  exact mem_singleton_iff.2 (sub_eq_zero.1 h3)

/-- **Theorem 9.18**, (g) ⇒ (f): if `f` is locally lsc at `x̄` and
`d̂f(x̄)(-w) = -d̂f(x̄)(w)` for all `w`, then `d̂f(x̄)` is linear. -/
theorem exists_regularSubderivative_eq_inner_of_odd [FiniteDimensional ℝ E] {f : E → EReal}
    {x : E} {c : ℝ} (hxc : f x = c) (hl : IsLocallyLscAt f x)
    (hodd : ∀ w, regularSubderivative f x (-w) = -regularSubderivative f x w) :
    ∃ v, ∀ w, regularSubderivative f x w = (⟪v, w⟫_ℝ : EReal) := by
  have hph := positivelyHomogeneous_regularSubderivative hxc
  have hlsc := lowerSemicontinuous_regularSubderivative f x
  have h0 : regularSubderivative f x 0 = 0 := by
    have h1 := hodd 0
    rw [neg_zero] at h1
    rcases hph.zero_eq_zero_or_bot with h00 | h00
    · exact h00
    · rw [h00, EReal.neg_bot] at h1
      exact absurd h1 (by simp)
  -- no value `⊥`: it would propagate along the ray and contradict lsc at `0`
  have hnbot : ∀ w, regularSubderivative f x w ≠ ⊥ := by
    intro w hw
    have hlt : ((-1 : ℝ) : EReal) < regularSubderivative f x 0 := by
      rw [h0, ← EReal.coe_zero]
      exact EReal.coe_lt_coe_iff.2 (by norm_num)
    have hev := hlsc 0 _ hlt
    have hto : Tendsto (fun t : ℝ ↦ t • w) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ ↦ t • w) (𝓝 0) (𝓝 ((0 : ℝ) • w)) :=
        (continuous_id.smul continuous_const).tendsto 0
      rw [zero_smul] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    obtain ⟨t, ht1, ht2⟩ := ((hto.eventually hev).and self_mem_nhdsWithin).exists
    rw [hph.2 ht2, hw, EReal.coe_mul_bot_of_pos ht2] at ht1
    exact not_lt_bot ht1
  have hntop : ∀ w, regularSubderivative f x w ≠ ⊤ := fun w hw ↦
    hnbot (-w) (by rw [hodd, hw, EReal.neg_top])
  obtain ⟨L, hL⟩ : ∃ L : E → ℝ, ∀ w, regularSubderivative f x w = (L w : EReal) :=
    ⟨fun w ↦ (regularSubderivative f x w).toReal,
      fun w ↦ (EReal.coe_toReal (hntop w) (hnbot w)).symm⟩
  have hsub : ∀ u w, L (u + w) ≤ L u + L w := fun u w ↦ by
    have h1 := regularSubderivative_subadditive hxc hl.lowerSemicontinuousAt u w
    rw [infAddition_eq_add_of_ne_bot (hnbot u) (hnbot w), hL (u + w), hL u, hL w,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    exact h1
  have hneg : ∀ w, L (-w) = -L w := fun w ↦ by
    have h1 := hodd w
    rw [hL (-w), hL w, ← EReal.coe_neg, EReal.coe_eq_coe_iff] at h1
    exact h1
  have hadd : ∀ u w, L (u + w) = L u + L w := fun u w ↦ by
    have h1 := hsub u w
    have h2 := hsub (-u) (-w)
    rw [← neg_add, hneg, hneg u, hneg w] at h2
    linarith
  have hL0 : L 0 = 0 := by
    have h1 := hL 0
    rw [h0] at h1
    exact (EReal.coe_eq_zero.1 h1.symm)
  have hsmul : ∀ (t : ℝ) w, L (t • w) = t * L w := by
    intro t w
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · have h1 := hph.2 (x := w) (neg_pos.2 ht)
      rw [hL ((-t) • w), hL w, ← EReal.coe_mul, EReal.coe_eq_coe_iff, neg_smul, hneg] at h1
      linarith
    · rw [zero_smul, zero_mul, hL0]
    · have h1 := hph.2 (x := w) ht
      rw [hL (t • w), hL w, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at h1
      exact h1
  let Lin : E →ₗ[ℝ] ℝ :=
    { toFun := L
      map_add' := hadd
      map_smul' := fun t w ↦ by rw [hsmul, smul_eq_mul, RingHom.id_apply] }
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap Lin),
    fun w ↦ ?_⟩
  rw [InnerProductSpace.toDual_symm_apply, hL w]
  rfl

/-- **Theorem 9.18**, (a) ⇔ (b) ⇔ (c) ⇔ (f) ⇔ (g), for `f` finite at `x̄`:
(a) `f` is strictly differentiable at `x̄`;
(b) `f` is strictly continuous at `x̄` and has at most one subgradient there;
(c) `f` is locally lsc at `x̄`, `∂f(x̄)` is a singleton, and `∂^∞f(x̄) = {0}`;
(f) `f` is locally lsc at `x̄`, and `d̂f(x̄)` is linear, written in the Riesz
form `d̂f(x̄) = ⟪v, ·⟫`;
(g) `f` is locally lsc at `x̄`, and `d̂f(x̄)(-w) = -d̂f(x̄)(w)` for all `w`. -/
theorem tfae_strictlyDifferentiableAt [FiniteDimensional ℝ E] {f : E → EReal} {x : E} {c : ℝ}
    (hxc : f x = c) :
    List.TFAE [StrictlyDifferentiableAt f x,
      ERealStrictlyContinuousAt f x ∧ (subdifferential f x).Subsingleton,
      IsLocallyLscAt f x ∧ (∃ v, subdifferential f x = {v}) ∧
        horizonSubdifferential f x = {0},
      IsLocallyLscAt f x ∧ ∃ v, ∀ w, regularSubderivative f x w = (⟪v, w⟫_ℝ : EReal),
      IsLocallyLscAt f x ∧
        ∀ w, regularSubderivative f x (-w) = -regularSubderivative f x w] := by
  tfae_have 1 → 2 := fun ⟨_, h⟩ ↦
    ⟨h.eRealStrictlyContinuousAt, by rw [h.subdifferential_eq]; exact subsingleton_singleton⟩
  tfae_have 2 → 3 := fun ⟨hsc, hss⟩ ↦ by
    obtain ⟨⟨u, hu⟩, -⟩ := hsc.subdifferential_nonempty_compact
    exact ⟨hsc.isLocallyLscAt, ⟨u, hss.eq_singleton_of_mem hu⟩,
      (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero hxc hsc.isLocallyLscAt).1 hsc⟩
  tfae_have 3 → 1 := fun ⟨hl, ⟨v, hv⟩, hh⟩ ↦
    ⟨v, hasStrictGradientAt_of_subdifferential_eq
      ((eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero hxc hl).2 hh) hv⟩
  tfae_have 1 → 4 := fun ⟨v, h⟩ ↦
    ⟨h.eRealStrictlyContinuousAt.isLocallyLscAt, v, h.regularSubderivative_eq⟩
  tfae_have 4 → 2 := fun ⟨hl, v, hlin⟩ ↦ by
    obtain ⟨hsc, hsub⟩ := eRealStrictlyContinuousAt_of_regularSubderivative_eq_inner hxc hl hlin
    exact ⟨hsc, subsingleton_singleton.anti hsub⟩
  tfae_have 1 → 5 := fun ⟨v, h⟩ ↦ ⟨h.eRealStrictlyContinuousAt.isLocallyLscAt, fun w ↦ by
    rw [h.regularSubderivative_eq, h.regularSubderivative_eq, inner_neg_right, EReal.coe_neg]⟩
  tfae_have 5 → 4 := fun ⟨hl, hodd⟩ ↦ ⟨hl, exists_regularSubderivative_eq_inner_of_odd hxc hl hodd⟩
  tfae_finish

end RW
