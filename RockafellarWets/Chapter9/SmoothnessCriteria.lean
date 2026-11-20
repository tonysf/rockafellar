/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: strict differentiability, smoothness and gradient continuity

* **Theorem 9.18**, conditions (d) and (e), with all seven conditions in
  `tfae_strictlyDifferentiableAt_all` and `df(x̄) = ⟪∇f(x̄), ·⟫`
  (`HasStrictGradientAt.subderivative_eq`).  Both (d) and (e) reduce to
  `IsSubdifferentiallyRegularAt.hasStrictGradientAt_of_subderivative_le`: at a
  regular point a linear majorant `df(x̄) ≤ ⟪g, ·⟫` forces `∂^∞f(x̄) = {0}`
  (8.30), hence strict continuity (9.13), and `∂f(x̄) = {g}`.
* **Corollary 9.19** (`tfae_contDiffOn`): on an open set where `f` is finite,
  strict differentiability, `C¹`, strict continuity plus regularity with
  single-valued `∂f`, and lsc with `∂f` locally bounded and single-valued where
  nonempty are equivalent.
* **Corollary 9.20**: a regular function is strictly differentiable wherever it
  is differentiable, and its gradient is continuous relative to that set.
* **Corollary 9.21**: for `f` strictly continuous and regular on an open set,
  `∂̂(-f)(x̄)` is `{-∇f(x̄)}` or `∅` according as `f` is differentiable at `x̄`,
  `-∂(-f)(x̄)` consists of the limits of gradients at nearby points of
  differentiability, and `-∂(-f)(x̄) ⊆ ∂f(x̄)`.

The convex special cases mentioned after 9.20 and in 9.21 are not stated here.
-/

import RockafellarWets.Chapter9.StrictDifferentiability
import RockafellarWets.Chapter9.RegularStrictContinuity
import RockafellarWets.Chapter8.RegularSubgradientBridge
import RockafellarWets.Chapter8.SubderivativeFormulas

open Filter Set Topology Metric Asymptotics
open scoped ENNReal NNReal InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem toReal_neg_ereal (a : EReal) : (-a).toReal = -a.toReal := by
  induction a using EReal.rec with
  | bot => simp
  | coe r => rw [← EReal.coe_neg, EReal.toReal_coe, EReal.toReal_coe]
  | top => simp

/-! ### Theorem 9.18 (d) and (e) -/

/-- Strict differentiability of `f` with gradient `v` gives that of `-f` with `-v`. -/
theorem HasStrictGradientAt.neg {f : E → EReal} {v x : E} (h : HasStrictGradientAt f v x) :
    HasStrictGradientAt (fun y ↦ -f y) (-v) x := by
  refine ⟨h.1.mono fun y hy ↦ ?_, ?_⟩
  · show -f y = ((-f y).toReal : EReal)
    rw [hy, ← EReal.coe_neg, EReal.toReal_coe]
  · have e : (fun y ↦ (-f y).toReal) = fun y ↦ -(f y).toReal :=
      funext fun y ↦ toReal_neg_ereal (f y)
    rw [e, show innerSL ℝ (-v) = -innerSL ℝ v from map_neg (innerSL ℝ) v]
    exact h.2.neg

/-- A strict gradient is a regular subgradient (8.8(a)). -/
theorem HasStrictGradientAt.mem_regularSubdifferential {f : E → EReal} {v x : E}
    (h : HasStrictGradientAt f v x) : v ∈ regularSubdifferential f x := by
  refine ⟨(f x).toReal, h.eRealStrictlyContinuousAt.finite, fun ε hε ↦ ?_⟩
  have ho := (HasFDerivAtFilter.isLittleO h.2.hasFDerivAt).def hε
  filter_upwards [ho, h.1] with y hy hfy
  rw [hfy, EReal.coe_le_coe_iff]
  rw [innerSL_apply_apply, Real.norm_eq_abs] at hy
  linarith [neg_abs_le ((f y).toReal - (f x).toReal - ⟪v, y - x⟫_ℝ)]

/-- **Theorem 9.18**: `df(x̄) = ⟪∇f(x̄), ·⟫`. -/
theorem HasStrictGradientAt.subderivative_eq [FiniteDimensional ℝ E] {f : E → EReal}
    {v x : E} (h : HasStrictGradientAt f v x) (w : E) :
    subderivative f x w = (⟪v, w⟫_ℝ : EReal) := by
  refine le_antisymm ?_
    (inner_le_subderivative_of_mem_regularSubdifferential h.mem_regularSubdifferential w)
  rw [← h.regularSubderivative_eq w]
  exact subderivative_le_regularSubderivative h.eRealStrictlyContinuousAt.finite w

/-- **Theorem 9.18**, (a) ⇒ regularity of `f`. -/
theorem HasStrictGradientAt.isSubdifferentiallyRegularAt [FiniteDimensional ℝ E]
    {f : E → EReal} {v x : E} (h : HasStrictGradientAt f v x) :
    IsSubdifferentiallyRegularAt f x :=
  isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.2
    ⟨h.eRealStrictlyContinuousAt.isLocallyLscAt,
      funext fun w ↦ (h.subderivative_eq w).trans (h.regularSubderivative_eq w).symm⟩

omit [InnerProductSpace ℝ E] in
/-- Strict continuity at `x̄` gives continuity of `f` at all nearby points. -/
theorem ERealStrictlyContinuousAt.eventually_continuousAt {f : E → EReal} {x : E}
    (h : ERealStrictlyContinuousAt f x) : ∀ᶠ y in 𝓝 x, ContinuousAt f y := by
  obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.2
  obtain ⟨U, hU, hUo, hfin, hL⟩ := h.exists_lipschitzOnWith hk
  filter_upwards [hU] with y hy
  have h1 : ContinuousAt (fun z ↦ (f z).toReal) y :=
    hL.continuousOn.continuousAt (hUo.mem_nhds hy)
  have h2 : (fun z ↦ ((f z).toReal : EReal)) =ᶠ[𝓝 y] f :=
    Filter.mem_of_superset (hUo.mem_nhds hy) fun z hz ↦ (hfin z hz).symm
  exact (continuous_coe_real_ereal.continuousAt.comp h1).congr h2

/-- **Theorem 9.18**, (a) ⇒ (d). -/
theorem HasStrictGradientAt.regular_neg_regular [FiniteDimensional ℝ E] {f : E → EReal}
    {v x : E} (h : HasStrictGradientAt f v x) :
    (∀ᶠ y in 𝓝 x, ContinuousAt f y) ∧ IsSubdifferentiallyRegularAt f x ∧
      IsSubdifferentiallyRegularAt (fun y ↦ -f y) x ∧ (regularSubdifferential f x).Nonempty ∧
      (regularSubdifferential (fun y ↦ -f y) x).Nonempty :=
  ⟨h.eRealStrictlyContinuousAt.eventually_continuousAt, h.isSubdifferentiallyRegularAt,
    h.neg.isSubdifferentiallyRegularAt, ⟨v, h.mem_regularSubdifferential⟩,
    ⟨-v, h.neg.mem_regularSubdifferential⟩⟩

/-- An upper expansion `f(y) ≤ f(x̄) + ⟪g, y - x̄⟫ + ε|y - x̄|` near `x̄` for every
`ε > 0` bounds `df(x̄)` above by `⟪g, ·⟫`. -/
theorem subderivative_le_inner_of_upper_expansion {f : E → EReal} {x g : E} {c : ℝ}
    (hxc : f x = c)
    (hup : ∀ ε > 0, ∀ᶠ y in 𝓝 x, f y ≤ ((c + ⟪g, y - x⟫_ℝ + ε * ‖y - x‖ : ℝ) : EReal))
    (w : E) : subderivative f x w ≤ (⟪g, w⟫_ℝ : EReal) := by
  have hmono : subderivative f x w ≤
      liminf (fun τ : ℝ ↦ differenceQuotient f x τ w) (𝓝[>] 0) := by
    unfold subderivative
    have h1 : (fun τ : ℝ ↦ differenceQuotient f x τ w) =
        (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2) ∘ fun τ ↦ (τ, w) := rfl
    rw [h1, liminf_comp]
    exact liminf_le_liminf_of_le (tendsto_pair_const w)
  have hpath : Tendsto (fun τ : ℝ ↦ x + τ • w) (𝓝[>] 0) (𝓝 x) := by
    have h1 : Tendsto (fun τ : ℝ ↦ x + τ • w) (𝓝 0) (𝓝 (x + (0 : ℝ) • w)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hbound : ∀ ε > 0, liminf (fun τ : ℝ ↦ differenceQuotient f x τ w) (𝓝[>] 0) ≤
      ((⟪g, w⟫_ℝ + ε * ‖w‖ : ℝ) : EReal) := by
    intro ε hε
    refine le_trans liminf_le_limsup (limsup_le_of_le (by isBoundedDefault) ?_)
    filter_upwards [hpath.eventually (hup ε hε), self_mem_nhdsWithin] with τ hτ hpos
    have hpos' : (0 : ℝ) < τ := hpos
    rw [differenceQuotient_le_coe_iff hxc hpos']
    rw [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_of_nonneg hpos'.le] at hτ
    refine hτ.trans (le_of_eq ?_)
    congr 1
    ring
  refine hmono.trans ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨a, ha1, ha2⟩ := EReal.exists_between_coe_real hlt
  have ha : ⟪g, w⟫_ℝ < a := EReal.coe_lt_coe_iff.1 ha1
  have hw1 : (0 : ℝ) < ‖w‖ + 1 := by positivity
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = (a - ⟪g, w⟫_ℝ) / (‖w‖ + 1) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hε_def]; exact div_pos (sub_pos.2 ha) hw1
  have h3 : ⟪g, w⟫_ℝ + ε * ‖w‖ < a := by
    have h4 : ε * (‖w‖ + 1) = a - ⟪g, w⟫_ℝ := by rw [hε_def]; exact div_mul_cancel₀ _ hw1.ne'
    nlinarith
  exact absurd (lt_of_lt_of_le ha2 ((hbound ε hε).trans (EReal.coe_le_coe_iff.2 h3.le)))
    (lt_irrefl _)

/-- At a regular point, a linear upper bound `df(x̄) ≤ ⟪g, ·⟫` forces strict
differentiability with `∇f(x̄) = g`. -/
theorem IsSubdifferentiallyRegularAt.hasStrictGradientAt_of_subderivative_le
    [FiniteDimensional ℝ E] {f : E → EReal} {x g : E} (hreg : IsSubdifferentiallyRegularAt f x)
    (hle : ∀ w, subderivative f x w ≤ (⟪g, w⟫_ℝ : EReal)) : HasStrictGradientAt f g x := by
  have hl := hreg.isLocallyLscAt
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hl.2.1 hl.1).symm
  have hdom : effectiveDomain (subderivative f x) = univ :=
    eq_univ_of_forall fun w ↦ lt_of_le_of_lt (hle w) (EReal.coe_lt_top _)
  have h0 : horizonSubdifferential f x = {0} := by
    rw [hreg.horizonSubdifferential_eq_polar_domain, hdom]
    ext v
    constructor
    · intro hv
      have h1 : ⟪v, v⟫_ℝ ≤ 0 := hv v (mem_univ v)
      exact mem_singleton_iff.2 (real_inner_self_nonpos.1 h1)
    · intro hv
      rw [mem_singleton_iff.1 hv]
      intro w _
      simp
  have hsc := (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero hxc hl).2 h0
  have hsub : subdifferential f x ⊆ {g} := by
    intro v hv
    rw [hreg.subdifferential_eq_linearMinorantSet] at hv
    have h1 := (hv (v - g)).trans (hle (v - g))
    rw [EReal.coe_le_coe_iff] at h1
    have h2 : ⟪v - g, v - g⟫_ℝ ≤ 0 := by
      rw [inner_sub_left]
      linarith
    exact mem_singleton_iff.2 (sub_eq_zero.1 (real_inner_self_nonpos.1 h2))
  obtain ⟨⟨u, hu⟩, -⟩ := hsc.subdifferential_nonempty_compact
  have hug : u = g := hsub hu
  exact hasStrictGradientAt_of_subdifferential_eq hsc
    (Subset.antisymm hsub (singleton_subset_iff.2 (hug ▸ hu)))

/-- A regular subgradient `u` of `-f` at `x̄` is an upper expansion of `f` with `-u`. -/
theorem upper_expansion_of_mem_regularSubdifferential_neg {f : E → EReal} {x u : E}
    (hu : u ∈ regularSubdifferential (fun y ↦ -f y) x) :
    ∃ c : ℝ, f x = c ∧ ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      f y ≤ ((c + ⟪-u, y - x⟫_ℝ + ε * ‖y - x‖ : ℝ) : EReal) := by
  obtain ⟨c', hc', hev⟩ := hu
  refine ⟨-c', ?_, fun ε hε ↦ (hev ε hε).mono fun y hy ↦ ?_⟩
  · have h1 : -f x = (c' : EReal) := hc'
    rw [EReal.coe_neg, ← h1, neg_neg]
  · have h1 := EReal.le_neg_of_le_neg hy
    rw [← EReal.coe_neg] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    rw [inner_neg_left]
    ring

/-- A differentiable majorant touching `f` at `x̄` is an upper expansion of `f`. -/
theorem upper_expansion_of_le_differentiable [CompleteSpace E] {f : E → EReal} {x : E}
    {k : E → ℝ} (hle : ∀ᶠ y in 𝓝 x, f y ≤ (k y : EReal)) (hd : DifferentiableAt ℝ k x) :
    ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      f y ≤ ((k x + ⟪gradient k x, y - x⟫_ℝ + ε * ‖y - x‖ : ℝ) : EReal) := by
  intro ε hε
  have ho := (HasFDerivAtFilter.isLittleO
    (hasGradientAt_iff_hasFDerivAt.1 hd.hasGradientAt)).def hε
  filter_upwards [ho, hle] with y hy hfy
  refine hfy.trans (EReal.coe_le_coe_iff.2 ?_)
  have e : ‖k y - k x - ⟪gradient k x, y - x⟫_ℝ‖ ≤ ε * ‖y - x‖ := hy
  rw [Real.norm_eq_abs] at e
  linarith [le_abs_self (k y - k x - ⟪gradient k x, y - x⟫_ℝ)]

/-- **Theorem 9.18**, (d) ⇒ (a). -/
theorem hasStrictGradientAt_of_regular_of_mem_regularSubdifferential_neg [FiniteDimensional ℝ E]
    {f : E → EReal} {x u : E} (hreg : IsSubdifferentiallyRegularAt f x)
    (hu : u ∈ regularSubdifferential (fun y ↦ -f y) x) : HasStrictGradientAt f (-u) x := by
  obtain ⟨c, hxc, hup⟩ := upper_expansion_of_mem_regularSubdifferential_neg hu
  exact hreg.hasStrictGradientAt_of_subderivative_le
    (subderivative_le_inner_of_upper_expansion hxc hup)

/-- **Theorem 9.18**, (e) ⇒ (a). -/
theorem hasStrictGradientAt_of_regular_of_le_differentiable [FiniteDimensional ℝ E]
    {f : E → EReal} {x : E} {k : E → ℝ} (hreg : IsSubdifferentiallyRegularAt f x)
    (hle : ∀ᶠ y in 𝓝 x, f y ≤ (k y : EReal)) (hx : f x = (k x : EReal))
    (hd : DifferentiableAt ℝ k x) : HasStrictGradientAt f (gradient k x) x :=
  hreg.hasStrictGradientAt_of_subderivative_le
    (subderivative_le_inner_of_upper_expansion hx (upper_expansion_of_le_differentiable hle hd))

/-- **Theorem 9.18**, (a) ⇒ (e). -/
theorem HasStrictGradientAt.exists_differentiable_majorant [FiniteDimensional ℝ E]
    {f : E → EReal} {v x : E} (h : HasStrictGradientAt f v x) :
    IsSubdifferentiallyRegularAt f x ∧ ∃ k : E → ℝ, (∀ᶠ y in 𝓝 x, f y ≤ (k y : EReal)) ∧
      f x = (k x : EReal) ∧ DifferentiableAt ℝ k x :=
  ⟨h.isSubdifferentiallyRegularAt, fun y ↦ (f y).toReal, h.1.mono fun _ hy ↦ hy.le,
    h.eRealStrictlyContinuousAt.finite, h.2.hasFDerivAt.differentiableAt⟩

/-- **Theorem 9.18**, all seven conditions, for `f` finite at `x̄`:
(a) `f` is strictly differentiable at `x̄`;
(b) `f` is strictly continuous at `x̄` and has at most one subgradient there;
(c) `f` is locally lsc at `x̄`, `∂f(x̄)` is a singleton and `∂^∞f(x̄) = {0}`;
(d) `f` is continuous around `x̄`, `f` and `-f` are regular at `x̄`, and
`∂̂f(x̄)`, `∂̂(-f)(x̄)` are nonempty;
(e) `f` is regular at `x̄`, and near `x̄` some `h ≥ f` with `h(x̄) = f(x̄)` is
differentiable at `x̄`;
(f) `f` is locally lsc at `x̄` and `d̂f(x̄)` is linear (Riesz form `⟪v, ·⟫`);
(g) `f` is locally lsc at `x̄` and `d̂f(x̄)(-w) = -d̂f(x̄)(w)` for all `w`. -/
theorem tfae_strictlyDifferentiableAt_all [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    {c : ℝ} (hxc : f x = c) :
    List.TFAE [StrictlyDifferentiableAt f x,
      ERealStrictlyContinuousAt f x ∧ (subdifferential f x).Subsingleton,
      IsLocallyLscAt f x ∧ (∃ v, subdifferential f x = {v}) ∧
        horizonSubdifferential f x = {0},
      (∀ᶠ y in 𝓝 x, ContinuousAt f y) ∧ IsSubdifferentiallyRegularAt f x ∧
        IsSubdifferentiallyRegularAt (fun y ↦ -f y) x ∧ (regularSubdifferential f x).Nonempty ∧
        (regularSubdifferential (fun y ↦ -f y) x).Nonempty,
      IsSubdifferentiallyRegularAt f x ∧ ∃ k : E → ℝ, (∀ᶠ y in 𝓝 x, f y ≤ (k y : EReal)) ∧
        f x = (k x : EReal) ∧ DifferentiableAt ℝ k x,
      IsLocallyLscAt f x ∧ ∃ v, ∀ w, regularSubderivative f x w = (⟪v, w⟫_ℝ : EReal),
      IsLocallyLscAt f x ∧
        ∀ w, regularSubderivative f x (-w) = -regularSubderivative f x w] := by
  have hold := tfae_strictlyDifferentiableAt hxc
  tfae_have 1 ↔ 2 := hold.out 0 1
  tfae_have 1 ↔ 3 := hold.out 0 2
  tfae_have 1 ↔ 6 := hold.out 0 3
  tfae_have 1 ↔ 7 := hold.out 0 4
  tfae_have 1 → 4 := fun ⟨_, h⟩ ↦ h.regular_neg_regular
  tfae_have 4 → 1 := fun ⟨_, hreg, _, _, ⟨u, hu⟩⟩ ↦
    ⟨-u, hasStrictGradientAt_of_regular_of_mem_regularSubdifferential_neg hreg hu⟩
  tfae_have 1 → 5 := fun ⟨_, h⟩ ↦ h.exists_differentiable_majorant
  tfae_have 5 → 1 := fun ⟨hreg, k, hle, hx, hd⟩ ↦
    ⟨_, hasStrictGradientAt_of_regular_of_le_differentiable hreg hle hx hd⟩
  tfae_finish

/-! ### Corollary 9.19 -/

omit [InnerProductSpace ℝ E] in
/-- Lower semicontinuity on an open set gives local lower semicontinuity at its points
of finiteness. -/
theorem isLocallyLscAt_of_lowerSemicontinuousOn {f : E → EReal} {O : Set E} (hO : IsOpen O)
    (hl : LowerSemicontinuousOn f O) {x : E} (hx : x ∈ O) (h1 : f x ≠ ⊥) (h2 : f x ≠ ⊤) :
    IsLocallyLscAt f x := by
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO x hx
  refine ⟨h1, h2, ε / 2, half_pos hε, fun α _ ↦ ?_⟩
  have hK : closedBall x (ε / 2) ⊆ O := (closedBall_subset_ball (half_lt_self hε)).trans hεO
  obtain ⟨v, hv, heq⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 (hl.mono hK) (α : EReal)
  have h3 : closedBall x (ε / 2) ∩ {y | f y ≤ α} = closedBall x (ε / 2) ∩ v := heq
  rw [h3]
  exact isClosed_closedBall.inter hv

/-- The gradient of the real representative is the strict gradient. -/
theorem HasStrictGradientAt.gradient_eq [CompleteSpace E] {f : E → EReal} {v x : E}
    (h : HasStrictGradientAt f v x) : gradient (fun y ↦ (f y).toReal) x = v :=
  HasGradientAt.gradient (hasGradientAt_iff_hasFDerivAt.2 h.2.hasFDerivAt)

/-- Subgradient selections converge at a point of strict continuity where the
limiting subdifferential is a singleton (osc and local boundedness of `∂f`). -/
theorem tendsto_of_eventually_mem_subdifferential [FiniteDimensional ℝ E] {f : E → EReal}
    {x v : E} (hsc : ERealStrictlyContinuousAt f x) (hv : subdifferential f x = {v})
    {l : Filter E} (hl : l ≤ 𝓝 x) {G : E → E} (hG : ∀ᶠ y in l, G y ∈ subdifferential f y) :
    Tendsto G l (𝓝 v) := by
  obtain ⟨V, hV, hbdd⟩ := hsc.locallyBoundedAt_subdifferential
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
  refine (isCompact_closedBall (0 : E) R).tendsto_nhds_of_unique_mapClusterPt ?_ ?_
  · filter_upwards [hl hV, hG] with y hy hGy
    exact hR (mem_svImage.2 ⟨y, hy, hGy⟩)
  · intro z _ hz
    have hmem : z ∈ svOuterLimit (subdifferential f) x := by
      intro W hW
      have h1 : ∃ᶠ y in l, G y ∈ W := hz.frequently hW
      have h2 : ∃ᶠ y in l, (subdifferential f y ∩ W).Nonempty :=
        (h1.and_eventually hG).mono fun y hy ↦ ⟨G y, hy.2, hy.1⟩
      exact h2.filter_mono hl
    have h3 := svOscAt_subdifferential_of_eRealStrictlyContinuousAt hsc hmem
    rwa [hv, mem_singleton_iff] at h3

/-- **Corollary 9.19**: for `f` finite on an open set `O`, the following are
equivalent: (a) `f` is strictly differentiable on `O`; (b) `f` is `C¹` on `O`;
(c) `f` is strictly continuous and regular on `O` with `∂f` single-valued;
(d) `f` is lsc on `O`, `∂f` is locally bounded on `O`, and `∂f` is single-valued
where it is nonempty-valued in `O`. -/
theorem tfae_contDiffOn [FiniteDimensional ℝ E] {f : E → EReal} {O : Set E} (hO : IsOpen O)
    (hfin : ∀ x ∈ O, f x ≠ ⊥ ∧ f x ≠ ⊤) :
    List.TFAE [∀ x ∈ O, StrictlyDifferentiableAt f x,
      ContDiffOn ℝ 1 (fun y ↦ (f y).toReal) O,
      ∀ x ∈ O, ERealStrictlyContinuousAt f x ∧ IsSubdifferentiallyRegularAt f x ∧
        ∃ v, subdifferential f x = {v},
      LowerSemicontinuousOn f O ∧ (∀ x ∈ O, SvLocallyBoundedAt (subdifferential f) x) ∧
        ∀ x ∈ O, (subdifferential f x).Subsingleton] := by
  have hxc : ∀ x ∈ O, f x = (((f x).toReal : ℝ) : EReal) := fun x hx ↦
    (EReal.coe_toReal (hfin x hx).2 (hfin x hx).1).symm
  tfae_have 1 → 3 := fun ha x hx ↦ by
    obtain ⟨v, h⟩ := ha x hx
    exact ⟨h.eRealStrictlyContinuousAt, h.isSubdifferentiallyRegularAt, v, h.subdifferential_eq⟩
  tfae_have 3 → 1 := fun hc x hx ↦ by
    obtain ⟨hsc, -, v, hv⟩ := hc x hx
    exact ⟨v, hasStrictGradientAt_of_subdifferential_eq hsc hv⟩
  tfae_have 1 → 2 := fun ha ↦ by
    have hgrad : ∀ y ∈ O, HasStrictGradientAt f (gradient (fun z ↦ (f z).toReal) y) y :=
      fun y hy ↦ by
        obtain ⟨v, h⟩ := ha y hy
        rwa [h.gradient_eq]
    have hcont : ContinuousOn (fun y ↦ gradient (fun z ↦ (f z).toReal) y) O := by
      intro y hy
      refine tendsto_of_eventually_mem_subdifferential (hgrad y hy).eRealStrictlyContinuousAt
        (hgrad y hy).subdifferential_eq nhdsWithin_le_nhds ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [(hgrad z hz).subdifferential_eq]
      exact mem_singleton _
    intro x hx
    refine ContDiffAt.contDiffWithinAt (contDiffAt_one_iff.2
      ⟨fun y ↦ innerSL ℝ (gradient (fun z ↦ (f z).toReal) y), O, hO.mem_nhds hx,
        (innerSL ℝ).continuous.comp_continuousOn hcont, fun y hy ↦ (hgrad y hy).2.hasFDerivAt⟩)
  tfae_have 2 → 1 := fun hb x hx ↦ by
    have hcd : ContDiffAt ℝ 1 (fun y ↦ (f y).toReal) x := hb.contDiffAt (hO.mem_nhds hx)
    have hs := hcd.hasStrictFDerivAt one_ne_zero
    have e : innerSL ℝ ((InnerProductSpace.toDual ℝ E).symm
        (fderiv ℝ (fun y ↦ (f y).toReal) x)) = fderiv ℝ (fun y ↦ (f y).toReal) x := by
      ext w
      rw [innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]
    refine ⟨(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y ↦ (f y).toReal) x), ?_⟩
    refine ⟨Filter.mem_of_superset (hO.mem_nhds hx) fun y hy ↦ hxc y hy, ?_⟩
    rw [e]
    exact hs
  tfae_have 3 → 4 := fun hc ↦
    ⟨fun x hx ↦ (hc x hx).1.continuousAt.lowerSemicontinuousAt.lowerSemicontinuousWithinAt O,
      fun x hx ↦ (hc x hx).1.locallyBoundedAt_subdifferential, fun x hx ↦ by
        obtain ⟨-, -, v, hv⟩ := hc x hx
        rw [hv]
        exact subsingleton_singleton⟩
  tfae_have 4 → 1 := fun ⟨hlsc, hlb, hss⟩ x hx ↦ by
    have hl := isLocallyLscAt_of_lowerSemicontinuousOn hO hlsc hx (hfin x hx).1 (hfin x hx).2
    have hsc := (eRealStrictlyContinuousAt_iff_locallyBoundedAt_subdifferential (hxc x hx) hl).2
      (hlb x hx)
    have h2 : ERealStrictlyContinuousAt f x ∧ (subdifferential f x).Subsingleton :=
      ⟨hsc, hss x hx⟩
    exact ((tfae_strictlyDifferentiableAt (hxc x hx)).out 1 0).1 h2
  tfae_finish

/-! ### Corollary 9.20 -/

/-- **Corollary 9.20**: at a point where `f` is regular and finite nearby, differentiability
of `f` implies strict differentiability. -/
theorem IsSubdifferentiallyRegularAt.hasStrictGradientAt_of_differentiableAt
    [FiniteDimensional ℝ E] {f : E → EReal} {x : E} (hreg : IsSubdifferentiallyRegularAt f x)
    (hfin : ∀ᶠ y in 𝓝 x, f y = ((f y).toReal : EReal))
    (hd : DifferentiableAt ℝ (fun y ↦ (f y).toReal) x) :
    HasStrictGradientAt f (gradient (fun y ↦ (f y).toReal) x) x :=
  hasStrictGradientAt_of_regular_of_le_differentiable hreg (hfin.mono fun _ hy ↦ hy.le)
    hfin.self_of_nhds hd

/-- **Corollary 9.20**, in the differentiability sense of 7(16): a regular function is
strictly differentiable wherever it is differentiable. -/
theorem IsSubdifferentiallyRegularAt.strictlyDifferentiableAt_of_erealDifferentiableAt
    [FiniteDimensional ℝ E] {f : E → EReal} {x : E} (hreg : IsSubdifferentiallyRegularAt f x)
    (hd : ERealDifferentiableAt f x) : StrictlyDifferentiableAt f x := by
  obtain ⟨L, hx1, hx2, hnear, ho⟩ := hd
  have hfin : ∀ᶠ y in 𝓝 x, f y = ((f y).toReal : EReal) :=
    hnear.mono fun y hy ↦ (EReal.coe_toReal hy.2 hy.1).symm
  have hfd : HasFDerivAt (fun y ↦ (f y).toReal) L x := HasFDerivAtFilter.of_isLittleO ho
  have hdiff : DifferentiableAt ℝ (fun y ↦ (f y).toReal) x := hfd.differentiableAt
  exact ⟨_, hreg.hasStrictGradientAt_of_differentiableAt hfin hdiff⟩

/-- **Corollary 9.20**: relative to the set of points of an open set `O` where a regular
`f` is differentiable, the gradient mapping is continuous. -/
theorem continuousOn_gradient_of_regular [FiniteDimensional ℝ E] {f : E → EReal} {O : Set E}
    (hreg : ∀ x ∈ O, IsSubdifferentiallyRegularAt f x) :
    ContinuousOn (fun x ↦ gradient (fun y ↦ (f y).toReal) x)
      {x | x ∈ O ∧ ERealDifferentiableAt f x} := by
  have hgrad : ∀ x ∈ {x | x ∈ O ∧ ERealDifferentiableAt f x},
      HasStrictGradientAt f (gradient (fun y ↦ (f y).toReal) x) x := by
    rintro x ⟨hx, hd⟩
    obtain ⟨v, h⟩ := (hreg x hx).strictlyDifferentiableAt_of_erealDifferentiableAt hd
    rwa [h.gradient_eq]
  intro x hx
  refine tendsto_of_eventually_mem_subdifferential (hgrad x hx).eRealStrictlyContinuousAt
    (hgrad x hx).subdifferential_eq nhdsWithin_le_nhds ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [(hgrad z hz).subdifferential_eq]
  exact mem_singleton _

/-! ### Corollary 9.21 -/

open Classical in
/-- **Corollary 9.21**: for `f` strictly continuous and regular at `x̄`,
`∂̂(-f)(x̄) = {-∇f(x̄)}` if `f` is differentiable at `x̄`, and `∅` otherwise. -/
theorem regularSubdifferential_neg_eq [FiniteDimensional ℝ E] {f : E → EReal} {x : E}
    (hsc : ERealStrictlyContinuousAt f x) (hreg : IsSubdifferentiallyRegularAt f x) :
    regularSubdifferential (fun y ↦ -f y) x =
      if DifferentiableAt ℝ (fun y ↦ (f y).toReal) x then
        {-gradient (fun y ↦ (f y).toReal) x} else ∅ := by
  have hsub : ∀ u ∈ regularSubdifferential (fun y ↦ -f y) x,
      DifferentiableAt ℝ (fun y ↦ (f y).toReal) x ∧ u = -gradient (fun y ↦ (f y).toReal) x := by
    intro u hu
    have h := hasStrictGradientAt_of_regular_of_mem_regularSubdifferential_neg hreg hu
    refine ⟨h.2.hasFDerivAt.differentiableAt, ?_⟩
    rw [h.gradient_eq, neg_neg]
  split_ifs with hd
  · refine Subset.antisymm (fun u hu ↦ mem_singleton_iff.2 (hsub u hu).2)
      (singleton_subset_iff.2 ?_)
    exact (hreg.hasStrictGradientAt_of_differentiableAt hsc.1 hd).neg.mem_regularSubdifferential
  · exact eq_empty_of_forall_notMem fun u hu ↦ hd (hsub u hu).1

omit [InnerProductSpace ℝ E] in
/-- Negation preserves strict continuity. -/
theorem ERealStrictlyContinuousAt.neg {f : E → EReal} {x : E}
    (h : ERealStrictlyContinuousAt f x) : ERealStrictlyContinuousAt (fun y ↦ -f y) x := by
  refine ⟨h.1.mono fun y hy ↦ ?_, ?_⟩
  · show -f y = ((-f y).toReal : EReal)
    rw [hy, ← EReal.coe_neg, EReal.toReal_coe]
  · obtain ⟨k, U, hU, hL⟩ := strictlyContinuousAt_iff.1 h.2
    refine strictlyContinuousAt_iff.2 ⟨k, U, hU, ?_⟩
    have e : (fun y ↦ (-f y).toReal) = fun y ↦ -(f y).toReal :=
      funext fun y ↦ toReal_neg_ereal (f y)
    rw [e]
    intro y hy z hz
    rw [edist_neg_neg]
    exact hL hy hz

/-- **Corollary 9.21**: for `f` strictly continuous and regular on an open set `O` and
`x̄ ∈ O`, `-∂(-f)(x̄)` is the set of limits of gradients `∇f(xν)` at points `xν → x̄`
where `f` is differentiable. -/
theorem neg_subdifferential_neg_eq [FiniteDimensional ℝ E] {f : E → EReal} {O : Set E}
    (hO : IsOpen O)
    (h : ∀ x ∈ O, ERealStrictlyContinuousAt f x ∧ IsSubdifferentiallyRegularAt f x) {x : E}
    (hx : x ∈ O) :
    -subdifferential (fun y ↦ -f y) x =
      {v | ∃ xs : ℕ → E, Tendsto xs atTop (𝓝 x) ∧
        (∀ n, DifferentiableAt ℝ (fun y ↦ (f y).toReal) (xs n)) ∧
        Tendsto (fun n ↦ gradient (fun y ↦ (f y).toReal) (xs n)) atTop (𝓝 v)} := by
  have hcont : ContinuousAt (fun y ↦ -f y) x := (h x hx).1.neg.continuousAt
  have hfx : ∃ c : ℝ, (fun y ↦ -f y) x = c :=
    ⟨_, (h x hx).1.neg.finite⟩
  ext v
  rw [Set.mem_neg, mem_subdifferential_iff_exists_seq]
  constructor
  · rintro ⟨-, xs, vs, hxs, -, hvs, hlim⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hxs.eventually (hO.mem_nhds hx))
    have hpt : ∀ n, DifferentiableAt ℝ (fun y ↦ (f y).toReal) (xs (n + N)) ∧
        vs (n + N) = -gradient (fun y ↦ (f y).toReal) (xs (n + N)) := by
      intro n
      have hmem := hvs (n + N)
      have hO' := hN (n + N) (Nat.le_add_left N n)
      rw [regularSubdifferential_neg_eq (h _ hO').1 (h _ hO').2] at hmem
      split_ifs at hmem with hd
      · exact ⟨hd, mem_singleton_iff.1 hmem⟩
      · exact absurd hmem (notMem_empty _)
    refine ⟨fun n ↦ xs (n + N), hxs.comp (tendsto_add_atTop_nat N), fun n ↦ (hpt n).1, ?_⟩
    have h1 : Tendsto (fun n ↦ -vs (n + N)) atTop (𝓝 (- -v)) :=
      (hlim.comp (tendsto_add_atTop_nat N)).neg
    rw [neg_neg] at h1
    refine h1.congr fun n ↦ ?_
    rw [(hpt n).2, neg_neg]
  · rintro ⟨xs, hxs, hd, hlim⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hxs.eventually (hO.mem_nhds hx))
    refine ⟨hfx, fun n ↦ xs (n + N), fun n ↦ -gradient (fun y ↦ (f y).toReal) (xs (n + N)),
      hxs.comp (tendsto_add_atTop_nat N),
      (hcont.tendsto.comp (hxs.comp (tendsto_add_atTop_nat N))), fun n ↦ ?_,
      (hlim.comp (tendsto_add_atTop_nat N)).neg⟩
    have hO' := hN (n + N) (Nat.le_add_left N n)
    rw [regularSubdifferential_neg_eq (h _ hO').1 (h _ hO').2, if_pos (hd (n + N))]
    exact mem_singleton _

/-- **Corollary 9.21**: `-∂(-f)(x̄) ⊆ ∂f(x̄)`. -/
theorem neg_subdifferential_neg_subset [FiniteDimensional ℝ E] {f : E → EReal} {O : Set E}
    (hO : IsOpen O)
    (h : ∀ x ∈ O, ERealStrictlyContinuousAt f x ∧ IsSubdifferentiallyRegularAt f x) {x : E}
    (hx : x ∈ O) : -subdifferential (fun y ↦ -f y) x ⊆ subdifferential f x := by
  rw [neg_subdifferential_neg_eq hO h hx]
  rintro v ⟨xs, hxs, hd, hlim⟩
  have hosc := svOscAt_subdifferential_of_eRealStrictlyContinuousAt (h x hx).1
  apply hosc
  intro W hW
  rw [Filter.frequently_iff]
  intro A hA
  obtain ⟨n, hnA, hnW, hnO⟩ :=
    ((hxs.eventually hA).and ((hlim.eventually hW).and (hxs.eventually (hO.mem_nhds hx)))).exists
  refine ⟨xs n, hnA, gradient (fun y ↦ (f y).toReal) (xs n), ?_, hnW⟩
  have hs := (h _ hnO).2.hasStrictGradientAt_of_differentiableAt (h _ hnO).1.1 (hd n)
  rw [hs.subdifferential_eq]
  exact mem_singleton _

end RW
