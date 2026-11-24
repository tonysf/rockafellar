/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second subderivatives

Section 13B: the second-order difference quotients 13(4) and 13(5), the
second subderivatives of Definition 13.3, positive homogeneity of degree `p`
(Definition 13.4), Proposition 13.5, and the twice semidifferentiable and
twice epi-differentiable functions of Definition 13.6.

As in Chapter 7, the limits are taken along the joint filter "`τ ↓ 0` and
`w' → w`", that is `𝓝[>] 0 ×ˢ 𝓝 w`, and division by `τ²/2` is multiplication
by the real number `2/τ²`.  The quotient 13(4) uses the inf-addition
convention `∞ - ∞ = ∞` of the book through `infAddition`.

**Correction to Proposition 13.5.**  The book asserts that `d²f(x̄)` is
positively homogeneous of degree 2, which by Definition 13.4 includes
`d²f(x̄)(0) < ∞`.  That can fail when `df(x̄)(0) = -∞`: for `f(x) = -√|x|` on
`ℝ` one has `df(0) ≡ -∞`, every quotient `Δ²_τ f(0)(w)` equals `∞`, and so
`d²f(0) ≡ ∞` (`secondSubderivativeAt_negSqrtAbs`).  The scaling law
`d²f(x̄)(λw) = λ² d²f(x̄)(w)` and lower semicontinuity hold in general, and
`d²f(x̄)(0) < ∞` holds when `df(x̄)(0) ≠ -∞`, that is, when `df(x̄)(0) = 0`
(`isPosHomogeneousOfDegree_two_secondSubderivativeAt`).  This condition is
sufficient but not necessary: for `f(x) = -√(-x)` on `x < 0` and `f = 0` on
`x ≥ 0`, `df(0)(0) = -∞`, yet `d²f(0)` is positively homogeneous of degree 2
(`isPosHomogeneousOfDegree_two_secondSubderivativeAt_negSqrtNegPart`).  The
function `d²f(x̄ | v)` is positively homogeneous of degree 2 without
restriction.
-/

import RockafellarWets.Chapter7.EpiDerivatives
import RockafellarWets.Chapter7.EpigraphAddition
import RockafellarWets.Chapter8.RegularSubgradientBridge
import RockafellarWets.Chapter8.SubderivativeRelationships
import RockafellarWets.Chapter6.NormalCones

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

/-! ### Lower limits over `l ×ˢ 𝓝 w` -/

section LowerLimits

variable {ι E : Type*} [TopologicalSpace E]

/-- A lower limit over `l ×ˢ 𝓝 w` is lower semicontinuous in `w`. -/
theorem lowerSemicontinuous_liminf_prod (l : Filter ι) (g : ι → E → EReal) :
    LowerSemicontinuous fun w ↦ liminf (fun p : ι × E ↦ g p.1 p.2) (l ×ˢ 𝓝 w) := by
  intro w α hα
  obtain ⟨β, hαβ, hβ⟩ := exists_between hα
  have hev : ∀ᶠ p in l ×ˢ 𝓝 w, β < g p.1 p.2 := eventually_lt_of_lt_liminf hβ
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hev
  obtain ⟨V', hV'V, hV'o, hwV'⟩ := mem_nhds_iff.1 hV
  filter_upwards [hV'o.mem_nhds hwV'] with w' hw'
  refine hαβ.trans_le (le_liminf_of_le (h := ?_))
  exact mem_of_superset (prod_mem_prod hU (hV'o.mem_nhds hw')) fun p hp ↦
    le_of_lt (show β < g p.1 p.2 from hUV ⟨hp.1, hV'V hp.2⟩)

/-- The epigraph of a lower limit over `l ×ˢ 𝓝 w` is the outer limit of the
epigraphs along `l`: the lower limit is the lower epi-limit. -/
theorem mem_outerSetLimitAlong_epigraph_iff_liminf {l : Filter ι} (g : ι → E → EReal)
    (w : E) (α : ℝ) :
    (w, α) ∈ outerSetLimitAlong l (fun i ↦ epigraph (g i)) ↔
      liminf (fun p : ι × E ↦ g p.1 p.2) (l ×ˢ 𝓝 w) ≤ α := by
  constructor
  · intro hmem
    by_contra hlt
    push_neg at hlt
    obtain ⟨b, hαb, hb⟩ := EReal.exists_between_coe_real hlt
    have hev : ∀ᶠ p in l ×ˢ 𝓝 w, (b : EReal) < g p.1 p.2 := eventually_lt_of_lt_liminf hb
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hev
    have hN : V ×ˢ Iio b ∈ 𝓝 (w, α) :=
      prod_mem_nhds hV (Iio_mem_nhds (EReal.coe_lt_coe_iff.1 hαb))
    obtain ⟨i, ⟨⟨w', β⟩, hep, hw'V, hβ⟩, hiU⟩ := ((hmem _ hN).and_eventually hU).exists
    have h1 : (b : EReal) < g i w' := hUV (show (i, w') ∈ U ×ˢ V from ⟨hiU, hw'V⟩)
    have h2 : g i w' ≤ (β : EReal) := hep
    have h3 : (β : EReal) < (b : EReal) := EReal.coe_lt_coe_iff.2 hβ
    exact lt_irrefl _ (h1.trans_le (h2.trans h3.le))
  · intro hle N hN
    obtain ⟨V, hV, I, hI, hVI⟩ := mem_nhds_prod_iff.1 hN
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hI
    have hα' : α + ε / 2 ∈ I := hball (by
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
      linarith)
    have hfreq : ∃ᶠ p in l ×ˢ 𝓝 w, g p.1 p.2 < ((α + ε / 2 : ℝ) : EReal) :=
      frequently_lt_of_liminf_lt (h := hle.trans_lt (EReal.coe_lt_coe_iff.2 (by linarith)))
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨p, hp, hpUV⟩ := (hfreq.and_eventually (prod_mem_prod hU hV)).exists
    exact ⟨p.1, hpUV.1, (p.2, α + ε / 2), le_of_lt hp, hVI ⟨hpUV.2, hα'⟩⟩

/-- The lower limit over `l ×ˢ 𝓝 w` is the lower epi-limit along `l`. -/
theorem epigraph_liminf_prod (l : Filter ι) (g : ι → E → EReal) :
    epigraph (fun w ↦ liminf (fun p : ι × E ↦ g p.1 p.2) (l ×ˢ 𝓝 w)) =
      outerSetLimitAlong l (fun i ↦ epigraph (g i)) := by
  ext ⟨w, α⟩
  rw [mem_epigraph_iff, mem_outerSetLimitAlong_epigraph_iff_liminf]

end LowerLimits

/-! ### Multiplication by a positive real on `EReal` -/

/-- Every extended real is `⊥`, `⊤`, or a real number. -/
theorem ereal_trichotomy (a : EReal) : a = ⊥ ∨ a = ⊤ ∨ ∃ r : ℝ, a = r := by
  induction a with
  | bot => exact Or.inl rfl
  | coe r => exact Or.inr (Or.inr ⟨r, rfl⟩)
  | top => exact Or.inr (Or.inl rfl)

theorem EReal.coe_mul_liminf_of_pos {ι : Type*} {F : Filter ι} [F.NeBot] (u : ι → EReal) {c : ℝ}
    (hc : 0 < c) : (c : EReal) * liminf u F = liminf (fun i ↦ (c : EReal) * u i) F := by
  have hmono : Monotone fun a : EReal ↦ (c : EReal) * a := fun a b hab ↦
    mul_le_mul_of_nonneg_left hab (by exact_mod_cast hc.le)
  have hcont : ContinuousAt (fun a : EReal ↦ (c : EReal) * a) (liminf u F) := by
    have hc0 : (c : EReal) ≠ 0 := by exact_mod_cast hc.ne'
    exact (EReal.continuousAt_mul (p := ((c : EReal), liminf u F)) (Or.inl hc0) (Or.inl hc0)
      (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))).comp
      (continuousAt_const.prodMk continuousAt_id)
  exact hmono.map_liminf_of_continuousAt u hcont

/-! ### Second-order difference quotients -/

section Quotients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Formula 13(5): the second-order difference quotient
`Δ²_τ f(x̄ | v)(w) = [f(x̄ + τw) - f(x̄) - τ⟪v, w⟫] / (½τ²)`. -/
noncomputable def secondDifferenceQuotient (f : E → EReal) (x v : E) (τ : ℝ) (w : E) : EReal :=
  ((2 / τ ^ 2 : ℝ) : EReal) * (f (x + τ • w) - f x - ((τ * ⟪v, w⟫_ℝ : ℝ) : EReal))

/-- Formula 13(4): the second-order difference quotient
`Δ²_τ f(x̄)(w) = [f(x̄ + τw) - f(x̄) - τ df(x̄)(w)] / (½τ²)`, the difference being
taken in the inf-addition convention, so that the quotient is `∞` when
`f(x̄ + τw) = df(x̄)(w) = ∞` or `-∞`. -/
noncomputable def secondDifferenceQuotientAt (f : E → EReal) (x : E) (τ : ℝ) (w : E) : EReal :=
  ((2 / τ ^ 2 : ℝ) : EReal) *
    infAddition (f (x + τ • w) - f x) (-((τ : EReal) * subderivative f x w))

/-- **Definition 13.3**, formula 13(6): the second subderivative
`d²f(x̄ | v)(w) = liminf_{τ ↓ 0, w' → w} Δ²_τ f(x̄ | v)(w')`. -/
noncomputable def secondSubderivative (f : E → EReal) (x v w : E) : EReal :=
  liminf (fun p : ℝ × E ↦ secondDifferenceQuotient f x v p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)

/-- **Definition 13.3**, formula 13(7): the second subderivative without
mention of `v`, `d²f(x̄)(w) = liminf_{τ ↓ 0, w' → w} Δ²_τ f(x̄)(w')`. -/
noncomputable def secondSubderivativeAt (f : E → EReal) (x w : E) : EReal :=
  liminf (fun p : ℝ × E ↦ secondDifferenceQuotientAt f x p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)

theorem secondDifferenceQuotient_of_coe {f : E → EReal} {x v w : E} {τ c r : ℝ}
    (hx : f x = c) (hr : f (x + τ • w) = r) :
    secondDifferenceQuotient f x v τ w = ((2 / τ ^ 2 * (r - c - τ * ⟪v, w⟫_ℝ) : ℝ) : EReal) := by
  rw [secondDifferenceQuotient, hx, hr, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul]

theorem secondDifferenceQuotient_of_top {f : E → EReal} {x v w : E} {τ c : ℝ} (hτ : τ ≠ 0)
    (hx : f x = c) (hr : f (x + τ • w) = ⊤) : secondDifferenceQuotient f x v τ w = ⊤ := by
  rw [secondDifferenceQuotient, hx, hr, EReal.top_sub_coe, EReal.top_sub_coe,
    EReal.coe_mul_top_of_pos (by positivity)]

theorem secondDifferenceQuotient_of_bot {f : E → EReal} {x v w : E} {τ c : ℝ} (hτ : τ ≠ 0)
    (hx : f x = c) (hr : f (x + τ • w) = ⊥) : secondDifferenceQuotient f x v τ w = ⊥ := by
  rw [secondDifferenceQuotient, hx, hr, EReal.bot_sub, EReal.bot_sub,
    EReal.coe_mul_bot_of_pos (by positivity)]

/-- The quotient 13(5) vanishes in the direction `0`. -/
theorem secondDifferenceQuotient_zero_right {f : E → EReal} {x v : E} {c : ℝ} (hx : f x = c)
    (τ : ℝ) : secondDifferenceQuotient f x v τ 0 = 0 := by
  rw [secondDifferenceQuotient_of_coe hx (r := c) (by rw [smul_zero, add_zero, hx])]
  simp

/-- Formula 13(8): `Δ²_τ f(x̄ | v)(w) = (2/τ) [Δ_τ f(x̄)(w) - ⟪v, w⟫]`. -/
theorem secondDifferenceQuotient_eq_differenceQuotient {f : E → EReal} {x v : E} {c : ℝ}
    (hx : f x = c) {τ : ℝ} (hτ : 0 < τ) (w : E) :
    secondDifferenceQuotient f x v τ w =
      ((2 / τ : ℝ) : EReal) * (differenceQuotient f x τ w - ((⟪v, w⟫_ℝ : ℝ) : EReal)) := by
  rcases ereal_trichotomy (f (x + τ • w)) with h | h | ⟨r, h⟩
  · rw [secondDifferenceQuotient_of_bot hτ.ne' hx h, differenceQuotient_eq_bot hτ hx h,
      EReal.bot_sub, EReal.coe_mul_bot_of_pos (by positivity)]
  · rw [secondDifferenceQuotient_of_top hτ.ne' hx h, differenceQuotient_eq_top hτ hx h,
      EReal.top_sub_coe, EReal.coe_mul_top_of_pos (by positivity)]
  · rw [secondDifferenceQuotient_of_coe hx h, differenceQuotient_eq_coe hx h, ← EReal.coe_sub,
      ← EReal.coe_mul]
    congr 1
    field_simp

/-- When `df(x̄)(w) = ⟪v, w⟫`, the two quotients 13(4) and 13(5) agree. -/
theorem secondDifferenceQuotientAt_eq_of_subderivative_eq {f : E → EReal} {x v w : E} {τ : ℝ}
    (hw : subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)) :
    secondDifferenceQuotientAt f x τ w = secondDifferenceQuotient f x v τ w := by
  rw [secondDifferenceQuotientAt, secondDifferenceQuotient, hw, ← EReal.coe_mul,
    ← EReal.coe_neg]
  congr 1
  rw [infAddition]
  split_ifs with h
  · rcases h with h | h
    · rw [h, EReal.top_sub_coe]
    · exact absurd h (EReal.coe_ne_top _)
  · rw [EReal.coe_neg, ← sub_eq_add_neg]

/-- Scaling the direction: `Δ²_τ f(x̄ | v)(cw) = c² Δ²_{cτ} f(x̄ | v)(w)`. -/
theorem secondDifferenceQuotient_smul (f : E → EReal) (x v : E) (τ : ℝ) {c : ℝ} (hc : c ≠ 0)
    (w : E) :
    secondDifferenceQuotient f x v τ (c • w) =
      ((c ^ 2 : ℝ) : EReal) * secondDifferenceQuotient f x v (c * τ) w := by
  have h1 : τ • c • w = (c * τ) • w := by rw [smul_smul, mul_comm]
  have h2 : τ * ⟪v, c • w⟫_ℝ = c * τ * ⟪v, w⟫_ℝ := by
    rw [real_inner_smul_right]
    ring
  have h3 : ((2 / τ ^ 2 : ℝ) : EReal) =
      ((c ^ 2 : ℝ) : EReal) * ((2 / (c * τ) ^ 2 : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    rcases eq_or_ne τ 0 with rfl | hτ
    · simp
    · field_simp
  rw [secondDifferenceQuotient, secondDifferenceQuotient, h1, h2, h3, mul_assoc]

/-- Scaling the direction in 13(4): `Δ²_τ f(x̄)(cw) = c² Δ²_{cτ} f(x̄)(w)` for `c > 0`. -/
theorem secondDifferenceQuotientAt_smul {f : E → EReal} {x : E} {c₀ : ℝ} (hx : f x = c₀)
    (τ : ℝ) {c : ℝ} (hc : 0 < c) (w : E) :
    secondDifferenceQuotientAt f x τ (c • w) =
      ((c ^ 2 : ℝ) : EReal) * secondDifferenceQuotientAt f x (c * τ) w := by
  have hhom := (lowerSemicontinuous_positivelyHomogeneous_subderivative hx).2
  have h1 : τ • c • w = (c * τ) • w := by rw [smul_smul, mul_comm]
  have h2 : (τ : EReal) * subderivative f x (c • w) =
      ((c * τ : ℝ) : EReal) * subderivative f x w := by
    rw [hhom.2 hc, ← mul_assoc, ← EReal.coe_mul, mul_comm τ c]
  have h3 : ((2 / τ ^ 2 : ℝ) : EReal) =
      ((c ^ 2 : ℝ) : EReal) * ((2 / (c * τ) ^ 2 : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    rcases eq_or_ne τ 0 with rfl | hτ
    · simp
    · field_simp
  rw [secondDifferenceQuotientAt, secondDifferenceQuotientAt, h1, h2, h3, mul_assoc]

end Quotients

/-! ### Definition 13.3 -/

section Definition133

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Definition 13.3**: `d²f(x̄ | v)` is the lower epi-limit of the quotients
`Δ²_τ f(x̄ | v)` as `τ ↓ 0`: its epigraph is the outer limit of their epigraphs. -/
theorem epigraph_secondSubderivative (f : E → EReal) (x v : E) :
    epigraph (secondSubderivative f x v) =
      outerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (secondDifferenceQuotient f x v τ)) :=
  epigraph_liminf_prod _ _

/-- **Definition 13.3**: `d²f(x̄)` is the lower epi-limit of the quotients
`Δ²_τ f(x̄)` as `τ ↓ 0`. -/
theorem epigraph_secondSubderivativeAt (f : E → EReal) (x : E) :
    epigraph (secondSubderivativeAt f x) =
      outerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (secondDifferenceQuotientAt f x τ)) :=
  epigraph_liminf_prod _ _

/-- **Definition 13.3**: the two second subderivatives agree when `df(x̄)` is the
linear function `⟪v, ·⟫`. -/
theorem secondSubderivativeAt_eq_secondSubderivative_of_subderivative_eq {f : E → EReal}
    {x v : E} (hd : ∀ w, subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)) :
    secondSubderivativeAt f x = secondSubderivative f x v := by
  funext w
  unfold secondSubderivativeAt secondSubderivative
  congr 1
  funext p
  exact secondDifferenceQuotientAt_eq_of_subderivative_eq (hd p.2)

/-- **Definition 13.3**: `d²f(x̄ | v) = d²f(x̄)` when `f` is differentiable at `x̄`
(formula 7(16)) with gradient `v = ∇f(x̄)`. -/
theorem secondSubderivativeAt_eq_secondSubderivative_of_hasERealGradientAt {f : E → EReal}
    {x v : E} (hf : HasERealGradientAt f x (innerSL ℝ v)) :
    secondSubderivativeAt f x = secondSubderivative f x v := by
  obtain ⟨hx, hx', hfin, ho⟩ := hf
  have hxc : f x = (((f x).toReal : ℝ) : EReal) := (EReal.coe_toReal hx' hx).symm
  refine secondSubderivativeAt_eq_secondSubderivative_of_subderivative_eq fun w ↦ ?_
  have hs : HasSemiderivative f x w ((innerSL ℝ v) w : EReal) :=
    ⟨hx, hx', tendsto_of_isLittleO hxc (innerSL ℝ v).continuous
      (fun a _ w ↦ by rw [map_smul, smul_eq_mul]) hfin ho w⟩
  rw [hs.subderivative_eq, innerSL_apply_apply]

end Definition133

/-! ### Definition 13.4 -/

section Definition134

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 13.4**: `h` is positively homogeneous of degree `p > 0` when
`h(λw) = λ^p h(w)` for all `λ > 0` and `w`, and `h(0) < ∞`. -/
def IsPosHomogeneousOfDegree (h : E → EReal) (p : ℝ) : Prop :=
  0 < p ∧ (∀ ⦃c : ℝ⦄, 0 < c → ∀ w, h (c • w) = ((c ^ p : ℝ) : EReal) * h w) ∧ h 0 < ⊤

/-- **Definition 13.4**: a function positively homogeneous of degree `p` has
`h(0) = 0` or `h(0) = -∞`. -/
theorem IsPosHomogeneousOfDegree.zero_eq_zero_or_bot {h : E → EReal} {p : ℝ}
    (hh : IsPosHomogeneousOfDegree h p) : h 0 = 0 ∨ h 0 = ⊥ := by
  obtain ⟨hp, hsmul, h0⟩ := hh
  rcases ereal_trichotomy (h 0) with hb | ht | ⟨r, hr⟩
  · exact Or.inr hb
  · exact absurd ht h0.ne
  · left
    have h2 := hsmul (c := 2) two_pos 0
    rw [smul_zero, hr, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at h2
    have hgt : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow (by norm_num) hp
    have : r = 0 := by nlinarith
    rw [hr, this, EReal.coe_zero]

/-- **Definition 13.4** with `p = 1` is the positive homogeneity of
Definition 3.18. -/
theorem isPosHomogeneousOfDegree_one_iff {h : E → EReal} :
    IsPosHomogeneousOfDegree h 1 ↔ PositivelyHomogeneous h := by
  simp only [IsPosHomogeneousOfDegree, Real.rpow_one, zero_lt_one, true_and,
    PositivelyHomogeneous]
  constructor
  · rintro ⟨hs, h0⟩
    exact ⟨h0, fun w c hc ↦ hs hc w⟩
  · rintro ⟨h0, hs⟩
    exact ⟨fun c hc w ↦ hs hc, h0⟩

/-- Positive homogeneity of degree 2 with the natural-number power `λ²`. -/
theorem isPosHomogeneousOfDegree_two_iff {h : E → EReal} :
    IsPosHomogeneousOfDegree h 2 ↔
      (∀ ⦃c : ℝ⦄, 0 < c → ∀ w, h (c • w) = ((c ^ 2 : ℝ) : EReal) * h w) ∧ h 0 < ⊤ := by
  simp only [IsPosHomogeneousOfDegree, two_pos, true_and]
  constructor
  · rintro ⟨hs, h0⟩
    refine ⟨fun c hc w ↦ ?_, h0⟩
    rw [hs hc w, show (c ^ (2 : ℝ)) = c ^ 2 from Real.rpow_two c]
  · rintro ⟨hs, h0⟩
    refine ⟨fun c hc w ↦ ?_, h0⟩
    rw [hs hc w, show (c ^ (2 : ℝ)) = c ^ 2 from Real.rpow_two c]

end Definition134

/-! ### Proposition 13.5 -/

section Proposition135

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem tendsto_const_mul_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun τ : ℝ ↦ c * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun τ : ℝ ↦ c * τ) (𝓝 0) (𝓝 (c * 0)) := tendsto_id.const_mul c
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with τ hτ using mul_pos hc hτ

/-- The substitution `(τ, w') ↦ (c⁻¹τ, cw')` carries the joint filter at `w`
onto the joint filter at `cw`. -/
theorem map_prod_scaling {c : ℝ} (hc : 0 < c) (w : E) :
    map (fun p : ℝ × E ↦ (c⁻¹ * p.1, c • p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) =
      𝓝[>] (0 : ℝ) ×ˢ 𝓝 (c • w) := by
  have hc' : c ≠ 0 := hc.ne'
  refine map_eq_of_inverse (fun p : ℝ × E ↦ (c * p.1, c⁻¹ • p.2)) ?_ ?_ ?_
  · funext p
    simp [Function.comp, smul_smul, hc']
  · refine (tendsto_const_mul_nhdsGT_zero (inv_pos.2 hc)).prodMap ?_
    exact ((continuous_const_smul c).tendsto w)
  · refine (tendsto_const_mul_nhdsGT_zero hc).prodMap ?_
    have h := (continuous_const_smul c⁻¹).tendsto (c • w)
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at h

instance nhdsGT_prod_neBot (w : E) : (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w).NeBot := inferInstance

/-- **Proposition 13.5**: `d²f(x̄ | v)(cw) = c² d²f(x̄ | v)(w)` for `c > 0`. -/
theorem secondSubderivative_smul (f : E → EReal) (x v : E) {c : ℝ} (hc : 0 < c) (w : E) :
    secondSubderivative f x v (c • w) = ((c ^ 2 : ℝ) : EReal) * secondSubderivative f x v w := by
  rw [secondSubderivative, secondSubderivative, ← map_prod_scaling hc w, ← liminf_comp,
    EReal.coe_mul_liminf_of_pos _ (by positivity)]
  congr 1
  funext p
  simp only [Function.comp]
  rw [secondDifferenceQuotient_smul f x v _ hc.ne', ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- **Proposition 13.5**: `d²f(x̄)(cw) = c² d²f(x̄)(w)` for `c > 0`. -/
theorem secondSubderivativeAt_smul {f : E → EReal} {x : E} {c₀ : ℝ} (hx : f x = c₀) {c : ℝ}
    (hc : 0 < c) (w : E) :
    secondSubderivativeAt f x (c • w) = ((c ^ 2 : ℝ) : EReal) * secondSubderivativeAt f x w := by
  rw [secondSubderivativeAt, secondSubderivativeAt, ← map_prod_scaling hc w, ← liminf_comp,
    EReal.coe_mul_liminf_of_pos _ (by positivity)]
  congr 1
  funext p
  simp only [Function.comp]
  rw [secondDifferenceQuotientAt_smul hx _ hc, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- **Proposition 13.5**: `d²f(x̄ | v)` is lower semicontinuous. -/
theorem lowerSemicontinuous_secondSubderivative (f : E → EReal) (x v : E) :
    LowerSemicontinuous (secondSubderivative f x v) :=
  lowerSemicontinuous_liminf_prod _ _

/-- **Proposition 13.5**: `d²f(x̄)` is lower semicontinuous. -/
theorem lowerSemicontinuous_secondSubderivativeAt (f : E → EReal) (x : E) :
    LowerSemicontinuous (secondSubderivativeAt f x) :=
  lowerSemicontinuous_liminf_prod _ _

/-- `d²f(x̄ | v)(0) ≤ 0`, since every quotient vanishes in the direction `0`. -/
theorem secondSubderivative_zero_le {f : E → EReal} {x v : E} {c : ℝ} (hx : f x = c) :
    secondSubderivative f x v 0 ≤ 0 := by
  refine liminf_le_of_frequently_le' ?_
  refine (tendsto_pair_const (0 : E)).frequently (Frequently.of_forall fun τ ↦ ?_)
  rw [secondDifferenceQuotient_zero_right hx]

/-- **Proposition 13.5**: `d²f(x̄ | v)` is positively homogeneous of degree 2. -/
theorem isPosHomogeneousOfDegree_two_secondSubderivative {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (v : E) : IsPosHomogeneousOfDegree (secondSubderivative f x v) 2 :=
  isPosHomogeneousOfDegree_two_iff.2 ⟨fun _ hc w ↦ secondSubderivative_smul f x v hc w,
    (secondSubderivative_zero_le hx).trans_lt EReal.zero_lt_top⟩

/-- The quotient 13(4) in the direction `0` vanishes when `df(x̄)(0) = 0`. -/
theorem secondDifferenceQuotientAt_zero_right {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c)
    (h0 : subderivative f x 0 = 0) (τ : ℝ) : secondDifferenceQuotientAt f x τ 0 = 0 := by
  rw [secondDifferenceQuotientAt, h0, mul_zero, neg_zero, infAddition_zero, smul_zero, add_zero,
    hx, ← EReal.coe_sub, sub_self, EReal.coe_zero, mul_zero]

/-- `df(x̄)(0)` is either `0` or `-∞`. -/
theorem subderivative_zero_eq_zero_or_bot {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    subderivative f x 0 = 0 ∨ subderivative f x 0 = ⊥ :=
  (lowerSemicontinuous_positivelyHomogeneous_subderivative hx).2.zero_eq_zero_or_bot

/-- **Proposition 13.5**, corrected: `d²f(x̄)` is positively homogeneous of degree 2
as soon as `df(x̄)(0) ≠ -∞`.  (The scaling law holds in general by
`secondSubderivativeAt_smul`; see `secondSubderivativeAt_negSqrtAbs` for a
failure of `d²f(x̄)(0) < ∞` when `df(x̄)(0) = -∞`, and
`isPosHomogeneousOfDegree_two_secondSubderivativeAt_negSqrtNegPart` for a case
with `df(x̄)(0) = -∞` where the conclusion still holds.) -/
theorem isPosHomogeneousOfDegree_two_secondSubderivativeAt {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (h0 : subderivative f x 0 ≠ ⊥) :
    IsPosHomogeneousOfDegree (secondSubderivativeAt f x) 2 := by
  have h00 : subderivative f x 0 = 0 := (subderivative_zero_eq_zero_or_bot hx).resolve_right h0
  refine isPosHomogeneousOfDegree_two_iff.2 ⟨fun _ hc w ↦ secondSubderivativeAt_smul hx hc w, ?_⟩
  refine lt_of_le_of_lt (liminf_le_of_frequently_le' ?_) (EReal.zero_lt_top)
  refine (tendsto_pair_const (0 : E)).frequently (Frequently.of_forall fun τ ↦ ?_)
  rw [secondDifferenceQuotientAt_zero_right hx h00]

/-- Pointwise concavity in `v` of the quotients 13(5): they are affine in `v`
where `f(x̄ + τw)` is finite and constant otherwise. -/
theorem le_secondDifferenceQuotient_combo {f : E → EReal} {x v₀ v₁ : E} {c : ℝ} (hx : f x = c)
    {τ : ℝ} (hτ : τ ≠ 0) (w : E) {a b β₀ β₁ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h₀ : (β₀ : EReal) ≤ secondDifferenceQuotient f x v₀ τ w)
    (h₁ : (β₁ : EReal) ≤ secondDifferenceQuotient f x v₁ τ w) :
    ((a * β₀ + b * β₁ : ℝ) : EReal) ≤ secondDifferenceQuotient f x (a • v₀ + b • v₁) τ w := by
  rcases ereal_trichotomy (f (x + τ • w)) with h | h | ⟨r, h⟩
  · rw [secondDifferenceQuotient_of_bot hτ hx h] at h₀
    exact absurd (le_bot_iff.1 h₀) (EReal.coe_ne_bot _)
  · rw [secondDifferenceQuotient_of_top hτ hx h]
    exact le_top
  · rw [secondDifferenceQuotient_of_coe hx h] at h₀ h₁ ⊢
    rw [EReal.coe_le_coe_iff] at h₀ h₁ ⊢
    have hlin : 2 / τ ^ 2 * (r - c - τ * ⟪a • v₀ + b • v₁, w⟫_ℝ) =
        a * (2 / τ ^ 2 * (r - c - τ * ⟪v₀, w⟫_ℝ)) + b * (2 / τ ^ 2 * (r - c - τ * ⟪v₁, w⟫_ℝ)) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have : r - c = a * (r - c) + b * (r - c) := by rw [← add_mul, hab, one_mul]
      linear_combination (2 / τ ^ 2) * this
    rw [hlin]
    nlinarith

/-- **Proposition 13.5**: `d²f(x̄ | v)(w)` depends concavely on `v`: its hypograph
is convex. -/
theorem convex_hypograph_secondSubderivative {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c)
    (w : E) : Convex ℝ (hypograph fun v ↦ secondSubderivative f x v w) := by
  rintro ⟨v₀, α₀⟩ h₀ ⟨v₁, α₁⟩ h₁ a b ha hb hab
  simp only [hypograph, mem_setOf_eq] at h₀ h₁
  simp only [hypograph, mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  by_contra hcon
  push_neg at hcon
  obtain ⟨s, hs1, hs2⟩ := EReal.exists_between_coe_real hcon
  have hs2' : s < a * α₀ + b * α₁ := EReal.coe_lt_coe_iff.1 hs2
  have e0 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      ((α₀ - (a * α₀ + b * α₁ - s) : ℝ) : EReal) < secondDifferenceQuotient f x v₀ p.1 p.2 :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) h₀)
  have e1 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      ((α₁ - (a * α₀ + b * α₁ - s) : ℝ) : EReal) < secondDifferenceQuotient f x v₁ p.1 p.2 :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) h₁)
  have e2 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hle : (s : EReal) ≤ secondSubderivative f x (a • v₀ + b • v₁) w := by
    refine le_liminf_of_le (h := ?_)
    filter_upwards [e0, e1, e2] with p hp0 hp1 hp2
    have hcombo := le_secondDifferenceQuotient_combo hx hp2.ne' p.2 ha hb hab hp0.le hp1.le
    have heq : a * (α₀ - (a * α₀ + b * α₁ - s)) + b * (α₁ - (a * α₀ + b * α₁ - s)) = s := by
      linear_combination (-(a * α₀ + b * α₁ - s)) * hab
    rwa [heq] at hcombo
  exact absurd hs1 (not_lt.2 hle)

/-- **Proposition 13.5**: `d²f(x̄ | v)(w) = ∞` when `⟪v, w⟫ < df(x̄)(w)`. -/
theorem secondSubderivative_eq_top_of_inner_lt {f : E → EReal} {x v w : E} {c : ℝ}
    (hx : f x = c) (h : ((⟪v, w⟫_ℝ : ℝ) : EReal) < subderivative f x w) :
    secondSubderivative f x v w = ⊤ := by
  obtain ⟨β, hβ1, hβ2⟩ := EReal.exists_between_coe_real h
  have hβ1' : ⟪v, w⟫_ℝ < β := EReal.coe_lt_coe_iff.1 hβ1
  have hγ : 0 < β - ⟪v, w⟫_ℝ := by linarith
  rw [EReal.eq_top_iff_forall_lt]
  intro M
  have hδ : 0 < (β - ⟪v, w⟫_ℝ) / (|M| + 1) := by positivity
  have e1 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (β : EReal) < differenceQuotient f x p.1 p.2 :=
    eventually_lt_of_lt_liminf hβ2
  have e2 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, ⟪v, p.2⟫_ℝ < ⟪v, w⟫_ℝ + (β - ⟪v, w⟫_ℝ) / 2 := by
    have hc : Continuous fun u : E ↦ ⟪v, u⟫_ℝ := continuous_const.inner continuous_id
    exact tendsto_snd.eventually ((hc.tendsto w).eventually (gt_mem_nhds (by linarith)))
  have e3 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, 0 < p.1 := tendsto_fst.eventually self_mem_nhdsWithin
  have e4 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, p.1 < (β - ⟪v, w⟫_ℝ) / (|M| + 1) :=
    tendsto_fst.eventually (nhdsWithin_le_nhds (Iio_mem_nhds hδ))
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one M)) (le_liminf_of_le (h := ?_))
  filter_upwards [e1, e2, e3, e4] with p hp1 hp2 hp3 hp4
  obtain ⟨τ, u⟩ := p
  simp only at hp1 hp2 hp3 hp4 ⊢
  rcases ereal_trichotomy (f (x + τ • u)) with hf | hf | ⟨r, hf⟩
  · rw [differenceQuotient_eq_bot hp3 hx hf] at hp1
    exact absurd hp1 not_lt_bot
  · rw [secondDifferenceQuotient_of_top hp3.ne' hx hf]
    exact le_top
  · rw [differenceQuotient_eq_coe hx hf, EReal.coe_lt_coe_iff] at hp1
    rw [secondDifferenceQuotient_of_coe hx hf, EReal.coe_le_coe_iff]
    have hrc : τ * β < r - c := by
      have := mul_lt_mul_of_pos_left hp1 hp3
      rwa [← mul_assoc, mul_inv_cancel₀ hp3.ne', one_mul] at this
    have h5 := mul_lt_mul_of_pos_left hp2 hp3
    have hτγ : τ * (|M| + 1) < β - ⟪v, w⟫_ℝ := by
      rwa [lt_div_iff₀ (by positivity)] at hp4
    have h6 := mul_lt_mul_of_pos_left hτγ hp3
    have h7 : (M + 1) * τ ^ 2 ≤ (|M| + 1) * τ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) (sq_nonneg τ)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith

/-- **Proposition 13.5**: `d²f(x̄ | v)(w) = -∞` when `⟪v, w⟫ > df(x̄)(w)`. -/
theorem secondSubderivative_eq_bot_of_lt_inner {f : E → EReal} {x v w : E} {c : ℝ}
    (hx : f x = c) (h : subderivative f x w < ((⟪v, w⟫_ℝ : ℝ) : EReal)) :
    secondSubderivative f x v w = ⊥ := by
  obtain ⟨β, hβ1, hβ2⟩ := EReal.exists_between_coe_real h
  have hβ2' : β < ⟪v, w⟫_ℝ := EReal.coe_lt_coe_iff.1 hβ2
  have hγ : 0 < ⟪v, w⟫_ℝ - β := by linarith
  rw [EReal.eq_bot_iff_forall_lt]
  intro M
  have hδ : 0 < (⟪v, w⟫_ℝ - β) / (|M| + 1) := by positivity
  have f1 : ∃ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, differenceQuotient f x p.1 p.2 < (β : EReal) :=
    frequently_lt_of_liminf_lt (h := hβ1)
  have e2 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, ⟪v, w⟫_ℝ - (⟪v, w⟫_ℝ - β) / 2 < ⟪v, p.2⟫_ℝ := by
    have hc : Continuous fun u : E ↦ ⟪v, u⟫_ℝ := continuous_const.inner continuous_id
    exact tendsto_snd.eventually ((hc.tendsto w).eventually (lt_mem_nhds (by linarith)))
  have e3 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, 0 < p.1 := tendsto_fst.eventually self_mem_nhdsWithin
  have e4 : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, p.1 < (⟪v, w⟫_ℝ - β) / (|M| + 1) :=
    tendsto_fst.eventually (nhdsWithin_le_nhds (Iio_mem_nhds hδ))
  refine lt_of_le_of_lt (liminf_le_of_frequently_le' ?_) (EReal.coe_lt_coe_iff.2 (sub_one_lt M))
  refine (f1.and_eventually (e2.and (e3.and e4))).mono ?_
  rintro ⟨τ, u⟩ ⟨hp1, hp2, hp3, hp4⟩
  simp only at hp1 hp2 hp3 hp4 ⊢
  rcases ereal_trichotomy (f (x + τ • u)) with hf | hf | ⟨r, hf⟩
  · rw [secondDifferenceQuotient_of_bot hp3.ne' hx hf]
    exact bot_le
  · rw [differenceQuotient_eq_top hp3 hx hf] at hp1
    exact absurd hp1 not_top_lt
  · rw [differenceQuotient_eq_coe hx hf, EReal.coe_lt_coe_iff] at hp1
    rw [secondDifferenceQuotient_of_coe hx hf, EReal.coe_le_coe_iff]
    have hrc : r - c < τ * β := by
      have := mul_lt_mul_of_pos_left hp1 hp3
      rwa [← mul_assoc, mul_inv_cancel₀ hp3.ne', one_mul] at this
    have h5 := mul_lt_mul_of_pos_left hp2 hp3
    have hτγ : τ * (|M| + 1) < ⟪v, w⟫_ℝ - β := by
      rwa [lt_div_iff₀ (by positivity)] at hp4
    have h6 := mul_lt_mul_of_pos_left hτγ hp3
    have h7 : (-(|M| + 1)) * τ ^ 2 ≤ (M - 1) * τ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [neg_abs_le M]) (sq_nonneg τ)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith

/-- **Proposition 13.5**: finiteness of `d²f(x̄ | v)(w)` necessitates
`⟪v, w⟫ = df(x̄)(w)`. -/
theorem subderivative_eq_inner_of_secondSubderivative_finite {f : E → EReal} {x v w : E} {c : ℝ}
    (hx : f x = c) (htop : secondSubderivative f x v w ≠ ⊤)
    (hbot : secondSubderivative f x v w ≠ ⊥) :
    subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) := by
  rcases lt_trichotomy (subderivative f x w) ((⟪v, w⟫_ℝ : ℝ) : EReal) with h | h | h
  · exact absurd (secondSubderivative_eq_bot_of_lt_inner hx h) hbot
  · exact h
  · exact absurd (secondSubderivative_eq_top_of_inner_lt hx h) htop

/-- **Proposition 13.5**: `dom d²f(x̄ | v) ⊂ {w | df(x̄)(w) ≤ ⟪v, w⟫}`. -/
theorem effectiveDomain_secondSubderivative_subset {f : E → EReal} {x v : E} {c : ℝ}
    (hx : f x = c) :
    effectiveDomain (secondSubderivative f x v) ⊆
      {w | subderivative f x w ≤ ((⟪v, w⟫_ℝ : ℝ) : EReal)} := by
  intro w hw
  by_contra hlt
  simp only [mem_setOf_eq, not_le] at hlt
  have htop := secondSubderivative_eq_top_of_inner_lt hx hlt
  have hw' : secondSubderivative f x v w < ⊤ := hw
  rw [htop] at hw'
  exact lt_irrefl _ hw'

/-- **Proposition 13.5**: if `d²f(x̄ | v)` is proper then `v ∈ ∂̂f(x̄)` and
`dom d²f(x̄ | v) ⊂ {w | df(x̄)(w) = ⟪v, w⟫} ⊂ N_{∂̂f(x̄)}(v)`. -/
theorem IsProper.secondSubderivative_consequences [FiniteDimensional ℝ E] {f : E → EReal}
    {x v : E} {c : ℝ} (hx : f x = c) (hp : IsProper (secondSubderivative f x v)) :
    v ∈ regularSubdifferential f x ∧
      effectiveDomain (secondSubderivative f x v) ⊆
        {w | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} ∧
      {w | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} ⊆
        normalCone (regularSubdifferential f x) v := by
  have hge : ∀ w, ((⟪v, w⟫_ℝ : ℝ) : EReal) ≤ subderivative f x w := by
    intro w
    by_contra hlt
    push_neg at hlt
    exact (hp.2 w).ne' (secondSubderivative_eq_bot_of_lt_inner hx hlt)
  have hv : v ∈ regularSubdifferential f x :=
    (mem_regularSubdifferential_iff_inner_le_subderivative hx).2 hge
  refine ⟨hv, fun w hw ↦ le_antisymm (effectiveDomain_secondSubderivative_subset hx hw) (hge w),
    fun w hw ↦ regularNormalCone_subset_normalCone _ _ ?_⟩
  refine mem_regularNormalCone_iff.2 ⟨hv, fun ε hε ↦ ⟨1, one_pos, fun v' hv' _ ↦ ?_⟩⟩
  have h1 := inner_le_subderivative_of_mem_regularSubdifferential hv' w
  rw [show subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) from hw, EReal.coe_le_coe_iff] at h1
  have h2 : ⟪w, v' - v⟫_ℝ ≤ 0 := by
    rw [inner_sub_right, real_inner_comm v' w, real_inner_comm v w]
    linarith
  exact h2.trans (by positivity)

/-- The inclusion `{w | df(x̄)(w) = ⟪v, w⟫} ⊂ N_{∂̂f(x̄)}(v)` of Proposition 13.5
for any `v ∈ ∂̂f(x̄)`. -/
theorem setOf_subderivative_eq_inner_subset_normalCone {f : E → EReal} {x v : E}
    (hv : v ∈ regularSubdifferential f x) :
    {w | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} ⊆
      normalCone (regularSubdifferential f x) v := by
  intro w hw
  refine regularNormalCone_subset_normalCone _ _ ?_
  refine mem_regularNormalCone_iff.2 ⟨hv, fun ε hε ↦ ⟨1, one_pos, fun v' hv' _ ↦ ?_⟩⟩
  have h1 := inner_le_subderivative_of_mem_regularSubdifferential hv' w
  rw [show subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal) from hw, EReal.coe_le_coe_iff] at h1
  have h2 : ⟪w, v' - v⟫_ℝ ≤ 0 := by
    rw [inner_sub_right, real_inner_comm v' w, real_inner_comm v w]
    linarith
  exact h2.trans (by positivity)

end Proposition135

/-! ### The counterexample to the printed homogeneity of `d²f(x̄)` -/

section NegSqrtAbs

/-- The function `x ↦ -√|x|` on `ℝ`. -/
noncomputable def negSqrtAbs (x : ℝ) : EReal := ((-Real.sqrt |x| : ℝ) : EReal)

/-- `d(-√|·|)(0) ≡ -∞`. -/
theorem subderivative_negSqrtAbs (w : ℝ) : subderivative negSqrtAbs 0 w = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro M
  refine lt_of_le_of_lt (liminf_le_of_frequently_le' ?_) (EReal.coe_lt_coe_iff.2 (sub_one_lt M))
  rw [Filter.frequently_iff]
  intro S hS
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hS
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨u, huV, hu0⟩ : ∃ u ∈ V, u ≠ 0 := by
    by_cases hw : w = 0
    · refine ⟨ε / 2, hball ?_, by positivity⟩
      rw [Metric.mem_ball, hw, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      linarith
    · exact ⟨w, mem_of_mem_nhds hV, hw⟩
  have hu : 0 < |u| := abs_pos.2 hu0
  obtain ⟨δ, hδ, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  set τ : ℝ := min (δ / 2) (|u| / (|M| + 1) ^ 2) with hτdef
  have hτ : 0 < τ := lt_min (half_pos hδ) (by positivity)
  have hτU : τ ∈ U := hIoo ⟨hτ, lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)⟩
  refine ⟨(τ, u), hUV ⟨hτU, huV⟩, ?_⟩
  have hτu : τ * (|M| + 1) ^ 2 ≤ |u| := by
    have := min_le_right (δ / 2) (|u| / (|M| + 1) ^ 2)
    rw [← hτdef, le_div_iff₀ (by positivity)] at this
    exact this
  have hsq : (|M| + 1) * τ ≤ Real.sqrt |τ * u| := by
    rw [Real.le_sqrt (by positivity) (abs_nonneg _), abs_mul, abs_of_pos hτ]
    nlinarith
  change differenceQuotient negSqrtAbs 0 τ u ≤ ((M - 1 : ℝ) : EReal)
  rw [differenceQuotient_eq_coe (c := 0) (r := -Real.sqrt |τ * u|)
    (by simp [negSqrtAbs]) (by simp [negSqrtAbs, smul_eq_mul]), EReal.coe_le_coe_iff, sub_zero]
  have h1 : τ⁻¹ * (-Real.sqrt |τ * u|) = -(Real.sqrt |τ * u| / τ) := by ring
  have h2 : |M| + 1 ≤ Real.sqrt |τ * u| / τ := by
    rw [le_div_iff₀ hτ]
    linarith
  rw [h1]
  linarith [neg_abs_le M]

/-- For `f = -√|·|` every quotient `Δ²_τ f(0)(w)` equals `∞`, hence `d²f(0) ≡ ∞`. -/
theorem secondSubderivativeAt_negSqrtAbs (w : ℝ) : secondSubderivativeAt negSqrtAbs 0 w = ⊤ := by
  refine eq_top_iff.2 (le_liminf_of_le (h := ?_))
  filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p hp
  rw [secondDifferenceQuotientAt, subderivative_negSqrtAbs, EReal.coe_mul_bot_of_pos hp,
    EReal.neg_bot, infAddition, if_pos (Or.inr rfl), EReal.coe_mul_top_of_pos (by
      have : (0 : ℝ) < p.1 := hp
      positivity)]

/-- **Correction to Proposition 13.5**: `d²f(x̄)` need not be positively
homogeneous of degree 2 in the sense of Definition 13.4, since `d²f(0)(0) = ∞`
for `f = -√|·|`, although `f(0) = 0` is finite. -/
theorem not_isPosHomogeneousOfDegree_secondSubderivativeAt_negSqrtAbs :
    negSqrtAbs 0 = 0 ∧ ¬ IsPosHomogeneousOfDegree (secondSubderivativeAt negSqrtAbs 0) 2 := by
  refine ⟨by simp [negSqrtAbs], fun h ↦ ?_⟩
  have h0 := h.2.2
  rw [secondSubderivativeAt_negSqrtAbs] at h0
  exact lt_irrefl _ h0

end NegSqrtAbs

/-! ### The hypothesis `df(x̄)(0) ≠ -∞` is sufficient, not necessary -/

section NegSqrtNegPart

/-- The function `x ↦ -√(-x)` for `x < 0` and `x ↦ 0` for `x ≥ 0` on `ℝ` (`Real.sqrt` vanishes
on `(-∞, 0]`). -/
noncomputable def negSqrtNegPart (x : ℝ) : EReal := ((-Real.sqrt (-x) : ℝ) : EReal)

theorem negSqrtNegPart_zero : negSqrtNegPart 0 = ((0 : ℝ) : EReal) := by simp [negSqrtNegPart]

theorem negSqrtNegPart_of_nonneg {x : ℝ} (hx : 0 ≤ x) : negSqrtNegPart x = ((0 : ℝ) : EReal) := by
  simp [negSqrtNegPart, Real.sqrt_eq_zero_of_nonpos (neg_nonpos.2 hx)]

/-- `d(negSqrtNegPart)(0)(u) = 0` for `u > 0`. -/
theorem subderivative_negSqrtNegPart_of_pos {u : ℝ} (hu : 0 < u) :
    subderivative negSqrtNegPart 0 u = 0 := by
  have heq : (fun p : ℝ × ℝ ↦ differenceQuotient negSqrtNegPart 0 p.1 p.2) =ᶠ[𝓝[>] (0 : ℝ) ×ˢ 𝓝 u]
      fun _ ↦ (0 : EReal) := by
    filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0),
      tendsto_snd.eventually (Ioi_mem_nhds hu)] with p hp1 hp2
    have h1 : (0 : ℝ) < p.1 := hp1
    have h2 : (0 : ℝ) < p.2 := hp2
    rw [differenceQuotient_eq_coe (c := 0) (r := 0) negSqrtNegPart_zero
      (by rw [zero_add, smul_eq_mul]; exact negSqrtNegPart_of_nonneg (mul_pos h1 h2).le)]
    simp
  rw [subderivative, liminf_congr heq, liminf_const]

theorem secondDifferenceQuotientAt_negSqrtNegPart_of_pos {τ u : ℝ} (hτ : 0 < τ) (hu : 0 < u) :
    secondDifferenceQuotientAt negSqrtNegPart 0 τ u = 0 := by
  rw [secondDifferenceQuotientAt, subderivative_negSqrtNegPart_of_pos hu, mul_zero, neg_zero,
    infAddition_zero, zero_add, smul_eq_mul, negSqrtNegPart_of_nonneg (mul_pos hτ hu).le,
    negSqrtNegPart_zero, ← EReal.coe_sub, sub_self, EReal.coe_zero, mul_zero]

theorem secondSubderivativeAt_negSqrtNegPart_zero_le :
    secondSubderivativeAt negSqrtNegPart 0 0 ≤ 0 := by
  refine liminf_le_of_frequently_le' ?_
  rw [Filter.frequently_iff]
  intro S hS
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hS
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨δ, hδ, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  have hδ' : (0 : ℝ) < δ := hδ
  refine ⟨(δ / 2, ε / 2), hUV ⟨hIoo ⟨half_pos hδ', half_lt_self hδ'⟩, hball ?_⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith
  · exact (secondDifferenceQuotientAt_negSqrtNegPart_of_pos (half_pos hδ') (half_pos hε)).le

/-- `d(negSqrtNegPart)(0)(0) = -∞`: the quotients in directions `u < 0` near `0` are unbounded
below. -/
theorem subderivative_negSqrtNegPart_zero : subderivative negSqrtNegPart 0 0 = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro M
  refine lt_of_le_of_lt (liminf_le_of_frequently_le' ?_) (EReal.coe_lt_coe_iff.2 (sub_one_lt M))
  rw [Filter.frequently_iff]
  intro S hS
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hS
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨δ, hδ, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
  have hδ' : (0 : ℝ) < δ := hδ
  have hε' : (0 : ℝ) < ε := hε
  have huV : -(ε / 2) ∈ V := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hε')]; linarith)
  set τ : ℝ := min (δ / 2) ((ε / 2) / (|M| + 1) ^ 2) with hτdef
  have hτ : 0 < τ := lt_min (half_pos hδ') (by positivity)
  have hτU : τ ∈ U := hIoo ⟨hτ, lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ')⟩
  refine ⟨(τ, -(ε / 2)), hUV ⟨hτU, huV⟩, ?_⟩
  have hτu : τ * (|M| + 1) ^ 2 ≤ ε / 2 := by
    have := min_le_right (δ / 2) ((ε / 2) / (|M| + 1) ^ 2)
    rw [← hτdef, le_div_iff₀ (by positivity)] at this
    exact this
  have hneg : -(τ * -(ε / 2)) = τ * (ε / 2) := by ring
  have hsq : (|M| + 1) * τ ≤ Real.sqrt (τ * (ε / 2)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith
  change differenceQuotient negSqrtNegPart 0 τ (-(ε / 2)) ≤ ((M - 1 : ℝ) : EReal)
  rw [differenceQuotient_eq_coe (c := 0) (r := -Real.sqrt (τ * (ε / 2))) negSqrtNegPart_zero
    (by rw [zero_add, smul_eq_mul, negSqrtNegPart, hneg]), EReal.coe_le_coe_iff, sub_zero]
  have h1 : τ⁻¹ * (-Real.sqrt (τ * (ε / 2))) = -(Real.sqrt (τ * (ε / 2)) / τ) := by ring
  have h2 : |M| + 1 ≤ Real.sqrt (τ * (ε / 2)) / τ := by
    rw [le_div_iff₀ hτ]
    linarith
  rw [h1]
  linarith [neg_abs_le M]

/-- **Proposition 13.5**: the hypothesis `df(x̄)(0) ≠ -∞` of
`isPosHomogeneousOfDegree_two_secondSubderivativeAt` is sufficient but not necessary.  For
`f(x) = -√(-x)` on `x < 0` and `f = 0` on `x ≥ 0`, `df(0)(0) = -∞`, and still `d²f(0)` is
positively homogeneous of degree 2 in the sense of Definition 13.4 (`d²f(0)(0) ≤ 0`, since
the quotients `Δ²_τ f(0)(u)` vanish for `u > 0`). -/
theorem isPosHomogeneousOfDegree_two_secondSubderivativeAt_negSqrtNegPart :
    negSqrtNegPart 0 = ((0 : ℝ) : EReal) ∧ subderivative negSqrtNegPart 0 0 = ⊥ ∧
      IsPosHomogeneousOfDegree (secondSubderivativeAt negSqrtNegPart 0) 2 :=
  ⟨negSqrtNegPart_zero, subderivative_negSqrtNegPart_zero,
    isPosHomogeneousOfDegree_two_iff.2
      ⟨fun _ hc w ↦ secondSubderivativeAt_smul negSqrtNegPart_zero hc w,
        secondSubderivativeAt_negSqrtNegPart_zero_le.trans_lt EReal.zero_lt_top⟩⟩

end NegSqrtNegPart

/-! ### Definition 13.6 -/

section Definition136

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Definition 13.6(a)**: `f` is twice semidifferentiable at `x̄` when it is
semidifferentiable at `x̄` and the quotients `Δ²_τ f(x̄)` converge continuously
to `d²f(x̄)` as `τ ↓ 0`. -/
def TwiceSemidifferentiableAt (f : E → EReal) (x : E) : Prop :=
  SemidifferentiableAt f x ∧ ∀ w, Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotientAt f x p.1 p.2)
    (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (secondSubderivativeAt f x w))

/-- **Definition 13.6(b)**: `f` is twice epi-differentiable at `x̄` for `v` when the
quotients `Δ²_τ f(x̄ | v)` epi-converge to `d²f(x̄ | v)` as `τ ↓ 0`. -/
def TwiceEpiDifferentiableAt (f : E → EReal) (x v : E) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ PKConvergesAlong (𝓝[>] (0 : ℝ))
    (fun τ ↦ epigraph (secondDifferenceQuotient f x v τ)) (epigraph (secondSubderivative f x v))

/-- **Definition 13.6(b)**: properly twice epi-differentiable at `x̄` for `v`. -/
def ProperlyTwiceEpiDifferentiableAt (f : E → EReal) (x v : E) : Prop :=
  TwiceEpiDifferentiableAt f x v ∧ IsProper (secondSubderivative f x v)

/-- The discussion after Definition 13.6: twice semidifferentiability asks that the
lower limit defining `d²f(x̄)(w)` be a full limit for every `w`. -/
theorem twiceSemidifferentiableAt_iff_exists_tendsto {f : E → EReal} {x : E} :
    TwiceSemidifferentiableAt f x ↔ SemidifferentiableAt f x ∧ ∀ w, ∃ β : EReal,
      Tendsto (fun p : ℝ × E ↦ secondDifferenceQuotientAt f x p.1 p.2)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 β) := by
  refine ⟨fun h ↦ ⟨h.1, fun w ↦ ⟨_, h.2 w⟩⟩, fun h ↦ ⟨h.1, fun w ↦ ?_⟩⟩
  obtain ⟨β, hβ⟩ := h.2 w
  have heq : secondSubderivativeAt f x w = β := hβ.liminf_eq
  rwa [heq]

/-- Since `d²f(x̄ | v)` is always the lower epi-limit, epi-convergence to some
function is the same as epi-convergence to `d²f(x̄ | v)`. -/
theorem twiceEpiDifferentiableAt_iff_exists {f : E → EReal} {x v : E} :
    TwiceEpiDifferentiableAt f x v ↔ f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∃ h : E → EReal,
      PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (secondDifferenceQuotient f x v τ))
        (epigraph h) := by
  refine ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, _, h3⟩, fun ⟨h1, h2, h, hconv⟩ ↦ ⟨h1, h2, ?_⟩⟩
  have hh : h = secondSubderivative f x v :=
    eq_of_epigraph_eq (by rw [epigraph_secondSubderivative, hconv.outer_eq])
  rwa [← hh]

/-- The discussion after Definition 13.6: since `d²f(x̄ | v)` is already the
lower epi-limit, twice epi-differentiability is the inclusion of its epigraph
in the inner limit of the epigraphs of the quotients. -/
theorem twiceEpiDifferentiableAt_iff_subset {f : E → EReal} {x v : E} :
    TwiceEpiDifferentiableAt f x v ↔ f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ epigraph (secondSubderivative f x v) ⊆
      innerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (secondDifferenceQuotient f x v τ)) := by
  refine ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3.inner_eq.symm.subset⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, ?_, ?_⟩⟩
  · refine Subset.antisymm ?_ h3
    rw [epigraph_secondSubderivative]
    exact innerSetLimitAlong_subset_outerSetLimitAlong _
  · exact (epigraph_secondSubderivative f x v).symm

end Definition136

end RW
