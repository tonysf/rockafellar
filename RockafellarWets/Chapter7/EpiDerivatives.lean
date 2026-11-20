/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Epi-derivatives

Definition 7.23, formula 7(24) and Proposition 7.24.

The epi-limit in 7(23) is the epi-limit of the difference quotients
`Δ_τ f(x̄)` as `τ ↓ 0`, read through 7(10)–7(11): the lower and upper epi-limit
values at `w` are the values at `w` of the functions whose epigraphs are the
outer and inner limits, along `𝓝[>] 0`, of the epigraphs `epi Δ_τ f(x̄)`
(Definition 7.1 for the parameter `τ`).  The boundary function
`epiBoundary` of the root `EpiLimits` API turns these closed, upward-closed
sets back into functions.

The main facts are:
* formula 7(24): `epi Δ_τ f(x̄) = τ⁻¹(epi f - (x̄, f(x̄)))` for `τ > 0`
  (`epigraph_differenceQuotient`), so the outer and inner limits of the
  epigraphs are the tangent cone and the derivable cone of `epi f`;
* the lower epi-limit is the function `df(x̄)` of formula 7(21)
  (`lowerEpiDerivative_eq_subderivative`), whence
  `epi df(x̄) = T_{epi f}(x̄, f(x̄))` at every point
  (`epigraph_subderivative_eq_tangentCone`);
* Proposition 7.24: epi-differentiability at `x̄` is geometric derivability of
  `epi f` at `(x̄, f(x̄))`, and the epi-derivative function has the tangent
  cone as its epigraph;
* the remarks after 7.23: an epi-derivative equals `df(x̄)(w)`, and a
  semiderivative is an epi-derivative.
-/

import RockafellarWets.Chapter7.SemidifferentiabilityCharacterizations
import RockafellarWets.Chapter7.EpiLimits
import RockafellarWets.Chapter6.TangentCones

open Filter Set Topology Metric

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Formula 7(24) -/

/-- The epigraph inequality for a difference quotient at a positive scale. -/
theorem differenceQuotient_le_coe_iff {f : E → EReal} {x w : E} {c τ α : ℝ}
    (hx : f x = c) (hτ : 0 < τ) :
    differenceQuotient f x τ w ≤ (α : EReal) ↔ f (x + τ • w) ≤ ((c + τ * α : ℝ) : EReal) := by
  rw [differenceQuotient, hx]
  cases f (x + τ • w) with
  | bot => simp [EReal.bot_sub, EReal.coe_mul_bot_of_pos (inv_pos.2 hτ)]
  | top =>
    rw [EReal.top_sub_coe, EReal.coe_mul_top_of_pos (inv_pos.2 hτ)]
    constructor <;> intro htop
    · exact absurd (top_le_iff.1 htop) (EReal.coe_ne_top α)
    · exact absurd (top_le_iff.1 htop) (EReal.coe_ne_top _)
  | coe r =>
    rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff,
      inv_mul_le_iff₀ hτ]
    constructor <;> intro hr <;> linarith

/-- **Formula 7(24)**: for `τ > 0`, `epi Δ_τ f(x̄) = τ⁻¹(epi f - (x̄, f(x̄)))`. -/
theorem epigraph_differenceQuotient {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c)
    {τ : ℝ} (hτ : 0 < τ) :
    epigraph (differenceQuotient f x τ) = blowUp (epigraph f) (x, c) τ := by
  ext ⟨w, α⟩
  rw [mem_epigraph_iff, differenceQuotient_le_coe_iff hx hτ, mem_blowUp]
  constructor
  · intro h
    refine ⟨(x + τ • w, c + τ * α), (mem_epigraph_iff f _ _).2 h, ?_⟩
    rw [Prod.mk_sub_mk, Prod.smul_mk, add_sub_cancel_left, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ hτ.ne', one_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hτ.ne',
      one_mul]
  · rintro ⟨⟨y, β⟩, hy, hyw⟩
    have hw : τ⁻¹ • (y - x) = w := by
      have := congrArg Prod.fst hyw
      simpa using this
    have hα : τ⁻¹ * (β - c) = α := by
      have := congrArg Prod.snd hyw
      simpa using this
    have h1 : x + τ • w = y := by
      rw [← hw, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, add_sub_cancel]
    have h2 : c + τ * α = β := by
      rw [← hα, ← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul, add_sub_cancel]
    rw [h1, h2]
    exact (mem_epigraph_iff f y β).1 hy

/-- Formula 7(24) as an eventual identity of families along `τ ↓ 0`. -/
theorem epigraph_differenceQuotient_eventuallyEq {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) :
    (fun τ ↦ epigraph (differenceQuotient f x τ)) =ᶠ[𝓝[>] (0 : ℝ)]
      blowUp (epigraph f) (x, c) := by
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact epigraph_differenceQuotient hx hτ

/-- The outer limit of the epigraphs of the difference quotients is the
tangent cone to `epi f` at `(x̄, f(x̄))`. -/
theorem outerSetLimitAlong_epigraph_differenceQuotient {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) :
    outerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (differenceQuotient f x τ)) =
      tangentCone (epigraph f) (x, c) := by
  rw [tangentCone_eq_outerSetLimitAlong,
    outerSetLimitAlong_congr (epigraph_differenceQuotient_eventuallyEq hx)]

/-- The inner limit of the epigraphs of the difference quotients is the
derivable cone of `epi f` at `(x̄, f(x̄))`. -/
theorem innerSetLimitAlong_epigraph_differenceQuotient {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) :
    innerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (differenceQuotient f x τ)) =
      derivableCone (epigraph f) (x, c) := by
  rw [derivableCone_eq_innerSetLimitAlong ((mem_epigraph_iff f x c).2 (le_of_eq hx)),
    innerSetLimitAlong_congr (epigraph_differenceQuotient_eventuallyEq hx)]

/-! ### Epigraphical limits along a filter -/

section UpwardClosed

variable {ι : Type*} {l : Filter ι}

omit [NormedSpace ℝ E] in
/-- Outer limits of epigraphs are closed upward in the height variable. -/
theorem outerSetLimitAlong_epigraph_upward (g : ι → E → EReal) {w : E} {a b : ℝ}
    (ha : (w, a) ∈ outerSetLimitAlong l (fun i ↦ epigraph (g i))) (hab : a ≤ b) :
    (w, b) ∈ outerSetLimitAlong l (fun i ↦ epigraph (g i)) := by
  intro V hV
  have hT : Continuous fun p : E × ℝ ↦ (p.1, p.2 + (b - a)) :=
    continuous_fst.prodMk (continuous_snd.add continuous_const)
  have hV' : (fun p : E × ℝ ↦ (p.1, p.2 + (b - a))) ⁻¹' V ∈ 𝓝 (w, a) := by
    apply hT.continuousAt.preimage_mem_nhds
    simpa using hV
  refine (ha _ hV').mono fun i ⟨p, hp, hpV⟩ ↦ ⟨(p.1, p.2 + (b - a)), ?_, hpV⟩
  exact le_trans hp (EReal.coe_le_coe_iff.2 (by linarith))

omit [NormedSpace ℝ E] in
/-- Inner limits of epigraphs are closed upward in the height variable. -/
theorem innerSetLimitAlong_epigraph_upward (g : ι → E → EReal) {w : E} {a b : ℝ}
    (ha : (w, a) ∈ innerSetLimitAlong l (fun i ↦ epigraph (g i))) (hab : a ≤ b) :
    (w, b) ∈ innerSetLimitAlong l (fun i ↦ epigraph (g i)) := by
  intro V hV
  have hT : Continuous fun p : E × ℝ ↦ (p.1, p.2 + (b - a)) :=
    continuous_fst.prodMk (continuous_snd.add continuous_const)
  have hV' : (fun p : E × ℝ ↦ (p.1, p.2 + (b - a))) ⁻¹' V ∈ 𝓝 (w, a) := by
    apply hT.continuousAt.preimage_mem_nhds
    simpa using hV
  refine (ha _ hV').mono fun i ⟨p, hp, hpV⟩ ↦ ⟨(p.1, p.2 + (b - a)), ?_, hpV⟩
  exact le_trans hp (EReal.coe_le_coe_iff.2 (by linarith))

end UpwardClosed

/-! ### Definition 7.23 -/

/-- Formula 7(10) for `τ ↓ 0`: the lower epi-limit of the difference
quotients, the function whose epigraph is the outer limit of their epigraphs. -/
noncomputable def lowerEpiDerivative (f : E → EReal) (x : E) : E → EReal :=
  epiBoundary (outerSetLimitAlong (𝓝[>] (0 : ℝ)) fun τ ↦ epigraph (differenceQuotient f x τ))

/-- Formula 7(10) for `τ ↓ 0`: the upper epi-limit of the difference
quotients, the function whose epigraph is the inner limit of their epigraphs. -/
noncomputable def upperEpiDerivative (f : E → EReal) (x : E) : E → EReal :=
  epiBoundary (innerSetLimitAlong (𝓝[>] (0 : ℝ)) fun τ ↦ epigraph (differenceQuotient f x τ))

theorem epigraph_lowerEpiDerivative (f : E → EReal) (x : E) :
    epigraph (lowerEpiDerivative f x) =
      outerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (differenceQuotient f x τ)) :=
  epigraph_epiBoundary (isClosed_outerSetLimitAlong _ _)
    fun _ _ _ ha hab ↦ outerSetLimitAlong_epigraph_upward _ ha hab

theorem epigraph_upperEpiDerivative (f : E → EReal) (x : E) :
    epigraph (upperEpiDerivative f x) =
      innerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (differenceQuotient f x τ)) :=
  epigraph_epiBoundary (isClosed_innerSetLimitAlong _ _)
    fun _ _ _ ha hab ↦ innerSetLimitAlong_epigraph_upward _ ha hab

/-- The lower epi-limit never exceeds the upper one. -/
theorem lowerEpiDerivative_le_upperEpiDerivative (f : E → EReal) (x : E) :
    lowerEpiDerivative f x ≤ upperEpiDerivative f x := by
  rw [← epigraph_subset_epigraph_iff, epigraph_lowerEpiDerivative, epigraph_upperEpiDerivative]
  exact innerSetLimitAlong_subset_outerSetLimitAlong _

/-- **Definition 7.23**, formulas 7(23) and 7(11): `β` is the epi-derivative of
`f` at `x̄` for `w` when the lower and upper epi-limits of the difference
quotients at `w` both equal `β`. -/
def HasEpiDerivative (f : E → EReal) (x w : E) (β : EReal) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ lowerEpiDerivative f x w = β ∧ upperEpiDerivative f x w = β

/-- **Definition 7.23**: `f` is epi-differentiable at `x̄` for `w`. -/
def EpiDifferentiableFor (f : E → EReal) (x w : E) : Prop :=
  ∃ β, HasEpiDerivative f x w β

/-- **Definition 7.23**: `f` is epi-differentiable at `x̄` when the difference
quotients epi-converge on the whole space as `τ ↓ 0`, i.e. their epigraphs
converge to the epigraph of some function. -/
def EpiDifferentiableAt (f : E → EReal) (x : E) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∃ h : E → EReal,
    PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (differenceQuotient f x τ)) (epigraph h)

/-- **Definition 7.23**: `f` is properly epi-differentiable at `x̄` when the
epi-limit function is proper. -/
def ProperlyEpiDifferentiableAt (f : E → EReal) (x : E) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∃ h : E → EReal, IsProper h ∧
    PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (differenceQuotient f x τ)) (epigraph h)

/-- Definition 7.23: epi-convergence on the whole space is epi-differentiability
for every `w`, the limit being the common epi-limit function. -/
theorem epiDifferentiableAt_iff_forall {f : E → EReal} {x : E} :
    EpiDifferentiableAt f x ↔ f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∀ w, EpiDifferentiableFor f x w := by
  constructor
  · rintro ⟨hx, hx', h, hin, hout⟩
    have hl : lowerEpiDerivative f x = h :=
      eq_of_epigraph_eq (by rw [epigraph_lowerEpiDerivative, hout])
    have hu : upperEpiDerivative f x = h :=
      eq_of_epigraph_eq (by rw [epigraph_upperEpiDerivative, hin])
    exact ⟨hx, hx', fun w ↦ ⟨h w, hx, hx', congrFun hl w, congrFun hu w⟩⟩
  · rintro ⟨hx, hx', hall⟩
    have heq : lowerEpiDerivative f x = upperEpiDerivative f x := by
      funext w
      obtain ⟨β, -, -, hl, hu⟩ := hall w
      rw [hl, hu]
    refine ⟨hx, hx', lowerEpiDerivative f x, ?_, (epigraph_lowerEpiDerivative f x).symm⟩
    rw [← epigraph_upperEpiDerivative, heq]

/-! ### The lower epi-limit is `df(x̄)` -/

/-- The epigraph of `df(x̄)` (formula 7(21)) is the outer limit of the
epigraphs of the difference quotients. -/
theorem mem_outerSetLimitAlong_epigraph_iff (f : E → EReal) (x w : E) (α : ℝ) :
    (w, α) ∈ outerSetLimitAlong (𝓝[>] (0 : ℝ))
        (fun τ ↦ epigraph (differenceQuotient f x τ)) ↔
      subderivative f x w ≤ α := by
  constructor
  · intro hmem
    by_contra hlt
    push_neg at hlt
    obtain ⟨b, hαb, hb⟩ := EReal.exists_between_coe_real hlt
    have hev : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (b : EReal) < differenceQuotient f x p.1 p.2 :=
      eventually_lt_of_lt_liminf hb
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hev
    have hN : V ×ˢ Iio b ∈ 𝓝 (w, α) :=
      prod_mem_nhds hV (Iio_mem_nhds (EReal.coe_lt_coe_iff.1 hαb))
    obtain ⟨τ, ⟨⟨w', β⟩, hep, hw'V, hβ⟩, hτU⟩ := ((hmem _ hN).and_eventually hU).exists
    have h1 : (b : EReal) < differenceQuotient f x τ w' :=
      hUV (show (τ, w') ∈ U ×ˢ V from ⟨hτU, hw'V⟩)
    have h2 : differenceQuotient f x τ w' ≤ (β : EReal) := hep
    have h3 : (β : EReal) < (b : EReal) := EReal.coe_lt_coe_iff.2 hβ
    exact lt_irrefl _ (h1.trans_le (h2.trans h3.le))
  · intro hle N hN
    obtain ⟨V, hV, I, hI, hVI⟩ := mem_nhds_prod_iff.1 hN
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hI
    have hα' : α + ε / 2 ∈ I := hball (by
      rw [mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
      linarith)
    have hfreq : ∃ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
        differenceQuotient f x p.1 p.2 < ((α + ε / 2 : ℝ) : EReal) :=
      frequently_lt_of_liminf_lt (h := hle.trans_lt (EReal.coe_lt_coe_iff.2 (by linarith)))
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨p, hp, hpUV⟩ := (hfreq.and_eventually (prod_mem_prod hU hV)).exists
    exact ⟨p.1, hpUV.1, (p.2, α + ε / 2), le_of_lt hp, hVI ⟨hpUV.2, hα'⟩⟩

/-- The epigraph of `df(x̄)` is the outer limit of the epigraphs of the
difference quotients. -/
theorem epigraph_subderivative (f : E → EReal) (x : E) :
    epigraph (subderivative f x) =
      outerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (differenceQuotient f x τ)) := by
  ext ⟨w, α⟩
  rw [mem_epigraph_iff, mem_outerSetLimitAlong_epigraph_iff]

/-- The lower epi-limit of the difference quotients is `df(x̄)`, formula 7(21);
in particular an epi-derivative, when it exists, equals `df(x̄)(w)`. -/
theorem lowerEpiDerivative_eq_subderivative (f : E → EReal) (x : E) :
    lowerEpiDerivative f x = subderivative f x :=
  eq_of_epigraph_eq (by rw [epigraph_lowerEpiDerivative, epigraph_subderivative])

/-- The paragraph after Definition 7.23: an epi-derivative coincides with
`df(x̄)(w)`. -/
theorem HasEpiDerivative.subderivative_eq {f : E → EReal} {x w : E} {β : EReal}
    (h : HasEpiDerivative f x w β) : subderivative f x w = β := by
  rw [← lowerEpiDerivative_eq_subderivative]
  exact h.2.2.1

/-- `epi df(x̄) = T_{epi f}(x̄, f(x̄))` at every point where `f` is finite
(the epigraphical reading of 7.24, valid without epi-differentiability). -/
theorem epigraph_subderivative_eq_tangentCone {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) :
    epigraph (subderivative f x) = tangentCone (epigraph f) (x, c) := by
  rw [epigraph_subderivative, outerSetLimitAlong_epigraph_differenceQuotient hx]

/-- The upper epi-limit has the derivable cone of `epi f` as its epigraph. -/
theorem epigraph_upperEpiDerivative_eq_derivableCone {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) :
    epigraph (upperEpiDerivative f x) = derivableCone (epigraph f) (x, c) := by
  rw [epigraph_upperEpiDerivative, innerSetLimitAlong_epigraph_differenceQuotient hx]

/-! ### Proposition 7.24 -/

/-- **Proposition 7.24**: `f` is epi-differentiable at `x̄` if and only if
`epi f` is geometrically derivable at `(x̄, f(x̄))`. -/
theorem epiDifferentiableAt_iff_isGeometricallyDerivable {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) :
    EpiDifferentiableAt f x ↔ IsGeometricallyDerivable (epigraph f) (x, c) := by
  have hx1 : f x ≠ ⊥ := by rw [hx]; exact EReal.coe_ne_bot c
  have hx2 : f x ≠ ⊤ := by rw [hx]; exact EReal.coe_ne_top c
  rw [isGeometricallyDerivable_iff ((mem_epigraph_iff f x c).2 (le_of_eq hx)),
    ← outerSetLimitAlong_congr (epigraph_differenceQuotient_eventuallyEq hx),
    ← innerSetLimitAlong_congr (epigraph_differenceQuotient_eventuallyEq hx)]
  constructor
  · rintro ⟨-, -, h, hin, hout⟩
    rw [hin, hout]
  · intro heq
    refine ⟨hx1, hx2, lowerEpiDerivative f x, ?_, (epigraph_lowerEpiDerivative f x).symm⟩
    rw [epigraph_lowerEpiDerivative, heq]

/-- **Proposition 7.24**, second clause: when `f` is epi-differentiable at
`x̄`, the epi-derivative function has `T_{epi f}(x̄, f(x̄))` as its epigraph. -/
theorem epigraph_eq_tangentCone_of_pkConvergesAlong {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) {h : E → EReal}
    (hconv : PKConvergesAlong (𝓝[>] (0 : ℝ))
      (fun τ ↦ epigraph (differenceQuotient f x τ)) (epigraph h)) :
    epigraph h = tangentCone (epigraph f) (x, c) := by
  rw [← hconv.outer_eq, outerSetLimitAlong_epigraph_differenceQuotient hx]

/-- **Proposition 7.24**, second clause, in function form: the epi-derivative
function is `df(x̄)`. -/
theorem eq_subderivative_of_pkConvergesAlong {f : E → EReal} {x : E} {h : E → EReal}
    (hconv : PKConvergesAlong (𝓝[>] (0 : ℝ))
      (fun τ ↦ epigraph (differenceQuotient f x τ)) (epigraph h)) :
    h = subderivative f x :=
  eq_of_epigraph_eq (by rw [epigraph_subderivative, hconv.outer_eq])

/-- At a point of epi-differentiability, `df(x̄)` is an epi-derivative for
every `w`. -/
theorem EpiDifferentiableAt.hasEpiDerivative {f : E → EReal} {x : E}
    (h : EpiDifferentiableAt f x) (w : E) :
    HasEpiDerivative f x w (subderivative f x w) := by
  obtain ⟨-, -, hall⟩ := epiDifferentiableAt_iff_forall.1 h
  obtain ⟨β, hβ⟩ := hall w
  rwa [hβ.subderivative_eq]

/-! ### Semiderivatives are epi-derivatives -/

/-- A height above the limit of the quotients along the ray through `w`
puts `(w, α)` in the inner limit of the epigraphs. -/
theorem mem_innerSetLimitAlong_epigraph_of_eventually {f : E → EReal} {x w : E} {α : ℝ}
    (h : ∀ᶠ τ in 𝓝[>] (0 : ℝ), differenceQuotient f x τ w ≤ α) :
    (w, α) ∈ innerSetLimitAlong (𝓝[>] (0 : ℝ))
      (fun τ ↦ epigraph (differenceQuotient f x τ)) :=
  fun _ hN ↦ h.mono fun _ hτ ↦ ⟨(w, α), hτ, mem_of_mem_nhds hN⟩

/-- The paragraph after Definition 7.23: if `f` is semidifferentiable at `x̄`
for `w`, it is also epi-differentiable for `w`, with the same value. -/
theorem HasSemiderivative.hasEpiDerivative {f : E → EReal} {x w : E} {β : EReal}
    (h : HasSemiderivative f x w β) : HasEpiDerivative f x w β := by
  have hl : lowerEpiDerivative f x w = β := by
    rw [lowerEpiDerivative_eq_subderivative, h.subderivative_eq]
  refine ⟨h.1, h.2.1, hl, le_antisymm ?_
    ((le_of_eq hl.symm).trans (lowerEpiDerivative_le_upperEpiDerivative f x w))⟩
  by_contra hlt
  push_neg at hlt
  obtain ⟨α, hβα, hαu⟩ := EReal.exists_between_coe_real hlt
  have hray := h.hasOneSidedDirDeriv.2.2
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), differenceQuotient f x τ w ≤ α :=
    (hray.eventually (gt_mem_nhds hβα)).mono fun _ hτ ↦ hτ.le
  have hmem := mem_innerSetLimitAlong_epigraph_of_eventually hev
  rw [← epigraph_upperEpiDerivative, mem_epigraph_iff] at hmem
  exact absurd hmem (not_le.2 hαu)

/-- The paragraph after Definition 7.23: a function semidifferentiable at `x̄`
is properly epi-differentiable there. -/
theorem SemidifferentiableAt.properlyEpiDifferentiableAt {f : E → EReal} {x : E}
    (hs : SemidifferentiableAt f x) : ProperlyEpiDifferentiableAt f x := by
  obtain ⟨g, -, -, hall⟩ := hs.exists_semiderivative
  have hx := (hall 0).1.1
  have hx' := (hall 0).1.2.1
  have hepi : EpiDifferentiableAt f x :=
    epiDifferentiableAt_iff_forall.2 ⟨hx, hx', fun w ↦ ⟨_, (hall w).1.hasEpiDerivative⟩⟩
  obtain ⟨-, -, h, hconv⟩ := hepi
  have hh : h = fun w ↦ (g w : EReal) := by
    rw [eq_subderivative_of_pkConvergesAlong hconv]
    funext w
    exact (hall w).2.1
  refine ⟨hx, hx', h, ?_, hconv⟩
  rw [hh]
  exact ⟨⟨0, EReal.coe_lt_top _⟩, fun w ↦ EReal.bot_lt_coe _⟩

end RW
