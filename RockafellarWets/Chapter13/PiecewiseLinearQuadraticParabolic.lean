/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Parabolic subderivatives of piecewise linear-quadratic functions

Exercise 13.61.  In the local conical model of a piecewise linear-quadratic function `f` around
`x̄` (`PLQLocalModel`), with `h₁ = df(x̄)` and `h₂ = d²f(x̄)`, the parabolic quotients are

  `Δ²_τ f(x̄)(w | z) = Δ_{τ/2} h₁(w)(z) + h₂(w + (τ/2)z)`

for `w ∈ dom h₁` and small `τ` (`PLQLocalModel.parabolicDifferenceQuotient_eq`).  For convex `f`,
`h₁` is the support function of `∂f(x̄)`, so `dh₁(w) = σ_{∂f(x̄ | w)}` with
`∂f(x̄ | w) = argmax_{v ∈ ∂f(x̄)} ⟪v, w⟫` (Corollary 8.25).  The lower bound
`d²f(x̄)(w | z) ≥ d²f(x̄)(w) + ⟪v, z⟫` for `v ∈ ∂f(x̄ | w)` is 13(39) combined with 13.9, and the
upper bound and parabolic epi-differentiability come from the limits along the constant path
`z' = z`.
-/

import RockafellarWets.Chapter13.PiecewiseLinearQuadraticSecondOrder
import RockafellarWets.Chapter13.ParabolicSubderivatives
import RockafellarWets.Chapter10.PLQCalculus
import RockafellarWets.Chapter8.SupportSubgradients

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- Convergence along constant paths at the points where the limit function is finite puts its
epigraph inside the inner limit of the epigraphs. -/
theorem epigraph_subset_innerSetLimitAlong_of_tendsto_of_lt_top {ι : Type*} {l : Filter ι}
    {g : ι → E → EReal} {G : E → EReal}
    (hg : ∀ z, G z < ⊤ → Tendsto (fun i ↦ g i z) l (𝓝 (G z))) :
    epigraph G ⊆ innerSetLimitAlong l (fun i ↦ epigraph (g i)) := by
  rintro ⟨z, α⟩ hzα N hN
  change G z ≤ (α : EReal) at hzα
  obtain ⟨V, hV, I, hI, hVI⟩ := mem_nhds_prod_iff.1 hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hI
  have hlt : G z < ((α + ε / 2 : ℝ) : EReal) :=
    lt_of_le_of_lt hzα (EReal.coe_lt_coe_iff.2 (by linarith))
  filter_upwards [(hg z (lt_of_le_of_lt hzα (EReal.coe_lt_top α))).eventually (Iio_mem_nhds hlt)]
    with i hi
  refine ⟨(z, α + ε / 2), le_of_lt hi, hVI ⟨mem_of_mem_nhds hV, hball ?_⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hε)]
  linarith

namespace PLQLocalModel

variable {f : E → EReal} {x : E} (M : PLQLocalModel f x)

/-- **Exercise 13.61**: in the model, `Δ²_τ f(x̄)(w | z) = Δ_{τ/2} h₁(w)(z) + h₂(w + (τ/2)z)` for
`w ∈ dom h₁` and `τ‖w + (τ/2)z‖ < δ`, with `h₁ = df(x̄)` and `h₂ = d²f(x̄)`. -/
theorem parabolicDifferenceQuotient_eq [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) {w : E} (hw : w ∈ M.coneUnion) {τ : ℝ} (hτ : 0 < τ) {z : E}
    (hτz : τ * ‖w + (τ / 2) • z‖ < M.radius) :
    parabolicDifferenceQuotient f x w τ z =
      differenceQuotient (subderivative f x) w (τ / 2) z + M.secondForm (w + (τ / 2) • z) := by
  obtain ⟨j, hj⟩ := M.mem_coneUnion.1 hw
  have hdj := M.subderivative_eq hf hx hj
  have hstep : x + τ • w + (τ ^ 2 / 2) • z = x + τ • (w + (τ / 2) • z) := by
    rw [smul_add, smul_smul, add_assoc]
    congr 3
    ring
  have hτ2 : (0 : ℝ) < τ / 2 := by positivity
  rw [parabolicDifferenceQuotient_of_subderivative_eq hdj, hstep]
  by_cases hU : w + (τ / 2) • z ∈ M.coneUnion
  · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hU
    have hbase : (M.piece i).eval x = (M.piece j).eval x := by
      have := (M.eq_eval_base ⟨_, hi⟩).symm.trans (M.eq_eval_base ⟨w, hj⟩)
      exact_mod_cast this
    rw [M.eq_expansion hi hτ hτz, M.eq_eval_base ⟨w, hj⟩,
      differenceQuotient_eq_coe hdj (M.subderivative_eq hf hx hi), M.secondForm_eq hf hx hi,
      ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff,
      hbase]
    generalize ⟪M.grad i, w + (τ / 2) • z⟫_ℝ = A
    generalize ⟪w + (τ / 2) • z, (M.piece i).matrix (w + (τ / 2) • z)⟫_ℝ = B
    field_simp
    ring
  · rw [M.eq_top_of_not_mem hU hτ hτz, M.eq_eval_base ⟨w, hj⟩, EReal.top_sub_coe,
      EReal.top_sub_coe, EReal.coe_mul_top_of_pos (by positivity),
      differenceQuotient_eq_top hτ2 hdj (M.subderivative_eq_top hf hx hU),
      M.secondForm_eq_top hU, EReal.top_add_top]

/-- Along a fixed direction, the parabolic quotients converge to `dh₁(w)(z) + h₂(w)` whenever
`dh₁(w)(z)` is finite. -/
theorem tendsto_parabolicDifferenceQuotient [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f) {w : E}
    (hw : w ∈ M.coneUnion) (z : E) (hz : subderivative (subderivative f x) w z < ⊤) :
    Tendsto (fun τ ↦ parabolicDifferenceQuotient f x w τ z) (𝓝[>] (0 : ℝ))
      (𝓝 (subderivative (subderivative f x) w z + M.secondForm w)) := by
  have hplq₁ : IsPiecewiseLinearQuadratic (subderivative f x) :=
    (hf.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic
  have hplq₂ := M.isPiecewiseLinearQuadratic_secondForm hf hx
  have hw₁ : w ∈ effectiveDomain (subderivative f x) := by
    rw [M.effectiveDomain_subderivative hf hx]; exact hw
  have hw₂ : w ∈ effectiveDomain M.secondForm := by
    rw [M.effectiveDomain_secondForm hf hx]; exact hw
  have hne₁ : subderivative (subderivative f x) w z ≠ ⊥ :=
    (hplq₁.subderivative_piecewiseLinear hw₁).1.isPiecewiseLinearQuadratic.ne_bot z
  have hhalf : Tendsto (fun τ : ℝ ↦ (1 / 2 : ℝ) * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_const_mul_nhdsGT_zero (by norm_num)
  have hA := (hplq₁.hasOneSidedDirDeriv hw₁ z).2.2.comp hhalf
  -- eventually `h₁(w + (τ/2)z) < ∞`, so the second argument stays in `dom h₂`
  have hfinA : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      differenceQuotient (subderivative f x) w ((1 / 2 : ℝ) * τ) z < ⊤ :=
    hA.eventually (Iio_mem_nhds hz)
  have hpath : Tendsto (fun τ : ℝ ↦ w + (τ / 2) • z) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    have : Tendsto (fun τ : ℝ ↦ w + (τ / 2) • z) (𝓝 (0 : ℝ)) (𝓝 (w + ((0 : ℝ) / 2) • z)) :=
      (continuous_const.add ((continuous_id.div_const 2).smul continuous_const)).tendsto 0
    rw [zero_div, zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hdom : ∀ᶠ τ in 𝓝[>] (0 : ℝ), w + (τ / 2) • z ∈ effectiveDomain M.secondForm := by
    filter_upwards [hfinA, self_mem_nhdsWithin] with τ hτ hτpos
    rw [M.effectiveDomain_secondForm hf hx, ← M.effectiveDomain_subderivative hf hx]
    have hτ' : (0 : ℝ) < 1 / 2 * τ := by have : (0 : ℝ) < τ := hτpos; positivity
    rw [mem_effectiveDomain_iff]
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    have hw1 : subderivative f x w = (((subderivative f x w).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (ne_of_lt hw₁) (hplq₁.ne_bot w)).symm
    have h2 : w + ((1 / 2 : ℝ) * τ) • z = w + (τ / 2) • z := by congr 1; ring_nf
    rw [differenceQuotient_eq_top hτ' hw1 (by rw [h2]; exact hcon)] at hτ
    exact lt_irrefl _ hτ
  have hB : Tendsto (fun τ ↦ M.secondForm (w + (τ / 2) • z)) (𝓝[>] (0 : ℝ))
      (𝓝 (M.secondForm w)) :=
    (hplq₂.continuousOn w hw₂).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hpath, hdom⟩)
  have hne₂ : M.secondForm w ≠ ⊥ := M.secondForm_ne_bot w
  have hsum := (EReal.continuousAt_add (Or.inr hne₂) (Or.inl hne₁)).tendsto.comp
    (hA.prodMk_nhds hB)
  refine hsum.congr' ?_
  have hsmall : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), τ * ‖w + (τ / 2) • z‖ < M.radius := by
    have h : Tendsto (fun τ : ℝ ↦ τ * ‖w + (τ / 2) • z‖) (𝓝 (0 : ℝ))
        (𝓝 (0 * ‖w + ((0 : ℝ) / 2) • z‖)) := by
      have hc : Continuous (fun τ : ℝ ↦ τ * ‖w + (τ / 2) • z‖) := by fun_prop
      exact hc.tendsto 0
    rw [zero_mul] at h
    exact (h.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds M.radius_pos)
  filter_upwards [hsmall, self_mem_nhdsWithin] with τ hτz hτ
  rw [Function.comp_apply, M.parabolicDifferenceQuotient_eq hf hx hw hτ hτz]
  simp only [Function.comp_apply]
  congr 2
  ring

/-- `d²f(x̄)` is positively homogeneous of degree 2 on the model. -/
theorem secondForm_smul [FiniteDimensional ℝ E] (hf : IsPiecewiseLinearQuadratic f)
    (hx : x ∈ effectiveDomain f) (u : E) {s : ℝ} (hs : 0 < s) :
    M.secondForm (s • u) = ((s ^ 2 : ℝ) : EReal) * M.secondForm u := by
  by_cases hu : u ∈ M.coneUnion
  · obtain ⟨i, hi⟩ := M.mem_coneUnion.1 hu
    rw [M.secondForm_eq hf hx (M.smul_mem_cone hi hs), M.secondForm_eq hf hx hi, ← EReal.coe_mul,
      map_smul, real_inner_smul_left, real_inner_smul_right]
    congr 1
    ring
  · have hsu : s • u ∉ M.coneUnion := by rwa [M.smul_mem_coneUnion_iff hs]
    rw [M.secondForm_eq_top hsu, M.secondForm_eq_top hu, EReal.coe_mul_top_of_pos (by positivity)]

include M in
/-- Piecewise linear-quadratic functions are semidifferentiable relative to their domain: if
`s ↓ 0`, `ζ_s → ζ̄` and `x̄ + sζ_s ∈ dom f`, then `Δ_s f(x̄)(ζ_s) → df(x̄)(ζ̄)`. -/
theorem tendsto_differenceQuotient_of_mem_dom [FiniteDimensional ℝ E]
    (hf : IsPiecewiseLinearQuadratic f) (hx : x ∈ effectiveDomain f) {ι : Type*} {l : Filter ι}
    [l.NeBot] {s : ι → ℝ} {ζ : ι → E} {ζ₀ : E} (hs : Tendsto s l (𝓝[>] (0 : ℝ))) (hζ : Tendsto ζ l (𝓝 ζ₀))
    (hdom : ∀ᶠ i in l, x + s i • ζ i ∈ effectiveDomain f) :
    Tendsto (fun i ↦ differenceQuotient f x (s i) (ζ i)) l (𝓝 (subderivative f x ζ₀)) := by
  obtain ⟨i₀, hi₀⟩ := M.exists_mem_cone_zero hx
  have hc := M.eq_eval_base ⟨0, hi₀⟩
  have hd := (hf.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic
  have hq := M.isPiecewiseLinearQuadratic_secondForm hf hx
  have hspos : ∀ᶠ i in l, 0 < s i := hs.eventually self_mem_nhdsWithin
  have hs0 : Tendsto s l (𝓝 0) := hs.mono_right nhdsWithin_le_nhds
  have hsmall : ∀ᶠ i in l, ‖s i • ζ i‖ < M.radius := by
    have h : Tendsto (fun i ↦ s i • ζ i) l (𝓝 ((0 : ℝ) • ζ₀)) := hs0.smul hζ
    rw [zero_smul] at h
    exact h.eventually ((continuous_norm.tendsto (0 : E)).eventually
      (gt_mem_nhds (by rw [norm_zero]; exact M.radius_pos)))
  -- the directions stay in `⋃ Kᵢ`, the common domain of `df(x̄)` and `d²f(x̄)`
  have hmem : ∀ᶠ i in l, ζ i ∈ M.coneUnion := by
    filter_upwards [hdom, hsmall, hspos] with i h1 h2 h3
    obtain ⟨j, hj⟩ := (M.dom_iff _ h2).1 h1
    exact M.mem_coneUnion.2 ⟨j, M.mem_cone_of_smul_mem h3 hj⟩
  have hζ₀ : ζ₀ ∈ M.coneUnion := M.isClosed_coneUnion.mem_of_tendsto hζ hmem
  have hdomd : effectiveDomain (subderivative f x) = M.coneUnion :=
    M.effectiveDomain_subderivative hf hx
  have hdomq : effectiveDomain M.secondForm = M.coneUnion := M.effectiveDomain_secondForm hf hx
  have hζd : Tendsto ζ l (𝓝[effectiveDomain (subderivative f x)] ζ₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hζ, by rw [hdomd]; exact hmem⟩
  have hζq : Tendsto ζ l (𝓝[effectiveDomain M.secondForm] ζ₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hζ, by rw [hdomq]; exact hmem⟩
  have h1 := (hd.continuousOn ζ₀ (by rw [hdomd]; exact hζ₀)).tendsto.comp hζd
  have h2 := (hq.continuousOn ζ₀ (by rw [hdomq]; exact hζ₀)).tendsto.comp hζq
  obtain ⟨j₀, hj₀⟩ := M.mem_coneUnion.1 hζ₀
  have hfin₁ : subderivative f x ζ₀ ≠ ⊥ ∧ subderivative f x ζ₀ ≠ ⊤ := by
    rw [M.subderivative_eq hf hx hj₀]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  have hfin₂ : M.secondForm ζ₀ ≠ ⊥ ∧ M.secondForm ζ₀ ≠ ⊤ := by
    rw [M.secondForm_eq hf hx hj₀]; exact ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩
  have h1r := (EReal.tendsto_toReal hfin₁.2 hfin₁.1).comp h1
  have h2r := (EReal.tendsto_toReal hfin₂.2 hfin₂.1).comp h2
  have hsum : Tendsto (fun i ↦ (subderivative f x (ζ i)).toReal +
      s i / 2 * (M.secondForm (ζ i)).toReal) l
      (𝓝 ((subderivative f x ζ₀).toReal + 0 / 2 * (M.secondForm ζ₀).toReal)) :=
    h1r.add ((hs0.div_const 2).mul h2r)
  rw [zero_div, zero_mul, add_zero] at hsum
  rw [← EReal.coe_toReal hfin₁.2 hfin₁.1]
  refine ((continuous_coe_real_ereal.tendsto _).comp hsum).congr' ?_
  filter_upwards [hdom, hsmall, hspos, hmem] with i h1 h2 h3 h4
  obtain ⟨j, hj⟩ := M.mem_coneUnion.1 h4
  have hexp := M.eq_expansion hj h3 (by rwa [norm_smul, Real.norm_of_nonneg h3.le] at h2)
  rw [Function.comp_apply, differenceQuotient_eq_coe (M.eq_eval_base ⟨_, hj⟩) hexp,
    M.subderivative_eq hf hx hj, M.secondForm_eq hf hx hj, EReal.toReal_coe, EReal.toReal_coe]
  congr 1
  field_simp
  ring

end PLQLocalModel

/-- **Exercise 13.61** (parabolic aspects of piecewise linear-quadratic functions).  Let `f` be
convex and piecewise linear-quadratic, `x̄ ∈ dom f` and `w ∈ dom df(x̄)`.  Then `f` is parabolically
epi-differentiable at `x̄` for `w`, and
`d²f(x̄)(w | z) = d²f(x̄)(w) + σ_{∂f(x̄ | w)}(z)` with
`∂f(x̄ | w) = {v ∈ ∂f(x̄) | df(x̄)(w) = ⟪v, w⟫} = argmax_{v ∈ ∂f(x̄)} ⟪v, w⟫`; in particular
`d²f(x̄)(w | z) < ∞` exactly when `z ∈ T_K(w)` for `K = dom df(x̄)`. -/
theorem parabolic_aspects_of_piecewise_linear_quadratic [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hc : Convex ℝ (epigraph f)) {x : E}
    (hx : x ∈ effectiveDomain f) {w : E} (hw : w ∈ effectiveDomain (subderivative f x)) :
    IsParabolicallyEpiDifferentiableAt f x w ∧
    (∀ z, parabolicSubderivative f x w z = secondSubderivativeAt f x w +
      supportFunction
        {v ∈ subdifferential f x | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} z) ∧
    {v ∈ subdifferential f x | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} =
      {v ∈ subdifferential f x | ∀ v' ∈ subdifferential f x, ⟪v', w⟫_ℝ ≤ ⟪v, w⟫_ℝ} ∧
    (∀ z, parabolicSubderivative f x w z < ⊤ ↔
      z ∈ tangentCone (effectiveDomain (subderivative f x)) w) := by
  obtain ⟨M⟩ := hf.nonempty_localModel x
  have hh₂ : secondSubderivativeAt f x = M.secondForm := funext (M.secondSubderivativeAt_eq hf hx)
  have hfin : f x = ((f x).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (hf.ne_bot x)).symm
  have hp : IsProper f := ⟨⟨x, hx⟩, fun y ↦ lt_of_le_of_ne bot_le (hf.ne_bot y).symm⟩
  have hw' : w ∈ M.coneUnion := by rwa [← M.effectiveDomain_subderivative hf hx]
  have hplq₁ : IsPiecewiseLinearQuadratic (subderivative f x) :=
    (hf.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic
  set D := subdifferential f x with hD
  obtain ⟨hDne, hDpoly, -⟩ := hf.convex_subgradient_properties hc hx
  have hsupp : subderivative f x = supportFunction D := hf.subderivative_eq_support hc hx
  have hconv₁ : Convex ℝ (epigraph (subderivative f x)) := by
    rw [hsupp]; exact convex_epigraph_of_sublinear (sublinear_supportFunction D)
  -- `dh₁(w) = σ_{∂f(x̄ | w)}`
  set Dw := {v ∈ D | subderivative f x w = ((⟪v, w⟫_ℝ : ℝ) : EReal)} with hDw
  have hsub₁ : subdifferential (subderivative f x) w = Dw := by
    rw [hsupp, subdifferential_supportFunction hDpoly.convex hDpoly.isClosed hDne
      (by rw [← hsupp]; exact hw), hDw, hsupp]
    ext v
    simp only [mem_setOf_eq]
    exact and_congr_right fun _ ↦ eq_comm
  have hdh₁ : subderivative (subderivative f x) w = supportFunction Dw := by
    rw [← hsub₁]; exact hplq₁.subderivative_eq_support hconv₁ hw
  -- the value `h₂(w)` is finite
  obtain ⟨j, hj⟩ := M.mem_coneUnion.1 hw'
  set c₂ := ⟪w, (M.piece j).matrix w⟫_ℝ with hc₂
  have hq : M.secondForm w = (c₂ : EReal) := M.secondForm_eq hf hx hj
  -- lower bound via 13(39) and 13.9
  have hlow : ∀ z, M.secondForm w + supportFunction Dw z ≤ parabolicSubderivative f x w z := by
    intro z
    rw [hq, add_comm, ← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _)), supportFunction_le_iff]
    intro v hv
    have hv' := inner_le_subderivative_of_convex hp hc hfin hv.1
    have h1 := secondSubderivative_le_parabolicSubderivative_sub_inner hfin hv.2 z
    rw [M.secondSubderivative_eq hf hx hv', if_pos hv.2, hq] at h1
    rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
      at h1 ⊢
    rwa [add_comm]
  -- upper bound along the constant path
  have hup : ∀ z, supportFunction Dw z < ⊤ →
      Tendsto (fun τ ↦ parabolicDifferenceQuotient f x w τ z) (𝓝[>] (0 : ℝ))
        (𝓝 (M.secondForm w + supportFunction Dw z)) := by
    intro z hz
    have := M.tendsto_parabolicDifferenceQuotient hf hx hw' z (by rwa [hdh₁])
    rwa [hdh₁, add_comm] at this
  have hval : ∀ z, parabolicSubderivative f x w z = M.secondForm w + supportFunction Dw z := by
    intro z
    refine le_antisymm ?_ (hlow z)
    by_cases hz : supportFunction Dw z < ⊤
    · have ht : Tendsto (fun τ : ℝ ↦ (τ, z)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) :=
        tendsto_id.prodMk tendsto_const_nhds
      calc parabolicSubderivative f x w z
          ≤ liminf ((fun p : ℝ × E ↦ parabolicDifferenceQuotient f x w p.1 p.2) ∘
              fun τ : ℝ ↦ (τ, z)) (𝓝[>] (0 : ℝ)) := by
            rw [parabolicSubderivative, liminf_comp]
            exact liminf_le_liminf_of_le ht
        _ = M.secondForm w + supportFunction Dw z := (hup z hz).liminf_eq
    · rw [not_lt, top_le_iff] at hz
      rw [hz, hq, EReal.coe_add_top]
      exact le_top
  have hdom₁ := (hplq₁.subderivative_piecewiseLinear hw).2
  refine ⟨?_, fun z ↦ by rw [hh₂, hval], ?_, fun z ↦ ?_⟩
  · -- parabolic epi-differentiability
    have hw1 : subderivative f x w ≠ ⊤ := ne_of_lt hw
    refine ⟨by rw [hfin]; exact EReal.coe_ne_bot _, by rw [hfin]; exact EReal.coe_ne_top _,
      hplq₁.ne_bot w, hw1, ⟨0, ?_⟩, ?_, ?_⟩
    · rw [hval, ← hdh₁]
      have h0 := (hplq₁.hasOneSidedDirDeriv hw 0).2.2
      have hw1' : subderivative f x w = (((subderivative f x w).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal hw1 (hplq₁.ne_bot w)).symm
      have h00 : subderivative (subderivative f x) w 0 = 0 := by
        refine tendsto_nhds_unique h0 (tendsto_const_nhds.congr' ?_)
        filter_upwards with τ
        rw [differenceQuotient_zero_right hw1']
      rw [h00, add_zero, hq]
      exact EReal.coe_lt_top _
    · refine Subset.antisymm ?_ ?_
      · exact (innerSetLimitAlong_subset_outerSetLimitAlong _).trans
          (epigraph_parabolicSubderivative f x w).symm.subset
      · refine epigraph_subset_innerSetLimitAlong_of_tendsto_of_lt_top fun z hz ↦ ?_
        rw [hval] at hz ⊢
        refine hup z ?_
        rw [hq] at hz
        by_contra hcon
        rw [not_lt, top_le_iff] at hcon
        rw [hcon, EReal.coe_add_top] at hz
        exact lt_irrefl _ hz
    · exact (epigraph_parabolicSubderivative f x w).symm
  · -- `∂f(x̄ | w)` is the argmax set
    ext v
    simp only [hDw, mem_setOf_eq]
    refine and_congr_right fun hvD ↦ ?_
    rw [hsupp]
    constructor
    · intro heq v' hv'
      exact EReal.coe_le_coe_iff.1 ((inner_le_supportFunction hv' w).trans_eq heq)
    · intro hmax
      exact le_antisymm ((supportFunction_le_iff _ _ _).2 fun v' hv' ↦
        EReal.coe_le_coe_iff.2 (hmax v' hv')) (inner_le_supportFunction hvD w)
  · rw [hval, hq, ← hdh₁, ← hdom₁, mem_effectiveDomain_iff]
    constructor
    · intro h
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [hcon, EReal.coe_add_top] at h
      exact lt_irrefl _ h
    · intro h
      rcases ereal_trichotomy (subderivative (subderivative f x) w z) with h' | h' | ⟨r, h'⟩
      · rw [h', EReal.add_bot]; exact bot_lt_top
      · rw [h'] at h; exact absurd h (lt_irrefl _)
      · rw [h', ← EReal.coe_add]; exact EReal.coe_lt_top _

end RW
