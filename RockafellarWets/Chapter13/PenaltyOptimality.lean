/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order optimality with penalties

Exercise 13.26.  We minimize `f = δ_X + f₀ + θ_{Y,B} ∘ F` with `X` polyhedral, `f₀`, `F` of class
`C²`, and the piecewise linear-quadratic penalty `θ_{Y,B}` of 11.18 and 13.23.  As in Exercise
13.17 we write `δ_X + θ_{Y,B} ∘ F = h ∘ F₀` for the separable convex piecewise linear-quadratic
function `h(x, u) = δ_X(x) + θ_{Y,B}(u)` and `F₀(x) = (x, F(x))`, and apply the convex
piecewise linear-quadratic case of Theorem 13.14 together with 13.18, 13.23 and 13.24.  The second
subderivatives of the separable function `h` are the sums of those of its terms
(`secondSubderivative_separableSum_of_plq`), from the limits along half-lines in 13.9.
-/

import RockafellarWets.Chapter13.SmoothConstraintOptimality
import RockafellarWets.Chapter13.PLQPenaltySecondOrder
import RockafellarWets.Chapter10.SeparableSubgradients
import RockafellarWets.Chapter10.SeparableSubderivatives

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-! ### Separable functions -/

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- The quotients 13(5) of a separable function are the sums of those of its terms. -/
theorem secondDifferenceQuotient_separableSum {f : E → EReal} {g : P → EReal} {x : E} {y : P}
    {c d : ℝ} (hx : f x = c) (hy : g y = d) {τ : ℝ} (hτ : 0 < τ) (q w : WithLp 2 (E × P)) :
    secondDifferenceQuotient (separableSum f g) (WithLp.toLp 2 (x, y)) q τ w =
      secondDifferenceQuotient f x q.fst τ w.fst + secondDifferenceQuotient g y q.snd τ w.snd := by
  have hpos : 0 < 2 / τ ^ 2 := by positivity
  change ((2 / τ ^ 2 : ℝ) : EReal) * ((f (x + τ • w.fst) + g (y + τ • w.snd)) - (f x + g y) -
      ((τ * ⟪q, w⟫_ℝ : ℝ) : EReal)) =
    ((2 / τ ^ 2 : ℝ) : EReal) * (f (x + τ • w.fst) - f x - ((τ * ⟪q.fst, w.fst⟫_ℝ : ℝ) : EReal)) +
      ((2 / τ ^ 2 : ℝ) : EReal) * (g (y + τ • w.snd) - g y - ((τ * ⟪q.snd, w.snd⟫_ℝ : ℝ) : EReal))
  rw [hx, hy, WithLp.prod_inner_apply]
  cases hfv : f (x + τ • w.fst) <;> cases hgv : g (y + τ • w.snd) <;>
    simp [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_mul_bot_of_pos hpos,
      EReal.coe_mul_top_of_pos hpos]
  ring

/-- A separable sum of piecewise linear-quadratic functions is piecewise linear-quadratic. -/
theorem isPiecewiseLinearQuadratic_separableSum {f : E → EReal} {g : P → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hg : IsPiecewiseLinearQuadratic g) :
    IsPiecewiseLinearQuadratic (separableSum f g) := by
  have h := (hf.compAffine (WithLp.fstL 2 ℝ E P) 0).add (hg.compAffine (WithLp.sndL 2 ℝ E P) 0)
  convert h using 1
  funext q
  simp [separableSum]

/-- A separable sum of convex functions without `-∞` has a convex epigraph. -/
theorem convex_epigraph_separableSum {f : E → EReal} {g : P → EReal}
    (hf : Convex ℝ (epigraph f)) (hg : Convex ℝ (epigraph g)) (hfb : ∀ x, f x ≠ ⊥)
    (hgb : ∀ y, g y ≠ ⊥) : Convex ℝ (epigraph (separableSum f g)) := by
  have h := convex_epigraph_add_of_ne_bot (convex_epigraph_compAffine hf (WithLp.fstL 2 ℝ E P) 0)
    (convex_epigraph_compAffine hg (WithLp.sndL 2 ℝ E P) 0) (fun q ↦ hfb _) (fun q ↦ hgb _)
  convert h using 2
  funext q
  simp [separableSum]

/-- For convex piecewise linear-quadratic `f` and `g`, the second subderivatives of
`(x, y) ↦ f(x) + g(y)` are the sums of those of `f` and `g`: by 13.9 all three are limits of
their quotients along half-lines, and the quotients add. -/
theorem secondSubderivative_separableSum_of_plq {f : E → EReal} {g : P → EReal}
    (hf : IsPiecewiseLinearQuadratic f) (hfc : Convex ℝ (epigraph f))
    (hg : IsPiecewiseLinearQuadratic g) (hgc : Convex ℝ (epigraph g)) {x : E} {y : P}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain g) {q : WithLp 2 (E × P)}
    (ha : q.fst ∈ subdifferential f x) (hb : q.snd ∈ subdifferential g y)
    (w : WithLp 2 (E × P)) :
    secondSubderivative (separableSum f g) (WithLp.toLp 2 (x, y)) q w =
      secondSubderivative f x q.fst w.fst + secondSubderivative g y q.snd w.snd := by
  have hfx : f x = ((f x).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (hf.ne_bot x)).symm
  have hgy : g y = ((g y).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hy) (hg.ne_bot y)).symm
  have hh := isPiecewiseLinearQuadratic_separableSum hf hg
  have hhc := convex_epigraph_separableSum hfc hgc hf.ne_bot hg.ne_bot
  have hxy : WithLp.toLp 2 (x, y) ∈ effectiveDomain (separableSum f g) := by
    change f x + g y < ⊤
    rw [hfx, hgy, ← EReal.coe_add]
    exact EReal.coe_lt_top _
  have hq : q ∈ subdifferential (separableSum f g) (WithLp.toLp 2 (x, y)) :=
    (mem_subdifferential_separableSum_iff (hf.lowerSemicontinuous x)
      (hg.lowerSemicontinuous y) hfx hgy q).2 ⟨ha, hb⟩
  obtain ⟨-, -, -, -, -, h1, -⟩ := (piecewise_linear_quadratic_second_order hf hfc hx).2.1 _ ha
  obtain ⟨-, -, -, -, -, h2, -⟩ := (piecewise_linear_quadratic_second_order hg hgc hy).2.1 _ hb
  obtain ⟨-, -, -, -, -, h3, -⟩ := (piecewise_linear_quadratic_second_order hh hhc hxy).2.1 _ hq
  have hn1 : 0 ≤ secondSubderivative f x q.fst w.fst := by
    rw [(h1 w.fst).1]
    exact add_nonneg ((piecewise_linear_quadratic_second_order hf hfc hx).1.2.2 w.fst).1
      (indicatorVA_nonneg _ _)
  have hn2 : 0 ≤ secondSubderivative g y q.snd w.snd := by
    rw [(h2 w.snd).1]
    exact add_nonneg ((piecewise_linear_quadratic_second_order hg hgc hy).1.2.2 w.snd).1
      (indicatorVA_nonneg _ _)
  have hsum : Tendsto (fun τ ↦ secondDifferenceQuotient f x q.fst τ w.fst +
      secondDifferenceQuotient g y q.snd τ w.snd) (𝓝[>] (0 : ℝ))
      (𝓝 (secondSubderivative f x q.fst w.fst + secondSubderivative g y q.snd w.snd)) := by
    have hc := EReal.continuousAt_add (p := (secondSubderivative f x q.fst w.fst,
      secondSubderivative g y q.snd w.snd)) (.inr (ne_bot_of_le_ne_bot EReal.zero_ne_bot hn2))
      (.inl (ne_bot_of_le_ne_bot EReal.zero_ne_bot hn1))
    exact hc.tendsto.comp ((h1 w.fst).2.prodMk_nhds (h2 w.snd).2)
  refine tendsto_nhds_unique (h3 w).2 (hsum.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact (secondDifferenceQuotient_separableSum hfx hgy hτ q w).symm

/-- `d²δ_S(x̄ ∣ a)(w) = δ_K(w)` for polyhedral `S`, `a ∈ N_S(x̄)` and
`K = {w ∈ T_S(x̄) ∣ w ⊥ a}`. -/
theorem secondSubderivative_indicatorVA_of_isPolyhedral {S : Set E} (hS : IsPolyhedral S)
    {x : E} (hx : x ∈ S) {a : E} (ha : a ∈ normalCone S x) (w : E) :
    secondSubderivative (indicatorVA S) x a w =
      indicatorVA {w | w ∈ tangentCone S x ∧ ⟪w, a⟫_ℝ = 0} w := by
  have hplq := isPiecewiseLinearQuadratic_indicatorVA hS
  have hconv := convex_epigraph_indicatorVA hS.convex
  have hxd : x ∈ effectiveDomain (indicatorVA S) := by rw [effectiveDomain_indicatorVA]; exact hx
  have ha' : a ∈ subdifferential (indicatorVA S) x := by rw [subdifferential_indicatorVA]; exact ha
  rw [(((piecewise_linear_quadratic_second_order hplq hconv hxd).2.1 a ha').2.2.2.2.2.1 w).1,
    secondSubderivativeAt_indicatorVA_of_isPolyhedral hS hx, subderivative_indicatorVA hx]
  by_cases hw : w ∈ tangentCone S x
  · rw [indicatorVA_apply_mem hw, zero_add]
    by_cases h0 : ⟪w, a⟫_ℝ = 0
    · have h1 : w ∈ {w | indicatorVA (tangentCone S x) w = ((⟪a, w⟫_ℝ : ℝ) : EReal)} := by
        rw [mem_setOf_eq, indicatorVA_apply_mem hw, real_inner_comm, h0, EReal.coe_zero]
      rw [indicatorVA_apply_mem h1, indicatorVA_apply_mem (show w ∈ {w | w ∈ tangentCone S x ∧
        ⟪w, a⟫_ℝ = 0} from ⟨hw, h0⟩)]
    · have h1 : w ∉ {w | indicatorVA (tangentCone S x) w = ((⟪a, w⟫_ℝ : ℝ) : EReal)} := by
        rw [mem_setOf_eq, indicatorVA_apply_mem hw, real_inner_comm]
        intro h
        exact h0 (by exact_mod_cast h.symm)
      rw [indicatorVA_apply_not_mem h1, indicatorVA_apply_not_mem (show w ∉ {w | w ∈ tangentCone S x ∧
        ⟪w, a⟫_ℝ = 0} from fun h ↦ h0 h.2)]
  · rw [indicatorVA_apply_not_mem hw, indicatorVA_apply_not_mem (show w ∉ {w | w ∈ tangentCone S x ∧
      ⟪w, a⟫_ℝ = 0} from fun h ↦ hw h.1), EReal.top_add_of_ne_bot
      (ne_bot_of_le_ne_bot EReal.zero_ne_bot (indicatorVA_nonneg _ _))]

/-! ### Exercise 13.26 -/

omit [FiniteDimensional ℝ E] in
/-- A hyperplane through the origin is polyhedral. -/
theorem isPolyhedral_setOf_inner_eq_zero [FiniteDimensional ℝ E] (v : E) :
    IsPolyhedral {w : E | ⟪w, v⟫_ℝ = 0} := by
  have ha := isPolyhedral_linearHalfspace (innerSL ℝ v) 0
  have hb := isPolyhedral_linearHalfspace (innerSL ℝ (-v)) 0
  have : {w : E | ⟪w, v⟫_ℝ = 0} = {x | innerSL ℝ v x ≤ 0} ∩ {x | innerSL ℝ (-v) x ≤ 0} := by
    ext w
    simp only [mem_setOf_eq, mem_inter_iff, innerSL_apply_apply, inner_neg_left,
      real_inner_comm w v]
    constructor
    · intro h; rw [h]; simp
    · rintro ⟨h1, h2⟩; linarith
  rw [this]
  exact ha.inter hb

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- `θ_{K,B} ≥ 0` when `0 ∈ K`. -/
theorem plqPenalty_nonneg_of_zero_mem {K : Set P} (hK : (0 : P) ∈ K) (B : P →L[ℝ] P) (z : P) :
    0 ≤ plqPenalty K B z := by
  refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun y _ ↦
    ((⟪y, z⟫_ℝ - (1 / 2) * ⟪y, B y⟫_ℝ : ℝ) : EReal)) 0 hK)
  simp

/-- The second derivative of `L(·, y)` for `L(x, y) = f₀(x) + ⟪y, F(x)⟫ - c`. -/
theorem fderiv_fderiv_penaltyLagrangian_apply {f₀ : E → ℝ} (hf₀ : ContDiff ℝ 2 f₀) {F : E → P}
    (hF : ContDiff ℝ 2 F) (y : P) (c : ℝ) (x w : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ - c)) x w w =
      fderiv ℝ (fderiv ℝ f₀) x w w + ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ := by
  have h : fderiv ℝ (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ - c) = fderiv ℝ (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ) :=
    funext fun z ↦ fderiv_sub_const c
  rw [h]
  exact fderiv_fderiv_lagrangian_apply hf₀ hF y x w

/-- The multiplier set `Y(x̄) = {ȳ ∣ -∇ₓL(x̄, ȳ) ∈ N_X(x̄), ∇_yL(x̄, ȳ) ∈ N_Y(ȳ)}` of Exercise
13.26, for `L(x, y) = f₀(x) + ⟪y, F(x)⟫ - ½⟪y, By⟫`. -/
def penaltyMultiplierSet (f₀ : E → ℝ) (F : E → P) (X : Set E) (Y : Set P) (B : P →L[ℝ] P)
    (x : E) : Set P :=
  {y | -(gradient f₀ x + (fderiv ℝ F x).adjoint y) ∈ normalCone X x ∧ F x - B y ∈ normalCone Y y}

/-- The cone `X'(x̄) = T_X(x̄) ∩ ∇ₓL(x̄, ŷ)^⊥` of Exercise 13.26 for the multiplier `ŷ`; the cone
`Y'(x̄) = T_Y(ŷ) ∩ ∇_yL(x̄, ŷ)^⊥` is `penaltyCriticalCone Y B (F x̄) ŷ`. -/
def penaltyPrimalCriticalCone (f₀ : E → ℝ) (F : E → P) (X : Set E) (x : E) (ŷ : P) : Set E :=
  {w | w ∈ tangentCone X x ∧ ⟪w, gradient f₀ x + (fderiv ℝ F x).adjoint ŷ⟫_ℝ = 0}

/-- The function `w ↦ δ_{X'(x̄)}(w) + 2θ_{Y'(x̄),B}(∇F(x̄)w)` of Exercise 13.26 for the
multiplier `ŷ`. -/
noncomputable def penaltyCriticalTerm (f₀ : E → ℝ) (F : E → P) (X : Set E) (Y : Set P)
    (B : P →L[ℝ] P) (x : E) (ŷ : P) (w : E) : EReal :=
  indicatorVA (penaltyPrimalCriticalCone f₀ F X x ŷ) w +
    ((2 : ℝ) : EReal) * plqPenalty (penaltyCriticalCone Y B (F x) ŷ) B (fderiv ℝ F x w)

/-- **Exercise 13.26** (second-order optimality with penalties), with the independence clause
corrected.  Minimize `f = δ_X + θ_{Y,B} ∘ F + f₀` for polyhedral `X`, nonempty polyhedral `Y`,
symmetric positive-semidefinite `B`, and `f₀`, `F` of class `C²`, at `x̄ ∈ dom f` under the
qualification `y ∈ Y^∞, By = 0, -∇F(x̄)* y ∈ N_X(x̄) ⇒ y = 0`.  Then `Y(x̄)` is polyhedral and
compact; for `ŷ ∈ Y(x̄)` the cones `X'(x̄) = T_X(x̄) ∩ ∇ₓL(x̄, ŷ)^⊥` and
`Y'(x̄) = T_Y(ŷ) ∩ ∇_yL(x̄, ŷ)^⊥` are polyhedral, and the function
`w ↦ δ_{X'(x̄)}(w) + 2θ_{Y'(x̄),B}(∇F(x̄)w)` does not depend on the choice of `ŷ` (the cones
themselves may, see `PenaltyOptimalityCounterexample`);
(a) at a local minimum `Y(x̄) ≠ ∅` and, for any `ŷ ∈ Y(x̄)` and `w ∈ X'(x̄)`, the maximum over
`y ∈ Y(x̄)` of `⟪w, ∇²ₓₓL(x̄, y)w⟫` is attained and its sum with `2θ_{Y'(x̄),B}(∇F(x̄)w)` is
nonnegative;
(b) if `Y(x̄) ≠ ∅` and, for some `ŷ ∈ Y(x̄)`, that sum is positive for all `w ∈ X'(x̄) \ {0}`,
then `f(x) ≥ f(x̄) + ε‖x - x̄‖²` for `‖x - x̄‖ ≤ δ`, so `x̄` is locally optimal. -/
theorem second_order_optimality_with_penalties {X : Set E} (hX : IsPolyhedral X)
    {Y : Set P} (hY : IsPolyhedral Y) (hne : Y.Nonempty) {B : P →L[ℝ] P}
    (hB : ∀ u y, ⟪B u, y⟫_ℝ = ⟪u, B y⟫_ℝ) (hBpos : ∀ y, 0 ≤ ⟪y, B y⟫_ℝ)
    {f₀ : E → ℝ} (hf₀ : ContDiff ℝ 2 f₀) {F : E → P} (hF : ContDiff ℝ 2 F)
    {x : E} (hxX : x ∈ X) (hFx : F x ∈ effectiveDomain (plqPenalty Y B))
    (hQ : ∀ y ∈ horizonCone Y, B y = 0 → -((fderiv ℝ F x).adjoint y) ∈ normalCone X x → y = 0) :
    IsPolyhedral (penaltyMultiplierSet f₀ F X Y B x) ∧
    IsCompact (penaltyMultiplierSet f₀ F X Y B x) ∧
    (∀ ŷ ∈ penaltyMultiplierSet f₀ F X Y B x,
      IsPolyhedral (penaltyPrimalCriticalCone f₀ F X x ŷ) ∧
      IsCone (penaltyPrimalCriticalCone f₀ F X x ŷ) ∧
      IsPolyhedral (penaltyCriticalCone Y B (F x) ŷ) ∧ IsCone (penaltyCriticalCone Y B (F x) ŷ)) ∧
    (∀ ŷ₁ ∈ penaltyMultiplierSet f₀ F X Y B x, ∀ ŷ₂ ∈ penaltyMultiplierSet f₀ F X Y B x, ∀ w,
      penaltyCriticalTerm f₀ F X Y B x ŷ₁ w = penaltyCriticalTerm f₀ F X Y B x ŷ₂ w) ∧
    (IsLocalMin (fun z ↦ indicatorVA X z + plqPenalty Y B (F z) + (f₀ z : EReal)) x →
      (penaltyMultiplierSet f₀ F X Y B x).Nonempty ∧
      ∀ ŷ ∈ penaltyMultiplierSet f₀ F X Y B x, ∀ w ∈ penaltyPrimalCriticalCone f₀ F X x ŷ,
        ∃ y₀ ∈ penaltyMultiplierSet f₀ F X Y B x,
          (∀ y ∈ penaltyMultiplierSet f₀ F X Y B x,
            fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ - 1 / 2 * ⟪y, B y⟫_ℝ)) x w w ≤
              fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y₀, F z⟫_ℝ - 1 / 2 * ⟪y₀, B y₀⟫_ℝ)) x w w) ∧
          0 ≤ ((fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y₀, F z⟫_ℝ - 1 / 2 * ⟪y₀, B y₀⟫_ℝ)) x w w :
              ℝ) : EReal) +
            ((2 : ℝ) : EReal) * plqPenalty (penaltyCriticalCone Y B (F x) ŷ) B (fderiv ℝ F x w)) ∧
    ((penaltyMultiplierSet f₀ F X Y B x).Nonempty →
      (∃ ŷ ∈ penaltyMultiplierSet f₀ F X Y B x, ∀ w ∈ penaltyPrimalCriticalCone f₀ F X x ŷ,
        w ≠ 0 → ∃ y ∈ penaltyMultiplierSet f₀ F X Y B x,
          0 < ((fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ - 1 / 2 * ⟪y, B y⟫_ℝ)) x w w :
              ℝ) : EReal) +
            ((2 : ℝ) : EReal) * plqPenalty (penaltyCriticalCone Y B (F x) ŷ) B (fderiv ℝ F x w)) →
      IsLocalMin (fun z ↦ indicatorVA X z + plqPenalty Y B (F z) + (f₀ z : EReal)) x ∧
      ∃ ε > 0, ∃ δ > 0, ∀ z, ‖z - x‖ ≤ δ →
        indicatorVA X x + plqPenalty Y B (F x) + (f₀ x : EReal) +
            ((ε * ‖z - x‖ ^ 2 : ℝ) : EReal) ≤
          indicatorVA X z + plqPenalty Y B (F z) + (f₀ z : EReal)) := by
  set Yx := penaltyMultiplierSet f₀ F X Y B x with hYx
  set f : E → EReal := fun z ↦ indicatorVA X z + plqPenalty Y B (F z) + (f₀ z : EReal) with hf
  obtain ⟨hθp, hθl, hθc, hθplq⟩ := plqPenalty_properties hY hne hB hBpos
  have hδplq := isPiecewiseLinearQuadratic_indicatorVA hX
  have hδc := convex_epigraph_indicatorVA hX.convex
  have hθne : plqPenalty Y B (F x) ≠ ⊤ := ne_of_lt hFx
  have hθx : plqPenalty Y B (F x) = ((plqPenalty Y B (F x)).toReal : EReal) :=
    (EReal.coe_toReal hθne (hθp.2 _).ne').symm
  have hδx : indicatorVA X x = ((0 : ℝ) : EReal) := by
    rw [indicatorVA_apply_mem hxX, EReal.coe_zero]
  have hxd : x ∈ effectiveDomain (indicatorVA X) := by
    rw [effectiveDomain_indicatorVA]; exact hxX
  have hhplq := isPiecewiseLinearQuadratic_separableSum hδplq hθplq
  have hhc := convex_epigraph_separableSum hδc hθc hδplq.ne_bot hθplq.ne_bot
  have hGx : graphLift F x = WithLp.toLp 2 (x, F x) := rfl
  have hhx' : (fun z ↦ indicatorVA X z + plqPenalty Y B (F z)) x =
      (((plqPenalty Y B (F x)).toReal : ℝ) : EReal) := by
    change indicatorVA X x + plqPenalty Y B (F x) = _
    rw [hδx, EReal.coe_zero, zero_add, ← hθx]
  have hhx : separableSum (indicatorVA X) (plqPenalty Y B) (graphLift F x) =
      (((plqPenalty Y B (F x)).toReal : ℝ) : EReal) := hhx'
  have hū : graphLift F x ∈ effectiveDomain (separableSum (indicatorVA X) (plqPenalty Y B)) := by
    change separableSum (indicatorVA X) (plqPenalty Y B) (graphLift F x) < ⊤
    rw [hhx]
    exact EReal.coe_lt_top _
  have hG2 := contDiff_graphLift hF
  have hG1 : ContDiff ℝ 1 (graphLift F) := hG2.of_le (by norm_num)
  -- subgradients of `θ` and `h`
  have hθsub : ∀ y, y ∈ subdifferential (plqPenalty Y B) (F x) ↔ F x - B y ∈ normalCone Y y := by
    intro y
    rw [subdifferential_plqPenalty hY hne hB hBpos]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1, h⟩⟩
  have hsubh : ∀ q, q ∈ subdifferential (separableSum (indicatorVA X) (plqPenalty Y B))
      (graphLift F x) ↔ q.fst ∈ normalCone X x ∧ q.snd ∈ subdifferential (plqPenalty Y B) (F x) := by
    intro q
    rw [hGx, mem_subdifferential_separableSum_iff (hδplq.lowerSemicontinuous x) (hθl (F x)) hδx
      hθx q, subdifferential_indicatorVA]
  -- the qualification of 13.14
  have hQ₀ : ∀ q ∈ horizonSubdifferential (separableSum (indicatorVA X) (plqPenalty Y B))
      (graphLift F x), (fderiv ℝ (graphLift F) x).adjoint q = 0 → q = 0 := by
    intro q hq h0
    rw [hGx] at hq
    have hq' := horizonSubdifferential_separableSum_subset (hδplq.lowerSemicontinuous x)
      (hθl (F x)) hδx hθx hq
    rw [mem_setOf_eq, horizonSubdifferential_indicatorVA,
      (horizonSubdifferential_plqPenalty hY hne hB hBpos hFx).2] at hq'
    rw [adjoint_fderiv_graphLift hF] at h0
    have h1 : q.fst = -((fderiv ℝ F x).adjoint q.snd) := eq_neg_of_add_eq_zero_left h0
    have hy := hQ q.snd hq'.2.1.1 hq'.2.1.2 (by rw [← h1]; exact hq'.1)
    rw [hy, map_zero, neg_zero] at h1
    apply WithLp.ofLp_injective
    exact Prod.ext h1 hy
  -- subgradients of the composition
  have hl : LowerSemicontinuous (separableSum (indicatorVA X) (plqPenalty Y B)) :=
    hhplq.lowerSemicontinuous
  have hlsc : IsLocallyLscAt (separableSum (indicatorVA X) (plqPenalty Y B)) (graphLift F x) :=
    isLocallyLscAt_of_isLocallyClosedAt_epigraph hhx
      (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal _ hl) _)
  have hr := (isSubdifferentiallyRegularAt_of_convex hhc hlsc).1
  have hsubC := subdifferential_comp_eq_of_regular hG1 hl hr hQ₀
  have hchar : ∀ u, u ∈ subdifferential
      (separableSum (indicatorVA X) (plqPenalty Y B) ∘ graphLift F) x ↔
      ∃ y ∈ subdifferential (plqPenalty Y B) (F x),
        u - (fderiv ℝ F x).adjoint y ∈ normalCone X x := by
    intro u
    rw [hsubC]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [hsubh] at hq
      refine ⟨q.snd, hq.2, ?_⟩
      rw [adjoint_fderiv_graphLift hF, add_sub_cancel_right]
      exact hq.1
    · rintro ⟨y, hy, hxy⟩
      refine ⟨WithLp.toLp 2 (u - (fderiv ℝ F x).adjoint y, y), (hsubh _).2 ⟨hxy, hy⟩, ?_⟩
      rw [adjoint_fderiv_graphLift hF]
      simp
  have hYx_iff : ∀ y, y ∈ Yx ↔ y ∈ subdifferential (plqPenalty Y B) (F x) ∧
      -gradient f₀ x - (fderiv ℝ F x).adjoint y ∈ normalCone X x := by
    intro y
    rw [hθsub, ← neg_add']
    exact and_comm
  have hmemv : ∀ y ∈ Yx, -gradient f₀ x ∈ subdifferential
      (separableSum (indicatorVA X) (plqPenalty Y B) ∘ graphLift F) x := fun y hy ↦
    (hchar _).2 ⟨y, ((hYx_iff y).1 hy).1, ((hYx_iff y).1 hy).2⟩
  -- the multiplier sets
  have hmsY : ∀ q ∈ multiplierSet (graphLift F) (separableSum (indicatorVA X) (plqPenalty Y B)) x
      (-gradient f₀ x), q.snd ∈ Yx := by
    intro q hq
    have h1 := (hsubh q).1 hq.1
    have h2 := hq.2
    rw [adjoint_fderiv_graphLift hF] at h2
    refine (hYx_iff _).2 ⟨h1.2, ?_⟩
    rw [← h2, add_sub_cancel_right]
    exact h1.1
  have hYms : ∀ y ∈ Yx, WithLp.toLp 2 (-gradient f₀ x - (fderiv ℝ F x).adjoint y, y) ∈
      multiplierSet (graphLift F) (separableSum (indicatorVA X) (plqPenalty Y B)) x
        (-gradient f₀ x) := by
    intro y hy
    refine ⟨(hsubh _).2 ⟨((hYx_iff y).1 hy).2, ((hYx_iff y).1 hy).1⟩, ?_⟩
    rw [adjoint_fderiv_graphLift hF]
    simp
  -- the second subderivatives of `h` along the graph
  have hΦ : ∀ q ∈ multiplierSet (graphLift F) (separableSum (indicatorVA X) (plqPenalty Y B)) x
      (-gradient f₀ x), ∀ w, secondSubderivative (separableSum (indicatorVA X) (plqPenalty Y B))
        (graphLift F x) q (fderiv ℝ (graphLift F) x w) =
        penaltyCriticalTerm f₀ F X Y B x q.snd w := by
    intro q hq w
    have h1 := (hsubh q).1 hq.1
    have h2 := hq.2
    rw [adjoint_fderiv_graphLift hF] at h2
    have hqf : q.fst = -(gradient f₀ x + (fderiv ℝ F x).adjoint q.snd) := by
      rw [eq_sub_of_add_eq h2, neg_add']
    rw [hGx, secondSubderivative_separableSum_of_plq hδplq hδc hθplq hθc hxd hFx
      (by rw [subdifferential_indicatorVA]; exact h1.1) h1.2, fderiv_graphLift_apply hF,
      secondSubderivative_indicatorVA_of_isPolyhedral hX hxX h1.1,
      (piecewise_linear_quadratic_penalties hY hne hB hBpos h1.2).2.2.2.2.1, penaltyCriticalTerm]
    congr 2
    ext w'
    simp only [mem_setOf_eq, penaltyPrimalCriticalCone, hqf, inner_neg_right, neg_eq_zero]
  have hinner2 : ∀ q : WithLp 2 (E × P), ∀ w,
      ⟪q, fderiv ℝ (fderiv ℝ (graphLift F)) x w w⟫_ℝ =
        ⟪q.snd, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ := by
    intro q w
    rw [fderiv_fderiv_graphLift_apply hF, WithLp.prod_inner_apply]
    simp
  -- independence of the choice of `ŷ`
  have hind : ∀ ŷ₁ ∈ Yx, ∀ ŷ₂ ∈ Yx, ∀ w,
      penaltyCriticalTerm f₀ F X Y B x ŷ₁ w = penaltyCriticalTerm f₀ F X Y B x ŷ₂ w := by
    intro ŷ₁ h₁ ŷ₂ h₂ w
    obtain ⟨-, -, hfbar, -, -, -⟩ :=
      chain_rule_second_subderivatives_plq hG2 hhplq hhc hū hQ₀ (hmemv ŷ₁ h₁)
    have e₁ := hΦ _ (hYms ŷ₁ h₁) w
    have e₂ := hΦ _ (hYms ŷ₂ h₂) w
    rw [← hfbar w _ (hYms ŷ₁ h₁)] at e₁
    rw [← hfbar w _ (hYms ŷ₂ h₂)] at e₂
    exact e₁.symm.trans e₂
  -- the second subderivative of `f`
  have hd2 : ∀ ŷ ∈ Yx, ∀ w, ∀ y₀ ∈ Yx,
      (∀ y ∈ Yx, ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ ≤ ⟪y₀, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ) →
      secondSubderivative f x 0 w =
        penaltyCriticalTerm f₀ F X Y B x ŷ w +
          ((⟪y₀, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) : EReal) +
            ((fderiv ℝ (fderiv ℝ f₀) x w w : ℝ) : EReal) := by
    intro ŷ hŷ w y₀ hy₀ hm
    obtain ⟨hsup, -, -, -, -, -⟩ :=
      chain_rule_second_subderivatives_plq hG2 hhplq hhc hū hQ₀ (hmemv ŷ hŷ)
    have hsa : secondSubderivative f x (-gradient f₀ x + gradient f₀ x) w =
        secondSubderivative (separableSum (indicatorVA X) (plqPenalty Y B) ∘ graphLift F) x
          (-gradient f₀ x) w + ((fderiv ℝ (fderiv ℝ f₀) x w w : ℝ) : EReal) :=
      secondSubderivative_add_smooth
        (Eventually.of_forall (hasFDerivAt_fderiv_of_contDiff_two hf₀))
        (hasFDerivAt_fderiv_fderiv_of_contDiff_two hf₀ x) (fderiv_apply_eq_inner_gradient f₀ x)
        hhx' w
    rw [neg_add_cancel] at hsa
    rw [hsa, hsup w]
    congr 1
    apply le_antisymm
    · refine iSup₂_le fun q hq ↦ ?_
      rw [hΦ q hq w, hinner2 q w, hind _ (hmsY q hq) ŷ hŷ w]
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.2 (hm _ (hmsY q hq)))
    · refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun q _ ↦
        secondSubderivative (separableSum (indicatorVA X) (plqPenalty Y B)) (graphLift F x) q
          (fderiv ℝ (graphLift F) x w) +
        ((⟪q, fderiv ℝ (fderiv ℝ (graphLift F)) x w w⟫_ℝ : ℝ) : EReal)) _ (hYms y₀ hy₀))
      rw [hΦ _ (hYms y₀ hy₀) w, hinner2]
      exact congrArg₂ (· + ·) (hind ŷ hŷ y₀ hy₀ w) rfl
  -- polyhedrality and compactness of `Y(x̄)`
  have hYpoly : IsPolyhedral Yx := by
    have hNX := hX.isPolyhedral_normalCone hxX
    have hsubθ := (plqPenalty_subgradient_properties hY hne hB hBpos hFx).1
    let φ : E →ᵃ[ℝ] E := ⟨fun n ↦ -n - gradient f₀ x, -LinearMap.id, fun p v ↦ by
      simp only [vadd_eq_add, LinearMap.neg_apply, LinearMap.id_apply]
      abel⟩
    have hφ : φ '' normalCone X x = {u | -(gradient f₀ x + u) ∈ normalCone X x} := by
      ext u
      constructor
      · rintro ⟨n, hn, rfl⟩
        have : -(gradient f₀ x + (-n - gradient f₀ x)) = n := by abel
        change -(gradient f₀ x + (-n - gradient f₀ x)) ∈ normalCone X x
        rw [this]
        exact hn
      · intro hu
        refine ⟨-(gradient f₀ x + u), hu, ?_⟩
        change -(-(gradient f₀ x + u)) - gradient f₀ x = u
        abel
    have h2 : IsPolyhedral ((fderiv ℝ F x).adjoint ⁻¹' (φ '' normalCone X x)) :=
      (hNX.affine_image φ).continuousLinear_preimage _
    rw [hφ] at h2
    have : Yx = (fderiv ℝ F x).adjoint ⁻¹' {u | -(gradient f₀ x + u) ∈ normalCone X x} ∩
        subdifferential (plqPenalty Y B) (F x) := by
      ext y
      rw [mem_inter_iff, hθsub]
      rfl
    rw [this]
    exact h2.inter hsubθ
  have hYcpt : IsCompact Yx := by
    by_cases hv : -gradient f₀ x ∈ subdifferential
        (separableSum (indicatorVA X) (plqPenalty Y B) ∘ graphLift F) x
    · obtain ⟨-, -, hcpt⟩ := multiplierSet_properties hG2 hl hr hQ₀ hv
      have : Yx = (WithLp.sndL 2 ℝ E P) '' multiplierSet (graphLift F)
          (separableSum (indicatorVA X) (plqPenalty Y B)) x (-gradient f₀ x) := by
        ext y
        constructor
        · intro hy; exact ⟨_, hYms y hy, rfl⟩
        · rintro ⟨q, hq, rfl⟩; exact hmsY q hq
      rw [this]
      exact hcpt.image (WithLp.sndL 2 ℝ E P).continuous
    · rw [Set.eq_empty_of_forall_notMem fun y hy ↦ hv (hmemv y hy)]
      exact isCompact_empty
  have hlag : ∀ y w, fderiv ℝ (fderiv ℝ (fun z ↦ f₀ z + ⟪y, F z⟫_ℝ - 1 / 2 * ⟪y, B y⟫_ℝ)) x w w =
      fderiv ℝ (fderiv ℝ f₀) x w w + ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ := fun y w ↦
    fderiv_fderiv_penaltyLagrangian_apply hf₀ hF y _ x w
  have hfx' : indicatorVA X x + plqPenalty Y B (F x) + (f₀ x : EReal) =
      (((plqPenalty Y B (F x)).toReal + f₀ x : ℝ) : EReal) := by
    rw [hδx, EReal.coe_zero, zero_add, EReal.coe_add, ← hθx]
  have hfx : f x = (((plqPenalty Y B (F x)).toReal + f₀ x : ℝ) : EReal) := hfx'
  have hmaxex : ∀ w, Yx.Nonempty → ∃ y₀ ∈ Yx, ∀ y ∈ Yx,
      ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ ≤ ⟪y₀, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ := by
    intro w hne'
    obtain ⟨y₀, hy₀, hmax⟩ := hYcpt.exists_isMaxOn hne'
      (show ContinuousOn (fun y : P ↦ ⟪y, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ) Yx from
        (continuous_id.inner continuous_const).continuousOn)
    exact ⟨y₀, hy₀, fun y hy ↦ hmax hy⟩
  have hθ'nn : ∀ ŷ ∈ Yx, ∀ w, 0 ≤ ((2 : ℝ) : EReal) *
      plqPenalty (penaltyCriticalCone Y B (F x) ŷ) B (fderiv ℝ F x w) := by
    intro ŷ hŷ w
    exact EReal.mul_nonneg (EReal.coe_nonneg.2 (by norm_num)) (plqPenalty_nonneg_of_zero_mem
      (piecewise_linear_quadratic_penalties hY hne hB hBpos ((hYx_iff ŷ).1 hŷ).1).2.1.1 B _)
  refine ⟨hYpoly, hYcpt, fun ŷ hŷ ↦ ?_, hind, ?_, ?_⟩
  · obtain ⟨hp1, hc1, -⟩ := piecewise_linear_quadratic_penalties hY hne hB hBpos
      ((hYx_iff ŷ).1 hŷ).1
    refine ⟨(hX.isPolyhedral_tangentCone hxX).inter (isPolyhedral_setOf_inner_eq_zero _),
      ⟨⟨(isCone_tangentCone hxX).1, inner_zero_left _⟩, ?_⟩, hp1, hc1⟩
    rintro w ⟨h1, h2⟩ c hc
    exact ⟨(isCone_tangentCone hxX).2 h1 hc, by rw [real_inner_smul_left, h2, mul_zero]⟩
  · -- (a) necessity
    intro hmin
    obtain ⟨h0, h2⟩ := RW.IsLocalMin.secondOrder_necessary hmin hfx
    have hv0 : -gradient f₀ x ∈ subdifferential
        (separableSum (indicatorVA X) (plqPenalty Y B) ∘ graphLift F) x :=
      (zero_mem_subdifferential_add_smooth_iff (g := fun z ↦ indicatorVA X z + plqPenalty Y B (F z))
        (x := x) hhx' (hf₀.contDiffAt.of_le (by norm_num))).1
        (regularSubdifferential_subset_subdifferential _ x h0)
    obtain ⟨y, hy, hxy⟩ := (hchar _).1 hv0
    have hyY : y ∈ Yx := (hYx_iff y).2 ⟨hy, hxy⟩
    refine ⟨⟨y, hyY⟩, fun ŷ hŷ w hw ↦ ?_⟩
    obtain ⟨y₀, hy₀, hm⟩ := hmaxex w ⟨y, hyY⟩
    refine ⟨y₀, hy₀, fun y' hy' ↦ ?_, ?_⟩
    · rw [hlag, hlag]
      linarith [hm y' hy']
    · have h2w := h2 w
      rw [hd2 ŷ hŷ w y₀ hy₀ hm, penaltyCriticalTerm, indicatorVA_apply_mem hw, zero_add] at h2w
      rw [hlag, EReal.coe_add]
      calc (0 : EReal) ≤ _ := h2w
        _ = _ := by abel
  · -- (b) sufficiency
    rintro ⟨y₁, hy₁⟩ ⟨ŷ, hŷ, hpos⟩
    have hpos' : ∀ w, w ≠ 0 → 0 < secondSubderivative f x 0 w := by
      intro w hw0
      obtain ⟨y₀, hy₀, hm⟩ := hmaxex w ⟨y₁, hy₁⟩
      rw [hd2 ŷ hŷ w y₀ hy₀ hm, penaltyCriticalTerm]
      by_cases hw : w ∈ penaltyPrimalCriticalCone f₀ F X x ŷ
      · rw [indicatorVA_apply_mem hw, zero_add]
        obtain ⟨y, hy, hlt⟩ := hpos w hw hw0
        rw [hlag] at hlt
        calc (0 : EReal) < _ := hlt
          _ ≤ (((fderiv ℝ (fderiv ℝ f₀) x w w + ⟪y₀, fderiv ℝ (fderiv ℝ F) x w w⟫_ℝ : ℝ) :
              EReal) + ((2 : ℝ) : EReal) *
                plqPenalty (penaltyCriticalCone Y B (F x) ŷ) B (fderiv ℝ F x w)) :=
            add_le_add (EReal.coe_le_coe_iff.2 (by linarith [hm y hy])) le_rfl
          _ = _ := by rw [EReal.coe_add]; abel
      · rw [indicatorVA_apply_not_mem hw, EReal.top_add_of_ne_bot
          (ne_bot_of_le_ne_bot EReal.zero_ne_bot (hθ'nn ŷ hŷ w)), EReal.top_add_coe,
          EReal.top_add_coe]
        exact EReal.zero_lt_top
    obtain ⟨ε, hε, δ, hδ, hgr⟩ := exists_growth_of_secondSubderivative_pos hfx hpos'
    refine ⟨isLocalMin_of_secondSubderivative_pos hfx hpos', ε, hε, δ, hδ, fun z hz ↦ ?_⟩
    rw [hfx', ← EReal.coe_add]
    exact hgr z hz

end RW
