/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proximal and sharp Lagrangians

Examples 11.57 and 11.58. Formula 11(28) specializes through the
self-conjugacy of `½|·|²` and through the conjugate of a norm, which is the
indicator of the unit ball of the polar norm. The illustrations for
`f(x,u) = f₀(x) + δ_D(F(x) + u)` follow directly from the definition of the
augmented Lagrangian.
-/
import RockafellarWets.Chapter11.AugmentedLagrangianFormulas

open Set Filter Topology Metric
open scoped InnerProductSpace Pointwise
namespace RW
noncomputable section

section PolarBall

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- The unit ball `B° = {z | ‖z‖° ≤ 1}` of the polar norm of `N`, described by
`⟨z,u⟩ ≤ N(u)` for all `u`. -/
def polarNormBall (N : Seminorm ℝ P) : Set P := {z | ∀ u, ⟪z, u⟫_ℝ ≤ N u}

/-- The conjugate of a norm is the indicator of the polar unit ball. -/
theorem fenchelConjugate_sharpAugmentingFunction (N : Seminorm ℝ P) :
    fenchelConjugate (sharpAugmentingFunction N) = indicatorVA (polarNormBall N) := by
  funext v
  by_cases hv : v ∈ polarNormBall N
  · rw [indicatorVA_apply_mem hv]
    apply le_antisymm
    · rw [fenchelConjugate_le_iff]
      intro u
      change (⟪v, u⟫_ℝ : EReal) - ((N u : ℝ) : EReal) ≤ 0
      rw [← EReal.coe_sub, ← EReal.coe_zero, EReal.coe_le_coe_iff]
      linarith [hv u]
    · have h := le_fenchelConjugate (sharpAugmentingFunction N) 0 v
      change (⟪v, (0 : P)⟫_ℝ : EReal) - ((N 0 : ℝ) : EReal) ≤ _ at h
      rwa [inner_zero_right, map_zero, EReal.coe_zero, sub_zero] at h
  · rw [indicatorVA_apply_not_mem hv]
    simp only [polarNormBall, mem_setOf_eq, not_forall, not_le] at hv
    obtain ⟨u₀, hu₀⟩ := hv
    set d := ⟪v, u₀⟫_ℝ - N u₀ with hd
    have hd0 : 0 < d := by linarith
    refine top_le_iff.mp (EReal.ge_of_forall_gt_iff_ge.mp fun z _ ↦ ?_)
    set t := (|z| + 1) / d with ht
    have ht0 : 0 < t := div_pos (by positivity) hd0
    have h := le_fenchelConjugate (sharpAugmentingFunction N) (t • u₀) v
    change (⟪v, t • u₀⟫_ℝ : EReal) - ((N (t • u₀) : ℝ) : EReal) ≤ _ at h
    refine le_trans ?_ h
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, real_inner_smul_right, map_smul_eq_mul,
      Real.norm_eq_abs, abs_of_pos ht0]
    have htd : t * d = |z| + 1 := by rw [ht]; field_simp
    nlinarith [le_abs_self z]

/-- `rσ*(r⁻¹z)` for a norm `σ = N` is the indicator of `rB°`. -/
theorem coe_mul_fenchelConjugate_sharp (N : Seminorm ℝ P) {r : ℝ} (hr : 0 < r) (z : P) :
    (r : EReal) * fenchelConjugate (sharpAugmentingFunction N) (r⁻¹ • z) =
      indicatorVA {z : P | ∀ u, ⟪z, u⟫_ℝ ≤ r * N u} z := by
  rw [fenchelConjugate_sharpAugmentingFunction]
  have hiff : r⁻¹ • z ∈ polarNormBall N ↔ z ∈ {z : P | ∀ u, ⟪z, u⟫_ℝ ≤ r * N u} := by
    simp only [polarNormBall, mem_setOf_eq, real_inner_smul_left]
    refine forall_congr' fun u ↦ ?_
    rw [inv_mul_le_iff₀ hr]
  by_cases hz : z ∈ {z : P | ∀ u, ⟪z, u⟫_ℝ ≤ r * N u}
  · rw [indicatorVA_apply_mem (hiff.mpr hz), indicatorVA_apply_mem hz, mul_zero]
  · rw [indicatorVA_apply_not_mem (fun h ↦ hz (hiff.mp h)), indicatorVA_apply_not_mem hz,
      EReal.coe_mul_top_of_pos hr]

end PolarBall

section Formulas

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  {f : WithLp 2 (E × P) → EReal}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Example 11.57**: the proximal Lagrangian
`l̄(x,y,r) = inf_u {f(x,u) + (r/2)|u|² - ⟨y,u⟩}
  = sup_z {l(x,y-z) - |z|²/(2r)} = sup_z {l(x,z) - |z-y|²/(2r)}`. -/
theorem proximalLagrangian_formulas
    (hf : IsDualizingParameterization (primalObjective f) f) {r : ℝ} (hr : 0 < r) (x : E)
    (y : P) :
    augmentedLagrangian f (proximalAugmentingFunction P) x y r =
        ⨅ u, f (WithLp.toLp 2 (x, u)) + ((r / 2 * ‖u‖ ^ 2 : ℝ) : EReal) - (⟪y, u⟫_ℝ : EReal) ∧
    augmentedLagrangian f (proximalAugmentingFunction P) x y r =
        ⨆ z, lagrangian f x (y - z) - ((‖z‖ ^ 2 / (2 * r) : ℝ) : EReal) ∧
    augmentedLagrangian f (proximalAugmentingFunction P) x y r =
        ⨆ z, lagrangian f x z - ((‖z - y‖ ^ 2 / (2 * r) : ℝ) : EReal) := by
  have h28 := augmentedLagrangian_eq_iSup_lagrangian hf (isAugmentingFunction_proximal (P := P))
    (fun _ ↦ EReal.coe_ne_top _) hr x y
  have hconj : fenchelConjugate (proximalAugmentingFunction P) =
      fun v ↦ ((‖v‖ ^ 2 / 2 : ℝ) : EReal) := fenchelConjugate_half_norm_sq
  rw [hconj] at h28
  have h2 : augmentedLagrangian f (proximalAugmentingFunction P) x y r =
      ⨆ z, lagrangian f x (y - z) - ((‖z‖ ^ 2 / (2 * r) : ℝ) : EReal) := by
    rw [h28]
    refine iSup_congr fun z ↦ ?_
    rw [← EReal.coe_mul, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
    congr 2
    field_simp
  refine ⟨iInf_congr fun u ↦ ?_, h2, ?_⟩
  · change f (WithLp.toLp 2 (x, u)) + (r : EReal) * ((‖u‖ ^ 2 / 2 : ℝ) : EReal) - _ = _
    rw [← EReal.coe_mul]
    congr 3
    ring
  · rw [h2]
    have he := (Equiv.subLeft y).iSup_comp
      (g := fun z ↦ lagrangian f x z - ((‖z - y‖ ^ 2 / (2 * r) : ℝ) : EReal))
    rw [← he]
    refine iSup_congr fun z ↦ ?_
    simp only [Equiv.subLeft_apply, sub_sub_cancel_left, norm_neg]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Example 11.58**: the sharp Lagrangian of a norm `N`,
`l̄(x,y,r) = inf_u {f(x,u) + rN(u) - ⟨y,u⟩} = sup_z {l(x,y-z) - δ_{rB°}(z)}
  = sup_{‖z-y‖° ≤ r} l(x,z)`. -/
theorem sharpLagrangian_formulas {N : Seminorm ℝ P} (hN : ∀ u, N u = 0 → u = 0)
    (hf : IsDualizingParameterization (primalObjective f) f) {r : ℝ} (hr : 0 < r) (x : E)
    (y : P) :
    augmentedLagrangian f (sharpAugmentingFunction N) x y r =
        ⨅ u, f (WithLp.toLp 2 (x, u)) + ((r * N u : ℝ) : EReal) - (⟪y, u⟫_ℝ : EReal) ∧
    augmentedLagrangian f (sharpAugmentingFunction N) x y r =
        ⨆ z, lagrangian f x (y - z) - indicatorVA {z : P | ∀ u, ⟪z, u⟫_ℝ ≤ r * N u} z ∧
    augmentedLagrangian f (sharpAugmentingFunction N) x y r =
        ⨆ (z : P) (_ : ∀ u, ⟪z - y, u⟫_ℝ ≤ r * N u), lagrangian f x z := by
  have h28 := augmentedLagrangian_eq_iSup_lagrangian hf (isAugmentingFunction_sharp hN)
    (fun _ ↦ EReal.coe_ne_top _) hr x y
  have h2 : augmentedLagrangian f (sharpAugmentingFunction N) x y r =
      ⨆ z, lagrangian f x (y - z) - indicatorVA {z : P | ∀ u, ⟪z, u⟫_ℝ ≤ r * N u} z := by
    rw [h28]
    exact iSup_congr fun z ↦ by rw [coe_mul_fenchelConjugate_sharp N hr]
  refine ⟨iInf_congr fun u ↦ ?_, h2, ?_⟩
  · change f (WithLp.toLp 2 (x, u)) + (r : EReal) * ((N u : ℝ) : EReal) - _ = _
    rw [← EReal.coe_mul]
  · rw [h2]
    apply le_antisymm
    · refine iSup_le fun z ↦ ?_
      by_cases hz : z ∈ {z : P | ∀ u, ⟪z, u⟫_ℝ ≤ r * N u}
      · rw [indicatorVA_apply_mem hz, sub_zero]
        refine le_iSup₂_of_le (f := fun (w : P) (_ : ∀ u, ⟪w - y, u⟫_ℝ ≤ r * N u) ↦
          lagrangian f x w) (y - z) (fun u ↦ ?_) le_rfl
        have h := hz (-u)
        rw [inner_neg_right, map_neg_eq_map] at h
        rw [sub_sub_cancel_left, inner_neg_left]
        exact h
      · rw [indicatorVA_apply_not_mem hz, EReal.sub_top]
        exact bot_le
    · refine iSup₂_le fun z hz ↦ ?_
      refine le_iSup_of_le (y - z) ?_
      have hz' : y - z ∈ {z : P | ∀ u, ⟪z, u⟫_ℝ ≤ r * N u} := by
        intro u
        have h := hz (-u)
        rw [inner_neg_right, map_neg_eq_map, ← inner_neg_left, neg_sub] at h
        exact h
      rw [indicatorVA_apply_mem hz', sub_zero, sub_sub_cancel]

end Formulas


section Composite

variable {E P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- An infimum of `A + B g` over a nonempty family with `g ≥ 0` and `B > 0`. -/
theorem iInf_coe_add_mul {ι : Type*} [Nonempty ι] {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) (A : ℝ)
    {B : ℝ} (hB : 0 < B) :
    (⨅ i, ((A + B * g i : ℝ) : EReal)) = ((A + B * ⨅ i, g i : ℝ) : EReal) := by
  have hbdd : BddBelow (range g) := ⟨0, by rintro _ ⟨i, rfl⟩; exact hg i⟩
  apply le_antisymm
  · rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have hz' : A + B * (⨅ i, g i) < z := EReal.coe_lt_coe_iff.mp hz
    have hlt : (⨅ i, g i) < (z - A) / B := by rw [lt_div_iff₀ hB]; linarith
    obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt hlt
    refine (iInf_le _ i).trans (EReal.coe_le_coe_iff.mpr ?_)
    rw [lt_div_iff₀ hB] at hi
    linarith
  · exact le_iInf fun i ↦ EReal.coe_le_coe_iff.mpr
      (by nlinarith [ciInf_le hbdd i])

omit [InnerProductSpace ℝ P] in
/-- The squared distance to a nonempty set is the infimum of squared distances. -/
theorem infDist_sq_eq_iInf {D : Set P} (hD : D.Nonempty) (c : P) :
    infDist c D ^ 2 = ⨅ v : D, ‖(v : P) - c‖ ^ 2 := by
  haveI : Nonempty D := hD.to_subtype
  have hmono : Monotone fun t : ℝ ↦ (max t 0) ^ 2 := fun a b h ↦
    pow_le_pow_left₀ (le_max_right _ _) (max_le_max h le_rfl) 2
  have hcont : Continuous fun t : ℝ ↦ (max t 0) ^ 2 := by fun_prop
  have hbdd : BddBelow (range fun v : D ↦ dist c (v : P)) :=
    ⟨0, by rintro _ ⟨v, rfl⟩; exact dist_nonneg⟩
  have h := hmono.map_ciInf_of_continuousAt hcont.continuousAt hbdd
  rw [← infDist_eq_iInf, max_eq_left infDist_nonneg] at h
  rw [h]
  exact iInf_congr fun v ↦ by rw [max_eq_left dist_nonneg, dist_eq_norm', norm_sub_rev]

/-- The integrand `f(x,u) = f₀(x) + δ_D(F(x) + u)` of Example 11.46 with
`θ = δ_D` and no abstract constraint on `x`. -/
def compositeIndicatorIntegrand (f₀ : E → ℝ) (F : E → P) (D : Set P) :
    WithLp 2 (E × P) → EReal :=
  fun q ↦ (f₀ q.fst : EReal) + indicatorVA D (F q.fst + q.snd)

/-- The augmented Lagrangian of the composite indicator integrand is an
infimum over the points of `D`. -/
theorem augmentedLagrangian_compositeIndicator (f₀ : E → ℝ) (F : E → P) (D : Set P)
    {σ : P → EReal} (hσ : ∀ u, 0 ≤ σ u) {r : ℝ} (hr : 0 ≤ r) (x : E) (y : P) :
    augmentedLagrangian (compositeIndicatorIntegrand f₀ F D) σ x y r =
      ⨅ v : D, (f₀ x : EReal) + (r : EReal) * σ ((v : P) - F x) -
        (⟪y, (v : P) - F x⟫_ℝ : EReal) := by
  apply le_antisymm
  · refine le_iInf fun v ↦ iInf_le_of_le ((v : P) - F x) (le_of_eq ?_)
    change (f₀ x : EReal) + indicatorVA D (F x + ((v : P) - F x)) + _ - _ = _
    rw [add_sub_cancel, indicatorVA_apply_mem v.2, add_zero]
  · refine le_iInf fun u ↦ ?_
    change _ ≤ (f₀ x : EReal) + indicatorVA D (F x + u) + (r : EReal) * σ u - (⟪y, u⟫_ℝ : EReal)
    by_cases hu : F x + u ∈ D
    · refine iInf_le_of_le ⟨F x + u, hu⟩ (le_of_eq ?_)
      rw [indicatorVA_apply_mem hu, add_zero, add_sub_cancel_left]
    · have hne : (r : EReal) * σ u ≠ ⊥ :=
        ne_bot_of_le_ne_bot EReal.zero_ne_bot (EReal.mul_nonneg (EReal.coe_nonneg.mpr hr) (hσ u))
      rw [indicatorVA_apply_not_mem hu, EReal.coe_add_top, EReal.top_add_of_ne_bot hne,
        EReal.top_sub_coe]
      exact le_top

/-- **Example 11.57**, illustration: with `θ = δ_D` for a nonempty set `D`,
`l̄(x,y,r) = f₀(x) + (r/2) d_D(r⁻¹y + F(x))² - (r/2)|r⁻¹y|²`. -/
theorem proximalLagrangian_compositeIndicator (f₀ : E → ℝ) (F : E → P) {D : Set P}
    (hD : D.Nonempty) {r : ℝ} (hr : 0 < r) (x : E) (y : P) :
    augmentedLagrangian (compositeIndicatorIntegrand f₀ F D) (proximalAugmentingFunction P) x y r =
      ((f₀ x + r / 2 * (infDist (r⁻¹ • y + F x) D ^ 2 - ‖r⁻¹ • y‖ ^ 2) : ℝ) : EReal) := by
  haveI : Nonempty D := hD.to_subtype
  rw [augmentedLagrangian_compositeIndicator f₀ F D
    (isAugmentingFunction_proximal (P := P)).nonneg hr.le]
  have hterm : ∀ v : D, (f₀ x : EReal) + (r : EReal) * proximalAugmentingFunction P ((v : P) - F x) -
      (⟪y, (v : P) - F x⟫_ℝ : EReal) =
      ((f₀ x - r / 2 * ‖r⁻¹ • y‖ ^ 2 + r / 2 * ‖(v : P) - (r⁻¹ • y + F x)‖ ^ 2 : ℝ) : EReal) := by
    intro v
    change (f₀ x : EReal) + (r : EReal) * ((‖(v : P) - F x‖ ^ 2 / 2 : ℝ) : EReal) - _ = _
    rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    have he : (v : P) - (r⁻¹ • y + F x) = ((v : P) - F x) - r⁻¹ • y := by abel
    have h1 : ‖((v : P) - F x) - r⁻¹ • y‖ ^ 2 =
        ‖(v : P) - F x‖ ^ 2 - 2 * (r⁻¹ * ⟪(v : P) - F x, y⟫_ℝ) + (r⁻¹ * ‖y‖) ^ 2 := by
      rw [norm_sub_sq_real, inner_smul_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hr]
    have h2 : ‖r⁻¹ • y‖ = r⁻¹ * ‖y‖ := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
    rw [he, h1, h2, real_inner_comm ((v : P) - F x) y]
    field_simp
    ring
  rw [iInf_congr hterm, iInf_coe_add_mul (fun _ ↦ sq_nonneg _) _ (half_pos hr),
    ← infDist_sq_eq_iInf hD]
  congr 1
  ring

/-- **Example 11.57**, illustration: for `y = 0` this is the quadratic penalty
`f₀(x) + (r/2) d_D(F(x))²`. -/
theorem proximalLagrangian_compositeIndicator_zero (f₀ : E → ℝ) (F : E → P) {D : Set P}
    (hD : D.Nonempty) {r : ℝ} (hr : 0 < r) (x : E) :
    augmentedLagrangian (compositeIndicatorIntegrand f₀ F D) (proximalAugmentingFunction P) x 0 r =
      ((f₀ x + r / 2 * infDist (F x) D ^ 2 : ℝ) : EReal) := by
  rw [proximalLagrangian_compositeIndicator f₀ F hD hr, smul_zero, zero_add, norm_zero]
  congr 1
  ring

/-- **Example 11.57**, illustration: for `D = {0}`,
`l̄(x,y,r) = f₀(x) + ⟨y,F(x)⟩ + (r/2)|F(x)|²`. -/
theorem proximalLagrangian_compositeIndicator_singleton (f₀ : E → ℝ) (F : E → P) {r : ℝ}
    (hr : 0 < r) (x : E) (y : P) :
    augmentedLagrangian (compositeIndicatorIntegrand f₀ F {0}) (proximalAugmentingFunction P)
      x y r = ((f₀ x + ⟪y, F x⟫_ℝ + r / 2 * ‖F x‖ ^ 2 : ℝ) : EReal) := by
  rw [augmentedLagrangian_compositeIndicator f₀ F {0}
    (isAugmentingFunction_proximal (P := P)).nonneg hr.le, iInf_unique]
  change (f₀ x : EReal) + (r : EReal) * ((‖(0 : P) - F x‖ ^ 2 / 2 : ℝ) : EReal) -
    (⟪y, (0 : P) - F x⟫_ℝ : EReal) = _
  rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_eq_coe_iff, zero_sub,
    norm_neg, inner_neg_right]
  ring

/-- **Example 11.58**, illustration: for `y = 0` the sharp Lagrangian is the
linear penalty `f₀(x) + r d_D(F(x))`, with the distance measured in `N`. -/
theorem sharpLagrangian_compositeIndicator_zero (N : Seminorm ℝ P) (f₀ : E → ℝ) (F : E → P)
    {D : Set P} (hD : D.Nonempty) {r : ℝ} (hr : 0 < r) (x : E) :
    augmentedLagrangian (compositeIndicatorIntegrand f₀ F D) (sharpAugmentingFunction N) x 0 r =
      ((f₀ x + r * ⨅ v : D, N ((v : P) - F x) : ℝ) : EReal) := by
  haveI : Nonempty D := hD.to_subtype
  rw [augmentedLagrangian_compositeIndicator f₀ F D (σ := sharpAugmentingFunction N)
    (fun u ↦ EReal.coe_nonneg.mpr (apply_nonneg N u)) hr.le]
  rw [← iInf_coe_add_mul (fun v ↦ apply_nonneg N _) _ hr]
  refine iInf_congr fun v ↦ ?_
  change (f₀ x : EReal) + (r : EReal) * ((N ((v : P) - F x) : ℝ) : EReal) -
    (⟪(0 : P), (v : P) - F x⟫_ℝ : EReal) = _
  rw [inner_zero_left, EReal.coe_zero, sub_zero, ← EReal.coe_mul, ← EReal.coe_add]

/-- **Example 11.58**, illustration: for `D = {0}`,
`l̄(x,y,r) = f₀(x) + ⟨y,F(x)⟩ + rN(F(x))`. -/
theorem sharpLagrangian_compositeIndicator_singleton (N : Seminorm ℝ P) (f₀ : E → ℝ)
    (F : E → P) {r : ℝ} (hr : 0 < r) (x : E) (y : P) :
    augmentedLagrangian (compositeIndicatorIntegrand f₀ F {0}) (sharpAugmentingFunction N)
      x y r = ((f₀ x + ⟪y, F x⟫_ℝ + r * N (F x) : ℝ) : EReal) := by
  rw [augmentedLagrangian_compositeIndicator f₀ F {0} (σ := sharpAugmentingFunction N)
    (fun u ↦ EReal.coe_nonneg.mpr (apply_nonneg N u)) hr.le, iInf_unique]
  change (f₀ x : EReal) + (r : EReal) * ((N ((0 : P) - F x) : ℝ) : EReal) -
    (⟪y, (0 : P) - F x⟫_ℝ : EReal) = _
  rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_eq_coe_iff, zero_sub,
    map_neg_eq_map, inner_neg_right]
  ring

/-- The ordinary Lagrangian of the composite indicator integrand,
`l(x,z) = f₀(x) + ⟨z,F(x)⟩ - σ_D(z)`, as in Example 11.46. -/
theorem lagrangian_compositeIndicator (f₀ : E → ℝ) (F : E → P) {D : Set P} (x : E) (z : P) :
    lagrangian (compositeIndicatorIntegrand f₀ F D) x z =
      ((f₀ x + ⟪z, F x⟫_ℝ : ℝ) : EReal) - supportFunction D z := by
  have h0 : lagrangian (compositeIndicatorIntegrand f₀ F D) x z =
      augmentedLagrangian (compositeIndicatorIntegrand f₀ F D) (fun _ ↦ (0 : EReal)) x z 0 := by
    refine iInf_congr fun u ↦ ?_
    rw [mul_zero, add_zero]
  rw [h0, augmentedLagrangian_compositeIndicator f₀ F D (fun _ ↦ le_rfl) le_rfl]
  have hterm : ∀ v : D, (f₀ x : EReal) + ((0 : ℝ) : EReal) * (0 : EReal) -
      (⟪z, (v : P) - F x⟫_ℝ : EReal) = ((f₀ x + ⟪z, F x⟫_ℝ : ℝ) : EReal) - (⟪(v : P), z⟫_ℝ : EReal) := by
    intro v
    rw [mul_zero, add_zero, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_eq_coe_iff,
      inner_sub_right, real_inner_comm z (v : P)]
    ring
  rw [iInf_congr hterm, supportFunction, sub_eq_add_neg,
    show ∀ g : D → EReal, -(⨆ v, g v) = ⨅ v, -g v from fun g ↦ EReal.negOrderIso.map_iSup g]
  have hiso := (erealAddRightOrderIso (f₀ x + ⟪z, F x⟫_ℝ)).map_iInf
    (fun v : D ↦ -(⟪(v : P), z⟫_ℝ : EReal))
  simp only [erealAddRightOrderIso_apply] at hiso
  rw [add_comm (((f₀ x + ⟪z, F x⟫_ℝ : ℝ) : EReal)), hiso]
  refine iInf_congr fun v ↦ ?_
  rw [add_comm (-(⟪(v : P), z⟫_ℝ : EReal)), ← sub_eq_add_neg]

/-- The composite indicator integrand is a dualizing parameterization for a
nonempty closed convex set `D`. -/
theorem compositeIndicator_isDualizing [NormedAddCommGroup E] (f₀ : E → ℝ) (F : E → P) {D : Set P}
    (hD : IsClosed D) (hDc : Convex ℝ D) (hDn : D.Nonempty) :
    IsDualizingParameterization (primalObjective (compositeIndicatorIntegrand f₀ F D))
      (compositeIndicatorIntegrand f₀ F D) where
  eq_primalObjective := rfl
  isProper := by
    obtain ⟨d, hd⟩ := hDn
    refine ⟨⟨WithLp.toLp 2 (0, d - F 0), ?_⟩, fun q ↦ ?_⟩
    · change (f₀ 0 : EReal) + indicatorVA D (F 0 + (d - F 0)) < ⊤
      rw [add_sub_cancel, indicatorVA_apply_mem hd, add_zero]
      exact EReal.coe_lt_top _
    · change ⊥ < (f₀ q.fst : EReal) + indicatorVA D (F q.fst + q.snd)
      by_cases h : F q.fst + q.snd ∈ D
      · rw [indicatorVA_apply_mem h, add_zero]
        exact EReal.bot_lt_coe _
      · rw [indicatorVA_apply_not_mem h, EReal.coe_add_top]
        exact bot_lt_top
  lowerSemicontinuous_slice := fun x ↦ by
    change LowerSemicontinuous (fun u ↦ (f₀ x : EReal) + indicatorVA D (F x + u))
    have hl : LowerSemicontinuous (fun u ↦ indicatorVA D (F x + u)) :=
      (lowerSemicontinuous_indicatorVA hD).comp (continuous_const.add continuous_id)
    exact lowerSemicontinuous_const.add' hl fun u ↦
      EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  convex_slice := fun x ↦ by
    have hmem : ∀ (u : P) (a : ℝ), (f₀ x : EReal) + indicatorVA D (F x + u) ≤ (a : EReal) →
        F x + u ∈ D ∧ f₀ x ≤ a := by
      intro u a h
      by_cases hu : F x + u ∈ D
      · rw [indicatorVA_apply_mem hu, add_zero, EReal.coe_le_coe_iff] at h
        exact ⟨hu, h⟩
      · rw [indicatorVA_apply_not_mem hu, EReal.coe_add_top, top_le_iff] at h
        exact absurd h (EReal.coe_ne_top _)
    rintro ⟨u₁, a₁⟩ h₁ ⟨u₂, a₂⟩ h₂ s t hs ht hst
    obtain ⟨hD₁, hf₁⟩ := hmem u₁ a₁ h₁
    obtain ⟨hD₂, hf₂⟩ := hmem u₂ a₂ h₂
    have hcomb : F x + (s • u₁ + t • u₂) ∈ D := by
      have h := hDc hD₁ hD₂ hs ht hst
      convert h using 1
      rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hst, one_smul]
    change (f₀ x : EReal) + indicatorVA D (F x + (s • u₁ + t • u₂)) ≤
      ((s * a₁ + t * a₂ : ℝ) : EReal)
    rw [indicatorVA_apply_mem hcomb, add_zero, EReal.coe_le_coe_iff]
    have e1 := mul_le_mul_of_nonneg_left hf₁ hs
    have e2 := mul_le_mul_of_nonneg_left hf₂ ht
    have e3 : f₀ x = s * f₀ x + t * f₀ x := by rw [← add_mul, hst, one_mul]
    linarith

/-- **Example 11.58**, illustration: with `θ = δ_D`,
`l̄(x,y,r) = f₀(x) + sup_{‖z-y‖° ≤ r} {⟨z,F(x)⟩ - σ_D(z)}`. -/
theorem sharpLagrangian_compositeIndicator [NormedAddCommGroup E] [FiniteDimensional ℝ P]
    {N : Seminorm ℝ P} (hN : ∀ u, N u = 0 → u = 0) (f₀ : E → ℝ) (F : E → P) {D : Set P}
    (hD : IsClosed D) (hDc : Convex ℝ D) (hDn : D.Nonempty) {r : ℝ} (hr : 0 < r) (x : E)
    (y : P) :
    augmentedLagrangian (compositeIndicatorIntegrand f₀ F D) (sharpAugmentingFunction N) x y r =
      (f₀ x : EReal) + ⨆ (z : P) (_ : ∀ u, ⟪z - y, u⟫_ℝ ≤ r * N u),
        ((⟪z, F x⟫_ℝ : ℝ) : EReal) - supportFunction D z := by
  have hf : IsDualizingParameterization (primalObjective (compositeIndicatorIntegrand f₀ F D))
      (compositeIndicatorIntegrand f₀ F D) := compositeIndicator_isDualizing f₀ F hD hDc hDn
  rw [(sharpLagrangian_formulas hN hf hr x y).2.2, ereal_add_iSup]
  refine iSup_congr fun z ↦ ?_
  rw [ereal_add_iSup]
  refine iSup_congr fun _ ↦ ?_
  rw [lagrangian_compositeIndicator, EReal.coe_add, sub_eq_add_neg, sub_eq_add_neg, add_assoc]

end Composite

end
end RW
