/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Second-order tangent sets

Definition 13.11 and Proposition 13.12.

The second-order tangent set `T²_C(x̄ | w)` is the outer limit, as `τ ↓ 0`, of
the parabolic difference sets `[C - x̄ - τw]/(½τ²)`.  Parabolic derivability
asks that it be nonempty and a full limit.  The arcs of 13(11) are read, as in
the discussion after Definition 13.59, through the second-order expansion
`ξ(τ) = x̄ + τw + ½τ²z_τ` with `z_τ → z`, i.e. `ξ'₊(0) = w` and `ξ''₊(0) = z`
in the sense `[ξ(τ) - ξ(0) - τξ'₊(0)]/(½τ²) → z`; the vectors with such arcs
are exactly those of the inner limit (`mem_innerSetLimitAlong_parabolicBlowUp_iff`).
-/

import RockafellarWets.Chapter13.SecondSubderivatives
import RockafellarWets.Chapter6.PolyhedralCones
import RockafellarWets.Chapter6.TangentNormalPolarity
import RockafellarWets.Chapter6.ConvexSets

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

section Definition1311

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The parabolic difference set `[C - x̄ - τw]/(½τ²)` of Definition 13.11. -/
def parabolicBlowUp (C : Set E) (x w : E) (τ : ℝ) : Set E :=
  (fun y ↦ (2 / τ ^ 2) • (y - x - τ • w)) '' C

theorem mem_parabolicBlowUp_iff {C : Set E} {x w z : E} {τ : ℝ} (hτ : τ ≠ 0) :
    z ∈ parabolicBlowUp C x w τ ↔ x + τ • w + (τ ^ 2 / 2) • z ∈ C := by
  have hτ2 : τ ^ 2 ≠ 0 := pow_ne_zero 2 hτ
  constructor
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    rw [smul_smul, div_mul_div_comm, mul_comm (τ ^ 2) 2, div_self (mul_ne_zero two_ne_zero hτ2),
      one_smul]
    abel
  · intro h
    refine ⟨_, h, ?_⟩
    change (2 / τ ^ 2) • (x + τ • w + (τ ^ 2 / 2) • z - x - τ • w) = z
    rw [show x + τ • w + (τ ^ 2 / 2) • z - x - τ • w = (τ ^ 2 / 2) • z by abel, smul_smul,
      div_mul_div_comm, mul_comm 2 (τ ^ 2), div_self (mul_ne_zero hτ2 two_ne_zero), one_smul]

/-- **Definition 13.11**: the second-order tangent set
`T²_C(x̄ | w) = limsup_{τ ↓ 0} [C - x̄ - τw]/(½τ²)`. -/
def secondOrderTangentSet (C : Set E) (x w : E) : Set E :=
  outerSetLimitAlong (𝓝[>] (0 : ℝ)) (parabolicBlowUp C x w)

/-- **Definition 13.11**: `C` is parabolically derivable at `x̄` for `w` when
`T²_C(x̄ | w)` is nonempty and achieved as a full limit. -/
def IsParabolicallyDerivable (C : Set E) (x w : E) : Prop :=
  (secondOrderTangentSet C x w).Nonempty ∧
    PKConvergesAlong (𝓝[>] (0 : ℝ)) (parabolicBlowUp C x w) (secondOrderTangentSet C x w)

/-- The arcs of formula 13(11): `ξ : [0, ε] → C` with `ξ(0) = x̄`, `ξ'₊(0) = w` and
`ξ''₊(0) = z`, the latter read as `[ξ(τ) - ξ(0) - τw]/(½τ²) → z`. -/
def HasParabolicArc (C : Set E) (x w z : E) : Prop :=
  ∃ ε > 0, ∃ ξ : ℝ → E, (∀ τ ∈ Icc 0 ε, ξ τ ∈ C) ∧ ξ 0 = x ∧
    Tendsto (fun τ ↦ τ⁻¹ • (ξ τ - x)) (𝓝[>] 0) (𝓝 w) ∧
    Tendsto (fun τ ↦ (2 / τ ^ 2) • (ξ τ - x - τ • w)) (𝓝[>] 0) (𝓝 z)

/-- The discussion of Definition 13.11: the vectors with an arc as in 13(11) are exactly
those in the inner limit of the parabolic difference sets. -/
theorem mem_innerSetLimitAlong_parabolicBlowUp_iff {C : Set E} {x w z : E} (hx : x ∈ C) :
    z ∈ innerSetLimitAlong (𝓝[>] (0 : ℝ)) (parabolicBlowUp C x w) ↔ HasParabolicArc C x w z := by
  constructor
  · intro hz
    set S := parabolicBlowUp C x w with hS
    -- the sets are eventually nonempty and approach `z`
    have hne : ∀ᶠ τ in 𝓝[>] (0 : ℝ), (S τ).Nonempty :=
      (hz univ univ_mem).mono fun τ h ↦ h.mono inter_subset_left
    have hd : Tendsto (fun τ ↦ infDist z (S τ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro r hr
      filter_upwards [hz (ball z r) (ball_mem_nhds z hr)] with τ ⟨y, hyS, hyb⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg]
      exact (infDist_le_dist_of_mem hyS).trans_lt (by rwa [dist_comm, ← mem_ball])
    obtain ⟨ε₀, hε₀, hε₀sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hne
    have hex : ∀ τ ∈ Ioo (0 : ℝ) ε₀, ∃ y ∈ S τ, dist z y < infDist z (S τ) + τ := fun τ hτ ↦
      (infDist_lt_iff (hε₀sub hτ)).1 (lt_add_of_pos_right _ hτ.1)
    choose! zτ hzτS hzτd using hex
    let ξ : ℝ → E := fun τ ↦ if τ ∈ Ioo (0 : ℝ) ε₀ then x + τ • w + (τ ^ 2 / 2) • zτ τ else x
    have hξ : ∀ τ ∈ Ioo (0 : ℝ) ε₀, ξ τ = x + τ • w + (τ ^ 2 / 2) • zτ τ := fun τ hτ ↦ if_pos hτ
    have hzlim : Tendsto zτ (𝓝[>] (0 : ℝ)) (𝓝 z) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have hup : Tendsto (fun τ ↦ infDist z (S τ) + τ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        simpa using hd.add (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
      refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hup
      filter_upwards [Ioo_mem_nhdsGT hε₀] with τ hτ
      rw [dist_comm]
      exact (hzτd τ hτ).le
    have hq : ∀ τ ∈ Ioo (0 : ℝ) ε₀, (2 / τ ^ 2) • (ξ τ - x - τ • w) = zτ τ := by
      intro τ hτ
      rw [hξ τ hτ, show x + τ • w + (τ ^ 2 / 2) • zτ τ - x - τ • w = (τ ^ 2 / 2) • zτ τ by abel,
        smul_smul, div_mul_div_comm, mul_comm 2 (τ ^ 2),
        div_self (mul_ne_zero (pow_ne_zero 2 hτ.1.ne') two_ne_zero), one_smul]
    refine ⟨ε₀ / 2, half_pos hε₀, ξ, ?_, if_neg (fun h ↦ lt_irrefl _ h.1), ?_, ?_⟩
    · intro τ hτ
      rcases eq_or_lt_of_le hτ.1 with h0 | hpos
      · rw [← h0]
        change (if (0 : ℝ) ∈ Ioo (0 : ℝ) ε₀ then _ else x) ∈ C
        rw [if_neg (fun h ↦ lt_irrefl _ h.1)]
        exact hx
      · have hτ' : τ ∈ Ioo (0 : ℝ) ε₀ := ⟨hpos, by linarith [hτ.2]⟩
        rw [hξ τ hτ']
        exact (mem_parabolicBlowUp_iff hpos.ne').1 (hzτS τ hτ')
    · have h1 : Tendsto (fun τ : ℝ ↦ w + (τ / 2) • zτ τ) (𝓝[>] (0 : ℝ)) (𝓝 w) := by
        have ht : Tendsto (fun τ : ℝ ↦ τ / 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          simpa using (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ)))).div_const 2
        simpa using tendsto_const_nhds.add (ht.smul hzlim)
      refine h1.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hε₀] with τ hτ
      rw [hξ τ hτ, add_assoc, add_sub_cancel_left, smul_add, smul_smul, inv_mul_cancel₀ hτ.1.ne',
        one_smul, smul_smul]
      congr 2
      field_simp
    · refine hzlim.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hε₀] with τ hτ
      exact (hq τ hτ).symm
  · rintro ⟨ε, hε, ξ, hξC, -, -, hlim⟩ V hV
    filter_upwards [hlim hV, Ioo_mem_nhdsGT hε] with τ hτV hτ
    refine ⟨_, ⟨ξ τ, hξC τ ⟨hτ.1.le, hτ.2.le⟩, rfl⟩, hτV⟩

/-- **Definition 13.11**, the arc form: `C` is parabolically derivable at `x̄` for `w` exactly
when `T²_C(x̄ | w)` is nonempty and each of its elements `z` has an arc as in 13(11). -/
theorem isParabolicallyDerivable_iff_hasParabolicArc {C : Set E} {x w : E} (hx : x ∈ C) :
    IsParabolicallyDerivable C x w ↔ (secondOrderTangentSet C x w).Nonempty ∧
      ∀ z ∈ secondOrderTangentSet C x w, HasParabolicArc C x w z := by
  constructor
  · rintro ⟨hne, hconv⟩
    refine ⟨hne, fun z hz ↦ (mem_innerSetLimitAlong_parabolicBlowUp_iff hx).1 ?_⟩
    rw [hconv.inner_eq]
    exact hz
  · rintro ⟨hne, harc⟩
    refine ⟨hne, Subset.antisymm ?_ ?_, rfl⟩
    · exact innerSetLimitAlong_subset_outerSetLimitAlong _
    · exact fun z hz ↦ (mem_innerSetLimitAlong_parabolicBlowUp_iff hx).2 (harc z hz)

end Definition1311

/-! ### Proposition 13.12 -/

section Proposition1312

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Proposition 13.12**: `T²_C(x̄ | w)` is closed. -/
theorem isClosed_secondOrderTangentSet (C : Set E) (x w : E) :
    IsClosed (secondOrderTangentSet C x w) :=
  isClosed_outerSetLimitAlong _ _

/-- **Proposition 13.12**, formula 13(12): if `C` is Clarke regular at `x̄`, then
`T²_C(x̄ | w) + u ⊂ T²_C(x̄ | w)` for every `u ∈ T_C(x̄)`. -/
theorem secondOrderTangentSet_add_tangent [FiniteDimensional ℝ E] {C : Set E} {x w z u : E}
    (hx : x ∈ C)
    (hreg : IsClarkeRegularAt C x) (hz : z ∈ secondOrderTangentSet C x w)
    (hu : u ∈ tangentCone C x) : z + u ∈ secondOrderTangentSet C x w := by
  rw [tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hx hreg] at hu
  intro V hV
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  have hu' := hu (ball u (r / 2)) (ball_mem_nhds u (half_pos hr))
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_prod_iff.1 hu'
  obtain ⟨W, hWo, hxW, hWA⟩ := mem_nhdsWithin.1 hA
  have hW : W ∈ 𝓝 x := hWo.mem_nhds hxW
  obtain ⟨σ₀, hσ₀, hσ₀B⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hB
  obtain ⟨ρ, hρ, hρW⟩ := Metric.mem_nhds_iff.1 hW
  -- points `x̄ + τw + ½τ²z'` with `z'` near `z` lie in `W` and `½τ²` is small, for small `τ`
  have hsmall : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ * ‖w‖ + τ ^ 2 / 2 * (‖z‖ + r) < ρ ∧ τ ^ 2 / 2 < σ₀ := by
    have h1 : Tendsto (fun τ : ℝ ↦ τ * ‖w‖ + τ ^ 2 / 2 * (‖z‖ + r)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun τ : ℝ ↦ τ * ‖w‖ + τ ^ 2 / 2 * (‖z‖ + r)) (𝓝 (0 : ℝ))
          (𝓝 (0 * ‖w‖ + 0 ^ 2 / 2 * (‖z‖ + r))) :=
        (by fun_prop : Continuous fun τ : ℝ ↦ τ * ‖w‖ + τ ^ 2 / 2 * (‖z‖ + r)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun τ : ℝ ↦ τ ^ 2 / 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun τ : ℝ ↦ τ ^ 2 / 2) (𝓝 (0 : ℝ)) (𝓝 (0 ^ 2 / 2)) :=
        (by fun_prop : Continuous fun τ : ℝ ↦ τ ^ 2 / 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact (h1.eventually (gt_mem_nhds hρ)).and (h2.eventually (gt_mem_nhds hσ₀))
  refine ((hz (ball z (r / 2)) (ball_mem_nhds z (half_pos hr))).and_eventually
    (hsmall.and self_mem_nhdsWithin)).mono ?_
  rintro τ ⟨⟨z', hz'S, hz'b⟩, ⟨hτρ, hτσ⟩, hτ⟩
  change 0 < τ at hτ
  have hx' := (mem_parabolicBlowUp_iff hτ.ne').1 hz'S
  set x' := x + τ • w + (τ ^ 2 / 2) • z' with hx'def
  have hx'W : x' ∈ W := by
    refine hρW ?_
    rw [mem_ball, dist_eq_norm, hx'def, add_assoc, add_sub_cancel_left]
    have hz'n : ‖z'‖ ≤ ‖z‖ + r := by
      have := norm_le_of_mem_closedBall (ball_subset_closedBall
        (show z' ∈ ball z r from ball_subset_ball (half_le_self hr.le) hz'b))
      linarith [norm_sub_norm_le z' z, (mem_ball_iff_norm.1
        (ball_subset_ball (half_le_self hr.le) hz'b)).le]
    calc ‖τ • w + (τ ^ 2 / 2) • z'‖ ≤ ‖τ • w‖ + ‖(τ ^ 2 / 2) • z'‖ := norm_add_le _ _
      _ = τ * ‖w‖ + τ ^ 2 / 2 * ‖z'‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hτ.le,
          Real.norm_of_nonneg (by positivity)]
      _ ≤ τ * ‖w‖ + τ ^ 2 / 2 * (‖z‖ + r) := by gcongr
      _ < ρ := hτρ
  obtain ⟨u', ⟨y, hyC, rfl⟩, hu'b⟩ :=
    hAB (show (x', τ ^ 2 / 2) ∈ A ×ˢ B from ⟨hWA ⟨hx'W, hx'⟩, hσ₀B ⟨by positivity, hτσ⟩⟩)
  refine ⟨z' + (τ ^ 2 / 2)⁻¹ • (y - x'), ?_, hrV ?_⟩
  · rw [mem_parabolicBlowUp_iff hτ.ne', smul_add, smul_smul,
      mul_inv_cancel₀ (by positivity : τ ^ 2 / 2 ≠ 0), one_smul]
    convert hyC using 1
    rw [hx'def]
    abel
  · rw [mem_ball, dist_eq_norm]
    calc ‖z' + (τ ^ 2 / 2)⁻¹ • (y - x') - (z + u)‖
        = ‖(z' - z) + ((τ ^ 2 / 2)⁻¹ • (y - x') - u)‖ := by congr 1; abel
      _ ≤ ‖z' - z‖ + ‖(τ ^ 2 / 2)⁻¹ • (y - x') - u‖ := norm_add_le _ _
      _ < r / 2 + r / 2 := add_lt_add (mem_ball_iff_norm.1 hz'b) (mem_ball_iff_norm.1 hu'b)
      _ = r := by ring

/-- **Proposition 13.12**: for a closed convex set, formula 13(12) holds. -/
theorem secondOrderTangentSet_add_tangent_of_convex [FiniteDimensional ℝ E] {C : Set E}
    {x w z u : E} (hconv : Convex ℝ C) (hcl : IsClosed C) (hx : x ∈ C)
    (hz : z ∈ secondOrderTangentSet C x w) (hu : u ∈ tangentCone C x) :
    z + u ∈ secondOrderTangentSet C x w :=
  secondOrderTangentSet_add_tangent hx (isClarkeRegularAt_of_convex hconv hx
    ⟨univ, univ_mem, isClosed_univ, by rwa [inter_univ]⟩) hz hu

/-- **Proposition 13.12**: under Clarke regularity a nonempty `T²_C(x̄ | w)` is unbounded,
unless `T_C(x̄) = {0}`. -/
theorem not_isBounded_secondOrderTangentSet [FiniteDimensional ℝ E] {C : Set E} {x w : E}
    (hx : x ∈ C) (hreg : IsClarkeRegularAt C x) (hne : (secondOrderTangentSet C x w).Nonempty)
    (hT : tangentCone C x ≠ {0}) : ¬ Bornology.IsBounded (secondOrderTangentSet C x w) := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ tangentCone C x, u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hT (Subset.antisymm h (singleton_subset_iff.2 (isCone_tangentCone hx).1))
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hR0 : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 (hR hz)
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖z‖) / ‖u‖)
  have hnpos : (0 : ℝ) < n :=
    lt_of_le_of_lt (div_nonneg (by linarith [norm_nonneg z]) hun.le) hn
  have hmem : z + (n : ℝ) • u ∈ secondOrderTangentSet C x w :=
    secondOrderTangentSet_add_tangent hx hreg hz ((isCone_tangentCone hx).2 hu hnpos)
  have h1 := mem_closedBall_zero_iff.1 (hR hmem)
  have h2 : (n : ℝ) * ‖u‖ - ‖z‖ ≤ ‖z + (n : ℝ) • u‖ := by
    have := norm_sub_norm_le ((n : ℝ) • u) (-z)
    rw [norm_smul, Real.norm_of_nonneg hnpos.le, norm_neg, sub_neg_eq_add, add_comm] at this
    linarith
  have h3 : R + ‖z‖ < n * ‖u‖ := by rwa [div_lt_iff₀ hun] at hn
  linarith

/-- The explicit second-order analysis of a polyhedron given by finitely many affine
inequalities: the outer limit is contained in the cone cut out by the constraints active
at `x̄` with `⟪aᵢ, w⟫ = 0`, and that cone is contained in the inner limit. -/
theorem parabolicBlowUp_setOf_inner_le {m : ℕ} {a : Fin m → E} {b : Fin m → ℝ} {x w : E}
    (hx : ∀ i, ⟪a i, x⟫_ℝ ≤ b i) (hw : ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w⟫_ℝ ≤ 0) :
    outerSetLimitAlong (𝓝[>] (0 : ℝ)) (parabolicBlowUp {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} x w) ⊆
        {z | ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w⟫_ℝ = 0 → ⟪a i, z⟫_ℝ ≤ 0} ∧
      {z | ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w⟫_ℝ = 0 → ⟪a i, z⟫_ℝ ≤ 0} ⊆
        innerSetLimitAlong (𝓝[>] (0 : ℝ))
          (parabolicBlowUp {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} x w) := by
  have hval : ∀ (τ : ℝ) (z : E) (i : Fin m), ⟪a i, x + τ • w + (τ ^ 2 / 2) • z⟫_ℝ =
      ⟪a i, x⟫_ℝ + τ * ⟪a i, w⟫_ℝ + τ ^ 2 / 2 * ⟪a i, z⟫_ℝ := by
    intro τ z i
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  constructor
  · intro z hz i hia hiw
    by_contra hpos
    push_neg at hpos
    have hV : {z' : E | 0 < ⟪a i, z'⟫_ℝ} ∈ 𝓝 z :=
      (isOpen_lt continuous_const (continuous_const.inner continuous_id)).mem_nhds hpos
    obtain ⟨τ, ⟨z', hz'S, hz'V⟩, hτ⟩ := ((hz _ hV).and_eventually self_mem_nhdsWithin).exists
    change 0 < τ at hτ
    have hmem := (mem_parabolicBlowUp_iff hτ.ne').1 hz'S i
    rw [hval, hia, hiw, mul_zero, add_zero] at hmem
    have : 0 < τ ^ 2 / 2 * ⟪a i, z'⟫_ℝ := mul_pos (by positivity) hz'V
    linarith
  · intro z hz V hV
    have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), z ∈ parabolicBlowUp {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} x w τ := by
      have hall : ∀ i, ∀ᶠ τ in 𝓝[>] (0 : ℝ), ⟪a i, x⟫_ℝ + τ * ⟪a i, w⟫_ℝ +
          τ ^ 2 / 2 * ⟪a i, z⟫_ℝ ≤ b i := by
        intro i
        have hcont : Continuous fun τ : ℝ ↦ ⟪a i, x⟫_ℝ + τ * ⟪a i, w⟫_ℝ +
            τ ^ 2 / 2 * ⟪a i, z⟫_ℝ := by fun_prop
        rcases lt_or_eq_of_le (hx i) with hlt | heq
        · have h0 : ⟪a i, x⟫_ℝ + 0 * ⟪a i, w⟫_ℝ + 0 ^ 2 / 2 * ⟪a i, z⟫_ℝ < b i := by simpa
          exact nhdsWithin_le_nhds ((hcont.tendsto 0).eventually (gt_mem_nhds h0) |>.mono
            fun τ hτ ↦ hτ.le)
        · rcases lt_or_eq_of_le (hw i heq) with hwlt | hweq
          · have hg : Continuous fun τ : ℝ ↦ ⟪a i, w⟫_ℝ + τ / 2 * ⟪a i, z⟫_ℝ := by fun_prop
            have h0 : ⟪a i, w⟫_ℝ + 0 / 2 * ⟪a i, z⟫_ℝ < 0 := by simpa using hwlt
            filter_upwards [nhdsWithin_le_nhds ((hg.tendsto 0).eventually (gt_mem_nhds h0)),
              self_mem_nhdsWithin] with τ hτ hτpos
            change 0 < τ at hτpos
            have := mul_neg_of_pos_of_neg hτpos hτ
            rw [heq]
            nlinarith
          · filter_upwards with τ
            rw [heq, hweq, mul_zero, add_zero]
            have := hz i heq hweq
            have : τ ^ 2 / 2 * ⟪a i, z⟫_ℝ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) this
            linarith
      filter_upwards [Filter.eventually_all.2 hall, self_mem_nhdsWithin] with τ hτ hτpos
      change 0 < τ at hτpos
      rw [mem_parabolicBlowUp_iff hτpos.ne']
      intro i
      rw [hval]
      exact hτ i
    filter_upwards [hev] with τ hτ
    exact ⟨z, hτ, mem_of_mem_nhds hV⟩

variable [FiniteDimensional ℝ E]

/-- **Proposition 13.12**, formula 13(13): a polyhedral set is parabolically derivable at
`x̄` for every `w ∈ T_C(x̄)`, and `T²_C(x̄ | w) = T_{T_C(x̄)}(w) = T_C(x̄) + ℝw`. -/
theorem IsPolyhedral.parabolic {C : Set E} (hC : IsPolyhedral C) {x w : E} (hx : x ∈ C)
    (hw : w ∈ tangentCone C x) :
    IsParabolicallyDerivable C x w ∧
      secondOrderTangentSet C x w = tangentCone (tangentCone C x) w ∧
      tangentCone (tangentCone C x) w = {z | ∃ k ∈ tangentCone C x, ∃ t : ℝ, z = k + t • w} := by
  obtain ⟨m, a, b, rfl⟩ := hC.isHPolyhedral.exists_inner_representation
  have hx' : ∀ i, ⟪a i, x⟫_ℝ ≤ b i := hx
  rw [tangentCone_setOf_inner_le hx'] at hw ⊢
  change ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w⟫_ℝ ≤ 0 at hw
  set P : Set E := {z | ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w⟫_ℝ = 0 → ⟪a i, z⟫_ℝ ≤ 0} with hP
  obtain ⟨hout, hin⟩ := parabolicBlowUp_setOf_inner_le hx' hw
  have hT2 : secondOrderTangentSet {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} x w = P :=
    Subset.antisymm hout (hin.trans (innerSetLimitAlong_subset_outerSetLimitAlong _))
  -- the tangent cone written as a homogeneous system
  classical
  let a' : Fin m → E := fun i ↦ if ⟪a i, x⟫_ℝ = b i then a i else 0
  have hK : {w' : E | ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w'⟫_ℝ ≤ 0} =
      {y : E | ∀ i, ⟪a' i, y⟫_ℝ ≤ (fun _ ↦ (0 : ℝ)) i} := by
    ext y
    simp only [mem_setOf_eq, a']
    refine forall_congr' fun i ↦ ?_
    split_ifs with h <;> simp [h]
  have hw' : ∀ i, ⟪a' i, w⟫_ℝ ≤ (fun _ ↦ (0 : ℝ)) i := by
    intro i
    simp only [a']
    split_ifs with h
    · exact hw i h
    · simp
  have hTK : tangentCone {w' : E | ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w'⟫_ℝ ≤ 0} w = P := by
    rw [hK, tangentCone_setOf_inner_le hw']
    ext z
    simp only [mem_setOf_eq, a', P]
    refine forall_congr' fun i ↦ ?_
    split_ifs with h <;> simp [h]
  have hsum : P = {z | ∃ k ∈ {w' : E | ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w'⟫_ℝ ≤ 0},
      ∃ t : ℝ, z = k + t • w} := by
    ext z
    constructor
    · intro hz
      -- choose a large multiple of `w` to push the strictly active constraints
      obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, 0 ≤ lam ∧ ∀ i, ⟪a i, x⟫_ℝ = b i → ⟪a i, w⟫_ℝ < 0 →
          ⟪a i, z⟫_ℝ + lam * ⟪a i, w⟫_ℝ ≤ 0 := by
        have hfin : ∀ i, ∃ l : ℝ, 0 ≤ l ∧ (⟪a i, x⟫_ℝ = b i → ⟪a i, w⟫_ℝ < 0 →
            ∀ l' ≥ l, ⟪a i, z⟫_ℝ + l' * ⟪a i, w⟫_ℝ ≤ 0) := by
          intro i
          by_cases hc : ⟪a i, x⟫_ℝ = b i ∧ ⟪a i, w⟫_ℝ < 0
          · refine ⟨|⟪a i, z⟫_ℝ| / (-⟪a i, w⟫_ℝ),
              div_nonneg (abs_nonneg _) (neg_nonneg.2 hc.2.le), fun _ _ l' hl' ↦ ?_⟩
            have hneg : 0 < -⟪a i, w⟫_ℝ := neg_pos.2 hc.2
            have : |⟪a i, z⟫_ℝ| ≤ l' * (-⟪a i, w⟫_ℝ) := by
              rwa [ge_iff_le, div_le_iff₀ hneg] at hl'
            nlinarith [le_abs_self ⟪a i, z⟫_ℝ]
          · exact ⟨0, le_rfl, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hc⟩
        choose l hl0 hl using hfin
        refine ⟨∑ i, l i, Finset.sum_nonneg fun i _ ↦ hl0 i, fun i h1 h2 ↦
          hl i h1 h2 _ (Finset.single_le_sum (fun j _ ↦ hl0 j) (Finset.mem_univ i))⟩
      refine ⟨z + lam • w, fun i hi ↦ ?_, -lam, by rw [neg_smul, add_neg_cancel_right]⟩
      rw [inner_add_right, real_inner_smul_right]
      rcases lt_or_eq_of_le (hw i hi) with hlt | heq
      · exact hlam.2 i hi hlt
      · rw [heq, mul_zero, add_zero]
        exact hz i hi heq
    · rintro ⟨k, hk, t, rfl⟩ i hi hiw
      rw [inner_add_right, real_inner_smul_right, hiw, mul_zero, add_zero]
      exact hk i hi
  have hinner : innerSetLimitAlong (𝓝[>] (0 : ℝ)) (parabolicBlowUp
      {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} x w) = secondOrderTangentSet
      {y : E | ∀ i, ⟪a i, y⟫_ℝ ≤ b i} x w :=
    Subset.antisymm (innerSetLimitAlong_subset_outerSetLimitAlong _) (by rw [hT2]; exact hin)
  refine ⟨⟨⟨0, by rw [hT2]; intro i _ _; simp⟩, hinner, rfl⟩, by rw [hT2, hTK],
    by rw [hTK, hsum]⟩

end Proposition1312

end RW
