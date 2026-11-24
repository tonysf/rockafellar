/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Proto-differentiability of polyhedral normal cones

Example 13.44.  For a polyhedral set `C`, `x̄ ∈ C`, `v̄ ∈ N_C(x̄)` and the critical cone
`K = {w ∈ T_C(x̄) ∣ w ⊥ v̄}`, the graph of `N_C` agrees near `(x̄, v̄)` with `(x̄, v̄) + gph N_K`
(`IsPolyhedral.normalCone_local_reduction`).  This gives the proto-differentiability of `N_C` at
`x̄` for `v̄` with `D N_C(x̄ ∣ v̄) = N_K`, and `P_C(x̄ + v̄ + h) = x̄ + P_K(h)` for small `h`, so that
`P_C` is semidifferentiable at `x̄ + v̄` with `D P_C(x̄ + v̄) = P_K`.  The book derives the example
from 13.43 (and so from Theorem 13.40); the local reduction is a direct route.
-/

import RockafellarWets.Chapter8.ProtoDifferentiability
import RockafellarWets.Chapter8.SingleValuedSemiderivatives
import RockafellarWets.Chapter8.HomogeneousMappings
import RockafellarWets.Chapter12.MonotoneDomains
import RockafellarWets.Chapter12.ConvexSubgradientMappings
import RockafellarWets.Chapter12.ResolventMaximality
import RockafellarWets.Chapter6.PolyhedralCones
import RockafellarWets.Chapter6.Polarity

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace Pointwise

namespace RW

/-! ### Set convergence from local agreement -/

/-- If the sets `S i` eventually agree with a closed set `G` on every ball around a fixed point,
they converge to `G`. -/
theorem pkConvergesAlong_of_eventually_inter_ball {ι X : Type*} [PseudoMetricSpace X]
    {l : Filter ι} [l.NeBot] {S : ι → Set X} {G : Set X} (hG : IsClosed G) (p₀ : X)
    (h : ∀ R > 0, ∀ᶠ i in l, S i ∩ ball p₀ R = G ∩ ball p₀ R) : PKConvergesAlong l S G := by
  have hinner : G ⊆ innerSetLimitAlong l S := by
    intro q hq V hV
    filter_upwards [h (dist q p₀ + 1) (by positivity)] with i hi
    have hq' : q ∈ S i ∩ ball p₀ (dist q p₀ + 1) := by
      rw [hi]; exact ⟨hq, by rw [mem_ball]; linarith⟩
    exact ⟨q, hq'.1, mem_of_mem_nhds hV⟩
  have houter : outerSetLimitAlong l S ⊆ G := by
    intro q hq
    by_contra hqG
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hG.isOpen_compl q hqG
    have hV : ball q δ ∩ ball p₀ (dist q p₀ + 1) ∈ 𝓝 q :=
      inter_mem (ball_mem_nhds q hδ) (isOpen_ball.mem_nhds (by rw [mem_ball]; linarith))
    obtain ⟨i, ⟨y, hyS, hyV⟩, hi⟩ :=
      ((hq _ hV).and_eventually (h (dist q p₀ + 1) (by positivity))).exists
    have hy : y ∈ G ∩ ball p₀ (dist q p₀ + 1) := by rw [← hi]; exact ⟨hyS, hyV.2⟩
    exact hball hyV.1 hy.1
  exact ⟨Subset.antisymm ((innerSetLimitAlong_subset_outerSetLimitAlong S).trans houter) hinner,
    Subset.antisymm houter (hinner.trans (innerSetLimitAlong_subset_outerSetLimitAlong S))⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Normal cones to convex cones -/

/-- The sum of two points of a convex cone lies in the cone. -/
theorem IsCone.add_mem_of_convex {K : Set E} (hKc : Convex ℝ K) (hK : IsCone K) {y w : E}
    (hy : y ∈ K) (hw : w ∈ K) : y + w ∈ K := by
  have h := hK.2 (hKc hy hw (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)) (by norm_num : (0 : ℝ) < 2)
  rwa [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul,
    one_smul] at h

/-- For a convex cone `K` and `w ∈ K`, `N_K(w) = {z ∈ K* ∣ z ⊥ w}`, `K*` the polar cone. -/
theorem normalCone_of_convex_isCone {K : Set E} (hKc : Convex ℝ K) (hK : IsCone K) {w : E}
    (hw : w ∈ K) : normalCone K w = {z | z ∈ polarCone K ∧ ⟪z, w⟫_ℝ = 0} := by
  rw [normalCone_eq_of_convex hKc hw]
  ext z
  simp only [mem_setOf_eq, mem_polarCone]
  constructor
  · intro h
    have h0 := h 0 hK.1
    have h2 := h ((2 : ℝ) • w) (hK.2 hw (by norm_num))
    rw [zero_sub, inner_neg_right] at h0
    rw [show (2 : ℝ) • w - w = w by rw [two_smul]; abel] at h2
    refine ⟨fun y hy ↦ ?_, by linarith⟩
    have := h (y + w) (hK.add_mem_of_convex hKc hy hw)
    rwa [add_sub_cancel_right] at this
  · rintro ⟨hz, hw0⟩ y hy
    rw [inner_sub_right, hw0, sub_zero]
    exact hz y hy

/-- Normal cones to a convex cone are invariant under positive scaling of the pair. -/
theorem smul_mem_normalCone_smul_iff {K : Set E} (hKc : Convex ℝ K) (hK : IsCone K) {τ : ℝ}
    (hτ : 0 < τ) {w z : E} : τ • z ∈ normalCone K (τ • w) ↔ z ∈ normalCone K w := by
  by_cases hw : w ∈ K
  · have hτw : τ • w ∈ K := hK.2 hw hτ
    rw [normalCone_of_convex_isCone hKc hK hτw, normalCone_of_convex_isCone hKc hK hw]
    simp only [mem_setOf_eq, mem_polarCone, real_inner_smul_left, real_inner_smul_right]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun y hy ↦ ?_, ?_⟩
      · have := h1 y hy
        nlinarith
      · have : τ * (τ * ⟪z, w⟫_ℝ) = 0 := h2
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hτ.ne'
        · rcases mul_eq_zero.1 h with h' | h'
          · exact absurd h' hτ.ne'
          · exact h'
    · rintro ⟨h1, h2⟩
      exact ⟨fun y hy ↦ mul_nonpos_of_nonneg_of_nonpos hτ.le (h1 y hy), by rw [h2]; ring⟩
  · have hτw : τ • w ∉ K := fun h ↦ hw (by
      have := hK.2 h (inv_pos.2 hτ)
      rwa [smul_smul, inv_mul_cancel₀ hτ.ne', one_smul] at this)
    rw [normalCone_eq_empty hw, normalCone_eq_empty hτw]
    simp

variable [FiniteDimensional ℝ E]

/-! ### Local reduction for polyhedral normal cones -/

/-- **The local reduction behind Example 13.44.**  For polyhedral `C`, `x̄ ∈ C`, `v̄ ∈ N_C(x̄)` and
`K = {w ∈ T_C(x̄) ∣ w ⊥ v̄}`, there is `ε > 0` with `v̄ + z ∈ N_C(x̄ + w) ⟺ z ∈ N_K(w)` whenever
`‖w‖, ‖z‖ < ε`. -/
theorem IsPolyhedral.normalCone_local_reduction {C : Set E} (hC : IsPolyhedral C) {x v : E}
    (hx : x ∈ C) (hv : v ∈ normalCone C x) :
    ∃ ε > 0, ∀ w z : E, ‖w‖ < ε → ‖z‖ < ε →
      (v + z ∈ normalCone C (x + w) ↔
        z ∈ normalCone {w | w ∈ tangentCone C x ∧ ⟪w, v⟫_ℝ = 0} w) := by
  set T := tangentCone C x with hT
  set N := normalCone C x with hN
  set K := {w | w ∈ T ∧ ⟪w, v⟫_ℝ = 0} with hK
  have hCc : Convex ℝ C := hC.convex
  have hTpoly : IsPolyhedral T := hC.isPolyhedral_tangentCone hx
  have hTc : Convex ℝ T := hTpoly.convex
  have hTcone : IsCone T := isCone_tangentCone hx
  have hTcl : IsClosed T := isClosed_tangentCone C x
  have hNT : N = polarCone T := normalCone_eq_polarCone_tangentCone hCc hx
  have hNpoly : IsPolyhedral N := hC.isPolyhedral_normalCone hx
  have hNc : Convex ℝ N := hNpoly.convex
  have hNcone : IsCone N := by rw [hNT]; exact isCone_polarCone T
  have hbip : polarCone N = T := by rw [hNT]; exact polarCone_bipolar_eq_self hTcl hTc hTcone
  -- the tangent cone to `N` at `v̄` is `K*`
  have hNN : normalCone N v = K := by
    rw [normalCone_of_convex_isCone hNc hNcone hv, hbip]
  have hTN : tangentCone N v = polarCone K := by
    rw [tangentCone_eq_polarCone_normalCone hNc hv, hNN]
  -- local conic structure of `C` at `x̄` and of `N` at `v̄`
  obtain ⟨V, hV, hCV⟩ := hC.exists_nhds_eq_tangentCone hx
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨V', hV', hNV⟩ := hNpoly.exists_nhds_eq_tangentCone hv
  obtain ⟨r', hr', hrV'⟩ := Metric.mem_nhds_iff.1 hV'
  have hmemC : ∀ w : E, ‖w‖ < r → (x + w ∈ C ↔ w ∈ T) := by
    intro w hw
    have hxw : x + w ∈ V := hrV (by rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hw)
    constructor
    · intro h
      have h' : x + w ∈ ((fun w ↦ x + w) '' T) ∩ V := by rw [← hCV]; exact ⟨h, hxw⟩
      obtain ⟨w', hw', hww⟩ := h'.1
      rw [add_right_inj] at hww
      rw [← hww]; exact hw'
    · intro h
      have h' : x + w ∈ C ∩ V := by rw [hCV]; exact ⟨⟨w, h, rfl⟩, hxw⟩
      exact h'.1
  have hmemN : ∀ z : E, ‖z‖ < r' → (v + z ∈ N ↔ z ∈ polarCone K) := by
    intro z hz
    rw [← hTN]
    have hvz : v + z ∈ V' := hrV' (by rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hz)
    constructor
    · intro h
      have h' : v + z ∈ ((fun z ↦ v + z) '' tangentCone N v) ∩ V' := by rw [← hNV]; exact ⟨h, hvz⟩
      obtain ⟨z', hz', hzz⟩ := h'.1
      rw [add_right_inj] at hzz
      rw [← hzz]; exact hz'
    · intro h
      have h' : v + z ∈ N ∩ V' := by rw [hNV]; exact ⟨⟨z, h, rfl⟩, hvz⟩
      exact h'.1
  -- normal cones to `C` near `x̄`
  have hNw : ∀ w : E, ‖w‖ < r / 2 → x + w ∈ C →
      normalCone C (x + w) = {u | u ∈ N ∧ ⟪u, w⟫_ℝ = 0} := by
    intro w hw hxw
    have hwT : w ∈ T := (hmemC w (by linarith)).1 hxw
    rw [normalCone_eq_of_convex hCc hxw]
    ext u
    simp only [mem_setOf_eq]
    constructor
    · intro h
      have h0 := h x hx
      have h2w : x + (2 : ℝ) • w ∈ C := (hmemC _ (by
        rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith)).2 (hTcone.2 hwT (by norm_num))
      have h2 := h _ h2w
      rw [show x - (x + w) = -w by abel, inner_neg_right] at h0
      rw [show x + (2 : ℝ) • w - (x + w) = w by rw [two_smul]; abel] at h2
      have huw : ⟪u, w⟫_ℝ = 0 := by linarith
      refine ⟨?_, huw⟩
      rw [hNT]
      intro t ht
      set s : ℝ := r / (2 * (‖t‖ + 1)) with hs
      have hs0 : 0 < s := by positivity
      have hst : ‖s • t‖ < r := by
        rw [norm_smul, Real.norm_of_nonneg hs0.le, hs]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg t]
      have hxs : x + s • t ∈ C := (hmemC _ hst).2 (hTcone.2 ht hs0)
      have := h _ hxs
      rw [show x + s • t - (x + w) = s • t - w by abel, inner_sub_right, huw, sub_zero,
        real_inner_smul_right] at this
      exact nonpos_of_mul_nonpos_right this hs0
    · rintro ⟨huN, huw⟩ y hy
      have hyx : y - x ∈ T := by
        rw [hT, tangentCone_eq_closure_radialCone hCc hx]
        exact subset_closure ⟨1, one_pos, by rw [one_smul, add_sub_cancel]; exact hy⟩
      rw [hNT] at huN
      rw [show y - (x + w) = (y - x) - w by abel, inner_sub_right, huw, sub_zero]
      exact huN _ hyx
  have hKc : Convex ℝ K := by
    intro y₁ hy₁ y₂ hy₂ a b ha hb hab
    exact ⟨hTc hy₁.1 hy₂.1 ha hb hab, by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hy₁.2, hy₂.2]; ring⟩
  have hKcone : IsCone K := ⟨⟨hTcone.1, inner_zero_left _⟩, fun y hy c hc ↦
    ⟨hTcone.2 hy.1 hc, by rw [real_inner_smul_left, hy.2, mul_zero]⟩⟩
  refine ⟨min (r / 2) (r' / 2), lt_min (by positivity) (by positivity), fun w z hw hz ↦ ?_⟩
  have hw2 : ‖w‖ < r / 2 := lt_of_lt_of_le hw (min_le_left _ _)
  have hz2 : ‖z‖ < r' / 2 := lt_of_lt_of_le hz (min_le_right _ _)
  constructor
  · intro h
    have hxw : x + w ∈ C := h.1
    have hwT : w ∈ T := (hmemC w (by linarith)).1 hxw
    rw [hNw w hw2 hxw] at h
    obtain ⟨hvzN, hvzw⟩ := h
    have hzK : z ∈ polarCone K := (hmemN z (by linarith)).1 hvzN
    -- `v̄ + 2z ∈ N`
    have h2z : v + (2 : ℝ) • z ∈ N := (hmemN _ (by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith)).2
      ((isCone_polarCone K).2 hzK (by norm_num))
    rw [hNT] at h2z
    have hv' : v ∈ polarCone T := by rw [← hNT]; exact hv
    have h1 := h2z w hwT
    have h3 := hv' w hwT
    rw [inner_add_left, real_inner_smul_left] at h1
    rw [inner_add_left] at hvzw
    have hvw : ⟪v, w⟫_ℝ = 0 := by linarith
    have hwK : w ∈ K := ⟨hwT, by rw [real_inner_comm]; exact hvw⟩
    rw [normalCone_of_convex_isCone hKc hKcone hwK]
    exact ⟨hzK, by linarith⟩
  · intro h
    have hwK : w ∈ K := h.1
    rw [normalCone_of_convex_isCone hKc hKcone hwK] at h
    obtain ⟨hzK, hzw⟩ := h
    have hxw : x + w ∈ C := (hmemC w (by linarith)).2 hwK.1
    rw [hNw w hw2 hxw]
    refine ⟨(hmemN z (by linarith)).2 hzK, ?_⟩
    rw [inner_add_left, hzw, add_zero, real_inner_comm]
    exact hwK.2

/-! ### Example 13.44 -/

/-- The critical cone `K = {w ∈ T_C(x̄) ∣ w ⊥ v̄}` of a polyhedral set is a closed convex cone. -/
theorem IsPolyhedral.critical_cone_properties {C : Set E} (hC : IsPolyhedral C) {x : E}
    (hx : x ∈ C) (v : E) :
    IsClosed {w | w ∈ tangentCone C x ∧ ⟪w, v⟫_ℝ = 0} ∧
    Convex ℝ {w | w ∈ tangentCone C x ∧ ⟪w, v⟫_ℝ = 0} ∧
    IsCone {w | w ∈ tangentCone C x ∧ ⟪w, v⟫_ℝ = 0} := by
  have hTc : Convex ℝ (tangentCone C x) := (hC.isPolyhedral_tangentCone hx).convex
  have hTcone : IsCone (tangentCone C x) := isCone_tangentCone hx
  refine ⟨(isClosed_tangentCone C x).inter (isClosed_eq (continuous_id.inner continuous_const)
    continuous_const), ?_, ⟨⟨hTcone.1, inner_zero_left _⟩, fun y hy c hc ↦
      ⟨hTcone.2 hy.1 hc, by rw [real_inner_smul_left, hy.2, mul_zero]⟩⟩⟩
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  exact ⟨hTc hy₁.1 hy₂.1 ha hb hab, by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hy₁.2, hy₂.2]; ring⟩

omit [FiniteDimensional ℝ E] in
/-- The graph of the normal cone mapping of a closed convex cone is closed. -/
theorem isClosed_svGraph_normalCone_of_cone {K : Set E} (hKcl : IsClosed K) (hKc : Convex ℝ K)
    (hK : IsCone K) : IsClosed (svGraph (normalCone K)) := by
  have heq : svGraph (normalCone K) =
      {p : E × E | p.1 ∈ K ∧ p.2 ∈ polarCone K ∧ ⟪p.2, p.1⟫_ℝ = 0} := by
    ext ⟨w, z⟩
    simp only [mem_svGraph, mem_setOf_eq]
    by_cases hw : w ∈ K
    · rw [normalCone_of_convex_isCone hKc hK hw]
      simp [hw]
    · rw [normalCone_eq_empty hw]
      simp [hw]
  rw [heq]
  exact (hKcl.preimage continuous_fst).inter (((isClosed_polarCone K).preimage continuous_snd).inter
    (isClosed_eq (continuous_snd.inner continuous_fst) continuous_const))

/-- **Example 13.44** (polyhedral sets).  For polyhedral `C`, `x̄ ∈ C`, `v̄ ∈ N_C(x̄)` and
`K = {w ∈ T_C(x̄) ∣ w ⊥ v̄}`: (a) `N_C` is proto-differentiable at `x̄` for `v̄` with
`D N_C(x̄ ∣ v̄) = N_K`; (b) `P_C(x̄ + v̄) = {x̄}` and `P_C` is semidifferentiable at `ū = x̄ + v̄`
with `D P_C(ū) = P_K`. -/
theorem polyhedral_sets_proto_differentiability {C : Set E} (hC : IsPolyhedral C) {x v : E}
    (hx : x ∈ C) (hv : v ∈ normalCone C x) :
    IsProtoDifferentiableAt (normalCone C) x v ∧
    graphicalDerivative (normalCone C) x v =
      normalCone {w | w ∈ tangentCone C x ∧ ⟪w, v⟫_ℝ = 0} ∧
    projMapping C (x + v) = {x} ∧
    HasMappingSemiderivative (projMapping C) (x + v) x
      (projMapping {w | w ∈ tangentCone C x ∧ ⟪w, v⟫_ℝ = 0}) := by
  set K := {w | w ∈ tangentCone C x ∧ ⟪w, v⟫_ℝ = 0} with hK
  obtain ⟨hKcl, hKc, hKcone⟩ := hC.critical_cone_properties hx v
  have hCc : Convex ℝ C := hC.convex
  obtain ⟨ε, hε, hred⟩ := hC.normalCone_local_reduction hx hv
  -- (a) the difference quotients of `N_C` agree with `gph N_K` on bounded sets
  have hconv : PKConvergesAlong (𝓝[>] (0 : ℝ))
      (fun τ ↦ svGraph (mappingDifferenceQuotient (normalCone C) x v τ))
      (svGraph (normalCone K)) := by
    refine pkConvergesAlong_of_eventually_inter_ball
      (isClosed_svGraph_normalCone_of_cone hKcl hKc hKcone) (0 : E × E) fun R hR ↦ ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (div_pos hε hR))]
      with τ hτ hτR
    have hτ' : (0 : ℝ) < τ := hτ
    have hτR' : τ * R < ε := by
      rw [mem_Iio, lt_div_iff₀ hR] at hτR; exact hτR
    ext ⟨w, z⟩
    simp only [mem_inter_iff, mem_svGraph, mem_ball_zero_iff]
    constructor
    · rintro ⟨h, hwz⟩
      refine ⟨?_, hwz⟩
      have hw : ‖w‖ < R := lt_of_le_of_lt (norm_fst_le (w, z)) hwz
      have hz : ‖z‖ < R := lt_of_le_of_lt (norm_snd_le (w, z)) hwz
      rw [mem_mappingDifferenceQuotient_iff hτ'.ne'] at h
      have hτw : ‖τ • w‖ < ε := by
        rw [norm_smul, Real.norm_of_nonneg hτ'.le]; nlinarith [norm_nonneg w]
      have hτz : ‖τ • z‖ < ε := by
        rw [norm_smul, Real.norm_of_nonneg hτ'.le]; nlinarith [norm_nonneg z]
      exact (smul_mem_normalCone_smul_iff hKc hKcone hτ').1 ((hred _ _ hτw hτz).1 h)
    · rintro ⟨h, hwz⟩
      refine ⟨?_, hwz⟩
      have hw : ‖w‖ < R := lt_of_le_of_lt (norm_fst_le (w, z)) hwz
      have hz : ‖z‖ < R := lt_of_le_of_lt (norm_snd_le (w, z)) hwz
      rw [mem_mappingDifferenceQuotient_iff hτ'.ne']
      have hτw : ‖τ • w‖ < ε := by
        rw [norm_smul, Real.norm_of_nonneg hτ'.le]; nlinarith [norm_nonneg w]
      have hτz : ‖τ • z‖ < ε := by
        rw [norm_smul, Real.norm_of_nonneg hτ'.le]; nlinarith [norm_nonneg z]
      exact (hred _ _ hτw hτz).2 ((smul_mem_normalCone_smul_iff hKc hKcone hτ').2 h)
  have hgraph : svGraph (graphicalDerivative (normalCone C) x v) = svGraph (normalCone K) := by
    rw [svGraph_graphicalDerivative_eq_outerLimit]; exact hconv.2
  have hD : graphicalDerivative (normalCone C) x v = normalCone K := svGraph_injective hgraph
  -- (b) projections
  have hKne : K.Nonempty := ⟨0, hKcone.1⟩
  set pK := resolventMap (normalCone K) 1 with hpK
  have hPK : ∀ w, projMapping K w = {pK w} := projMapping_eq_singleton_resolventMap hKcl hKc hKne
  have hpK0 : pK 0 = 0 := resolventMap_normalCone_self hKcl hKc hKcone.1
  have hLip : LipschitzWith 1 pK :=
    (svMaximalMonotone_normalCone hKcl hKc hKne).lipschitzWith_resolventMap one_pos
  have hmemP : ∀ (D : Set E), Convex ℝ D → ∀ p u : E, p ∈ D → u - p ∈ normalCone D p →
      p ∈ projMapping D u := by
    intro D hD p u _ hu
    rw [← svResolvent_normalCone_eq_projMapping hD, mem_svResolvent]
    exact ⟨u - p, hu, by rw [one_smul, add_sub_cancel]⟩
  have hnormP : ∀ (D : Set E), Convex ℝ D → ∀ p u : E, p ∈ projMapping D u →
      u - p ∈ normalCone D p := by
    intro D hD p u hp
    rw [← svResolvent_normalCone_eq_projMapping hD, mem_svResolvent] at hp
    obtain ⟨n, hn, hpn⟩ := hp
    rw [← hpn, one_smul, add_sub_cancel_left]
    exact hn
  have hPx : projMapping C (x + v) = {x} :=
    projMapping_eq_singleton hCc (hmemP C hCc x (x + v) hx (by rw [add_sub_cancel_left]; exact hv))
  have hfun : projMapping K = svSingleton pK := funext fun w ↦ hPK w
  refine ⟨by unfold IsProtoDifferentiableAt; rw [hgraph]; exact hconv, hD, hPx, ?_⟩
  rw [hfun]
  refine hasMappingSemiderivative_of_expansion hLip.continuous
    ⟨by change (0 : E) ∈ ({pK 0} : Set E); rw [hpK0]; exact mem_singleton _, fun w c hc ↦ ?_⟩
    fun ε' hε' ↦ ?_
  · -- positive homogeneity of `P_K`
    have hw := (resolventMap_normalCone_eq_iff hKcl hKc hKne (z := w) (y := pK w)).1 rfl
    have hcw : pK (c • w) = c • pK w := by
      rw [resolventMap_normalCone_eq_iff hKcl hKc hKne]
      refine ⟨hKcone.2 hw.1 hc, fun a ha ↦ ?_⟩
      have h1 := hw.2 (c⁻¹ • a) (hKcone.2 ha (inv_pos.2 hc))
      have heq : c • w - c • pK w = c • (w - pK w) := by rw [smul_sub]
      have heq2 : a - c • pK w = c • (c⁻¹ • a - pK w) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
      rw [heq, heq2, real_inner_smul_left, real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos hc.le (mul_nonpos_of_nonneg_of_nonpos hc.le h1)
    change ({pK (c • w)} : Set E) = c • ({pK w} : Set E)
    rw [hcw, Set.smul_set_singleton]
  · -- the expansion holds with zero error near `x̄ + v̄`
    have hball : ball (x + v) (ε / 2) ∈ 𝓝 (x + v) := ball_mem_nhds _ (by positivity)
    filter_upwards [hball] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    set h := y - (x + v) with hh
    have hq : pK h ∈ projMapping K h := by rw [hPK]; exact mem_singleton _
    have hqK : pK h ∈ K := hq.1
    have hqN : h - pK h ∈ normalCone K (pK h) := hnormP K hKc _ _ hq
    have hqn : ‖pK h‖ ≤ ‖h‖ := by
      have := hLip.dist_le_mul h 0
      rw [hpK0, NNReal.coe_one, one_mul, dist_zero_right, dist_zero_right] at this
      exact this
    have hq1 : ‖pK h‖ < ε := by linarith
    have hq2 : ‖h - pK h‖ < ε := by
      calc ‖h - pK h‖ ≤ ‖h‖ + ‖pK h‖ := norm_sub_le _ _
        _ < ε := by linarith
    have hmem : v + (h - pK h) ∈ normalCone C (x + pK h) := (hred _ _ hq1 hq2).2 hqN
    have hxq : x + pK h ∈ projMapping C y := by
      refine hmemP C hCc _ _ hmem.1 ?_
      rw [show y - (x + pK h) = v + (h - pK h) by rw [hh]; abel]
      exact hmem
    rw [projMapping_eq_singleton hCc hxq]
    refine ⟨singleton_nonempty _, fun p hp ↦ ?_⟩
    rw [mem_singleton_iff] at hp
    rw [hp, show x + pK h - x - pK (y - (x + v)) = 0 by rw [← hh]; abel, norm_zero]
    positivity

end RW
