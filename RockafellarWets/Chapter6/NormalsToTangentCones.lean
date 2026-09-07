/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Normals to Tangent Cones

Proposition 6.27 and the second polarity relation 6.28(b).

The book routes 6.27(a) through the graphical-limsup inclusion of 6.18(b),
proved there for a general normal vector by a diagonalization on top of
6.18(a).  What 6.27(b) actually consumes, and with it 6.28(b), is only the
*proximal* case, and that case does not need 6.18(a) or the diagonalization:
it is 4.19 and the inner half of 5.35 applied once.

The two structural facts making it work are that the magnified difference set
`[C - x̄]/τ` is the preimage of `C` under the affine homeomorphism
`z ↦ x̄ + τz`, so that proximal normals correspond exactly under the
magnification, and that a nearest point in a set stays a nearest point in any
subset still containing it -- which is what lets the subsequential limit `D`
supplied by 4.19 be used in place of the tangent cone itself.  Note that no
sequence of scales need realize the whole tangent cone; only the single point
carrying the proximal normal has to be captured.
-/

import RockafellarWets.Chapter4.SetConvergenceCompactness
import RockafellarWets.Chapter5.ProjectionGraphicalConvergence
import RockafellarWets.Chapter6.ClarkeRegularityCharacterizations
import RockafellarWets.Chapter6.ElementaryCones
import RockafellarWets.Chapter6.ProximalNormals

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section Magnification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The magnified difference set is the preimage of `C` under the affine
homeomorphism `z ↦ x̄ + τz`. -/
theorem blowUp_eq_preimage {C : Set E} {x : E} {τ : ℝ} (hτ : τ ≠ 0) :
    blowUp C x τ = (fun z ↦ x + τ • z) ⁻¹' C := by
  ext z
  simp only [mem_blowUp, mem_preimage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have heq : x + τ • (τ⁻¹ • (y - x)) = y := by
      rw [smul_smul, mul_inv_cancel₀ hτ, one_smul]
      abel
    rwa [heq]
  · intro hz
    refine ⟨x + τ • z, hz, ?_⟩
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hτ, one_smul]

theorem isClosed_blowUp {C : Set E} (hC : IsClosed C) (x : E) {τ : ℝ} (hτ : τ ≠ 0) :
    IsClosed (blowUp C x τ) := by
  rw [blowUp_eq_preimage hτ]
  exact hC.preimage (continuous_const.add (continuous_const_smul τ))

theorem add_smul_mem_of_mem_blowUp {C : Set E} {x : E} {τ : ℝ} (hτ : τ ≠ 0) {z : E}
    (hz : z ∈ blowUp C x τ) : x + τ • z ∈ C := by
  rwa [blowUp_eq_preimage hτ] at hz

end Magnification

section MagnifiedProjections

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Nearest points correspond under magnification: the affine map
`z ↦ x̄ + τz` scales all distances by `τ`. -/
theorem mem_projMapping_blowUp {C : Set E} {x : E} {τ : ℝ} (hτ : 0 < τ) {u w : E} :
    w ∈ projMapping (blowUp C x τ) u ↔ x + τ • w ∈ projMapping C (x + τ • u) := by
  have hnorm : ∀ a b : E, ‖(x + τ • a) - (x + τ • b)‖ = τ * ‖a - b‖ := by
    intro a b
    have hsub : (x + τ • a) - (x + τ • b) = τ • (a - b) := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  rw [blowUp_eq_preimage hτ.ne']
  constructor
  · rintro ⟨hw, hmin⟩
    refine ⟨hw, fun y hy ↦ ?_⟩
    have hy' : τ⁻¹ • (y - x) ∈ (fun z ↦ x + τ • z) ⁻¹' C := by
      have heq : x + τ • (τ⁻¹ • (y - x)) = y := by
        rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
        abel
      rw [mem_preimage, heq]
      exact hy
    have hle := hmin _ hy'
    have heq : x + τ • (τ⁻¹ • (y - x)) = y := by
      rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
      abel
    rw [hnorm w u, ← heq, hnorm (τ⁻¹ • (y - x)) u]
    exact mul_le_mul_of_nonneg_left hle hτ.le
  · rintro ⟨hw, hmin⟩
    refine ⟨hw, fun z hz ↦ ?_⟩
    have hle := hmin _ hz
    rw [hnorm w u, hnorm z u] at hle
    exact le_of_mul_le_mul_left hle hτ

/-- Proximal normals correspond under magnification. -/
theorem mem_proximalNormalCone_blowUp {C : Set E} {x : E} {τ : ℝ} (hτ : 0 < τ)
    {w v : E} :
    v ∈ proximalNormalCone (blowUp C x τ) w ↔ v ∈ proximalNormalCone C (x + τ • w) := by
  constructor
  · rintro ⟨σ, hσ, hproj⟩
    refine ⟨τ * σ, by positivity, ?_⟩
    rw [mem_projMapping_blowUp hτ] at hproj
    have heq : x + τ • (w + σ • v) = x + τ • w + (τ * σ) • v := by module
    rwa [heq] at hproj
  · rintro ⟨σ, hσ, hproj⟩
    refine ⟨σ / τ, by positivity, ?_⟩
    rw [mem_projMapping_blowUp hτ]
    have heq : x + τ • (w + (σ / τ) • v) = x + τ • w + σ • v := by
      match_scalars <;> field_simp
    rwa [heq]

end MagnifiedProjections

section ProximalTransfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The proximal case of 6.27(a), for a closed set.  A proximal normal to the
tangent cone is a normal vector to the set itself. -/
private theorem proximalNormalCone_tangentCone_subset_normalCone_of_isClosed
    {C : Set E} (hC : IsClosed C) {x : E} (hx : x ∈ C) {w v : E}
    (hv : v ∈ proximalNormalCone (tangentCone C x) w) : v ∈ normalCone C x := by
  obtain ⟨σ, hσ, hproj⟩ := hv
  have hwT : w ∈ tangentCone C x := hproj.1
  obtain ⟨xs, τs, hxC, -, hτpos, hτ0, hq⟩ := hwT
  have hmem : ∀ n, (τs n)⁻¹ • (xs n - x) ∈ blowUp C x (τs n) := fun n ↦ ⟨xs n, hxC n, rfl⟩
  have hclosed : ∀ n, IsClosed (blowUp C x (τs n)) := fun n ↦
    isClosed_blowUp hC x (hτpos n).ne'
  obtain ⟨φ, D, hφ, hPK⟩ := exists_pkConvergent_subsequence (fun n ↦ blowUp C x (τs n))
  have hwD : w ∈ D := by
    rw [← hPK.1]
    intro V hV
    have hto : Tendsto (fun k ↦ (τs (φ k))⁻¹ • (xs (φ k) - x)) atTop (nhds w) :=
      hq.comp hφ.tendsto_atTop
    filter_upwards [hto hV] with k hk
    exact ⟨_, hmem (φ k), hk⟩
  have hDT : D ⊆ tangentCone C x := by
    intro z hz
    rw [← hPK.2] at hz
    obtain ⟨ψ, y, hψ, hyC, hyto⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hz
    refine mem_tangentCone_of_forall (xs := fun k ↦ x + τs (φ (ψ k)) • y k)
      (τs := fun k ↦ τs (φ (ψ k))) (fun k ↦ ?_) (fun k ↦ hτpos _) ?_ ?_
    · exact add_smul_mem_of_mem_blowUp (hτpos _).ne' (hyC k)
    · exact hτ0.comp ((hφ.comp hψ).tendsto_atTop)
    · have heq : ∀ k, (τs (φ (ψ k)))⁻¹ • ((x + τs (φ (ψ k)) • y k) - x) = y k := by
        intro k
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (hτpos _).ne', one_smul]
      exact hyto.congr fun k ↦ (heq k).symm
  have hprojD : w ∈ projMapping D (w + σ • v) :=
    ⟨hwD, fun z hz ↦ hproj.2 z (hDT hz)⟩
  have hgraph : ((w + σ • v, w) : E × E)
      ∈ innerSetLimit (fun k ↦ svGraph (projMapping (blowUp C x (τs (φ k))))) :=
    svGraph_projMapping_subset_innerSetLimit (fun k ↦ hclosed (φ k)) hPK hprojD
  obtain ⟨ψ, qs, hψ, hqs, hqto⟩ :=
    mem_outerSetLimit_iff_exists_subsequence.1 (innerSetLimit_subset_outerSetLimit _ hgraph)
  have hfst : Tendsto (fun k ↦ (qs k).1) atTop (nhds (w + σ • v)) :=
    (continuous_fst.tendsto _).comp hqto
  have hsnd : Tendsto (fun k ↦ (qs k).2) atTop (nhds w) :=
    (continuous_snd.tendsto _).comp hqto
  have hprox : ∀ k, (qs k).1 - (qs k).2
      ∈ proximalNormalCone (blowUp C x (τs (φ (ψ k)))) ((qs k).2) := by
    intro k
    refine ⟨1, one_pos, ?_⟩
    have heq : (qs k).2 + (1 : ℝ) • ((qs k).1 - (qs k).2) = (qs k).1 := by module
    rw [heq]
    exact hqs k
  have hprox' : ∀ k, (qs k).1 - (qs k).2
      ∈ regularNormalCone C (x + τs (φ (ψ k)) • (qs k).2) := by
    intro k
    refine proximalNormalCone_subset_regularNormalCone ?_
    rw [← mem_proximalNormalCone_blowUp (hτpos _)]
    exact hprox k
  have hbase : Tendsto (fun k ↦ x + τs (φ (ψ k)) • (qs k).2) atTop (nhds x) := by
    have ht : Tendsto (fun k ↦ τs (φ (ψ k))) atTop (nhds 0) :=
      hτ0.comp ((hφ.comp hψ).tendsto_atTop)
    have h := tendsto_const_nhds (x := x) (f := atTop (α := ℕ)) |>.add (ht.smul hsnd)
    simpa using h
  have hvec : Tendsto (fun k ↦ (qs k).1 - (qs k).2) atTop (nhds (σ • v)) := by
    have h := hfst.sub hsnd
    simpa using h
  have hσv : σ • v ∈ normalCone C x :=
    mem_normalCone_of_forall hx hbase hprox' hvec
  have hscale := (isCone_normalCone hx).2 hσv (c := σ⁻¹) (by positivity)
  rwa [smul_smul, inv_mul_cancel₀ hσ.ne', one_smul] at hscale

/-- **Proposition 6.27(a)**, the case the rest of the section uses: at a point
where `C` is locally closed, every *proximal* normal to the tangent cone
`T = T_C(x̄)`, at any of its points, is a normal vector to `C` at `x̄`. -/
theorem proximalNormalCone_tangentCone_subset_normalCone {C : Set E} {x : E}
    (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) (w : E) :
    proximalNormalCone (tangentCone C x) w ⊆ normalCone C x := by
  obtain ⟨V, hV, -, hCVclosed⟩ := hlc
  intro v hv
  have hxCV : x ∈ C ∩ V := ⟨hx, mem_of_mem_nhds hV⟩
  rw [← normalCone_inter_nhds (C := C) hV]
  refine proximalNormalCone_tangentCone_subset_normalCone_of_isClosed hCVclosed hxCV
    (w := w) ?_
  rwa [tangentCone_inter_nhds hV]

end ProximalTransfer

section TangentNormalEstimate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Proposition 6.27(b)**: for `w` outside the tangent cone `T = T_C(x̄)`
there is a unit normal `v ∈ N_C(x̄)` with `⟪v, w⟫ = d_T(w)`.

The vector is the normalized displacement from a nearest point `w̄ ∈ P_T(w)`.
Because `T` is a cone, the quadratic `τ ↦ ‖τw̄ - w‖²` is minimized over
`τ ≥ 0` at `τ = 1`, which forces `⟪w̄, w⟫ = ‖w̄‖²`; no limiting argument is
needed for that, only the value of the quadratic at its unconstrained
minimizer. -/
theorem exists_mem_normalCone_norm_eq_one_inner_eq_infDist {C : Set E} {x : E}
    (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) {w : E} (hw : w ∉ tangentCone C x) :
    ∃ v ∈ normalCone C x, ‖v‖ = 1 ∧ ⟪v, w⟫_ℝ = infDist w (tangentCone C x) := by
  have hcone := isCone_tangentCone hx
  have hTclosed : IsClosed (tangentCone C x) := isClosed_tangentCone C x
  have hTne : (tangentCone C x).Nonempty := ⟨0, hcone.1⟩
  obtain ⟨wbar, hwbarT, hwbarmin⟩ := projMapping_nonempty hTclosed hTne w
  have hne : w - wbar ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hw (h ▸ hwbarT)
  have hnpos : 0 < ‖w - wbar‖ := norm_pos_iff.2 hne
  -- the tangent cone is a cone, so the whole ray through `wbar` is available
  have hmemray : ∀ τ : ℝ, 0 ≤ τ → τ • wbar ∈ tangentCone C x := by
    intro τ hτ
    rcases hτ.eq_or_lt with h | h
    · rw [← h, zero_smul]
      exact hcone.1
    · exact hcone.2 hwbarT h
  have hsq : ∀ τ : ℝ, ‖τ • wbar - w‖ ^ 2
      = τ ^ 2 * ‖wbar‖ ^ 2 - 2 * (τ * ⟪wbar, w⟫_ℝ) + ‖w‖ ^ 2 := by
    intro τ
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs, mul_pow,
      sq_abs]
  have hsq1 : ‖wbar - w‖ ^ 2 = ‖wbar‖ ^ 2 - 2 * ⟪wbar, w⟫_ℝ + ‖w‖ ^ 2 :=
    norm_sub_sq_real wbar w
  have hg : ∀ τ : ℝ, 0 ≤ τ → ‖wbar - w‖ ^ 2 ≤ ‖τ • wbar - w‖ ^ 2 := by
    intro τ hτ
    exact pow_le_pow_left₀ (norm_nonneg _) (hwbarmin _ (hmemray τ hτ)) 2
  have hb : (0 : ℝ) ≤ ‖wbar‖ ^ 2 := sq_nonneg _
  have hinner : ⟪wbar, w⟫_ℝ = ‖wbar‖ ^ 2 := by
    rcases hb.eq_or_lt with hb0 | hbpos
    · have hwbar0 : wbar = 0 := by
        have hn : ‖wbar‖ = 0 := by nlinarith [norm_nonneg wbar]
        exact norm_eq_zero.1 hn
      rw [hwbar0]
      simp
    · rcases le_or_gt 0 (⟪wbar, w⟫_ℝ) with hc | hc
      · have hτ0 : (0 : ℝ) ≤ ⟪wbar, w⟫_ℝ / ‖wbar‖ ^ 2 := div_nonneg hc hb
        have h1 := hg _ hτ0
        rw [hsq1, hsq] at h1
        have hbne : ‖wbar‖ ^ 2 ≠ 0 := ne_of_gt hbpos
        have hexp : (⟪wbar, w⟫_ℝ / ‖wbar‖ ^ 2) ^ 2 * ‖wbar‖ ^ 2
            - 2 * (⟪wbar, w⟫_ℝ / ‖wbar‖ ^ 2 * ⟪wbar, w⟫_ℝ)
            = -(⟪wbar, w⟫_ℝ ^ 2 / ‖wbar‖ ^ 2) := by
          field_simp
          ring
        rw [hexp] at h1
        have h2 : ‖wbar‖ ^ 2 - 2 * ⟪wbar, w⟫_ℝ ≤ -(⟪wbar, w⟫_ℝ ^ 2 / ‖wbar‖ ^ 2) := by
          linarith
        have h3 := mul_le_mul_of_nonneg_right h2 hb
        have h4 : -(⟪wbar, w⟫_ℝ ^ 2 / ‖wbar‖ ^ 2) * ‖wbar‖ ^ 2
            = -(⟪wbar, w⟫_ℝ ^ 2) := by
          rw [neg_mul, div_mul_cancel₀ _ hbne]
        rw [h4] at h3
        nlinarith [sq_nonneg (‖wbar‖ ^ 2 - ⟪wbar, w⟫_ℝ)]
      · have h0 := hg 0 le_rfl
        rw [hsq1, hsq] at h0
        nlinarith
  refine ⟨‖w - wbar‖⁻¹ • (w - wbar), ?_, ?_, ?_⟩
  · refine proximalNormalCone_tangentCone_subset_normalCone hx hlc wbar ?_
    refine (isCone_proximalNormalCone hwbarT).2 ?_ (by positivity)
    refine ⟨1, one_pos, ?_⟩
    have heq : wbar + (1 : ℝ) • (w - wbar) = w := by module
    rw [heq]
    exact ⟨hwbarT, hwbarmin⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hnpos),
      inv_mul_cancel₀ hnpos.ne']
  · have hd : infDist w (tangentCone C x) = ‖w - wbar‖ := by
      refine le_antisymm ?_ ?_
      · rw [← dist_eq_norm]
        exact infDist_le_dist_of_mem hwbarT
      · refine (le_infDist hTne).2 fun z hz ↦ ?_
        rw [dist_eq_norm, norm_sub_rev w z, norm_sub_rev w wbar]
        exact hwbarmin z hz
    rw [hd, real_inner_smul_left]
    have hsplit : ⟪w - wbar, w⟫_ℝ = ‖w - wbar‖ ^ 2 := by
      have hzero : ⟪w - wbar, wbar⟫_ℝ = 0 := by
        rw [real_inner_comm, inner_sub_right, hinner, real_inner_self_eq_norm_sq]
        ring
      have hexp : ⟪w - wbar, w⟫_ℝ
          = ⟪w - wbar, w - wbar⟫_ℝ + ⟪w - wbar, wbar⟫_ℝ := by
        rw [← inner_add_right]
        congr 1
        abel
      rw [hexp, hzero, real_inner_self_eq_norm_sq, add_zero]
    rw [hsplit, sq]
    field_simp

end TangentNormalEstimate

section TangentNormalPolarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Theorem 6.28(b)**, the inclusion `⊇`.  If `w` is not a regular tangent
vector then, by 6(16), there are `xν →_C x̄` with `w` at distance at least `ε`
from every `T_C(xν)`, and 6.27(b) converts each of those distances into a
unit normal at `xν` pairing with `w` by at least `ε`.  A cluster point of
those normals is normal at `x̄` by 6.6 and still pairs with `w` by at least
`ε`, so `w` is not in the polar of `N_C(x̄)`. -/
theorem polarCone_normalCone_subset_regularTangentCone {C : Set E} {x : E}
    (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    polarCone (normalCone C x) ⊆ regularTangentCone C x := by
  intro w hw
  rw [regularTangentCone_eq_svInnerLimitWithin_tangentCone hx hlc]
  by_contra hnot
  obtain ⟨ε, hε, xbars, hxbC, hxbto, hempty⟩ :=
    not_mem_svInnerLimitWithin_tangentCone_iff_exists_sequences.1 hnot
  obtain ⟨V, hV, hVclosed, hCVclosed⟩ := hlc
  have hintV : interior V ∈ nhds x :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hV)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hxbto hintV)
  have hlcn : ∀ n, IsLocallyClosedAt C (xbars (n + N)) := fun n ↦
    ⟨V, mem_interior_iff_mem_nhds.1 (hN _ (Nat.le_add_left N n)), hVclosed, hCVclosed⟩
  have hnotT : ∀ n, w ∉ tangentCone C (xbars (n + N)) := by
    intro n hmem
    have hbad : w ∈ tangentCone C (xbars (n + N)) ∩ ball w ε := ⟨hmem, mem_ball_self hε⟩
    rw [hempty _] at hbad
    exact hbad
  have hdist : ∀ n, ε ≤ infDist w (tangentCone C (xbars (n + N))) := by
    intro n
    by_contra hlt
    push_neg at hlt
    have hne : (tangentCone C (xbars (n + N))).Nonempty :=
      ⟨0, (isCone_tangentCone (hxbC _)).1⟩
    obtain ⟨z, hz, hzd⟩ := (infDist_lt_iff hne).1 hlt
    have hbad : z ∈ tangentCone C (xbars (n + N)) ∩ ball w ε :=
      ⟨hz, mem_ball.2 (by rwa [dist_comm])⟩
    rw [hempty _] at hbad
    exact hbad
  choose vs hvsN hvsnorm hvsinner using fun n ↦
    exists_mem_normalCone_norm_eq_one_inner_eq_infDist (hxbC (n + N)) (hlcn n) (hnotT n)
  have hball : ∀ n, vs n ∈ closedBall (0 : E) 1 := by
    intro n
    rw [mem_closedBall, dist_zero_right, hvsnorm n]
  obtain ⟨v, -, φ, hφ, hvto⟩ := (isCompact_closedBall (0 : E) 1).tendsto_subseq hball
  have hxto : Tendsto (fun k ↦ xbars (φ k + N)) atTop (nhds x) :=
    (hxbto.comp (tendsto_add_atTop_nat N)).comp hφ.tendsto_atTop
  have hvmem : v ∈ normalCone C x :=
    mem_normalCone_of_tendsto hx (fun k ↦ hxbC _) hxto (fun k ↦ hvsN (φ k)) hvto
  have hinner : ε ≤ ⟪v, w⟫_ℝ := by
    refine ge_of_tendsto (Filter.Tendsto.inner hvto tendsto_const_nhds)
      (Eventually.of_forall fun k ↦ ?_)
    simp only [Function.comp_apply, hvsinner]
    exact hdist (φ k)
  have hle : ⟪w, v⟫_ℝ ≤ 0 := hw v hvmem
  rw [real_inner_comm] at hle
  linarith

/-- **Theorem 6.28(b)**: the regular tangent cone is the polar of the normal
cone at a point of local closedness. -/
theorem regularTangentCone_eq_polarCone_normalCone {C : Set E} {x : E} (hx : x ∈ C)
    (hlc : IsLocallyClosedAt C x) :
    regularTangentCone C x = polarCone (normalCone C x) :=
  Subset.antisymm (regularTangentCone_subset_polarCone_normalCone hx hlc)
    (polarCone_normalCone_subset_regularTangentCone hx hlc)

/-- **Corollary 6.29**, the implication (a) ⟹ (b), completing the link between
the two groups of conditions. -/
theorem tangentCone_eq_regularTangentCone_of_normalCone_eq {C : Set E} {x : E}
    (hx : x ∈ C) (hlc : IsLocallyClosedAt C x)
    (h : normalCone C x = regularNormalCone C x) :
    tangentCone C x = regularTangentCone C x := by
  refine Subset.antisymm ?_ (regularTangentCone_subset_tangentCone hx)
  rw [regularTangentCone_eq_polarCone_normalCone hx hlc, h,
    regularNormalCone_eq_polarCone_tangentCone hx]
  exact subset_polarCone_bipolar _

/-- **Corollary 6.29**: Clarke regularity is condition (b). -/
theorem isClarkeRegularAt_iff_tangentCone_eq {C : Set E} {x : E} (hx : x ∈ C)
    (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔ tangentCone C x = regularTangentCone C x :=
  ⟨fun h ↦ tangentCone_eq_regularTangentCone_of_normalCone_eq hx hlc h.2,
    isClarkeRegularAt_of_tangentCone_eq hx hlc⟩

/-- **Corollary 6.29**: Clarke regularity is condition (d). -/
theorem isClarkeRegularAt_iff_tangentCone_eq_polarCone {C : Set E} {x : E}
    (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔ tangentCone C x = polarCone (normalCone C x) := by
  rw [isClarkeRegularAt_iff_tangentCone_eq hx hlc,
    regularTangentCone_eq_polarCone_normalCone hx hlc]

/-- **Corollary 6.29**: Clarke regularity is condition (g). -/
theorem isClarkeRegularAt_iff_svIscWithinAt {C : Set E} {x : E} (hx : x ∈ C)
    (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔ SvIscWithinAt (tangentCone C) C x := by
  rw [isClarkeRegularAt_iff_tangentCone_eq hx hlc,
    tangentCone_eq_regularTangentCone_iff_svIscWithinAt hx hlc]

/-- **Corollary 6.30**: at a point of Clarke regularity the tangent cone is the
polar of the normal cone. -/
theorem IsClarkeRegularAt.tangentCone_eq_polarCone {C : Set E} {x : E} (hx : x ∈ C)
    (h : IsClarkeRegularAt C x) : tangentCone C x = polarCone (normalCone C x) :=
  (isClarkeRegularAt_iff_tangentCone_eq_polarCone hx h.1).1 h

/-- **Corollary 6.30**: the tangent cone at a point of Clarke regularity is
convex. -/
theorem IsClarkeRegularAt.convex_tangentCone {C : Set E} {x : E} (hx : x ∈ C)
    (h : IsClarkeRegularAt C x) : Convex ℝ (tangentCone C x) := by
  rw [h.tangentCone_eq_polarCone hx]
  exact convex_polarCone _

/-- **Corollary 6.30**: Clarke regularity implies geometric derivability, the
regular tangent vectors being derivable. -/
theorem IsClarkeRegularAt.isGeometricallyDerivable {C : Set E} {x : E} (hx : x ∈ C)
    (h : IsClarkeRegularAt C x) : IsGeometricallyDerivable C x := by
  have hkey : tangentCone C x ⊆ derivableCone C x := by
    rw [(isClarkeRegularAt_iff_tangentCone_eq hx h.1).1 h]
    exact regularTangentCone_subset_derivableCone hx
  exact hkey

end TangentNormalPolarity

end RW
