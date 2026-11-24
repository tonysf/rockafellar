/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Chain rule for second-order tangents

Proposition 13.13.  For `C = {x | G(x) ∈ D}` with `G` of class `C²` and `D` closed, under the
constraint qualification `y ∈ N_D(G(x̄)), ∇G(x̄)* y = 0 ⇒ y = 0`:
`w ∈ T_C(x̄) ⇔ ∇G(x̄)w ∈ T_D(G(x̄))` and
`z ∈ T²_C(x̄ | w) ⇔ ∇G(x̄)z + ∇²G(x̄)(w, w) ∈ T²_D(G(x̄) | ∇G(x̄)w)`.
The forward implications pass to the limit in the second-order quotients
`Δ²_τ G(x̄)(w | z') = [G(x̄ + τw + ½τ²z') - G(x̄) - τ∇G(x̄)w]/(½τ²)`
(`mapSecondDifferenceQuotient`), which converge to `∇²G(x̄)(w, w) + ∇G(x̄)z`; the reverse implications use the metric regularity
estimate `d(x, C) ≤ κ d(G(x), D)` of Example 9.44.  The same estimate transfers parabolic
derivability from `D` to `C` when `D` is Clarke regular, with nonemptiness from 13(12) and the
tangent form `T_D(G(x̄)) + rge ∇G(x̄) = ℝᵐ` of the qualification (6.39); polyhedral `D` is covered
by Proposition 13.12.
-/

import RockafellarWets.Chapter13.SecondOrderTangents
import RockafellarWets.Chapter13.SecondOrderExpansions
import RockafellarWets.Chapter9.ConstraintMetricRegularity
import RockafellarWets.Chapter6.ConstraintNormals

open Filter Set Topology Metric
open scoped InnerProductSpace NNReal ENNReal Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- In a finite-dimensional inner product space, convergence follows from convergence of all
inner products. -/
theorem tendsto_of_forall_inner {ι : Type*} {l : Filter ι} {f : ι → F} {a : F}
    (h : ∀ u : F, Tendsto (fun i ↦ ⟪u, f i⟫_ℝ) l (𝓝 ⟪u, a⟫_ℝ)) : Tendsto f l (𝓝 a) := by
  set b := stdOrthonormalBasis ℝ F
  have h1 := tendsto_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ F)))
    fun j _ ↦ (h (b j)).smul_const (b j)
  simpa only [b.sum_repr'] using h1

/-- The second-order difference quotient `Δ²_τ G(x̄)(w | z)` of a mapping (proof of 13.13). -/
noncomputable def mapSecondDifferenceQuotient (G : E → F) (x w : E) (τ : ℝ) (z : E) : F :=
  (2 / τ ^ 2) • (G (x + τ • w + (τ ^ 2 / 2) • z) - G x - τ • fderiv ℝ G x w)

/-- For a `C²` mapping, `Δ²_τ G(x̄)(w | z') → ∇G(x̄)z + ∇²G(x̄)(w, w)` as `τ ↘ 0`, `z' → z`. -/
theorem tendsto_mapSecondDifferenceQuotient {G : E → F} (hG : ContDiff ℝ 2 G) (x w z : E) :
    Tendsto (fun p : ℝ × E ↦ mapSecondDifferenceQuotient G x w p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z)
      (𝓝 (fderiv ℝ G x z + fderiv ℝ (fderiv ℝ G) x w w)) := by
  refine tendsto_of_forall_inner fun u ↦ ?_
  set L : (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.compL ℝ E F ℝ (innerSL ℝ u)
  set v : E := (fderiv ℝ G x).adjoint u
  have hd1 : ∀ y, HasFDerivAt G (fderiv ℝ G y) y := fun y ↦
    (hG.differentiable (by norm_num) y).hasFDerivAt
  have hd2 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x :=
    ((hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  have hφ : ∀ᶠ y in 𝓝 x, HasFDerivAt (fun y ↦ ⟪u, G y⟫_ℝ) (L (fderiv ℝ G y)) y :=
    .of_forall fun y ↦ (innerSL ℝ u).hasFDerivAt.comp y (hd1 y)
  have hφ' : HasFDerivAt (fun y ↦ L (fderiv ℝ G y)) (L.comp (fderiv ℝ (fderiv ℝ G) x)) x :=
    L.hasFDerivAt.comp x hd2
  have hv : ∀ w', L (fderiv ℝ G x) w' = ⟪v, w'⟫_ℝ := fun w' ↦ by
    simp [L, v, ContinuousLinearMap.adjoint_inner_left]
  have hQ := tendsto_secondDifferenceQuotient_of_hasFDerivAt hφ hφ' hv w
  have hpath : Tendsto (fun p : ℝ × E ↦ (p.1, w + (p.1 / 2) • p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) := by
    refine tendsto_fst.prodMk ?_
    have h0 : Tendsto (fun p : ℝ × E ↦ p.1) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) (𝓝 0) :=
      tendsto_fst.mono_right nhdsWithin_le_nhds
    have h1 : Tendsto (fun p : ℝ × E ↦ p.1 / 2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) (𝓝 0) := by
      simpa using h0.div_const (2 : ℝ)
    simpa using tendsto_const_nhds.add (h1.smul tendsto_snd)
  have hinner : Tendsto (fun p : ℝ × E ↦ ⟪v, p.2⟫_ℝ) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 z) (𝓝 ⟪v, z⟫_ℝ) :=
    ((continuous_const.inner continuous_id).tendsto z).comp tendsto_snd
  have hlim := (hQ.comp hpath).add hinner
  have htarget : (L.comp (fderiv ℝ (fderiv ℝ G) x)) w w + ⟪v, z⟫_ℝ =
      ⟪u, fderiv ℝ G x z + fderiv ℝ (fderiv ℝ G) x w w⟫_ℝ := by
    simp only [L, v, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left, inner_add_right]
    ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [tendsto_fst.eventually self_mem_nhdsWithin] with p hp
  have hτ : p.1 ≠ 0 := ne_of_gt hp
  have hx : x + p.1 • (w + (p.1 / 2) • p.2) = x + p.1 • w + (p.1 ^ 2 / 2) • p.2 := by
    rw [smul_add, smul_smul, ← add_assoc]
    congr 2
    ring
  have hvw : ⟪v, w⟫_ℝ = ⟪u, fderiv ℝ G x w⟫_ℝ := by
    simp only [v, ContinuousLinearMap.adjoint_inner_left]
  simp only [Function.comp_apply, mapSecondDifferenceQuotient, real_inner_smul_right,
    inner_sub_right, hx, inner_add_right, hvw]
  field_simp
  ring

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Points of the parabolic blow-ups of `C = G⁻¹(D)` are carried by `Δ²_τ G(x̄)(w | ·)` into the
parabolic blow-ups of `D`. -/
theorem mapSecondDifferenceQuotient_mem_parabolicBlowUp {G : E → F} {D : Set F} {x w z : E}
    {τ : ℝ} (hτ : τ ≠ 0) (hz : z ∈ parabolicBlowUp (G ⁻¹' D) x w τ) :
    mapSecondDifferenceQuotient G x w τ z ∈ parabolicBlowUp D (G x) (fderiv ℝ G x w) τ := by
  rw [mem_parabolicBlowUp_iff hτ] at hz
  exact ⟨_, hz, rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- The metric regularity estimate `d(y, C) ≤ k d(G(y), D)` produces points of `C` near `y`. -/
theorem exists_mem_of_infEDist_le {C : Set E} {D : Set F} {G : E → F} {k : ℝ≥0}
    (hC : C.Nonempty) {y : E} (hy : infEDist y C ≤ (k : ℝ≥0∞) * infEDist (G y) D) {d : F}
    (hd : d ∈ D) {s : ℝ} (hs : 0 < s) (hGd : ‖G y - d‖ < s) :
    ∃ c ∈ C, ‖y - c‖ < (k + 1) * s := by
  have hD : D.Nonempty := ⟨d, hd⟩
  have h1 : infDist y C ≤ k * infDist (G y) D := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (infEDist_ne_top hD)) hy
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal] at h
    exact h
  have h2 : infDist (G y) D ≤ ‖G y - d‖ := by
    rw [← dist_eq_norm]
    exact infDist_le_dist_of_mem hd
  have h3 : infDist y C < (k + 1) * s := by
    have hk : (0 : ℝ) ≤ k := k.coe_nonneg
    calc infDist y C ≤ k * infDist (G y) D := h1
      _ ≤ k * s := mul_le_mul_of_nonneg_left (h2.trans hGd.le) hk
      _ < (k + 1) * s := by nlinarith
  obtain ⟨c, hc, hdist⟩ := (infDist_lt_iff hC).1 h3
  exact ⟨c, hc, by rwa [← dist_eq_norm]⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The key step of the reverse implication in 13.13, for one value of `τ`. -/
theorem exists_mem_parabolicBlowUp_of_metric {G : E → F} {D : Set F} {x w z : E} {k : ℝ≥0}
    {τ s : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hC : (G ⁻¹' D).Nonempty)
    (hMR : infEDist (x + τ • w + (τ ^ 2 / 2) • z) (G ⁻¹' D) ≤
      (k : ℝ≥0∞) * infEDist (G (x + τ • w + (τ ^ 2 / 2) • z)) D)
    {b : F} (hb : b ∈ parabolicBlowUp D (G x) (fderiv ℝ G x w) τ)
    (hbz : ‖mapSecondDifferenceQuotient G x w τ z - b‖ < s) :
    ∃ z' ∈ parabolicBlowUp (G ⁻¹' D) x w τ, ‖z' - z‖ < (k + 1) * s := by
  obtain ⟨d, hd, rfl⟩ := hb
  set y := x + τ • w + (τ ^ 2 / 2) • z
  have hτ2 : 0 < τ ^ 2 / 2 := by positivity
  have hc1 : (τ ^ 2 / 2) * (2 / τ ^ 2) = 1 := by field_simp
  have hc2 : (2 / τ ^ 2) * (τ ^ 2 / 2) = 1 := by field_simp
  have hGy : G y - d = (τ ^ 2 / 2) • (mapSecondDifferenceQuotient G x w τ z -
      (2 / τ ^ 2) • (d - G x - τ • fderiv ℝ G x w)) := by
    simp only [mapSecondDifferenceQuotient, ← smul_sub, smul_smul, hc1, one_smul, y]
    abel
  have hGd : ‖G y - d‖ < (τ ^ 2 / 2) * s := by
    rw [hGy, norm_smul, Real.norm_of_nonneg hτ2.le]
    exact mul_lt_mul_of_pos_left hbz hτ2
  obtain ⟨c, hc, hyc⟩ := exists_mem_of_infEDist_le hC hMR hd (by positivity) hGd
  refine ⟨(2 / τ ^ 2) • (c - x - τ • w), ⟨c, hc, rfl⟩, ?_⟩
  have he : (2 / τ ^ 2) • (c - x - τ • w) - z = (2 / τ ^ 2) • (c - y) := by
    simp only [y, smul_sub, smul_add, smul_smul, hc2, one_smul]
    abel
  rw [he, norm_smul, Real.norm_of_nonneg (by positivity), norm_sub_rev]
  calc 2 / τ ^ 2 * ‖y - c‖ < 2 / τ ^ 2 * ((k + 1) * (τ ^ 2 / 2 * s)) :=
        mul_lt_mul_of_pos_left hyc (by positivity)
    _ = (k + 1) * s := by field_simp

/-- **Proposition 13.13**, forward second-order implication. -/
theorem mem_secondOrderTangentSet_of_mem_preimage {G : E → F} (hG : ContDiff ℝ 2 G) {D : Set F}
    {x w z : E} (hz : z ∈ secondOrderTangentSet (G ⁻¹' D) x w) :
    fderiv ℝ G x z + fderiv ℝ (fderiv ℝ G) x w w ∈
      secondOrderTangentSet D (G x) (fderiv ℝ G x w) := by
  intro V hV
  obtain ⟨S, hS, N, hN, hSN⟩ := mem_prod_iff.1 ((tendsto_mapSecondDifferenceQuotient hG x w z) hV)
  refine ((hz N hN).and_eventually (inter_mem hS self_mem_nhdsWithin)).mono ?_
  rintro τ ⟨⟨z', hz'C, hz'N⟩, hτS, hτpos⟩
  exact ⟨_, mapSecondDifferenceQuotient_mem_parabolicBlowUp (ne_of_gt hτpos) hz'C,
    hSN (show (τ, z') ∈ S ×ˢ N from ⟨hτS, hz'N⟩)⟩

/-- The metric regularity estimate from the constraint qualification (Example 9.44), with the
nearness of the parabolic points `x̄ + τw + ½τ²z` and the convergence of the quotients. -/
theorem eventually_parabolic_metric {G : E → F} (hG : ContDiff ℝ 2 G) {D : Set F}
    (hD : IsClosed D) {x : E} (hx : G x ∈ D)
    (hQ : ∀ y ∈ normalCone D (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) (w z : E) :
    ∃ k : ℝ≥0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      infEDist (x + τ • w + (τ ^ 2 / 2) • z) (G ⁻¹' D) ≤
        (k : ℝ≥0∞) * infEDist (G (x + τ • w + (τ ^ 2 / 2) • z)) D := by
  obtain ⟨k, hk⟩ := (constraint_metricRegularity_iff (hG.of_le (by norm_num)) hD hx).2 hQ
  obtain ⟨ε, hε, hMR⟩ := hk.constraint_errorBound
  refine ⟨k, ?_⟩
  have hc : Continuous fun τ : ℝ ↦ x + τ • w + (τ ^ 2 / 2) • z := by fun_prop
  have h0 : (fun τ : ℝ ↦ x + τ • w + (τ ^ 2 / 2) • z) 0 = x := by simp
  have hnear := (hc.tendsto 0).eventually (h0 ▸ closedBall_mem_nhds x hε)
  exact (hnear.filter_mono nhdsWithin_le_nhds).mono fun τ hτ ↦ hMR _ (by simpa using hτ)

/-- **Proposition 13.13**, reverse second-order implication, in a form valid both for outer
and for inner limits. -/
theorem frequently_parabolicBlowUp_preimage {G : E → F} (hG : ContDiff ℝ 2 G) {D : Set F}
    (hD : IsClosed D) {x : E} (hx : G x ∈ D)
    (hQ : ∀ y ∈ normalCone D (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) {w z : E} {r : ℝ}
    (hr : 0 < r) : ∃ ρ > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      (parabolicBlowUp D (G x) (fderiv ℝ G x w) τ ∩
          ball (fderiv ℝ G x z + fderiv ℝ (fderiv ℝ G) x w w) ρ).Nonempty →
        (parabolicBlowUp (G ⁻¹' D) x w τ ∩ ball z r).Nonempty := by
  obtain ⟨k, hk⟩ := eventually_parabolic_metric hG hD hx hQ w z
  set t := fderiv ℝ G x z + fderiv ℝ (fderiv ℝ G) x w w
  set s := r / (k + 1)
  have hs : 0 < s := by positivity
  refine ⟨s / 2, by positivity, ?_⟩
  have hconv : ∀ᶠ τ in 𝓝[>] (0 : ℝ), mapSecondDifferenceQuotient G x w τ z ∈ ball t (s / 2) := by
    have h1 := (tendsto_mapSecondDifferenceQuotient hG x w z).comp (tendsto_pair_const z)
    exact h1.eventually (ball_mem_nhds t (by positivity))
  filter_upwards [hk, hconv, self_mem_nhdsWithin] with τ hτk hτc hτpos ⟨b, hbD, hbt⟩
  have hbz : ‖mapSecondDifferenceQuotient G x w τ z - b‖ < s := by
    rw [mem_ball, dist_eq_norm] at hτc hbt
    calc ‖mapSecondDifferenceQuotient G x w τ z - b‖
        = ‖(mapSecondDifferenceQuotient G x w τ z - t) - (b - t)‖ := by congr 1; abel
      _ ≤ ‖mapSecondDifferenceQuotient G x w τ z - t‖ + ‖b - t‖ := norm_sub_le _ _
      _ < s := by linarith
  obtain ⟨z', hz', hz'z⟩ := exists_mem_parabolicBlowUp_of_metric hτpos hs ⟨x, hx⟩ hτk hbD hbz
  refine ⟨z', hz', ?_⟩
  rw [mem_ball, dist_eq_norm]
  calc ‖z' - z‖ < (k + 1) * s := hz'z
    _ = r := by simp only [s]; field_simp

/-- **Proposition 13.13**, reverse second-order implication. -/
theorem mem_secondOrderTangentSet_preimage_of {G : E → F} (hG : ContDiff ℝ 2 G) {D : Set F}
    (hD : IsClosed D) {x : E} (hx : G x ∈ D)
    (hQ : ∀ y ∈ normalCone D (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) {w z : E}
    (hz : fderiv ℝ G x z + fderiv ℝ (fderiv ℝ G) x w w ∈
      secondOrderTangentSet D (G x) (fderiv ℝ G x w)) :
    z ∈ secondOrderTangentSet (G ⁻¹' D) x w := by
  intro N hN
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨ρ, hρ, hev⟩ := frequently_parabolicBlowUp_preimage hG hD hx hQ (w := w) (z := z) hr
  refine ((hz _ (ball_mem_nhds _ hρ)).and_eventually hev).mono fun τ ⟨h1, h2⟩ ↦ ?_
  obtain ⟨z', hz', hz'r⟩ := h2 h1
  exact ⟨z', hz', hrN hz'r⟩

/-- **Proposition 13.13**, the inner-limit version of the reverse implication. -/
theorem mem_innerSetLimitAlong_preimage_of {G : E → F} (hG : ContDiff ℝ 2 G) {D : Set F}
    (hD : IsClosed D) {x : E} (hx : G x ∈ D)
    (hQ : ∀ y ∈ normalCone D (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) {w z : E}
    (hz : fderiv ℝ G x z + fderiv ℝ (fderiv ℝ G) x w w ∈
      innerSetLimitAlong (𝓝[>] (0 : ℝ)) (parabolicBlowUp D (G x) (fderiv ℝ G x w))) :
    z ∈ innerSetLimitAlong (𝓝[>] (0 : ℝ)) (parabolicBlowUp (G ⁻¹' D) x w) := by
  intro N hN
  obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
  obtain ⟨ρ, hρ, hev⟩ := frequently_parabolicBlowUp_preimage hG hD hx hQ (w := w) (z := z) hr
  filter_upwards [hz _ (ball_mem_nhds _ hρ), hev] with τ h1 h2
  obtain ⟨z', hz', hz'r⟩ := h2 h1
  exact ⟨z', hz', hrN hz'r⟩

/-- **Proposition 13.13**, first-order part: `w ∈ T_C(x̄) ⇔ ∇G(x̄)w ∈ T_D(G(x̄))`. -/
theorem mem_tangentCone_preimage_iff {G : E → F} (hG : ContDiff ℝ 2 G) {D : Set F}
    (hD : IsClosed D) {x : E} (hx : G x ∈ D)
    (hQ : ∀ y ∈ normalCone D (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) (w : E) :
    w ∈ tangentCone (G ⁻¹' D) x ↔ fderiv ℝ G x w ∈ tangentCone D (G x) := by
  have hd1 : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  constructor
  · intro hw
    have h := tangentCone_constraints_subset (X := univ) (D := D) hd1
      (show w ∈ tangentCone (univ ∩ G ⁻¹' D) x by rwa [univ_inter])
    exact h.2
  · intro hw
    obtain ⟨k, hk⟩ := (constraint_metricRegularity_iff (hG.of_le (by norm_num)) hD hx).2 hQ
    obtain ⟨ε, hε, hMR⟩ := hk.constraint_errorBound
    rw [tangentCone_eq_outerSetLimitAlong] at hw ⊢
    intro N hN
    obtain ⟨r, hr, hrN⟩ := Metric.mem_nhds_iff.1 hN
    set s := r / (k + 1)
    have hs : 0 < s := by positivity
    have hline : HasDerivAt (fun t : ℝ ↦ x + t • w) ((1 : ℝ) • w) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have hdiff := hd1.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have hslope : Tendsto (fun t : ℝ ↦ t⁻¹ • (G (x + t • w) - G x)) (𝓝[>] 0)
        (𝓝 (fderiv ℝ G x w)) := by
      simpa [Function.comp_def] using hdiff.tendsto_slope_zero_right
    have hc : Continuous fun t : ℝ ↦ x + t • w := by fun_prop
    have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • w ∈ closedBall x ε :=
      ((hc.tendsto 0).eventually (by simpa using closedBall_mem_nhds x hε)).filter_mono
        nhdsWithin_le_nhds
    have hconv := hslope.eventually (ball_mem_nhds (fderiv ℝ G x w) (half_pos hs))
    refine ((hw _ (ball_mem_nhds _ (half_pos hs))).and_eventually
      ((hnear.and hconv).and self_mem_nhdsWithin)).mono ?_
    rintro t ⟨⟨b, ⟨d, hd, rfl⟩, hbt⟩, ⟨htn, htc⟩, htpos⟩
    have ht : (0 : ℝ) < t := htpos
    rw [mem_ball, dist_eq_norm] at hbt
    rw [dist_eq_norm] at htc
    have hGd : ‖G (x + t • w) - d‖ < t * s := by
      have he : G (x + t • w) - d = t • (t⁻¹ • (G (x + t • w) - G x) - t⁻¹ • (d - G x)) := by
        rw [← smul_sub, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
        abel
      rw [he, norm_smul, Real.norm_of_nonneg ht.le]
      refine mul_lt_mul_of_pos_left ?_ ht
      calc ‖t⁻¹ • (G (x + t • w) - G x) - t⁻¹ • (d - G x)‖
          = ‖(t⁻¹ • (G (x + t • w) - G x) - fderiv ℝ G x w) -
              (t⁻¹ • (d - G x) - fderiv ℝ G x w)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
        _ < s := by linarith
    obtain ⟨c, hc, hyc⟩ := exists_mem_of_infEDist_le ⟨x, hx⟩ (hMR _ htn) hd (by positivity) hGd
    refine ⟨t⁻¹ • (c - x), ⟨c, hc, rfl⟩, hrN ?_⟩
    rw [mem_ball, dist_eq_norm]
    have he : t⁻¹ • (c - x) - w = t⁻¹ • (c - (x + t • w)) := by
      simp only [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      abel
    rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), norm_sub_rev]
    calc t⁻¹ * ‖x + t • w - c‖ < t⁻¹ * ((k + 1) * (t * s)) :=
          mul_lt_mul_of_pos_left hyc (inv_pos.2 ht)
      _ = r := by simp only [s]; field_simp

/-- **Proposition 13.13** (chain rule for second-order tangents). -/
theorem chain_rule_for_second_order_tangents {G : E → F} (hG : ContDiff ℝ 2 G) {D : Set F}
    (hD : IsClosed D) {x : E} (hx : G x ∈ D)
    (hQ : ∀ y ∈ normalCone D (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    (∀ w, w ∈ tangentCone (G ⁻¹' D) x ↔ fderiv ℝ G x w ∈ tangentCone D (G x)) ∧
    (∀ w z, z ∈ secondOrderTangentSet (G ⁻¹' D) x w ↔
      fderiv ℝ G x z + fderiv ℝ (fderiv ℝ G) x w w ∈
        secondOrderTangentSet D (G x) (fderiv ℝ G x w)) ∧
    (∀ w, IsClarkeRegularAt D (G x) → IsParabolicallyDerivable D (G x) (fderiv ℝ G x w) →
      IsParabolicallyDerivable (G ⁻¹' D) x w) ∧
    (IsPolyhedral D → ∀ w ∈ tangentCone (G ⁻¹' D) x, IsParabolicallyDerivable (G ⁻¹' D) x w ∧
      secondOrderTangentSet D (G x) (fderiv ℝ G x w) =
        tangentCone (tangentCone D (G x)) (fderiv ℝ G x w)) := by
  have hsecond : ∀ w z, z ∈ secondOrderTangentSet (G ⁻¹' D) x w ↔
      fderiv ℝ G x z + fderiv ℝ (fderiv ℝ G) x w w ∈
        secondOrderTangentSet D (G x) (fderiv ℝ G x w) := fun w z ↦
    ⟨mem_secondOrderTangentSet_of_mem_preimage hG,
      mem_secondOrderTangentSet_preimage_of hG hD hx hQ⟩
  have hderiv : ∀ w, IsClarkeRegularAt D (G x) →
      IsParabolicallyDerivable D (G x) (fderiv ℝ G x w) →
      IsParabolicallyDerivable (G ⁻¹' D) x w := by
    intro w hreg ⟨⟨a, ha⟩, hPK⟩
    refine ⟨?_, ?_, rfl⟩
    · -- nonemptiness from 13(12) and `T_D(G x̄) + rge ∇G(x̄) = ℝᵐ`
      obtain ⟨k, hk⟩ := (constraint_metricRegularity_iff (hG.of_le (by norm_num)) hD hx).2 hQ
      have hrange := (constraint_metricRegularity_iff_tangent_range (hG.of_le (by norm_num)) hD hx
        hreg).1 ⟨k, hk⟩
      have hmem : fderiv ℝ (fderiv ℝ G) x w w - a ∈ tangentCone D (G x) + range (fderiv ℝ G x) := by
        rw [hrange]
        exact mem_univ _
      obtain ⟨u, hu, _, ⟨z₀, rfl⟩, hsum⟩ := hmem
      refine ⟨-z₀, (hsecond w (-z₀)).2 ?_⟩
      have hau := secondOrderTangentSet_add_tangent hx hreg ha hu
      have heq : fderiv ℝ G x (-z₀) + fderiv ℝ (fderiv ℝ G) x w w = a + u := by
        rw [eq_sub_iff_add_eq] at hsum
        simp only at hsum
        rw [map_neg, ← hsum]
        abel
      rw [heq]
      exact hau
    · refine Subset.antisymm (innerSetLimitAlong_subset_outerSetLimitAlong _) (fun z hz ↦ ?_)
      refine mem_innerSetLimitAlong_preimage_of hG hD hx hQ ?_
      rw [hPK.1]
      exact (hsecond w z).1 hz
  refine ⟨mem_tangentCone_preimage_iff hG hD hx hQ, hsecond, hderiv, fun hpoly w hw ↦ ?_⟩
  have hDw := (mem_tangentCone_preimage_iff hG hD hx hQ w).1 hw
  obtain ⟨hpar, heq, -⟩ := hpoly.parabolic hx hDw
  refine ⟨hderiv w (isClarkeRegularAt_of_convex hpoly.convex hx
    ⟨univ, univ_mem, isClosed_univ, by rw [inter_univ]; exact hpoly.isClosed⟩) hpar, heq⟩

end RW
