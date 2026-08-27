/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Distances Between Cones

This file proves Example 4.44: the `ρ`-distances between closed cones are
linear in `ρ`, the integrated set distance agrees with the `1`-distance and
never exceeds `1`, the Pompeiu--Hausdorff distance between distinct closed
cones is infinite, and the closed cones form a compact subset of the
hyperspace of Theorem 4.42.
-/

import RockafellarWets.Chapter3.Cones
import RockafellarWets.Chapter4.ConeLimits
import RockafellarWets.Chapter4.IntegratedSetDistance

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal InnerProductSpace NNReal Pointwise

namespace RW

section ConeHomogeneity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A cone is invariant under positive dilations. -/
theorem IsCone.smul_set_eq {K : Set E} (hK : IsCone K) {c : ℝ} (hc : 0 < c) :
    c • K = K := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hK.smul_mem hx hc.le
  · intro x hx
    refine ⟨c⁻¹ • x, hK.smul_mem hx (by positivity), ?_⟩
    simp [smul_smul, mul_inv_cancel₀ hc.ne']

/-- Positive homogeneity of the distance function of a cone. -/
theorem IsCone.infDist_smul {K : Set E} (hK : IsCone K) {c : ℝ} (hc : 0 < c)
    (x : E) :
    infDist (c • x) K = c * infDist x K := by
  conv_lhs => rw [← hK.smul_set_eq hc]
  rw [infDist_smul₀ hc.ne' K x, Real.norm_eq_abs, abs_of_pos hc]

theorem IsCone.infDist_zero {K : Set E} (hK : IsCone K) :
    infDist (0 : E) K = 0 :=
  infDist_zero_of_mem hK.1

/-- The distance to a cone never exceeds the norm, since every cone contains
the origin. -/
theorem IsCone.infDist_le_norm {K : Set E} (hK : IsCone K) (x : E) :
    infDist x K ≤ ‖x‖ := by
  simpa using infDist_le_dist_of_mem hK.1

end ConeHomogeneity

section ConeRhoDistances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Example 4.44**, linearity clause: `dl_ρ(K₁, K₂) = ρ · dl_1(K₁, K₂)`
for closed cones and every radius `ρ ≥ 0`. -/
theorem rhoDistance_isCone_eq {K₁ K₂ : Set E} (hK₁ : IsCone K₁)
    (hK₂ : IsCone K₂) (ρ : ℝ≥0) :
    rhoDistance ρ K₁ K₂ = (ρ : ℝ) * rhoDistance 1 K₁ K₂ := by
  rcases eq_or_lt_of_le (zero_le ρ) with hρ | hρ
  · have hρ0 : ρ = 0 := hρ.symm
    subst hρ0
    have hzero : rhoDistance 0 K₁ K₂ ≤ 0 := by
      rw [rhoDistance_le_iff le_rfl]
      intro x hx
      have hx0 : x = 0 := by
        simpa [mem_closedBall, dist_zero_right] using hx
      subst hx0
      simp [hK₁.infDist_zero, hK₂.infDist_zero]
    simpa using le_antisymm hzero (rhoDistance_nonneg _ _ _)
  · have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
    have hone : (0 : ℝ) ≤ rhoDistance 1 K₁ K₂ := rhoDistance_nonneg _ _ _
    refine le_antisymm ?_ ?_
    · rw [rhoDistance_le_iff (mul_nonneg hρR.le hone)]
      intro x hx
      have hxnorm : ‖x‖ ≤ (ρ : ℝ) := by
        simpa [mem_closedBall, dist_zero_right] using hx
      have hy : (ρ : ℝ)⁻¹ • x ∈ closedBall (0 : E) ((1 : ℝ≥0) : ℝ) := by
        simp only [mem_closedBall, dist_zero_right, norm_smul, norm_inv,
          Real.norm_eq_abs, abs_of_pos hρR, NNReal.coe_one]
        rw [inv_mul_le_iff₀ hρR, mul_one]
        exact hxnorm
      have hscale : ∀ K : Set E, IsCone K →
          infDist x K = (ρ : ℝ) * infDist ((ρ : ℝ)⁻¹ • x) K := by
        intro K hK
        rw [← hK.infDist_smul hρR, smul_smul, mul_inv_cancel₀ hρR.ne', one_smul]
      rw [hscale K₁ hK₁, hscale K₂ hK₂, ← mul_sub, abs_mul, abs_of_pos hρR]
      exact mul_le_mul_of_nonneg_left
        (abs_infDist_sub_infDist_le_rhoDistance 1 K₁ K₂ hy) hρR.le
    · have hkey : rhoDistance 1 K₁ K₂ ≤ (ρ : ℝ)⁻¹ * rhoDistance ρ K₁ K₂ := by
        rw [rhoDistance_le_iff
          (mul_nonneg (by positivity) (rhoDistance_nonneg _ _ _))]
        intro y hy
        have hynorm : ‖y‖ ≤ 1 := by
          simpa [mem_closedBall, dist_zero_right] using hy
        have hx : (ρ : ℝ) • y ∈ closedBall (0 : E) ((ρ : ℝ≥0) : ℝ) := by
          simp only [mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_eq_abs, abs_of_pos hρR]
          nlinarith [norm_nonneg y]
        have hscale : ∀ K : Set E, IsCone K →
            infDist y K = (ρ : ℝ)⁻¹ * infDist ((ρ : ℝ) • y) K := by
          intro K hK
          rw [hK.infDist_smul hρR, ← mul_assoc, inv_mul_cancel₀ hρR.ne',
            one_mul]
        rw [hscale K₁ hK₁, hscale K₂ hK₂, ← mul_sub, abs_mul, abs_inv,
          abs_of_pos hρR]
        exact mul_le_mul_of_nonneg_left
          (abs_infDist_sub_infDist_le_rhoDistance ρ K₁ K₂ hx) (by positivity)
      calc (ρ : ℝ) * rhoDistance 1 K₁ K₂
          ≤ (ρ : ℝ) * ((ρ : ℝ)⁻¹ * rhoDistance ρ K₁ K₂) :=
            mul_le_mul_of_nonneg_left hkey hρR.le
        _ = rhoDistance ρ K₁ K₂ := by
            rw [← mul_assoc, mul_inv_cancel₀ hρR.ne', one_mul]

/-- **Example 4.44**, bound clause: `dl_1(K₁, K₂) ≤ 1`. -/
theorem rhoDistance_one_isCone_le_one {K₁ K₂ : Set E} (hK₁ : IsCone K₁)
    (hK₂ : IsCone K₂) :
    rhoDistance 1 K₁ K₂ ≤ 1 := by
  rw [rhoDistance_le_iff zero_le_one]
  intro x hx
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa [mem_closedBall, dist_zero_right] using hx
  rw [abs_le]
  constructor
  · linarith [hK₂.infDist_le_norm x, infDist_nonneg (x := x) (s := K₁)]
  · linarith [hK₁.infDist_le_norm x, infDist_nonneg (x := x) (s := K₂)]

/-- The real-radius form of the linearity clause. -/
theorem rhoDistanceReal_isCone_eq {K₁ K₂ : Set E} (hK₁ : IsCone K₁)
    (hK₂ : IsCone K₂) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    rhoDistanceReal ρ K₁ K₂ = ρ * rhoDistance 1 K₁ K₂ := by
  rw [rhoDistanceReal, rhoDistance_isCone_eq hK₁ hK₂, Real.coe_toNNReal ρ hρ]

/-- **Example 4.44**, integrated clause: for closed cones the integrated set
distance is exactly the `1`-distance, because `∫₀^∞ ρ e^{-ρ} dρ = 1`. -/
theorem integratedSetDistance_isCone_eq {K₁ K₂ : Set E} (hK₁ : IsCone K₁)
    (hK₂ : IsCone K₂) :
    integratedSetDistance K₁ K₂ = rhoDistance 1 K₁ K₂ := by
  have hcongr : ∀ ρ ∈ Ioi (0 : ℝ),
      rhoDistanceReal ρ K₁ K₂ * Real.exp (-ρ)
        = rhoDistance 1 K₁ K₂ * ((0 + ρ) * Real.exp (-ρ)) := by
    intro ρ hρ
    rw [rhoDistanceReal_isCone_eq hK₁ hK₂ (le_of_lt hρ)]
    ring
  rw [integratedSetDistance, setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_const_mul, integral_Ioi_affine_mul_exp_neg]
  simp

/-- **Example 4.44**: the integrated distance between closed cones is at
most one. -/
theorem integratedSetDistance_isCone_le_one {K₁ K₂ : Set E} (hK₁ : IsCone K₁)
    (hK₂ : IsCone K₂) :
    integratedSetDistance K₁ K₂ ≤ 1 := by
  rw [integratedSetDistance_isCone_eq hK₁ hK₂]
  exact rhoDistance_one_isCone_le_one hK₁ hK₂

end ConeRhoDistances

section ConeHausdorff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A point of one closed cone missing another forces infinite
Pompeiu--Hausdorff distance: the ray through that point escapes linearly. -/
theorem hausdorffEDist_eq_top_of_mem_not_mem_isCone {L₁ L₂ : Set E}
    (hL₁ : IsCone L₁) (hL₂ : IsCone L₂) (hL₂closed : IsClosed L₂)
    {x : E} (hxL₁ : x ∈ L₁) (hxL₂ : x ∉ L₂) :
    hausdorffEDist L₁ L₂ = ⊤ := by
  by_contra hfin
  have hL₂ne : L₂.Nonempty := ⟨0, hL₂.1⟩
  have hd : 0 < infDist x L₂ := by
    rcases (infDist_nonneg (x := x) (s := L₂)).lt_or_eq with h | h
    · exact h
    · exact absurd ((hL₂closed.mem_iff_infDist_zero hL₂ne).2 h.symm) hxL₂
  set H := (hausdorffEDist L₁ L₂).toReal with hHdef
  have hHnn : 0 ≤ H := ENNReal.toReal_nonneg
  obtain ⟨t, ht⟩ := exists_nat_gt ((H + 1) / infDist x L₂)
  have htpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hmem : ((t : ℝ) + 1) • x ∈ L₁ := hL₁.smul_mem hxL₁ htpos.le
  have hle : infDist (((t : ℝ) + 1) • x) L₂ ≤ H := by
    have hinf : infEDist (((t : ℝ) + 1) • x) L₂ ≤ hausdorffEDist L₁ L₂ :=
      infEDist_le_hausdorffEDist_of_mem hmem
    exact ENNReal.toReal_mono hfin hinf
  rw [hL₂.infDist_smul htpos] at hle
  rw [div_lt_iff₀ hd] at ht
  nlinarith [hd, ht, hle]

/-- **Example 4.44**, Pompeiu--Hausdorff clause: distinct closed cones are
always at infinite Pompeiu--Hausdorff distance. -/
theorem hausdorffEDist_isCone_eq_top_of_ne {K₁ K₂ : Set E}
    (hK₁ : IsCone K₁) (hK₂ : IsCone K₂)
    (hK₁closed : IsClosed K₁) (hK₂closed : IsClosed K₂)
    (hne : K₁ ≠ K₂) :
    hausdorffEDist K₁ K₂ = ⊤ := by
  by_cases hsub : K₁ ⊆ K₂
  · have hnsub : ¬ K₂ ⊆ K₁ := fun h ↦ hne (Subset.antisymm hsub h)
    obtain ⟨x, hx₂, hx₁⟩ := Set.not_subset.1 hnsub
    rw [hausdorffEDist_comm]
    exact hausdorffEDist_eq_top_of_mem_not_mem_isCone hK₂ hK₁ hK₁closed hx₂ hx₁
  · obtain ⟨x, hx₁, hx₂⟩ := Set.not_subset.1 hsub
    exact hausdorffEDist_eq_top_of_mem_not_mem_isCone hK₁ hK₂ hK₂closed hx₁ hx₂

end ConeHausdorff

section ConeTruncations

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Retracting a point of a ray to the unit sphere never moves it away from a
point of the unit ball.  This is the projection observation the book uses for
the last identity of Example 4.44. -/
theorem norm_sub_unit_smul_le {x k : E} (hx : ‖x‖ ≤ 1) (hk : 1 ≤ ‖k‖) :
    ‖x - ‖k‖⁻¹ • k‖ ≤ ‖x - k‖ := by
  set s := ‖k‖ with hs
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le one_pos hk
  set u := s⁻¹ • k with hu
  have hunorm : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hspos, ← hs]
    field_simp
  have hk_eq : k = s • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
  have hinner : ⟪x, u⟫_ℝ ≤ 1 := by
    calc ⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
      _ = ‖x‖ := by rw [hunorm, mul_one]
      _ ≤ 1 := hx
  have hexp1 : ‖x - u‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, u⟫_ℝ + 1 := by
    rw [norm_sub_sq_real, hunorm]; ring
  have hexp2 : ‖x - k‖ ^ 2 = ‖x‖ ^ 2 - 2 * s * ⟪x, u⟫_ℝ + s ^ 2 := by
    rw [hk_eq, norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hspos, hunorm]
    ring
  have hsq : ‖x - u‖ ^ 2 ≤ ‖x - k‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hk)
      (by linarith : (0 : ℝ) ≤ s + 1 - 2 * ⟪x, u⟫_ℝ)]
  nlinarith [norm_nonneg (x - u), norm_nonneg (x - k)]

/-- For a cone, truncating to the unit ball does not change distances from
points of the unit ball. -/
theorem infEDist_inter_closedBall_eq_of_isCone {K : Set E} (hK : IsCone K)
    {x : E} (hx : ‖x‖ ≤ 1) :
    infEDist x (K ∩ closedBall (0 : E) 1) = infEDist x K := by
  refine le_antisymm ?_ (infEDist_anti inter_subset_left)
  have hrepr : infEDist x K = ⨅ k ∈ K, edist x k := rfl
  rw [hrepr]
  refine le_iInf₂ fun k hk ↦ ?_
  rcases le_total ‖k‖ 1 with hkle | hkge
  · exact infEDist_le_edist_of_mem ⟨hk, by simpa [mem_closedBall] using hkle⟩
  · have hkpos : (0 : ℝ) < ‖k‖ := lt_of_lt_of_le one_pos hkge
    have hmem : ‖k‖⁻¹ • k ∈ K ∩ closedBall (0 : E) 1 := by
      refine ⟨hK.smul_mem hk (by positivity), ?_⟩
      simp only [mem_closedBall, dist_zero_right, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hkpos]
      rw [inv_mul_cancel₀ hkpos.ne']
    refine le_trans (infEDist_le_edist_of_mem hmem) ?_
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (norm_sub_unit_smul_le hx hkge)

/-- **Example 4.44**, truncation identity: the `1`-distance of the truncated
inclusions is the Pompeiu--Hausdorff distance between the unit-ball
truncations. -/
theorem rhoHatEDistance_one_eq_hausdorffEDist_inter_closedBall
    {K₁ K₂ : Set E} (hK₁ : IsCone K₁) (hK₂ : IsCone K₂) :
    rhoHatEDistance 1 K₁ K₂
      = hausdorffEDist (K₁ ∩ closedBall (0 : E) 1)
          (K₂ ∩ closedBall (0 : E) 1) := by
  rw [rhoHatEDistance, hausdorffEDist_def]
  simp only [NNReal.coe_one]
  refine congrArg₂ (· ⊔ ·) ?_ ?_
  · refine iSup_congr fun x ↦ iSup_congr fun hx ↦ ?_
    exact (infEDist_inter_closedBall_eq_of_isCone hK₂
      (by simpa [mem_closedBall, dist_zero_right] using hx.2)).symm
  · refine iSup_congr fun y ↦ iSup_congr fun hy ↦ ?_
    exact (infEDist_inter_closedBall_eq_of_isCone hK₁
      (by simpa [mem_closedBall, dist_zero_right] using hy.2)).symm

end ConeTruncations

section ConeHatDistances

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Example 4.44**, hatted clause: for closed cones the truncated-inclusion
distance agrees with the `ρ`-distance at every radius, with no convexity
hypothesis.  This uses the cone half of Lemma 4.34. -/
theorem rhoHatDistance_eq_rhoDistance_of_isCone (r : ℝ≥0)
    {K₁ K₂ : Set E} (hK₁closed : IsClosed K₁) (hK₂closed : IsClosed K₂)
    (hK₁ : IsCone K₁) (hK₂ : IsCone K₂) :
    rhoHatDistance r K₁ K₂ = rhoDistance r K₁ K₂ := by
  have hK₁ne : K₁.Nonempty := ⟨0, hK₁.1⟩
  have hK₂ne : K₂.Nonempty := ⟨0, hK₂.1⟩
  refine le_antisymm (rhoHatDistance_le_rhoDistance r hK₁ne hK₂ne) ?_
  have he : 0 ≤ rhoHatDistance r K₁ K₂ := rhoHatDistance_nonneg r K₁ K₂
  obtain ⟨h12, h21⟩ := (rhoHatDistance_le_iff r hK₁ne hK₂ne he).1 le_rfl
  rw [rhoDistance_le_iff he]
  intro x hx
  have hA : infDist x K₂ ≤ infDist x K₁ + rhoHatDistance r K₁ K₂ :=
    (inter_closedBall_subset_cthickening_iff_infDist_le_of_isCone
      hK₁closed hK₁ne hK₁ hK₂ne he).1 h12 x hx
  have hB : infDist x K₁ ≤ infDist x K₂ + rhoHatDistance r K₁ K₂ :=
    (inter_closedBall_subset_cthickening_iff_infDist_le_of_isCone
      hK₂closed hK₂ne hK₂ hK₁ne he).1 h21 x hx
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **Example 4.44**, hatted linearity: `dl̂_ρ(K₁, K₂) = ρ · dl̂_1(K₁, K₂)`. -/
theorem rhoHatDistance_isCone_eq (r : ℝ≥0)
    {K₁ K₂ : Set E} (hK₁closed : IsClosed K₁) (hK₂closed : IsClosed K₂)
    (hK₁ : IsCone K₁) (hK₂ : IsCone K₂) :
    rhoHatDistance r K₁ K₂ = (r : ℝ) * rhoHatDistance 1 K₁ K₂ := by
  rw [rhoHatDistance_eq_rhoDistance_of_isCone r hK₁closed hK₂closed hK₁ hK₂,
    rhoHatDistance_eq_rhoDistance_of_isCone 1 hK₁closed hK₂closed hK₁ hK₂,
    rhoDistance_isCone_eq hK₁ hK₂]

end ConeHatDistances

section ConeCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem isCone_singleton_zero : IsCone ({0} : Set E) :=
  ⟨rfl, by
    intro x hx c _
    rw [mem_singleton_iff] at hx
    simp [hx]⟩

/-- The zero cone, as a point of the hyperspace of Theorem 4.42. -/
def zeroCone : SetMetricModel E :=
  ⟨⟨{0}, ⟨isClosed_singleton, ⟨0, rfl⟩⟩⟩⟩

@[simp]
theorem zeroCone_carrier : (zeroCone : SetMetricModel E).carrier = {0} := rfl

/-- **Example 4.44**, compactness clause: the closed cones form a compact
subset of the hyperspace `(cl-sets≠∅(E), dl)`. -/
theorem isCompact_setOf_isCone :
    IsCompact {C : SetMetricModel E | IsCone C.carrier} := by
  have hclosed : IsClosed {C : SetMetricModel E | IsCone C.carrier} := by
    refine IsSeqClosed.isClosed fun u C hu hlim ↦ ?_
    have hpk : PKConverges (fun n ↦ (u n).carrier) C.carrier :=
      SetMetricModel.tendsto_iff_pkConverges.1 hlim
    exact hpk.isCone hu
  refine IsCompact.of_isClosed_subset
    (ProperSpace.isCompact_closedBall (zeroCone : SetMetricModel E) 1)
    hclosed fun C hC ↦ ?_
  exact Metric.mem_closedBall.2
    (integratedSetDistance_isCone_le_one hC isCone_singleton_zero)

end ConeCompactness

section ConeSummary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Example 4.44**, displayed chain: for closed cones

  `dl(K₁,K₂) = dl_1(K₁,K₂) = dl̂_1(K₁,K₂) = dl∞(K₁ ∩ IB, K₂ ∩ IB) ≤ 1`,

together with the linearity `dl_ρ = dl̂_ρ = ρ · dl_1` at every radius. -/
theorem integratedSetDistance_isCone_chain {K₁ K₂ : Set E}
    (hK₁closed : IsClosed K₁) (hK₂closed : IsClosed K₂)
    (hK₁ : IsCone K₁) (hK₂ : IsCone K₂) :
    integratedSetDistance K₁ K₂ = rhoDistance 1 K₁ K₂
      ∧ rhoDistance 1 K₁ K₂ = rhoHatDistance 1 K₁ K₂
      ∧ rhoHatDistance 1 K₁ K₂
          = (hausdorffEDist (K₁ ∩ closedBall (0 : E) 1)
              (K₂ ∩ closedBall (0 : E) 1)).toReal
      ∧ integratedSetDistance K₁ K₂ ≤ 1
      ∧ ∀ ρ : ℝ≥0, rhoDistance ρ K₁ K₂ = (ρ : ℝ) * rhoDistance 1 K₁ K₂
          ∧ rhoHatDistance ρ K₁ K₂ = (ρ : ℝ) * rhoDistance 1 K₁ K₂ := by
  refine ⟨integratedSetDistance_isCone_eq hK₁ hK₂,
    (rhoHatDistance_eq_rhoDistance_of_isCone 1 hK₁closed hK₂closed hK₁ hK₂).symm,
    ?_, integratedSetDistance_isCone_le_one hK₁ hK₂, fun ρ ↦
      ⟨rhoDistance_isCone_eq hK₁ hK₂ ρ, ?_⟩⟩
  · exact congrArg ENNReal.toReal
      (rhoHatEDistance_one_eq_hausdorffEDist_inter_closedBall hK₁ hK₂)
  · rw [rhoHatDistance_eq_rhoDistance_of_isCone ρ hK₁closed hK₂closed hK₁ hK₂,
      rhoDistance_isCone_eq hK₁ hK₂]

end ConeSummary

end RW
