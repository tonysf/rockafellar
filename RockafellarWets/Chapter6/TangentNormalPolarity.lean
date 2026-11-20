/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangent-Normal Polarity and Clarke Regularity

Theorem 6.28 and Corollaries 6.29--6.30. The regular-tangent polarity proof
uses a direct projection witness, avoiding a dependency on Proposition 6.27.
The projection argument was originally infrastructure for Proposition 6.41.
-/

import RockafellarWets.Chapter6.ElementaryCones
import RockafellarWets.Chapter6.ProximalNormals
import RockafellarWets.Chapter6.RegularTangents
import RockafellarWets.Chapter6.Polarity

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Theorem 6.28(a)**: the regular normal cone is the polar of the tangent cone. -/
theorem regularNormalCone_eq_polarCone_tangentCone
    {C : Set F} {x : F} (hx : x ∈ C) :
    regularNormalCone C x = polarCone (tangentCone C x) := by
  ext v
  exact mem_regularNormalCone_iff_inner_nonpos hx

/-- Limiting normals pair nonpositively with regular tangents. -/
theorem inner_nonpos_of_mem_normalCone_of_mem_regularTangentCone
    {C : Set F} {x v w : F} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x)
    (hv : v ∈ normalCone C x) (hw : w ∈ regularTangentCone C x) :
    ⟪v, w⟫_ℝ ≤ 0 := by
  obtain ⟨_, xs, vs, hxsC, hxto, hvs, hvto⟩ := hv
  obtain ⟨ws, hws, hwto⟩ :=
    (mem_regularTangentCone_iff_forall_tangent_sequences hx hlc).1 hw xs hxsC hxto
  exact le_of_tendsto (hvto.inner hwto)
    (Eventually.of_forall fun n ↦ inner_nonpos_of_mem_regularNormalCone (hvs n) (hws n))

/-- A projection witness for Proposition 6.27(b) and Theorem 6.28(b): at a point of local closedness
the distance from `w` to the tangent cone is realized by a normal vector,
obtained by projecting `x̄ + τw` onto `C` and blowing up. -/
theorem exists_mem_normalCone_norm_eq_infDist_tangentCone
    {C : Set F} {x : F} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) (w : F) :
    ∃ v ∈ normalCone C x, ‖v‖ = infDist w (tangentCone C x) ∧
      ⟪v, w⟫_ℝ = infDist w (tangentCone C x) ^ 2 := by
  classical
  obtain ⟨V, hV, hVclosed, hDclosed⟩ := hlc
  have hxV : x ∈ V := mem_of_mem_nhds hV
  have hxD : x ∈ C ∩ V := ⟨hx, hxV⟩
  have hTD : tangentCone (C ∩ V) x = tangentCone C x := tangentCone_inter_nhds hV
  have h0T : (0 : F) ∈ tangentCone C x := (isCone_tangentCone hx).1
  obtain ⟨wbar, hwbarT, hwbard⟩ :=
    (isClosed_tangentCone C x).exists_infDist_eq_dist ⟨0, h0T⟩ w
  have hwbarnorm : ‖w - wbar‖ = infDist w (tangentCone C x) := by
    rw [hwbard, dist_eq_norm]
  rw [← hTD] at hwbarT
  obtain ⟨xs, τs, hxsD, -, hτpos, hτ0, hxq⟩ := hwbarT
  have hproj : ∀ n, ∃ q, q ∈ projMapping (C ∩ V) (x + τs n • w) :=
    fun n ↦ projMapping_nonempty hDclosed ⟨x, hxD⟩ _
  choose p hp using hproj
  -- the projected difference quotients beat the given ones
  have hcmp : ∀ n, ‖w - (τs n)⁻¹ • (p n - x)‖ ≤ ‖w - (τs n)⁻¹ • (xs n - x)‖ := by
    intro n
    have hmin := (hp n).2 (xs n) (hxsD n)
    have hid1 : p n - (x + τs n • w) = -(τs n • (w - (τs n)⁻¹ • (p n - x))) := by
      have h1 : τs n • (w - (τs n)⁻¹ • (p n - x)) = τs n • w - (p n - x) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ (hτpos n).ne', one_smul]
      rw [h1]
      abel
    have hid2 : xs n - (x + τs n • w) = -(τs n • (w - (τs n)⁻¹ • (xs n - x))) := by
      have h1 : τs n • (w - (τs n)⁻¹ • (xs n - x)) = τs n • w - (xs n - x) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ (hτpos n).ne', one_smul]
      rw [h1]
      abel
    rw [hid1, hid2, norm_neg, norm_neg, norm_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hτpos n)] at hmin
    exact le_of_mul_le_mul_left hmin (hτpos n)
  -- a uniform bound for the projected difference quotients
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ n, ‖w - (τs n)⁻¹ • (xs n - x)‖ ≤ R := by
    have hato : Tendsto (fun n ↦ ‖w - (τs n)⁻¹ • (xs n - x)‖) atTop
        (nhds ‖w - wbar‖) := (tendsto_const_nhds.sub hxq).norm
    obtain ⟨R, hRsub⟩ := (isBounded_range_of_tendsto _ hato).subset_closedBall (0 : ℝ)
    refine ⟨R, fun n ↦ ?_⟩
    have hmem := hRsub (mem_range_self n)
    rw [mem_closedBall, Real.dist_eq, sub_zero] at hmem
    exact (le_abs_self _).trans hmem
  have hubound : ∀ n, ‖(τs n)⁻¹ • (p n - x)‖ ≤ ‖w‖ + R := by
    intro n
    have h1 : ‖w - (τs n)⁻¹ • (p n - x)‖ ≤ R := (hcmp n).trans (hR n)
    have h2 : ‖(τs n)⁻¹ • (p n - x)‖ ≤ ‖w‖ + ‖w - (τs n)⁻¹ • (p n - x)‖ := by
      have h3 := norm_sub_le w (w - (τs n)⁻¹ • (p n - x))
      simpa using h3
    linarith
  have hpx : Tendsto (fun n ↦ p n - x) atTop (nhds 0) := by
    have hbound : ∀ n, ‖p n - x‖ ≤ τs n * (‖w‖ + R) := by
      intro n
      have hpe : ‖p n - x‖ = τs n * ‖(τs n)⁻¹ • (p n - x)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hτpos n)),
          ← mul_assoc, mul_inv_cancel₀ (hτpos n).ne', one_mul]
      rw [hpe]
      exact mul_le_mul_of_nonneg_left (hubound n) (hτpos n).le
    have hzero : Tendsto (fun n ↦ τs n * (‖w‖ + R)) atTop (nhds 0) := by
      simpa using hτ0.mul_const (‖w‖ + R)
    exact squeeze_zero_norm hbound hzero
  have hpto : Tendsto p atTop (nhds x) := by
    have h := hpx.add_const x
    simpa using h
  have hseq : ∀ n : ℕ, ((τs n)⁻¹ • (p n - x)) ∈ closedBall (0 : F) (‖w‖ + R) := by
    intro n
    rw [mem_closedBall, dist_zero_right]
    exact hubound n
  obtain ⟨qq, -, φ, hφ, hqqto⟩ :=
    (isCompact_closedBall (0 : F) (‖w‖ + R)).tendsto_subseq hseq
  have hφid : ∀ k, k ≤ φ k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_self n)))
  have hqqT : qq ∈ tangentCone C x := by
    rw [← hTD]
    exact mem_tangentCone_of_forall (xs := fun k ↦ p (φ k)) (τs := fun k ↦ τs (φ k))
      (fun k ↦ (hp (φ k)).1) (fun k ↦ hτpos (φ k)) (hτ0.comp hφ.tendsto_atTop) hqqto
  have hnormqq : ‖w - qq‖ = infDist w (tangentCone C x) := by
    refine le_antisymm ?_ ?_
    · have hlim1 : Tendsto (fun k ↦ ‖w - (τs (φ k))⁻¹ • (p (φ k) - x)‖) atTop
          (nhds ‖w - qq‖) := (tendsto_const_nhds.sub hqqto).norm
      have hlim2 : Tendsto (fun k ↦ ‖w - (τs (φ k))⁻¹ • (xs (φ k) - x)‖) atTop
          (nhds ‖w - wbar‖) :=
        ((tendsto_const_nhds.sub hxq).norm).comp hφ.tendsto_atTop
      have hle := le_of_tendsto_of_tendsto hlim1 hlim2
        (Filter.Eventually.of_forall fun k ↦ hcmp (φ k))
      exact hle.trans_eq hwbarnorm
    · rw [← dist_eq_norm]
      exact infDist_le_dist_of_mem hqqT
  -- the difference quotients are regular normals to the locally closed piece
  have hvecCV : ∀ n, w - (τs n)⁻¹ • (p n - x) ∈ regularNormalCone (C ∩ V) (p n) := by
    intro n
    have hid : (τs n)⁻¹ • ((x + τs n • w) - p n) = w - (τs n)⁻¹ • (p n - x) := by
      have h1 : (x + τs n • w) - p n = τs n • w - (p n - x) := by abel
      rw [h1, smul_sub, smul_smul, inv_mul_cancel₀ (hτpos n).ne', one_smul]
    rw [← hid]
    exact nonneg_smul_sub_mem_regularNormalCone_of_mem_projMapping (hp n)
      (inv_nonneg.2 (hτpos n).le)
  have hintV : interior V ∈ nhds x :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hV)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hpto hintV)
  have hshift : Tendsto (fun k ↦ φ (k + N)) atTop atTop :=
    hφ.tendsto_atTop.comp (tendsto_add_atTop_nat N)
  refine ⟨w - qq, ?_, hnormqq, ?_⟩
  · refine mem_normalCone_of_forall hx
      (xs := fun k ↦ p (φ (k + N)))
      (vs := fun k ↦ w - (τs (φ (k + N)))⁻¹ • (p (φ (k + N)) - x))
      (hpto.comp hshift) (fun k ↦ ?_)
      (tendsto_const_nhds.sub (hqqto.comp (tendsto_add_atTop_nat N)))
    have hge : N ≤ φ (k + N) := le_trans (Nat.le_add_left N k) (hφid (k + N))
    have hmemV : V ∈ nhds (p (φ (k + N))) :=
      mem_interior_iff_mem_nhds.1 (hN _ hge)
    rw [← regularNormalCone_inter_nhds hmemV]
    exact hvecCV _
  · -- conic minimality of the limiting quotient turns the distance into a pairing
    have hmin : ∀ lam : ℝ, 0 ≤ lam → ‖w - qq‖ ≤ ‖w - lam • qq‖ := by
      intro lam hlam
      rw [hnormqq, ← dist_eq_norm]
      exact infDist_le_dist_of_mem ((isCone_tangentCone hx).smul_mem hqqT hlam)
    have horth : ⟪w - qq, qq⟫_ℝ = 0 := by
      by_cases hqq0 : qq = 0
      · rw [hqq0, inner_zero_right]
      · have ha : (0 : ℝ) < ‖qq‖ ^ 2 := by
          have : ‖qq‖ ≠ 0 := norm_ne_zero_iff.2 hqq0
          positivity
        have hquad : ∀ lam : ℝ, 0 ≤ lam →
            ‖qq‖ ^ 2 - 2 * ⟪w, qq⟫_ℝ ≤ lam ^ 2 * ‖qq‖ ^ 2 - 2 * lam * ⟪w, qq⟫_ℝ := by
          intro lam hlam
          have h1 := hmin lam hlam
          have h2 : ‖w - qq‖ ^ 2 ≤ ‖w - lam • qq‖ ^ 2 := by
            have := norm_nonneg (w - qq)
            nlinarith
          rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_right, norm_smul,
            Real.norm_eq_abs, abs_of_nonneg hlam, mul_pow] at h2
          linarith
        have hb : 0 < ⟪w, qq⟫_ℝ := by
          have h0 := hquad 0 le_rfl
          nlinarith
        have hlam : (0 : ℝ) ≤ ⟪w, qq⟫_ℝ / ‖qq‖ ^ 2 := by positivity
        have h := hquad (⟪w, qq⟫_ℝ / ‖qq‖ ^ 2) hlam
        have hmul := mul_le_mul_of_nonneg_right h ha.le
        have hrhs : ((⟪w, qq⟫_ℝ / ‖qq‖ ^ 2) ^ 2 * ‖qq‖ ^ 2 -
            2 * (⟪w, qq⟫_ℝ / ‖qq‖ ^ 2) * ⟪w, qq⟫_ℝ) * ‖qq‖ ^ 2 = -⟪w, qq⟫_ℝ ^ 2 := by
          field_simp
          ring
        rw [hrhs] at hmul
        have hsq : (‖qq‖ ^ 2 - ⟪w, qq⟫_ℝ) ^ 2 ≤ 0 := by nlinarith
        have hzero : ‖qq‖ ^ 2 - ⟪w, qq⟫_ℝ = 0 :=
          pow_eq_zero_iff (n := 2) (by norm_num) |>.1
            (le_antisymm hsq (sq_nonneg _))
        rw [inner_sub_left, real_inner_self_eq_norm_sq]
        linarith
    have hsplit : w = (w - qq) + qq := by abel
    calc ⟪w - qq, w⟫_ℝ = ⟪w - qq, (w - qq) + qq⟫_ℝ := by rw [← hsplit]
      _ = ⟪w - qq, w - qq⟫_ℝ + ⟪w - qq, qq⟫_ℝ := inner_add_right _ _ _
      _ = ‖w - qq‖ ^ 2 := by rw [real_inner_self_eq_norm_sq, horth, add_zero]
      _ = infDist w (tangentCone C x) ^ 2 := by rw [hnormqq]

/-- **Theorem 6.28(b)**: at a point of local closedness, the regular tangent
cone is the polar of the limiting normal cone. -/
theorem regularTangentCone_eq_polarCone_normalCone
    {C : Set F} {x : F} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    regularTangentCone C x = polarCone (normalCone C x) := by
  refine Subset.antisymm ?_ ?_
  · intro w hw v hv
    rw [real_inner_comm]
    exact inner_nonpos_of_mem_normalCone_of_mem_regularTangentCone hx hlc hv hw
  · intro w hw
    by_contra hnot
    rw [regularTangentCone_eq_svInnerLimitWithin_tangentCone hx hlc] at hnot
    obtain ⟨ε, hε, xbars, hxbarC, hxbarto, hempty⟩ :=
      not_mem_svInnerLimitWithin_tangentCone_iff_exists_sequences.1 hnot
    obtain ⟨V, hV, hVclosed, hDclosed⟩ := hlc
    have hintV : interior V ∈ nhds x :=
      isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hV)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hxbarto hintV)
    have hnear : ∀ k : ℕ, IsLocallyClosedAt C (xbars (k + N)) := fun k ↦
      ⟨V, mem_interior_iff_mem_nhds.1 (hN _ (Nat.le_add_left N k)), hVclosed, hDclosed⟩
    have hlow : ∀ k : ℕ, ε ≤ infDist w (tangentCone C (xbars (k + N))) := by
      intro k
      by_contra hlt
      push_neg at hlt
      obtain ⟨z, hzT, hzd⟩ :=
        (infDist_lt_iff ⟨0, (isCone_tangentCone (hxbarC (k + N))).1⟩).1 hlt
      have hz : z ∈ tangentCone C (xbars (k + N)) ∩ ball w ε := ⟨hzT, mem_ball'.2 hzd⟩
      rw [hempty (k + N)] at hz
      exact hz
    have hhigh : ∀ k : ℕ, infDist w (tangentCone C (xbars (k + N))) ≤ ‖w‖ := by
      intro k
      have h := infDist_le_dist_of_mem (x := w)
        (isCone_tangentCone (hxbarC (k + N))).1
      rwa [dist_zero_right] at h
    have hpick : ∀ k : ℕ, ∃ v ∈ normalCone C (xbars (k + N)),
        ‖v‖ = infDist w (tangentCone C (xbars (k + N))) ∧
        ⟪v, w⟫_ℝ = infDist w (tangentCone C (xbars (k + N))) ^ 2 := fun k ↦
      exists_mem_normalCone_norm_eq_infDist_tangentCone (hxbarC (k + N)) (hnear k) w
    choose vs hvsmem hvsnorm hvsinner using hpick
    have hball : ∀ k : ℕ, vs k ∈ closedBall (0 : F) ‖w‖ := by
      intro k
      rw [mem_closedBall, dist_zero_right, hvsnorm k]
      exact hhigh k
    obtain ⟨v, -, φ, hφ, hvto⟩ := (isCompact_closedBall (0 : F) ‖w‖).tendsto_subseq hball
    have hxbarto' : Tendsto (fun k ↦ xbars (k + N)) atTop (nhds x) :=
      hxbarto.comp (tendsto_add_atTop_nat N)
    have hvmem : v ∈ normalCone C x :=
      mem_normalCone_of_tendsto hx (fun k ↦ hxbarC (φ k + N))
        (hxbarto'.comp hφ.tendsto_atTop) (fun k ↦ hvsmem (φ k)) hvto
    have hpos : ε ^ 2 ≤ ⟪v, w⟫_ℝ := by
      refine ge_of_tendsto (hvto.inner tendsto_const_nhds) ?_
      filter_upwards with k
      change ε ^ 2 ≤ ⟪vs (φ k), w⟫_ℝ
      rw [hvsinner (φ k)]
      nlinarith [hlow (φ k), hε.le]
    have hnonpos : ⟪v, w⟫_ℝ ≤ 0 := by
      simpa only [real_inner_comm] using hw v hvmem
    nlinarith [hε]

/-- **Corollary 6.29**, `(a) ⇒ (b)`: ordinary and regular tangents agree at
a Clarke regular point. -/
theorem tangentCone_eq_regularTangentCone_of_isClarkeRegularAt
    {C : Set F} {x : F} (hx : x ∈ C) (hreg : IsClarkeRegularAt C x) :
    tangentCone C x = regularTangentCone C x := by
  refine Subset.antisymm ?_ (regularTangentCone_subset_tangentCone hx)
  rw [regularTangentCone_eq_polarCone_normalCone hx hreg.1, hreg.2,
    regularNormalCone_eq_polarCone_tangentCone hx]
  exact subset_polarCone_bipolar _

/-- **Corollary 6.29(a),(b)**: Clarke regularity is regularity of every
tangent vector, provided the set is locally closed. -/
theorem isClarkeRegularAt_iff_tangentCone_eq_regularTangentCone
    {C : Set F} {x : F} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔ tangentCone C x = regularTangentCone C x := by
  refine ⟨tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hx, ?_⟩
  intro h
  refine isClarkeRegularAt_iff.2 ⟨hlc, ?_⟩
  intro v hv
  apply (mem_regularNormalCone_iff_inner_nonpos hx).2
  intro w hw
  rw [h] at hw
  exact inner_nonpos_of_mem_normalCone_of_mem_regularTangentCone hx hlc hv hw

/-- **Corollary 6.29(a),(c)**: the normal cone equals the polar of the
tangent cone exactly at Clarke regular points. -/
theorem isClarkeRegularAt_iff_normalCone_eq_polarCone_tangentCone
    {C : Set F} {x : F} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔ normalCone C x = polarCone (tangentCone C x) := by
  rw [← regularNormalCone_eq_polarCone_tangentCone hx]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hlc, h⟩⟩

/-- **Corollary 6.29(a),(d)**: the tangent cone equals the polar of the
normal cone exactly at Clarke regular points. -/
theorem isClarkeRegularAt_iff_tangentCone_eq_polarCone_normalCone
    {C : Set F} {x : F} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔ tangentCone C x = polarCone (normalCone C x) := by
  rw [← regularTangentCone_eq_polarCone_normalCone hx hlc]
  exact isClarkeRegularAt_iff_tangentCone_eq_regularTangentCone hx hlc

/-- **Corollary 6.29(a),(e)**: Clarke regularity is the nonpositive-pairing
condition for all tangent and limiting normal vectors. -/
theorem isClarkeRegularAt_iff_inner_nonpos
    {C : Set F} {x : F} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔
      ∀ w ∈ tangentCone C x, ∀ v ∈ normalCone C x, ⟪v, w⟫_ℝ ≤ 0 := by
  constructor
  · intro h w hw v hv
    apply inner_nonpos_of_mem_regularNormalCone (v := v) ?_ hw
    rwa [← h.2]
  · intro h
    refine isClarkeRegularAt_iff.2 ⟨hlc, ?_⟩
    intro v hv
    exact (mem_regularNormalCone_iff_inner_nonpos hx).2 (fun w hw ↦ h w hw v hv)

omit [FiniteDimensional ℝ F] in
/-- **Corollary 6.29(a),(f)**: Clarke regularity is outer semicontinuity of
the regular-normal mapping relative to the set. -/
theorem isClarkeRegularAt_iff_svOscWithinAt_regularNormalCone
    {C : Set F} {x : F} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔ SvOscWithinAt (regularNormalCone C) C x := by
  rw [svOscWithinAt_iff_svOuterLimitWithin_eq hx,
    ← normalCone_eq_svOuterLimitWithin hx]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hlc, h⟩⟩

/-- **Corollary 6.29(a),(g)**: Clarke regularity is inner semicontinuity of
the tangent-cone mapping relative to the set. -/
theorem isClarkeRegularAt_iff_svIscWithinAt_tangentCone
    {C : Set F} {x : F} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔ SvIscWithinAt (tangentCone C) C x := by
  change IsClarkeRegularAt C x ↔ tangentCone C x ⊆
    svInnerLimitWithin (tangentCone C) C x
  rw [← regularTangentCone_eq_svInnerLimitWithin_tangentCone hx hlc,
    isClarkeRegularAt_iff_tangentCone_eq_regularTangentCone hx hlc]
  exact ⟨fun h ↦ h.subset,
    fun h ↦ Subset.antisymm h (regularTangentCone_subset_tangentCone hx)⟩

/-- **Corollary 6.30**: the tangent cone at a Clarke regular point is convex. -/
theorem convex_tangentCone_of_isClarkeRegularAt
    {C : Set F} {x : F} (hx : x ∈ C) (hreg : IsClarkeRegularAt C x) :
    Convex ℝ (tangentCone C x) := by
  rw [tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hx hreg]
  exact convex_regularTangentCone hx

omit [FiniteDimensional ℝ F] in
/-- **Corollary 6.30**: the limiting normal cone at a Clarke regular point
is convex. -/
theorem convex_normalCone_of_isClarkeRegularAt
    {C : Set F} {x : F} (hreg : IsClarkeRegularAt C x) :
    Convex ℝ (normalCone C x) := by
  rw [hreg.2]
  exact convex_regularNormalCone C x

/-- **Corollary 6.30**: the normal cone at a Clarke regular point is the
polar of the tangent cone. -/
theorem normalCone_eq_polarCone_tangentCone_of_isClarkeRegularAt
    {C : Set F} {x : F} (hx : x ∈ C) (hreg : IsClarkeRegularAt C x) :
    normalCone C x = polarCone (tangentCone C x) :=
  (isClarkeRegularAt_iff_normalCone_eq_polarCone_tangentCone hx hreg.1).1 hreg

/-- **Corollary 6.30**: the tangent cone at a Clarke regular point is the
polar of the normal cone. -/
theorem tangentCone_eq_polarCone_normalCone_of_isClarkeRegularAt
    {C : Set F} {x : F} (hx : x ∈ C) (hreg : IsClarkeRegularAt C x) :
    tangentCone C x = polarCone (normalCone C x) :=
  (isClarkeRegularAt_iff_tangentCone_eq_polarCone_normalCone hx hreg.1).1 hreg

/-- **Corollary 6.30**: Clarke regularity implies geometric derivability. -/
theorem isGeometricallyDerivable_of_isClarkeRegularAt
    {C : Set F} {x : F} (hx : x ∈ C) (hreg : IsClarkeRegularAt C x) :
    IsGeometricallyDerivable C x := by
  unfold IsGeometricallyDerivable
  rw [tangentCone_eq_regularTangentCone_of_isClarkeRegularAt hx hreg]
  exact regularTangentCone_subset_derivableCone hx

/-- **Corollary 6.30**, all clauses together: convex mutual polar cones and
geometric derivability at a Clarke regular point. -/
theorem clarkeRegularity_consequences
    {C : Set F} {x : F} (hx : x ∈ C) (hreg : IsClarkeRegularAt C x) :
    Convex ℝ (tangentCone C x) ∧ Convex ℝ (normalCone C x) ∧
      normalCone C x = polarCone (tangentCone C x) ∧
      tangentCone C x = polarCone (normalCone C x) ∧
      IsGeometricallyDerivable C x :=
  ⟨convex_tangentCone_of_isClarkeRegularAt hx hreg,
    convex_normalCone_of_isClarkeRegularAt hreg,
    normalCone_eq_polarCone_tangentCone_of_isClarkeRegularAt hx hreg,
    tangentCone_eq_polarCone_normalCone_of_isClarkeRegularAt hx hreg,
    isGeometricallyDerivable_of_isClarkeRegularAt hx hreg⟩

end RW
