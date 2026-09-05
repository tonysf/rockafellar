/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Finite Product Cone Formulas

This file completes Proposition 6.41 for arbitrary finite products.  The
ambient product is the Euclidean `L²` product `PiLp 2 E` of finitely many
factors, never the sup-normed raw `Pi` type: 6.41 is a statement about `IRⁿ`
written as `IR^{n_1} × ⋯ × IR^{n_m}`, and its normal-cone formulas are false
for the sup norm.

The binary `WithLp 2 (E × F)` API of
[`ProductCones.lean`](RockafellarWets/Chapter6/ProductCones.lean) is left
unchanged and is not duplicated; the finite formulas are proved directly in
coordinates rather than by a dependent induction over binary products, and
nothing from that module is used.

One auxiliary result is proved here because the last clause of 6.41 needs it
and nothing in the repository supplies it yet; it is not a formalization of
the results it is drawn from.  The other ingredient, the locality of `N̂_C(x̄)`
under intersection with a neighborhood of `x̄`, is
`regularNormalCone_inter_nhds` of
[`ElementaryCones.lean`](RockafellarWets/Chapter6/ElementaryCones.lean).

* `tangentCone_eq_regularTangentCone_of_isClarkeRegularAt` is the *only*
  consequence of Clarke regularity that the last clause of 6.41 uses, namely
  `T_C(x̄) = T̂_C(x̄)`.  It is **not** a formalization of 6.28--6.30: none of
  the polarity equivalences of 6.28, none of the seven characterizations of
  6.29, and no part of 6.30 is stated.  The proof does not follow the book's,
  which routes through the tangent-normal polarity 6.28(b) and hence through
  6.27 and the approximation of normals 6.18(b), none of which are available
  here.  Instead it combines formula 6(16) from
  [`RegularTangents.lean`](RockafellarWets/Chapter6/RegularTangents.lean) with
  a direct projection argument: if the tangent cone at a nearby point misses a
  ball around `w`, then blowing up a nearest point of `C` to `x̄ + τw`
  produces, in the limit, a normal vector `v ∈ N_C(x̄)` with `⟨v, w⟩ > 0`,
  which Clarke regularity and 6(6) forbid.  The conic minimality
  `⟨w - q, q⟩ = 0` at the limiting difference quotient `q` is what turns the
  distance estimate into a strictly positive pairing.
-/

import RockafellarWets.Chapter6.ProductCones
import RockafellarWets.Chapter6.ElementaryCones
import RockafellarWets.Chapter6.ProximalNormals
import RockafellarWets.Chapter6.RegularTangents
import RockafellarWets.Chapter6.Polarity
import Mathlib.Analysis.InnerProductSpace.PiL2

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section ClarkeRegularTangents

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Infrastructure for the last clause of Proposition 6.41, not a
formalization of 6.27: at a point of local closedness the distance from `w` to
the tangent cone is realized by a *normal* vector, obtained by projecting the
points `x̄ + τw` onto `C` and blowing up. -/
private theorem exists_mem_normalCone_norm_eq_infDist_tangentCone
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

/-- Infrastructure for the last clause of Proposition 6.41: at a point of
Clarke regularity the ordinary and the regular tangent cones agree.

This is the implication `(a) ⇒ (b)` of Corollary 6.29 and *nothing else*: no
polarity relation of 6.28, no other characterization of 6.29 and no clause of
6.30 is claimed here.  The proof is not the book's.  Failure of the inclusion
would give, by formula 6(16), points `x̄ν →_C x̄` whose tangent cones all miss
a fixed ball around `w`; the projection lemma above then produces normals
`vν ∈ N_C(x̄ν)` of bounded length with `⟨vν, w⟩ ≥ ε²`, and a cluster point
lands in `N_C(x̄) = N̂_C(x̄)`, contradicting formula 6(6). -/
theorem tangentCone_eq_regularTangentCone_of_isClarkeRegularAt
    {C : Set F} {x : F} (hx : x ∈ C) (hreg : IsClarkeRegularAt C x) :
    tangentCone C x = regularTangentCone C x := by
  refine Subset.antisymm ?_ (regularTangentCone_subset_tangentCone hx)
  intro w hw
  by_contra hnot
  rw [regularTangentCone_eq_svInnerLimitWithin_tangentCone hx hreg.1] at hnot
  obtain ⟨ε, hε, xbars, hxbarC, hxbarto, hempty⟩ :=
    not_mem_svInnerLimitWithin_tangentCone_iff_exists_sequences.1 hnot
  obtain ⟨V, hV, hVclosed, hDclosed⟩ := hreg.1
  have hintV : interior V ∈ nhds x :=
    isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hV)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hxbarto hintV)
  have hlc : ∀ k : ℕ, IsLocallyClosedAt C (xbars (k + N)) := fun k ↦
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
    exists_mem_normalCone_norm_eq_infDist_tangentCone (hxbarC (k + N)) (hlc k) w
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
    refine inner_nonpos_of_mem_regularNormalCone ?_ hw
    rw [← hreg.2]
    exact hvmem
  nlinarith [hε]

/-- The bipolar reading of formula 6(6): the closed convex conic hull of the
tangent cone is the polar of the regular normal cone. -/
private theorem closure_conicHull_tangentCone {S : Set F} {y : F} (hy : y ∈ S) :
    closure (conicHull (tangentCone S y)) = polarCone (regularNormalCone S y) := by
  have h : regularNormalCone S y = polarCone (tangentCone S y) := by
    ext v
    rw [mem_regularNormalCone_iff_inner_nonpos hy, mem_polarCone]
  rw [h, polarCone_bipolar]

end ClarkeRegularTangents

section FiniteProducts

variable {ι : Type*} {E : ι → Type*}

/-- The finite product of the sets `C i`, regarded as a subset of the
Euclidean `L²` product. -/
def l2PiSet (C : ∀ i, Set (E i)) : Set (PiLp 2 E) :=
  {x | ∀ i, x i ∈ C i}

@[simp]
theorem mem_l2PiSet {C : ∀ i, Set (E i)} {x : PiLp 2 E} :
    x ∈ l2PiSet C ↔ ∀ i, x i ∈ C i :=
  Iff.rfl

@[simp]
theorem toLp_mem_l2PiSet {C : ∀ i, Set (E i)} {f : ∀ i, E i} :
    WithLp.toLp 2 f ∈ l2PiSet C ↔ ∀ i, f i ∈ C i :=
  Iff.rfl

section Update

variable [DecidableEq ι]

/-- The point of the finite Euclidean `L²` product agreeing with `x` off the
coordinate `i`, where it takes the value `y`.  Such single-coordinate
variations reduce the forward halves of the product formulas to one factor at
a time. -/
def l2PiUpdate (x : PiLp 2 E) (i : ι) (y : E i) : PiLp 2 E :=
  WithLp.toLp 2 (Function.update (WithLp.ofLp x) i y)

@[simp]
theorem l2PiUpdate_self (x : PiLp 2 E) (i : ι) (y : E i) :
    (l2PiUpdate x i y) i = y :=
  Function.update_self i y _

theorem l2PiUpdate_of_ne (x : PiLp 2 E) {i j : ι} (h : j ≠ i) (y : E i) :
    (l2PiUpdate x i y) j = x j :=
  Function.update_of_ne h y _

@[simp]
theorem l2PiUpdate_apply (x : PiLp 2 E) (i : ι) : l2PiUpdate x i (x i) = x := by
  have h : Function.update (WithLp.ofLp x) i (x i) = WithLp.ofLp x :=
    Function.update_eq_self i _
  rw [l2PiUpdate, h, WithLp.toLp_ofLp]

theorem l2PiUpdate_mem_l2PiSet {C : ∀ i, Set (E i)} {x : PiLp 2 E}
    (hx : x ∈ l2PiSet C) {i : ι} {y : E i} (hy : y ∈ C i) :
    l2PiUpdate x i y ∈ l2PiSet C := by
  intro j
  rcases eq_or_ne j i with rfl | h
  · rwa [l2PiUpdate_self]
  · rw [l2PiUpdate_of_ne x h]
    exact hx j

end Update

section Coordinates

variable [∀ i, NormedAddCommGroup (E i)]

/-- Coordinate evaluation on the Euclidean `L²` product is continuous. -/
theorem continuous_l2Pi_apply (i : ι) : Continuous fun x : PiLp 2 E ↦ x i :=
  PiLp.continuous_apply 2 E i

/-- Convergence in the finite Euclidean `L²` product is coordinatewise. -/
theorem tendsto_l2Pi_of_forall {α : Type*} {l : Filter α} {f : α → PiLp 2 E}
    {x : PiLp 2 E} (h : ∀ i, Tendsto (fun a ↦ (f a) i) l (nhds (x i))) :
    Tendsto f l (nhds x) := by
  have h1 : Tendsto (fun a ↦ WithLp.ofLp (f a)) l (nhds (WithLp.ofLp x)) :=
    tendsto_pi_nhds.2 h
  have h2 := ((PiLp.continuous_toLp 2 E).tendsto _).comp h1
  simpa [Function.comp_def] using h2

theorem continuous_l2PiUpdate [DecidableEq ι] (x : PiLp 2 E) (i : ι) :
    Continuous fun y : E i ↦ l2PiUpdate x i y := by
  refine (PiLp.continuous_toLp 2 E).comp ?_
  exact continuous_const.update i continuous_id

theorem l2Pi_zero_apply (i : ι) : (0 : PiLp 2 E) i = 0 := rfl

/-- A finite Euclidean `L²` product of closed sets is closed. -/
theorem isClosed_l2PiSet {C : ∀ i, Set (E i)} (hC : ∀ i, IsClosed (C i)) :
    IsClosed (l2PiSet C) := by
  have h : l2PiSet C = ⋂ i, (fun x : PiLp 2 E ↦ x i) ⁻¹' C i := by
    ext x
    simp [l2PiSet]
  rw [h]
  exact isClosed_iInter fun i ↦ (hC i).preimage (continuous_l2Pi_apply i)

variable [Fintype ι]

/-- The Euclidean norm of the finite `L²` product. -/
theorem l2Pi_norm_eq (x : PiLp 2 E) : ‖x‖ = Real.sqrt (∑ i, ‖x i‖ ^ 2) :=
  PiLp.norm_eq_of_L2 x

/-- Each coordinate of a vector of the Euclidean `L²` product is no longer
than the vector. -/
theorem l2Pi_norm_apply_le (x : PiLp 2 E) (i : ι) : ‖x i‖ ≤ ‖x‖ :=
  PiLp.norm_apply_le x i

/-- A single-coordinate variation moves the base point by exactly the
coordinate displacement.  This is where the Euclidean norm, rather than the
sup norm carried by the plain product, is used. -/
theorem norm_l2PiUpdate_sub [DecidableEq ι] (x : PiLp 2 E) (i : ι) (y : E i) :
    ‖l2PiUpdate x i y - x‖ = ‖y - x i‖ := by
  have hzero : ∀ j ∈ Finset.univ, j ≠ i → ‖(l2PiUpdate x i y - x) j‖ ^ 2 = 0 := by
    intro j _ hj
    have h : (l2PiUpdate x i y - x) j = 0 := by
      change (l2PiUpdate x i y) j - x j = 0
      rw [l2PiUpdate_of_ne x hj, sub_self]
    rw [h, norm_zero]
    norm_num
  have hsum : ∑ j, ‖(l2PiUpdate x i y - x) j‖ ^ 2 = ‖(l2PiUpdate x i y - x) i‖ ^ 2 :=
    Finset.sum_eq_single i hzero fun hj ↦ absurd (Finset.mem_univ i) hj
  have hi : (l2PiUpdate x i y - x) i = y - x i := by
    change (l2PiUpdate x i y) i - x i = y - x i
    rw [l2PiUpdate_self]
  rw [l2Pi_norm_eq, hsum, hi, Real.sqrt_sq (norm_nonneg _)]

end Coordinates

section TangentCones

variable [Fintype ι] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- **Proposition 6.41**: a tangent vector to a finite Euclidean product has
tangent coordinate vectors. -/
theorem tangentCone_l2PiSet_subset (C : ∀ i, Set (E i)) (x : PiLp 2 E) :
    tangentCone (l2PiSet C) x ⊆ l2PiSet fun i ↦ tangentCone (C i) (x i) := by
  rintro w ⟨zs, τs, hzC, -, hτpos, hτ0, hq⟩ i
  refine mem_tangentCone_of_forall (xs := fun n ↦ (zs n) i) (hτ := hτpos)
    (hτ0 := hτ0) (fun n ↦ hzC n i) ?_
  exact ((continuous_l2Pi_apply i).tendsto w).comp hq

/-- **Proposition 6.41**: derivable tangent vectors commute with finite
Euclidean products.  The combined path follows each factor's own path while
the parameter stays inside that factor's interval and rests at the base point
afterwards; near `0` no switch has yet happened in any of the finitely many
coordinates. -/
theorem derivableCone_l2PiSet (C : ∀ i, Set (E i)) (x : PiLp 2 E) :
    derivableCone (l2PiSet C) x = l2PiSet fun i ↦ derivableCone (C i) (x i) := by
  ext w
  constructor
  · rintro ⟨ε, hε, ξ, hξ0, hξC, hξt⟩ i
    refine ⟨ε, hε, fun t ↦ (ξ t) i, congrArg (fun z : PiLp 2 E ↦ z i) hξ0,
      fun t ht ↦ hξC t ht i, ?_⟩
    exact ((continuous_l2Pi_apply i).tendsto w).comp hξt
  · intro hw
    choose ε hε ξ hξ0 hξC hξt using hw
    have hxC : ∀ i, x i ∈ C i := by
      intro i
      have h0 := hξC i 0 ⟨le_rfl, (hε i).le⟩
      rwa [hξ0 i] at h0
    refine ⟨1, one_pos,
      fun t ↦ WithLp.toLp 2 (fun i ↦ if t ≤ ε i then ξ i t else x i), ?_, ?_, ?_⟩
    · have hfun : (fun i ↦ if (0 : ℝ) ≤ ε i then ξ i 0 else x i) = WithLp.ofLp x := by
        funext i
        rw [if_pos (hε i).le, hξ0 i]
      change WithLp.toLp 2 (fun i ↦ if (0 : ℝ) ≤ ε i then ξ i 0 else x i) = x
      rw [hfun, WithLp.toLp_ofLp]
    · intro t ht i
      change (if t ≤ ε i then ξ i t else x i) ∈ C i
      by_cases hti : t ≤ ε i
      · rw [if_pos hti]
        exact hξC i t ⟨ht.1, hti⟩
      · rw [if_neg hti]
        exact hxC i
    · refine tendsto_l2Pi_of_forall fun i ↦ ?_
      have heq : (fun t : ℝ ↦ t⁻¹ • (ξ i t - x i)) =ᶠ[nhdsWithin 0 (Ioi (0 : ℝ))]
          fun t : ℝ ↦
            (t⁻¹ • (WithLp.toLp 2 (fun j ↦ if t ≤ ε j then ξ j t else x j) - x)) i := by
        filter_upwards [Ioo_mem_nhdsGT (hε i)] with t ht
        change t⁻¹ • (ξ i t - x i) = t⁻¹ • ((if t ≤ ε i then ξ i t else x i) - x i)
        rw [if_pos ht.2.le]
      exact (hξt i).congr' heq

end TangentCones

section NormalCones

variable [Fintype ι] [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

/-- The inner product of the finite `L²` product is the coordinate sum. -/
theorem l2Pi_inner_apply (x y : PiLp 2 E) : ⟪x, y⟫_ℝ = ∑ i, ⟪x i, y i⟫_ℝ :=
  PiLp.inner_apply x y

/-- Pairing against a single-coordinate variation sees only that
coordinate. -/
theorem inner_l2PiUpdate_sub [DecidableEq ι] (v x : PiLp 2 E) (i : ι) (y : E i) :
    ⟪v, l2PiUpdate x i y - x⟫_ℝ = ⟪v i, y - x i⟫_ℝ := by
  have hzero : ∀ j ∈ Finset.univ, j ≠ i → ⟪v j, (l2PiUpdate x i y - x) j⟫_ℝ = 0 := by
    intro j _ hj
    have h : (l2PiUpdate x i y - x) j = 0 := by
      change (l2PiUpdate x i y) j - x j = 0
      rw [l2PiUpdate_of_ne x hj, sub_self]
    rw [h, inner_zero_right]
  have hsum : ∑ j, ⟪v j, (l2PiUpdate x i y - x) j⟫_ℝ
      = ⟪v i, (l2PiUpdate x i y - x) i⟫_ℝ :=
    Finset.sum_eq_single i hzero fun hj ↦ absurd (Finset.mem_univ i) hj
  have hi : (l2PiUpdate x i y - x) i = y - x i := by
    change (l2PiUpdate x i y) i - x i = y - x i
    rw [l2PiUpdate_self]
  rw [l2Pi_inner_apply, hsum, hi]

theorem inner_l2PiUpdate_zero [DecidableEq ι] (v : PiLp 2 E) (i : ι) (u : E i) :
    ⟪v, l2PiUpdate (0 : PiLp 2 E) i u⟫_ℝ = ⟪v i, u⟫_ℝ := by
  have h := inner_l2PiUpdate_sub v (0 : PiLp 2 E) i u
  rwa [sub_zero, l2Pi_zero_apply, sub_zero] at h

/-- **Proposition 6.41**: regular normal cones commute with finite Euclidean
products.  The reverse estimate distributes `ε` over the finitely many
coordinates, each coordinate displacement being dominated by the `L²`
displacement; the filter form of 6(5) makes the empty index type
unexceptional. -/
theorem regularNormalCone_l2PiSet (C : ∀ i, Set (E i)) (x : PiLp 2 E) :
    regularNormalCone (l2PiSet C) x =
      l2PiSet fun i ↦ regularNormalCone (C i) (x i) := by
  classical
  ext v
  constructor
  · rw [mem_regularNormalCone_iff]
    rintro ⟨hx, hv⟩ i
    rw [mem_regularNormalCone_iff]
    refine ⟨hx i, fun ε hε ↦ ?_⟩
    obtain ⟨δ, hδ, hvδ⟩ := hv ε hε
    refine ⟨δ, hδ, fun y hy hyd ↦ ?_⟩
    have hmem : l2PiUpdate x i y ∈ l2PiSet C := l2PiUpdate_mem_l2PiSet hx hy
    have hnorm : ‖l2PiUpdate x i y - x‖ = ‖y - x i‖ := norm_l2PiUpdate_sub x i y
    have h := hvδ (l2PiUpdate x i y) hmem (by rw [hnorm]; exact hyd)
    rwa [inner_l2PiUpdate_sub, hnorm] at h
  · intro hv
    have hx : x ∈ l2PiSet C := fun i ↦ (hv i).1
    refine ⟨hx, fun ε hε ↦ ?_⟩
    have hm0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    have hε' : (0 : ℝ) < ε / ((Fintype.card ι : ℝ) + 1) := by positivity
    have hcoord : ∀ i, ∀ᶠ z in nhdsWithin x (l2PiSet C),
        ⟪v i, z i - x i⟫_ℝ ≤ ε / ((Fintype.card ι : ℝ) + 1) * ‖z i - x i‖ := by
      intro i
      have hto : Tendsto (fun z : PiLp 2 E ↦ z i) (nhdsWithin x (l2PiSet C))
          (nhdsWithin (x i) (C i)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (((continuous_l2Pi_apply i).tendsto x).mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin] with z hz using hz i
      exact hto ((hv i).2 (ε / ((Fintype.card ι : ℝ) + 1)) hε')
    filter_upwards [eventually_all.2 hcoord] with z hz
    have hnn : (0 : ℝ) ≤ ‖z - x‖ := norm_nonneg _
    have hstep : ∀ i, ⟪v i, z i - x i⟫_ℝ ≤
        ε / ((Fintype.card ι : ℝ) + 1) * ‖z - x‖ := by
      intro i
      refine (hz i).trans (mul_le_mul_of_nonneg_left ?_ hε'.le)
      exact l2Pi_norm_apply_le (z - x) i
    calc
      ⟪v, z - x⟫_ℝ = ∑ i, ⟪v i, z i - x i⟫_ℝ := l2Pi_inner_apply v (z - x)
      _ ≤ ∑ _i : ι, ε / ((Fintype.card ι : ℝ) + 1) * ‖z - x‖ :=
        Finset.sum_le_sum fun i _ ↦ hstep i
      _ = (Fintype.card ι : ℝ) * (ε / ((Fintype.card ι : ℝ) + 1) * ‖z - x‖) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ε * ‖z - x‖ := by
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ hnn
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [hε.le]

/-- **Proposition 6.41**: limiting normal cones commute with finite Euclidean
products.  The reverse inclusion zips the finitely many witness sequences term
by term, so a single sequence of product points serves every coordinate. -/
theorem normalCone_l2PiSet (C : ∀ i, Set (E i)) (x : PiLp 2 E) :
    normalCone (l2PiSet C) x = l2PiSet fun i ↦ normalCone (C i) (x i) := by
  ext v
  constructor
  · rintro ⟨hx, zs, vs, -, hzto, hvs, hvto⟩ i
    refine mem_normalCone_of_forall (hx i) (xs := fun n ↦ (zs n) i)
      (vs := fun n ↦ (vs n) i) (((continuous_l2Pi_apply i).tendsto x).comp hzto)
      (fun n ↦ ?_) (((continuous_l2Pi_apply i).tendsto v).comp hvto)
    have h := hvs n
    rw [regularNormalCone_l2PiSet C (zs n)] at h
    exact h i
  · intro hv
    have hx : x ∈ l2PiSet C := fun i ↦ (hv i).1
    have hpick : ∀ i, ∃ zs ws : ℕ → E i, Tendsto zs atTop (nhds (x i)) ∧
        (∀ n, ws n ∈ regularNormalCone (C i) (zs n)) ∧
        Tendsto ws atTop (nhds (v i)) := by
      intro i
      obtain ⟨-, zs, ws, -, hzto, hws, hwto⟩ := hv i
      exact ⟨zs, ws, hzto, hws, hwto⟩
    choose zs ws hzto hws hwto using hpick
    refine mem_normalCone_of_forall hx
      (xs := fun n ↦ WithLp.toLp 2 fun i ↦ zs i n)
      (vs := fun n ↦ WithLp.toLp 2 fun i ↦ ws i n)
      (tendsto_l2Pi_of_forall fun i ↦ hzto i) (fun n ↦ ?_)
      (tendsto_l2Pi_of_forall fun i ↦ hwto i)
    rw [regularNormalCone_l2PiSet C]
    exact fun i ↦ hws i n

/-- Polarity commutes with finite Euclidean products of cones. -/
theorem polarCone_l2PiSet {K : ∀ i, Set (E i)} (hK : ∀ i, (0 : E i) ∈ K i) :
    polarCone (l2PiSet K) = l2PiSet fun i ↦ polarCone (K i) := by
  classical
  ext v
  constructor
  · intro hv i u hu
    have hmem : l2PiUpdate (0 : PiLp 2 E) i u ∈ l2PiSet K := by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · rwa [l2PiUpdate_self]
      · rw [l2PiUpdate_of_ne _ hj, l2Pi_zero_apply]
        exact hK j
    have h := hv _ hmem
    rwa [inner_l2PiUpdate_zero] at h
  · intro hv z hz
    rw [l2Pi_inner_apply]
    exact Finset.sum_nonpos fun i _ ↦ hv i (z i) (hz i)

end NormalCones

section RegularTangentCones

variable [Fintype ι] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- **Proposition 6.41**: regular tangent cones commute with finite Euclidean
products.  Both halves are read off Definition 6.25 in its exact sequential
form: forward, an arbitrary base sequence of one factor is extended to the
product by freezing the other coordinates; backward, the finitely many
selections are made against the *same* base sequence and the *same* scales and
zipped into one. -/
theorem regularTangentCone_l2PiSet {C : ∀ i, Set (E i)} {x : PiLp 2 E}
    (hx : x ∈ l2PiSet C) :
    regularTangentCone (l2PiSet C) x =
      l2PiSet fun i ↦ regularTangentCone (C i) (x i) := by
  classical
  ext w
  constructor
  · intro hw i
    rw [mem_regularTangentCone_iff_forall_sequences (hx i)]
    intro τs ybars hτpos hτ0 hybarC hybarto
    have hbaseC : ∀ n, l2PiUpdate x i (ybars n) ∈ l2PiSet C :=
      fun n ↦ l2PiUpdate_mem_l2PiSet hx (hybarC n)
    have hbaseto : Tendsto (fun n ↦ l2PiUpdate x i (ybars n)) atTop (nhds x) := by
      have h := ((continuous_l2PiUpdate x i).tendsto (x i)).comp hybarto
      rwa [l2PiUpdate_apply] at h
    obtain ⟨zs, hzsC, hzsto, hq⟩ :=
      (mem_regularTangentCone_iff_forall_sequences hx).1 hw τs
        (fun n ↦ l2PiUpdate x i (ybars n)) hτpos hτ0 hbaseC hbaseto
    refine ⟨fun n ↦ (zs n) i, fun n ↦ hzsC n i,
      ((continuous_l2Pi_apply i).tendsto x).comp hzsto, ?_⟩
    have h := ((continuous_l2Pi_apply i).tendsto w).comp hq
    refine h.congr fun n ↦ ?_
    change (τs n)⁻¹ • ((zs n) i - (l2PiUpdate x i (ybars n)) i)
      = (τs n)⁻¹ • ((zs n) i - ybars n)
    rw [l2PiUpdate_self]
  · intro hw
    rw [mem_regularTangentCone_iff_forall_sequences hx]
    intro τs xbars hτpos hτ0 hxbarC hxbarto
    have hpick : ∀ i, ∃ zs : ℕ → E i, (∀ n, zs n ∈ C i) ∧
        Tendsto zs atTop (nhds (x i)) ∧
        Tendsto (fun n ↦ (τs n)⁻¹ • (zs n - (xbars n) i)) atTop (nhds (w i)) := by
      intro i
      exact (mem_regularTangentCone_iff_forall_sequences (hx i)).1 (hw i) τs
        (fun n ↦ (xbars n) i) hτpos hτ0 (fun n ↦ hxbarC n i)
        (((continuous_l2Pi_apply i).tendsto x).comp hxbarto)
    choose zs hzsC hzsto hq using hpick
    exact ⟨fun n ↦ WithLp.toLp 2 fun i ↦ zs i n, fun n i ↦ hzsC i n,
      tendsto_l2Pi_of_forall fun i ↦ hzsto i, tendsto_l2Pi_of_forall fun i ↦ hq i⟩

end RegularTangentCones

section ClarkeRegularity

variable [Fintype ι] [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

/-- **Proposition 6.41**: a finite Euclidean product of closed sets is Clarke
regular at a feasible point exactly when every factor is regular at its
coordinate. -/
theorem isClarkeRegularAt_l2PiSet_iff {C : ∀ i, Set (E i)} {x : PiLp 2 E}
    (hC : ∀ i, IsClosed (C i)) (hx : x ∈ l2PiSet C) :
    IsClarkeRegularAt (l2PiSet C) x ↔ ∀ i, IsClarkeRegularAt (C i) (x i) := by
  classical
  constructor
  · intro hp i
    refine ⟨IsClosed.isLocallyClosedAt (hC i) (x i), Subset.antisymm ?_
      (regularNormalCone_subset_normalCone (C i) (x i))⟩
    intro v hv
    have hzero : ∀ j, (l2PiUpdate (0 : PiLp 2 E) i v) j ∈ normalCone (C j) (x j) := by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · rwa [l2PiUpdate_self]
      · rw [l2PiUpdate_of_ne _ hj, l2Pi_zero_apply]
        exact regularNormalCone_subset_normalCone (C j) (x j)
          (isCone_regularNormalCone (hx j)).1
    have hmemN : l2PiUpdate (0 : PiLp 2 E) i v ∈ normalCone (l2PiSet C) x := by
      rw [normalCone_l2PiSet]
      exact hzero
    have hmemR : l2PiUpdate (0 : PiLp 2 E) i v ∈ regularNormalCone (l2PiSet C) x := by
      rw [← hp.2]
      exact hmemN
    rw [regularNormalCone_l2PiSet] at hmemR
    have h := hmemR i
    rwa [l2PiUpdate_self] at h
  · intro h
    refine ⟨IsClosed.isLocallyClosedAt (isClosed_l2PiSet hC) x, ?_⟩
    rw [normalCone_l2PiSet, regularNormalCone_l2PiSet]
    ext v
    simp only [mem_l2PiSet]
    exact forall_congr' fun i ↦ by rw [(h i).2]

end ClarkeRegularity

section RegularCase

variable [Fintype ι] [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]

/-- **Proposition 6.41**, final clause: in the regular case the inclusion for
the ordinary tangent cone becomes an equation.  Only Clarke regularity of the
factors is assumed, as printed; geometric derivability is *not* assumed.  The
route is the regular tangent cone: `T̂` commutes with the product, and at a
point of Clarke regularity `T = T̂` in each factor. -/
theorem tangentCone_l2PiSet_of_isClarkeRegularAt {C : ∀ i, Set (E i)}
    {x : PiLp 2 E} (hx : x ∈ l2PiSet C)
    (hreg : ∀ i, IsClarkeRegularAt (C i) (x i)) :
    tangentCone (l2PiSet C) x = l2PiSet fun i ↦ tangentCone (C i) (x i) := by
  refine Subset.antisymm (tangentCone_l2PiSet_subset C x) ?_
  intro w hw
  have hwreg : w ∈ regularTangentCone (l2PiSet C) x := by
    rw [regularTangentCone_l2PiSet hx]
    intro i
    change w i ∈ regularTangentCone (C i) (x i)
    rw [← tangentCone_eq_regularTangentCone_of_isClarkeRegularAt (hx i) (hreg i)]
    exact hw i
  exact regularTangentCone_subset_tangentCone hx hwreg

/-- The closure of the unnumbered display after the example following 6.41:
the closed convex conic hulls of the tangent cones always multiply, regularity
or not.  This is the polar of the regular-normal formula; the display as
printed, without closures, is not proved here. -/
theorem closure_conicHull_tangentCone_l2PiSet {C : ∀ i, Set (E i)} {x : PiLp 2 E}
    (hx : x ∈ l2PiSet C) :
    closure (conicHull (tangentCone (l2PiSet C) x)) =
      l2PiSet fun i ↦ closure (conicHull (tangentCone (C i) (x i))) := by
  rw [closure_conicHull_tangentCone hx, regularNormalCone_l2PiSet,
    polarCone_l2PiSet fun i ↦ (isCone_regularNormalCone (hx i)).1]
  congr 1
  funext i
  exact (closure_conicHull_tangentCone (hx i)).symm

end RegularCase

end FiniteProducts

end RW
