/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Domains and ranges of maximal monotone mappings

Theorem 12.37, Corollaries 12.38 and 12.39 and Theorem 12.41.

The book obtains the convexity of `D = cl(dom T)` in 12.37 from a graphical
cluster point of `λT` as `λ ↘ 0`.  Here everything is read off the resolvents
`Pλ = (I + λT)⁻¹` directly.  For `b ∈ T(a)` the monotonicity inequality at the
graph point `(Pλ z, λ⁻¹(z - Pλ z))` reads `λ⟪b, Pλ z - a⟫ ≤ ⟪z - Pλ z, Pλ z - a⟫`,
and `Pλ z` stays bounded as `λ ↘ 0`.  Every cluster point `y` of `Pλ z` therefore
lies in `D` and satisfies `⟪z - y, a - y⟫ ≤ 0` for all `a ∈ dom T`.  For `z` in
the closed convex hull of `dom T` this forces `y = z`, so the closed convex
hull of `dom T` lies in `D` and `D` is convex.  For general `z` it identifies
`y` as the projection `P_D z`, so `Pλ → P_D`, uniformly on bounded sets
because the resolvents are nonexpansive.  Graphical convergence `λT → N_D`
then follows from the resolvents as in 12.32 (inner limit) and from a direct
continuity argument with the monotonicity inequality (outer limit).

Local boundedness (12.38) and near convexity (12.41) both rest on one
observation: if `vν ∈ T(xν)` with `xν → x̄` and `|vν| → ∞`, every cluster point
`u` of `vν/|vν|` satisfies `⟪u, a - x̄⟫ ≤ 0` for all `a ∈ dom T`.  For 12.41 the
vectors `vν = λν⁻¹(z - Pλν z)` lie in the subspace parallel to `aff D`, so at a
point `z ∈ rint D` the limit `u` would be orthogonal to that subspace while
lying in it.  This replaces the book's reduction to the full-dimensional case
by a change of coordinates.
-/

import RockafellarWets.Chapter12.MonotoneGraphicalConvergence
import RockafellarWets.Chapter12.ConvexSubgradientMappings
import RockafellarWets.Chapter6.BoundaryNormals
import RockafellarWets.Chapter6.RelativeInteriorQualification
import RockafellarWets.Chapter5.HorizonSetLimitsAlong
import RockafellarWets.Chapter3.HorizonCones

open Bornology Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

section Uniform

variable {ι X Y : Type*} [PseudoMetricSpace X] [ProperSpace X] [PseudoMetricSpace Y]

/-- Pointwise convergence of eventually equi-Lipschitz maps to a Lipschitz
map is uniform on bounded subsets of a proper space. -/
theorem tendstoUniformlyOn_of_lipschitzWith {l : Filter ι} {G : ι → X → Y} {g : X → Y}
    {K : NNReal} (hG : ∀ᶠ i in l, LipschitzWith K (G i)) (hg : LipschitzWith K g)
    (h : ∀ z, Tendsto (fun i ↦ G i z) l (𝓝 (g z))) {B : Set X} (hB : IsBounded B) :
    TendstoUniformlyOn G g l B := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := ε / (3 * ((K : ℝ) + 1)) with hδ
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hδpos : 0 < δ := by positivity
  obtain ⟨t, -, ht, hcover⟩ := finite_cover_balls_of_compact hB.isCompact_closure hδpos
  have hall : ∀ᶠ i in l, ∀ c ∈ t, dist (g c) (G i c) < ε / 3 := by
    refine (ht.eventually_all).2 fun c _ ↦ ?_
    filter_upwards [Metric.tendsto_nhds.1 (h c) (ε / 3) (by positivity)] with i hi
    rwa [dist_comm]
  have hKδ : (K : ℝ) * δ < ε / 3 := by
    have e : (K : ℝ) * δ = ε / 3 * ((K : ℝ) / ((K : ℝ) + 1)) := by
      rw [hδ]
      field_simp
    rw [e]
    have hlt : (K : ℝ) / ((K : ℝ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have hε3 : 0 < ε / 3 := by positivity
    nlinarith
  filter_upwards [hG, hall] with i hGi hi z hz
  obtain ⟨c, hct, hzc⟩ : ∃ c ∈ t, z ∈ ball c δ := by
    simpa only [mem_iUnion, exists_prop] using hcover (subset_closure hz)
  rw [mem_ball] at hzc
  have h1 : dist (g z) (g c) ≤ K * dist z c := hg.dist_le_mul z c
  have h2 : dist (G i c) (G i z) ≤ K * dist c z := hGi.dist_le_mul c z
  have h3 := hi c hct
  rw [dist_comm c z] at h2
  have h4 : (K : ℝ) * dist z c ≤ K * δ := mul_le_mul_of_nonneg_left hzc.le hK0
  calc dist (g z) (G i z) ≤ dist (g z) (g c) + dist (g c) (G i c) + dist (G i c) (G i z) :=
        dist_triangle4 _ _ _ _
    _ < ε := by linarith

end Uniform

section Sequences

variable {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]

/-- Failure of local boundedness at `x` produces graph points `(xν, vν)` with
`xν → x` and `|vν| → ∞`. -/
theorem exists_seq_of_not_svLocallyBoundedAt {S : X → Set Y} {x : X}
    (h : ¬ SvLocallyBoundedAt S x) :
    ∃ (xs : ℕ → X) (vs : ℕ → Y), (∀ n, vs n ∈ S (xs n)) ∧ Tendsto xs atTop (𝓝 x) ∧
      Tendsto (fun n ↦ ‖vs n‖) atTop atTop := by
  have hpick : ∀ n : ℕ, ∃ y ∈ ball x (1 / ((n : ℝ) + 1)), ∃ w ∈ S y, (n : ℝ) < ‖w‖ := by
    intro n
    have hnb : ¬ IsBounded (svImage S (ball x (1 / ((n : ℝ) + 1)))) := fun hb ↦
      h ⟨_, ball_mem_nhds x (by positivity), hb⟩
    rw [isBounded_iff_forall_norm_le] at hnb
    push_neg at hnb
    obtain ⟨w, hw, hwn⟩ := hnb n
    obtain ⟨y, hy, hwy⟩ := mem_svImage.1 hw
    exact ⟨y, hy, w, hwy, hwn⟩
  choose xs hxs vs hvs hvn using hpick
  refine ⟨xs, vs, hvs, ?_, ?_⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (mem_ball.1 (hxs n)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · exact tendsto_atTop_mono (fun n ↦ (hvn n).le) tendsto_natCast_atTop_atTop

end Sequences

section Normalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A sequence of vectors whose norms tend to infinity has a subsequence whose
normalizations converge to a unit vector. -/
theorem exists_subseq_tendsto_normalize [FiniteDimensional ℝ E] {v : ℕ → E}
    (hv : Tendsto (fun n ↦ ‖v n‖) atTop atTop) :
    ∃ (φ : ℕ → ℕ) (u : E), StrictMono φ ∧ ‖u‖ = 1 ∧
      Tendsto (fun n ↦ ‖v (φ n)‖⁻¹ • v (φ n)) atTop (𝓝 u) := by
  have hb : ∀ n, ‖v n‖⁻¹ • v n ∈ closedBall (0 : E) 1 := by
    intro n
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm]
    rcases (norm_nonneg (v n)).eq_or_lt with h | h
    · rw [← h]
      simp
    · rw [inv_mul_cancel₀ h.ne']
  obtain ⟨u, -, φ, hφ, hu⟩ := tendsto_subseq_of_bounded isBounded_closedBall hb
  refine ⟨φ, u, hφ, ?_, hu⟩
  have hone : ∀ᶠ n in atTop, ‖‖v (φ n)‖⁻¹ • v (φ n)‖ = 1 := by
    filter_upwards [(hv.comp hφ.tendsto_atTop).eventually_gt_atTop 0] with n hn
    have hn' : ‖v (φ n)‖ ≠ 0 := hn.ne'
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn']
  exact tendsto_nhds_unique (hu.norm) (tendsto_const_nhds.congr' (hone.mono fun n hn ↦ hn.symm))

/-- The key estimate behind 12.38, 12.40 and 12.41: if `⟪vν - bν, xν - aν⟫ ≥ 0`
with `xν → x̄`, `aν → ā`, `bν → b̄`, `|vν| → ∞` and `vν/|vν| → u`, then
`⟪u, ā - x̄⟫ ≤ 0`. -/
theorem inner_nonpos_of_inner_sub_nonneg {x v a b : ℕ → E} {xbar abar bbar u : E}
    (hmono : ∀ᶠ n in atTop, 0 ≤ ⟪v n - b n, x n - a n⟫_ℝ)
    (hx : Tendsto x atTop (𝓝 xbar)) (ha : Tendsto a atTop (𝓝 abar))
    (hb : Tendsto b atTop (𝓝 bbar)) (hnorm : Tendsto (fun n ↦ ‖v n‖) atTop atTop)
    (hu : Tendsto (fun n ↦ ‖v n‖⁻¹ • v n) atTop (𝓝 u)) : ⟪u, abar - xbar⟫_ℝ ≤ 0 := by
  have hc : Tendsto (fun n ↦ ‖v n‖⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hnorm
  have hlim : Tendsto (fun n ↦ ⟪‖v n‖⁻¹ • v n - ‖v n‖⁻¹ • b n, x n - a n⟫_ℝ) atTop
      (𝓝 ⟪u - (0 : ℝ) • bbar, xbar - abar⟫_ℝ) :=
    (hu.sub (hc.smul hb)).inner (hx.sub ha)
  rw [zero_smul, sub_zero] at hlim
  have hge : 0 ≤ ⟪u, xbar - abar⟫_ℝ := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [hmono] with n hn
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) hn
  rw [← neg_sub xbar abar, inner_neg_right]
  linarith

end Normalization

section RelativeInterior

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The relative interior through balls: `z ∈ rint s` exactly when `z ∈ s` and
some ball around `z` meets the affine hull of `s` only inside `s`. -/
theorem mem_intrinsicInterior_iff_ball {s : Set V} {z : V} :
    z ∈ intrinsicInterior ℝ s ↔
      z ∈ s ∧ ∃ r > 0, ∀ y ∈ affineSpan ℝ s, dist y z < r → y ∈ s := by
  constructor
  · intro hz
    obtain ⟨p, hp, rfl⟩ := mem_intrinsicInterior.1 hz
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hp)
    refine ⟨(interior_subset hp : p ∈ ((↑) ⁻¹' s : Set (affineSpan ℝ s))), r, hr,
      fun y hy hyz ↦ ?_⟩
    have hmem : (⟨y, hy⟩ : affineSpan ℝ s) ∈ ball p r := by
      rw [mem_ball, Subtype.dist_eq]
      exact hyz
    exact hball hmem
  · rintro ⟨hz, r, hr, hball⟩
    refine mem_intrinsicInterior.2 ⟨⟨z, subset_affineSpan ℝ s hz⟩, ?_, rfl⟩
    refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨r, hr, fun q hq ↦ ?_⟩)
    rw [mem_ball, Subtype.dist_eq] at hq
    exact hball q q.2 hq

variable [FiniteDimensional ℝ V]

/-- The line segment principle for relative interiors: the half-open segment
from a closure point of a convex set to a relative-interior point lies in the
relative interior. -/
theorem Convex.add_smul_sub_mem_intrinsicInterior {s : Set V} (hs : Convex ℝ s) {x z : V}
    (hx : x ∈ closure s) (hz : z ∈ intrinsicInterior ℝ s) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) : x + t • (z - x) ∈ intrinsicInterior ℝ s := by
  obtain ⟨hzs, r, hr, hball⟩ := mem_intrinsicInterior_iff_ball.1 hz
  obtain ⟨x', hx's, hxx'⟩ := Metric.mem_closure_iff.1 hx (t * r / 2) (by positivity)
  have key : ∀ y ∈ affineSpan ℝ s, dist y (x + t • (z - x)) < t * r / 2 → y ∈ s := by
    intro y hy hyw
    set z' : V := x' + t⁻¹ • (y - x') with hz'
    have hz'A : z' ∈ affineSpan ℝ s := by
      have h := AffineMap.lineMap_mem t⁻¹ (subset_affineSpan ℝ s hx's) hy
      rwa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] at h
    have e : t • (z' - z) = (y - (x + t • (z - x))) + (1 - t) • (x - x') := by
      rw [hz', smul_sub, smul_add, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
      module
    have hz'z : dist z' z < r := by
      have hn : t * ‖z' - z‖ ≤ ‖y - (x + t • (z - x))‖ + (1 - t) * ‖x - x'‖ := by
        calc t * ‖z' - z‖ = ‖t • (z' - z)‖ := by
              rw [norm_smul, Real.norm_of_nonneg ht0.le]
          _ ≤ ‖y - (x + t • (z - x))‖ + ‖(1 - t) • (x - x')‖ := by
              rw [e]
              exact norm_add_le _ _
          _ = ‖y - (x + t • (z - x))‖ + (1 - t) * ‖x - x'‖ := by
              rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      have h1 : ‖y - (x + t • (z - x))‖ < t * r / 2 := by rwa [← dist_eq_norm]
      have h2 : (1 - t) * ‖x - x'‖ ≤ t * r / 2 := by
        have : ‖x - x'‖ < t * r / 2 := by rwa [← dist_eq_norm]
        have h1t : 0 ≤ 1 - t := by linarith
        nlinarith [norm_nonneg (x - x')]
      rw [dist_eq_norm]
      by_contra hcon
      push_neg at hcon
      nlinarith
    have hz's : z' ∈ s := hball z' hz'A hz'z
    have hy_eq : y = x' + t • (z' - x') := by
      rw [hz', add_sub_cancel_left, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul,
        add_sub_cancel]
    rw [hy_eq]
    exact hs.add_smul_sub_mem hx's hz's ⟨ht0.le, ht1⟩
  have hxA : x ∈ affineSpan ℝ s :=
    closure_minimal (subset_affineSpan ℝ s) (AffineSubspace.closed_of_finiteDimensional _) hx
  have hwA : x + t • (z - x) ∈ affineSpan ℝ s := by
    have h := AffineMap.lineMap_mem t hxA (subset_affineSpan ℝ s hzs)
    rwa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm] at h
  refine mem_intrinsicInterior_iff_ball.2
    ⟨key _ hwA (by rw [dist_self]; positivity), t * r / 2, by positivity, key⟩

/-- A convex set lies in the closure of its relative interior (2.40). -/
theorem Convex.subset_closure_intrinsicInterior {s : Set V} (hs : Convex ℝ s) :
    s ⊆ closure (intrinsicInterior ℝ s) := by
  intro x hx
  obtain ⟨z, hz⟩ := Set.Nonempty.intrinsicInterior hs ⟨x, hx⟩
  have ht : Tendsto (fun t : ℝ ↦ x + t • (z - x)) (𝓝[>] 0) (𝓝 x) := by
    have h : Tendsto (fun t : ℝ ↦ x + t • (z - x)) (𝓝 0) (𝓝 (x + (0 : ℝ) • (z - x))) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  have h1 : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))
  filter_upwards [h1, eventually_mem_nhdsWithin] with t ht1 ht0
  exact Convex.add_smul_sub_mem_intrinsicInterior hs (subset_closure hx) hz ht0 ht1.le

/-- The relative interior of a convex set is convex. -/
theorem Convex.convex_intrinsicInterior {s : Set V} (hs : Convex ℝ s) :
    Convex ℝ (intrinsicInterior ℝ s) := by
  intro x hx z hz a b ha hb hab
  rcases hb.eq_or_lt with rfl | hb'
  · rw [add_zero] at hab
    rw [hab, one_smul, zero_smul, add_zero]
    exact hx
  · obtain rfl : a = 1 - b := by linarith
    have h := Convex.add_smul_sub_mem_intrinsicInterior hs
      (subset_closure (intrinsicInterior_subset hx)) hz hb' (by linarith)
    convert h using 1
    module

/-- In finite dimensions a set and its closure have the same affine hull. -/
theorem affineSpan_closure (s : Set V) : affineSpan ℝ (closure s) = affineSpan ℝ s :=
  le_antisymm
    (affineSpan_le.2 (closure_minimal (subset_affineSpan ℝ s)
      (AffineSubspace.closed_of_finiteDimensional _)))
    (affineSpan_mono ℝ subset_closure)

end RelativeInterior

section Domains

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A maximal monotone mapping has a nonempty domain. -/
theorem SvMaximalMonotone.svDom_nonempty {T : E → Set E} (hT : SvMaximalMonotone T) :
    (svDom T).Nonempty := by
  by_cases h : (0 : E) ∈ T 0
  · exact ⟨0, 0, h⟩
  · obtain ⟨x, v, hv, -⟩ := hT.2 0 0 h
    exact ⟨x, v, hv⟩

/-- An outer semicontinuous mapping that is locally bounded at a point of the
closure of its domain is nonempty there. -/
theorem mem_svDom_of_mem_closure {T : E → Set E} (hT : IsClosed (svGraph T)) {x : E}
    (hx : x ∈ closure (svDom T)) (hlb : SvLocallyBoundedAt T x) : x ∈ svDom T := by
  obtain ⟨V, hV, hbdd⟩ := hlb
  obtain ⟨xs, hxs, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  choose vs hvs using hxs
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : E)
  have hev : ∀ᶠ n in atTop, vs n ∈ closedBall (0 : E) R :=
    (hlim.eventually hV).mono fun n hn ↦ hR (mem_svImage.2 ⟨xs n, hn, hvs n⟩)
  obtain ⟨v, -, φ, hφ, hv⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall
    hev.frequently
  exact ⟨v, hT.mem_of_tendsto ((hlim.comp hφ.tendsto_atTop).prodMk_nhds hv)
    (Eventually.of_forall fun n ↦ hvs (φ n))⟩

/-- The graph point `(Pλ z, λ⁻¹(z - Pλ z))` places the resolvent in the domain. -/
theorem SvMaximalMonotone.resolventMap_mem_svDom {T : E → Set E} (hT : SvMaximalMonotone T)
    {lam : ℝ} (hlam : 0 < lam) (z : E) : resolventMap T lam z ∈ svDom T :=
  ⟨_, hT.inv_smul_sub_resolventMap_mem hlam z⟩

/-- The monotonicity inequality at the resolvent point `x = (I + λT)⁻¹ z`:
`λ⟪b, x - a⟫ ≤ ⟪z - x, x - a⟫` for every `b ∈ T(a)`. -/
theorem SvMaximalMonotone.mul_inner_le_inner_resolventMap {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) (z : E) {a b : E} (hb : b ∈ T a) :
    lam * ⟪b, resolventMap T lam z - a⟫_ℝ ≤
      ⟪z - resolventMap T lam z, resolventMap T lam z - a⟫_ℝ := by
  have h := hT.1 hb (hT.inv_smul_sub_resolventMap_mem hlam z)
  rw [inner_sub_left, real_inner_smul_left] at h
  have h' := mul_le_mul_of_nonneg_left h hlam.le
  rw [mul_zero, mul_sub, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at h'
  linarith

/-- The resolvent moves `z` by at most `|z - a| + λ|b|` from any graph point `(a, b)`. -/
theorem SvMaximalMonotone.norm_resolventMap_sub_le {T : E → Set E} (hT : SvMaximalMonotone T)
    {lam : ℝ} (hlam : 0 < lam) (z : E) {a b : E} (hb : b ∈ T a) :
    ‖resolventMap T lam z - a‖ ≤ ‖z - a‖ + lam * ‖b‖ := by
  have hres := hT.resolventMap_add_smul hlam hb
  have hlip := (hT.lipschitzWith_resolventMap hlam).norm_sub_le z (a + lam • b)
  rw [hres, NNReal.coe_one, one_mul] at hlip
  calc ‖resolventMap T lam z - a‖ ≤ ‖z - (a + lam • b)‖ := hlip
    _ = ‖(z - a) - lam • b‖ := by rw [sub_add_eq_sub_sub]
    _ ≤ ‖z - a‖ + ‖lam • b‖ := norm_sub_le _ _
    _ = ‖z - a‖ + lam * ‖b‖ := by rw [norm_smul, Real.norm_of_nonneg hlam.le]

/-- The resolvents `Pλ z` stay bounded for `0 < λ ≤ 1`. -/
theorem SvMaximalMonotone.exists_bound_resolventMap {T : E → Set E} (hT : SvMaximalMonotone T)
    (z : E) : ∃ R, ∀ lam : ℝ, 0 < lam → lam ≤ 1 → resolventMap T lam z ∈ closedBall (0 : E) R := by
  obtain ⟨a, b, hb⟩ := hT.svDom_nonempty
  refine ⟨‖a‖ + ‖z - a‖ + ‖b‖, fun lam hlam hlam1 ↦ ?_⟩
  rw [mem_closedBall_zero_iff]
  have h := hT.norm_resolventMap_sub_le hlam z hb
  have hb' : lam * ‖b‖ ≤ ‖b‖ := by nlinarith [norm_nonneg b]
  calc ‖resolventMap T lam z‖ = ‖(resolventMap T lam z - a) + a‖ := by rw [sub_add_cancel]
    _ ≤ ‖resolventMap T lam z - a‖ + ‖a‖ := norm_add_le _ _
    _ ≤ ‖a‖ + ‖z - a‖ + ‖b‖ := by linarith

/-- Limits of resolvents as `λ ↘ 0`: if `(I + λν T)⁻¹ z → y`, then `y ∈ cl(dom T)`
and `⟪z - y, y - a⟫ ≥ 0` for every `a ∈ dom T`. -/
theorem SvMaximalMonotone.inner_nonneg_of_tendsto_resolventMap {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (𝓝[>] 0)) {z y : E}
    (hy : Tendsto (fun n ↦ resolventMap T (lam n) z) atTop (𝓝 y)) :
    y ∈ closure (svDom T) ∧ ∀ a ∈ svDom T, 0 ≤ ⟪z - y, y - a⟫_ℝ := by
  have hpos : ∀ᶠ n in atTop, 0 < lam n := hlam.eventually eventually_mem_nhdsWithin
  have hlim0 : Tendsto lam atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin hlam
  refine ⟨mem_closure_of_tendsto hy ?_, fun a ⟨b, hb⟩ ↦ ?_⟩
  · filter_upwards [hpos] with n hn
    exact hT.resolventMap_mem_svDom hn z
  · have hl : Tendsto (fun n ↦ ⟪z - resolventMap T (lam n) z, resolventMap T (lam n) z - a⟫_ℝ -
        lam n * ⟪b, resolventMap T (lam n) z - a⟫_ℝ) atTop
        (𝓝 (⟪z - y, y - a⟫_ℝ - 0 * ⟪b, y - a⟫_ℝ)) :=
      ((tendsto_const_nhds.sub hy).inner (hy.sub tendsto_const_nhds)).sub
        (hlim0.mul (tendsto_const_nhds.inner (hy.sub tendsto_const_nhds)))
    rw [zero_mul, sub_zero] at hl
    refine ge_of_tendsto hl ?_
    filter_upwards [hpos] with n hn
    exact sub_nonneg.2 (hT.mul_inner_le_inner_resolventMap hn z hb)

/-- **Theorem 12.37**, convexity: the closure of the domain of a maximal
monotone mapping is convex. -/
theorem SvMaximalMonotone.convex_closure_svDom {T : E → Set E} (hT : SvMaximalMonotone T) :
    Convex ℝ (closure (svDom T)) := by
  have key : closure (convexHull ℝ (svDom T)) ⊆ closure (svDom T) := by
    intro z hz
    set lam : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hlamdef
    have hlampos : ∀ n, 0 < lam n := fun n ↦ by positivity
    have hlam1 : ∀ n, lam n ≤ 1 := fun n ↦ by
      rw [hlamdef, div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hlam : Tendsto lam atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall hlampos⟩
    obtain ⟨R, hR⟩ := hT.exists_bound_resolventMap z
    obtain ⟨y, -, φ, hφ, hy⟩ :=
      tendsto_subseq_of_bounded (isBounded_closedBall (x := (0 : E)) (r := R))
        (x := fun n ↦ resolventMap T (lam n) z) fun n ↦ hR _ (hlampos n) (hlam1 n)
    obtain ⟨hyD, hineq⟩ :=
      hT.inner_nonneg_of_tendsto_resolventMap (hlam.comp hφ.tendsto_atTop) hy
    have hconv : Convex ℝ {a : E | 0 ≤ ⟪z - y, y - a⟫_ℝ} := by
      intro a₁ h₁ a₂ h₂ s t hs ht hst
      simp only [mem_setOf_eq] at h₁ h₂ ⊢
      have e : y - (s • a₁ + t • a₂) = s • (y - a₁) + t • (y - a₂) := by
        calc y - (s • a₁ + t • a₂) = (s + t) • y - (s • a₁ + t • a₂) := by
              rw [hst, one_smul]
          _ = s • (y - a₁) + t • (y - a₂) := by module
      rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right]
      exact add_nonneg (mul_nonneg hs h₁) (mul_nonneg ht h₂)
    have hH : closure (convexHull ℝ (svDom T)) ⊆ {a : E | 0 ≤ ⟪z - y, y - a⟫_ℝ} :=
      closure_minimal (convexHull_min hineq hconv)
        (isClosed_le continuous_const (by fun_prop))
    have h := hH hz
    simp only [mem_setOf_eq] at h
    rw [← neg_sub z y, inner_neg_right, real_inner_self_eq_norm_sq] at h
    have hzy : z = y := by
      have : ‖z - y‖ = 0 := by nlinarith [norm_nonneg (z - y)]
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    rw [hzy]
    exact hyD
  have heq : closure (svDom T) = closure (convexHull ℝ (svDom T)) :=
    Subset.antisymm (closure_mono (subset_convexHull ℝ _)) key
  rw [heq]
  exact (convex_convexHull ℝ _).closure

/-- The normal cone mapping of the closure of the domain is maximal monotone. -/
theorem SvMaximalMonotone.svMaximalMonotone_normalCone_closure_svDom {T : E → Set E}
    (hT : SvMaximalMonotone T) : SvMaximalMonotone (normalCone (closure (svDom T))) :=
  svMaximalMonotone_normalCone isClosed_closure hT.convex_closure_svDom
    hT.svDom_nonempty.closure

/-- The projection onto a nonempty closed convex set `D`, written as the
single-valued resolvent `(I + N_D)⁻¹`, is characterized by the variational
inequality. -/
theorem resolventMap_normalCone_eq_iff {D : Set E} (hDc : IsClosed D) (hD : Convex ℝ D)
    (hne : D.Nonempty) {z y : E} :
    resolventMap (normalCone D) 1 z = y ↔ y ∈ D ∧ ∀ a ∈ D, ⟪z - y, a - y⟫_ℝ ≤ 0 := by
  rw [(svMaximalMonotone_normalCone hDc hD hne).resolventMap_eq_iff one_pos]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hy : y ∈ D := hv.1
    refine ⟨hy, fun a ha ↦ ?_⟩
    rw [normalCone_eq_of_convex hD hy] at hv
    simpa only [one_smul, add_sub_cancel_left] using hv a ha
  · rintro ⟨hy, h⟩
    refine ⟨z - y, ?_, by rw [one_smul, add_sub_cancel]⟩
    rw [normalCone_eq_of_convex hD hy]
    exact h

omit [FiniteDimensional ℝ E] in
/-- **Theorem 12.37**, `(I + N_D)⁻¹ = P_D` for a convex set `D` (6.17). -/
theorem svResolvent_normalCone_eq_projMapping {D : Set E} (hD : Convex ℝ D) :
    svResolvent (normalCone D) 1 = projMapping D := by
  rw [projMapping_eq_svInv_add_normalCone_of_convex hD]
  funext z
  ext x
  rw [mem_svResolvent, mem_svInv]
  simp only [one_smul, mem_image]

/-- The projection onto a nonempty closed convex set is single-valued, given by
the resolvent of the normal cone mapping. -/
theorem projMapping_eq_singleton_resolventMap {D : Set E} (hDc : IsClosed D) (hD : Convex ℝ D)
    (hne : D.Nonempty) (z : E) :
    projMapping D z = {resolventMap (normalCone D) 1 z} := by
  rw [← svResolvent_normalCone_eq_projMapping hD]
  exact (svMaximalMonotone_normalCone hDc hD hne).svResolvent_eq_singleton_resolventMap one_pos z

/-- The projection fixes the points of `D`. -/
theorem resolventMap_normalCone_self {D : Set E} (hDc : IsClosed D) (hD : Convex ℝ D)
    {z : E} (hz : z ∈ D) : resolventMap (normalCone D) 1 z = z :=
  (resolventMap_normalCone_eq_iff hDc hD ⟨z, hz⟩).2 ⟨hz, fun a _ ↦ by simp⟩

/-- **Theorem 12.37**, the resolvents along any sequence `λν ↘ 0` converge
pointwise to the projection onto `D = cl(dom T)`. -/
theorem SvMaximalMonotone.tendsto_resolventMap_seq {T : E → Set E} (hT : SvMaximalMonotone T)
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (𝓝[>] 0)) (z : E) :
    Tendsto (fun n ↦ resolventMap T (lam n) z) atTop
      (𝓝 (resolventMap (normalCone (closure (svDom T))) 1 z)) := by
  have hDconv := hT.convex_closure_svDom
  have hne : (closure (svDom T)).Nonempty := hT.svDom_nonempty.closure
  obtain ⟨R, hR⟩ := hT.exists_bound_resolventMap z
  have hev : ∀ᶠ n in atTop, resolventMap T (lam n) z ∈ closedBall (0 : E) R := by
    have h1 : ∀ᶠ n in atTop, lam n < 1 :=
      (tendsto_nhds_of_tendsto_nhdsWithin hlam).eventually (Iio_mem_nhds (zero_lt_one' ℝ))
    filter_upwards [hlam.eventually eventually_mem_nhdsWithin, h1] with n hn hn1
    exact hR _ hn hn1.le
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨y, -, φ, hφ, hy⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall
    (hns.eventually hev).frequently
  refine ⟨φ, ?_⟩
  obtain ⟨hyD, hin⟩ :=
    hT.inner_nonneg_of_tendsto_resolventMap ((hlam.comp hns).comp hφ.tendsto_atTop) hy
  have hP : resolventMap (normalCone (closure (svDom T))) 1 z = y := by
    refine (resolventMap_normalCone_eq_iff isClosed_closure hDconv hne).2 ⟨hyD, fun a ha ↦ ?_⟩
    have hdom : svDom T ⊆ {a : E | ⟪z - y, a - y⟫_ℝ ≤ 0} := fun a ha ↦ by
      have := hin a ha
      simp only [mem_setOf_eq]
      rw [← neg_sub y a, inner_neg_right]
      linarith
    exact closure_minimal hdom (isClosed_le (by fun_prop) continuous_const) ha
  rw [hP]
  exact hy

/-- **Theorem 12.37**, the resolvents converge pointwise to the projection onto
`D = cl(dom T)` as `λ ↘ 0`. -/
theorem SvMaximalMonotone.tendsto_resolventMap_nhdsWithin_zero {T : E → Set E}
    (hT : SvMaximalMonotone T) (z : E) :
    Tendsto (fun lam ↦ resolventMap T lam z) (𝓝[>] 0)
      (𝓝 (resolventMap (normalCone (closure (svDom T))) 1 z)) :=
  tendsto_iff_seq_tendsto.2 fun _ hlam ↦ hT.tendsto_resolventMap_seq hlam z

/-- **Theorem 12.37**, uniform convergence: as `λ ↘ 0` the resolvents
`(I + λT)⁻¹` converge to the projection `P_D` uniformly on bounded sets. -/
theorem SvMaximalMonotone.tendstoUniformlyOn_resolventMap {T : E → Set E}
    (hT : SvMaximalMonotone T) {B : Set E} (hB : IsBounded B) :
    TendstoUniformlyOn (fun lam ↦ resolventMap T lam)
      (resolventMap (normalCone (closure (svDom T))) 1) (𝓝[>] 0) B :=
  tendstoUniformlyOn_of_lipschitzWith
    (eventually_mem_nhdsWithin.mono fun _ hlam ↦ hT.lipschitzWith_resolventMap hlam)
    (hT.svMaximalMonotone_normalCone_closure_svDom.lipschitzWith_resolventMap one_pos)
    hT.tendsto_resolventMap_nhdsWithin_zero hB

/-- **Theorem 12.37**, uniform convergence along any sequence `λν ↘ 0`. -/
theorem SvMaximalMonotone.tendstoUniformlyOn_resolventMap_seq {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (𝓝[>] 0)) {B : Set E}
    (hB : IsBounded B) :
    TendstoUniformlyOn (fun n ↦ resolventMap T (lam n))
      (resolventMap (normalCone (closure (svDom T))) 1) atTop B :=
  tendstoUniformlyOn_of_lipschitzWith
    ((hlam.eventually eventually_mem_nhdsWithin).mono fun _ hn ↦
      hT.lipschitzWith_resolventMap hn)
    (hT.svMaximalMonotone_normalCone_closure_svDom.lipschitzWith_resolventMap one_pos)
    (fun z ↦ hT.tendsto_resolventMap_seq hlam z) hB

/-- **Theorem 12.37**, `T(x)∞ = N_D(x)` for `x ∈ dom T` and `D = cl(dom T)`. -/
theorem SvMaximalMonotone.horizonCone_apply {T : E → Set E} (hT : SvMaximalMonotone T) {x : E}
    (hx : x ∈ svDom T) : horizonCone (T x) = normalCone (closure (svDom T)) x := by
  obtain ⟨v₀, hv₀⟩ := hx
  have hxD : x ∈ closure (svDom T) := subset_closure ⟨v₀, hv₀⟩
  rw [normalCone_eq_of_convex hT.convex_closure_svDom hxD]
  ext w
  constructor
  · intro hw a ha
    suffices hdom : svDom T ⊆ {a : E | ⟪w, a - x⟫_ℝ ≤ 0} from
      closure_minimal hdom (isClosed_le (by fun_prop) continuous_const) ha
    rintro a ⟨b, hb⟩
    simp only [mem_setOf_eq]
    by_contra hpos
    push_neg at hpos
    set c := ⟪w, a - x⟫_ℝ with hc
    set d := ⟪v₀ - b, x - a⟫_ℝ with hd
    have hτ : 0 ≤ (|d| + 1) / c := by positivity
    have hm := hT.1 hb (smul_add_mem_of_mem_horizonCone (hT.convex_apply x) (hT.isClosed_apply x)
      hv₀ hw hτ)
    have e1 : ⟪w, x - a⟫_ℝ = -c := by rw [hc, ← inner_neg_right, neg_sub]
    rw [add_sub_assoc, inner_add_left, real_inner_smul_left, e1, ← hd] at hm
    have hc0 : c ≠ 0 := hpos.ne'
    have e2 : (|d| + 1) / c * -c = -(|d| + 1) := by field_simp
    rw [e2] at hm
    linarith [le_abs_self d]
  · intro hw
    refine mem_horizonCone_of_forall_smul_add_mem (x := v₀) ?_
    intro τ hτ
    refine hT.mem_of_forall_inner_nonneg fun a b hb ↦ ?_
    have h1 := hT.1 hb hv₀
    have h2 := hw a (subset_closure ⟨b, hb⟩)
    have h3 : 0 ≤ ⟪w, x - a⟫_ℝ := by
      rw [← neg_sub a x, inner_neg_right]
      linarith
    rw [add_sub_assoc, inner_add_left, real_inner_smul_left]
    have := mul_nonneg hτ h3
    linarith

/-- **Theorem 12.37**, graphical convergence `λT → N_D` as `λ ↘ 0`. -/
theorem SvMaximalMonotone.pkConvergesAlong_smul {T : E → Set E} (hT : SvMaximalMonotone T) :
    PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun lam ↦ svGraph (fun x ↦ lam • T x))
      (svGraph (normalCone (closure (svDom T)))) := by
  set D := closure (svDom T) with hDdef
  have hDconv : Convex ℝ D := hT.convex_closure_svDom
  have hN : SvMaximalMonotone (normalCone D) := hT.svMaximalMonotone_normalCone_closure_svDom
  have hin : svGraph (normalCone D) ⊆
      innerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun lam ↦ svGraph (fun x ↦ lam • T x)) := by
    rintro ⟨x, v⟩ hv V hV
    have hv' : v ∈ normalCone D x := hv
    have hP : resolventMap (normalCone D) 1 (x + v) = x :=
      (hN.resolventMap_eq_iff one_pos).2 ⟨v, hv', by rw [one_smul]⟩
    have ht := hT.tendsto_resolventMap_nhdsWithin_zero (x + v)
    rw [← hDdef, hP] at ht
    have ht2 : Tendsto (fun lam ↦ (resolventMap T lam (x + v), x + v - resolventMap T lam (x + v)))
        (𝓝[>] 0) (𝓝 (x, v)) := by
      have h := ht.prodMk_nhds ((tendsto_const_nhds (x := x + v)).sub ht)
      rwa [add_sub_cancel_left] at h
    filter_upwards [ht2 hV, eventually_mem_nhdsWithin] with lam h1 h2
    refine ⟨_, ?_, h1⟩
    change x + v - resolventMap T lam (x + v) ∈ lam • T (resolventMap T lam (x + v))
    have hm := hT.inv_smul_sub_resolventMap_mem h2 (x + v)
    have e : x + v - resolventMap T lam (x + v) =
        lam • (lam⁻¹ • (x + v - resolventMap T lam (x + v))) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt h2), one_smul]
    rw [e]
    exact smul_mem_smul_set hm
  have hout : outerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun lam ↦ svGraph (fun x ↦ lam • T x)) ⊆
      svGraph (normalCone D) := by
    rintro ⟨x, v⟩ hxv
    have hxD : x ∈ D := by
      by_contra hx
      have hV : (Dᶜ ×ˢ (univ : Set E)) ∈ 𝓝 (x, v) :=
        prod_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hx) univ_mem
      obtain ⟨_, p, hp, hpV⟩ := (hxv _ hV).exists
      obtain ⟨u, hu, -⟩ := mem_smul_set.1 hp
      exact hpV.1 (subset_closure ⟨u, hu⟩)
    change v ∈ normalCone D x
    rw [normalCone_eq_of_convex hDconv hxD]
    have hdom : svDom T ⊆ {a : E | ⟪v, a - x⟫_ℝ ≤ 0} := by
      rintro a ⟨b, hb⟩
      simp only [mem_setOf_eq]
      by_contra hpos
      push_neg at hpos
      have hg : Continuous (fun q : ℝ × (E × E) ↦ ⟪q.2.2 - q.1 • b, q.2.1 - a⟫_ℝ) := by
        fun_prop
      have h0 : ⟪v - (0 : ℝ) • b, x - a⟫_ℝ < 0 := by
        rw [zero_smul, sub_zero, ← neg_sub a x, inner_neg_right]
        linarith
      have hmem : {q : ℝ × (E × E) | ⟪q.2.2 - q.1 • b, q.2.1 - a⟫_ℝ < 0} ∈
          𝓝 ((0 : ℝ), (x, v)) :=
        (isOpen_lt hg continuous_const).mem_nhds h0
      obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.1 hmem
      have hU' : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ U := nhdsWithin_le_nhds hU
      have hevU : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ U ∧ 0 < lam :=
        hU'.and eventually_mem_nhdsWithin
      obtain ⟨lam, ⟨hlamU, hlampos⟩, p, hp, hpW⟩ := (hevU.and_frequently (hxv W hW)).exists
      obtain ⟨u, hu, hpu⟩ := mem_smul_set.1 hp
      have hlt : ⟪p.2 - lam • b, p.1 - a⟫_ℝ < 0 := hUW (Set.mk_mem_prod hlamU hpW)
      rw [← hpu, ← smul_sub, real_inner_smul_left] at hlt
      have := hT.1 hb hu
      nlinarith
    intro a ha
    exact closure_minimal hdom (isClosed_le (by fun_prop) continuous_const) ha
  have hio := innerSetLimitAlong_subset_outerSetLimitAlong (l := 𝓝[>] (0 : ℝ))
    (fun lam ↦ svGraph (fun x ↦ lam • T x))
  exact ⟨Subset.antisymm (hio.trans hout) hin, Subset.antisymm hout (hin.trans hio)⟩

/-- Convergence along a filter gives convergence along every sequence tending
to that filter. -/
theorem PKConvergesAlong.pkConverges_comp {ι F : Type*} [TopologicalSpace F] {l : Filter ι}
    {C : ι → Set F} {D : Set F} (h : PKConvergesAlong l C D) {u : ℕ → ι}
    (hu : Tendsto u atTop l) : PKConverges (fun n ↦ C (u n)) D := by
  have hin : D ⊆ innerSetLimit (fun n ↦ C (u n)) := by
    intro q hq V hV
    have hq' : q ∈ innerSetLimitAlong l C := by
      rw [h.inner_eq]
      exact hq
    exact hu.eventually (hq' V hV)
  have hout : outerSetLimit (fun n ↦ C (u n)) ⊆ D := by
    intro q hq
    rw [← h.outer_eq]
    intro V hV
    exact hu.frequently (hq V hV)
  have hio := innerSetLimit_subset_outerSetLimit (fun n ↦ C (u n))
  exact ⟨Subset.antisymm (hio.trans hout) hin, Subset.antisymm hout (hin.trans hio)⟩

/-- **Theorem 12.37**, graphical convergence `λν T → N_D` along every sequence
`λν ↘ 0`. -/
theorem SvMaximalMonotone.graphicalConverges_smul {T : E → Set E} (hT : SvMaximalMonotone T)
    {lam : ℕ → ℝ} (hlam : Tendsto lam atTop (𝓝[>] 0)) :
    GraphicalConverges (fun n x ↦ lam n • T x) (normalCone (closure (svDom T))) :=
  hT.pkConvergesAlong_smul.pkConverges_comp hlam

/-- **Theorem 12.37 (normal vectors to domains)**, collected.  For maximal
monotone `T` and `D = cl(dom T)`: `D` is convex; `T(x)∞ = N_D(x)` for
`x ∈ dom T`; `λT → N_D` graphically as `λ ↘ 0`; `(I + N_D)⁻¹ = P_D`; and the
resolvents `(I + λT)⁻¹` converge to `P_D` uniformly on bounded sets. -/
theorem normal_vectors_to_domains {T : E → Set E} (hT : SvMaximalMonotone T) :
    Convex ℝ (closure (svDom T)) ∧
      (∀ x ∈ svDom T, horizonCone (T x) = normalCone (closure (svDom T)) x) ∧
      PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun lam ↦ svGraph (fun x ↦ lam • T x))
        (svGraph (normalCone (closure (svDom T)))) ∧
      svResolvent (normalCone (closure (svDom T))) 1 = projMapping (closure (svDom T)) ∧
      (∀ z, projMapping (closure (svDom T)) z =
        {resolventMap (normalCone (closure (svDom T))) 1 z}) ∧
      ∀ B : Set E, IsBounded B → TendstoUniformlyOn (fun lam ↦ resolventMap T lam)
        (resolventMap (normalCone (closure (svDom T))) 1) (𝓝[>] 0) B :=
  ⟨hT.convex_closure_svDom, fun _ hx ↦ hT.horizonCone_apply hx, hT.pkConvergesAlong_smul,
    svResolvent_normalCone_eq_projMapping hT.convex_closure_svDom,
    projMapping_eq_singleton_resolventMap isClosed_closure hT.convex_closure_svDom
      hT.svDom_nonempty.closure,
    fun _ hB ↦ hT.tendstoUniformlyOn_resolventMap hB⟩

/-- **Corollary 12.38**, the boundary criterion: a maximal monotone mapping is
locally bounded at `x̄` exactly when `x̄` is not a boundary point of `cl(dom T)`. -/
theorem SvMaximalMonotone.svLocallyBoundedAt_iff_notMem_frontier {T : E → Set E}
    (hT : SvMaximalMonotone T) {xbar : E} :
    SvLocallyBoundedAt T xbar ↔ xbar ∉ frontier (closure (svDom T)) := by
  set D := closure (svDom T) with hDdef
  have hDc : IsClosed D := isClosed_closure
  have hDconv : Convex ℝ D := hT.convex_closure_svDom
  have hN : SvMaximalMonotone (normalCone D) := hT.svMaximalMonotone_normalCone_closure_svDom
  constructor
  · intro hlb hfr
    obtain ⟨u, hu, hu0⟩ := (mem_frontier_iff_exists_nonzero_normal hDc).1 hfr
    have hP : resolventMap (normalCone D) 1 (xbar + u) = xbar :=
      (hN.resolventMap_eq_iff one_pos).2 ⟨u, hu, by rw [one_smul]⟩
    have ht := hT.tendsto_resolventMap_nhdsWithin_zero (xbar + u)
    rw [← hDdef, hP] at ht
    obtain ⟨V, hV, hbdd⟩ := hlb
    obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : E)
    have h1 : ∀ᶠ lam in 𝓝[>] (0 : ℝ), resolventMap T lam (xbar + u) ∈ V ∧ 0 < lam :=
      (ht.eventually hV).and eventually_mem_nhdsWithin
    have h2 : Tendsto (fun lam ↦ lam⁻¹ * ‖xbar + u - resolventMap T lam (xbar + u)‖)
        (𝓝[>] (0 : ℝ)) atTop := by
      have hn : Tendsto (fun lam ↦ ‖xbar + u - resolventMap T lam (xbar + u)‖) (𝓝[>] 0)
          (𝓝 ‖xbar + u - xbar‖) := (tendsto_const_nhds.sub ht).norm
      rw [add_sub_cancel_left] at hn
      exact tendsto_inv_nhdsGT_zero.atTop_mul_pos (norm_pos_iff.2 hu0) hn
    obtain ⟨lam, ⟨hJV, hlam⟩, hbig⟩ := (h1.and (h2.eventually_gt_atTop R)).exists
    have hmem : lam⁻¹ • (xbar + u - resolventMap T lam (xbar + u)) ∈ svImage T V :=
      mem_svImage.2 ⟨_, hJV, hT.inv_smul_sub_resolventMap_mem hlam _⟩
    have h3 := hR hmem
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)] at h3
    linarith
  · intro hfr
    by_cases hxD : xbar ∈ D
    · by_contra hlb
      obtain ⟨xs, vs, hvs, hxs, hnorm⟩ := exists_seq_of_not_svLocallyBoundedAt hlb
      obtain ⟨φ, u, hφ, hu1, hu⟩ := exists_subseq_tendsto_normalize hnorm
      have hdom : svDom T ⊆ {a : E | ⟪u, a - xbar⟫_ℝ ≤ 0} := by
        rintro a ⟨b, hb⟩
        exact inner_nonpos_of_inner_sub_nonneg (x := xs ∘ φ) (v := vs ∘ φ)
          (a := fun _ ↦ a) (b := fun _ ↦ b) (Eventually.of_forall fun n ↦ hT.1 hb (hvs (φ n)))
          (hxs.comp hφ.tendsto_atTop) tendsto_const_nhds tendsto_const_nhds
          (hnorm.comp hφ.tendsto_atTop) hu
      have hun : u ∈ normalCone D xbar := by
        rw [normalCone_eq_of_convex hDconv hxD]
        intro a ha
        exact closure_minimal hdom (isClosed_le (by fun_prop) continuous_const) ha
      have hu0 : u ≠ 0 := by
        intro h
        rw [h, norm_zero] at hu1
        exact zero_ne_one hu1
      exact hfr ((mem_frontier_iff_exists_nonzero_normal hDc).2 ⟨u, hun, hu0⟩)
    · exact svLocallyBoundedAt_of_notMem_closure_svDom hxD

/-- **Corollary 12.38**, at points of the domain: `T` is locally bounded at
`x̄ ∈ dom T` exactly when `T(x̄)` is bounded. -/
theorem SvMaximalMonotone.svLocallyBoundedAt_iff_isBounded {T : E → Set E}
    (hT : SvMaximalMonotone T) {xbar : E} (hx : xbar ∈ svDom T) :
    SvLocallyBoundedAt T xbar ↔ IsBounded (T xbar) := by
  refine ⟨SvLocallyBoundedAt.isBounded_apply, fun hb ↦ ?_⟩
  rw [hT.svLocallyBoundedAt_iff_notMem_frontier]
  intro hfr
  obtain ⟨u, hu, hu0⟩ := (mem_frontier_iff_exists_nonzero_normal isClosed_closure).1 hfr
  rw [← hT.horizonCone_apply hx, isBounded_iff_horizonCone_eq_singleton_zero.1 hb] at hu
  exact hu0 hu

/-- **Corollary 12.38 (local boundedness of monotone mappings)**, collected. -/
theorem local_boundedness_of_monotone_mappings {T : E → Set E} (hT : SvMaximalMonotone T) :
    (∀ xbar, SvLocallyBoundedAt T xbar ↔ xbar ∉ frontier (closure (svDom T))) ∧
      ∀ xbar ∈ svDom T, SvLocallyBoundedAt T xbar ↔ IsBounded (T xbar) :=
  ⟨fun _ ↦ hT.svLocallyBoundedAt_iff_notMem_frontier,
    fun _ hx ↦ hT.svLocallyBoundedAt_iff_isBounded hx⟩

/-- **Corollary 12.39(a)**: `dom T = IRⁿ` exactly when `T` is locally bounded
everywhere. -/
theorem SvMaximalMonotone.svDom_eq_univ_iff {T : E → Set E} (hT : SvMaximalMonotone T) :
    svDom T = univ ↔ SvLocallyBounded T := by
  constructor
  · intro h x
    rw [hT.svLocallyBoundedAt_iff_notMem_frontier, h, closure_univ, frontier_univ]
    exact notMem_empty x
  · intro h
    have hfr : frontier (closure (svDom T)) = ∅ :=
      eq_empty_of_forall_notMem fun x ↦ hT.svLocallyBoundedAt_iff_notMem_frontier.1 (h x)
    have hD : closure (svDom T) = univ :=
      (isClopen_iff_frontier_eq_empty.2 hfr).eq_univ hT.svDom_nonempty.closure
    exact eq_univ_of_forall fun x ↦
      mem_svDom_of_mem_closure hT.isClosed_svGraph (hD ▸ mem_univ x) (h x)

/-- **Corollary 12.39(a)**, the particular case: a maximal monotone mapping
with bounded range has full domain. -/
theorem SvMaximalMonotone.svDom_eq_univ_of_isBounded_svRange {T : E → Set E}
    (hT : SvMaximalMonotone T) (h : IsBounded (svRange T)) : svDom T = univ :=
  hT.svDom_eq_univ_iff.2 (SvBounded.svLocallyBounded h)

/-- **Corollary 12.39(b)**: `rge T = IRⁿ` exactly when `T⁻¹` is locally
bounded everywhere. -/
theorem SvMaximalMonotone.svRange_eq_univ_iff {T : E → Set E} (hT : SvMaximalMonotone T) :
    svRange T = univ ↔ SvLocallyBounded (svInv T) := by
  rw [← svDom_svInv]
  exact hT.inv.svDom_eq_univ_iff

/-- **Corollary 12.39(b)**, the particular case: a maximal monotone mapping
with bounded domain has full range. -/
theorem SvMaximalMonotone.svRange_eq_univ_of_isBounded_svDom {T : E → Set E}
    (hT : SvMaximalMonotone T) (h : IsBounded (svDom T)) : svRange T = univ :=
  hT.svRange_eq_univ_iff.2 (SvBounded.svLocallyBounded (S := svInv T) h)

/-- **Corollary 12.39 (full domains and ranges)**, collected. -/
theorem full_domains_and_ranges {T : E → Set E} (hT : SvMaximalMonotone T) :
    (svDom T = univ ↔ SvLocallyBounded T) ∧ (IsBounded (svRange T) → svDom T = univ) ∧
      (svRange T = univ ↔ SvLocallyBounded (svInv T)) ∧
      (IsBounded (svDom T) → svRange T = univ) :=
  ⟨hT.svDom_eq_univ_iff, hT.svDom_eq_univ_of_isBounded_svRange, hT.svRange_eq_univ_iff,
    hT.svRange_eq_univ_of_isBounded_svDom⟩

/-- **Theorem 12.41**, the core inclusion: the relative interior of the convex
set `cl(dom T)` lies in `dom T`. -/
theorem SvMaximalMonotone.intrinsicInterior_closure_svDom_subset {T : E → Set E}
    (hT : SvMaximalMonotone T) : intrinsicInterior ℝ (closure (svDom T)) ⊆ svDom T := by
  intro z hz
  set D := closure (svDom T) with hDdef
  have hDconv : Convex ℝ D := hT.convex_closure_svDom
  have hzD : z ∈ D := intrinsicInterior_subset hz
  set lam : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hlamdef
  have hlampos : ∀ n, 0 < lam n := fun n ↦ by positivity
  have hlam : Tendsto lam atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hlampos⟩
  set x : ℕ → E := fun n ↦ resolventMap T (lam n) z with hxdef
  set v : ℕ → E := fun n ↦ (lam n)⁻¹ • (z - x n) with hvdef
  have hv : ∀ n, v n ∈ T (x n) := fun n ↦ hT.inv_smul_sub_resolventMap_mem (hlampos n) z
  have hx : Tendsto x atTop (𝓝 z) := by
    have h := hT.tendsto_resolventMap_seq hlam z
    rwa [← hDdef, resolventMap_normalCone_self isClosed_closure hDconv hzD] at h
  by_cases hbdd : ∃ R, ∃ᶠ n in atTop, ‖v n‖ ≤ R
  · obtain ⟨R, hR⟩ := hbdd
    obtain ⟨w, -, φ, hφ, hw⟩ := tendsto_subseq_of_frequently_bounded
      (isBounded_closedBall (x := (0 : E)) (r := R))
      (hR.mono fun n hn ↦ mem_closedBall_zero_iff.2 hn)
    exact ⟨w, hT.isClosed_svGraph.mem_of_tendsto ((hx.comp hφ.tendsto_atTop).prodMk_nhds hw)
      (Eventually.of_forall fun n ↦ hv (φ n))⟩
  · push_neg at hbdd
    have hnorm : Tendsto (fun n ↦ ‖v n‖) atTop atTop :=
      tendsto_atTop.2 fun R ↦ (hbdd R).mono fun n hn ↦ hn.le
    obtain ⟨φ, u, hφ, hu1, hu⟩ := exists_subseq_tendsto_normalize hnorm
    have hdom : svDom T ⊆ {a : E | ⟪u, a - z⟫_ℝ ≤ 0} := by
      rintro a ⟨b, hb⟩
      exact inner_nonpos_of_inner_sub_nonneg (x := x ∘ φ) (v := v ∘ φ)
        (a := fun _ ↦ a) (b := fun _ ↦ b) (Eventually.of_forall fun n ↦ hT.1 hb (hv (φ n)))
        (hx.comp hφ.tendsto_atTop) tendsto_const_nhds tendsto_const_nhds
        (hnorm.comp hφ.tendsto_atTop) hu
    have hD : ∀ a ∈ D, ⟪u, a - z⟫_ℝ ≤ 0 := fun a ha ↦
      closure_minimal hdom (isClosed_le (by fun_prop) continuous_const) ha
    have horth : ∀ a ∈ D, ⟪u, a - z⟫_ℝ = 0 := by
      intro a ha
      obtain ⟨ε, hε, hmem⟩ := exists_pos_add_smul_sub_mem_of_mem_intrinsicInterior hz ha
      have h := hD _ hmem
      rw [add_sub_cancel_left, real_inner_smul_right, ← neg_sub a z, inner_neg_right] at h
      have : 0 ≤ ⟪u, a - z⟫_ℝ := by nlinarith
      exact le_antisymm (hD a ha) this
    have hle : vectorSpan ℝ D ≤ (ℝ ∙ u)ᗮ := by
      rw [vectorSpan_def]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, a', ha', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      change ⟪u, a -ᵥ a'⟫_ℝ = 0
      rw [vsub_eq_sub, ← sub_sub_sub_cancel_right a a' z, inner_sub_right, horth a ha,
        horth a' ha', sub_zero]
    have hxD : ∀ n, x n ∈ D := fun n ↦ subset_closure (hT.resolventMap_mem_svDom (hlampos n) z)
    have huM : u ∈ vectorSpan ℝ D := by
      refine (Submodule.closed_of_finiteDimensional _).mem_of_tendsto hu
        (Eventually.of_forall fun n ↦ ?_)
      refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
      exact vsub_mem_vectorSpan ℝ hzD (hxD (φ n))
    have h := hle huM
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq, hu1] at h
    norm_num at h

/-- **Theorem 12.41**: the relative interiors of `dom T` and of `cl(dom T)`
coincide (the remark after 12.41). -/
theorem SvMaximalMonotone.intrinsicInterior_svDom {T : E → Set E} (hT : SvMaximalMonotone T) :
    intrinsicInterior ℝ (svDom T) = intrinsicInterior ℝ (closure (svDom T)) := by
  have hA := affineSpan_closure (svDom T)
  ext z
  rw [mem_intrinsicInterior_iff_ball, mem_intrinsicInterior_iff_ball, hA]
  constructor
  · rintro ⟨hz, r, hr, hball⟩
    exact ⟨subset_closure hz, r, hr, fun y hy hyz ↦ subset_closure (hball y hy hyz)⟩
  · rintro ⟨hz, r, hr, hball⟩
    have hzi : z ∈ intrinsicInterior ℝ (closure (svDom T)) := by
      rw [mem_intrinsicInterior_iff_ball, hA]
      exact ⟨hz, r, hr, hball⟩
    refine ⟨hT.intrinsicInterior_closure_svDom_subset hzi, r / 2, by positivity,
      fun y hy hyz ↦ hT.intrinsicInterior_closure_svDom_subset ?_⟩
    rw [mem_intrinsicInterior_iff_ball, hA]
    refine ⟨hball y hy (by linarith), r / 2, by positivity, fun y' hy' hy'y ↦ hball y' hy' ?_⟩
    calc dist y' z ≤ dist y' y + dist y z := dist_triangle _ _ _
      _ < r := by linarith

/-- **Theorem 12.41 (near convexity of domains and ranges)**, domains: there is
a convex set `C` with `C ⊂ dom T ⊂ cl C`, namely `C = rint(cl(dom T))`. -/
theorem SvMaximalMonotone.exists_convex_subset_svDom {T : E → Set E} (hT : SvMaximalMonotone T) :
    ∃ C : Set E, Convex ℝ C ∧ C ⊆ svDom T ∧ svDom T ⊆ closure C :=
  ⟨intrinsicInterior ℝ (closure (svDom T)),
    Convex.convex_intrinsicInterior hT.convex_closure_svDom,
    hT.intrinsicInterior_closure_svDom_subset,
    subset_closure.trans (Convex.subset_closure_intrinsicInterior hT.convex_closure_svDom)⟩

/-- **Theorem 12.41**, ranges: there is a convex set `C` with
`C ⊂ rge T ⊂ cl C`. -/
theorem SvMaximalMonotone.exists_convex_subset_svRange {T : E → Set E}
    (hT : SvMaximalMonotone T) :
    ∃ C : Set E, Convex ℝ C ∧ C ⊆ svRange T ∧ svRange T ⊆ closure C := by
  rw [← svDom_svInv]
  exact hT.inv.exists_convex_subset_svDom

/-- **Theorem 12.41 (near convexity of domains and ranges)**, collected. -/
theorem near_convexity_of_domains_and_ranges {T : E → Set E} (hT : SvMaximalMonotone T) :
    (∃ C : Set E, Convex ℝ C ∧ C ⊆ svDom T ∧ svDom T ⊆ closure C) ∧
      (∃ C : Set E, Convex ℝ C ∧ C ⊆ svRange T ∧ svRange T ⊆ closure C) ∧
      intrinsicInterior ℝ (svDom T) = intrinsicInterior ℝ (closure (svDom T)) ∧
      intrinsicInterior ℝ (svRange T) = intrinsicInterior ℝ (closure (svRange T)) :=
  ⟨hT.exists_convex_subset_svDom, hT.exists_convex_subset_svRange, hT.intrinsicInterior_svDom,
    by simpa only [svDom_svInv] using hT.inv.intrinsicInterior_svDom⟩

end Domains

end RW
