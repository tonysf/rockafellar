/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Differentiability and semidifferentiability of monotone mappings

Theorem 12.65, with differentiability of a set-valued mapping (the definition
after 8.43) as `SvDifferentiableAt`.

(a) ⇒ (b): a semiderivative is the graphical derivative `DT(x̄|v̄)`, maximal
monotone by 12.64 and, by 8.43, continuous with full domain, hence single-valued
everywhere by 12.63(c).  (This replaces the book's detour through `0 ∈ int dom`.)

(b) ⇒ (a) follows the book.  Every graphical cluster point `H` of the difference
quotients along `τν ↘ 0` (12.33, no escape since `(0, 0)` lies in every graph) is
maximal monotone with `H ⊂ DT(x̄|v̄)`.  The book asserts that this forces `H` to be
locally bounded everywhere; here the step is proved: `dom H` is open by 12.38 and
12.41 (bounded values), and closed because a point of `cl(dom H)` is approached
along the ray from the origin, on which `H` agrees with the positively
homogeneous `DT(x̄|v̄)`.  So `H = DT(x̄|v̄)`, which is therefore maximal monotone,
and the quotients converge to it graphically by the subsequence principle for the
resolvents (12.32).  Uniform local boundedness (12.40(a)) then gives the linear
growth estimate of 8.43(e), whence semidifferentiability and the expansion 8.43(f).

(b) ⇔ (c) uses `DR_λ(z̄_λ) = (I + λDT(x̄|v̄))⁻¹` from 12.64, and the primed clauses
use 8.43(e,f) and 9.25(b), a linear map on `IRⁿ` being bijective exactly when its
determinant is nonzero.
-/

import RockafellarWets.Chapter12.MonotoneProtoDerivatives
import RockafellarWets.Chapter12.MonotoneContinuity
import RockafellarWets.Chapter12.ConvexSubgradientConvergence

open Bornology Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

section Definition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiability of a set-valued mapping (the definition after 8.43):
`∅ ≠ T(x) ⊂ v̄ + A[x - x̄] + o(|x - x̄|)IB` for `x` near `x̄`, for some vector `v̄`
and some linear map `A`.  Then `T(x̄) = {v̄}`. -/
def SvDifferentiableAt (T : E → Set F) (x : E) : Prop :=
  ∃ (u : F) (A : E →L[ℝ] F), HasMappingFirstOrderExpansion T x u A

theorem svPositivelyHomogeneous_svSingleton_iff {A : E → F} :
    SvPositivelyHomogeneous (svSingleton A) ↔
      A 0 = 0 ∧ ∀ w (c : ℝ), 0 < c → A (c • w) = c • A w := by
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨(mem_singleton_iff.1 h0).symm, fun w c hc ↦ ?_⟩
    have h := hs w c hc
    rwa [svSingleton, svSingleton, smul_set_singleton, singleton_eq_singleton_iff] at h
  · rintro ⟨h0, hs⟩
    exact ⟨h0.symm, fun w c hc ↦ by simp only [svSingleton, hs w c hc, smul_set_singleton]⟩

theorem svPositivelyHomogeneous_svSingleton_continuousLinearMap (L : E →L[ℝ] F) :
    SvPositivelyHomogeneous (svSingleton L) :=
  svPositivelyHomogeneous_svSingleton_iff.2 ⟨map_zero L, fun w c _ ↦ map_smul L c w⟩

end Definition

section MaximalMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A maximal monotone mapping that is locally bounded at a point of its domain
is nonempty-valued around it (12.38, 12.41). -/
theorem SvMaximalMonotone.eventually_nonempty_of_svLocallyBoundedAt {T : E → Set E}
    (hT : SvMaximalMonotone T) {x : E} (hx : x ∈ svDom T) (hlb : SvLocallyBoundedAt T x) :
    ∀ᶠ y in 𝓝 x, (T y).Nonempty := by
  have hfr := hT.svLocallyBoundedAt_iff_notMem_frontier.1 hlb
  have hint : x ∈ interior (closure (svDom T)) := by
    by_contra h
    exact hfr ⟨subset_closure (subset_closure hx), h⟩
  exact mem_of_superset (isOpen_interior.mem_nhds hint) hT.interior_closure_svDom_subset

/-- A maximal monotone mapping `H` with `0 ∈ dom H`, contained in a positively
homogeneous single-valued mapping `d`, coincides with `d`.  Its domain is open,
because `H` is bounded-valued (12.38, 12.41), and closed, because a point of
`cl(dom H)` is approached along the ray from the origin, on which `H = d` grows
linearly. -/
theorem SvMaximalMonotone.eq_svSingleton_of_subset {H : E → Set E} (hH : SvMaximalMonotone H)
    {d : E → E} (hd : ∀ w (c : ℝ), 0 < c → d (c • w) = c • d w) (hsub : ∀ w, H w ⊆ {d w})
    (h0 : (0 : E) ∈ svDom H) : H = svSingleton d := by
  set C := svDom H with hC
  have hmem : ∀ w ∈ C, d w ∈ H w := by
    rintro w ⟨y, hy⟩
    rwa [← mem_singleton_iff.1 (hsub w hy)]
  have hopen : IsOpen C := by
    refine isOpen_iff_mem_nhds.2 fun w hw ↦ ?_
    have hb : IsBounded (H w) := isBounded_singleton.subset (hsub w)
    exact hH.eventually_nonempty_of_svLocallyBoundedAt hw
      ((hH.svLocallyBoundedAt_iff_isBounded hw).2 hb)
  have hclosed : IsClosed C := by
    refine isClosed_of_closure_subset fun w hw ↦ ?_
    have hconv : Convex ℝ (closure C) := hH.convex_closure_svDom
    have h0int : (0 : E) ∈ interior (closure C) :=
      interior_mono subset_closure (hopen.interior_eq.symm ▸ h0)
    have hseg : ∀ t : ℝ, 0 < t → t < 1 → t • w ∈ C := by
      intro t ht0 ht1
      apply hH.interior_closure_svDom_subset
      apply hconv.openSegment_interior_closure_subset_interior h0int (subset_closure hw)
      exact ⟨1 - t, t, by linarith, ht0, by ring, by simp⟩
    let t : ℕ → ℝ := fun n ↦ 1 - 1 / ((n : ℝ) + 1) / 2
    have hle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n ↦ by
      rw [div_le_one (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)]
    have ht0 : ∀ n, 0 < t n := fun n ↦ by
      have := hle n
      simp only [t]
      linarith
    have ht1 : ∀ n, t n < 1 := fun n ↦ by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      simp only [t]
      linarith
    have htl : Tendsto t atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat.div_const 2)
      rwa [zero_div, sub_zero] at this
    have hgraph : ∀ n, (t n • w, t n • d w) ∈ svGraph H := fun n ↦ by
      change t n • d w ∈ H (t n • w)
      rw [← hd w (t n) (ht0 n)]
      exact hmem _ (hseg _ (ht0 n) (ht1 n))
    have hlim : Tendsto (fun n ↦ (t n • w, t n • d w)) atTop (𝓝 (w, d w)) := by
      have := (htl.smul_const w).prodMk_nhds (htl.smul_const (d w))
      simpa using this
    exact ⟨d w, hH.isClosed_svGraph.mem_of_tendsto hlim (Eventually.of_forall hgraph)⟩
  have huniv : C = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, h0⟩
  funext w
  exact Subset.antisymm (hsub w) (singleton_subset_iff.2 (hmem w (huniv ▸ mem_univ w)))


omit [FiniteDimensional ℝ E] in
/-- The difference quotients `Δ_τT(x̄|v̄)` all contain the graph point `(0, 0)`, so
they do not escape to the horizon. -/
theorem not_svEscapesToHorizon_mappingDifferenceQuotient {T : E → Set E} {x v : E}
    (hv : v ∈ T x) {τ : ℕ → ℝ} (hτ : ∀ n, τ n ≠ 0) :
    ¬ SvEscapesToHorizon (fun n ↦ mappingDifferenceQuotient T x v (τ n)) := by
  intro h
  obtain ⟨n, hn⟩ := (h {0} isBounded_singleton {0} isBounded_singleton).exists
  have h0 : (0 : E) ∈ mappingDifferenceQuotient T x v (τ n) 0 :=
    (mem_mappingDifferenceQuotient_iff (hτ n)).2 (by simpa using hv)
  exact (eq_empty_iff_forall_notMem.1 (hn 0 (mem_singleton 0))) 0 ⟨h0, mem_singleton 0⟩

/-- **Theorem 12.65**, (b) ⇒ proto-differentiability.  If `DT(x̄|v̄)` is
single-valued, every cluster point `H` of the difference quotients along a
sequence `τν ↘ 0` (12.33) is maximal monotone with `H ⊂ DT(x̄|v̄)`, hence equal to
`DT(x̄|v̄)`; so `DT(x̄|v̄)` is maximal monotone and the difference quotients
converge to it graphically, by the subsequence principle for the resolvents
(12.32). -/
theorem SvMaximalMonotone.isProtoDifferentiableAt_of_eq_svSingleton {T : E → Set E}
    (hT : SvMaximalMonotone T) {x v : E} (hv : v ∈ T x) {d : E → E}
    (hd : graphicalDerivative T x v = svSingleton d) :
    IsProtoDifferentiableAt T x v ∧ SvMaximalMonotone (graphicalDerivative T x v) := by
  have hhom : ∀ w (c : ℝ), 0 < c → d (c • w) = c • d w := by
    have h := svPositivelyHomogeneous_graphicalDerivative hv
    rw [hd, svPositivelyHomogeneous_svSingleton_iff] at h
    exact h.2
  have key : ∀ τ : ℕ → ℝ, (∀ n, 0 < τ n) → Tendsto τ atTop (𝓝[>] 0) →
      SvMaximalMonotone (svSingleton d) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
        GraphicalConverges (fun n ↦ mappingDifferenceQuotient T x v (τ (φ n))) (svSingleton d) := by
    intro τ hpos hτ
    obtain ⟨φ, H, hφ, hH, hconv⟩ := exists_graphicalConverges_svMaximalMonotone
      (fun n ↦ hT.differenceQuotient x v (hpos n).ne')
      (not_svEscapesToHorizon_mappingDifferenceQuotient hv fun n ↦ (hpos n).ne')
    have hsubH : ∀ w, H w ⊆ {d w} := by
      intro w z hz
      have h1 : z ∈ graphicalOuterLimit (fun n ↦ mappingDifferenceQuotient T x v (τ (φ n))) w :=
        graphicalInnerLimit_subset _ w ((graphicalConverges_iff.1 hconv).2 w hz)
      have h2 : (w, z) ∈ svGraph (graphicalDerivative T x v) := by
        rw [svGraph_graphicalDerivative_eq_outerLimit]
        exact outerSetLimit_comp_subset
          (C := fun τ ↦ svGraph (mappingDifferenceQuotient T x v τ)) (hτ.comp hφ.tendsto_atTop) h1
      rw [hd] at h2
      exact h2
    have h0H : (0 : E) ∈ svDom H := by
      refine ⟨0, (graphicalConverges_iff.1 hconv).1 0 (mem_graphicalOuterLimit_iff.2
        ⟨id, fun _ ↦ 0, fun _ ↦ 0, strictMono_id, fun n ↦ ?_, tendsto_const_nhds,
          tendsto_const_nhds⟩)⟩
      exact (mem_mappingDifferenceQuotient_iff (hpos _).ne').2 (by simpa using hv)
    have hHd := hH.eq_svSingleton_of_subset hhom hsubH h0H
    rw [hHd] at hH hconv
    exact ⟨hH, φ, hφ, hconv⟩
  have hmaxd : SvMaximalMonotone (svSingleton d) :=
    (key _ (fun n ↦ by positivity) tendsto_one_div_add_one_nhdsGT).1
  refine ⟨?_, hd ▸ hmaxd⟩
  unfold IsProtoDifferentiableAt
  rw [hd]
  refine pkConvergesAlong_iff_forall_seq.2 fun τ hτ ↦ ?_
  set τ' : ℕ → ℝ := fun n ↦ if 0 < τ n then τ n else 1 with hτ'def
  have hpos' : ∀ n, 0 < τ' n := fun n ↦ by
    simp only [τ']
    split_ifs with h
    exacts [h, one_pos]
  have heq : τ' =ᶠ[atTop] τ :=
    (hτ.eventually self_mem_nhdsWithin).mono fun n hn ↦ by
      simp only [τ', if_pos (show 0 < τ n from hn)]
  have hτ' : Tendsto τ' atTop (𝓝[>] 0) := hτ.congr' heq.symm
  have hmax' : ∀ n, SvMaximalMonotone (mappingDifferenceQuotient T x v (τ' n)) :=
    fun n ↦ hT.differenceQuotient x v (hpos' n).ne'
  have hconv' : GraphicalConverges (fun n ↦ mappingDifferenceQuotient T x v (τ' n))
      (svSingleton d) := by
    rw [graphicalConverges_iff_tendsto_resolventMap hmax' hmaxd one_pos]
    intro z
    refine Filter.tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    obtain ⟨-, φ, -, hconv⟩ := key (τ' ∘ ns) (fun n ↦ hpos' _) (hτ'.comp hns)
    exact ⟨φ, (graphicalConverges_iff_tendsto_resolventMap (fun n ↦ hmax' _) hmaxd one_pos).1
      hconv z⟩
  have hC : (fun n ↦ svGraph (mappingDifferenceQuotient T x v (τ' n))) =ᶠ[atTop]
      (fun n ↦ svGraph (mappingDifferenceQuotient T x v (τ n))) :=
    heq.mono fun n hn ↦ by simp only [hn]
  exact ⟨(innerSetLimitAlong_congr hC).symm.trans hconv'.1,
    (outerSetLimitAlong_congr hC).symm.trans hconv'.2⟩

/-- **Theorem 12.65**, the growth estimate in the proof of (b) ⇒ (a): when the
difference quotients converge graphically to a mapping with full domain,
uniform local boundedness (12.40(a)) gives `ε, δ, ρ > 0` with
`Δ_τT(x̄|v̄)(δIB) ⊂ ρIB` for `τ ∈ (0, ε)`, hence
`T(x) ⊂ v̄ + (2ρ/δ)|x - x̄|IB` near `x̄`, and `T(x) ≠ ∅` near `x̄` by 12.38. -/
theorem SvMaximalMonotone.hasMappingLinearGrowth_of_isProtoDifferentiableAt {T : E → Set E}
    (hT : SvMaximalMonotone T) {x v : E} (hv : v ∈ T x) (hp : IsProtoDifferentiableAt T x v)
    (hdom : svDom (graphicalDerivative T x v) = univ) : HasMappingLinearGrowth T x v := by
  have hbound : ∃ δ > 0, ∃ ε > 0, ∃ ρ : ℝ, ∀ τ : ℝ, 0 < τ → τ < ε → ∀ w : E, ‖w‖ < δ →
      ∀ z ∈ mappingDifferenceQuotient T x v τ w, ‖z‖ ≤ ρ := by
    by_contra hcon
    push_neg at hcon
    have hk : ∀ k : ℕ, ∃ τ : ℝ, 0 < τ ∧ τ < 1 / ((k : ℝ) + 1) ∧ ∃ w : E,
        ‖w‖ < 1 / ((k : ℝ) + 1) ∧ ∃ z ∈ mappingDifferenceQuotient T x v τ w, (k : ℝ) < ‖z‖ :=
      fun k ↦ hcon _ (by positivity) _ (by positivity) k
    choose τ hτ0 hτ1 w hw z hz hzk using hk
    have hτ : Tendsto τ atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨squeeze_zero (fun k ↦ (hτ0 k).le) (fun k ↦ (hτ1 k).le)
        tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hτ0⟩
    have hwl : Tendsto w atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun k ↦ norm_nonneg _) (fun k ↦ (hw k).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨V, hV, B, hB, -, hTV⟩ := exists_eventually_svImage_subset_of_graphicalConverges
      (fun k ↦ hT.differenceQuotient x v (hτ0 k).ne') (hp.graphicalConverges hτ)
      (by rw [hdom, interior_univ]; trivial)
    obtain ⟨R, hR⟩ := hB.subset_closedBall (0 : E)
    obtain ⟨k, hk1, hk2, hk3⟩ :=
      (hTV.and ((hwl.eventually hV).and (eventually_gt_atTop ⌈R⌉₊))).exists
    have hzB := hR (hk1 (mem_svImage.2 ⟨w k, hk2, hz k⟩))
    rw [mem_closedBall_zero_iff] at hzB
    have hRk : R < k := (Nat.le_ceil R).trans_lt (by exact_mod_cast hk3)
    linarith [hzk k]
  obtain ⟨δ, hδ, ε, hε, ρ, hρ⟩ := hbound
  have hρ0 : 0 ≤ ρ := by
    have h := hρ (ε / 2) (by positivity) (by linarith) 0 (by simpa using hδ) 0
      ((mem_mappingDifferenceQuotient_iff (by positivity)).2 (by simpa using hv))
    simpa using h
  have hgrowth : ∀ y, ‖y - x‖ < ε * δ / 2 → ∀ v' ∈ T y, ‖v' - v‖ ≤ 2 * ρ / δ * ‖y - x‖ := by
    intro y hy v' hv'
    by_cases hyx : y = x
    · subst hyx
      rw [sub_self, norm_zero, mul_zero]
      have hle : ∀ n : ℕ, ‖v' - v‖ ≤ ρ * (ε / ((n : ℝ) + 2)) := by
        intro n
        have hτn : 0 < ε / ((n : ℝ) + 2) := by positivity
        have hτε : ε / ((n : ℝ) + 2) < ε := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [n.cast_nonneg (α := ℝ)]
        have h := hρ _ hτn hτε 0 (by simpa using hδ) ((ε / ((n : ℝ) + 2))⁻¹ • (v' - v))
          ((mem_mappingDifferenceQuotient_iff hτn.ne').2
            (by rw [smul_zero, add_zero, smul_inv_smul₀ hτn.ne', add_sub_cancel]; exact hv'))
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hτn.le), inv_mul_le_iff₀ hτn] at h
        linarith
      have hlim : Tendsto (fun n : ℕ ↦ ρ * (ε / ((n : ℝ) + 2))) atTop (𝓝 0) := by
        have h := (tendsto_const_nhds (x := ε)).div_atTop
          (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
        simpa using h.const_mul ρ
      exact ge_of_tendsto' hlim hle
    · have hn : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
      set τ := 2 * ‖y - x‖ / δ with hτdef
      have hτ0 : 0 < τ := by positivity
      have hτε : τ < ε := by
        rw [hτdef, div_lt_iff₀ hδ]
        linarith
      set w := τ⁻¹ • (y - x) with hwdef
      have hw : ‖w‖ < δ := by
        rw [hwdef, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hτ0.le), hτdef, inv_div,
          div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      have hz := hρ τ hτ0 hτε w hw (τ⁻¹ • (v' - v))
        ((mem_mappingDifferenceQuotient_iff hτ0.ne').2 (by
          rw [smul_inv_smul₀ hτ0.ne', smul_inv_smul₀ hτ0.ne', add_sub_cancel, add_sub_cancel]
          exact hv'))
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hτ0.le), inv_mul_le_iff₀ hτ0] at hz
      calc ‖v' - v‖ ≤ τ * ρ := hz
        _ = 2 * ρ / δ * ‖y - x‖ := by rw [hτdef]; field_simp
  have hr : 0 < ε * δ / 2 := by positivity
  have hlb : SvLocallyBoundedAt T x := by
    refine ⟨ball x (ε * δ / 2), ball_mem_nhds _ hr,
      (isBounded_closedBall (x := v) (r := 2 * ρ / δ * (ε * δ / 2))).subset ?_⟩
    intro v' hv'
    obtain ⟨y, hy, hv'y⟩ := mem_svImage.1 hv'
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_closedBall, dist_eq_norm]
    exact (hgrowth y hy v' hv'y).trans (mul_le_mul_of_nonneg_left hy.le (by positivity))
  refine ⟨2 * ρ / δ, by positivity, ?_⟩
  filter_upwards [hT.eventually_nonempty_of_svLocallyBoundedAt ⟨v, hv⟩ hlb,
    ball_mem_nhds x hr] with y hy hyb
  rw [mem_ball, dist_eq_norm] at hyb
  exact ⟨hy, fun v' hv' ↦ hgrowth y hyb v' hv'⟩


/-- **Theorem 12.65**, (a) ⇒ (b): a semiderivative is the graphical derivative,
which is then maximal monotone (12.64), continuous and with full domain (8.43),
hence single-valued everywhere by 12.63(c). -/
theorem SvMaximalMonotone.exists_eq_svSingleton_of_hasMappingSemiderivative {T : E → Set E}
    (hT : SvMaximalMonotone T) {x v : E} (hv : v ∈ T x) {H : E → Set E}
    (hH : HasMappingSemiderivative T x v H) :
    ∃ d : E → E, graphicalDerivative T x v = svSingleton d := by
  obtain ⟨hp, hD⟩ := hH.protoDerivative
  have hmax := svMaximalMonotone_graphicalDerivative hT hv hp
  obtain ⟨-, -, hcont, hdom⟩ := hH.properties hv
  rw [← hD] at hcont hdom
  have h : ∀ w, ∃ y, graphicalDerivative T x v w = {y} := fun w ↦
    (hmax.svContinuousAt_iff_singleton (hdom ▸ mem_univ w)).1.1
      (svContinuousWithinAt_univ.1 (hcont w (mem_univ w)))
  choose d hd using h
  exact ⟨d, funext hd⟩

/-- **Theorem 12.65**, (b) ⇒ (a), with the consequences: `T` is semidifferentiable
at `x̄` for `v̄`, `T(x̄) = {v̄}`, `T` is continuous at `x̄`, `DT(x̄|v̄)` is maximal
monotone and continuous, and `T(x) ⊂ v̄ + DT(x̄|v̄)(x - x̄) + o(|x - x̄|)IB` with
`T(x) ≠ ∅` near `x̄` (8.43(e,f)). -/
theorem SvMaximalMonotone.semidifferentiability_of_eq_svSingleton {T : E → Set E}
    (hT : SvMaximalMonotone T) {x v : E} (hv : v ∈ T x) {d : E → E}
    (hd : graphicalDerivative T x v = svSingleton d) :
    HasMappingSemiderivative T x v (svSingleton d) ∧ IsProtoDifferentiableAt T x v ∧
      SvMaximalMonotone (graphicalDerivative T x v) ∧ HasMappingLinearGrowth T x v ∧
      T x = {v} ∧ SvContinuousAt T x ∧ Continuous d ∧ HasMappingFirstOrderExpansion T x v d := by
  obtain ⟨hp, hmax⟩ := hT.isProtoDifferentiableAt_of_eq_svSingleton hv hd
  have hdom : svDom (graphicalDerivative T x v) = univ := by
    rw [hd]
    exact eq_univ_of_forall fun w ↦ singleton_nonempty _
  have hg := hT.hasMappingLinearGrowth_of_isProtoDifferentiableAt hv hp hdom
  have hfib := hg.baseFiber
  obtain ⟨hc, -, he⟩ := expansion_of_graphicalDerivative_and_linearGrowth hd hg
  exact ⟨hasMappingSemiderivative_of_linearGrowth hd hg, hp, hmax, hg, hfib,
    (hT.svContinuousAt_iff_singleton ⟨v, hv⟩).1.2 ⟨v, hfib⟩, hc, he⟩

omit [FiniteDimensional ℝ E] in
/-- **Theorem 12.65**, (c) ⇒ (b): if `DR_λ(z̄_λ) = A` with an inverse `B`, then
`DT(x̄|v̄)(w) = {λ⁻¹(B(w) - w)}`, from `DR_λ(z̄_λ) = (I + λDT(x̄|v̄))⁻¹` (12.64). -/
theorem graphicalDerivative_eq_svSingleton_of_svResolvent {T : E → Set E} {x v : E} {lam : ℝ}
    (hlam : lam ≠ 0) {A B : E → E}
    (hA : graphicalDerivative (svResolvent T lam) (x + lam • v) x = svSingleton A)
    (hAB : ∀ w, A (B w) = w) (hBA : ∀ z, B (A z) = z) :
    graphicalDerivative T x v = svSingleton (fun w ↦ lam⁻¹ • (B w - w)) := by
  rw [graphicalDerivative_svResolvent T hlam x v] at hA
  funext w
  ext u
  refine (mem_svResolvent_add_smul_iff hlam).symm.trans ?_
  rw [hA]
  change w = A (w + lam • u) ↔ u = lam⁻¹ • (B w - w)
  constructor
  · intro h
    have hb : B w = w + lam • u := by
      calc B w = B (A (w + lam • u)) := by rw [← h]
        _ = w + lam • u := hBA _
    rw [hb, add_sub_cancel_left, inv_smul_smul₀ hlam]
  · intro h
    rw [h, smul_inv_smul₀ hlam, add_sub_cancel, hAB]

/-- **Theorem 12.65**, (b) ⇔ (c): `DT(x̄|v̄)` is single-valued exactly when `R_λ` is
semidifferentiable at `z̄_λ` with `DR_λ(z̄_λ)` bijective. -/
theorem SvMaximalMonotone.exists_eq_svSingleton_iff_svResolvent {T : E → Set E}
    (hT : SvMaximalMonotone T) {x v : E} (hv : v ∈ T x) {lam : ℝ} (hlam : 0 < lam) :
    (∃ d : E → E, graphicalDerivative T x v = svSingleton d) ↔
      ∃ A : E → E, HasMappingSemiderivative (svResolvent T lam) (x + lam • v) x (svSingleton A) ∧
        Function.Bijective A := by
  have hDR := graphicalDerivative_svResolvent T hlam.ne' x v
  constructor
  · rintro ⟨d, hd⟩
    have hp := (hT.isProtoDifferentiableAt_of_eq_svSingleton hv hd).1
    obtain ⟨H, hH⟩ := (hT.isProtoDifferentiableAt_iff_semidifferentiable_svResolvent hlam hv).1 hp
    obtain ⟨A, hA⟩ := (hT.semidifferentiable_svResolvent_iff hlam hv).1 ⟨H, hH⟩
    have hHA : H = svSingleton A := hH.protoDerivative.2.symm.trans hA
    rw [hHA] at hH
    have hrel : ∀ z y, y = A z ↔ y + lam • d y = z := by
      intro z y
      have h : y ∈ graphicalDerivative (svResolvent T lam) (x + lam • v) x z ↔
          y + lam • d y = z := by
        rw [hDR, hd, mem_svResolvent]
        simp only [svSingleton, mem_singleton_iff, exists_eq_left]
      rw [hA] at h
      exact h
    refine ⟨A, hH, fun z₁ z₂ h ↦ ?_, fun y ↦ ⟨y + lam • d y, ((hrel _ _).2 rfl).symm⟩⟩
    rw [← (hrel z₁ (A z₁)).1 rfl, ← (hrel z₂ (A z₂)).1 rfl, h]
  · rintro ⟨A, hH, hbij⟩
    set e := Equiv.ofBijective A hbij
    exact ⟨_, graphicalDerivative_eq_svSingleton_of_svResolvent hlam.ne' hH.protoDerivative.2
      e.apply_symm_apply e.symm_apply_apply⟩

/-- **Theorem 12.65**, (a′) ⇔ (b′): `T` is differentiable at `x̄` exactly when
`DT(x̄|v̄)` is a linear mapping. -/
theorem SvMaximalMonotone.svDifferentiableAt_iff {T : E → Set E} (hT : SvMaximalMonotone T)
    {x v : E} (hv : v ∈ T x) :
    SvDifferentiableAt T x ↔ ∃ L : E →L[ℝ] E, graphicalDerivative T x v = svSingleton L := by
  constructor
  · rintro ⟨u, L, he⟩
    obtain ⟨hD, hg⟩ := graphicalDerivative_and_linearGrowth_of_expansion L.continuous
      (svPositivelyHomogeneous_svSingleton_continuousLinearMap L) he
    have huv : v = u := by
      have h := hg.baseFiber
      rw [h] at hv
      exact hv
    subst huv
    exact ⟨L, hD⟩
  · rintro ⟨L, hL⟩
    exact ⟨v, L, (hT.semidifferentiability_of_eq_svSingleton hv hL).2.2.2.2.2.2.2⟩

/-- A linear map on a finite-dimensional space is bijective exactly when its
determinant is nonzero. -/
theorem ContinuousLinearMap.bijective_iff_det_ne_zero (L : E →L[ℝ] E) :
    Function.Bijective L ↔ L.det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ContinuousLinearMap.det,
    ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  rfl

/-- **Theorem 12.65**, (b′) ⇔ (c′): `DT(x̄|v̄)` is linear exactly when `R_λ` is
differentiable at `z̄_λ` with `∇R_λ(z̄_λ)` nonsingular. -/
theorem SvMaximalMonotone.exists_linear_iff_differentiableAt_resolventMap {T : E → Set E}
    (hT : SvMaximalMonotone T) {x v : E} (hv : v ∈ T x) {lam : ℝ} (hlam : 0 < lam) :
    (∃ L : E →L[ℝ] E, graphicalDerivative T x v = svSingleton L) ↔
      DifferentiableAt ℝ (resolventMap T lam) (x + lam • v) ∧
        (fderiv ℝ (resolventMap T lam) (x + lam • v)).det ≠ 0 := by
  have hR : resolventMap T lam (x + lam • v) = x := hT.resolventMap_add_smul hlam hv
  have hcalm : CalmAt (resolventMap T lam) (x + lam • v) :=
    ⟨1, hT.calmAtWith_resolventMap hlam _⟩
  -- the graphical derivative of the resolvent at a differentiability point
  have hderiv : ∀ hd : DifferentiableAt ℝ (resolventMap T lam) (x + lam • v),
      graphicalDerivative (svResolvent T lam) (x + lam • v) x =
        svSingleton (fderiv ℝ (resolventMap T lam) (x + lam • v)) := fun hd ↦ by
    have h := (hasFDerivAt_iff_calm_graphical.1 hd.hasFDerivAt).2
    rwa [hR, ← hT.svResolvent_eq_svSingleton hlam] at h
  constructor
  · rintro ⟨L, hL⟩
    have hd : DifferentiableAt ℝ (resolventMap T lam) (x + lam • v) :=
      (hT.differentiableAt_resolventMap_iff hlam hv).2
        ⟨LinearMap.graph (L : E →ₗ[ℝ] E), by
          rw [hL]
          ext ⟨w, u⟩
          simp [LinearMap.mem_graph_iff, svGraph, svSingleton]⟩
    obtain ⟨A, hA, hbij⟩ := (hT.exists_eq_svSingleton_iff_svResolvent hv hlam).1 ⟨L, hL⟩
    have hfA : ⇑(fderiv ℝ (resolventMap T lam) (x + lam • v)) = A := by
      have h := (hderiv hd).symm.trans hA.protoDerivative.2
      funext w
      exact singleton_eq_singleton_iff.1 (congrFun h w)
    refine ⟨hd, (ContinuousLinearMap.bijective_iff_det_ne_zero _).1 ?_⟩
    rw [hfA]
    exact hbij
  · rintro ⟨hd, hdet⟩
    set L := fderiv ℝ (resolventMap T lam) (x + lam • v) with hLdef
    have hbij := (ContinuousLinearMap.bijective_iff_det_ne_zero L).2 hdet
    set Le : E ≃L[ℝ] E :=
      (LinearEquiv.ofBijective (L : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv with hLe
    have hLe_apply : ∀ w, Le w = L w := fun w ↦ rfl
    refine ⟨lam⁻¹ • ((Le.symm : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E), ?_⟩
    have h := graphicalDerivative_eq_svSingleton_of_svResolvent (T := T) (x := x) (v := v)
      hlam.ne' (hderiv hd) (B := Le.symm)
      (fun w ↦ by rw [← hLe_apply, Le.apply_symm_apply])
      (fun z ↦ by rw [← hLe_apply, Le.symm_apply_apply])
    rw [h]
    rfl

/-- **Theorem 12.65 (differentiability and semidifferentiability)**.  For maximal
monotone `T`, `v̄ ∈ T(x̄)` and `λ > 0`, with `R_λ = (I + λT)⁻¹` and
`z̄_λ = x̄ + λv̄`, the following are equivalent: (a) `T` is semidifferentiable at
`x̄` for `v̄`; (b) `DT(x̄|v̄)` is single-valued; (c) `R_λ` is semidifferentiable at
`z̄_λ` with `DR_λ(z̄_λ)` bijective.  They imply that `T` is continuous at `x̄` with
`T(x̄) = {v̄}`, that `DT(x̄|v̄)` is maximal monotone and continuous, and that
`T(x) ⊂ v̄ + DT(x̄|v̄)(x - x̄) + o(|x - x̄|)IB` (with `T(x) ≠ ∅`) near `x̄`.  The
more special properties are equivalent as well: (a′) `T` is differentiable at
`x̄`; (b′) `DT(x̄|v̄)` is linear; (c′) `R_λ` is differentiable at `z̄_λ` with
`∇R_λ(z̄_λ)` nonsingular. -/
theorem differentiability_and_semidifferentiability {T : E → Set E} (hT : SvMaximalMonotone T)
    {x v : E} (hv : v ∈ T x) {lam : ℝ} (hlam : 0 < lam) :
    List.TFAE [∃ H, HasMappingSemiderivative T x v H,
      ∃ d : E → E, graphicalDerivative T x v = svSingleton d,
      ∃ A : E → E, HasMappingSemiderivative (svResolvent T lam) (x + lam • v) x (svSingleton A) ∧
        Function.Bijective A] ∧
    ((∃ H, HasMappingSemiderivative T x v H) →
      SvContinuousAt T x ∧ T x = {v} ∧ SvMaximalMonotone (graphicalDerivative T x v) ∧
        ∃ d : E → E, graphicalDerivative T x v = svSingleton d ∧ Continuous d ∧
          HasMappingFirstOrderExpansion T x v d) ∧
    List.TFAE [SvDifferentiableAt T x,
      ∃ L : E →L[ℝ] E, graphicalDerivative T x v = svSingleton L,
      DifferentiableAt ℝ (resolventMap T lam) (x + lam • v) ∧
        (fderiv ℝ (resolventMap T lam) (x + lam • v)).det ≠ 0] := by
  refine ⟨?_, fun ⟨H, hH⟩ ↦ ?_, ?_⟩
  · tfae_have 1 → 2 := fun ⟨H, hH⟩ ↦ hT.exists_eq_svSingleton_of_hasMappingSemiderivative hv hH
    tfae_have 2 → 1 := fun ⟨d, hd⟩ ↦ ⟨_, (hT.semidifferentiability_of_eq_svSingleton hv hd).1⟩
    tfae_have 2 ↔ 3 := hT.exists_eq_svSingleton_iff_svResolvent hv hlam
    tfae_finish
  · obtain ⟨d, hd⟩ := hT.exists_eq_svSingleton_of_hasMappingSemiderivative hv hH
    obtain ⟨-, -, hmax, -, hfib, hcont, hc, he⟩ := hT.semidifferentiability_of_eq_svSingleton hv hd
    exact ⟨hcont, hfib, hmax, d, hd, hc, he⟩
  · tfae_have 1 ↔ 2 := hT.svDifferentiableAt_iff hv
    tfae_have 2 ↔ 3 := hT.exists_linear_iff_differentiableAt_resolventMap hv hlam
    tfae_finish

end MaximalMonotone

end RW
