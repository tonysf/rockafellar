/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Subdifferential criteria for strict continuity
-/

import RockafellarWets.Chapter9.StrictContinuityFromSlopes
import RockafellarWets.Chapter8.SubgradientExistence
import RockafellarWets.Chapter8.RegularSubderivativeSupport
import RockafellarWets.Chapter8.SupportPolarity

open Filter Function Metric Set Topology Bornology
open scoped ENNReal NNReal InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → EReal} {x : E} {c : ℝ}

theorem norm_le_of_mem_subdifferential_of_lipschitzOnWith {U : Set E} {k : ℝ≥0}
    (hU : IsOpen U) (hfin : ∀ y ∈ U, f y = ((f y).toReal : EReal))
    (hf : LipschitzOnWith k (fun y ↦ (f y).toReal) U) {y v : E} (hy : y ∈ U)
    (hv : v ∈ subdifferential f y) : ‖v‖ ≤ k := by
  have hreg {a w : E} (ha : a ∈ U) (hw : w ∈ regularSubdifferential f a) : ‖w‖ ≤ k := by
    have h := EReal.coe_le_coe_iff.mp ((inner_le_subderivative_of_mem_regularSubdifferential hw w).trans
      (subderivative_bounds_of_lipschitzOnWith hfin hf (hU.mem_nhds ha) w).2)
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg w, k.coe_nonneg]
  obtain ⟨_, a, w, ha, _, hw, hlim⟩ := mem_subdifferential_iff_exists_seq.mp hv
  exact le_of_tendsto hlim.norm ((ha.eventually (hU.mem_nhds hy)).mono fun n hn ↦ hreg hn (hw n))

theorem ERealStrictlyContinuousAt.locallyBoundedAt_subdifferential (h : ERealStrictlyContinuousAt f x) :
    SvLocallyBoundedAt (subdifferential f) x := by
  obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.2
  obtain ⟨U, hu, hU, hfin, hL⟩ := h.exists_lipschitzOnWith hk
  refine ⟨U, hu, (isBounded_closedBall (x := (0 : E)) (r := k)).subset ?_⟩
  intro v hv
  obtain ⟨y, hy, hv⟩ := mem_svImage.mp hv
  exact mem_closedBall_zero_iff.mpr (norm_le_of_mem_subdifferential_of_lipschitzOnWith hU hfin hL hy hv)

theorem locallyBoundedAt_regularSubdifferential_of_subdifferential
    (h : SvLocallyBoundedAt (subdifferential f) x) : SvLocallyBoundedAt (regularSubdifferential f) x := by
  obtain ⟨U, hu, hb⟩ := h
  refine ⟨U, hu, hb.subset ?_⟩
  intro v hv
  obtain ⟨y, hy, hv⟩ := mem_svImage.mp hv
  exact mem_svImage.mpr ⟨y, hy, regularSubdifferential_subset_subdifferential f y hv⟩

theorem horizonSubdifferential_eq_zero_of_locallyBoundedAt_regularSubdifferential (hx : f x = c)
    (h : SvLocallyBoundedAt (regularSubdifferential f) x) : horizonSubdifferential f x = {0} := by
  obtain ⟨U, hu, R, hR⟩ : ∃ U ∈ 𝓝 x, ∃ R : ℝ, ∀ w ∈ svImage (regularSubdifferential f) U, ‖w‖ ≤ R := by
    obtain ⟨U, hU, hb⟩ := h
    exact ⟨U, hU, hb.exists_norm_le⟩
  ext v
  rw [mem_horizonSubdifferential_iff_zero_or_scaledSeq hx, mem_singleton_iff]
  refine ⟨?_, Or.inl⟩
  rintro (h | ⟨y,w,t,hy,hw,ht,ht₀,hv⟩)
  · exact h
  · apply norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg v))
    have hlim : Tendsto (fun n ↦ t n * R) atTop (𝓝 0) := by simpa using ht₀.mul_const R
    apply le_of_tendsto_of_tendsto hv.norm hlim
    filter_upwards [(tendsto_attentiveNhds_iff.mp hy).1.eventually hu] with n hn
    rw [norm_smul_of_nonneg (ht n).le]
    exact mul_le_mul_of_nonneg_left (hR _ (mem_svImage.mpr ⟨y n, hn, hw n⟩)) (ht n).le

variable [FiniteDimensional ℝ E]

theorem subdifferential_nonempty_compact_of_horizon_eq_zero (hx : f x = c) (hl : IsLocallyLscAt f x)
    (h : horizonSubdifferential f x = {0}) : (subdifferential f x).Nonempty ∧ IsCompact (subdifferential f x) := by
  have hc : IsClosed (cosmicSet (subdifferential f x) (horizonSubdifferential f x)) := by
    rw [cosmicSet_subdifferential hx]
    exact isClosed_outerSetLimitAlong _ _
  have hh := (isClosed_cosmicSet_iff (subdifferential_properties hx).2.2.2.2.1).mp hc
  rw [h] at hh
  refine ⟨(subdifferential_nonempty_or_exists_nonzero_horizon hl hx).resolve_right ?_,
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hh.1, isBounded_iff_horizonCone_eq_singleton_zero.mpr
      (Subset.antisymm hh.2.2 (singleton_subset_iff.mpr (zero_mem_horizonCone _)))⟩⟩
  rintro ⟨v,hv,hne⟩
  exact hne (h ▸ hv : v ∈ ({0} : Set E))

theorem regularSubderivative_finite_of_horizon_eq_zero (hx : f x = c) (hl : IsLocallyLscAt f x)
    (h : horizonSubdifferential f x = {0}) (w : E) : ∃ r : ℝ, regularSubderivative f x w = r := by
  obtain ⟨hne, hcomp⟩ := subdifferential_nonempty_compact_of_horizon_eq_zero hx hl h
  rw [regularSubderivative_eq_supportFunction_of_mem_polar hx hl (by rw [h, polarCone_singleton_zero]; trivial)]
  exact (nonempty_bounded_iff_supportFunction_finite _).mp ⟨hne,hcomp.isBounded⟩ w

private theorem strictlyContinuous_of_regular_lt_top (hx : f x = c) (hl : IsLocallyLscAt f x)
    (h : ∀ w, regularSubderivative f x w < ⊤) : ERealStrictlyContinuousAt f x := by
  apply eRealStrictlyContinuousAt_of_interior_regularSubderivative hx hl
  rw [show effectiveDomain (regularSubderivative f x) = univ from eq_univ_iff_forall.mpr h, interior_univ]
  trivial

/-- **Theorem 9.13(a,b)**. Local lower semicontinuity identifies strict
continuity with the absence of nonzero horizon subgradients. -/
theorem eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero (hx : f x = c) (hl : IsLocallyLscAt f x) :
    ERealStrictlyContinuousAt f x ↔ horizonSubdifferential f x = {0} := by
  refine ⟨fun h ↦ horizonSubdifferential_eq_zero_of_locallyBoundedAt_regularSubdifferential hx
    (locallyBoundedAt_regularSubdifferential_of_subdifferential h.locallyBoundedAt_subdifferential), ?_⟩
  intro h
  apply strictlyContinuous_of_regular_lt_top hx hl fun w ↦ ?_
  obtain ⟨r, hr⟩ := regularSubderivative_finite_of_horizon_eq_zero hx hl h w
  exact hr ▸ EReal.coe_lt_top _

/-- **Theorem 9.13(c)**. -/
theorem eRealStrictlyContinuousAt_iff_locallyBoundedAt_regularSubdifferential (hx : f x = c) (hl : IsLocallyLscAt f x) :
    ERealStrictlyContinuousAt f x ↔ SvLocallyBoundedAt (regularSubdifferential f) x :=
  ⟨fun h ↦ locallyBoundedAt_regularSubdifferential_of_subdifferential h.locallyBoundedAt_subdifferential,
    fun h ↦ (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero hx hl).mpr
      (horizonSubdifferential_eq_zero_of_locallyBoundedAt_regularSubdifferential hx h)⟩

/-- **Theorem 9.13(d)**. -/
theorem eRealStrictlyContinuousAt_iff_locallyBoundedAt_subdifferential (hx : f x = c) (hl : IsLocallyLscAt f x) :
    ERealStrictlyContinuousAt f x ↔ SvLocallyBoundedAt (subdifferential f) x :=
  ⟨ERealStrictlyContinuousAt.locallyBoundedAt_subdifferential, fun h ↦
    (eRealStrictlyContinuousAt_iff_locallyBoundedAt_regularSubdifferential hx hl).mpr
      (locallyBoundedAt_regularSubdifferential_of_subdifferential h)⟩

/-- **Theorem 9.13(e)**. -/
theorem eRealStrictlyContinuousAt_iff_regularSubderivative_finite (hx : f x = c) (hl : IsLocallyLscAt f x) :
    ERealStrictlyContinuousAt f x ↔ ∀ w, ∃ r : ℝ, regularSubderivative f x w = r := by
  refine ⟨fun h ↦ regularSubderivative_finite_of_horizon_eq_zero hx hl
    ((eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero hx hl).mp h), ?_⟩
  intro h
  apply strictlyContinuous_of_regular_lt_top hx hl fun w ↦ ?_
  obtain ⟨r,hr⟩ := h w
  exact hr ▸ EReal.coe_lt_top _

/-- **Theorem 9.13(f)**. The upper bounds on ordinary subderivatives can
depend on the direction, on a different neighborhood for every direction. -/
theorem eRealStrictlyContinuousAt_iff_subderivative_locally_bddAbove (hx : f x = c) (hl : IsLocallyLscAt f x) :
    ERealStrictlyContinuousAt f x ↔ (∀ᶠ y in 𝓝 x, f y = ((f y).toReal : EReal)) ∧
      ∀ w, ∃ b : ℝ, ∀ᶠ y in 𝓝 x, subderivative f y w ≤ (b : EReal) := by
  constructor
  · intro h
    obtain ⟨k, hk, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h.2
    obtain ⟨U, hu, hU, hfin, hL⟩ := h.exists_lipschitzOnWith hk
    exact ⟨h.1, fun w ↦ ⟨k * ‖w‖, (show ∀ᶠ y in 𝓝 x, y ∈ U from hu).mono
      fun y hy ↦ (subderivative_bounds_of_lipschitzOnWith hfin hL (hU.mem_nhds hy) w).2⟩⟩
  · rintro ⟨-, h⟩
    apply strictlyContinuous_of_regular_lt_top hx hl fun w ↦ ?_
    obtain ⟨b, hb⟩ := h w
    apply lt_of_le_of_lt _ (EReal.coe_lt_top b)
    change (w,b) ∈ epigraph (regularSubderivative f x)
    rw [epigraph_regularSubderivative_eq_inner_epigraph_subderivative hl]
    intro V hV
    filter_upwards [hb.filter_mono (show attentiveNhds f x ≤ 𝓝 x from inf_le_left)] with y hy
    exact ⟨(w,b), hy, mem_of_mem_nhds hV⟩

end RW
