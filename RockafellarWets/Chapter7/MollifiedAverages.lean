/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Functions mollified by averaging

Example 7.19 uses nonnegative bounded measurable probability kernels.
Their supports form a bounded sequence converging to the origin in the
Painlevé–Kuratowski sense. Smoothness of the kernels is unnecessary.
-/

import RockafellarWets.Chapter7.EpiLimits
import RockafellarWets.Chapter7.ExtendedUniformConvergence
import Mathlib.Analysis.Convolution

open Bornology Filter Function MeasureTheory Metric Set Topology
open scoped Convolution

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

/-- The hypotheses on the kernels in Example 7.19, for a translation-invariant
reference measure (in particular Lebesgue measure in Euclidean space). -/
structure IsBoundedMollifierSequence (ψ : ℕ → E → ℝ) (μ : Measure E) : Prop where
  nonneg : ∀ n z, 0 ≤ ψ n z
  measurable : ∀ n, Measurable (ψ n)
  bounded : ∀ n, ∃ M : ℝ, ∀ z, ψ n z ≤ M
  integral_eq_one : ∀ n, ∫ z, ψ n z ∂μ = 1
  bounded_supports : IsBounded (⋃ n, support (ψ n))
  converges_supports : PKConverges (fun n ↦ support (ψ n)) {0}

variable {ψ : ℕ → E → ℝ} {μ : Measure E}

omit [BorelSpace E] in
/-- The support of a bounded mollifier is eventually contained in each
neighborhood of the origin. -/
theorem IsBoundedMollifierSequence.tendsto_support_smallSets (hψ : IsBoundedMollifierSequence ψ μ) :
    Tendsto (fun n ↦ support (ψ n)) atTop (𝓝 (0 : E)).smallSets := by
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : E)).mp hψ.bounded_supports
  have h := (outerSetLimit_subset_iff_eventuallyOuterApproximates isClosed_singleton).mp
    hψ.converges_supports.outer_eq.subset
  apply tendsto_smallSets_iff.mpr
  intro U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  filter_upwards [h (max R 0 + 1) (by positivity) r hr] with n hn
  intro z hz
  have hzb := hR (mem_iUnion.mpr ⟨n, hz⟩)
  have hz' := hn ⟨hz, closedBall_subset_closedBall (by linarith [le_max_left R 0]) hzb⟩
  obtain ⟨_, hzero, hd⟩ := mem_thickening_iff.mp hz'
  rw [mem_singleton_iff] at hzero
  exact hball (hzero ▸ hd)

/-- The average of the translates of `f` with weight `ψ`. -/
noncomputable def mollifiedAverage (μ : Measure E) (ψ f : E → ℝ) (x : E) : ℝ :=
  ∫ z, ψ z * f (x - z) ∂μ

variable [μ.IsAddLeftInvariant] [SFinite μ]

omit [SFinite μ] in
theorem IsBoundedMollifierSequence.integrable_average [μ.IsNegInvariant]
    (hψ : IsBoundedMollifierSequence ψ μ) {f : E → ℝ} (hf : LocallyIntegrable f μ)
    (n : ℕ) (x : E) : Integrable (fun z ↦ ψ n z * f (x - z)) μ := by
  classical
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : E)).mp hψ.bounded_supports
  let K := closedBall x R
  have hK : Integrable (K.indicator f) μ :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (hf.integrableOn_isCompact (isCompact_closedBall x R))
  obtain ⟨M, hM⟩ := hψ.bounded n
  have h := (hK.comp_sub_left x).bdd_mul (hψ.measurable n).aestronglyMeasurable
    (.of_forall fun z ↦ show ‖ψ n z‖ ≤ M by rw [Real.norm_of_nonneg (hψ.nonneg n z)]; exact hM z)
  apply h.congr (.of_forall fun z ↦ ?_)
  by_cases hz : z ∈ support (ψ n)
  · have hd := hR (mem_iUnion.mpr ⟨n, hz⟩)
    have hmem : x - z ∈ K := by simpa [K, mem_closedBall, dist_eq_norm] using hd
    simp [hmem]
  · simp [notMem_support.mp hz]

/-- **Example 7.19(a).** The averages converge along every incoming
sequence at each continuity point. -/
theorem IsBoundedMollifierSequence.tendsto_mollifiedAverage
    (hψ : IsBoundedMollifierSequence ψ μ) {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {x : E} (hc : ContinuousAt f x) {z : ℕ → E} (hz : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n ↦ mollifiedAverage μ (ψ n) f (z n)) atTop (𝓝 (f x)) := by
  apply convolution_tendsto_right (.of_forall hψ.nonneg) (.of_forall hψ.integral_eq_one)
    hψ.tendsto_support_smallSets (.of_forall fun _ ↦ hf.aestronglyMeasurable) _ hz
  exact hc.tendsto.comp tendsto_snd

/-- The compact-uniform conclusion in 7.19(a), in the ordinary bounded
sense since a continuous real-valued function is bounded on a compact set. -/
theorem IsBoundedMollifierSequence.tendstoUniformlyOn_mollifiedAverage
    (hψ : IsBoundedMollifierSequence ψ μ) {f : E → ℝ} (hf : LocallyIntegrable f μ)
    {B : Set E} (hB : IsCompact B) (hc : ∀ x ∈ B, ContinuousAt f x) :
    TendstoUniformlyOn (fun n ↦ mollifiedAverage μ (ψ n) f) f atTop B := by
  have hcc : ∀ x ∈ B, ConvergesContinuouslyWithinAt
      (fun n y ↦ (mollifiedAverage μ (ψ n) f y : EReal)) (fun y ↦ (f y : EReal)) B x := by
    intro x hx z _ hz
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp
      (hψ.tendsto_mollifiedAverage hf (hc x hx) hz)
  have hu := (convergesContinuouslyOn_iff_continuousOn_and_erealConvergesUniformlyOn.mp hcc).2
    B Subset.rfl hB
  obtain ⟨M, hM⟩ := hB.bddAbove_image
    (continuous_abs.comp_continuousOn (fun x hx ↦ (hc x hx).continuousWithinAt))
  exact hu.tendstoUniformlyOn_of_bounded (le_max_left 0 M)
    (fun x hx ↦ (hM (mem_image_of_mem _ hx)).trans (le_max_right ..))

omit [SFinite μ] in
/-- Nonnegativity and unit integral preserve any local strict lower bound,
eventually along a sequence of approaching centers. -/
private theorem eventually_le_mollifiedAverage [μ.IsNegInvariant] (hψ : IsBoundedMollifierSequence ψ μ)
    {f : E → ℝ} (hf : LocallyIntegrable f μ) {x : E} (hl : LowerSemicontinuousAt f x)
    {m : ℝ} (hm : m < f x) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {z : ℕ → E} (hz : Tendsto z atTop (𝓝 x)) :
    ∀ᶠ n in atTop, m ≤ mollifiedAverage μ (ψ (φ n)) f (z n) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hl m hm)
  have hshr := (tendsto_smallSets_iff.mp hψ.tendsto_support_smallSets) (ball 0 (r / 2))
    (ball_mem_nhds _ (half_pos hr))
  filter_upwards [hφ.tendsto_atTop.eventually hshr,
    hz.eventually_mem (ball_mem_nhds x (half_pos hr))] with n hn hzn
  have hb : ∀ y, ψ (φ n) y * m ≤ ψ (φ n) y * f (z n - y) := by
    intro y
    by_cases hy : y ∈ support (ψ (φ n))
    · have hd : dist (z n - y) (z n) = ‖y‖ := by simp
      have hy' := mem_ball_zero_iff.mp (hn hy)
      have hmem : z n - y ∈ ball x r := calc
        dist (z n - y) x ≤ dist (z n - y) (z n) + dist (z n) x := dist_triangle ..
        _ < r := by rw [hd]; linarith [show dist (z n) x < r / 2 from hzn]
      exact mul_le_mul_of_nonneg_left (hball hmem).le (hψ.nonneg ..)
    · simp [notMem_support.mp hy]
  have hi := integral_mono ((integrable_of_integral_eq_one (hψ.integral_eq_one (φ n))).mul_const m)
    (hψ.integrable_average hf (φ n) (z n)) hb
  simpa [mollifiedAverage, integral_mul_const, hψ.integral_eq_one] using hi

/-- **Example 7.19(b).** A lower semicontinuous function determined by its
lower limits along continuity points is the epi-limit of its averages. -/
theorem IsBoundedMollifierSequence.epiConverges_mollifiedAverage [μ.IsNegInvariant]
    (hψ : IsBoundedMollifierSequence ψ μ) {f : E → ℝ} (hf : LocallyIntegrable f μ)
    (hl : LowerSemicontinuous f)
    (hdet : ∀ x, (f x : EReal) = liminf (fun y ↦ (f y : EReal))
      (𝓝[{y | ContinuousAt f y}] x)) :
    EpiConverges (fun n x ↦ (mollifiedAverage μ (ψ n) f x : EReal)) (fun x ↦ (f x : EReal)) := by
  let S := fun n ↦ epigraph (fun x ↦ (mollifiedAverage μ (ψ n) f x : EReal))
  let T := epigraph (fun x ↦ (f x : EReal))
  have ho : outerSetLimit S ⊆ T := by
    rintro ⟨x, t⟩ hp
    obtain ⟨φ, p, hφ, hpS, hpx⟩ := mem_outerSetLimit_iff_exists_subsequence.mp hp
    apply EReal.coe_le_coe_iff.mpr
    by_contra! hlt
    obtain ⟨m, htm, hmf⟩ := exists_between hlt
    have hev := eventually_le_mollifiedAverage hψ hf (hl x) hmf hφ hpx.fst_nhds
    apply htm.not_ge
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hpx.snd_nhds
    exact hev.mono fun n hn ↦ hn.trans (EReal.coe_le_coe_iff.mp (hpS n))
  have hi : T ⊆ innerSetLimit S := by
    rintro ⟨x, t⟩ ht
    rw [← (isClosed_innerSetLimit S).closure_eq, mem_closure_iff_nhds]
    intro W hW
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hW
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
    let s := t + r / 2
    have hts : t < s := by dsimp [s]; linarith
    have hsV : s ∈ V := hrV (by simp [s, mem_ball, abs_of_pos hr, half_lt_self hr])
    have hlt : liminf (fun y ↦ (f y : EReal)) (𝓝[{y | ContinuousAt f y}] x) < (s : EReal) :=
      (hdet x ▸ (show (f x : EReal) ≤ (t : EReal) from ht)).trans_lt (EReal.coe_lt_coe_iff.mpr hts)
    have hnear : U ∩ {y | ContinuousAt f y} ∈ 𝓝[{y | ContinuousAt f y}] x :=
      inter_mem (nhdsWithin_le_nhds hU) self_mem_nhdsWithin
    obtain ⟨y, hyf, hy⟩ := (((frequently_lt_of_liminf_lt) hlt).and_eventually hnear).exists
    refine ⟨(y, s), hUV ⟨hy.1, hsV⟩, ?_⟩
    intro W' hW'
    have hconv := hψ.tendsto_mollifiedAverage hf hy.2 (tendsto_const_nhds (x := y))
    filter_upwards [hconv.eventually_lt_const (EReal.coe_lt_coe_iff.mp hyf)] with n hn
    exact ⟨(y, s), EReal.coe_le_coe_iff.mpr hn.le, mem_of_mem_nhds hW'⟩
  have hio := innerSetLimit_subset_outerSetLimit S
  exact ⟨(hio.trans ho).antisymm hi, ho.antisymm (hi.trans hio)⟩

end RW
