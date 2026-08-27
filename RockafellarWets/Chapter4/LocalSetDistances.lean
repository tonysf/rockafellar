/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Local Set Distances

This file defines the two radius-dependent set distances in formula 4(11)
and proves Theorems 4.35--4.36 together with the basic estimates in
Proposition 4.37 and Corollary 4.38.
-/

import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.BundledFun
import Mathlib.Topology.Order.MonotoneConvergence
import RockafellarWets.Chapter4.DistanceFunctionRelations
import RockafellarWets.Chapter4.HausdorffConvergence
import RockafellarWets.Chapter4.UniformApproximation

open Bornology Filter Function Metric Set Topology
open scoped ENNReal NNReal

namespace RW

/-- The space `cl-sets≠∅(E)` used in Chapter 4: nonempty closed subsets of
the ambient space. -/
def ClosedNonemptySet (E : Type*) [TopologicalSpace E] :=
  {C : Set E // IsClosed C ∧ C.Nonempty}

namespace ClosedNonemptySet

variable {E : Type*} [TopologicalSpace E]

instance : SetLike (ClosedNonemptySet E) E where
  coe C := C.1
  coe_injective' _ _ h := Subtype.ext h

theorem isClosed (C : ClosedNonemptySet E) : IsClosed (C : Set E) := C.property.1

theorem nonempty (C : ClosedNonemptySet E) : (C : Set E).Nonempty := C.property.2

end ClosedNonemptySet

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The distance function of `C`, restricted to the closed ball of radius
`ρ`, regarded as a continuous function on a compact space. -/
noncomputable def distanceProfile (ρ : ℝ≥0) (C : Set E) :
    C(closedBall (0 : E) (ρ : ℝ), ℝ) where
  toFun x := infDist (x : E) C
  continuous_toFun := (continuous_infDist_pt C).comp continuous_subtype_val

/-- Formula 4(11): the `ρ`-distance, i.e. the uniform distance between the
two point-to-set distance functions on `ρ ℝ`. -/
noncomputable def rhoDistance (ρ : ℝ≥0) (C D : Set E) : ℝ :=
  dist (distanceProfile ρ C) (distanceProfile ρ D)

/-- Formula 4(11), extended-valued backend for the truncated-inclusion
distance.  The real-valued book version is `rhoHatDistance`. -/
noncomputable def rhoHatEDistance (ρ : ℝ≥0) (C D : Set E) : ℝ≥0∞ :=
  (⨆ x ∈ C ∩ closedBall (0 : E) (ρ : ℝ), infEDist x D) ⊔
    ⨆ y ∈ D ∩ closedBall (0 : E) (ρ : ℝ), infEDist y C

/-- Formula 4(11): the least simultaneous enlargement needed to cover both
ball truncations by the other set.  Nonempty target sets make this finite. -/
noncomputable def rhoHatDistance (ρ : ℝ≥0) (C D : Set E) : ℝ :=
  (rhoHatEDistance ρ C D).toReal

theorem rhoDistance_nonneg (ρ : ℝ≥0) (C D : Set E) :
    0 ≤ rhoDistance ρ C D :=
  dist_nonneg

theorem rhoDistance_self (ρ : ℝ≥0) (C : Set E) : rhoDistance ρ C C = 0 := by
  simp only [rhoDistance, dist_self]

theorem rhoDistance_comm (ρ : ℝ≥0) (C D : Set E) :
    rhoDistance ρ C D = rhoDistance ρ D C := by
  exact dist_comm _ _

theorem rhoDistance_triangle (ρ : ℝ≥0) (C₁ C₂ C₃ : Set E) :
    rhoDistance ρ C₁ C₃ ≤ rhoDistance ρ C₁ C₂ + rhoDistance ρ C₂ C₃ :=
  dist_triangle _ _ _

/-- Theorem 4.36, pseudo-metric clause, packaged as Mathlib's bundled
`PseudoMetric`. -/
noncomputable def rhoPseudoMetric (ρ : ℝ≥0) :
    PseudoMetric (ClosedNonemptySet E) ℝ where
  toFun C D := rhoDistance ρ (C : Set E) (D : Set E)
  refl' C := rhoDistance_self ρ (C : Set E)
  symm' C D := rhoDistance_comm ρ (C : Set E) (D : Set E)
  triangle' C D F := rhoDistance_triangle ρ (C : Set E) (D : Set E) (F : Set E)

theorem abs_infDist_sub_infDist_le_rhoDistance
    (ρ : ℝ≥0) (C D : Set E) {x : E}
    (hx : x ∈ closedBall (0 : E) (ρ : ℝ)) :
    |infDist x C - infDist x D| ≤ rhoDistance ρ C D := by
  simpa only [rhoDistance, distanceProfile, Real.dist_eq] using
    (ContinuousMap.dist_apply_le_dist
      (f := distanceProfile ρ C) (g := distanceProfile ρ D) ⟨x, hx⟩)

theorem rhoDistance_le_iff {e : ℝ} (he : 0 ≤ e)
    (ρ : ℝ≥0) (C D : Set E) :
    rhoDistance ρ C D ≤ e ↔
      ∀ x ∈ closedBall (0 : E) (ρ : ℝ),
        |infDist x C - infDist x D| ≤ e := by
  rw [rhoDistance, ContinuousMap.dist_le he]
  constructor
  · intro h x hx
    simpa only [distanceProfile, Real.dist_eq] using h ⟨x, hx⟩
  · rintro h ⟨x, hx⟩
    simpa only [distanceProfile, Real.dist_eq] using h x hx

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem rhoHatEDistance_le_iff (ρ : ℝ≥0) (C D : Set E) {e : ℝ} :
    rhoHatEDistance ρ C D ≤ ENNReal.ofReal e ↔
      C ∩ closedBall (0 : E) (ρ : ℝ) ⊆ cthickening e D ∧
        D ∩ closedBall (0 : E) (ρ : ℝ) ⊆ cthickening e C := by
  simp only [rhoHatEDistance, sup_le_iff, iSup_le_iff, mem_cthickening_iff,
    Set.subset_def]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem localExcessEDistance_ne_top
    (ρ : ℝ≥0) (C : Set E) {D : Set E} (hDne : D.Nonempty) :
    (⨆ x ∈ C ∩ closedBall (0 : E) (ρ : ℝ), infEDist x D) ≠ ⊤ := by
  rcases hDne with ⟨y, hyD⟩
  refine ne_top_of_le_ne_top
    (ENNReal.ofReal_ne_top : ENNReal.ofReal ((ρ : ℝ) + ‖y‖) ≠ ⊤) ?_
  refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
  calc
    infEDist x D ≤ edist x y := infEDist_le_edist_of_mem hyD
    _ = ENNReal.ofReal (dist x y) := by rw [edist_dist]
    _ ≤ ENNReal.ofReal ((ρ : ℝ) + ‖y‖) := ENNReal.ofReal_le_ofReal <| by
      rw [mem_inter_iff, mem_closedBall, dist_zero_right] at hx
      calc
        dist x y ≤ ‖x‖ + ‖y‖ := by
          rw [dist_eq_norm]
          exact norm_sub_le _ _
        _ ≤ (ρ : ℝ) + ‖y‖ := by linarith [hx.2]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem rhoHatEDistance_ne_top
    (ρ : ℝ≥0) {C D : Set E} (hCne : C.Nonempty) (hDne : D.Nonempty) :
    rhoHatEDistance ρ C D ≠ ⊤ := by
  rw [rhoHatEDistance]
  exact (sup_lt_iff.2 ⟨
    (lt_top_iff_ne_top.2 (localExcessEDistance_ne_top ρ C hDne)),
    (lt_top_iff_ne_top.2 (localExcessEDistance_ne_top ρ D hCne))⟩).ne

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem rhoHatDistance_nonneg (ρ : ℝ≥0) (C D : Set E) :
    0 ≤ rhoHatDistance ρ C D :=
  ENNReal.toReal_nonneg

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem rhoHatDistance_le_iff
    (ρ : ℝ≥0) {C D : Set E} (hCne : C.Nonempty) (hDne : D.Nonempty)
    {e : ℝ} (he : 0 ≤ e) :
    rhoHatDistance ρ C D ≤ e ↔
      C ∩ closedBall (0 : E) (ρ : ℝ) ⊆ cthickening e D ∧
        D ∩ closedBall (0 : E) (ρ : ℝ) ⊆ cthickening e C := by
  change (rhoHatEDistance ρ C D).toReal ≤ e ↔ _
  rw [← ENNReal.le_ofReal_iff_toReal_le
    (rhoHatEDistance_ne_top ρ hCne hDne) he]
  exact rhoHatEDistance_le_iff ρ C D

theorem rhoDistance_mono {r s : ℝ≥0} (hrs : r ≤ s) (C D : Set E) :
    rhoDistance r C D ≤ rhoDistance s C D := by
  apply (rhoDistance_le_iff (rhoDistance_nonneg s C D) r C D).2
  intro x hx
  exact abs_infDist_sub_infDist_le_rhoDistance s C D
    (closedBall_subset_closedBall (mod_cast hrs) hx)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem rhoHatEDistance_mono {r s : ℝ≥0} (hrs : r ≤ s) (C D : Set E) :
    rhoHatEDistance r C D ≤ rhoHatEDistance s C D := by
  simp only [rhoHatEDistance]
  apply sup_le
  · refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
    have hx' : x ∈ C ∩ closedBall (0 : E) (s : ℝ) :=
      ⟨hx.1, closedBall_subset_closedBall (mod_cast hrs) hx.2⟩
    have hinner : infEDist x D ≤
        ⨆ (_ : x ∈ C ∩ closedBall (0 : E) (s : ℝ)), infEDist x D :=
      le_iSup (fun _ : x ∈ C ∩ closedBall (0 : E) (s : ℝ) ↦ infEDist x D) hx'
    exact (hinner.trans (le_iSup (fun z : E ↦
      ⨆ (_ : z ∈ C ∩ closedBall (0 : E) (s : ℝ)), infEDist z D) x)).trans le_sup_left
  · refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
    have hx' : x ∈ D ∩ closedBall (0 : E) (s : ℝ) :=
      ⟨hx.1, closedBall_subset_closedBall (mod_cast hrs) hx.2⟩
    have hinner : infEDist x C ≤
        ⨆ (_ : x ∈ D ∩ closedBall (0 : E) (s : ℝ)), infEDist x C :=
      le_iSup (fun _ : x ∈ D ∩ closedBall (0 : E) (s : ℝ) ↦ infEDist x C) hx'
    exact (hinner.trans (le_iSup (fun z : E ↦
      ⨆ (_ : z ∈ D ∩ closedBall (0 : E) (s : ℝ)), infEDist z C) x)).trans le_sup_right

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem rhoHatDistance_mono {r s : ℝ≥0} (hrs : r ≤ s)
    {C D : Set E} (hCne : C.Nonempty) (hDne : D.Nonempty) :
    rhoHatDistance r C D ≤ rhoHatDistance s C D :=
  ENNReal.toReal_mono (rhoHatEDistance_ne_top s hCne hDne)
    (rhoHatEDistance_mono hrs C D)

end Definitions

section UniformDistanceConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem PKConverges.tendsto_infDist
    {Cseq : ℕ → Set E} {C : Set E} (hlim : PKConverges Cseq C)
    (hCclosed : IsClosed C) (hCne : C.Nonempty) (x : E) :
    Tendsto (fun n ↦ infDist x (Cseq n)) atTop (nhds (infDist x C)) := by
  have hE := (pkConverges_iff_tendsto_infEDist hCclosed).1 hlim x
  simpa only [infDist] using
    (ENNReal.tendsto_toReal (infEDist_ne_top hCne)).comp hE

/-- Theorem 4.35: set convergence entails uniform convergence of the
distance functions on each bounded ball. -/
theorem PKConverges.tendsto_rhoDistance
    {Cseq : ℕ → Set E} {C : Set E} (hlim : PKConverges Cseq C)
    (hCclosed : IsClosed C) (hCne : C.Nonempty) (ρ : ℝ≥0) :
    Tendsto (fun n ↦ rhoDistance ρ (Cseq n) C) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro e he
  rcases (isCompact_closedBall (0 : E) (ρ : ℝ)).finite_cover_balls
      (show 0 < e / 6 by positivity) with
    ⟨t, htBall, htFinite, htCover⟩
  have hcenters : ∀ᶠ n in atTop, ∀ p ∈ t,
      dist (infDist p (Cseq n)) (infDist p C) < e / 3 := by
    apply htFinite.eventually_all.2
    intro p hp
    exact (hlim.tendsto_infDist hCclosed hCne p).eventually
      (ball_mem_nhds _ (show 0 < e / 3 by positivity))
  rcases eventually_atTop.1 hcenters with ⟨N, hN⟩
  refine ⟨N, fun n hn ↦ ?_⟩
  have hlocal : rhoDistance ρ (Cseq n) C < e := by
    rw [rhoDistance]
    letI : Nonempty (closedBall (0 : E) (ρ : ℝ)) := ⟨⟨0, by simp⟩⟩
    apply ContinuousMap.dist_lt_iff_of_nonempty.2
    rintro ⟨x, hx⟩
    rcases mem_iUnion₂.1 (htCover hx) with ⟨p, hpt, hxp⟩
    have hnp : dist (infDist p (Cseq n)) (infDist p C) < e / 3 := hN n hn p hpt
    have hxn : dist (infDist x (Cseq n)) (infDist p (Cseq n)) ≤ dist x p := by
      simpa only [NNReal.coe_one, one_mul] using
        (lipschitz_infDist_pt (Cseq n)).dist_le_mul x p
    have hxC : dist (infDist x C) (infDist p C) ≤ dist x p := by
      simpa only [NNReal.coe_one, one_mul] using
        (lipschitz_infDist_pt C).dist_le_mul x p
    calc
      dist (distanceProfile ρ (Cseq n) ⟨x, hx⟩) (distanceProfile ρ C ⟨x, hx⟩) =
          dist (infDist x (Cseq n)) (infDist x C) := rfl
      _ ≤ dist (infDist x (Cseq n)) (infDist p (Cseq n)) +
          dist (infDist p (Cseq n)) (infDist p C) +
          dist (infDist p C) (infDist x C) := dist_triangle4 _ _ _ _
      _ < e := by
        rw [dist_comm (infDist p C) (infDist x C)]
        have hxp' : dist x p < e / 6 := mem_ball.1 hxp
        linarith
  simpa only [Real.dist_eq, sub_zero,
    abs_of_nonneg (rhoDistance_nonneg ρ (Cseq n) C)] using hlocal

/-- Theorem 4.35(a): the inner-limit inclusion is equivalent to eventual
uniform upper bounds for the distance functions on bounded balls. -/
theorem subset_innerSetLimit_iff_eventually_infDist_le_uniform
    {Cseq : ℕ → Set E} {C : Set E} (hCclosed : IsClosed C)
    (hCne : C.Nonempty) (hCseqne : ∀ n, (Cseq n).Nonempty) :
    C ⊆ innerSetLimit Cseq ↔
      ∀ ρ > 0, ∀ e > 0, ∀ᶠ n in atTop,
        ∀ x ∈ closedBall (0 : E) ρ,
          infDist x (Cseq n) ≤ infDist x C + e := by
  constructor
  · intro hinner ρ hρ e he
    have hunif :=
      (subset_innerSetLimit_iff_eventuallyInnerApproximates hCclosed).1 hinner
    let r : ℝ := 2 * ρ + infDist 0 C
    have hr : 0 < r := by
      dsimp only [r]
      nlinarith [show 0 ≤ infDist (0 : E) C from infDist_nonneg]
    have hsub := hunif r hr (e / 2) (half_pos he)
    exact hsub.mono fun n hn ↦ by
      have hhalf := infDist_le_on_closedBall_of_truncated_subset
        (ρ := ρ) (ρ' := r) (e := e / 2) hCclosed hCne (hCseqne n)
          (half_pos he).le le_rfl
          (hn.trans (thickening_subset_cthickening _ _))
      intro x hx
      exact (hhalf x hx).trans (by linarith)
  · intro hunif
    apply (subset_innerSetLimit_iff_eventuallyInnerApproximates hCclosed).2
    intro ρ hρ e he
    have hdist := hunif ρ hρ (e / 2) (half_pos he)
    exact hdist.mono fun n hn ↦ by
      have hclosed := inter_closedBall_subset_cthickening_of_infDist_le
        (hCseqne n) (half_pos he).le hn
      exact hclosed.trans
        (cthickening_subset_thickening' he (half_lt_self he) (Cseq n))

/-- Theorem 4.35(b), on the book's nonempty closed-set space: the
outer-limit inclusion is equivalent to eventual uniform lower bounds for
the distance functions on bounded balls. -/
theorem outerSetLimit_subset_iff_eventually_infDist_ge_uniform
    {Cseq : ℕ → Set E} {C : Set E} (hCclosed : IsClosed C)
    (hCne : C.Nonempty) (hCseqclosed : ∀ n, IsClosed (Cseq n))
    (hCseqne : ∀ n, (Cseq n).Nonempty) :
    outerSetLimit Cseq ⊆ C ↔
      ∀ ρ > 0, ∀ e > 0, ∀ᶠ n in atTop,
        ∀ x ∈ closedBall (0 : E) ρ,
          infDist x C ≤ infDist x (Cseq n) + e := by
  constructor
  · intro houter ρ hρ e he
    have hunif :=
      (outerSetLimit_subset_iff_eventuallyOuterApproximates hCclosed).1 houter
    let r : ℝ := 4 * ρ + infDist 0 C
    have hr : 0 < r := by
      dsimp only [r]
      nlinarith [show 0 ≤ infDist (0 : E) C from infDist_nonneg]
    have hsub := hunif r hr (e / 2) (half_pos he)
    exact hsub.mono fun n hn x hx ↦ by
      by_cases hfar : 2 * ρ + infDist 0 C ≤ infDist 0 (Cseq n)
      · exact (infDist_le_infDist_on_closedBall_of_origin_gap C (Cseq n) hfar x hx).trans
          (le_add_of_nonneg_right he.le)
      · have hrad : 2 * ρ + infDist 0 (Cseq n) ≤ r := by
          dsimp only [r]
          rw [not_le] at hfar
          linarith
        have hle := infDist_le_on_closedBall_of_truncated_subset
          (hCseqclosed n) (hCseqne n) hCne (half_pos he).le hrad
          (hn.trans (thickening_subset_cthickening _ _)) x hx
        linarith
  · intro hunif
    apply (outerSetLimit_subset_iff_eventuallyOuterApproximates hCclosed).2
    intro ρ hρ e he
    have hdist := hunif ρ hρ (e / 2) (half_pos he)
    exact hdist.mono fun n hn ↦ by
      have hclosed := inter_closedBall_subset_cthickening_of_infDist_le
        hCne (half_pos he).le hn
      exact hclosed.trans
        (cthickening_subset_thickening' he (half_lt_self he) C)

/-- Theorem 4.35, exact uniform-distance formulation in the finite-valued
regime of nonempty sets. -/
theorem pkConverges_iff_tendsto_rhoDistance
    {Cseq : ℕ → Set E} {C : Set E} (hCclosed : IsClosed C)
    (hCne : C.Nonempty) (hCseqne : ∀ n, (Cseq n).Nonempty) :
    PKConverges Cseq C ↔
      ∀ ρ : ℝ≥0, Tendsto (fun n ↦ rhoDistance ρ (Cseq n) C) atTop (nhds 0) := by
  constructor
  · intro hlim ρ
    exact hlim.tendsto_rhoDistance hCclosed hCne ρ
  · intro hdist
    apply (pkConverges_iff_tendsto_infEDist hCclosed).2
    intro x
    let ρ : ℝ≥0 := ‖x‖₊
    have hxρ : x ∈ closedBall (0 : E) (ρ : ℝ) := by
      simp only [mem_closedBall, dist_zero_right, ρ, coe_nnnorm, le_refl]
    have hbound : ∀ n,
        dist (infDist x (Cseq n)) (infDist x C) ≤ rhoDistance ρ (Cseq n) C := by
      intro n
      simpa only [Real.dist_eq] using
        abs_infDist_sub_infDist_le_rhoDistance ρ (Cseq n) C hxρ
    have hreal : Tendsto (fun n ↦ infDist x (Cseq n)) atTop (nhds (infDist x C)) := by
      apply tendsto_iff_dist_tendsto_zero.2
      exact squeeze_zero (fun n ↦ dist_nonneg) hbound (hdist ρ)
    exact (ENNReal.tendsto_toReal_iff
      (fun n ↦ infEDist_ne_top (hCseqne n)) (infEDist_ne_top hCne)).1 hreal

/-- Theorem 4.36: the truncated-inclusion distances characterize set
convergence as well. -/
theorem pkConverges_iff_tendsto_rhoHatDistance
    {Cseq : ℕ → Set E} {C : Set E} (hCclosed : IsClosed C)
    (hCne : C.Nonempty) (hCseqne : ∀ n, (Cseq n).Nonempty) :
    PKConverges Cseq C ↔
      ∀ ρ : ℝ≥0, Tendsto (fun n ↦ rhoHatDistance ρ (Cseq n) C)
        atTop (nhds 0) := by
  rw [pkConverges_iff_eventuallyInnerApproximates_and_eventuallyOuterApproximates hCclosed]
  constructor
  · rintro ⟨hinner, houter⟩ ρ
    rw [Metric.tendsto_atTop]
    intro e he
    let r : ℝ := max 1 (ρ : ℝ)
    have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hρr : (ρ : ℝ) ≤ r := le_max_right _ _
    have hI := hinner r hr (e / 2) (half_pos he)
    have hO := houter r hr (e / 2) (half_pos he)
    have hboth : ∀ᶠ n in atTop,
        Cseq n ∩ closedBall (0 : E) (ρ : ℝ) ⊆ cthickening (e / 2) C ∧
          C ∩ closedBall (0 : E) (ρ : ℝ) ⊆ cthickening (e / 2) (Cseq n) := by
      filter_upwards [hI, hO] with n hnI hnO
      constructor
      · exact (inter_subset_inter_right (Cseq n) (closedBall_subset_closedBall hρr)).trans
          (hnO.trans (thickening_subset_cthickening _ _))
      · exact (inter_subset_inter_right C (closedBall_subset_closedBall hρr)).trans
          (hnI.trans (thickening_subset_cthickening _ _))
    rcases eventually_atTop.1 hboth with ⟨N, hN⟩
    refine ⟨N, fun n hn ↦ ?_⟩
    have hle : rhoHatDistance ρ (Cseq n) C ≤ e / 2 :=
      (rhoHatDistance_le_iff ρ (hCseqne n) hCne (half_pos he).le).2 (hN n hn)
    have hnonneg := rhoHatDistance_nonneg ρ (Cseq n) C
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    linarith
  · intro hdist
    constructor
    · intro r hr e he
      let ρ : ℝ≥0 := ⟨r, hr.le⟩
      have hsmallDist :=
        (hdist ρ).eventually (ball_mem_nhds 0 (half_pos he))
      have hsmall : ∀ᶠ n in atTop, rhoHatDistance ρ (Cseq n) C < e / 2 := by
        filter_upwards [hsmallDist] with n hn
        simpa only [mem_ball, Real.dist_eq, sub_zero,
          abs_of_nonneg (rhoHatDistance_nonneg ρ (Cseq n) C)] using hn
      exact hsmall.mono fun n hn ↦ by
        have hincl := (rhoHatDistance_le_iff ρ (hCseqne n) hCne
          (rhoHatDistance_nonneg ρ (Cseq n) C)).1 le_rfl
        exact hincl.2.trans
          (cthickening_subset_thickening' he (hn.trans (half_lt_self he)) (Cseq n))
    · intro r hr e he
      let ρ : ℝ≥0 := ⟨r, hr.le⟩
      have hsmallDist :=
        (hdist ρ).eventually (ball_mem_nhds 0 (half_pos he))
      have hsmall : ∀ᶠ n in atTop, rhoHatDistance ρ (Cseq n) C < e / 2 := by
        filter_upwards [hsmallDist] with n hn
        simpa only [mem_ball, Real.dist_eq, sub_zero,
          abs_of_nonneg (rhoHatDistance_nonneg ρ (Cseq n) C)] using hn
      exact hsmall.mono fun n hn ↦ by
        have hincl := (rhoHatDistance_le_iff ρ (hCseqne n) hCne
          (rhoHatDistance_nonneg ρ (Cseq n) C)).1 le_rfl
        exact hincl.1.trans
          (cthickening_subset_thickening' he (hn.trans (half_lt_self he)) C)

/-- Theorem 4.36: it is enough to test the localized uniform distances at
all radii above any fixed threshold. -/
theorem pkConverges_iff_tendsto_rhoDistance_from
    {Cseq : ℕ → Set E} {C : Set E} (hCclosed : IsClosed C)
    (hCne : C.Nonempty) (hCseqne : ∀ n, (Cseq n).Nonempty) (r₀ : ℝ≥0) :
    PKConverges Cseq C ↔
      ∀ ρ : ℝ≥0, r₀ ≤ ρ →
        Tendsto (fun n ↦ rhoDistance ρ (Cseq n) C) atTop (nhds 0) := by
  rw [pkConverges_iff_tendsto_rhoDistance hCclosed hCne hCseqne]
  constructor
  · exact fun h ρ _ ↦ h ρ
  · intro h ρ
    let s : ℝ≥0 := max r₀ ρ
    apply squeeze_zero
      (fun n ↦ rhoDistance_nonneg ρ (Cseq n) C)
      (fun n ↦ rhoDistance_mono (le_max_right r₀ ρ) (Cseq n) C)
    exact h s (le_max_left r₀ ρ)

/-- Theorem 4.36, threshold form for the truncated-inclusion distances. -/
theorem pkConverges_iff_tendsto_rhoHatDistance_from
    {Cseq : ℕ → Set E} {C : Set E} (hCclosed : IsClosed C)
    (hCne : C.Nonempty) (hCseqne : ∀ n, (Cseq n).Nonempty) (r₀ : ℝ≥0) :
    PKConverges Cseq C ↔
      ∀ ρ : ℝ≥0, r₀ ≤ ρ →
        Tendsto (fun n ↦ rhoHatDistance ρ (Cseq n) C) atTop (nhds 0) := by
  rw [pkConverges_iff_tendsto_rhoHatDistance hCclosed hCne hCseqne]
  constructor
  · exact fun h ρ _ ↦ h ρ
  · intro h ρ
    let s : ℝ≥0 := max r₀ ρ
    apply squeeze_zero
      (fun n ↦ rhoHatDistance_nonneg ρ (Cseq n) C)
      (fun n ↦ rhoHatDistance_mono (le_max_right r₀ ρ)
        (hCseqne n) hCne)
    exact h s (le_max_left r₀ ρ)

end UniformDistanceConvergence

/-- Theorem 4.36: unlike `rhoDistance`, the truncated-inclusion expression
does not satisfy the triangle inequality.  At radius one, the middle set has
both of its points just outside the ball, making both adjacent distances
`1/5` while the two endpoint singletons are distance `2` apart. -/
theorem not_rhoHatDistance_triangle :
    ¬ rhoHatDistance (1 : ℝ≥0) ({1} : Set ℝ) ({-1} : Set ℝ) ≤
      rhoHatDistance (1 : ℝ≥0) ({1} : Set ℝ) ({-(6 / 5), 6 / 5} : Set ℝ) +
        rhoHatDistance (1 : ℝ≥0) ({-(6 / 5), 6 / 5} : Set ℝ) ({-1} : Set ℝ) := by
  have hAC : rhoHatDistance (1 : ℝ≥0) ({1} : Set ℝ)
      ({-(6 / 5), 6 / 5} : Set ℝ) ≤ 1 / 5 := by
    apply (rhoHatDistance_le_iff (1 : ℝ≥0) (by simp) (by simp) (by norm_num)).2
    constructor
    · rintro x ⟨hxA, _⟩
      simp only [mem_singleton_iff] at hxA
      subst x
      rw [mem_cthickening_iff]
      calc
        infEDist (1 : ℝ) ({-(6 / 5), 6 / 5} : Set ℝ) ≤ edist (1 : ℝ) (6 / 5) :=
          infEDist_le_edist_of_mem (by simp)
        _ ≤ ENNReal.ofReal (1 / 5) := by
          rw [edist_dist]
          norm_num [Real.dist_eq]
    · rintro x ⟨hxC, hxball⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hxC
      rcases hxC with rfl | rfl <;>
        norm_num [mem_closedBall, Real.dist_eq] at hxball
  have hCB : rhoHatDistance (1 : ℝ≥0) ({-(6 / 5), 6 / 5} : Set ℝ)
      ({-1} : Set ℝ) ≤ 1 / 5 := by
    apply (rhoHatDistance_le_iff (1 : ℝ≥0) (by simp) (by simp) (by norm_num)).2
    constructor
    · rintro x ⟨hxC, hxball⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hxC
      rcases hxC with rfl | rfl <;>
        norm_num [mem_closedBall, Real.dist_eq] at hxball
    · rintro x ⟨hxB, _⟩
      simp only [mem_singleton_iff] at hxB
      subst x
      rw [mem_cthickening_iff]
      calc
        infEDist (-1 : ℝ) ({-(6 / 5), 6 / 5} : Set ℝ) ≤
            edist (-1 : ℝ) (-(6 / 5)) := infEDist_le_edist_of_mem (by simp)
        _ ≤ ENNReal.ofReal (1 / 5) := by
          rw [edist_dist]
          norm_num [Real.dist_eq]
  have hAB : ¬ rhoHatDistance (1 : ℝ≥0) ({1} : Set ℝ) ({-1} : Set ℝ) ≤ 1 := by
    intro hle
    have hincl := ((rhoHatDistance_le_iff (1 : ℝ≥0) (by simp) (by simp)
      (by norm_num : (0 : ℝ) ≤ 1)).1 hle).1
    have hmem := hincl (show
      (1 : ℝ) ∈ ({1} : Set ℝ) ∩ closedBall 0 1 by
        constructor
        · simp
        · norm_num [mem_closedBall, Real.dist_eq])
    rw [mem_cthickening_iff, infEDist_singleton, edist_dist] at hmem
    norm_num [Real.dist_eq] at hmem
  intro htriangle
  apply hAB
  calc
    rhoHatDistance (1 : ℝ≥0) ({1} : Set ℝ) ({-1} : Set ℝ) ≤
        rhoHatDistance (1 : ℝ≥0) ({1} : Set ℝ) ({-(6 / 5), 6 / 5} : Set ℝ) +
          rhoHatDistance (1 : ℝ≥0) ({-(6 / 5), 6 / 5} : Set ℝ) ({-1} : Set ℝ) :=
      htriangle
    _ ≤ 1 := by linarith

section DistanceEstimates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Proposition 4.37(a), first inequality. -/
theorem rhoHatDistance_le_rhoDistance
    (r : ℝ≥0) {C D : Set E} (hCne : C.Nonempty) (hDne : D.Nonempty) :
    rhoHatDistance r C D ≤ rhoDistance r C D := by
  have he := rhoDistance_nonneg r C D
  apply (rhoHatDistance_le_iff r hCne hDne he).2
  have hdist := (rhoDistance_le_iff he r C D).1 le_rfl
  constructor
  · apply inter_closedBall_subset_cthickening_of_infDist_le hDne he
    intro x hx
    have habs := hdist x hx
    rw [abs_le] at habs
    linarith
  · apply inter_closedBall_subset_cthickening_of_infDist_le hCne he
    intro x hx
    have habs := hdist x hx
    rw [abs_le] at habs
    linarith

/-- Proposition 4.37(a), second inequality, with the general `2r` radius
from Lemma 4.34. -/
theorem rhoDistance_le_rhoHatDistance_of_two_mul
    {r s : ℝ≥0} {C D : Set E} (hCclosed : IsClosed C)
    (hDclosed : IsClosed D) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hrs : 2 * (r : ℝ) + max (infDist 0 C) (infDist 0 D) ≤ (s : ℝ)) :
    rhoDistance r C D ≤ rhoHatDistance s C D := by
  let e := rhoHatDistance s C D
  have he : 0 ≤ e := rhoHatDistance_nonneg s C D
  have hincl := (rhoHatDistance_le_iff s hCne hDne he).1 le_rfl
  have hCradius : 2 * (r : ℝ) + infDist 0 C ≤ (s : ℝ) := by
    calc
      2 * (r : ℝ) + infDist 0 C ≤
          2 * (r : ℝ) + max (infDist 0 C) (infDist 0 D) := by
            gcongr
            exact le_max_left _ _
      _ ≤ (s : ℝ) := hrs
  have hDradius : 2 * (r : ℝ) + infDist 0 D ≤ (s : ℝ) := by
    calc
      2 * (r : ℝ) + infDist 0 D ≤
          2 * (r : ℝ) + max (infDist 0 C) (infDist 0 D) := by
            gcongr
            exact le_max_right _ _
      _ ≤ (s : ℝ) := hrs
  have hDtoC := infDist_le_on_closedBall_of_truncated_subset
    hCclosed hCne hDne he hCradius hincl.1
  have hCtoD := infDist_le_on_closedBall_of_truncated_subset
    hDclosed hDne hCne he hDradius hincl.2
  apply (rhoDistance_le_iff he r C D).2
  intro x hx
  rw [abs_le]
  constructor
  · linarith [hDtoC x hx]
  · linarith [hCtoD x hx]

/-- Proposition 4.37(c). -/
theorem rhoDistance_le_max_infDist_zero_add
    (r : ℝ≥0) (C D : Set E) :
    rhoDistance r C D ≤
      max (infDist 0 C) (infDist 0 D) + (r : ℝ) := by
  have he : 0 ≤ max (infDist 0 C) (infDist 0 D) + (r : ℝ) := by
    exact add_nonneg
      ((show 0 ≤ infDist (0 : E) C from infDist_nonneg).trans
        (le_max_left _ _)) (NNReal.coe_nonneg r)
  apply (rhoDistance_le_iff he r C D).2
  intro x hx
  rw [mem_closedBall, dist_zero_right] at hx
  have hC : infDist x C ≤ infDist 0 C + (r : ℝ) := by
    calc
      infDist x C ≤ infDist 0 C + dist x 0 := infDist_le_infDist_add_dist
      _ ≤ infDist 0 C + (r : ℝ) := by
        rw [dist_zero_right]
        gcongr
  have hD : infDist x D ≤ infDist 0 D + (r : ℝ) := by
    calc
      infDist x D ≤ infDist 0 D + dist x 0 := infDist_le_infDist_add_dist
      _ ≤ infDist 0 D + (r : ℝ) := by
        rw [dist_zero_right]
        gcongr
  rw [abs_le]
  constructor <;> nlinarith [infDist_nonneg (x := x) (s := C),
    infDist_nonneg (x := x) (s := D), le_max_left (infDist 0 C) (infDist 0 D),
    le_max_right (infDist 0 C) (infDist 0 D)]

/-- Proposition 4.37(b): once a ball contains both sets, both localized
distances stabilize at their common value. -/
theorem rhoDistances_eq_of_union_subset_closedBall
    {r₀ r : ℝ≥0} {C D : Set E} (hCclosed : IsClosed C)
    (hDclosed : IsClosed D) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hCD : C ∪ D ⊆ closedBall (0 : E) (r₀ : ℝ)) (hr : r₀ ≤ r) :
    rhoHatDistance r C D = rhoDistance r C D ∧
      rhoDistance r C D = rhoDistance r₀ C D := by
  let e := rhoHatDistance r₀ C D
  have he : 0 ≤ e := rhoHatDistance_nonneg r₀ C D
  have hincl₀ := (rhoHatDistance_le_iff r₀ hCne hDne he).1 le_rfl
  have hCsub : C ⊆ cthickening e D := by
    intro x hx
    exact hincl₀.1 ⟨hx, hCD (Or.inl hx)⟩
  have hDsub : D ⊆ cthickening e C := by
    intro x hx
    exact hincl₀.2 ⟨hx, hCD (Or.inr hx)⟩
  have hrho : rhoDistance r C D ≤ e := by
    apply (rhoDistance_le_iff he r C D).2
    intro x _
    have hDtoC := infDist_le_infDist_add_of_subset_cthickening
      hCclosed hCne hDne he hCsub x
    have hCtoD := infDist_le_infDist_add_of_subset_cthickening
      hDclosed hDne hCne he hDsub x
    rw [abs_le]
    constructor <;> linarith
  have hchain₀ : e ≤ rhoDistance r₀ C D :=
    rhoHatDistance_le_rhoDistance r₀ hCne hDne
  have hmono : rhoDistance r₀ C D ≤ rhoDistance r C D :=
    rhoDistance_mono hr C D
  have hall : rhoDistance r C D = e := le_antisymm hrho (hchain₀.trans hmono)
  have hhat : rhoHatDistance r C D = e := le_antisymm
    ((rhoHatDistance_le_rhoDistance r hCne hDne).trans_eq hall)
    (rhoHatDistance_mono hr hCne hDne)
  have hzero : rhoDistance r₀ C D = e :=
    le_antisymm (hmono.trans hrho) hchain₀
  constructor
  · exact hhat.trans hall.symm
  · exact hall.trans hzero.symm

omit [FiniteDimensional ℝ E] in
private theorem exists_mem_closedBall_dist_le_radius_sub
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) {x : E}
    (hx : x ∈ closedBall (0 : E) s) :
    ∃ y ∈ closedBall (0 : E) r, dist x y ≤ s - r := by
  rw [mem_closedBall, dist_zero_right] at hx
  by_cases hxr : ‖x‖ ≤ r
  · exact ⟨x, by simpa only [mem_closedBall, dist_zero_right], by
      simp only [dist_self]
      linarith⟩
  · have hrx : r < ‖x‖ := lt_of_not_ge hxr
    have hxpos : 0 < ‖x‖ := lt_of_le_of_lt hr hrx
    let y : E := (r / ‖x‖) • x
    have hynorm : ‖y‖ = r := by
      dsimp only [y]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hr (norm_nonneg x))]
      field_simp
    refine ⟨y, ?_, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right, hynorm] using le_rfl
    · have hdist : dist x y = ‖x‖ - r := by
        dsimp only [y]
        rw [dist_eq_norm]
        have hsub : x - (r / ‖x‖) • x = (1 - r / ‖x‖) • x := by
          rw [sub_smul, one_smul]
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg]
        · field_simp
        · exact sub_nonneg.mpr ((div_le_one hxpos).2 hrx.le)
      rw [hdist]
      linarith

private theorem rhoDistance_le_add_two_mul_radius_sub
    {r s : ℝ≥0} (hrs : r ≤ s) (C D : Set E) :
    rhoDistance s C D ≤
      rhoDistance r C D + 2 * ((s : ℝ) - (r : ℝ)) := by
  have he : 0 ≤ rhoDistance r C D + 2 * ((s : ℝ) - (r : ℝ)) :=
    add_nonneg (rhoDistance_nonneg r C D) <| mul_nonneg (by norm_num) <| by
      exact sub_nonneg.mpr (by exact_mod_cast hrs)
  apply (rhoDistance_le_iff he s C D).2
  intro x hx
  rcases exists_mem_closedBall_dist_le_radius_sub
      (NNReal.coe_nonneg r) (by exact_mod_cast hrs) hx with ⟨y, hy, hxy⟩
  have hyCD := abs_infDist_sub_infDist_le_rhoDistance r C D hy
  have hxC : dist (infDist x C) (infDist y C) ≤ dist x y := by
    simpa only [NNReal.coe_one, one_mul] using
      (lipschitz_infDist_pt C).dist_le_mul x y
  have hxD : dist (infDist y D) (infDist x D) ≤ dist x y := by
    simpa only [NNReal.coe_one, one_mul, dist_comm x y] using
      (lipschitz_infDist_pt D).dist_le_mul y x
  rw [← Real.dist_eq]
  calc
    dist (infDist x C) (infDist x D) ≤
        dist (infDist x C) (infDist y C) +
          dist (infDist y C) (infDist y D) +
          dist (infDist y D) (infDist x D) := dist_triangle4 _ _ _ _
    _ ≤ dist x y + rhoDistance r C D + dist x y := by
      gcongr
      simpa only [Real.dist_eq] using hyCD
    _ ≤ rhoDistance r C D + 2 * ((s : ℝ) - (r : ℝ)) := by
      linarith

/-- Proposition 4.37(d), the quantitative radius-continuity estimate. -/
theorem abs_rhoDistance_sub_rhoDistance_le
    (r s : ℝ≥0) (C D : Set E) :
    |rhoDistance r C D - rhoDistance s C D| ≤
      2 * |(r : ℝ) - (s : ℝ)| := by
  rcases le_total r s with hrs | hsr
  · have hmono := rhoDistance_mono hrs C D
    have hinc := rhoDistance_le_add_two_mul_radius_sub hrs C D
    rw [abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hrs))]
    linarith
  · have hmono := rhoDistance_mono hsr C D
    have hinc := rhoDistance_le_add_two_mul_radius_sub hsr C D
    rw [abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hsr))]
    linarith

/-- The continuity assertion in Proposition 4.37, strengthened to a global
Lipschitz estimate with constant two. -/
theorem rhoDistance_lipschitzWith (C D : Set E) :
    LipschitzWith 2 (fun r : ℝ≥0 ↦ rhoDistance r C D) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro r s
  simpa only [Real.dist_eq, NNReal.dist_eq, NNReal.coe_ofNat] using
    abs_rhoDistance_sub_rhoDistance_le r s C D

theorem continuous_rhoDistance (C D : Set E) :
    Continuous (fun r : ℝ≥0 ↦ rhoDistance r C D) :=
  (rhoDistance_lipschitzWith C D).continuous

end DistanceEstimates

section ConvexDistanceEstimates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Convex sharpening of Proposition 4.37(a): `r` replaces `2r`. -/
theorem rhoDistance_le_rhoHatDistance_of_convex
    {r s : ℝ≥0} {C D : Set E} (hCclosed : IsClosed C)
    (hDclosed : IsClosed D) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hCconv : Convex ℝ C) (hDconv : Convex ℝ D)
    (hrs : (r : ℝ) + max (infDist 0 C) (infDist 0 D) ≤ (s : ℝ)) :
    rhoDistance r C D ≤ rhoHatDistance s C D := by
  let e := rhoHatDistance s C D
  have he : 0 ≤ e := rhoHatDistance_nonneg s C D
  have hincl := (rhoHatDistance_le_iff s hCne hDne he).1 le_rfl
  have hCradius : (r : ℝ) + infDist 0 C ≤ (s : ℝ) := by
    calc
      (r : ℝ) + infDist 0 C ≤
          (r : ℝ) + max (infDist 0 C) (infDist 0 D) := by
            gcongr
            exact le_max_left _ _
      _ ≤ (s : ℝ) := hrs
  have hDradius : (r : ℝ) + infDist 0 D ≤ (s : ℝ) := by
    calc
      (r : ℝ) + infDist 0 D ≤
          (r : ℝ) + max (infDist 0 C) (infDist 0 D) := by
            gcongr
            exact le_max_right _ _
      _ ≤ (s : ℝ) := hrs
  have hDtoC := infDist_le_on_closedBall_of_convex_truncated_subset
    hCclosed hCne hCconv hDne he hCradius hincl.1
  have hCtoD := infDist_le_on_closedBall_of_convex_truncated_subset
    hDclosed hDne hDconv hCne he hDradius hincl.2
  apply (rhoDistance_le_iff he r C D).2
  intro x hx
  rw [abs_le]
  constructor
  · linarith [hDtoC x hx]
  · linarith [hCtoD x hx]

/-- Final clause of Proposition 4.37(a): convex sets containing the origin
have identical localized distance expressions at every radius. -/
theorem rhoHatDistance_eq_rhoDistance_of_convex_zero_mem
    (r : ℝ≥0) {C D : Set E} (hCclosed : IsClosed C)
    (hDclosed : IsClosed D) (hCconv : Convex ℝ C) (hDconv : Convex ℝ D)
    (h0C : 0 ∈ C) (h0D : 0 ∈ D) :
    rhoHatDistance r C D = rhoDistance r C D := by
  have hCne : C.Nonempty := ⟨0, h0C⟩
  have hDne : D.Nonempty := ⟨0, h0D⟩
  apply le_antisymm (rhoHatDistance_le_rhoDistance r hCne hDne)
  apply rhoDistance_le_rhoHatDistance_of_convex
    hCclosed hDclosed hCne hDne hCconv hDconv
  simp only [infDist_zero_of_mem h0C, infDist_zero_of_mem h0D, max_self, add_zero]
  exact le_rfl

end ConvexDistanceEstimates

section PompeiuHausdorffLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The truncated excesses exhaust the full extended
Pompeiu--Hausdorff distance. -/
theorem iSup_rhoHatEDistance_eq_hausdorffEDist (C D : Set E) :
    (⨆ r : ℝ≥0, rhoHatEDistance r C D) = hausdorffEDist C D := by
  rw [hausdorffEDist_def]
  apply le_antisymm
  · refine iSup_le fun r ↦ ?_
    rw [rhoHatEDistance]
    apply sup_le
    · refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
      have hfull : infEDist x D ≤ ⨆ y ∈ C, infEDist y D := by
        refine le_iSup_of_le x ?_
        exact le_iSup (fun _ : x ∈ C ↦ infEDist x D) hx.1
      exact hfull.trans le_sup_left
    · refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
      have hfull : infEDist x C ≤ ⨆ y ∈ D, infEDist y C := by
        refine le_iSup_of_le x ?_
        exact le_iSup (fun _ : x ∈ D ↦ infEDist x C) hx.1
      exact hfull.trans le_sup_right
  · apply sup_le
    · refine iSup_le fun x ↦ iSup_le fun hxC ↦ ?_
      let r : ℝ≥0 := ‖x‖₊
      have hxBall : x ∈ closedBall (0 : E) (r : ℝ) := by
        simp only [mem_closedBall, dist_zero_right, r, coe_nnnorm, le_refl]
      calc
        infEDist x D ≤ rhoHatEDistance r C D := by
          rw [rhoHatEDistance]
          have hlocal : infEDist x D ≤
              ⨆ z : E, ⨆ _ : z ∈ C ∩ closedBall (0 : E) (r : ℝ), infEDist z D := by
            refine le_iSup_of_le x ?_
            exact le_iSup
              (fun _ : x ∈ C ∩ closedBall (0 : E) (r : ℝ) ↦ infEDist x D)
              ⟨hxC, hxBall⟩
          exact hlocal.trans le_sup_left
        _ ≤ ⨆ s : ℝ≥0, rhoHatEDistance s C D :=
          le_iSup (fun s : ℝ≥0 ↦ rhoHatEDistance s C D) r
    · refine iSup_le fun x ↦ iSup_le fun hxD ↦ ?_
      let r : ℝ≥0 := ‖x‖₊
      have hxBall : x ∈ closedBall (0 : E) (r : ℝ) := by
        simp only [mem_closedBall, dist_zero_right, r, coe_nnnorm, le_refl]
      calc
        infEDist x C ≤ rhoHatEDistance r C D := by
          rw [rhoHatEDistance]
          have hlocal : infEDist x C ≤
              ⨆ z : E, ⨆ _ : z ∈ D ∩ closedBall (0 : E) (r : ℝ), infEDist z C := by
            refine le_iSup_of_le x ?_
            exact le_iSup
              (fun _ : x ∈ D ∩ closedBall (0 : E) (r : ℝ) ↦ infEDist x C)
              ⟨hxD, hxBall⟩
          exact hlocal.trans le_sup_right
        _ ≤ ⨆ s : ℝ≥0, rhoHatEDistance s C D :=
          le_iSup (fun s : ℝ≥0 ↦ rhoHatEDistance s C D) r

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Corollary 4.38 for the extended truncated-inclusion distance. -/
theorem tendsto_rhoHatEDistance_atTop (C D : Set E) :
    Tendsto (fun r : ℝ≥0 ↦ rhoHatEDistance r C D) atTop
      (nhds (hausdorffEDist C D)) := by
  simpa only [iSup_rhoHatEDistance_eq_hausdorffEDist] using
    (tendsto_atTop_iSup (fun _ _ hrs ↦ rhoHatEDistance_mono hrs C D))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem ofReal_rhoHatDistance
    (r : ℝ≥0) {C D : Set E} (hCne : C.Nonempty) (hDne : D.Nonempty) :
    ENNReal.ofReal (rhoHatDistance r C D) = rhoHatEDistance r C D :=
  ENNReal.ofReal_toReal (rhoHatEDistance_ne_top r hCne hDne)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Corollary 4.38 in the book's finite real-valued notation, embedded into
the extended nonnegative reals to include an infinite limit. -/
theorem tendsto_ofReal_rhoHatDistance_atTop
    {C D : Set E} (hCne : C.Nonempty) (hDne : D.Nonempty) :
    Tendsto (fun r : ℝ≥0 ↦ ENNReal.ofReal (rhoHatDistance r C D)) atTop
      (nhds (hausdorffEDist C D)) := by
  simpa only [ofReal_rhoHatDistance _ hCne hDne] using
    tendsto_rhoHatEDistance_atTop C D

/-- Corollary 4.38 for the uniform distance functions. -/
theorem tendsto_ofReal_rhoDistance_atTop
    {C D : Set E} (hCclosed : IsClosed C) (hDclosed : IsClosed D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) :
    Tendsto (fun r : ℝ≥0 ↦ ENNReal.ofReal (rhoDistance r C D)) atTop
      (nhds (hausdorffEDist C D)) := by
  let m : ℝ≥0 := ⟨max (infDist 0 C) (infDist 0 D),
    (show 0 ≤ infDist (0 : E) C from infDist_nonneg).trans (le_max_left _ _)⟩
  let shift : ℝ≥0 → ℝ≥0 := fun r ↦ 2 * r + m
  have hshift : Tendsto shift atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with r hr
    dsimp only [shift]
    calc
      b ≤ r := hr
      _ ≤ r + r := le_add_right le_rfl
      _ = 2 * r := by ring
      _ ≤ 2 * r + m := le_add_right le_rfl
  have hlower : ∀ r : ℝ≥0,
      rhoHatEDistance r C D ≤ ENNReal.ofReal (rhoDistance r C D) := by
    intro r
    rw [← ofReal_rhoHatDistance r hCne hDne]
    exact ENNReal.ofReal_le_ofReal (rhoHatDistance_le_rhoDistance r hCne hDne)
  have hupper : ∀ r : ℝ≥0,
      ENNReal.ofReal (rhoDistance r C D) ≤
        rhoHatEDistance (shift r) C D := by
    intro r
    rw [← ofReal_rhoHatDistance (shift r) hCne hDne]
    apply ENNReal.ofReal_le_ofReal
    apply rhoDistance_le_rhoHatDistance_of_two_mul
      hCclosed hDclosed hCne hDne
    dsimp only [shift, m]
    norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_rhoHatEDistance_atTop C D)
    ((tendsto_rhoHatEDistance_atTop C D).comp hshift) hlower hupper

end PompeiuHausdorffLimit

end RW
