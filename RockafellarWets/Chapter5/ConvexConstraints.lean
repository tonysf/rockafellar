/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Parameterized Convex Constraints

Example 5.10 studies the feasible-set mapping

  `T(w) = {x | fᵢ(x, w) ≤ 0 for i = 1, …, m}`

for continuous `fᵢ` that are convex in `x` for each fixed `w`, and shows that
a single Slater point -- a point `x̄` with `fᵢ(x̄, w̄) < 0` for every `i` --
forces `T` to be continuous throughout a neighborhood of `w̄`.

Outer semicontinuity is 5.7(a) applied to the closed graph, exactly as in 5.8
and needing no convexity.  Convexity enters only for inner semicontinuity,
through the Slater point: the segment from a strictly feasible point to any
feasible point is strictly feasible except at its far endpoint, so the
strictly feasible set is dense in `T(w̄)`, and strictly feasible points
survive small perturbations of `w` by continuity alone.

The book's proof routes this through the identity `int T(w) = {x | f(x,w) <
0}`, which is Theorem 2.34.  The density argument used here reaches the same
conclusion without it; the interior identity is nevertheless recorded below,
since the book asserts it, and it follows from the same segment computation
run in the opposite direction.
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import RockafellarWets.Chapter5.SemicontinuityCriteria

open Filter Set Topology

namespace RW

section Definitions

variable {D E ι : Type*} {f : ι → E → D → ℝ}

/-- **Example 5.10**: the feasible-set mapping of a parameterized system of
inequality constraints. -/
def convexConstraintSet (f : ι → E → D → ℝ) : D → Set E :=
  fun w ↦ {x | ∀ i, f i x w ≤ 0}

/-- The strictly feasible points of the system at the parameter `w`. -/
def strictConstraintSet (f : ι → E → D → ℝ) : D → Set E :=
  fun w ↦ {x | ∀ i, f i x w < 0}

@[simp]
theorem mem_convexConstraintSet {w : D} {x : E} :
    x ∈ convexConstraintSet f w ↔ ∀ i, f i x w ≤ 0 := Iff.rfl

@[simp]
theorem mem_strictConstraintSet {w : D} {x : E} :
    x ∈ strictConstraintSet f w ↔ ∀ i, f i x w < 0 := Iff.rfl

theorem strictConstraintSet_subset (f : ι → E → D → ℝ) (w : D) :
    strictConstraintSet f w ⊆ convexConstraintSet f w :=
  fun _ hx i ↦ (hx i).le

end Definitions

section ConvexConstraints

variable {D E ι : Type*} [TopologicalSpace D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ι → E → D → ℝ}

omit [NormedSpace ℝ E] in
/-- Sections of the constraint functions in the state variable. -/
private theorem continuous_state (hcont : ∀ i, Continuous fun p : E × D ↦ f i p.1 p.2)
    (i : ι) (w : D) : Continuous fun x : E ↦ f i x w :=
  (hcont i).comp (continuous_id.prodMk continuous_const)

omit [NormedSpace ℝ E] in
/-- Sections of the constraint functions in the parameter. -/
private theorem continuous_param (hcont : ∀ i, Continuous fun p : E × D ↦ f i p.1 p.2)
    (i : ι) (x : E) : Continuous fun w : D ↦ f i x w :=
  (hcont i).comp (continuous_const.prodMk continuous_id)

omit [NormedSpace ℝ E] in
/-- The graph is the intersection of the closed sets cut out by the
individual constraints. -/
theorem isClosed_svGraph_convexConstraintSet
    (hcont : ∀ i, Continuous fun p : E × D ↦ f i p.1 p.2) :
    IsClosed (svGraph (convexConstraintSet f)) := by
  have hrw : svGraph (convexConstraintSet f) =
      ⋂ i, {p : D × E | f i p.2 p.1 ≤ 0} := by
    ext p
    simp [svGraph, convexConstraintSet]
  rw [hrw]
  exact isClosed_iInter fun i ↦
    isClosed_Iic.preimage ((hcont i).comp continuous_swap)

omit [NormedSpace ℝ E] in
/-- **Example 5.10**: `T` is outer semicontinuous, by 5.7(a).  No convexity
is needed for this half. -/
theorem svOsc_convexConstraintSet
    (hcont : ∀ i, Continuous fun p : E × D ↦ f i p.1 p.2) :
    SvOsc (convexConstraintSet f) :=
  isClosed_svGraph_iff_svOsc.1 (isClosed_svGraph_convexConstraintSet hcont)

omit [TopologicalSpace D] in
/-- **Example 5.10**: each feasible set is convex. -/
theorem convex_convexConstraintSet
    (hconv : ∀ i w, ConvexOn ℝ (univ : Set E) fun x ↦ f i x w) (w : D) :
    Convex ℝ (convexConstraintSet f w) := by
  have hrw : convexConstraintSet f w = ⋂ i, {x ∈ (univ : Set E) | f i x w ≤ 0} := by
    ext x
    simp [convexConstraintSet]
  rw [hrw]
  exact convex_iInter fun i ↦ (hconv i w).convex_le 0

omit [NormedSpace ℝ E] in
/-- The strictly feasible set is open. -/
theorem isOpen_strictConstraintSet [Finite ι]
    (hcont : ∀ i, Continuous fun p : E × D ↦ f i p.1 p.2) (w : D) :
    IsOpen (strictConstraintSet f w) := by
  have hrw : strictConstraintSet f w = ⋂ i, {x : E | f i x w < 0} := by
    ext x
    simp [strictConstraintSet]
  rw [hrw]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_Iio.preimage (continuous_state hcont i w)

omit [TopologicalSpace D] in
/-- The segment computation behind Example 5.10: a point of the segment from
a feasible point `x` towards a strictly feasible point `x₀` is strictly
feasible as soon as it has left `x`. -/
theorem segment_mem_strictConstraintSet
    (hconv : ∀ i w, ConvexOn ℝ (univ : Set E) fun x ↦ f i x w) {w : D} {x x₀ : E}
    (hx : x ∈ convexConstraintSet f w) (hx₀ : x₀ ∈ strictConstraintSet f w)
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    (1 - τ) • x + τ • x₀ ∈ strictConstraintSet f w := by
  intro i
  have hjensen := (hconv i w).2 (mem_univ x) (mem_univ x₀)
    (by linarith : (0 : ℝ) ≤ 1 - τ) hτ0.le (by ring)
  have h₁ : (1 - τ) * f i x w ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (hx i)
  have h₂ : τ * f i x₀ w < 0 := mul_neg_of_pos_of_neg hτ0 (hx₀ i)
  simp only [smul_eq_mul] at hjensen
  linarith

omit [TopologicalSpace D] in
/-- Under a Slater point the strictly feasible set is dense in the feasible
set.  This replaces the book's appeal to the interior identity 2.34. -/
theorem convexConstraintSet_subset_closure_strict
    (hconv : ∀ i w, ConvexOn ℝ (univ : Set E) fun x ↦ f i x w) {w : D}
    (hne : (strictConstraintSet f w).Nonempty) :
    convexConstraintSet f w ⊆ closure (strictConstraintSet f w) := by
  obtain ⟨x₀, hx₀⟩ := hne
  intro x hx
  have hcont : Continuous fun τ : ℝ ↦ (1 - τ) • x + τ • x₀ :=
    ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  refine mem_closure_of_tendsto
    (f := fun τ : ℝ ↦ (1 - τ) • x + τ • x₀)
    (b := nhdsWithin (0 : ℝ) (Ioi 0)) ?_ ?_
  · have h0 : Tendsto (fun τ : ℝ ↦ (1 - τ) • x + τ • x₀) (nhds 0)
        (nhds ((1 - (0 : ℝ)) • x + (0 : ℝ) • x₀)) := hcont.tendsto 0
    simpa using h0.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with τ hτ0 hτ1
    exact segment_mem_strictConstraintSet hconv hx hx₀ hτ0 hτ1

/-- **Example 5.10**: with a Slater point at `w`, the mapping is inner
semicontinuous at `w`.

A strictly feasible point stays feasible for all nearby parameters, by
continuity in the parameter alone, so it lies in the inner limit.  The inner
limit is closed and, by density, contains all of `T(w)`. -/
theorem svIscAt_convexConstraintSet [Finite ι]
    (hcont : ∀ i, Continuous fun p : E × D ↦ f i p.1 p.2)
    (hconv : ∀ i w, ConvexOn ℝ (univ : Set E) fun x ↦ f i x w) {w : D}
    (hne : (strictConstraintSet f w).Nonempty) :
    SvIscAt (convexConstraintSet f) w := by
  have hstrict :
      strictConstraintSet f w ⊆ svInnerLimit (convexConstraintSet f) w := by
    intro x hx N hN
    have hev : ∀ᶠ w' in nhds w, ∀ i, f i x w' < 0 := by
      rw [Filter.eventually_all]
      exact fun i ↦
        (isOpen_Iio.preimage (continuous_param hcont i x)).mem_nhds (hx i)
    filter_upwards [hev] with w' hw'
    exact ⟨x, fun i ↦ (hw' i).le, mem_of_mem_nhds hN⟩
  calc convexConstraintSet f w
      ⊆ closure (strictConstraintSet f w) :=
        convexConstraintSet_subset_closure_strict hconv hne
    _ ⊆ svInnerLimit (convexConstraintSet f) w :=
        closure_minimal hstrict (isClosed_svInnerLimit _ w)

/-- The interior identity the book records as part of 5.10, and which is
Theorem 2.34: under a Slater point the interior of the feasible set is the
strictly feasible set.

The inclusion `⊂` runs the segment computation backwards, pushing `x` a short
way away from the Slater point and writing `x` itself as a convex combination
of the pushed point and the Slater point. -/
theorem interior_convexConstraintSet [Finite ι]
    (hcont : ∀ i, Continuous fun p : E × D ↦ f i p.1 p.2)
    (hconv : ∀ i w, ConvexOn ℝ (univ : Set E) fun x ↦ f i x w) {w : D}
    (hne : (strictConstraintSet f w).Nonempty) :
    interior (convexConstraintSet f w) = strictConstraintSet f w := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine Subset.antisymm (fun x hx ↦ ?_) fun x hx ↦
    (isOpen_strictConstraintSet hcont w).subset_interior_iff.2
      (strictConstraintSet_subset f w) hx
  -- Push `x` away from `x₀` while staying feasible.
  have hcontline : Continuous fun t : ℝ ↦ x + t • (x - x₀) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ t in nhds (0 : ℝ), x + t • (x - x₀) ∈ convexConstraintSet f w := by
    have h0 : x + (0 : ℝ) • (x - x₀) = x := by simp
    exact hcontline.continuousAt.preimage_mem_nhds (by rwa [h0, ← mem_interior_iff_mem_nhds])
  have hev' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      x + t • (x - x₀) ∈ convexConstraintSet f w :=
    hev.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), (0 : ℝ) < t :=
    Filter.eventually_mem_set.2 self_mem_nhdsWithin
  obtain ⟨t, hty, ht0⟩ := (hev'.and hpos).exists
  intro i
  have htpos : (0 : ℝ) < 1 + t := by linarith
  have ht1 : (1 : ℝ) + t ≠ 0 := ne_of_gt htpos
  have hinv : (0 : ℝ) < (1 + t)⁻¹ := inv_pos.2 htpos
  have hcoef : (1 + t)⁻¹ + t * (1 + t)⁻¹ = 1 := by field_simp
  have hcomb : (1 + t)⁻¹ • (x + t • (x - x₀)) + (t * (1 + t)⁻¹) • x₀ = x := by
    match_scalars <;> (field_simp; try ring)
  have hjensen := (hconv i w).2 (mem_univ (x + t • (x - x₀))) (mem_univ x₀)
    hinv.le (mul_pos ht0 hinv).le hcoef
  rw [hcomb] at hjensen
  simp only [smul_eq_mul] at hjensen
  have h₁ : (1 + t)⁻¹ * f i (x + t • (x - x₀)) w ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hinv.le (hty i)
  have h₂ : (t * (1 + t)⁻¹) * f i x₀ w < 0 :=
    mul_neg_of_pos_of_neg (mul_pos ht0 hinv) (hx₀ i)
  linarith

/-- **Example 5.10.**  A Slater point at `w₀` makes the feasible-set mapping
continuous at every parameter in an explicit open neighborhood of `w₀`,
namely the set of parameters for which that same point stays strictly
feasible. -/
theorem exists_isOpen_svContinuousAt_convexConstraintSet [Finite ι]
    (hcont : ∀ i, Continuous fun p : E × D ↦ f i p.1 p.2)
    (hconv : ∀ i w, ConvexOn ℝ (univ : Set E) fun x ↦ f i x w)
    {w₀ : D} {x₀ : E} (hslater : ∀ i, f i x₀ w₀ < 0) :
    ∃ O : Set D, IsOpen O ∧ w₀ ∈ O ∧
      ∀ w ∈ O, SvContinuousAt (convexConstraintSet f) w := by
  refine ⟨{w : D | ∀ i, f i x₀ w < 0}, ?_, hslater, fun w hw ↦
    ⟨svOsc_convexConstraintSet hcont w,
      svIscAt_convexConstraintSet hcont hconv ⟨x₀, hw⟩⟩⟩
  have hrw : {w : D | ∀ i, f i x₀ w < 0} = ⋂ i, {w : D | f i x₀ w < 0} := by
    ext w
    simp
  rw [hrw]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_Iio.preimage (continuous_param hcont i x₀)

end ConvexConstraints

end RW
