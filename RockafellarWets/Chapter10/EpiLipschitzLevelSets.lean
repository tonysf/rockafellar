/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epi-Lipschitzian level-set boundaries
-/

import RockafellarWets.Chapter10.LevelSetDescent

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}

/-- A uniform backward increase excludes boundary-level points from the
interior of a sublevel set. -/
theorem not_mem_interior_levelSet_of_backward_increase {y w : E} {lam δ : ℝ}
    (hl : 0 < lam) (hd : 0 < δ)
    (h : ∀ t ∈ Ioo (0:ℝ) δ, f y+lam*t ≤ f (y-t • w)) :
    y ∉ interior {z | f z ≤ f y} := by
  intro hy
  have hp : Tendsto (fun t : ℝ ↦ y-t • w) (𝓝[>] 0) (𝓝 y) := by
    simpa using (((continuous_const.sub (continuous_id.smul continuous_const)) :
      Continuous (fun t : ℝ ↦ y-t • w)).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo (0:ℝ) δ := Ioo_mem_nhdsGT hd
  obtain ⟨t,ht,hz⟩ := (ht.and (hp.eventually (mem_interior_iff_mem_nhds.mp hy))).exists
  have hi := h t ht
  have hz' : f (y-t • w) ≤ f y := hz
  have := mul_pos hl ht.1
  linarith

/-- The local boundary and interior equalities from Example 10.4. -/
theorem levelSet_boundary_of_uniform_descent (hf : Continuous f)
    {V : Set E} {w : E} {lam δ c : ℝ} (hl : 0 < lam) (hd : 0 < δ)
    (h : ∀ y ∈ V, ∀ t ∈ Ioo (0:ℝ) δ, f y+lam*t ≤ f (y-t • w)) :
    V ∩ frontier {y | f y ≤ c} = V ∩ {y | f y = c} ∧
      V ∩ interior {y | f y ≤ c} = V ∩ {y | f y < c} := by
  let C := {y | f y ≤ c}
  have hc : IsClosed C := isClosed_le hf continuous_const
  have hint {y : E} (hy : f y < c) : y ∈ interior C := by
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset ((isOpen_lt hf continuous_const).mem_nhds hy)
      (fun z (hz : f z < c) ↦ (show z ∈ C from hz.le))
  have hnot {y : E} (hy : y ∈ V) (he : f y = c) : y ∉ interior C := by
    have hn := not_mem_interior_levelSet_of_backward_increase hl hd (h y hy)
    simpa only [he] using hn
  constructor
  · ext y
    rw [hc.frontier_eq]
    constructor
    · rintro ⟨hy,hyC,hyi⟩
      exact ⟨hy,le_antisymm hyC (le_of_not_gt (fun hlt ↦ hyi (hint hlt)))⟩
    · rintro ⟨hy,he⟩
      exact ⟨hy,he.le,hnot hy he⟩
  · ext y
    constructor
    · rintro ⟨hy,hyi⟩
      have hle : f y ≤ c := (interior_subset (s := C) hyi : y ∈ C)
      exact ⟨hy,lt_of_le_of_ne hle (fun he ↦ hnot hy he hyi)⟩
    · rintro ⟨hy,hlt⟩
      exact ⟨hy,hint hlt⟩

/-- **Example 10.4**, pointed normals and the genuine Lipschitz epigraph
representation of a nonstationary level-set boundary. -/
theorem epiLipschitz_levelSet_of_zero_not_mem_convexHull_subdifferential
    (hf : ∀ y, StrictlyContinuousAt f y)
    (hz : (0:E) ∉ convexHull ℝ (subdifferential (fun y ↦ (f y:EReal)) x)) :
    let C := {y | f y ≤ f x}
    IsEpiLipschitzAt C x ∧ ∃ V ∈ 𝓝 x,
      V ∩ frontier C = V ∩ {y | f y = f x} ∧
      V ∩ interior C = V ∩ {y | f y < f x} := by
  let C := {y | f y ≤ f x}
  have hc : Continuous f := continuous_of_forall_strictlyContinuousAt hf
  have hclosed : IsClosed C := isClosed_le hc continuous_const
  have hsc : ERealStrictlyContinuousAt (fun y ↦ (f y:EReal)) x :=
    ⟨by simp,by simpa only [EReal.toReal_coe] using hf x⟩
  have hz' : (0:E) ∉ subdifferential (fun y ↦ (f y:EReal)) x :=
    fun h ↦ hz (subset_convexHull ℝ _ h)
  have hh := (eRealStrictlyContinuousAt_iff_horizonSubdifferential_eq_zero (f := fun y ↦ (f y:EReal))
    hsc.finite hsc.isLocallyLscAt).mp hsc
  have hnormal : normalCone C x ⊆ positiveHull (subdifferential (fun y ↦ (f y:EReal)) x) := by
    have hn := normalCone_levelSet_subset (f := fun y ↦ (f y:EReal))
      (continuous_coe_real_ereal.comp hc).lowerSemicontinuous
      (x := x) rfl hz'
    rw [hh,union_eq_left.mpr (singleton_subset_iff.mpr (zero_mem_positiveHull _))] at hn
    simpa only [levelSet,EReal.coe_le_coe_iff] using hn
  obtain ⟨hne,hcomp⟩ := hsc.subdifferential_nonempty_compact
  obtain ⟨w,hw,a,ha,hinner⟩ := exists_uniform_negative_inner hne hcomp hz
  have hpointed := (isPointed_positiveHull_of_inner_neg (fun v hv ↦ (hinner v hv).trans ha)).mono hnormal
  obtain ⟨v,hv,lam,hl,V,hV,δ,hd,hstep⟩ := (hf x).exists_uniform_two_sided_descent hz
  have hnot : x ∉ interior C := not_mem_interior_levelSet_of_backward_increase hl hd
    (fun t ht ↦ (hstep x (mem_of_mem_nhds hV) t ht).2)
  have hbound := levelSet_boundary_of_uniform_descent hc hl hd
    (c := f x) (fun y hy t ht ↦ (hstep y hy t ht).2)
  exact ⟨(isEpiLipschitzAt_iff_at_boundary (show x ∈ C from (le_rfl : f x ≤ f x)) hnot).mpr
    ⟨RW.IsClosed.isLocallyClosedAt hclosed x,hpointed⟩,V,hV,hbound⟩

end RW
