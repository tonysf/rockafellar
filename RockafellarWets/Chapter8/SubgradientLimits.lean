/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Attentive outer semicontinuity of subgradients

A second attentive outer limit cannot add new points to the first. Applying
this observation in cosmic space proves the ordinary and horizon assertions
simultaneously.
-/

import RockafellarWets.Chapter8.Subgradients

open Filter Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] {f : E → EReal}

/-- Function-attentive convergence is ordinary convergence on the graph
with its product topology. -/
theorem attentiveNhds_eq_comap_graph (f : E → EReal) (x : E) :
    attentiveNhds f x = comap (fun y ↦ (y, f y)) (𝓝 (x, f x)) := by
  rw [nhds_prod_eq, comap_prod]
  change _ = comap id (𝓝 x) ⊓ comap f (𝓝 (f x))
  rw [comap_id]
  rfl

theorem pure_le_attentiveNhds (f : E → EReal) (x : E) : pure x ≤ attentiveNhds f x := by
  rw [attentiveNhds_eq_comap_graph, ← map_le_iff_le_comap, map_pure]
  exact pure_le_nhds _

instance (f : E → EReal) (x : E) : (attentiveNhds f x).NeBot :=
  neBot_of_le (pure_le_attentiveNhds f x)

/-- A property that holds near a point in the attentive topology also holds
near each sufficiently close attentive base point. -/
theorem eventually_eventually_attentiveNhds {x : E} {P : E → Prop}
    (h : ∀ᶠ z in attentiveNhds f x, P z) :
    ∀ᶠ y in attentiveNhds f x, ∀ᶠ z in attentiveNhds f y, P z := by
  rw [attentiveNhds_eq_comap_graph] at h ⊢
  obtain ⟨V, hV, hsub⟩ := h
  obtain ⟨W, hWV, hWo, hxW⟩ := mem_nhds_iff.mp hV
  filter_upwards [preimage_mem_comap (m := fun y ↦ (y,f y)) (hWo.mem_nhds hxW)] with y hy
  rw [attentiveNhds_eq_comap_graph]
  exact ⟨W, hWo.mem_nhds hy, (preimage_mono hWV).trans hsub⟩

private theorem outer_attentive_idempotent {B : Type*} [TopologicalSpace B] (f : E → EReal)
    (F : E → Set B) (x : E) :
    outerSetLimitAlong (attentiveNhds f x) (fun y ↦ outerSetLimitAlong (attentiveNhds f y) F) ⊆
      outerSetLimitAlong (attentiveNhds f x) F := by
  intro v hv V hV
  obtain ⟨W, hWV, hWo, hvW⟩ := mem_nhds_iff.mp hV
  by_contra hno
  have hmiss := eventually_eventually_attentiveNhds (not_frequently.mp hno)
  obtain ⟨y, ⟨z, hz, hzW⟩, hy⟩ := ((hv W (hWo.mem_nhds hvW)).and_eventually hmiss).exists
  exact (not_frequently.mpr hy) (hz V (mem_of_superset (hWo.mem_nhds hzW) hWV))

variable [InnerProductSpace ℝ E]

/-- Formula 8(6). Combining ordinary and horizon subgradients gives the
outer limit in the cosmic compactification. -/
theorem cosmicSet_subdifferential {x : E} {c : ℝ} (hx : f x = c) :
    cosmicSet (subdifferential f x) (horizonSubdifferential f x) =
      outerSetLimitAlong (attentiveNhds f x) (ordinaryCosmicFamily (regularSubdifferential f)) := by
  rw [subdifferential_of_finite hx, horizonSubdifferential_of_finite hx,
    outerSetLimitAlong_ordinaryCosmicFamily]

/-- **Proposition 8.7.** The limiting subdifferential is outer semicontinuous
under function-attentive convergence to any finite graph point. -/
theorem outerSetLimitAlong_subdifferential_subset {x : E} {c : ℝ} (hx : f x = c) :
    outerSetLimitAlong (attentiveNhds f x) (subdifferential f) ⊆ subdifferential f x := by
  rw [subdifferential_of_finite hx]
  exact (outerSetLimitAlong_mono (fun _ _ h ↦ h.2)).trans
    (outer_attentive_idempotent f (regularSubdifferential f) x)

/-- **Proposition 8.7**, cosmic outer semicontinuity. -/
theorem outerSetLimitAlong_cosmicSubdifferential_subset {x : E} {c : ℝ} (hx : f x = c) :
    outerSetLimitAlong (attentiveNhds f x)
      (fun y ↦ cosmicSet (subdifferential f y) (horizonSubdifferential f y)) ⊆
        cosmicSet (subdifferential f x) (horizonSubdifferential f x) := by
  rw [cosmicSet_subdifferential hx]
  apply (outerSetLimitAlong_mono ?_).trans (outer_attentive_idempotent f _ x)
  intro y
  rw [outerSetLimitAlong_ordinaryCosmicFamily]
  exact cosmicSet_mono (fun _ h ↦ h.2) (fun _ h ↦ h.2)

/-- **Proposition 8.7**, horizon outer semicontinuity. -/
theorem outerSetLimitAlong_horizonSubdifferential_subset [FiniteDimensional ℝ E] {x : E}
    {c : ℝ} (hx : f x = c) :
    outerSetLimitAlong (attentiveNhds f x) (horizonSubdifferential f) ⊆
      horizonSubdifferential f x := by
  let l := attentiveNhds f x
  let C := fun y ↦ outerSetLimitAlong (attentiveNhds f y) (regularSubdifferential f)
  let K := fun y ↦ horizonOuterSetLimitAlong (attentiveNhds f y) (regularSubdifferential f)
  have hK (y : E) : IsCone (K y) := isCone_horizonOuterSetLimitAlong _ _
  have hcos : outerSetLimitAlong l (fun y ↦ cosmicSet (C y) (K y)) ⊆ cosmicSet (C x) (K x) := by
    simpa only [C, K, l, ← outerSetLimitAlong_ordinaryCosmicFamily] using
      outer_attentive_idempotent f (ordinaryCosmicFamily (regularSubdifferential f)) x
  rw [outerSetLimitAlong_cosmicSet C K hK] at hcos
  have hdir := ((cosmicSet_subset_iff
    ((isCone_horizonOuterSetLimitAlong l C).union (isCone_outerSetLimitAlong hK)) (hK x)).mp hcos).2
  rw [horizonSubdifferential_of_finite hx]
  exact (outerSetLimitAlong_mono (fun _ _ h ↦ h.2)).trans (subset_union_right.trans hdir)

end RW
