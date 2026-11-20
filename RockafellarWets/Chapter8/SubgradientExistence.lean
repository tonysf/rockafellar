/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Existence of subgradients
-/

import RockafellarWets.Chapter8.SubdifferentialRegularityCriterion
import RockafellarWets.Chapter6.BoundaryNormals
import RockafellarWets.Chapter3.ConvexHullFunctionSharp

open Filter Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {x : E} {c : ℝ}

/-- **Corollary 8.10.** A finite point of a locally lower semicontinuous
function has an ordinary subgradient or a nonzero horizon subgradient. -/
theorem subdifferential_nonempty_or_exists_nonzero_horizon (hl : IsLocallyLscAt f x)
    (hx : f x = c) :
    (subdifferential f x).Nonempty ∨ ∃ v ∈ horizonSubdifferential f x, v ≠ 0 := by
  let g := epiClosure f
  let p := WithLp.toLp 2 (x,c)
  have hgc : g x = c := (epiClosure_eq_of_lowerSemicontinuousAt hl.lowerSemicontinuousAt).trans hx
  have hcl : IsClosed (euclideanEpigraph g) :=
    (isClosed_epigraph_of_lsc_ereal g (lowerSemicontinuous_epiLowerLimit _)).preimage
      (l2ProdEquiv E).continuous
  have hbd : p ∈ frontier (euclideanEpigraph g) := by
    rw [hcl.frontier_eq]
    refine ⟨hgc.le,?_⟩
    change p ∉ interior ((l2ProdEquiv E).toHomeomorph ⁻¹' epigraph g)
    rw [← (l2ProdEquiv E).toHomeomorph.preimage_interior]
    exact graphPoint_not_mem_interior_epigraph hgc.symm
  obtain ⟨n,hn,hne⟩ := (mem_frontier_iff_exists_nonzero_normal hcl).mp hbd
  obtain ⟨⟨v,b⟩,rfl⟩ := (WithLp.toLp_surjective 2) n
  rw [← normalCone_congr_nhds (hl.euclideanEpigraph_eventuallyEq_epiClosure hx)] at hn
  rcases (mem_normalCone_epigraph_iff_slices hl hx).mp hn with ⟨_,hv⟩ | ⟨rfl,hv⟩
  · exact Or.inl ⟨_,hv⟩
  · exact Or.inr ⟨v,hv,fun he ↦ hne (he ▸ rfl)⟩

/-- The ordinary and directional subgradients together give a nonempty
set in the cosmic compactification. -/
theorem cosmicSet_subdifferential_nonempty (hl : IsLocallyLscAt f x) (hx : f x = c) :
    (cosmicSet (subdifferential f x) (horizonSubdifferential f x)).Nonempty := by
  rcases subdifferential_nonempty_or_exists_nonzero_horizon hl hx with ⟨v,hv⟩ | ⟨v,hv,hne⟩
  · exact ⟨cosmicEmbed v,cosmicEmbed_mem_cosmicSet_iff.mpr hv⟩
  · refine ⟨cosmicDirection (cosmicDirectionOf v hne),mem_cosmicSet.mpr (Or.inr
      ⟨cosmicDirectionOf v hne,?_,rfl⟩)⟩
    rw [coe_cosmicDirectionOf, NormedSpace.normalize]
    exact (subdifferential_properties hx).2.2.2.2.1.smul_mem hv (inv_nonneg.mpr (norm_nonneg v))

/-- Regular subgradients exist along a function-attentive sequence approaching
every finite point of local lower semicontinuity. -/
theorem exists_attentive_seq_regularSubdifferential_nonempty (hl : IsLocallyLscAt f x)
    (hx : f x = c) :
    ∃ y : ℕ → E, Tendsto y atTop (attentiveNhds f x) ∧
      ∀ n, (regularSubdifferential f (y n)).Nonempty ∧ (subdifferential f (y n)).Nonempty := by
  suffices h : ∃ y : ℕ → E, Tendsto y atTop (attentiveNhds f x) ∧
      ∀ n, (regularSubdifferential f (y n)).Nonempty by
    obtain ⟨y,hy,hs⟩ := h
    exact ⟨y,hy,fun n ↦ ⟨hs n,(hs n).mono (regularSubdifferential_subset_subdifferential f _)⟩⟩
  rcases subdifferential_nonempty_or_exists_nonzero_horizon hl hx with ⟨v,hv⟩ | ⟨v,hv,hne⟩
  · obtain ⟨_,y,w,hy,hf,hw,_⟩ := mem_subdifferential_iff_exists_seq.mp hv
    exact ⟨y,tendsto_attentiveNhds_iff.mpr ⟨hy,hf⟩,fun n ↦ ⟨w n,hw n⟩⟩
  · obtain ⟨y,w,_,hy,hw,_⟩ := ((mem_horizonSubdifferential_iff_zero_or_scaledSeq hx).mp hv).resolve_left hne
    exact ⟨y,hy,fun n ↦ ⟨w n,hw n⟩⟩

end RW
