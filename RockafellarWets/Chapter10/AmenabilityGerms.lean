/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Locality of amenability and closure of fully amenable domains
-/
import RockafellarWets.Chapter10.FullyAmenableDomains

open Set Filter Topology

noncomputable section
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A set model is unchanged by replacing its set by an equal local germ. -/
def AmenableSetModel.congr_nhds {C D : Set E} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableSetModel C x r full) (he : C =ᶠ[𝓝 x] D) : AmenableSetModel D x r full := by
  apply Classical.choice
  change Nonempty (AmenableSetModel D x r full)
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp he
  exact ⟨{
    M with
    neighborhood := M.neighborhood ∩ V
    isOpen := M.isOpen.inter hVo
    mem := ⟨M.mem,hxV⟩
    base := (Iff.of_eq he.self_of_nhds).mp M.base
    smooth := M.smooth.mono inter_subset_left
    eqOn := fun y hy ↦ (show y ∈ D ↔ y ∈ C from Iff.of_eq (hV hy.2).symm).trans (M.eqOn y hy.1) }⟩

/-- A locally closed set agrees with its closure near the base point. -/
theorem IsLocallyClosedAt.eventuallyEq_closure {C : Set E} {x : E}
    (h : IsLocallyClosedAt C x) : C =ᶠ[𝓝 x] (show Set E from closure C) := by
  obtain ⟨V,hV,_,hCV⟩ := h
  obtain ⟨U,hUV,hU,hxU⟩ := mem_nhds_iff.mp hV
  filter_upwards [hU.mem_nhds hxU] with y hy
  apply propext
  change y ∈ C ↔ y ∈ closure C
  constructor
  · intro hyC
    exact subset_closure hyC
  · intro hyC
    have hh : y ∈ closure (U ∩ C) := hU.inter_closure ⟨hy,hyC⟩
    have hsub : U ∩ C ⊆ C ∩ V := fun z hz ↦ ⟨hz.2,hUV hz.1⟩
    exact (closure_minimal hsub hCV hh).1

/-- **Definition 10.23**, closure of the domain preserves full amenability. -/
theorem FullyAmenableAt.closure_domain {f : E → EReal} {x : E} (h : FullyAmenableAt f x) :
    SetFullyAmenableAt (closure (effectiveDomain f)) x := by
  obtain ⟨M⟩ := h.domain
  exact ⟨M.congr_nhds h.polyhedral_properties.1.eventuallyEq_closure⟩

end RW
end
