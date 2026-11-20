/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Localizing the outer mapping in Exercise 10.39
-/

import RockafellarWets.Chapter10.GraphGerms
import RockafellarWets.Chapter10.CompositionModulusMax
import RockafellarWets.Chapter10.CompositionHausdorffModulus
import RockafellarWets.Chapter9.SingleValuedGraphicalDerivatives

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : E → Set F} {f : F → G} {x : E} {u : G}

/-- A singleton mapping with its input restricted to a compact set. -/
def restrictedSingleton (f : F → G) (C : Set F) (w : F) : Set G := {v | w ∈ C ∧ v = f w}

theorem svOsc_restrictedSingleton {C : Set F} (hC : IsCompact C) (hf : ContinuousOn f C) :
    SvOsc (restrictedSingleton f C) := by
  apply isClosed_svGraph_iff_svOsc.mp
  have he : svGraph (restrictedSingleton f C) = (fun w ↦ (w,f w)) '' C := by
    ext p
    exact ⟨fun h ↦ ⟨p.1,h.1,Prod.ext rfl h.2.symm⟩,fun ⟨w,hw,he⟩ ↦ by simpa only [← he] using ⟨hw,rfl⟩⟩
  rw [he]
  exact (hC.image_of_continuousOn (continuousOn_id.prodMk hf)).isClosed

theorem restrictedSingleton_eventuallyEq {C : Set F} {w : F} (hw : w ∈ interior C) :
    restrictedSingleton f C =ᶠ[𝓝 w] svSingleton f := by
  filter_upwards [isOpen_interior.mem_nhds hw] with z hz
  ext v
  simp only [restrictedSingleton,mem_setOf_eq,interior_subset hz,true_and,svSingleton,mem_singleton_iff]

/-- Only continuity on the base fiber is needed for outer semicontinuity
of the intermediate-value mapping at the selected graph point. -/
theorem svOscAt_singletonCompAux (hS : SvOscAt S x) (hf : ∀ w ∈ S x, ContinuousAt f w) :
    SvOscAt (svCompAux (svSingleton f) S) (x,u) := by
  intro w hw
  obtain ⟨p,z,hp,hpz,hz⟩ := mem_outerSetLimitAlong_iff_exists_seq.mp hw
  have hwS : w ∈ S x := hS (mem_outerSetLimitAlong_iff_exists_seq.mpr
    ⟨fun n ↦ (p n).1,z,(continuous_fst.tendsto (x,u)).comp hp,fun n ↦ (hpz n).1,hz⟩)
  refine ⟨hwS,?_⟩
  have he (n : ℕ) : (p n).2 = f (z n) := (hpz n).2
  have ht : Tendsto (fun n ↦ (p n).2) atTop (𝓝 (f w)) := by
    simpa only [he] using (hf w hwS).tendsto.comp hz
  exact tendsto_nhds_unique ((continuous_snd.tendsto (x,u)).comp hp) ht

/-- A compact cutoff around all relevant intermediate values gives a
closed-graph outer mapping, while preserving the composition graph germ. -/
theorem exists_outerComposition_cutoff (hS : SvOsc S)
    (hf : ∀ w ∈ S x, StrictlyContinuousAt f w)
    (hb : SvLocallyBoundedAt (svCompAux (svSingleton f) S) (x,u)) :
    ∃ C : Set F, IsCompact C ∧
      svCompAux (svSingleton f) S (x,u) ⊆ interior C ∧
      (∀ w ∈ C, StrictlyContinuousAt f w) ∧
      SvOsc (restrictedSingleton f C) ∧
      SvLocallyBoundedAt (svCompAux (restrictedSingleton f C) S) (x,u) ∧
      svCompAux (restrictedSingleton f C) S (x,u) = svCompAux (svSingleton f) S (x,u) ∧
      svGraph (svComp (restrictedSingleton f C) S) =ᶠ[𝓝 (x,u)] svGraph (svComp (svSingleton f) S) := by
  have ho := svOscAt_singletonCompAux (u := u) (hS x) (fun w hw ↦ (hf w hw).continuousAt)
  have hK : IsCompact (svCompAux (svSingleton f) S (x,u)) :=
    Metric.isCompact_of_isClosed_isBounded ho.isClosed hb.isBounded_apply
  obtain ⟨C,hC,hKC,hCf⟩ := exists_compact_between hK (isOpen_setOf_strictlyContinuousAt f)
    (fun w hw ↦ hf w hw.1)
  have hosc := svOsc_restrictedSingleton hC (fun w hw ↦ (hCf hw).continuousAt.continuousWithinAt)
  have hb' : SvLocallyBoundedAt (svCompAux (restrictedSingleton f C) S) (x,u) := by
    obtain ⟨V,hV,hbV⟩ := hb
    refine ⟨V,hV,hbV.subset ?_⟩
    intro w hw
    obtain ⟨p,hp,hw⟩ := mem_svImage.mp hw
    exact mem_svImage.mpr ⟨p,hp,hw.1,hw.2.2⟩
  have heK : svCompAux (restrictedSingleton f C) S (x,u) = svCompAux (svSingleton f) S (x,u) := by
    ext w
    exact ⟨fun h ↦ ⟨h.1,h.2.2⟩,fun h ↦ ⟨h.1,interior_subset (hKC h),h.2⟩⟩
  obtain ⟨V,hV,hVC⟩ := ho.exists_nhds_svImage_subset hb isOpen_interior hKC
  refine ⟨C,hC,hKC,hCf,hosc,hb',heK,?_⟩
  filter_upwards [hV] with p hp
  apply propext
  constructor
  · intro h
    obtain ⟨w,hw,hv⟩ := mem_svComp.mp h
    exact mem_svComp.mpr ⟨w,hw,hv.2⟩
  · intro h
    obtain ⟨w,hw,hv⟩ := mem_svComp.mp h
    exact mem_svComp.mpr ⟨w,hw,interior_subset (hVC (mem_svImage.mpr ⟨p,hp,hw,hv⟩)),hv⟩

end RW
