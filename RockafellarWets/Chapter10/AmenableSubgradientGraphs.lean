/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Relative closedness of amenable subgradient graphs
-/
import RockafellarWets.Chapter10.ConvexSubgradientMultiplierLimits

open Set Filter Topology

namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 10.25(b)**: the subgradient graph of an amenable model is
closed relative to a neighborhood times the subgradient space. -/
theorem AmenableFunctionModel.subgradientGraph_closed_relative
    {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) :
    ∃V : Set E, IsOpen V ∧ x ∈ V ∧ IsClosed {p : V × E | p.2 ∈ subdifferential f p.1} := by
  have hnear := (M.qualification_eventually hr).and (M.isOpen.mem_nhds M.mem)
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hnear
  refine ⟨V,hVo,hxV,isSeqClosed_iff_isClosed.mp ?_⟩
  intro ps p hps hp
  let ys (n : ℕ) : E := (ps n).1
  let us (n : ℕ) : E := (ps n).2
  have hy : Tendsto ys atTop (𝓝 (p.1:E)) := (continuous_subtype_val.tendsto p.1).comp hp.fst_nhds
  have hu : Tendsto us atTop (𝓝 p.2) := hp.snd_nhds
  have hvn (n : ℕ) := hV (ps n).1.property
  have hvp := hV p.1.property
  have hfin (n : ℕ) : f (ys n) ≠ ⊥ ∧ f (ys n) ≠ ⊤ := by
    obtain ⟨a,ha⟩ := (hps n).1
    exact ⟨by rw [ha]; exact EReal.coe_ne_bot a,by rw [ha]; exact EReal.coe_ne_top a⟩
  let Ms (n : ℕ) : AmenableFunctionModel f (ys n) r full :=
    { M with mem := (hvn n).2, finite := hfin n, qualification := (hvn n).1 }
  have him (n : ℕ) : us n ∈ (fderiv ℝ M.inner (ys n)).adjoint '' subdifferential M.outer (M.inner (ys n)) := by
    have hh := hps n
    change us n ∈ subdifferential f (ys n) at hh
    rwa [((Ms n).derivatives hr).1] at hh
  have hcont := M.smooth.continuousOn.continuousAt (M.isOpen.mem_nhds hvp.2)
  have hder := (M.smooth.continuousOn_fderiv_of_isOpen M.isOpen (by exact_mod_cast hr)).continuousAt
    (M.isOpen.mem_nhds hvp.2)
  obtain ⟨v,hv,he⟩ := mem_image_subdifferential_of_tendsto_of_convex M.proper M.lsc M.convex hcont
    (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hder) hvp.1 hy hu him
  obtain ⟨a,ha⟩ := hv.1
  have hfpoint : f p.1 = (a:EReal) := (M.eqOn p.1 hvp.2).trans ha
  have hfp : f p.1 ≠ ⊥ ∧ f p.1 ≠ ⊤ := by
    rw [hfpoint]
    exact ⟨EReal.coe_ne_bot a,EReal.coe_ne_top a⟩
  let N : AmenableFunctionModel f (p.1:E) r full :=
    { M with mem := hvp.2, finite := hfp, qualification := hvp.1 }
  change p.2 ∈ subdifferential f p.1
  rw [(N.derivatives hr).1]
  exact ⟨v,hv,he⟩

/-- **Exercise 10.25(b)**, the representation-free statement. -/
theorem AmenableAt.subgradientGraph_closed_relative {f : E → EReal} {x : E} (h : AmenableAt f x) :
    ∃V : Set E, IsOpen V ∧ x ∈ V ∧ IsClosed {p : V × E | p.2 ∈ subdifferential f p.1} := by
  obtain ⟨M⟩ := h
  exact M.subgradientGraph_closed_relative le_rfl

end RW
