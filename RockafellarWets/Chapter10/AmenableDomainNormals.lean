/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Domain normals induced by amenable representations
-/
import RockafellarWets.Chapter10.AmenableComposition

open Set Filter Topology
open scoped InnerProductSpace

namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Regular normals can be restricted to a locally smaller set. -/
theorem regularNormalCone_mono_local {C D : Set E} {x : E} (hx : x ∈ C)
    (hCD : ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ D) :
    regularNormalCone D x ⊆ regularNormalCone C x := by
  intro v hv
  refine ⟨hx,?_⟩
  intro ε hε
  have hfilter : 𝓝[C] x ≤ 𝓝[D] x := by
    apply nhdsWithin_le_iff.mpr
    filter_upwards [hCD.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with y hy hyC
    exact hy hyC
  exact Filter.Eventually.filter_mono hfilter (hv.2 ε hε)

/-- Every horizon subgradient of an amenable model is already a regular
normal to its domain. This direction does not require closedness of the domain. -/
theorem AmenableFunctionModel.horizon_subset_regularNormal_domain
    {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) :
    horizonSubdifferential f x ⊆ regularNormalCone (effectiveDomain f) x := by
  have hval : M.outer (M.inner x) = ((f x).toReal:EReal) := by
    rw [← M.eqOn x M.mem]
    exact (EReal.coe_toReal M.finite.2 M.finite.1).symm
  have hxD : M.inner x ∈ closure (effectiveDomain M.outer) := subset_closure (hval.trans_lt (EReal.coe_lt_top _))
  have hmd := ((M.smooth x M.mem).contDiffAt (M.isOpen.mem_nhds M.mem)).differentiableAt
    (by exact_mod_cast (show r ≠ 0 by omega))
  rw [(M.derivatives hr).2.1,horizonSubdifferential_eq_normalCone_closure_domain M.proper M.lsc M.convex hval,
    normalCone_eq_regularNormalCone_of_convex (convex_effectiveDomain_of_convex_epigraph M.convex).closure hxD]
  apply (adjoint_image_regularNormalCone_subset_preimage hmd.hasFDerivAt _).trans
  apply regularNormalCone_mono_local (C := effectiveDomain f)
    (D := M.inner ⁻¹' closure (effectiveDomain M.outer)) (x := x) (lt_top_iff_ne_top.mpr M.finite.2)
  filter_upwards [M.isOpen.mem_nhds M.mem] with y hy hdy
  apply subset_closure
  change M.outer (M.inner y) < ⊤
  rw [← M.eqOn y hy]
  exact hdy

theorem AmenableAt.horizon_subset_normal_domain {f : E → EReal} {x : E}
    (h : AmenableAt f x) : horizonSubdifferential f x ⊆ normalCone (effectiveDomain f) x := by
  obtain ⟨M⟩ := h
  exact (M.horizon_subset_regularNormal_domain le_rfl).trans (regularNormalCone_subset_normalCone _ _)

end RW
