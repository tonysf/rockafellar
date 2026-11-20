/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Domains of amenable functions with closed outer domain
-/
import RockafellarWets.Chapter10.AmenableFunctionCalculus

open Set

noncomputable section
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A closed outer domain gives an amenable model of the function domain
with the same smoothness and polyhedrality. -/
def AmenableFunctionModel.domain_of_isClosed {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hD : IsClosed (effectiveDomain M.outer)) :
    AmenableSetModel (effectiveDomain f) x r full where
  Target := M.Target
  constraint := effectiveDomain M.outer
  inner := M.inner
  neighborhood := M.neighborhood
  isOpen := M.isOpen
  mem := M.mem
  base := lt_top_iff_ne_top.mpr M.finite.2
  closed := hD
  convex := convex_effectiveDomain_of_convex_epigraph M.convex
  smooth := M.smooth
  eqOn := by
    intro y hy
    change f y < ⊤ ↔ M.outer (M.inner y) < ⊤
    rw [M.eqOn y hy]
  qualification := by
    simpa only [hD.closure_eq] using M.qualification
  polyhedral := fun h ↦ (M.plq h).isPolyhedral_effectiveDomain M.convex

/-- **Definition 10.23**, the domain of a fully amenable function is fully
amenable at its base point. -/
theorem FullyAmenableAt.domain {f : E → EReal} {x : E} (h : FullyAmenableAt f x) :
    SetFullyAmenableAt (effectiveDomain f) x := by
  obtain ⟨M⟩ := h
  exact ⟨M.domain_of_isClosed (M.plq rfl).isClosed_effectiveDomain⟩

/-- The domain-normal identity holds for every amenable representation
whose outer domain is closed. -/
theorem AmenableFunctionModel.horizon_eq_normal_domain_of_isClosed
    {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r)
    (hD : IsClosed (effectiveDomain M.outer)) :
    horizonSubdifferential f x = normalCone (effectiveDomain f) x := by
  have hval : M.outer (M.inner x) = ((f x).toReal:EReal) := by
    rw [← M.eqOn x M.mem]
    exact (EReal.coe_toReal M.finite.2 M.finite.1).symm
  rw [(M.derivatives hr).2.1,(M.domain_of_isClosed hD).cones hr |>.2.1]
  change (fderiv ℝ M.inner x).adjoint '' horizonSubdifferential M.outer (M.inner x) =
    (fderiv ℝ M.inner x).adjoint '' normalCone (effectiveDomain M.outer) (M.inner x)
  rw [horizonSubdifferential_eq_normalCone_domain_of_locallyLsc M.convex M.proper
    (locallyLscAt_of_lowerSemicontinuous_finite M.lsc hval) hval]

/-- **Exercise 10.25(a)**, the domain-normal identity in the fully amenable case. -/
theorem FullyAmenableAt.horizon_eq_normal_domain {f : E → EReal} {x : E}
    (h : FullyAmenableAt f x) : horizonSubdifferential f x = normalCone (effectiveDomain f) x := by
  obtain ⟨M⟩ := h
  exact M.horizon_eq_normal_domain_of_isClosed (by norm_num) (M.plq rfl).isClosed_effectiveDomain

end RW
end
