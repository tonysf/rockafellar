/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Subgradient proto-differentiability from amenability

Corollary 13.41.  Full amenability persists at the points of `dom f` near `x̄` (10.25(b)); at such
points `f` is prox-regular and subdifferentially continuous for every subgradient (13.32) and twice
epi-differentiable (13.15), so Theorem 13.40 applies.
-/

import RockafellarWets.Chapter13.SubgradientProtoDifferentiability
import RockafellarWets.Chapter13.SecondOrderChainRuleAmenable
import RockafellarWets.Chapter13.AmenableProxRegularity

open Filter Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- At a point of full amenability, `∂f` is proto-differentiable for every subgradient, with
`D(∂f)(x̄ | v̄) = ∂[½d²f(x̄ | v̄)]`. -/
theorem FullyAmenableAt.isProtoDifferentiableAt {f : E → EReal} {x v : E}
    (hf : FullyAmenableAt f x) (hv : v ∈ subdifferential f x) :
    IsProtoDifferentiableAt (subdifferential f) x v ∧
      graphicalDerivative (subdifferential f) x v =
        subdifferential (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x v w) := by
  obtain ⟨hpr, hsc⟩ := hf.stronglyAmenableAt.isProxRegularAt hv
  have hte := (hf.properlyTwiceEpiDifferentiableAt hv).1
  obtain ⟨h1, h2⟩ := (proto_differentiability_of_subgradient_mappings hpr).1 hsc
  exact ⟨h1.2 hte, h2 hte⟩

/-- **Corollary 13.41** (subgradient proto-differentiability from amenability): if `f` is fully
amenable at `x̄`, there is a neighborhood `V` of `x̄` such that `∂f` is proto-differentiable at `x`
for `v` whenever `x ∈ V ∩ dom f` and `v ∈ ∂f(x)`. -/
theorem subgradient_proto_differentiability_from_amenability {f : E → EReal} {x : E}
    (hf : FullyAmenableAt f x) :
    ∃ V ∈ 𝓝 x, ∀ y ∈ V ∩ effectiveDomain f, ∀ v ∈ subdifferential f y,
      IsProtoDifferentiableAt (subdifferential f) y v :=
  ⟨_, hf.eventually, fun _ ⟨hy, hyd⟩ _ hv ↦ ((hy hyd).isProtoDifferentiableAt hv).1⟩

end RW
