/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Graphically Lipschitzian mappings

Definition 9.66 and its single-valued and inverse examples. A local change
of coordinates is represented by two maps that are C¹ near the respective
base points and inverse there. The target coordinates have dimensions
`d` and `e`, with `d + e = dim E + dim F`.
-/

import RockafellarWets.Chapter9.LipschitzModulus
import RockafellarWets.Chapter5.LocallyBoundedContinuity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open Filter Metric Set Topology
open scoped NNReal

namespace RW

section Coordinates

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A change of coordinates near `x`, continuously differentiable in both
directions. The inverse identities are required on neighborhoods, while
the globally defined representatives outside those neighborhoods are irrelevant. -/
def IsC1CoordinateChangeAt (Φ : X → Y) (Ψ : Y → X) (x : X) : Prop :=
  ContDiffAt ℝ 1 Φ x ∧ ContDiffAt ℝ 1 Ψ (Φ x) ∧ Ψ (Φ x) = x ∧
    (∀ᶠ z in 𝓝 x, Ψ (Φ z) = z) ∧ ∀ᶠ z in 𝓝 (Φ x), Φ (Ψ z) = z

theorem isC1CoordinateChangeAt_continuousLinearEquiv (L : X ≃L[ℝ] Y) (x : X) :
    IsC1CoordinateChangeAt L L.symm x :=
  ⟨L.contDiff.contDiffAt,L.symm.contDiff.contDiffAt,L.symm_apply_apply x,
    Eventually.of_forall L.symm_apply_apply,Eventually.of_forall L.apply_symm_apply⟩

end Coordinates

section Definition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Definition 9.66.** Near a graph point, a `C¹` change of coordinates
identifies the graph with the graph of a Lipschitz mapping on a neighborhood
in `ℝᵈ`. The complementary dimension is explicitly constrained to be
`dim E + dim F - d`. -/
def GraphicallyLipschitzianAt (S : E → Set F) (x : E) (u : F) (d : ℕ) : Prop :=
  u ∈ S x ∧ ∃ e : ℕ, d + e = Module.finrank ℝ E + Module.finrank ℝ F ∧
    ∃ (Φ : (E × F) → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e))
      (Ψ : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)) → E × F)
      (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin e)),
      IsC1CoordinateChangeAt Φ Ψ (x,u) ∧ StrictlyContinuousAt g (Φ (x,u)).1 ∧
        ∀ᶠ z in 𝓝 (x,u), z ∈ svGraph S ↔ (Φ z).2 = g (Φ z).1

theorem GraphicallyLipschitzianAt.mem {S : E → Set F} {x : E} {u : F} {d : ℕ}
    (h : GraphicallyLipschitzianAt S x u d) : u ∈ S x := h.1

theorem GraphicallyLipschitzianAt.dimension_le {S : E → Set F} {x : E} {u : F} {d : ℕ}
    (h : GraphicallyLipschitzianAt S x u d) : d ≤ Module.finrank ℝ E + Module.finrank ℝ F := by
  obtain ⟨_,e,he,_⟩ := h
  omega

/-- At the base point the coordinate image belongs to the selected
Lipschitz graph; this follows from the graph-germ identity. -/
theorem IsC1CoordinateChangeAt.base_graph_of_eventually_graph
    {S : E → Set F} {x : E} {u : F} (hu : u ∈ S x) {d e : ℕ}
    {Φ : (E × F) → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)}
    {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin e)}
    (hgraph : ∀ᶠ z in 𝓝 (x,u), z ∈ svGraph S ↔ (Φ z).2 = g (Φ z).1) :
    (Φ (x,u)).2 = g (Φ (x,u)).1 := hgraph.self_of_nhds.mp hu

/-- A linear change of coordinates giving a local Lipschitz graph is a
particular graphically Lipschitzian representation. -/
theorem graphicallyLipschitzianAt_of_linear_graph
    {S : E → Set F} {x : E} {u : F} (hu : u ∈ S x) {d e : ℕ}
    (hd : d + e = Module.finrank ℝ E + Module.finrank ℝ F)
    (L : (E × F) ≃L[ℝ] (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin e))
    (hg : StrictlyContinuousAt g (L (x,u)).1)
    (hgraph : ∀ᶠ z in 𝓝 (x,u), z ∈ svGraph S ↔ (L z).2 = g (L z).1) :
    GraphicallyLipschitzianAt S x u d :=
  ⟨hu,e,hd,L,L.symm,g,isC1CoordinateChangeAt_continuousLinearEquiv L (x,u),hg,hgraph⟩

end Definition

section Examples

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private theorem strictlyContinuousAt_coordinates {f : E → F} {x : E}
    (hf : StrictlyContinuousAt f x)
    (A : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (B : F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) :
    StrictlyContinuousAt (fun a ↦ B (f (A.symm a))) (A x) := by
  obtain ⟨k,U,hU,hL⟩ := strictlyContinuousAt_iff.mp hf
  have hV : A.symm ⁻¹' U ∈ 𝓝 (A x) := by
    apply A.symm.continuous.continuousAt.preimage_mem_nhds
    simpa only [A.symm_apply_apply] using hU
  exact strictlyContinuousAt_iff.mpr ⟨‖B.toContinuousLinearMap‖₊ * (k * ‖A.symm.toContinuousLinearMap‖₊),
    A.symm ⁻¹' U,hV,B.toContinuousLinearMap.lipschitz.comp_lipschitzOnWith
      (hL.comp (fun _ _ _ _ ↦ A.symm.toContinuousLinearMap.lipschitz _ _) (fun _ ha ↦ ha))⟩

/-- **Definition 9.66**, first example: a strictly continuous single-valued
mapping is graphically Lipschitzian, of its domain dimension. -/
theorem StrictlyContinuousAt.graphicallyLipschitzianAt_singleton {f : E → F} {x : E}
    (hf : StrictlyContinuousAt f x) :
    GraphicallyLipschitzianAt (svSingleton f) x (f x) (Module.finrank ℝ E) := by
  let A := (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv
  let B := (stdOrthonormalBasis ℝ F).repr.toContinuousLinearEquiv
  let L := A.prodCongr B
  let g := fun a ↦ B (f (A.symm a))
  apply graphicallyLipschitzianAt_of_linear_graph
    (show f x ∈ svSingleton f x from rfl) rfl L g
    (strictlyContinuousAt_coordinates hf A B)
  exact Eventually.of_forall fun z ↦ by
    change z.2 = f z.1 ↔ B z.2 = B (f (A.symm (A z.1)))
    rw [A.symm_apply_apply,B.injective.eq_iff]

/-- **Definition 9.66**, second example: the inverse of a strictly
continuous single-valued mapping is graphically Lipschitzian, with the
same dimension. The coordinate change interchanges the two graph axes. -/
theorem StrictlyContinuousAt.graphicallyLipschitzianAt_inverse_singleton {f : E → F} {x : E}
    (hf : StrictlyContinuousAt f x) :
    GraphicallyLipschitzianAt (svInv (svSingleton f)) (f x) x (Module.finrank ℝ E) := by
  let A := (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv
  let B := (stdOrthonormalBasis ℝ F).repr.toContinuousLinearEquiv
  let L := (ContinuousLinearEquiv.prodComm ℝ F E).trans (A.prodCongr B)
  let g := fun a ↦ B (f (A.symm a))
  apply graphicallyLipschitzianAt_of_linear_graph (show x ∈ svInv (svSingleton f) (f x) from rfl)
    (Nat.add_comm _ _) L g (strictlyContinuousAt_coordinates hf A B)
  exact Eventually.of_forall fun z ↦ by
    change z.1 = f z.2 ↔ B z.1 = B (f (A.symm (A z.2)))
    rw [A.symm_apply_apply,B.injective.eq_iff]

end Examples

end RW
