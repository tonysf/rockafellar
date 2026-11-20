/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Calmness of piecewise polyhedral mappings
-/

import RockafellarWets.Chapter9.PolyhedralLipschitz

open Filter Metric Set Topology
open scoped NNReal BigOperators

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The one-base-point Lipschitz estimate (9.30), with a specified constant. -/
def SvCalmAtWith (k : ℝ≥0) (S : E → Set F) (x : E) : Prop :=
  (S x).Nonempty ∧ ∀ᶠ a in 𝓝 x, ∀ u ∈ S a, ∃ v ∈ S x, dist u v ≤ k * dist a x

def SvCalmAt (S : E → Set F) (x : E) : Prop := ∃ k, SvCalmAtWith k S x

/-- A set is piecewise polyhedral when it is a finite union of polyhedra. -/
def IsPiecewisePolyhedral {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : Set G) : Prop :=
  ∃ m : ℕ, ∃ C : Fin m → Set G, (∀ i, IsPolyhedral (C i)) ∧ A = ⋃ i, C i

/-- Projection preserves polyhedrality, so a polyhedral mapping has closed domain. -/
theorem isClosed_svDom_of_isPolyhedral_graph {S : E → Set F}
    (hp : IsPolyhedral (svGraph S)) : IsClosed (svDom S) := by
  have he : svDom S = (LinearMap.fst ℝ E F) '' svGraph S := by
    ext x
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨(x,u),hu,rfl⟩
    · rintro ⟨⟨a,u⟩,hu,rfl⟩
      exact ⟨u,hu⟩
  rw [he]
  exact (hp.linear_image (LinearMap.fst ℝ E F)).isClosed

/-- A finite union of mappings with closed domains and a global Lipschitz
estimate on each domain has a common calmness constant at all domain points. -/
theorem exists_calm_constant_iUnion {ι : Type*} [Fintype ι] (S : ι → E → Set F)
    (hclosed : ∀ i, IsClosed (svDom (S i)))
    (hlip : ∀ i, SvLipschitzOn (S i) (svDom (S i))) :
    ∃ k : ℝ≥0, ∀ x ∈ svDom (fun a ↦ ⋃ i, S i a), SvCalmAtWith k (fun a ↦ ⋃ i, S i a) x := by
  classical
  choose ks hks using hlip
  let k : ℝ≥0 := ∑ i, ks i
  refine ⟨k,fun x hx ↦ ⟨hx,?_⟩⟩
  have hnear : ∀ᶠ a in 𝓝 x, ∀ i, a ∈ svDom (S i) → x ∈ svDom (S i) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x ∈ svDom (S i)
    · exact .of_forall fun _ _ ↦ hi
    · filter_upwards [(hclosed i).isOpen_compl.mem_nhds hi] with a ha ha'
      exact (ha ha').elim
  filter_upwards [hnear] with a ha u hu
  obtain ⟨i,hi⟩ := mem_iUnion.mp hu
  have hai : a ∈ svDom (S i) := ⟨u,hi⟩
  obtain ⟨v,hv,hbound⟩ := (svLipschitzOnWith_iff_transport (hks i).1).mp (hks i) a hai x (ha i hai) u hi
  refine ⟨v,mem_iUnion.mpr ⟨i,hv⟩,hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (show (ks i : ℝ) ≤ k from NNReal.coe_le_coe.mpr (Finset.single_le_sum (fun _ _ ↦ zero_le _) (Finset.mem_univ i)))
    dist_nonneg

/-- **Example 9.57.** A piecewise polyhedral mapping is calm at every point
of its domain. The same constant works at every point; the neighborhoods may vary. -/
theorem exists_calm_constant_of_piecewisePolyhedral_graph {S : E → Set F}
    (hS : IsPiecewisePolyhedral (svGraph S)) :
    ∃ k : ℝ≥0, ∀ x ∈ svDom S, SvCalmAtWith k S x := by
  obtain ⟨m,C,hC,hG⟩ := hS
  let T (i : Fin m) (x : E) : Set F := {u | (x,u) ∈ C i}
  have hT (i : Fin m) : IsPolyhedral (svGraph (T i)) := hC i
  have he : S = fun x ↦ ⋃ i, T i x := by
    funext x
    ext u
    change (x,u) ∈ svGraph S ↔ _
    rw [hG]
    simp only [mem_iUnion,T,mem_setOf_eq]
  rw [he]
  exact exists_calm_constant_iUnion T
    (fun i ↦ isClosed_svDom_of_isPolyhedral_graph (hT i))
    (fun i ↦ svLipschitzOn_of_isPolyhedral_graph (hT i))

theorem svCalmAt_of_piecewisePolyhedral_graph {S : E → Set F}
    (hS : IsPiecewisePolyhedral (svGraph S)) {x : E} (hx : x ∈ svDom S) : SvCalmAt S x := by
  obtain ⟨k,hk⟩ := exists_calm_constant_of_piecewisePolyhedral_graph hS
  exact ⟨k,hk x hx⟩

end RW
