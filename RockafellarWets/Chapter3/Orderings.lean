/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3E*: Cone-Induced Orderings

This file formalizes Proposition 3.38 from Rockafellar-Wets:
- the relation induced by a closed convex cone satisfies the standard order-like
  rules;
- conversely, any relation satisfying those rules comes from a closed convex
  cone;
- antisymmetry of the cone-induced relation is equivalent to pointedness.
-/

import RockafellarWets.Chapter3.PointedCones
import Mathlib.Topology.Sequences

open Set Topology Filter

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The relation induced by a cone `K`: `x ≥_K y` means `x - y ∈ K`. -/
def GeByCone (K : Set E) (x y : E) : Prop :=
  x - y ∈ K

/-- The order-like axioms appearing in Proposition 3.38. -/
def IsConeOrder (r : E → E → Prop) : Prop :=
  (∀ x : E, r x x) ∧
  (∀ ⦃x y : E⦄, r x y → r (-y) (-x)) ∧
  (∀ ⦃x y : E⦄ ⦃c : ℝ⦄, r x y → 0 ≤ c → r (c • x) (c • y)) ∧
  (∀ ⦃x y x' y' : E⦄, r x y → r x' y' → r (x + x') (y + y')) ∧
  (∀ ⦃x y : E⦄ ⦃u v : ℕ → E⦄,
    (∀ n, r (u n) (v n)) →
    Tendsto u atTop (𝓝 x) →
    Tendsto v atTop (𝓝 y) →
    r x y)

/-- The cone extracted from a relation by comparing points with `0`. -/
def coneOfRelation (r : E → E → Prop) : Set E :=
  {x : E | r x 0}

theorem geByCone_refl {K : Set E} (hcone : IsCone K) (x : E) :
    GeByCone K x x := by
  simpa [GeByCone] using hcone.1

theorem geByCone_neg_swap {K : Set E} {x y : E} (hxy : GeByCone K x y) :
    GeByCone K (-y) (-x) := by
  simpa [GeByCone, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hxy

theorem geByCone_smul {K : Set E} (hcone : IsCone K) {x y : E} {c : ℝ}
    (hxy : GeByCone K x y) (hc : 0 ≤ c) :
    GeByCone K (c • x) (c • y) := by
  simpa [GeByCone, smul_sub] using hcone.smul_mem hxy hc

theorem geByCone_add {K : Set E} (hconv : Convex ℝ K) (hcone : IsCone K)
    {x y x' y' : E} (hxy : GeByCone K x y) (hx'y' : GeByCone K x' y') :
    GeByCone K (x + x') (y + y') := by
  have hsum : (x - y) + (x' - y') ∈ K :=
    add_mem_of_convex_isCone hconv hcone hxy hx'y'
  simpa [GeByCone, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

theorem geByCone_of_tendsto {K : Set E} (hclosed : IsClosed K)
    {x y : E} {u v : ℕ → E}
    (huv : ∀ n, GeByCone K (u n) (v n))
    (hu : Tendsto u atTop (𝓝 x)) (hv : Tendsto v atTop (𝓝 y)) :
    GeByCone K x y := by
  have hmem : ∀ n, u n - v n ∈ K := by
    intro n
    exact huv n
  simpa [GeByCone] using hclosed.mem_of_tendsto (hu.sub hv) (Eventually.of_forall hmem)

/-- The relation induced by a closed convex cone satisfies the axioms in
Proposition 3.38(a)-(e). -/
theorem isConeOrder_geByCone {K : Set E} (hclosed : IsClosed K)
    (hconv : Convex ℝ K) (hcone : IsCone K) :
    IsConeOrder (GeByCone K) := by
  refine ⟨geByCone_refl hcone, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact geByCone_neg_swap hxy
  · intro x y c hxy hc
    exact geByCone_smul hcone hxy hc
  · intro x y x' y' hxy hx'y'
    exact geByCone_add hconv hcone hxy hx'y'
  · intro x y u v huv hu hv
    exact geByCone_of_tendsto hclosed huv hu hv

theorem relation_iff_geByCone_coneOfRelation {r : E → E → Prop}
    (hr : IsConeOrder r) {x y : E} :
    r x y ↔ GeByCone (coneOfRelation r) x y := by
  rcases hr with ⟨hrefl, hneg, hsmul, hadd, hlim⟩
  constructor
  · intro hxy
    change r (x - y) 0
    have hyy : r (-y) (-y) := hrefl (-y)
    simpa [sub_eq_add_neg] using hadd hxy hyy
  · intro hxy
    change r (x - y) 0 at hxy
    have hyy : r y y := hrefl y
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd hxy hyy

theorem isCone_coneOfRelation {r : E → E → Prop} (hr : IsConeOrder r) :
    IsCone (coneOfRelation r) := by
  rcases hr with ⟨hrefl, hneg, hsmul, hadd, hlim⟩
  refine ⟨?_, ?_⟩
  · exact hrefl 0
  · intro x hx c hc
    simpa using hsmul hx hc.le

theorem convex_coneOfRelation {r : E → E → Prop} (hr : IsConeOrder r) :
    Convex ℝ (coneOfRelation r) := by
  have hcone : IsCone (coneOfRelation r) := isCone_coneOfRelation hr
  rw [hcone.convex_iff_add_mem]
  rcases hr with ⟨hrefl, hneg, hsmul, hadd, hlim⟩
  intro x y hx hy
  simpa using hadd hx hy

theorem isClosed_coneOfRelation {r : E → E → Prop} (hr : IsConeOrder r) :
    IsClosed (coneOfRelation r) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rcases mem_closure_iff_seq_limit.mp hx with ⟨u, hu, hu_tendsto⟩
  rcases hr with ⟨hrefl, hneg, hsmul, hadd, hlim⟩
  exact hlim hu hu_tendsto tendsto_const_nhds

/-- The converse part of Proposition 3.38: any relation satisfying the
order-like axioms comes from a closed convex cone. -/
theorem exists_closed_convex_cone_of_isConeOrder {r : E → E → Prop}
    (hr : IsConeOrder r) :
    ∃ K : Set E,
      IsClosed K ∧ Convex ℝ K ∧ IsCone K ∧
      ∀ ⦃x y : E⦄, r x y ↔ GeByCone K x y := by
  refine ⟨coneOfRelation r, isClosed_coneOfRelation hr, convex_coneOfRelation hr,
    isCone_coneOfRelation hr, ?_⟩
  intro x y
  exact relation_iff_geByCone_coneOfRelation hr

/-- The additional antisymmetry property in Proposition 3.38 is equivalent to
pointedness of the underlying cone. -/
theorem antisymm_geByCone_iff_isPointed {K : Set E}
    (hconv : Convex ℝ K) (hcone : IsCone K) :
    (∀ ⦃x y : E⦄, GeByCone K x y → GeByCone K y x → x = y) ↔ IsPointed K := by
  rw [isPointed_iff_inter_neg_eq_singleton_zero hconv hcone]
  constructor
  · intro hanti
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨hxK, hxnegK⟩
      have hx0 : GeByCone K x 0 := by
        simpa [GeByCone] using hxK
      have h0x : GeByCone K 0 x := by
        simpa [GeByCone] using hxnegK
      have : x = 0 := hanti hx0 h0x
      simp [this]
    · intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      constructor
      · exact hcone.1
      · simpa using hcone.1
  · intro hpointed x y hxy hyx
    have hinter : x - y ∈ K ∩ -K := by
      refine ⟨hxy, ?_⟩
      simpa [GeByCone, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hyx
    have hzero : x - y = 0 := by
      have : x - y ∈ ({0} : Set E) := by
        simpa [hpointed] using hinter
      simpa using this
    exact sub_eq_zero.mp hzero

end RW
