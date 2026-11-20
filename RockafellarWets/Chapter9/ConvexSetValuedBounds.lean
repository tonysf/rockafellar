/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Sub-Lipschitz estimates on convex parameter sets
-/

import RockafellarWets.Chapter9.BoundedSetValuedMappings

open Set Filter Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {X : Set E} {x : E}

omit [NormedSpace ℝ E] in
/-- The inequality of finite-radius and full moduli is local in the fibers. -/
theorem svLipschitzModulusWithin_le_hausdorffModulus_of_eventually
    (hS : ∀ᶠ a in 𝓝[X] x, (S a).Nonempty ∧ IsClosed (S a)) (r : ℝ≥0) :
    svLipschitzModulusWithin S X r x ≤ svHausdorffLipschitzModulusWithin S X x := by
  refine le_iInf fun k ↦ ?_
  obtain ⟨U,hU,hu⟩ := k.2
  apply lipschitzModulusWithin_le (inter_mem hU hS)
  intro a ha b hb
  rw [edist_dist]
  exact (ofReal_rhoDistance_le_hausdorffEDist r ha.2.2 hb.2.2 ha.2.1 hb.2.1).trans (hu a ha.1 b hb.1)

/-- **Theorem 9.31.** A common upper bound on the radius-`r` moduli gives
the same `r`-Lipschitz constant on a convex set. -/
theorem svRhoLipschitzOnWith_of_modulus_le_of_convex (hc : Convex ℝ X) {r k : ℝ≥0}
    (h : ∀ a ∈ X, svLipschitzModulus S r a ≤ (k : ℝ≥0∞)) : SvRhoLipschitzOnWith k r S X :=
  lipschitzOnWith_of_modulus_le_of_convex hc h

/-- The supremum in 9.31 itself works as the constant whenever finite. -/
theorem svRhoLipschitzOnWith_iSup_modulus (hc : Convex ℝ X) {r : ℝ≥0}
    (hfin : (⨆ a : X, svLipschitzModulus S r a) < ⊤) :
    SvRhoLipschitzOnWith (⨆ a : X, svLipschitzModulus S r a).toNNReal r S X := by
  apply svRhoLipschitzOnWith_of_modulus_le_of_convex hc
  intro x hx
  rw [ENNReal.coe_toNNReal hfin.ne]
  exact le_iSup (fun a : X ↦ svLipschitzModulus S r a) ⟨x,hx⟩

theorem svSubLipschitzOn_of_iSup_modulus_lt_top (hc : Convex ℝ X) (hS : NonemptyClosedValuedOn S X)
    (hfin : ∀ r : ℝ≥0, (⨆ a : X, svLipschitzModulus S r a) < ⊤) : SvSubLipschitzOn S X :=
  ⟨hS,fun r ↦ ⟨_,svRhoLipschitzOnWith_iSup_modulus hc (hfin r)⟩⟩

omit [NormedSpace ℝ E] in
theorem SvStrictlyContinuousAt.nonempty_isClosed (h : SvStrictlyContinuousAt S x) :
    (S x).Nonempty ∧ IsClosed (S x) := by
  have hs : {z | (S z).Nonempty ∧ IsClosed (S z)} ∈ 𝓝 x := by
    simpa only [nhdsWithin_univ] using h.2.1
  exact mem_of_mem_nhds (s := {z | (S z).Nonempty ∧ IsClosed (S z)}) hs

/-- The finite-radius bound attains its maximum on a nonempty compact convex
set of strict continuity. The maximum works as a common Lipschitz constant. -/
theorem exists_max_svModulus_of_compact_convex (hc : Convex ℝ X) (hX : IsCompact X) (hne : X.Nonempty)
    (hs : ∀ a ∈ X, SvStrictlyContinuousAt S a) (r : ℝ≥0) :
    ∃ z ∈ X, ∃ k : ℝ≥0, svLipschitzModulus S r z = k ∧ (⨆ a : X, svLipschitzModulus S r a) = k ∧
      SvRhoLipschitzOnWith k r S X :=
  exists_max_modulus_of_compact_convex hc hX hne (fun z hz ↦ (hs z hz).2.2 r)

/-- Sub-Lipschitz continuity on every compact convex set of strict continuity. -/
theorem svSubLipschitzOn_of_compact_convex (hc : Convex ℝ X) (hX : IsCompact X)
    (h : ∀ a ∈ X, SvStrictlyContinuousAt S a) : SvSubLipschitzOn S X := by
  have hn : NonemptyClosedValuedOn S X := fun a ha ↦ (h a ha).nonempty_isClosed
  refine ⟨hn,fun r ↦ ?_⟩
  rcases X.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0,fun _ h ↦ h.elim⟩
  · obtain ⟨_,_,k,_,_,hk⟩ := exists_max_svModulus_of_compact_convex hc hX hne h r
    exact ⟨k,hk⟩

/-- A single bound for all radii gives full global Lipschitz continuity. -/
theorem svLipschitzOnWith_of_moduli_le_of_convex (hc : Convex ℝ X) (hS : NonemptyClosedValuedOn S X)
    {k : ℝ≥0} (h : ∀ r : ℝ≥0, ∀ a ∈ X, svLipschitzModulus S r a ≤ (k : ℝ≥0∞)) :
    SvLipschitzOnWith k S X := svLipschitzOnWith_of_forall_rho hS (fun _ ↦ svRhoLipschitzOnWith_of_modulus_le_of_convex hc (h _))

/-- In particular the supremum of the full moduli serves as a global constant. -/
theorem svLipschitzOnWith_iSup_hausdorffModulus (hc : Convex ℝ X) (h : ∀ a ∈ X, SvStrictlyContinuousAt S a)
    (hfin : (⨆ a : X, svHausdorffLipschitzModulus S a) < ⊤) :
    SvLipschitzOnWith (⨆ a : X, svHausdorffLipschitzModulus S a).toNNReal S X := by
  apply svLipschitzOnWith_of_moduli_le_of_convex hc (fun a ha ↦ (h a ha).nonempty_isClosed)
  intro r a ha
  rw [ENNReal.coe_toNNReal hfin.ne]
  exact (svLipschitzModulusWithin_le_hausdorffModulus_of_eventually (h a ha).2.1 r).trans
    (le_iSup (fun z : X ↦ svHausdorffLipschitzModulus S z) ⟨a,ha⟩)

end RW
