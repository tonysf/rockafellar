/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Minty parameterization of a graph

Theorem 12.15.  For a maximal monotone `T`, the Minty mappings
`P = (I + T)⁻¹` and `Q = (I + T⁻¹)⁻¹` are single-valued, maximal monotone and
nonexpansive, and `z ↦ (P(z), Q(z))` maps `ℝⁿ` one-to-one onto `gph T`, with

`(P(z), Q(z)) = (x, v) ⟺ z = x + v, (x, v) ∈ gph T`.

The parameterization is Lipschitz continuous in both directions, the inverse
being `(x, v) ↦ x + v`.  With the sup norm on `E × E` the constants are `1` and
`2`.  The proof is the book's: 12.8(a) makes `T⁻¹` maximal monotone, 12.12 makes
both resolvents single-valued, maximal monotone and nonexpansive, and Lemma
12.14 gives `P + Q = I`.
-/

import RockafellarWets.Chapter12.ResolventMaximality

open Set
open scoped InnerProductSpace Pointwise NNReal

namespace RW

section Minty

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {T : E → Set E}

/-- The Minty parameterization `z ↦ (P(z), Q(z))` with `P = (I + T)⁻¹` and
`Q = (I + T⁻¹)⁻¹`. -/
noncomputable def mintyMap (T : E → Set E) (z : E) : E × E :=
  (resolventMap T 1 z, resolventMap (svInv T) 1 z)

/-- **Theorem 12.15.** The Minty mappings `P` and `Q` are single-valued. -/
theorem SvMaximalMonotone.minty_singleValued (hT : SvMaximalMonotone T) (z : E) :
    svResolvent T 1 z = {resolventMap T 1 z} ∧
      svResolvent (svInv T) 1 z = {resolventMap (svInv T) 1 z} :=
  ⟨hT.svResolvent_eq_singleton_resolventMap one_pos z,
    hT.inv.svResolvent_eq_singleton_resolventMap one_pos z⟩

/-- **Theorem 12.15.** The Minty mappings are maximal monotone. -/
theorem SvMaximalMonotone.minty_maximalMonotone (hT : SvMaximalMonotone T) :
    SvMaximalMonotone (svResolvent T 1) ∧ SvMaximalMonotone (svResolvent (svInv T) 1) :=
  ⟨hT.svMaximalMonotone_svResolvent one_pos, hT.inv.svMaximalMonotone_svResolvent one_pos⟩

omit [FiniteDimensional ℝ E] in
/-- **Theorem 12.15.** The Minty mappings are nonexpansive. -/
theorem SvMaximalMonotone.minty_nonexpansive (hT : SvMaximalMonotone T) :
    SvNonexpansive (svResolvent T 1) ∧ SvNonexpansive (svResolvent (svInv T) 1) :=
  ⟨hT.1.svNonexpansive_svResolvent zero_le_one, hT.inv.1.svNonexpansive_svResolvent zero_le_one⟩

/-- **Theorem 12.15.** Both single-valued Minty mappings are Lipschitz with
constant one. -/
theorem SvMaximalMonotone.minty_lipschitzWith (hT : SvMaximalMonotone T) :
    LipschitzWith 1 (resolventMap T 1) ∧ LipschitzWith 1 (resolventMap (svInv T) 1) :=
  ⟨hT.lipschitzWith_resolventMap one_pos, hT.inv.lipschitzWith_resolventMap one_pos⟩

theorem SvMaximalMonotone.resolventMap_one_eq_iff (hT : SvMaximalMonotone T) {z x : E} :
    resolventMap T 1 z = x ↔ ∃ v ∈ T x, x + v = z := by
  rw [hT.resolventMap_eq_iff one_pos]
  simp only [one_smul]

theorem SvMaximalMonotone.resolventMap_svInv_one_eq_iff (hT : SvMaximalMonotone T) {z v : E} :
    resolventMap (svInv T) 1 z = v ↔ ∃ x, v ∈ T x ∧ x + v = z := by
  rw [hT.inv.resolventMap_eq_iff one_pos]
  simp only [one_smul, mem_svInv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, add_comm _ _⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, add_comm _ _⟩

/-- **Theorem 12.15**, the parameterization identity:
`(P(z), Q(z)) = (x, v) ⟺ z = x + v, (x, v) ∈ gph T`. -/
theorem SvMaximalMonotone.mintyMap_eq_iff (hT : SvMaximalMonotone T) {z x v : E} :
    mintyMap T z = (x, v) ↔ z = x + v ∧ (x, v) ∈ svGraph T := by
  simp only [mintyMap, Prod.mk.injEq, hT.resolventMap_one_eq_iff,
    hT.resolventMap_svInv_one_eq_iff, mem_svGraph]
  constructor
  · rintro ⟨⟨v', hv', hz⟩, ⟨x', hx', hz'⟩⟩
    have hQ : resolventMap (svInv T) 1 z = v' := hT.resolventMap_svInv_one_eq_iff.2 ⟨x, hv', hz⟩
    have hQ' : resolventMap (svInv T) 1 z = v := hT.resolventMap_svInv_one_eq_iff.2 ⟨x', hx', hz'⟩
    have hvv : v' = v := hQ.symm.trans hQ'
    subst hvv
    exact ⟨hz.symm, hv'⟩
  · rintro ⟨rfl, hv⟩
    exact ⟨⟨v, hv, rfl⟩, ⟨x, hv, rfl⟩⟩

/-- **Theorem 12.15** with Lemma 12.14: `P + Q = I`. -/
theorem SvMaximalMonotone.resolventMap_add_resolventMap_svInv (hT : SvMaximalMonotone T)
    (z : E) : resolventMap T 1 z + resolventMap (svInv T) 1 z = z :=
  ((hT.mintyMap_eq_iff (z := z)).1 rfl).1.symm

/-- **Theorem 12.15.** The Minty parameterization takes values in `gph T`. -/
theorem SvMaximalMonotone.mintyMap_mem_svGraph (hT : SvMaximalMonotone T) (z : E) :
    mintyMap T z ∈ svGraph T :=
  ((hT.mintyMap_eq_iff (z := z)).1 rfl).2

/-- **Theorem 12.15.** The Minty parameterization is one-to-one. -/
theorem SvMaximalMonotone.mintyMap_injective (hT : SvMaximalMonotone T) :
    Function.Injective (mintyMap T) := by
  intro z₁ z₂ h
  rw [← hT.resolventMap_add_resolventMap_svInv z₁, ← hT.resolventMap_add_resolventMap_svInv z₂]
  exact congrArg (fun p : E × E ↦ p.1 + p.2) h

/-- **Theorem 12.15.** The Minty parameterization maps onto `gph T`. -/
theorem SvMaximalMonotone.range_mintyMap (hT : SvMaximalMonotone T) :
    range (mintyMap T) = svGraph T := by
  refine Subset.antisymm (range_subset_iff.2 hT.mintyMap_mem_svGraph) fun p hp ↦ ?_
  exact ⟨p.1 + p.2, (hT.mintyMap_eq_iff (z := p.1 + p.2) (x := p.1) (v := p.2)).2 ⟨rfl, hp⟩⟩

/-- **Theorem 12.15.** The parameterization is Lipschitz continuous. -/
theorem SvMaximalMonotone.lipschitzWith_mintyMap (hT : SvMaximalMonotone T) :
    LipschitzWith 1 (mintyMap T) := by
  have h := LipschitzWith.prodMk hT.minty_lipschitzWith.1 hT.minty_lipschitzWith.2
  simpa only [max_self] using h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The inverse of the parameterization, `(x, v) ↦ x + v`, is Lipschitz
continuous. -/
theorem lipschitzWith_fst_add_snd : LipschitzWith 2 (fun p : E × E ↦ p.1 + p.2) := by
  have h := LipschitzWith.add (LipschitzWith.prod_fst (α := E) (β := E))
    (LipschitzWith.prod_snd (α := E) (β := E))
  have h2 : (1 + 1 : ℝ≥0) = 2 := by norm_num
  rwa [h2] at h

/-- **Theorem 12.15.** The Minty parameterization as a one-to-one
correspondence between `ℝⁿ` and `gph T`. -/
noncomputable def SvMaximalMonotone.mintyEquiv (hT : SvMaximalMonotone T) : E ≃ svGraph T where
  toFun z := ⟨mintyMap T z, hT.mintyMap_mem_svGraph z⟩
  invFun p := p.1.1 + p.1.2
  left_inv z := hT.resolventMap_add_resolventMap_svInv z
  right_inv p := by
    apply Subtype.ext
    exact (hT.mintyMap_eq_iff (z := p.1.1 + p.1.2) (x := p.1.1) (v := p.1.2)).2 ⟨rfl, p.2⟩

@[simp]
theorem SvMaximalMonotone.mintyEquiv_apply (hT : SvMaximalMonotone T) (z : E) :
    (hT.mintyEquiv z : E × E) = mintyMap T z :=
  rfl

@[simp]
theorem SvMaximalMonotone.mintyEquiv_symm_apply (hT : SvMaximalMonotone T) (p : svGraph T) :
    hT.mintyEquiv.symm p = p.1.1 + p.1.2 :=
  rfl

/-- **Theorem 12.15.** The parameterization of `gph T` is Lipschitz continuous
in both directions. -/
theorem SvMaximalMonotone.lipschitzWith_mintyEquiv (hT : SvMaximalMonotone T) :
    LipschitzWith 1 hT.mintyEquiv ∧ LipschitzWith 2 hT.mintyEquiv.symm := by
  refine ⟨hT.lipschitzWith_mintyMap.subtype_mk _, ?_⟩
  have h := (lipschitzWith_fst_add_snd (E := E)).comp (LipschitzWith.subtype_val (svGraph T))
  simpa only [mul_one] using h

end Minty

end RW
