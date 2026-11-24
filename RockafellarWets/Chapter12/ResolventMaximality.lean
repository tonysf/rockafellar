/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Maximality and single-valued resolvents

Theorem 12.12.  For monotone `T` and `λ > 0`, the resolvent `(I + λT)⁻¹` is
monotone and nonexpansive (proved in `Resolvents`).  Moreover `T` is maximal
monotone exactly when `rge(I + λT) = ℝⁿ`, equivalently
`dom(I + λT)⁻¹ = ℝⁿ`, and then `(I + λT)⁻¹` is maximal monotone and a
single-valued mapping of the whole space into itself.

The proof follows the book.  Replacing `T` by `λT` reduces to `λ = 1`.  For a
maximal monotone `T`, the nonexpansive mapping `S` of Proposition 12.11 is
given on its domain by a Lipschitz map with constant one, which Kirszbraun's
theorem 9.58 extends to the whole space.  The extension corresponds to a
monotone enlargement of `T`, so maximality forces `dom S = ℝⁿ`, and
`dom S = dom(I + T)⁻¹`.  Conversely, if the resolvent is everywhere defined,
any pair `(x̂, v̂)` satisfying the monotonicity inequality against `gph T` is
compared with the graph point `(x, v)` with `x + λv = x̂ + λv̂`, which forces
`(x, v) = (x̂, v̂)`.

Kirszbraun's theorem is used for a finite-dimensional space, the book's
setting `ℝⁿ`; the other implications hold in every real inner product space.

`resolventMap T λ` is a single-valued selection of the resolvent; for maximal
monotone `T` and `λ > 0` it is the resolvent itself.
-/

import RockafellarWets.Chapter12.MonotoneNonexpansiveCorrespondence
import RockafellarWets.Chapter12.ContinuousMaximality
import RockafellarWets.Chapter12.MaximalMonotoneGraphs
import RockafellarWets.Chapter9.HilbertLipschitzExtension

open Set
open scoped InnerProductSpace Pointwise

namespace RW

section ResolventMaximality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive multiples of maximal monotone mappings are maximal monotone. -/
theorem SvMaximalMonotone.smul {T : E → Set E} (hT : SvMaximalMonotone T) {lam : ℝ}
    (hlam : 0 < lam) : SvMaximalMonotone (fun x ↦ lam • T x) := by
  refine svMaximalMonotone_iff_forall_inner_nonneg.2 ⟨hT.1.smul hlam.le, fun x v h ↦ ?_⟩
  rw [mem_smul_set]
  refine ⟨lam⁻¹ • v, hT.mem_of_forall_inner_nonneg fun x' w hw ↦ ?_, by
    rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]⟩
  have h' := h x' (lam • w) (smul_mem_smul_set hw)
  have e : lam⁻¹ • v - w = lam⁻¹ • (v - lam • w) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  rw [e, real_inner_smul_left]
  exact mul_nonneg (inv_nonneg.2 hlam.le) h'

/-- **Theorem 12.12**, sufficiency: if the resolvent `(I + λT)⁻¹` of a monotone
mapping is defined everywhere, the mapping is maximal monotone. -/
theorem svMaximalMonotone_of_svDom_svResolvent {T : E → Set E} (hT : SvMonotone T) {lam : ℝ}
    (hlam : 0 < lam) (hdom : svDom (svResolvent T lam) = univ) : SvMaximalMonotone T := by
  refine svMaximalMonotone_iff_forall_inner_nonneg.2 ⟨hT, fun xh vh h ↦ ?_⟩
  have hz : xh + lam • vh ∈ svDom (svResolvent T lam) := hdom ▸ mem_univ _
  obtain ⟨x, hx⟩ := hz
  obtain ⟨v, hv, hxv⟩ := mem_svResolvent.1 hx
  have h₁ := h x v hv
  have e : xh - x = lam • (v - vh) := by
    rw [smul_sub]
    calc xh - x = (x + lam • v) - lam • vh - x := by rw [hxv]; abel
      _ = lam • v - lam • vh := by abel
  rw [e, real_inner_smul_right, ← neg_sub v vh, inner_neg_left, real_inner_self_eq_norm_sq]
    at h₁
  have hn : ‖v - vh‖ ^ 2 ≤ 0 := by nlinarith
  have hvv : v = vh := sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
    (le_antisymm hn (sq_nonneg _))))
  have hxx : x = xh := by
    rw [hvv, sub_self, smul_zero] at e
    exact (sub_eq_zero.1 e).symm
  rw [← hvv, ← hxx]
  exact hv

/-- **Theorem 12.12**, necessity for `λ = 1`, through Proposition 12.11 and
Kirszbraun's extension theorem 9.58. -/
theorem SvMaximalMonotone.svDom_svResolvent_one_eq_univ [FiniteDimensional ℝ E] {T : E → Set E}
    (hT : SvMaximalMonotone T) : svDom (svResolvent T 1) = univ := by
  have hS : SvNonexpansive (svCayley T) := svNonexpansive_svCayley_iff.2 hT.1
  obtain ⟨s, hs, hSs⟩ := svNonexpansive_iff_lipschitzOnWith.1 hS
  obtain ⟨g, hg, hsg⟩ := exists_lipschitz_extension_same_constant hs
  have hT' : SvMonotone (svCayleyInv (fun z ↦ ({g z} : Set E))) :=
    svMonotone_svCayleyInv_iff.2 (svNonexpansive_singleton_iff.2 hg)
  have hsub : ∀ x, T x ⊆ svCayleyInv (fun z ↦ ({g z} : Set E)) x := by
    intro x v hv
    have hz : v + x ∈ svDom (svCayley T) := ⟨v - x, x, v, hv, rfl, rfl⟩
    have h₁ : v - x ∈ svCayley T (v + x) := ⟨x, v, hv, rfl, rfl⟩
    rw [hSs _ hz, mem_singleton_iff] at h₁
    rw [mem_svCayleyInv, mem_singleton_iff, h₁, hsg hz]
  have heq := hT.eq_of_subset hT' hsub
  rw [← svDom_svCayley, ← heq, svCayley_svCayleyInv]
  exact eq_univ_of_forall fun z ↦ ⟨g z, mem_singleton _⟩

/-- **Theorem 12.12**, necessity: the resolvent of a maximal monotone mapping
is defined everywhere. -/
theorem SvMaximalMonotone.svDom_svResolvent_eq_univ [FiniteDimensional ℝ E] {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) : svDom (svResolvent T lam) = univ := by
  rw [svResolvent_eq_svResolvent_smul]
  exact (hT.smul hlam).svDom_svResolvent_one_eq_univ

/-- **Theorem 12.12.** A monotone mapping `T` is maximal monotone if and only if
`dom(I + λT)⁻¹ = ℝⁿ`. -/
theorem svMaximalMonotone_iff_svDom_svResolvent [FiniteDimensional ℝ E] {T : E → Set E}
    (hT : SvMonotone T) {lam : ℝ} (hlam : 0 < lam) :
    SvMaximalMonotone T ↔ svDom (svResolvent T lam) = univ :=
  ⟨fun h ↦ h.svDom_svResolvent_eq_univ hlam, svMaximalMonotone_of_svDom_svResolvent hT hlam⟩

/-- **Theorem 12.12.** A monotone mapping `T` is maximal monotone if and only if
`rge(I + λT) = ℝⁿ`. -/
theorem svMaximalMonotone_iff_svRange [FiniteDimensional ℝ E] {T : E → Set E}
    (hT : SvMonotone T) {lam : ℝ} (hlam : 0 < lam) :
    SvMaximalMonotone T ↔ svRange (svAdd (fun x ↦ ({x} : Set E)) (fun x ↦ lam • T x)) = univ := by
  rw [← svDom_svResolvent]
  exact svMaximalMonotone_iff_svDom_svResolvent hT hlam

/-- A single-valued selection of the resolvent `(I + λT)⁻¹`, equal to the
resolvent wherever the resolvent is single-valued and nonempty. -/
noncomputable def resolventMap (T : E → Set E) (lam : ℝ) (z : E) : E :=
  open Classical in if h : (svResolvent T lam z).Nonempty then h.some else z

theorem resolventMap_mem {T : E → Set E} {lam : ℝ} {z : E}
    (hz : z ∈ svDom (svResolvent T lam)) : resolventMap T lam z ∈ svResolvent T lam z := by
  classical
  have hz' : (svResolvent T lam z).Nonempty := hz
  simp only [resolventMap, dif_pos hz']
  exact hz'.some_mem

/-- For monotone `T` and `λ ≥ 0`, the resolvent is the singleton of
`resolventMap` on its domain. -/
theorem SvMonotone.svResolvent_eq_resolventMap {T : E → Set E} (hT : SvMonotone T) {lam : ℝ}
    (hlam : 0 ≤ lam) {z : E} (hz : z ∈ svDom (svResolvent T lam)) :
    svResolvent T lam z = {resolventMap T lam z} :=
  hT.svResolvent_eq_singleton hlam (resolventMap_mem hz)

/-- **Theorem 12.12.** For maximal monotone `T` and `λ > 0`, the resolvent is a
single-valued mapping from the whole space into itself. -/
theorem SvMaximalMonotone.svResolvent_eq_singleton_resolventMap [FiniteDimensional ℝ E]
    {T : E → Set E} (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) (z : E) :
    svResolvent T lam z = {resolventMap T lam z} :=
  hT.1.svResolvent_eq_resolventMap hlam.le (by rw [hT.svDom_svResolvent_eq_univ hlam]; trivial)

theorem SvMaximalMonotone.svResolvent_eq_fun [FiniteDimensional ℝ E] {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) :
    svResolvent T lam = fun z ↦ ({resolventMap T lam z} : Set E) :=
  funext (hT.svResolvent_eq_singleton_resolventMap hlam)

/-- For maximal monotone `T` and `λ > 0`, the single-valued resolvent is
Lipschitz continuous with constant one. -/
theorem SvMaximalMonotone.lipschitzWith_resolventMap [FiniteDimensional ℝ E] {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) :
    LipschitzWith 1 (resolventMap T lam) := by
  have h := hT.1.svNonexpansive_svResolvent hlam.le
  rw [hT.svResolvent_eq_fun hlam] at h
  exact svNonexpansive_singleton_iff.1 h

/-- The characterization of the single-valued resolvent:
`resolventMap T λ z = x ↔ λ⁻¹(z - x) ∈ T(x)`, in the form `∃ v ∈ T x, x + λv = z`. -/
theorem SvMaximalMonotone.resolventMap_eq_iff [FiniteDimensional ℝ E] {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) {z x : E} :
    resolventMap T lam z = x ↔ ∃ v ∈ T x, x + lam • v = z := by
  rw [← mem_svResolvent, hT.svResolvent_eq_singleton_resolventMap hlam, mem_singleton_iff, eq_comm]

/-- **Theorem 12.12.** For maximal monotone `T` and `λ > 0`, the resolvent
`(I + λT)⁻¹` is itself maximal monotone. -/
theorem SvMaximalMonotone.svMaximalMonotone_svResolvent [FiniteDimensional ℝ E] {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) :
    SvMaximalMonotone (svResolvent T lam) := by
  have hmono := hT.1.svMonotone_svResolvent hlam.le
  rw [hT.svResolvent_eq_fun hlam] at hmono ⊢
  exact svMaximalMonotone_singleton_of_continuous
    (hT.lipschitzWith_resolventMap hlam).continuous hmono

/-- **Theorem 12.12**, collected: for monotone `T` and `λ > 0` the resolvent is
monotone and nonexpansive, and `T` is maximal monotone exactly when
`rge(I + λT)` is the whole space; then the resolvent is maximal monotone and
single-valued everywhere. -/
theorem resolvent_theorem [FiniteDimensional ℝ E] {T : E → Set E} (hT : SvMonotone T) {lam : ℝ}
    (hlam : 0 < lam) :
    SvMonotone (svResolvent T lam) ∧ SvNonexpansive (svResolvent T lam) ∧
      (SvMaximalMonotone T ↔ svRange (svAdd (fun x ↦ ({x} : Set E)) (fun x ↦ lam • T x)) = univ) ∧
      (SvMaximalMonotone T ↔ svDom (svResolvent T lam) = univ) ∧
      (SvMaximalMonotone T → SvMaximalMonotone (svResolvent T lam) ∧
        ∃ p : E → E, LipschitzWith 1 p ∧ ∀ z, svResolvent T lam z = {p z}) :=
  ⟨hT.svMonotone_svResolvent hlam.le, hT.svNonexpansive_svResolvent hlam.le,
    svMaximalMonotone_iff_svRange hT hlam, svMaximalMonotone_iff_svDom_svResolvent hT hlam,
    fun h ↦ ⟨h.svMaximalMonotone_svResolvent hlam, resolventMap T lam,
      h.lipschitzWith_resolventMap hlam, h.svResolvent_eq_singleton_resolventMap hlam⟩⟩

end ResolventMaximality

end RW
