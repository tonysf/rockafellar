/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Convergence of convex hulls

This file proves Proposition 4.30(b), together with the general inner-limit
half used throughout Proposition 4.30.
-/

import RockafellarWets.Chapter2.ConvexHulls
import RockafellarWets.Chapter3.CosmicSpace
import RockafellarWets.Chapter3.PointedCones
import RockafellarWets.Chapter4.ConeLimits
import RockafellarWets.Chapter4.ImageLimits
import RockafellarWets.Chapter4.Products
import RockafellarWets.Chapter4.SetLimitCharacterizations
import Mathlib.Topology.MetricSpace.Sequences

open Bornology Filter Function Set Topology
open scoped BigOperators

namespace RW

section ConvexHullConvergence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Convexification commutes with the inner-limit inclusion. -/
theorem convexHull_innerSetLimit_subset (C : ℕ → Set E) :
    convexHull ℝ (innerSetLimit C) ⊆
      innerSetLimit (fun n ↦ convexHull ℝ (C n)) := by
  intro x hx
  rcases (mem_convexHull_iff_exists_fintype.mp hx) with
    ⟨ι, hι, w, z, hw0, hw1, hz, hsum⟩
  letI : Fintype ι := hι
  have hzProduct : z ∈
      innerSetLimit (fun n ↦ dependentSetProduct (fun _ : ι ↦ C n)) := by
    apply dependentSetProduct_innerSetLimit_subset
    exact mem_dependentSetProduct.2 hz
  subst x
  intro V hV
  have hcont : Continuous (fun y : ι → E ↦ ∑ i, w i • y i) := by
    fun_prop
  have hpre : (fun y : ι → E ↦ ∑ i, w i • y i) ⁻¹' V ∈ nhds z :=
    hcont.continuousAt hV
  exact (hzProduct _ hpre).mono fun n ⟨y, hyProduct, hyV⟩ ↦ by
    refine ⟨∑ i, w i • y i, ?_, hyV⟩
    apply mem_convexHull_of_exists_fintype (w := w) (z := y)
    · exact hw0
    · exact hw1
    · exact mem_dependentSetProduct.1 hyProduct
    · rfl

theorem exists_finrank_succ_convexCombination
    {S : Set E} (hSne : S.Nonempty) {x : E} (hx : x ∈ convexHull ℝ S) :
    ∃ (z : Fin (Module.finrank ℝ E + 1) → E)
      (w : stdSimplex ℝ (Fin (Module.finrank ℝ E + 1))),
      (∀ i, z i ∈ S) ∧ ∑ i, (w : Fin _ → ℝ) i • z i = x := by
  let n : ℕ := Module.finrank ℝ E + 1
  let s0 : S := ⟨hSne.choose, hSne.choose_spec⟩
  obtain ⟨ι, _, z, w, hzS, hAI, hwpos, hw1, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull (𝕜 := ℝ) hx
  have hcard : Fintype.card ι ≤ n :=
    hAI.card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  let β := ι ⊕ Fin (n - Fintype.card ι)
  have hβ : Fintype.card β = n := by
    simp [β, n, Nat.add_sub_of_le hcard]
  let e : β ≃ Fin n := Fintype.equivFinOfCardEq hβ
  let zβ : β → S :=
    Sum.elim (fun i ↦ ⟨z i, hzS (mem_range_self i)⟩) (fun _ ↦ s0)
  let wβ : β → ℝ := Sum.elim w (fun _ ↦ 0)
  let z' : Fin n → E := fun j ↦ zβ (e.symm j)
  let w' : Fin n → ℝ := wβ ∘ e.symm
  have hw' : w' ∈ stdSimplex ℝ (Fin n) := by
    constructor
    · intro j
      dsimp [w', wβ]
      cases e.symm j with
      | inl i => exact (hwpos i).le
      | inr k => exact le_rfl
    · calc
        ∑ j, w' j = ∑ b : β, wβ b :=
          Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)
        _ = (∑ i : ι, w i) +
            ∑ _k : Fin (n - Fintype.card ι), (0 : ℝ) := by
          rw [Fintype.sum_sum_type]
          simp [wβ]
        _ = 1 := by simp [hw1]
  refine ⟨z', ⟨w', hw'⟩, ?_, ?_⟩
  · intro j
    exact (zβ (e.symm j)).property
  · calc
      ∑ j, (w' j) • z' j =
          ∑ b : β, wβ b • ((zβ b : S) : E) :=
        Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)
      _ = (∑ i : ι, w i • z i) +
          ∑ _k : Fin (n - Fintype.card ι),
            (0 : ℝ) • ((s0 : S) : E) := by
        rw [Fintype.sum_sum_type]
        simp [wβ, zβ]
      _ = x := by simp [hcomb]

/-- **Proposition 4.30(b).** Convex hulls preserve set convergence when all
sets in the approximating sequence lie in one bounded region. -/
theorem PKConverges.convexHull_of_uniformly_bounded
    {C : ℕ → Set E} {D B : Set E} (hlim : PKConverges C D)
    (hB : IsBounded B) (hCB : ∀ n, C n ⊆ B) :
    PKConverges (fun n ↦ convexHull ℝ (C n)) (convexHull ℝ D) := by
  have hinner : convexHull ℝ D ⊆
      innerSetLimit (fun n ↦ convexHull ℝ (C n)) := by
    rw [← hlim.inner_eq]
    exact convexHull_innerSetLimit_subset C
  have houter : outerSetLimit (fun n ↦ convexHull ℝ (C n)) ⊆
      convexHull ℝ D := by
    intro x hx
    rcases mem_outerSetLimit_iff_exists_subsequence.1 hx with
      ⟨φ, y, hφ, hyHull, hyx⟩
    have hCne : ∀ n, (C (φ n)).Nonempty := by
      intro n
      by_contra hn
      have hEmpty := not_nonempty_iff_eq_empty.mp hn
      simpa [hEmpty] using hyHull n
    choose z w hzC hsum using fun n ↦
      exists_finrank_succ_convexCombination (hCne n) (hyHull n)
    let k : ℕ := Module.finrank ℝ E + 1
    have hzBounded : IsBounded (range z) := by
      apply (IsBounded.pi (ι := Fin k) fun _ ↦ hB).subset
      rintro q ⟨n, rfl⟩
      rw [Set.mem_pi]
      intro i _hi
      exact hCB (φ n) (hzC n i)
    rcases tendsto_subseq_of_bounded hzBounded (fun n ↦ mem_range_self n) with
      ⟨zbar, _hzbarRange, ψ, hψ, hzzbar⟩
    rcases CompactSpace.tendsto_subseq (w ∘ ψ) with
      ⟨wbar, χ, hχ, hwwbar⟩
    have hzbarD : ∀ i, zbar i ∈ D := by
      intro i
      rw [← hlim.outer_eq]
      exact mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ ∘ ψ ∘ χ, fun n ↦ z (ψ (χ n)) i,
          (hφ.comp hψ).comp hχ, fun n ↦ hzC (ψ (χ n)) i,
          (tendsto_pi_nhds.1 (hzzbar.comp hχ.tendsto_atTop) i)⟩
    apply mem_convexHull_of_exists_fintype
      (w := fun i ↦ ((wbar : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i)
      (z := zbar)
    · exact wbar.property.1
    · exact wbar.property.2
    · exact hzbarD
    · have hsumTendsto : Tendsto
          (fun n ↦ ∑ i, (((w (ψ (χ n)) : stdSimplex ℝ (Fin k)) :
              Fin k → ℝ) i) • z (ψ (χ n)) i)
          atTop
          (nhds (∑ i, (((wbar : stdSimplex ℝ (Fin k)) : Fin k → ℝ) i) •
            zbar i)) := by
        apply tendsto_finset_sum
        intro i _hi
        have hwcoord := tendsto_pi_nhds.1
          (continuous_subtype_val.continuousAt.tendsto.comp hwwbar) i
        have hzcoord := tendsto_pi_nhds.1
          (hzzbar.comp hχ.tendsto_atTop) i
        exact hwcoord.smul hzcoord
      have hySub : Tendsto (fun n ↦ y (ψ (χ n))) atTop (nhds x) :=
        hyx.comp (hψ.comp hχ).tendsto_atTop
      apply tendsto_nhds_unique hsumTendsto
      simpa only [hsum] using hySub
  constructor
  · exact Set.Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner
  · exact Set.Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit _))

private def coordinateSum (ι : Type*) [Fintype ι] :
    (ι → E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun z ↦ ∑ i, z i
      map_add' := fun x y ↦ by simp [Finset.sum_add_distrib]
      map_smul' := fun c z ↦ by simp [Finset.smul_sum] }
    (Fintype.card ι) fun z ↦ by
      calc
        ‖∑ i, z i‖ ≤ ∑ i, ‖z i‖ := norm_sum_le _ _
        _ ≤ ∑ _i : ι, ‖z‖ :=
          Finset.sum_le_sum fun i _ ↦ norm_le_pi_norm z i
        _ = Fintype.card ι * ‖z‖ := by simp

private theorem image_coordinateSum_pi_eq_convexHull
    {K : Set E} (hKcone : IsCone K) :
    coordinateSum (E := E) (Fin (Module.finrank ℝ E + 1)) ''
        dependentSetProduct (fun _ : Fin (Module.finrank ℝ E + 1) ↦ K) =
      convexHull ℝ K := by
  ext x
  rw [mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply (mem_convexHull_iff_exists_finrank_succ_sum_mem hKcone).2
    exact ⟨z, mem_dependentSetProduct.1 hz, rfl⟩
  · intro hx
    rcases (mem_convexHull_iff_exists_finrank_succ_sum_mem hKcone).1 hx with
      ⟨z, hz, hsum⟩
    exact ⟨z, mem_dependentSetProduct.2 hz, hsum⟩

/-- **Proposition 4.30(a).** Convex hulls preserve convergence of cones when
the limit cone is pointed. -/
theorem PKConverges.convexHull_of_cones_of_pointed
    {Kseq : ℕ → Set E} {K : Set E} (hlim : PKConverges Kseq K)
    (hKseqCone : ∀ n, IsCone (Kseq n)) (hKpointed : IsPointed K) :
    PKConverges (fun n ↦ convexHull ℝ (Kseq n)) (convexHull ℝ K) := by
  let ι := Fin (Module.finrank ℝ E + 1)
  let Pseq : ℕ → Set (ι → E) := fun n ↦
    dependentSetProduct (fun _ : ι ↦ Kseq n)
  let P : Set (ι → E) := dependentSetProduct (fun _ : ι ↦ K)
  let G : (ι → E) →L[ℝ] E := coordinateSum ι
  have hprod : PKConverges Pseq P := by
    apply pkConverges_dependentSetProduct
    exact fun _ ↦ hlim
  have hescape : NoConvergentImageEscapeAlong G Pseq := by
    intro φ z y hφ hzP hGzy
    by_contra hzBounded
    rcases exists_cosmicDirection_subsequence_of_not_isBounded hzBounded with
      ⟨u, ψ, hψ, hcosmic⟩
    rcases exists_scaling_of_tendsto_cosmicDirection hcosmic with
      ⟨scale, hscalePos, hscale0, hscaled⟩
    have huK : ∀ i, (u : ι → E) i ∈ K := by
      intro i
      rw [← hlim.outer_eq]
      exact mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ ∘ ψ, fun n ↦ scale n • z (ψ n) i, hφ.comp hψ,
          fun n ↦ (hKseqCone (φ (ψ n))).smul_mem
            (mem_dependentSetProduct.1 (hzP (ψ n)) i) (hscalePos n).le,
          tendsto_pi_nhds.1 hscaled i⟩
    have hsumScaled : Tendsto
        (fun n ↦ G (scale n • z (ψ n))) atTop (nhds 0) := by
      have hGsub : Tendsto (fun n ↦ G (z (ψ n))) atTop (nhds y) := by
        simpa only [Function.comp_apply] using
          hGzy.comp hψ.tendsto_atTop
      simpa only [map_smul, zero_smul] using hscale0.smul hGsub
    have hsumU : G (u : ι → E) = 0 := by
      exact tendsto_nhds_unique (G.continuous.continuousAt.tendsto.comp hscaled)
        hsumScaled
    have huZero : (u : ι → E) = 0 := by
      apply funext
      exact hKpointed.fintype (u : ι → E) huK (by
        simpa only [G, coordinateSum, LinearMap.mkContinuous_apply] using hsumU)
    have huNorm : ‖(u : ι → E)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp u.property
    simp [huZero] at huNorm
  have himage := hprod.image_of_noConvergentImageEscapeAlong
    G.continuous hescape
  have hseqEq : (fun n ↦ G '' Pseq n) =
      (fun n ↦ convexHull ℝ (Kseq n)) := by
    funext n
    exact image_coordinateSum_pi_eq_convexHull (hKseqCone n)
  have hlimitEq : G '' P = convexHull ℝ K := by
    apply image_coordinateSum_pi_eq_convexHull
    exact hlim.isCone hKseqCone
  simpa only [hseqEq, hlimitEq] using himage

end ConvexHullConvergence

end RW
