/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lipschitz extensions with the same constant
-/

import RockafellarWets.Chapter9.FiniteBallIntersection
import Mathlib.Order.Zorn

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private def extensionGraphBound (k : ℝ≥0) (G : Set (E × F)) : Prop :=
  ∀ p ∈ G, ∀ q ∈ G, dist p.2 q.2 ≤ k * dist p.1 q.1

private theorem norm_scaled_center_diff (k : ℝ≥0) (x a b : E) :
    ‖(k:ℝ) • (x-a) - (k:ℝ) • (x-b)‖ = k * dist a b := by
  have he : (x-a)-(x-b) = -(a-b) := by abel
  simp only [← smul_sub,norm_smul,Real.norm_eq_abs,NNReal.abs_eq,he,norm_neg,dist_eq_norm]

/-- A point can be added to a Lipschitz graph without increasing the constant. -/
private theorem exists_extension_graph_value {k : ℝ≥0} {G : Set (E × F)}
    (hG : extensionGraphBound k G) (x : E) :
    ∃ y : F, ∀ p ∈ G, dist y p.2 ≤ k * dist x p.1 := by
  classical
  rcases G.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0,fun p hp ↦ (notMem_empty p hp).elim⟩
  obtain ⟨p₀,hp₀⟩ := hne
  let q₀ : G := ⟨p₀,hp₀⟩
  let B (p : G) := closedBall p.val.2 (k * dist x p.val.1)
  have hfinite (u : Finset G) : (B q₀ ∩ ⋂ p ∈ u, B p).Nonempty := by
    let v := insert q₀ u
    have hv : v.Nonempty := Finset.insert_nonempty _ _
    letI : Nonempty v := hv.to_subtype
    let a (q : v) := (k:ℝ) • (x-q.val.val.1)
    let b (q : v) := q.val.val.2
    have hab (i j : v) : ‖b i-b j‖ ≤ ‖a i-a j‖ := by
      change ‖i.val.val.2-j.val.val.2‖ ≤ ‖(k:ℝ) • (x-i.val.val.1) - (k:ℝ) • (x-j.val.val.1)‖
      rw [norm_scaled_center_diff,← dist_eq_norm]
      exact hG _ i.val.property _ j.val.property
    obtain ⟨y,hy⟩ := exists_mem_closedBalls_of_pairwise_dist_le a b hab
    have hm (p : G) (hp : p ∈ v) : y ∈ B p := by
      have h := hy ⟨p,hp⟩
      simpa only [a,b,B,mem_closedBall,dist_eq_norm,norm_smul,Real.norm_eq_abs,NNReal.abs_eq] using h
    exact ⟨y,hm q₀ (Finset.mem_insert_self _ _),mem_iInter₂.mpr fun p hp ↦ hm p (Finset.mem_insert_of_mem hp)⟩
  obtain ⟨y,_,hy⟩ := (isCompact_closedBall p₀.2 (k * dist x p₀.1)).inter_iInter_nonempty B
    (fun _ ↦ isClosed_closedBall) hfinite
  exact ⟨y,fun p hp ↦ mem_closedBall.mp (mem_iInter.mp hy ⟨p,hp⟩)⟩

/-- **Theorem 9.58 (Kirszbraun extension).** A Lipschitz mapping into a
finite-dimensional real Hilbert space extends to the whole domain space with
exactly the same Lipschitz constant. -/
theorem exists_lipschitz_extension_same_constant {f : E → F} {X : Set E} {k : ℝ≥0}
    (hf : LipschitzOnWith k f X) : ∃ g : E → F, LipschitzWith k g ∧ EqOn f g X := by
  classical
  let G₀ : Set (E × F) := {p | p.1 ∈ X ∧ p.2 = f p.1}
  have h₀ : extensionGraphBound k G₀ := by
    intro p hp q hq
    rw [hp.2,hq.2]
    exact hf.dist_le_mul _ hp.1 _ hq.1
  have hchain : ∀ c ⊆ {G : Set (E × F) | extensionGraphBound k G}, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ {G : Set (E × F) | extensionGraphBound k G}, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hch _
    refine ⟨⋃₀ c,?_,fun s hs ↦ subset_sUnion_of_mem hs⟩
    intro p hp q hq
    obtain ⟨A,hAc,hp⟩ := mem_sUnion.mp hp
    obtain ⟨B,hBc,hq⟩ := mem_sUnion.mp hq
    rcases hch.total hAc hBc with hAB | hBA
    · exact hc hBc p (hAB hp) q hq
    · exact hc hAc p hp q (hBA hq)
  obtain ⟨G,hsub,hmax⟩ := zorn_subset_nonempty {G | extensionGraphBound k G} hchain G₀ h₀
  have hG : extensionGraphBound k G := hmax.1
  have hfull (x : E) : ∃ y : F, (x,y) ∈ G := by
    obtain ⟨y,hy⟩ := exists_extension_graph_value hG x
    refine ⟨y,hmax.mem_of_prop_insert ?_⟩
    intro p hp q hq
    rcases mem_insert_iff.mp hp with rfl | hp <;> rcases mem_insert_iff.mp hq with rfl | hq
    · simp
    · exact hy q hq
    · simpa only [dist_comm] using hy p hp
    · exact hG p hp q hq
  choose g hg using hfull
  refine ⟨g,LipschitzWith.of_dist_le_mul fun x y ↦ hG _ (hg x) _ (hg y),?_⟩
  intro x hx
  apply dist_le_zero.mp
  have h := hG (x,f x) (hsub ⟨hx,rfl⟩) (x,g x) (hg x)
  simpa only [dist_self,mul_zero] using h

/-- **Theorem 9.58**, uniqueness on the closure. Every continuous extension
to the closure agrees there with the Lipschitz extension, and hence has the
same Lipschitz estimate. -/
theorem exists_unique_continuous_extension_on_closure {f : E → F} {X : Set E} {k : ℝ≥0}
    (hf : LipschitzOnWith k f X) :
    ∃ g : E → F, LipschitzWith k g ∧ EqOn f g X ∧
      ∀ h : E → F, ContinuousOn h (closure X) → EqOn f h X →
        EqOn h g (closure X) ∧ LipschitzOnWith k h (closure X) := by
  obtain ⟨g,hg,he⟩ := exists_lipschitz_extension_same_constant hf
  refine ⟨g,hg,he,fun h hh hfh ↦ ?_⟩
  have heq : EqOn h g (closure X) :=
    (hfh.symm.trans he).of_subset_closure hh hg.continuous.continuousOn subset_closure (Subset.rfl)
  refine ⟨heq,LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
  rw [heq hx,heq hy]
  exact hg.dist_le_mul x y

end RW
