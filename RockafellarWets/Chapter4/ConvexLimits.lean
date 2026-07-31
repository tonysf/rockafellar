/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Limits of Convex Sets

This file proves the convexity assertion in Theorem 4.15 of
Rockafellar--Wets: the inner limit of convex sets is convex, and consequently
every Painleve--Kuratowski limit of convex sets is convex.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Filter Set Topology

namespace RW

section ConvexLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inner limit is convex when the terms are eventually convex.  This
slightly strengthens the convexity clause of Theorem 4.15, where every term is
assumed convex. -/
theorem convex_innerSetLimit_of_eventually
    (C : ℕ → Set E) (hC : ∀ᶠ n in atTop, Convex ℝ (C n)) :
    Convex ℝ (innerSetLimit C) := by
  intro x hx y hy a b ha hb hab V hV
  let f : E × E → E := fun p ↦ a • p.1 + b • p.2
  have hf : Continuous f :=
    (continuous_fst.const_smul a).add (continuous_snd.const_smul b)
  have hpre : f ⁻¹' V ∈ nhds (x, y) := by
    apply hf.continuousAt
    simpa only [f, hab] using hV
  rcases mem_nhds_prod_iff.1 hpre with ⟨U, hU, W, hW, hUW⟩
  filter_upwards [hC, hx U hU, hy W hW] with n hn hxn hyn
  rcases hxn with ⟨x', hx'C, hx'U⟩
  rcases hyn with ⟨y', hy'C, hy'W⟩
  refine ⟨a • x' + b • y', hn hx'C hy'C ha hb hab, ?_⟩
  have hpair : (x', y') ∈ U ×ˢ W := ⟨hx'U, hy'W⟩
  exact hUW hpair

/-- **Theorem 4.15 (inner-limit convexity).** The inner limit of convex sets
is convex. -/
theorem convex_innerSetLimit (C : ℕ → Set E) (hC : ∀ n, Convex ℝ (C n)) :
    Convex ℝ (innerSetLimit C) :=
  convex_innerSetLimit_of_eventually C (Eventually.of_forall hC)

/-- **Theorem 4.15 (limit convexity).** A Painleve--Kuratowski limit of convex
sets is convex. -/
theorem PKConverges.convex {C : ℕ → Set E} {D : Set E}
    (hlim : PKConverges C D) (hC : ∀ n, Convex ℝ (C n)) : Convex ℝ D := by
  rw [← hlim.inner_eq]
  exact convex_innerSetLimit C hC

/-- Eventual-convexity form of the preceding limit theorem. -/
theorem PKConverges.convex_of_eventually {C : ℕ → Set E} {D : Set E}
    (hlim : PKConverges C D) (hC : ∀ᶠ n in atTop, Convex ℝ (C n)) : Convex ℝ D := by
  rw [← hlim.inner_eq]
  exact convex_innerSetLimit_of_eventually C hC

end ConvexLimits

section ConvexLimitRegressions

/-- Regression: the limit of a constant closed interval is convex. -/
example : Convex ℝ (innerSetLimit (fun _ : ℕ ↦ Set.Icc (-1 : ℝ) 1)) := by
  exact convex_innerSetLimit _ fun _ ↦ convex_Icc _ _

/-- Regression: finite changes do not affect the eventual-convexity theorem. -/
example (C : ℕ → Set ℝ) (hC : ∀ n ≥ 7, Convex ℝ (C n)) :
    Convex ℝ (innerSetLimit C) := by
  apply convex_innerSetLimit_of_eventually C
  filter_upwards [eventually_ge_atTop 7] with n hn
  exact hC n hn

end ConvexLimitRegressions

end RW
