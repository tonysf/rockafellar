/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 4: Compactness for Set Convergence

The subsequence compactness theorem 4.18.  A countable topological basis
turns a set into its Boolean pattern of basis elements that it meets.  The
compactness of the resulting Cantor cube supplies a subsequence on which all
of these hit-or-miss decisions stabilize.
-/

import Mathlib.Topology.Compactness.Compact
import RockafellarWets.Chapter4.SetLimitCharacterizations

open Filter Function Set Topology

namespace RW

section SubsequenceLemmas

variable {E : Type*} [TopologicalSpace E]

/-- Passing to a subsequence can only enlarge the inner set limit. -/
theorem innerSetLimit_subset_subsequence {C : ℕ → Set E} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) :
    innerSetLimit C ⊆ innerSetLimit (C ∘ φ) := by
  intro x hx V hV
  exact hφ.tendsto_atTop.eventually (hx V hV)

/-- Passing to a subsequence can only shrink the outer set limit. -/
theorem outerSetLimit_subsequence_subset {C : ℕ → Set E} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) :
    outerSetLimit (C ∘ φ) ⊆ outerSetLimit C := by
  intro x hx V hV
  rw [frequently_atTop]
  intro N
  have hlarge : ∀ᶠ n in atTop, N ≤ φ n :=
    hφ.tendsto_atTop (eventually_ge_atTop N)
  rcases ((hx V hV).and_eventually hlarge).exists with ⟨n, hnHit, hnLarge⟩
  exact ⟨φ n, hnLarge, hnHit⟩

end SubsequenceLemmas

section SetConvergenceCompactness

variable {E : Type*} [PseudoMetricSpace E] [SecondCountableTopology E]

private noncomputable def basisHitSignature (C : ℕ → Set E) (n : ℕ)
    (U : TopologicalSpace.countableBasis E) : Bool :=
  @ite Bool ((C n ∩ (U : Set E)).Nonempty) (Classical.propDecidable _) true false

/-- In a second-countable space, every sequence of sets has a
Painleve--Kuratowski convergent subsequence.  The limit is allowed to be
empty; theorem 4.18 below identifies precisely when a nonempty one can be
chosen. -/
theorem exists_pkConvergent_subsequence (C : ℕ → Set E) :
    ∃ (φ : ℕ → ℕ) (D : Set E),
      StrictMono φ ∧ PKConverges (C ∘ φ) D := by
  classical
  let signature : ℕ → (TopologicalSpace.countableBasis E → Bool) :=
    basisHitSignature C
  rcases CompactSpace.tendsto_subseq signature with ⟨q, φ, hφ, hq⟩
  refine ⟨φ, outerSetLimit (C ∘ φ), hφ, ?_⟩
  refine ⟨Set.Subset.antisymm (innerSetLimit_subset_outerSetLimit _) ?_, rfl⟩
  intro x hx V hV
  rcases mem_nhds_iff.1 hV with ⟨O, hOV, hOopen, hxO⟩
  rcases (TopologicalSpace.isBasis_countableBasis E).exists_subset_of_mem_open hxO hOopen with
    ⟨U, hUbasis, hxU, hUO⟩
  let U' : TopologicalSpace.countableBasis E := ⟨U, hUbasis⟩
  have hfrequentHit : ∃ᶠ n in atTop, (C (φ n) ∩ U).Nonempty :=
    hx U ((TopologicalSpace.isBasis_countableBasis E).isOpen hUbasis |>.mem_nhds hxU)
  have hcoord : Tendsto
      (fun n ↦ basisHitSignature C (φ n) U') atTop (nhds (q U')) := by
    simpa only [signature, Function.comp_apply] using (tendsto_pi_nhds.1 hq U')
  have heq : ∀ᶠ n in atTop, basisHitSignature C (φ n) U' = q U' := by
    simpa only [nhds_discrete, tendsto_pure] using hcoord
  have hfrequentTrue : ∃ᶠ n in atTop, basisHitSignature C (φ n) U' = true := by
    exact hfrequentHit.mono fun n hn ↦ by
      have hn' : (C (φ n) ∩ (U' : Set E)).Nonempty := by
        simpa only [U'] using hn
      simp only [basisHitSignature, if_pos hn']
  rcases (hfrequentTrue.and_eventually heq).exists with ⟨n, hnTrue, hnEq⟩
  have hqTrue : q U' = true := hnEq.symm.trans hnTrue
  filter_upwards [heq] with n hn
  have hnTrue' : basisHitSignature C (φ n) U' = true := hn.trans hqTrue
  have hnHit : (C (φ n) ∩ U).Nonempty := by
    simpa [basisHitSignature, U'] using hnTrue'
  exact hnHit.mono (inter_subset_inter_right _ (hUO.trans hOV))

/-- A nonempty outer-limit point can be retained while extracting a
Painleve--Kuratowski convergent subsequence. -/
theorem exists_pkConvergent_subsequence_with_nonempty_limit
    {C : ℕ → Set E} (houter : (outerSetLimit C).Nonempty) :
    ∃ (φ : ℕ → ℕ) (D : Set E),
      StrictMono φ ∧ D.Nonempty ∧ PKConverges (C ∘ φ) D := by
  rcases houter with ⟨x, hx⟩
  rcases mem_outerSetLimit_iff_exists_subsequence.1 hx with
    ⟨ψ, y, hψ, hyC, hyx⟩
  rcases exists_pkConvergent_subsequence (C ∘ ψ) with ⟨φ, D, hφ, hconv⟩
  have hsubOuter : x ∈ outerSetLimit ((C ∘ ψ) ∘ φ) :=
    mem_outerSetLimit_iff_exists_subsequence.2
      ⟨id, y ∘ φ, strictMono_id, fun n ↦ by simpa using hyC (φ n),
        hyx.comp hφ.tendsto_atTop⟩
  refine ⟨ψ ∘ φ, D, hψ.comp hφ, ?_, ?_⟩
  · exact ⟨x, hconv.outer_eq ▸ hsubOuter⟩
  · simpa only [Function.comp_def] using hconv

/-- **Theorem 4.18 (compactness for set convergence).** Every sequence of
nonempty sets either escapes to the horizon (its outer limit is empty) or
has a subsequence converging to a nonempty set. -/
theorem pkCompactness_of_nonempty_sets (C : ℕ → Set E)
    (_hC : ∀ n, (C n).Nonempty) :
    outerSetLimit C = ∅ ∨
      ∃ (φ : ℕ → ℕ) (D : Set E),
        StrictMono φ ∧ D.Nonempty ∧ PKConverges (C ∘ φ) D := by
  rcases Set.eq_empty_or_nonempty (outerSetLimit C) with houter | houter
  · exact Or.inl houter
  · exact Or.inr (exists_pkConvergent_subsequence_with_nonempty_limit houter)

end SetConvergenceCompactness

end RW
