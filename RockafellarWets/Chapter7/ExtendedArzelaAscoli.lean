/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Extended Arzelà–Ascoli theorem

The upper and lower rays are treated by the same compactness argument. A
graphical limit of the restricted profiles gives pointwise set convergence by
equi-outer semicontinuity. Compactness of the extended reals then identifies
each limiting fiber with the ray of a scalar value.
-/

import RockafellarWets.Chapter7.EpiPointwiseConvergence
import RockafellarWets.Chapter7.ExtendedUniformConvergence
import RockafellarWets.Chapter5.ArzelaAscoli

open Filter Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : ℕ → E → EReal} {X : Set E}

private theorem exists_subsequence_rayProfile
    (P : EReal → Set ℝ)
    (hP : ∀ (a : ℕ → EReal) b, PKConverges (fun n ↦ P (a n)) (P b) ↔ Tendsto a atTop (𝓝 b))
    (he : ∀ x ∈ X, SvAsymptoticallyEquiOscWithinAt (fun n y ↦ P (f n y)) X x) :
    ∃ (φ : ℕ → ℕ) (g : E → EReal), StrictMono φ ∧ SvOscOn (P ∘ g) X ∧
      GraphicalConvergesOn (fun n y ↦ P (f (φ n) y)) (P ∘ g) X ∧
      ∀ x ∈ X, Tendsto (fun n ↦ f (φ n) x) atTop (𝓝 (g x)) := by
  classical
  obtain ⟨φ, S, hφ, hS⟩ := exists_graphicalConverges_subsequence
    (fun n ↦ svRestrict (fun y ↦ P (f n y)) X)
  have hrel : GraphicalConvergesOn (fun n y ↦ P (f (φ n) y)) S X :=
    graphicalConvergesOn_of_graphicalConverges_svRestrict (φ := φ)
      (Sseq := fun n y ↦ P (f n y)) (X := X) hS
  have hp (x : E) (hx : x ∈ X) : PKConverges (fun n ↦ P (f (φ n) x)) (S x) :=
    PointwiseConvergesAt.of_graphicalConvergesWithinAt (Sseq := fun n y ↦ P (f (φ n) y)) (S := S) hx ((he x hx).comp_strictMono hφ) (hrel x hx)
  have hex (x : E) (hx : x ∈ X) : ∃ b, S x = P b := by
    obtain ⟨b, ψ, hψ, hb⟩ := CompactSpace.tendsto_subseq (fun n ↦ f (φ n) x)
    have h := (hP _ _).mpr hb
    have hs : S x ⊆ P b := (hp x hx).inner_eq.symm.subset.trans
      ((innerSetLimit_subset_subsequence hψ).trans h.inner_eq.subset)
    have hr : P b ⊆ S x := h.outer_eq.symm.subset.trans
      ((outerSetLimit_subsequence_subset hψ).trans (hp x hx).outer_eq.subset)
    exact ⟨b, hs.antisymm hr⟩
  let g := fun x ↦ if hx : x ∈ X then (hex x hx).choose else ⊤
  have hg (x : E) (hx : x ∈ X) : S x = P (g x) := by
    simpa only [g, dif_pos hx] using (hex x hx).choose_spec
  refine ⟨φ, g, hφ, ?_, ?_, ?_⟩
  · intro x hx
    have hnear : P ∘ g =ᶠ[𝓝[X] x] S := by
      filter_upwards [self_mem_nhdsWithin (s := X) (a := x)] with y hy
      exact (hg y hy).symm
    change outerSetLimitAlong (𝓝[X] x) (P ∘ g) ⊆ P (g x)
    rw [outerSetLimitAlong_congr hnear, ← hg x hx]
    exact (outerSetLimitAlong_mono_filter nhdsWithin_le_nhds S).trans (hS.svOsc x)
  · intro x hx
    simpa only [GraphicalConvergesWithinAt, Function.comp_apply, ← hg x hx] using hrel x hx
  · intro x hx
    apply (hP _ _).mp
    rw [← hg x hx]
    exact hp x hx

/-- **Exercise 7.16(a).** Relative asymptotic equi-lower semicontinuity
gives a subsequence converging both pointwise and epigraphically on `X`. -/
theorem exists_subsequence_epiConvergesWithinAt_and_pointwise
    (he : ∀ x ∈ X, AsymptoticallyEquiLscWithinAt f X x) :
    ∃ (φ : ℕ → ℕ) (g : E → EReal), StrictMono φ ∧ LowerSemicontinuousOn g X ∧
      ∀ x ∈ X, EpiConvergesWithinAt (f ∘ φ) g X x ∧ Tendsto (fun n ↦ f (φ n) x) atTop (𝓝 (g x)) := by
  obtain ⟨φ, g, hφ, hos, hg, hp⟩ := exists_subsequence_rayProfile
    (epiProfile id) pkConverges_epiProfile_iff_tendsto he
  exact ⟨φ, g, hφ, (svOscOn_epiProfile_iff g X).mp hos, fun x hx ↦ ⟨hg x hx, hp x hx⟩⟩

/-- **Exercise 7.16(b).** The analogous conclusion for upper semicontinuity
and hypographical convergence. -/
theorem exists_subsequence_hypoConvergesWithinAt_and_pointwise
    (he : ∀ x ∈ X, AsymptoticallyEquiUscWithinAt f X x) :
    ∃ (φ : ℕ → ℕ) (g : E → EReal), StrictMono φ ∧ UpperSemicontinuousOn g X ∧
      ∀ x ∈ X, HypoConvergesWithinAt (f ∘ φ) g X x ∧ Tendsto (fun n ↦ f (φ n) x) atTop (𝓝 (g x)) := by
  obtain ⟨φ, g, hφ, hos, hg, hp⟩ := exists_subsequence_rayProfile
    (hypoProfile id) pkConverges_hypoProfile_iff_tendsto he
  exact ⟨φ, g, hφ, fun x hx ↦ (svOscWithinAt_hypoProfile_iff g X x).mp (hos x hx), fun x hx ↦ ⟨hg x hx, hp x hx⟩⟩

/-- **Exercise 7.16(c).** If both forms of asymptotic equi-semicontinuity
hold, the same subsequence converges uniformly on every compact subset. -/
theorem exists_subsequence_erealConvergesUniformlyOn
    (hl : ∀ x ∈ X, AsymptoticallyEquiLscWithinAt f X x)
    (hu : ∀ x ∈ X, AsymptoticallyEquiUscWithinAt f X x) :
    ∃ (φ : ℕ → ℕ) (g : E → EReal), StrictMono φ ∧ ContinuousOn g X ∧
      ∀ B ⊆ X, IsCompact B → ERealConvergesUniformlyOn (f ∘ φ) g B := by
  obtain ⟨φ, g, hφ, -, hg⟩ := exists_subsequence_epiConvergesWithinAt_and_pointwise hl
  refine ⟨φ, g, hφ, convergesContinuouslyOn_iff_continuousOn_and_erealConvergesUniformlyOn.mp ?_⟩
  intro x hx
  exact (convergesContinuouslyWithinAt_iff_epi_and_equiSemicontinuity hx).mpr
    ⟨(hg x hx).1, (hl x hx).comp_strictMono hφ, (hu x hx).comp_strictMono hφ⟩

end RW
