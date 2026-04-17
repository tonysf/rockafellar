/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1G-H: Moreau Envelopes and Epi-Addition

This file formalizes:
- Definition 1.22: Moreau envelope `eλ f` and proximal mapping `Pλ f`
- Definition 1(12): Infimal convolution (epi-addition)
- Key properties and connections between these operations
-/

import RockafellarWets.Chapter1.Defs
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic

open Set Filter Topology Classical

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Definition 1.22: Moreau envelopes and proximal mappings

For a function `f : E → ℝ` and parameter `λ > 0`:
  `eλ f(x) := inf_w { f(w) + (1/2λ)‖w - x‖² }`
  `Pλ f(x) := argmin_w { f(w) + (1/2λ)‖w - x‖² }`
-/

/-- The **Moreau envelope** of `f` with parameter `lam > 0`. -/
def moreauEnvelope (f : E → ℝ) (lam : ℝ) (x : E) : ℝ :=
  ⨅ w : E, f w + (1 / (2 * lam)) * ‖w - x‖ ^ 2

/-- The **proximal mapping** (prox operator). -/
def proximalMapping (f : E → ℝ) (lam : ℝ) (x : E) : Set E :=
  {w : E | f w + (1 / (2 * lam)) * ‖w - x‖ ^ 2 = moreauEnvelope f lam x}

/-! ## Infimal Convolution (Epi-addition)

Definition 1(12): For `f₁, f₂ : E → ℝ`, the epi-sum is:
  `(f₁ □ f₂)(x) = inf_w { f₁(w) + f₂(x - w) }`
-/

/-- The **infimal convolution** (epi-sum) of two functions. -/
def infConvolution (f₁ f₂ : E → ℝ) (x : E) : ℝ :=
  ⨅ w : E, f₁ w + f₂ (x - w)

infixl:70 " □ " => infConvolution

/-! ## Basic properties -/

/-- The Moreau envelope is bounded above by `f` (take `w = x`). -/
theorem moreauEnvelope_le_apply (f : E → ℝ) {lam : ℝ} (hlam : lam > 0) (x : E)
    (hbdd : BddBelow (range fun w => f w + (1 / (2 * lam)) * ‖w - x‖ ^ 2)) :
    moreauEnvelope f lam x ≤ f x := by
  unfold moreauEnvelope
  apply ciInf_le_of_le
  · exact hbdd
  · -- witness: w = x
    change f x + (1 / (2 * lam)) * ‖x - x‖ ^ 2 ≤ f x
    simp [sub_self, norm_zero]

/-- The Moreau envelope is the infimal convolution of `f` with `(1/2λ)‖·‖²`.
This is equation 1(13) in R&W. -/
theorem moreauEnvelope_eq_infConvolution (f : E → ℝ) {lam : ℝ} (_hlam : lam > 0) (x : E) :
    moreauEnvelope f lam x = infConvolution f (fun w => (1 / (2 * lam)) * ‖w‖ ^ 2) x := by
  simp only [moreauEnvelope, infConvolution]
  congr 1; ext w
  congr 1
  rw [norm_sub_rev]

/-- Infimal convolution is commutative. -/
theorem infConvolution_comm (f₁ f₂ : E → ℝ) (x : E) :
    (f₁ □ f₂) x = (f₂ □ f₁) x := by
  -- The map w ↦ x - w is a self-inverse bijection that swaps the two summands
  simp only [infConvolution]
  let e : E ≃ E := ⟨(x - ·), (x - ·), fun w => by simp, fun w => by simp⟩
  rw [show (⨅ w, f₁ w + f₂ (x - w)) = ⨅ w, (f₂ w + f₁ (x - w)) from
    Equiv.iInf_congr e (fun w => by simp [e, add_comm])]

/-- Associativity of infimal convolution at a point, under the slice
bounded-below hypotheses needed for the real-valued infima to behave as
expected. -/
theorem infConvolution_assoc_of_slice_bddBelow
    (f₁ f₂ f₃ : E → ℝ) (x : E)
    (h12 : ∀ u : E, BddBelow (Set.range fun w : E => f₁ w + f₂ (u - w)))
    (h23 : ∀ u : E, BddBelow (Set.range fun z : E => f₂ z + f₃ (u - z)))
    (hleft : BddBelow (Set.range fun u : E => (f₁ □ f₂) u + f₃ (x - u)))
    (hright : BddBelow (Set.range fun w : E => f₁ w + (f₂ □ f₃) (x - w))) :
    ((f₁ □ f₂) □ f₃) x = (f₁ □ (f₂ □ f₃)) x := by
  apply le_antisymm
  · refine le_ciInf ?_
    intro w
    have hrewrite :
        f₁ w + (f₂ □ f₃) (x - w) =
          ⨅ z : E, f₁ w + (f₂ z + f₃ ((x - w) - z)) := by
      simpa [infConvolution, add_assoc] using (add_ciInf (h23 (x - w)) (f₁ w))
    rw [hrewrite]
    refine le_ciInf ?_
    intro z
    have hu :
        ((f₁ □ f₂) □ f₃) x ≤ (f₁ □ f₂) (w + z) + f₃ (x - (w + z)) := by
      unfold infConvolution
      exact ciInf_le hleft (w + z)
    have hw :
        (f₁ □ f₂) (w + z) ≤ f₁ w + f₂ ((w + z) - w) := by
      unfold infConvolution
      exact ciInf_le (h12 (w + z)) w
    exact le_trans hu <| by
      have hsum : (f₁ □ f₂) (w + z) + f₃ (x - (w + z)) ≤
          (f₁ w + f₂ ((w + z) - w)) + f₃ (x - (w + z)) :=
        add_le_add hw le_rfl
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
  · refine le_ciInf ?_
    intro u
    have hrewrite :
        (f₁ □ f₂) u + f₃ (x - u) =
          ⨅ w : E, (f₁ w + f₂ (u - w)) + f₃ (x - u) := by
      simpa [infConvolution, add_assoc] using (ciInf_add (h12 u) (f₃ (x - u)))
    rw [hrewrite]
    refine le_ciInf ?_
    intro w
    have hw :
        (f₁ □ (f₂ □ f₃)) x ≤ f₁ w + (f₂ □ f₃) (x - w) := by
      unfold infConvolution
      exact ciInf_le hright w
    have hz :
        (f₂ □ f₃) (x - w) ≤ f₂ (u - w) + f₃ ((x - w) - (u - w)) := by
      unfold infConvolution
      exact ciInf_le (h23 (x - w)) (u - w)
    exact le_trans hw <| by
      have hsum : f₁ w + (f₂ □ f₃) (x - w) ≤
          f₁ w + (f₂ (u - w) + f₃ ((x - w) - (u - w))) :=
        add_le_add le_rfl hz
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

/-- Function-level associativity of infimal convolution under the slice
bounded-below hypotheses needed for the real-valued infima to behave as
expected. -/
theorem infConvolution_assoc_of_bddBelow
    (f₁ f₂ f₃ : E → ℝ)
    (h12 : ∀ u : E, BddBelow (Set.range fun w : E => f₁ w + f₂ (u - w)))
    (h23 : ∀ u : E, BddBelow (Set.range fun z : E => f₂ z + f₃ (u - z)))
    (hleft : ∀ x : E,
      BddBelow (Set.range fun u : E => (f₁ □ f₂) u + f₃ (x - u)))
    (hright : ∀ x : E,
      BddBelow (Set.range fun w : E => f₁ w + (f₂ □ f₃) (x - w))) :
    (f₁ □ f₂) □ f₃ = f₁ □ (f₂ □ f₃) := by
  funext x
  exact infConvolution_assoc_of_slice_bddBelow f₁ f₂ f₃ x h12 h23 (hleft x) (hright x)

/-- A Moreau-envelope/infimal-convolution associativity identity. This is the
algebraic reassociation used when inserting the quadratic kernel in the
cancellation route toward Theorem `3.34`. -/
theorem moreauEnvelope_infConvolution_assoc_of_slice_bddBelow
    (f₁ f₂ : E → ℝ) {lam : ℝ} (hlam : lam > 0) (x : E)
    (h12 : ∀ u : E, BddBelow (Set.range fun w : E => f₁ w + f₂ (u - w)))
    (h2q : ∀ u : E, BddBelow (Set.range fun z : E =>
      f₂ z + (1 / (2 * lam)) * ‖u - z‖ ^ 2))
    (hleft : BddBelow (Set.range fun u : E =>
      (f₁ □ f₂) u + (1 / (2 * lam)) * ‖x - u‖ ^ 2))
    (hright : BddBelow (Set.range fun w : E =>
      f₁ w + moreauEnvelope f₂ lam (x - w))) :
    moreauEnvelope (f₁ □ f₂) lam x = (f₁ □ moreauEnvelope f₂ lam) x := by
  rw [moreauEnvelope_eq_infConvolution (f := f₁ □ f₂) hlam]
  have hassoc :=
    infConvolution_assoc_of_slice_bddBelow
      f₁ f₂ (fun y : E => (1 / (2 * lam)) * ‖y‖ ^ 2) x
      h12
      (by
        intro u
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h2q u)
      (by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hleft)
      (by
        simpa [moreauEnvelope_eq_infConvolution (f := f₂) hlam] using hright)
  calc
    ((f₁ □ f₂) □ fun y : E => (1 / (2 * lam)) * ‖y‖ ^ 2) x
        = (f₁ □ (f₂ □ fun y : E => (1 / (2 * lam)) * ‖y‖ ^ 2)) x := hassoc
    _ = (f₁ □ moreauEnvelope f₂ lam) x := by
      unfold infConvolution
      congr 1
      ext w
      congr 1
      exact (moreauEnvelope_eq_infConvolution (f := f₂) hlam (x - w)).symm

/-- Function-level reassociation of the Moreau envelope across an infimal
convolution, under the bounded-below hypotheses needed for the real-valued
infima to behave as expected. -/
theorem moreauEnvelope_infConvolution_assoc_of_bddBelow
    (f₁ f₂ : E → ℝ) {lam : ℝ} (hlam : lam > 0)
    (h12 : ∀ u : E, BddBelow (Set.range fun w : E => f₁ w + f₂ (u - w)))
    (h2q : ∀ u : E, BddBelow (Set.range fun z : E =>
      f₂ z + (1 / (2 * lam)) * ‖u - z‖ ^ 2))
    (hleft : ∀ x : E, BddBelow (Set.range fun u : E =>
      (f₁ □ f₂) u + (1 / (2 * lam)) * ‖x - u‖ ^ 2))
    (hright : ∀ x : E, BddBelow (Set.range fun w : E =>
      f₁ w + moreauEnvelope f₂ lam (x - w))) :
    moreauEnvelope (f₁ □ f₂) lam = f₁ □ moreauEnvelope f₂ lam := by
  funext x
  exact moreauEnvelope_infConvolution_assoc_of_slice_bddBelow
    f₁ f₂ hlam x h12 h2q (hleft x) (hright x)

/-- The linear-functional infimum of an infimal convolution splits into the sum
of the linear-functional infima of the two summands, provided those shifted
summands are bounded below. This is the algebraic identity used in the proof of
Theorem `3.34`. -/
theorem iInf_sub_linear_infConvolution_eq
    (f₁ f₂ : E → ℝ) (l : E →ₗ[ℝ] ℝ)
    (hbdd₁ : BddBelow (Set.range fun w : E => f₁ w - l w))
    (hbdd₂ : BddBelow (Set.range fun w : E => f₂ w - l w)) :
    (⨅ x : E, (f₁ □ f₂) x - l x) =
      (⨅ w : E, f₁ w - l w) + (⨅ w : E, f₂ w - l w) := by
  let A : E → ℝ := fun w => f₁ w - l w
  let B : E → ℝ := fun w => f₂ w - l w
  have hAB : ∀ x : E, BddBelow (Set.range fun w : E => A w + B (x - w)) := by
    intro x
    rcases hbdd₁ with ⟨c₁, hc₁⟩
    rcases hbdd₂ with ⟨c₂, hc₂⟩
    refine ⟨c₁ + c₂, ?_⟩
    rintro _ ⟨w, rfl⟩
    have h₁ : c₁ ≤ A w := hc₁ ⟨w, rfl⟩
    have h₂ : c₂ ≤ B (x - w) := hc₂ ⟨x - w, rfl⟩
    linarith
  have hSlice : ∀ x : E, BddBelow (Set.range fun w : E => f₁ w + f₂ (x - w)) := by
    intro x
    rcases hbdd₁ with ⟨c₁, hc₁⟩
    rcases hbdd₂ with ⟨c₂, hc₂⟩
    refine ⟨c₁ + c₂ + l x, ?_⟩
    rintro _ ⟨w, rfl⟩
    have h₁ : c₁ ≤ f₁ w - l w := hc₁ ⟨w, rfl⟩
    have h₂ : c₂ ≤ f₂ (x - w) - l (x - w) := hc₂ ⟨x - w, rfl⟩
    have hlin : l x = l w + l (x - w) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        l.map_add w (x - w)
    linarith
  have hOuter :
      BddBelow (Set.range fun x : E => ⨅ w : E, A w + B (x - w)) := by
    rcases hbdd₁ with ⟨c₁, hc₁⟩
    rcases hbdd₂ with ⟨c₂, hc₂⟩
    refine ⟨c₁ + c₂, ?_⟩
    rintro _ ⟨x, rfl⟩
    refine le_ciInf ?_
    intro w
    have h₁ : c₁ ≤ A w := hc₁ ⟨w, rfl⟩
    have h₂ : c₂ ≤ B (x - w) := hc₂ ⟨x - w, rfl⟩
    linarith
  have hPointwise :
      ∀ x : E, (f₁ □ f₂) x - l x = ⨅ w : E, A w + B (x - w) := by
    intro x
    unfold infConvolution
    rw [sub_eq_add_neg, ciInf_add (hSlice x) (-l x)]
    congr 1
    funext w
    have hlin : l x = l w + l (x - w) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        l.map_add w (x - w)
    dsimp [A, B]
    linarith
  have hLower :
      (⨅ w : E, A w) + (⨅ w : E, B w) ≤
        ⨅ x : E, ⨅ w : E, A w + B (x - w) := by
    refine le_ciInf ?_
    intro x
    refine le_ciInf ?_
    intro w
    exact add_le_add (ciInf_le hbdd₁ w) (ciInf_le hbdd₂ (x - w))
  have hUpperW :
      ∀ w : E,
        (⨅ x : E, ⨅ u : E, A u + B (x - u)) ≤ A w + (⨅ u : E, B u) := by
    intro w
    have htemp :
        (⨅ x : E, ⨅ u : E, A u + B (x - u)) ≤
          ⨅ u : E, A w + B u := by
      refine le_ciInf ?_
      intro u
      calc
        (⨅ x : E, ⨅ u' : E, A u' + B (x - u')) ≤
            ⨅ u' : E, A u' + B ((w + u) - u') := by
              exact ciInf_le hOuter (w + u)
        _ ≤ A w + B ((w + u) - w) := by
              exact ciInf_le (hAB (w + u)) w
        _ = A w + B u := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [← add_ciInf hbdd₂ (A w)] at htemp
    exact htemp
  have hUpper :
      (⨅ x : E, ⨅ w : E, A w + B (x - w)) ≤
        (⨅ w : E, A w) + (⨅ w : E, B w) := by
    have htemp :
        (⨅ x : E, ⨅ u : E, A u + B (x - u)) ≤
          ⨅ w : E, A w + (⨅ u : E, B u) := by
      refine le_ciInf ?_
      intro w
      exact hUpperW w
    rw [← ciInf_add hbdd₁ (⨅ u : E, B u)] at htemp
    exact htemp
  calc
    (⨅ x : E, (f₁ □ f₂) x - l x)
        = ⨅ x : E, ⨅ w : E, A w + B (x - w) := by
            simp [hPointwise]
    _ = (⨅ w : E, A w) + (⨅ w : E, B w) := le_antisymm hUpper hLower

/-- **Exercise 1.28(a)** (one direction): Every point in the Minkowski sum
of epigraphs lies in the epigraph of the infimal convolution, provided the
infimal-convolution slices are bounded below so the real-valued infimum has the
expected meaning.
  `epi f₁ + epi f₂ ⊆ epi(f₁ □ f₂)` -/
theorem epigraph_infConvolution_supset (f₁ f₂ : E → ℝ)
    (hbdd : ∀ x : E, BddBelow (range fun w => f₁ w + f₂ (x - w))) :
    {p : E × ℝ | ∃ p₁ ∈ epigraph (fun x => (f₁ x : EReal)),
                   ∃ p₂ ∈ epigraph (fun x => (f₂ x : EReal)),
                   p = (p₁.1 + p₂.1, p₁.2 + p₂.2)} ⊆
    epigraph (fun x => ((f₁ □ f₂) x : EReal)) := by
  intro ⟨x, α⟩ hm
  simp only [mem_setOf_eq] at hm
  obtain ⟨⟨x₁, α₁⟩, hep₁, ⟨x₂, α₂⟩, hep₂, hprod⟩ := hm
  simp only [Prod.mk.injEq] at hprod
  obtain ⟨hx, hα⟩ := hprod
  simp only [epigraph, mem_setOf_eq, ge_iff_le] at hep₁ hep₂ ⊢
  -- hep₁ : (f₁ x₁ : EReal) ≤ α₁
  -- hep₂ : (f₂ x₂ : EReal) ≤ α₂
  -- Goal : ((f₁ □ f₂) x : EReal) ≤ (α : EReal)
  rw [hα]
  -- Goal : ((f₁ □ f₂) (x₁ + x₂) : EReal) ≤ ↑(α₁ + α₂)
  rw [hx]
  show ((⨅ w, f₁ w + f₂ (x₁ + x₂ - w) : ℝ) : EReal) ≤ ↑(α₁ + α₂)
  have hval : f₁ x₁ + f₂ ((x₁ + x₂) - x₁) = f₁ x₁ + f₂ x₂ := by
    congr 1; simp [add_sub_cancel_left]
  have h₁ : f₁ x₁ ≤ α₁ := by exact_mod_cast hep₁
  have h₂ : f₂ x₂ ≤ α₂ := by exact_mod_cast hep₂
  have hle : f₁ x₁ + f₂ x₂ ≤ α₁ + α₂ := add_le_add h₁ h₂
  have hinf : ⨅ w, f₁ w + f₂ (x₁ + x₂ - w) ≤ f₁ x₁ + f₂ x₂ := by
    rw [← hval]
    exact ciInf_le (hbdd (x₁ + x₂)) x₁
  exact_mod_cast le_trans hinf hle

/-! ## Theorem 1.25: Proximal behavior (statements)

These are the key results about Moreau envelopes. Full proofs require
the parametric minimization machinery of Theorem 1.17.
-/

/-- **Theorem 1.25** (part): For `f` proper, lsc, and prox-bounded with
threshold `λ_f > 0`, and for `λ ∈ (0, λ_f)`:
- `Pλ f(x)` is nonempty and compact
- `eλ f(x)` is finite and continuous in `(λ, x)`
- `eλ f(x) ↗ f(x)` as `λ ↘ 0` -/
theorem moreauEnvelope_converges_to_f
    {f : E → ℝ} (x : E)
    (hf_cont : ContinuousAt f x)
    (hf_bdd : ∃ c : ℝ, ∀ w : E, f w ≥ c) :
    Filter.Tendsto (fun lam => moreauEnvelope f lam x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
  rcases hf_bdd with ⟨c, hc⟩
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rcases (Metric.continuousAt_iff.mp hf_cont) (ε / 2) hε2 with ⟨r, hrpos, hr⟩
  let B : ℝ := max 0 (f x - ε / 2 - c) + 1
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨r ^ 2 / (2 * B), by positivity, ?_⟩
  intro lam hlam hdist
  have hlam_pos : 0 < lam := hlam
  have hlam_lt : lam < r ^ 2 / (2 * B) := by
    simpa [Real.dist_eq, abs_of_pos hlam_pos] using hdist
  have hbdd :
      BddBelow (range fun w => f w + (1 / (2 * lam)) * ‖w - x‖ ^ 2) := by
    refine ⟨c, ?_⟩
    rintro _ ⟨w, rfl⟩
    have hpen_nonneg : 0 ≤ (1 / (2 * lam)) * ‖w - x‖ ^ 2 := by positivity
    linarith [hc w]
  have hupper : moreauEnvelope f lam x ≤ f x :=
    moreauEnvelope_le_apply f hlam_pos x hbdd
  have hlower : f x - ε / 2 ≤ moreauEnvelope f lam x := by
    unfold moreauEnvelope
    refine le_ciInf ?_
    intro w
    by_cases hnear : dist w x < r
    · have hfw_dist : dist (f w) (f x) < ε / 2 := hr hnear
      have hfw_abs : |f w - f x| < ε / 2 := by
        simpa [Real.dist_eq] using hfw_dist
      have hfw : f x - ε / 2 ≤ f w := by
        have hleft := (abs_lt.mp hfw_abs).1
        linarith
      have hpen_nonneg : 0 ≤ (1 / (2 * lam)) * ‖w - x‖ ^ 2 := by positivity
      linarith
    · have hfar : r ≤ dist w x := le_of_not_gt hnear
      have hnorm_far : r ≤ ‖w - x‖ := by simpa [dist_eq_norm] using hfar
      have hsq : r ^ 2 ≤ ‖w - x‖ ^ 2 := by
        nlinarith
      have hBlt_div : B < r ^ 2 / (2 * lam) := by
        refine (_root_.lt_div_iff₀ ?_).2 ?_
        · positivity
        · have htmp : lam * (2 * B) < r ^ 2 := by
            exact (_root_.lt_div_iff₀ (by positivity)).mp hlam_lt
          nlinarith
      have hBlt : B < (1 / (2 * lam)) * r ^ 2 := by
        simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hBlt_div
      have hpen : B < (1 / (2 * lam)) * ‖w - x‖ ^ 2 := by
        have hmul :
            (1 / (2 * lam)) * r ^ 2 ≤ (1 / (2 * lam)) * ‖w - x‖ ^ 2 := by
          gcongr
        exact lt_of_lt_of_le hBlt hmul
      have hBbound : f x - ε / 2 < c + B := by
        dsimp [B]
        by_cases hcx : 0 ≤ f x - ε / 2 - c
        · rw [max_eq_right hcx]
          linarith
        · rw [max_eq_left (le_of_not_ge hcx)]
          linarith
      linarith [hc w, hpen]
  have hdist' : dist (moreauEnvelope f lam x) (f x) < ε := by
    have hsub : f x - moreauEnvelope f lam x ≤ ε / 2 := by
      linarith
    have hsub' : f x - moreauEnvelope f lam x < ε := by
      linarith
    simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)] using hsub'
  exact hdist'

end RW
