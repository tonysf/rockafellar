/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: the extended chain rule for subgradients

**Theorem 10.49** for `f = g ∘ F` with `g : ℝᵐ → ℝ̄` proper lsc (here only lsc is needed) and
`F` strictly continuous at `x̄`, with `f(x̄)` finite.  Writing `∂(yF)(x̄)` for the subgradients of
the scalarization `x ↦ ⟪y, F(x)⟫`, which equal `D*F(x̄)(y)` (9.24(b)):

* `∂̂f(x̄) ⊃ ⋃ {∂̂(yF)(x̄) | y ∈ ∂̂g(F(x̄))}` (`regularSubdifferential_comp_superset`);
* if the only `y ∈ ∂^∞g(F(x̄))` with `0 ∈ ∂(yF)(x̄)` is `y = 0`, then
  `∂f(x̄) ⊂ ⋃ {∂(yF)(x̄) | y ∈ ∂g(F(x̄))}` and
  `∂^∞f(x̄) ⊂ ⋃ {∂(yF)(x̄) | y ∈ ∂^∞g(F(x̄))}` (`subdifferential_comp_subset_of_strictlyContinuous`).

* regularity: if `g` is regular at `F(x̄)` and `yF` is regular at `x̄` for every `y` in the cone
  `⋃_{r > 0} r ∂g(F(x̄))` and in `∂^∞g(F(x̄))`, then `f` is regular at `x̄` and both inclusions
  are equalities (`comp_regular_of_strictlyContinuous`).  The book asks regularity of `yF` only
  for `y ∈ ∂g(F(x̄))`; the 10.40 regularity clause used here needs it on all coderivative values
  of the profile `E_g` (heights `r > 0` and `0`), so this clause is stated under that hypothesis.
  The printed hypothesis alone does not suffice when `∂g(F(x̄)) = ∅`: `g(u) = -√u` on `[0, ∞)`
  (`∞` elsewhere) is regular at `0` with `∂g(0) = ∅` and `∂^∞g(0) = (-∞, 0]`, and `F(x) = |x|`
  satisfies the qualification, yet `f(x) = -√|x|` is not regular at `0` (the epigraph has regular
  normal cone `{0}` at `(0, 0)` but nonzero horizontal limiting normals).  When `F` is strictly
  differentiable at `x̄` every `yF` is regular, which gives the book's parenthetical case
  (`comp_regular_of_hasStrictFDerivAt` in `LipschitzConstraintNormals`).

As in the book, these come from the coderivative chain rule 10.40 (root's
`InnerCompositionCoderivatives`, `InnerCompositionRegularity`) applied to the profile mappings
`E_f = E_g ∘ F`, whose coderivatives at heights `1` and `0` are the subgradients and horizon
subgradients (8.35).  The cosmic outer semicontinuity of
`x ↦ D*F(x)(∂g(F(x))) ∪ dir D*F(x)(∂^∞g(F(x)))` with respect to `f`-attentive convergence is
proved in sequential form in `ExtendedChainRuleOsc`.
-/

import RockafellarWets.Chapter10.InnerCompositionCoderivatives
import RockafellarWets.Chapter10.InnerCompositionRegularity
import RockafellarWets.Chapter8.ProfileDerivatives
import RockafellarWets.Chapter9.CoderivativeScalarization
import RockafellarWets.Chapter9.SmoothnessCriteria
import RockafellarWets.Chapter5.ProfileMappings

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Theorem 10.49**: `∂̂f(x̄) ⊃ D̂*F(x̄)(∂̂g(F(x̄))) = ⋃ {∂̂(yF)(x̄) | y ∈ ∂̂g(F(x̄))}`. -/
theorem regularSubdifferential_comp_superset {g : F → EReal} {G : E → F} {x : E} {c : ℝ}
    (hG : StrictlyContinuousAt G x) (hc : g (G x) = c) :
    {v | ∃ y ∈ regularSubdifferential g (G x),
        v ∈ regularSubdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x} ⊆
      regularSubdifferential (fun a ↦ g (G a)) x := by
  rintro v ⟨y, hy, hv⟩
  have hu : c ∈ epiProfile g (G x) := by
    show ((c : ℝ) : EReal) ≥ g (G x)
    rw [hc]
  have hS1 : regularCoderivative (epiProfile g) (G x) c 1 = regularSubdifferential g (G x) := by
    simpa using (coderivatives_epiProfile_of_pos hc one_pos).2
  have hf1 : regularCoderivative (epiProfile (fun a ↦ g (G a))) x c 1 =
      regularSubdifferential (fun a ↦ g (G a)) x := by
    simpa using (coderivatives_epiProfile_of_pos (f := fun a ↦ g (G a)) (x := x) hc one_pos).2
  rw [← hf1]
  apply regularCoderivative_inner_comp_superset (S := epiProfile g) hG hu (1 : ℝ)
  refine mem_svComp.2 ⟨y, by rw [hS1]; exact hy, ?_⟩
  rw [regularCoderivative_svSingleton_eq_regularSubdifferential hG y]
  exact hv

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- The composition of an lsc function with a mapping continuous near `x̄` is locally lsc. -/
theorem isLocallyLscAt_comp {g : F → EReal} {G : E → F} {x : E} {c : ℝ}
    (hl : LowerSemicontinuous g) (hG : StrictlyContinuousAt G x) (hc : g (G x) = c) :
    IsLocallyLscAt (fun a ↦ g (G a)) x := by
  obtain ⟨k, U, hU, hL⟩ := strictlyContinuousAt_iff.1 hG
  have hlsc : LowerSemicontinuousOn (fun a ↦ g (G a)) (interior U) := by
    intro y hy a ha
    have hGy : ContinuousAt G y := hL.continuousOn.continuousAt
      (mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)
    exact (hGy.tendsto.eventually (hl (G y) a ha)).filter_mono nhdsWithin_le_nhds
  exact isLocallyLscAt_of_lowerSemicontinuousOn isOpen_interior hlsc (mem_interior_iff_mem_nhds.2 hU)
    (by rw [hc]; exact EReal.coe_ne_bot c) (by rw [hc]; exact EReal.coe_ne_top c)

/-- **Theorem 10.49**: under the qualification that the only `y ∈ ∂^∞g(F(x̄))` with
`0 ∈ ∂(yF)(x̄)` is `y = 0`,
`∂f(x̄) ⊂ ⋃ {∂(yF)(x̄) | y ∈ ∂g(F(x̄))}` and `∂^∞f(x̄) ⊂ ⋃ {∂(yF)(x̄) | y ∈ ∂^∞g(F(x̄))}`. -/
theorem subdifferential_comp_subset_of_strictlyContinuous {g : F → EReal} {G : E → F} {x : E}
    {c : ℝ} (hl : LowerSemicontinuous g) (hG : StrictlyContinuousAt G x) (hc : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x → y = 0) :
    subdifferential (fun a ↦ g (G a)) x ⊆
        {v | ∃ y ∈ subdifferential g (G x),
          v ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x} ∧
      horizonSubdifferential (fun a ↦ g (G a)) x ⊆
        {v | ∃ y ∈ horizonSubdifferential g (G x),
          v ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x} := by
  have hS : SvOsc (epiProfile g) := (svOsc_epiProfile_iff g).2 hl
  have hlg : IsLocallyLscAt g (G x) :=
    isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ (hl.lowerSemicontinuousOn _) (mem_univ _)
      (by rw [hc]; exact EReal.coe_ne_bot c) (by rw [hc]; exact EReal.coe_ne_top c)
  have hS0 : coderivative (epiProfile g) (G x) c 0 = horizonSubdifferential g (G x) :=
    coderivative_epiProfile_zero hc hlg
  have hS1 : coderivative (epiProfile g) (G x) c 1 = subdifferential g (G x) := by
    simpa using (coderivatives_epiProfile_of_pos hc one_pos).1
  have hQ' : ∀ z ∈ coderivative (epiProfile g) (G x) c 0,
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪z, G a⟫_ℝ : ℝ) : EReal)) x → z = 0 := by
    rw [hS0]
    exact hQ
  have hlf := isLocallyLscAt_comp hl hG hc
  have hf1 : coderivative (epiProfile (fun a ↦ g (G a))) x c 1 =
      subdifferential (fun a ↦ g (G a)) x := by
    simpa using (coderivatives_epiProfile_of_pos (f := fun a ↦ g (G a)) (x := x) hc one_pos).1
  have hf0 : coderivative (epiProfile (fun a ↦ g (G a))) x c 0 =
      horizonSubdifferential (fun a ↦ g (G a)) x :=
    coderivative_epiProfile_zero (f := fun a ↦ g (G a)) hc hlf
  constructor
  · intro v hv
    rw [← hf1] at hv
    obtain ⟨z, hz, hvz⟩ := mem_svComp.1
      (coderivative_inner_comp_subset_of_scalar_qualification (S := epiProfile g) hS hG hQ' 1 hv)
    rw [hS1] at hz
    rw [coderivative_svSingleton_eq_subdifferential hG z] at hvz
    exact ⟨z, hz, hvz⟩
  · intro v hv
    rw [← hf0] at hv
    obtain ⟨z, hz, hvz⟩ := mem_svComp.1
      (coderivative_inner_comp_subset_of_scalar_qualification (S := epiProfile g) hS hG hQ' 0 hv)
    rw [hS0] at hz
    rw [coderivative_svSingleton_eq_subdifferential hG z] at hvz
    exact ⟨z, hz, hvz⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem euclideanSvGraph_epiProfile (g : F → EReal) :
    euclideanSvGraph (epiProfile g) = l2Epigraph g := rfl

/-- **Theorem 10.49**, regular case: `f` is regular at `x̄` with
`∂f(x̄) = ⋃ {∂(yF)(x̄) | y ∈ ∂g(F(x̄))}` and `∂^∞f(x̄) = ⋃ {∂(yF)(x̄) | y ∈ ∂^∞g(F(x̄))}`. -/
theorem comp_regular_of_strictlyContinuous {g : F → EReal} {G : E → F} {x : E} {c : ℝ}
    (hl : LowerSemicontinuous g) (hG : StrictlyContinuousAt G x) (hc : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x),
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x → y = 0)
    (hrg : IsSubdifferentiallyRegularAt g (G x))
    (hry : ∀ y, ((∃ r : ℝ, 0 < r ∧ y ∈ r • subdifferential g (G x)) ∨
        y ∈ horizonSubdifferential g (G x)) →
      IsSubdifferentiallyRegularAt (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x) :
    IsSubdifferentiallyRegularAt (fun a ↦ g (G a)) x ∧
      subdifferential (fun a ↦ g (G a)) x =
        {v | ∃ y ∈ subdifferential g (G x),
          v ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x} ∧
      horizonSubdifferential (fun a ↦ g (G a)) x =
        {v | ∃ y ∈ horizonSubdifferential g (G x),
          v ∈ subdifferential (fun a ↦ ((⟪y, G a⟫_ℝ : ℝ) : EReal)) x} := by
  have hS : SvOsc (epiProfile g) := (svOsc_epiProfile_iff g).2 hl
  have hlg : IsLocallyLscAt g (G x) :=
    isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ (hl.lowerSemicontinuousOn _) (mem_univ _)
      (by rw [hc]; exact EReal.coe_ne_bot c) (by rw [hc]; exact EReal.coe_ne_top c)
  have hS0 : coderivative (epiProfile g) (G x) c 0 = horizonSubdifferential g (G x) :=
    coderivative_epiProfile_zero hc hlg
  have hS1 : coderivative (epiProfile g) (G x) c 1 = subdifferential g (G x) := by
    simpa using (coderivatives_epiProfile_of_pos hc one_pos).1
  have hQ' : ∀ z ∈ coderivative (epiProfile g) (G x) c 0,
      (0 : E) ∈ subdifferential (fun a ↦ ((⟪z, G a⟫_ℝ : ℝ) : EReal)) x → z = 0 := by
    rw [hS0]
    exact hQ
  have hu : c ∈ epiProfile g (G x) := by
    show ((c : ℝ) : EReal) ≥ g (G x)
    rw [hc]
  have hcR : (g (G x)).toReal = c := by rw [hc, EReal.toReal_coe]
  have hrS : IsGraphicallyRegularAt (epiProfile g) (G x) c := by
    have h := hrg.2.2
    rw [hcR] at h
    exact h
  have hrf : ∀ r z, z ∈ coderivative (epiProfile g) (G x) c r →
      IsSubdifferentiallyRegularAt (fun a ↦ ((⟪z, G a⟫_ℝ : ℝ) : EReal)) x := by
    intro r z hz
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · rw [(coderivatives_epiProfile_of_neg g (G x) c hr).1] at hz
      exact absurd hz (notMem_empty z)
    · rw [hS0] at hz
      exact hry z (Or.inr hz)
    · rw [(coderivatives_epiProfile_of_pos hc hr).1] at hz
      exact hry z (Or.inl ⟨r, hr, hz⟩)
  obtain ⟨hreg, heq⟩ := inner_comp_regular_and_coderivative_eq hS hG hu hQ' hrS hrf
  have hlf := isLocallyLscAt_comp hl hG hc
  have hf1 : coderivative (epiProfile (fun a ↦ g (G a))) x c 1 =
      subdifferential (fun a ↦ g (G a)) x := by
    simpa using (coderivatives_epiProfile_of_pos (f := fun a ↦ g (G a)) (x := x) hc one_pos).1
  have hf0 : coderivative (epiProfile (fun a ↦ g (G a))) x c 0 =
      horizonSubdifferential (fun a ↦ g (G a)) x :=
    coderivative_epiProfile_zero (f := fun a ↦ g (G a)) hc hlf
  have hset : ∀ r, coderivative (epiProfile (fun a ↦ g (G a))) x c r =
      {v | ∃ z ∈ coderivative (epiProfile g) (G x) c r,
        v ∈ subdifferential (fun a ↦ ((⟪z, G a⟫_ℝ : ℝ) : EReal)) x} := by
    intro r
    have h1 := congrFun heq r
    ext v
    rw [show coderivative (epiProfile (fun a ↦ g (G a))) x c r =
      coderivative (fun a ↦ epiProfile g (G a)) x c r from rfl, h1, mem_svComp]
    constructor
    · rintro ⟨z, hz, hv⟩
      rw [coderivative_svSingleton_eq_subdifferential hG z] at hv
      exact ⟨z, hz, hv⟩
    · rintro ⟨z, hz, hv⟩
      rw [← coderivative_svSingleton_eq_subdifferential hG z] at hv
      exact ⟨z, hz, hv⟩
  refine ⟨⟨by show g (G x) ≠ ⊥; rw [hc]; exact EReal.coe_ne_bot c,
    by show g (G x) ≠ ⊤; rw [hc]; exact EReal.coe_ne_top c, ?_⟩, ?_, ?_⟩
  · show IsClarkeRegularAt (l2Epigraph (fun a ↦ g (G a))) (WithLp.toLp 2 (x, (g (G x)).toReal))
    rw [hcR]
    exact hreg
  · rw [← hf1, hset 1, hS1]
  · rw [← hf0, hset 0, hS0]

end RW
