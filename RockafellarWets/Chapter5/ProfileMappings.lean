/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Profile Mappings

Example 5.5 attaches to an extended-real-valued function `f` the set-valued
mapping `Ef(x) = {α ∈ IR | α ≥ f(x)}`, whose graph is the epigraph of `f`.
It is the dictionary entry translating semicontinuity of functions, from
Chapter 1, into semicontinuity of set-valued mappings, from Definition 5.4:
`Ef` is osc exactly where `f` is lsc, and isc exactly where `f` is usc.

Note that the profile values are sets of *real* numbers even though `f` takes
values in `IR‾`; this is the convention `Ef : IRⁿ →→ IR¹` of the book, and it
is what makes `gph Ef` literally the Chapter 1 epigraph `epi f ⊂ E × IR`.

The final clause -- that the level-set mapping `α ↦ lev≤α f` is osc
everywhere exactly when `f` is lsc everywhere -- comes for free: that mapping
is `Ef⁻¹`, and 5.7(a) says a mapping is osc exactly when its inverse is.
-/

import RockafellarWets.Chapter1.Semicontinuity
import RockafellarWets.Chapter5.SemicontinuityCriteria

open Filter Set Topology

namespace RW

section Definitions

variable {E : Type*}

/-- **Example 5.5**: the epigraphical profile mapping
`Ef(x) = {α ∈ IR | α ≥ f(x)}`. -/
def epiProfile (f : E → EReal) : E → Set ℝ :=
  fun x ↦ {α : ℝ | (α : EReal) ≥ f x}

/-- **Example 5.5**: the hypographical profile mapping
`Hf(x) = {α ∈ IR | α ≤ f(x)}`. -/
def hypoProfile (f : E → EReal) : E → Set ℝ :=
  fun x ↦ {α : ℝ | (α : EReal) ≤ f x}

@[simp]
theorem mem_epiProfile {f : E → EReal} {x : E} {α : ℝ} :
    α ∈ epiProfile f x ↔ f x ≤ (α : EReal) := Iff.rfl

@[simp]
theorem mem_hypoProfile {f : E → EReal} {x : E} {α : ℝ} :
    α ∈ hypoProfile f x ↔ (α : EReal) ≤ f x := Iff.rfl

/-- `gph Ef = epi f`. -/
theorem svGraph_epiProfile (f : E → EReal) :
    svGraph (epiProfile f) = epigraph f := rfl

/-- `gph Hf = hypo f`. -/
theorem svGraph_hypoProfile (f : E → EReal) :
    svGraph (hypoProfile f) = hypograph f := rfl

/-- `Ef⁻¹(α) = lev≤α f`. -/
theorem svInv_epiProfile (f : E → EReal) (α : ℝ) :
    svInv (epiProfile f) α = levelSet f (α : EReal) := rfl

/-- `Hf⁻¹(α) = lev≥α f`. -/
theorem svInv_hypoProfile (f : E → EReal) (α : ℝ) :
    svInv (hypoProfile f) α = upperLevelSet f (α : EReal) := rfl

/-- `dom Ef = dom f`.  A real number lies above `f(x)` exactly when `f(x)`
falls short of `∞`. -/
theorem svDom_epiProfile (f : E → EReal) :
    svDom (epiProfile f) = effectiveDomain f := by
  ext x
  simp only [mem_svDom, effectiveDomain, mem_setOf_eq]
  constructor
  · rintro ⟨α, hα⟩
    exact lt_of_le_of_lt hα (EReal.coe_lt_top α)
  · intro hx
    obtain ⟨α, hα, -⟩ := EReal.exists_between_coe_real hx
    exact ⟨α, hα.le⟩

/-- `dom Hf` is the set where `f` exceeds `-∞`. -/
theorem svDom_hypoProfile (f : E → EReal) :
    svDom (hypoProfile f) = {x | ⊥ < f x} := by
  ext x
  simp only [mem_svDom, mem_setOf_eq]
  constructor
  · rintro ⟨α, hα⟩
    exact lt_of_lt_of_le (EReal.bot_lt_coe α) hα
  · intro hx
    obtain ⟨α, -, hα⟩ := EReal.exists_between_coe_real hx
    exact ⟨α, hα.le⟩

end Definitions

section AlongFilter

variable {E : Type*}

/-- The filter-generic core of the epigraphical outer half of
**Example 5.5**: along any filter `l`, the outer limit of the profile values
lies inside the profile at `x` exactly when `f` cannot drop in the limit.

Both the absolute form of 5.5 and its form relative to a set `X` are this
statement for the filters `𝓝 x̄` and `𝓝ₓ x̄`.  Nothing in it uses a topology
on `E`, only one on the value space `IR`. -/
theorem outerSetLimitAlong_epiProfile_subset_iff (f : E → EReal) (x : E)
    (l : Filter E) :
    outerSetLimitAlong l (epiProfile f) ⊆ epiProfile f x ↔
      ∀ y, y < f x → ∀ᶠ x' in l, y < f x' := by
  constructor
  · intro h y hy
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    obtain ⟨α, hyα, hαx⟩ := EReal.exists_between_coe_real hy
    have hmem : α ∈ outerSetLimitAlong l (epiProfile f) := fun W hW ↦
      hcon.mono fun _ hx' ↦
        ⟨α, le_trans (not_lt.1 hx') hyα.le, mem_of_mem_nhds hW⟩
    exact absurd (h hmem) (not_le.2 hαx)
  · intro hlsc α hα
    by_contra hcon
    rw [mem_epiProfile, not_le] at hcon
    obtain ⟨γ, hαγ, hγ⟩ := EReal.exists_between_coe_real hcon
    obtain ⟨_, ⟨β, hβ, hβlt⟩, hx'⟩ :=
      ((hα (Iio γ) (Iio_mem_nhds (by exact_mod_cast hαγ))).and_eventually
        (hlsc (γ : EReal) hγ)).exists
    exact absurd (lt_of_le_of_lt hβ (by exact_mod_cast hβlt)) (not_lt.2 hx'.le)

/-- The filter-generic core of the epigraphical inner half of
**Example 5.5**. -/
theorem epiProfile_subset_innerSetLimitAlong_iff (f : E → EReal) (x : E)
    (l : Filter E) :
    epiProfile f x ⊆ innerSetLimitAlong l (epiProfile f) ↔
      ∀ y, f x < y → ∀ᶠ x' in l, f x' < y := by
  constructor
  · intro h y hy
    obtain ⟨α, hxα, hαy⟩ := EReal.exists_between_coe_real hy
    obtain ⟨γ, hαγ, hγy⟩ := EReal.exists_between_coe_real hαy
    have hev := h (mem_epiProfile.2 hxα.le) (Iio γ)
      (Iio_mem_nhds (by exact_mod_cast hαγ))
    filter_upwards [hev] with x' hx'
    obtain ⟨β, hβ, hβlt⟩ := hx'
    exact lt_trans (lt_of_le_of_lt hβ (by exact_mod_cast hβlt)) hγy
  · intro husc α hα W hW
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
    have hlt : f x < ((α + ε / 2 : ℝ) : EReal) :=
      lt_of_le_of_lt hα (by exact_mod_cast (by linarith : α < α + ε / 2))
    filter_upwards [husc _ hlt] with x' hx'
    refine ⟨α + ε / 2, hx'.le, hball ?_⟩
    have : dist (α + ε / 2) α < ε := by
      rw [Real.dist_eq, show α + ε / 2 - α = ε / 2 by ring,
        abs_of_pos (by linarith)]
      linarith
    exact this

/-- The filter-generic core of the hypographical outer half of
**Example 5.5**. -/
theorem outerSetLimitAlong_hypoProfile_subset_iff (f : E → EReal) (x : E)
    (l : Filter E) :
    outerSetLimitAlong l (hypoProfile f) ⊆ hypoProfile f x ↔
      ∀ y, f x < y → ∀ᶠ x' in l, f x' < y := by
  constructor
  · intro h y hy
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    obtain ⟨α, hxα, hαy⟩ := EReal.exists_between_coe_real hy
    have hmem : α ∈ outerSetLimitAlong l (hypoProfile f) := fun W hW ↦
      hcon.mono fun _ hx' ↦
        ⟨α, le_trans hαy.le (not_lt.1 hx'), mem_of_mem_nhds hW⟩
    exact absurd (h hmem) (not_le.2 hxα)
  · intro husc α hα
    by_contra hcon
    rw [mem_hypoProfile, not_le] at hcon
    obtain ⟨γ, hγ, hγα⟩ := EReal.exists_between_coe_real hcon
    obtain ⟨_, ⟨β, hβ, hβlt⟩, hx'⟩ :=
      ((hα (Ioi γ) (Ioi_mem_nhds (by exact_mod_cast hγα))).and_eventually
        (husc (γ : EReal) hγ)).exists
    exact absurd (lt_of_lt_of_le (by exact_mod_cast hβlt) hβ) (not_lt.2 hx'.le)

/-- The filter-generic core of the hypographical inner half of
**Example 5.5**. -/
theorem hypoProfile_subset_innerSetLimitAlong_iff (f : E → EReal) (x : E)
    (l : Filter E) :
    hypoProfile f x ⊆ innerSetLimitAlong l (hypoProfile f) ↔
      ∀ y, y < f x → ∀ᶠ x' in l, y < f x' := by
  constructor
  · intro h y hy
    obtain ⟨α, hyα, hαx⟩ := EReal.exists_between_coe_real hy
    obtain ⟨γ, hγα, hγ⟩ := EReal.exists_between_coe_real hyα
    have hev := h (mem_hypoProfile.2 hαx.le) (Ioi γ)
      (Ioi_mem_nhds (by exact_mod_cast hγ))
    filter_upwards [hev] with x' hx'
    obtain ⟨β, hβ, hβlt⟩ := hx'
    exact lt_of_lt_of_le hγα (le_trans (by exact_mod_cast hβlt.le) hβ)
  · intro hlsc α hα W hW
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hW
    have hlt : ((α - ε / 2 : ℝ) : EReal) < f x :=
      lt_of_lt_of_le (by exact_mod_cast (by linarith : α - ε / 2 < α)) hα
    filter_upwards [hlsc _ hlt] with x' hx'
    refine ⟨α - ε / 2, hx'.le, hball ?_⟩
    have : dist (α - ε / 2) α < ε := by
      rw [Real.dist_eq, show α - ε / 2 - α = -(ε / 2) by ring, abs_neg,
        abs_of_pos (by linarith)]
      linarith
    exact this

/-- The profile values are closed: `Ef(x)` is the preimage of `[f(x), ∞]`
under the embedding of `IR` in `IR‾`.  This is the closed-valuedness that
5.56 must supply when it appeals to 5.55. -/
theorem isClosed_epiProfile (f : E → EReal) (x : E) :
    IsClosed (epiProfile f x) :=
  isClosed_Ici.preimage continuous_coe_real_ereal

/-- The hypographical counterpart. -/
theorem isClosed_hypoProfile (f : E → EReal) (x : E) :
    IsClosed (hypoProfile f x) :=
  isClosed_Iic.preimage continuous_coe_real_ereal

end AlongFilter

section Semicontinuity

variable {E : Type*} [TopologicalSpace E]

/-- **Example 5.5**: `Ef` is outer semicontinuous at `x` exactly when `f` is
lower semicontinuous at `x`. -/
theorem svOscAt_epiProfile_iff (f : E → EReal) (x : E) :
    SvOscAt (epiProfile f) x ↔ LowerSemicontinuousAt f x :=
  outerSetLimitAlong_epiProfile_subset_iff f x _

/-- **Example 5.5** relative to a set `X`. -/
theorem svOscWithinAt_epiProfile_iff (f : E → EReal) (X : Set E) (x : E) :
    SvOscWithinAt (epiProfile f) X x ↔ LowerSemicontinuousWithinAt f X x :=
  outerSetLimitAlong_epiProfile_subset_iff f x _

/-- **Example 5.5**: `Ef` is inner semicontinuous at `x` exactly when `f` is
upper semicontinuous at `x`. -/
theorem svIscAt_epiProfile_iff (f : E → EReal) (x : E) :
    SvIscAt (epiProfile f) x ↔ UpperSemicontinuousAt f x :=
  epiProfile_subset_innerSetLimitAlong_iff f x _

/-- **Example 5.5** relative to a set `X`. -/
theorem svIscWithinAt_epiProfile_iff (f : E → EReal) (X : Set E) (x : E) :
    SvIscWithinAt (epiProfile f) X x ↔ UpperSemicontinuousWithinAt f X x :=
  epiProfile_subset_innerSetLimitAlong_iff f x _

/-- **Example 5.5**: `Ef` is continuous at `x` exactly when `f` is. -/
theorem svContinuousAt_epiProfile_iff (f : E → EReal) (x : E) :
    SvContinuousAt (epiProfile f) x ↔ ContinuousAt f x := by
  rw [SvContinuousAt, svOscAt_epiProfile_iff, svIscAt_epiProfile_iff,
    continuousAt_iff_lower_upperSemicontinuousAt]

/-- **Example 5.5** relative to a set `X`: `Ef` is continuous at `x` relative
to `X` exactly when `f` is. -/
theorem svContinuousWithinAt_epiProfile_iff (f : E → EReal) (X : Set E)
    (x : E) :
    SvContinuousWithinAt (epiProfile f) X x ↔ ContinuousWithinAt f X x := by
  rw [SvContinuousWithinAt, svOscWithinAt_epiProfile_iff,
    svIscWithinAt_epiProfile_iff,
    continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]

/-- The everywhere form: `Ef` is osc exactly when `f` is lsc. -/
theorem svOsc_epiProfile_iff (f : E → EReal) :
    SvOsc (epiProfile f) ↔ LowerSemicontinuous f :=
  forall_congr' (svOscAt_epiProfile_iff f)

/-- The everywhere form: `Ef` is isc exactly when `f` is usc. -/
theorem svIsc_epiProfile_iff (f : E → EReal) :
    SvIsc (epiProfile f) ↔ UpperSemicontinuous f :=
  forall_congr' (svIscAt_epiProfile_iff f)

/-- The form relative to `X`: `Ef` is osc relative to `X` exactly when `f` is
lsc relative to `X`. -/
theorem svOscOn_epiProfile_iff (f : E → EReal) (X : Set E) :
    SvOscOn (epiProfile f) X ↔ LowerSemicontinuousOn f X :=
  forall₂_congr fun x _ ↦ svOscWithinAt_epiProfile_iff f X x

/-- The form relative to `X`: `Ef` is isc relative to `X` exactly when `f` is
usc relative to `X`. -/
theorem svIscOn_epiProfile_iff (f : E → EReal) (X : Set E) :
    SvIscOn (epiProfile f) X ↔ UpperSemicontinuousOn f X :=
  forall₂_congr fun x _ ↦ svIscWithinAt_epiProfile_iff f X x

/-- **Example 5.5**, final clause: the level-set mapping `α ↦ lev≤α f` is osc
everywhere exactly when `f` is lsc everywhere.  It is `Ef⁻¹`, so this is
5.7(a) applied to the previous equivalence. -/
theorem svOsc_levelSet_iff (f : E → EReal) :
    SvOsc (fun α : ℝ ↦ levelSet f (α : EReal)) ↔ LowerSemicontinuous f := by
  rw [show (fun α : ℝ ↦ levelSet f (α : EReal)) = svInv (epiProfile f) from rfl,
    svOsc_svInv_iff, svOsc_epiProfile_iff]

/-- The analogue for the hypographical profile: `Hf` is osc at `x` exactly
when `f` is usc at `x`. -/
theorem svOscAt_hypoProfile_iff (f : E → EReal) (x : E) :
    SvOscAt (hypoProfile f) x ↔ UpperSemicontinuousAt f x :=
  outerSetLimitAlong_hypoProfile_subset_iff f x _

/-- The hypographical analogue relative to a set `X`. -/
theorem svOscWithinAt_hypoProfile_iff (f : E → EReal) (X : Set E) (x : E) :
    SvOscWithinAt (hypoProfile f) X x ↔ UpperSemicontinuousWithinAt f X x :=
  outerSetLimitAlong_hypoProfile_subset_iff f x _

/-- The analogue for the hypographical profile: `Hf` is isc at `x` exactly
when `f` is lsc at `x`. -/
theorem svIscAt_hypoProfile_iff (f : E → EReal) (x : E) :
    SvIscAt (hypoProfile f) x ↔ LowerSemicontinuousAt f x :=
  hypoProfile_subset_innerSetLimitAlong_iff f x _

/-- The hypographical analogue relative to a set `X`. -/
theorem svIscWithinAt_hypoProfile_iff (f : E → EReal) (X : Set E) (x : E) :
    SvIscWithinAt (hypoProfile f) X x ↔ LowerSemicontinuousWithinAt f X x :=
  hypoProfile_subset_innerSetLimitAlong_iff f x _

end Semicontinuity

end RW
