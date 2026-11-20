/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: The sequential reading of epi-derivatives

The display after Definition 7.23: the epi-derivative `β` of `f` at `x̄` for
`w` is a value such that for all sequences `τν ↓ 0`

* `liminf_ν [f(x̄ + τν wν) - f(x̄)]/τν ≥ β` for every sequence `wν → w`, and
* `limsup_ν [f(x̄ + τν wν) - f(x̄)]/τν ≤ β` for some sequence `wν → w`.

`hasEpiDerivative_iff_forall_seq` shows that the definition through the
epigraphical limits along `τ ↓ 0` (formulas 7(10)–7(11), `HasEpiDerivative`)
is equivalent to asking, for every sequence `τν ↓ 0`, that the sequential
lower and upper epi-limits of Definition 7.1 (`epiLowerLimit`,
`epiUpperLimit`) both equal `β` at `w`; `hasEpiDerivative_iff_liminf_limsup`
then reads this through 7(3) (`epiLimits_eq_at_iff_liminf_limsup`) as the
printed display.  The comparison rests on two facts about set limits along the
countably generated filter `𝓝[>] 0`: outer limits along a sequence `τν ↓ 0`
are contained in the outer limit along the filter, and every point of the
latter is in the outer limit along some such sequence; dually for inner
limits.
-/

import RockafellarWets.Chapter7.EpiDerivatives
import RockafellarWets.Chapter7.EpiLimitCharacterization

open Filter Set Topology Metric

namespace RW

/-! ### Set limits along a filter versus along sequences -/

section SetLimitsSequences

variable {ι X : Type*} [TopologicalSpace X] {l : Filter ι} {S : ι → Set X}

theorem outerSetLimit_comp_subset_outerSetLimitAlong {xs : ℕ → ι} (hxs : Tendsto xs atTop l) :
    outerSetLimit (fun n ↦ S (xs n)) ⊆ outerSetLimitAlong l S := by
  intro p hp V hV
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨n, hnV, hnU⟩ := ((hp V hV).and_eventually (hxs.eventually hU)).exists
  exact ⟨xs n, hnU, hnV⟩

theorem innerSetLimitAlong_subset_innerSetLimit_of_tendsto {xs : ℕ → ι} (hxs : Tendsto xs atTop l) :
    innerSetLimitAlong l S ⊆ innerSetLimit (fun n ↦ S (xs n)) :=
  fun _ hp V hV ↦ hxs.eventually (hp V hV)

variable [FirstCountableTopology X] [l.IsCountablyGenerated]

/-- A point of the outer limit along `l` is in the inner limit along some
sequence tending to `l` inside a prescribed member `T` of `l`. -/
theorem exists_seq_mem_innerSetLimit_of_mem_outerSetLimitAlong {p : X}
    (hp : p ∈ outerSetLimitAlong l S) {T : Set ι} (hT : T ∈ l) :
    ∃ xs : ℕ → ι, (∀ n, xs n ∈ T) ∧ Tendsto xs atTop l ∧ p ∈ innerSetLimit (fun n ↦ S (xs n)) := by
  obtain ⟨U, hU⟩ := l.exists_antitone_basis
  obtain ⟨V, hV⟩ := (𝓝 p).exists_antitone_basis
  have hpick : ∀ n, ∃ i ∈ U n ∩ T, (S i ∩ V n).Nonempty := fun n ↦
    Filter.frequently_iff.1 (hp (V n) (hV.mem n)) (inter_mem (hU.mem n) hT)
  choose xs hxs hxsS using hpick
  refine ⟨xs, fun n ↦ (hxs n).2, hU.tendsto fun n ↦ (hxs n).1, fun W hW ↦ ?_⟩
  obtain ⟨k, hk⟩ := hV.toHasBasis.mem_iff.1 hW
  filter_upwards [eventually_ge_atTop k] with n hn
  obtain ⟨q, hqS, hqV⟩ := hxsS n
  exact ⟨q, hqS, hk.2 (hV.antitone hn hqV)⟩

omit [FirstCountableTopology X] in
/-- A point outside the inner limit along `l` is outside the outer limit
along some sequence tending to `l` inside a prescribed member `T` of `l`. -/
theorem exists_seq_not_mem_outerSetLimit_of_not_mem_innerSetLimitAlong {p : X}
    (hp : p ∉ innerSetLimitAlong l S) {T : Set ι} (hT : T ∈ l) :
    ∃ xs : ℕ → ι, (∀ n, xs n ∈ T) ∧ Tendsto xs atTop l ∧ p ∉ outerSetLimit (fun n ↦ S (xs n)) := by
  simp only [mem_innerSetLimitAlong, not_forall, Filter.not_eventually, exists_prop] at hp
  obtain ⟨V, hV, hfreq⟩ := hp
  obtain ⟨U, hU⟩ := l.exists_antitone_basis
  have hpick : ∀ n, ∃ i ∈ U n ∩ T, ¬(S i ∩ V).Nonempty := fun n ↦
    Filter.frequently_iff.1 hfreq (inter_mem (hU.mem n) hT)
  choose xs hxs hxsS using hpick
  refine ⟨xs, fun n ↦ (hxs n).2, hU.tendsto fun n ↦ (hxs n).1, fun hmem ↦ ?_⟩
  obtain ⟨n, hn⟩ := (hmem V hV).exists
  exact hxsS n hn

end SetLimitsSequences

/-! ### The display after Definition 7.23 -/

section EpiDerivativeSequences

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem le_of_forall_real_le_imp {a b : EReal} (h : ∀ α : ℝ, b ≤ α → a ≤ α) : a ≤ b := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨α, h1, h2⟩ := EReal.exists_between_coe_real hlt
  exact absurd (h α h1.le) (not_le.2 h2)

theorem le_of_forall_real_lt_imp {a b : EReal} (h : ∀ α : ℝ, b < α → a ≤ α) : a ≤ b := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨α, h1, h2⟩ := EReal.exists_between_coe_real hlt
  exact absurd (h α h1) (not_le.2 h2)

theorem tendsto_nhdsGT_of_pos {τs : ℕ → ℝ} (hτ : ∀ n, 0 < τs n) (hτ0 : Tendsto τs atTop (𝓝 0)) :
    Tendsto τs atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ0 (Eventually.of_forall hτ)

/-- The display after **Definition 7.23**, in terms of Definition 7.1: `β` is
the epi-derivative of `f` at `x̄` for `w` exactly when, along every sequence
`τν ↓ 0`, the lower and upper epi-limits of the difference quotients at `w`
are both `β`. -/
theorem hasEpiDerivative_iff_forall_seq {f : E → EReal} {x w : E} {β : EReal} :
    HasEpiDerivative f x w β ↔ f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∀ τs : ℕ → ℝ, (∀ n, 0 < τs n) →
      Tendsto τs atTop (𝓝 0) →
        epiLowerLimit (fun n ↦ differenceQuotient f x (τs n)) w = β ∧
          epiUpperLimit (fun n ↦ differenceQuotient f x (τs n)) w = β := by
  -- values at `w` read through epigraph membership
  have hlowS : ∀ (τs : ℕ → ℝ) (α : ℝ),
      epiLowerLimit (fun n ↦ differenceQuotient f x (τs n)) w ≤ α ↔
        (w, α) ∈ outerSetLimit (fun n ↦ epigraph (differenceQuotient f x (τs n))) := by
    intro τs α
    rw [← epigraph_epiLowerLimit, mem_epigraph_iff]
  have hupS : ∀ (τs : ℕ → ℝ) (α : ℝ),
      epiUpperLimit (fun n ↦ differenceQuotient f x (τs n)) w ≤ α ↔
        (w, α) ∈ innerSetLimit (fun n ↦ epigraph (differenceQuotient f x (τs n))) := by
    intro τs α
    rw [← epigraph_epiUpperLimit, mem_epigraph_iff]
  have hlowF : ∀ α : ℝ, lowerEpiDerivative f x w ≤ α ↔
      (w, α) ∈ outerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (differenceQuotient f x τ)) := by
    intro α
    rw [← epigraph_lowerEpiDerivative, mem_epigraph_iff]
  have hupF : ∀ α : ℝ, upperEpiDerivative f x w ≤ α ↔
      (w, α) ∈ innerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun τ ↦ epigraph (differenceQuotient f x τ)) := by
    intro α
    rw [← epigraph_upperEpiDerivative, mem_epigraph_iff]
  constructor
  · rintro ⟨hx, hx', hl, hu⟩
    refine ⟨hx, hx', fun τs hτ hτ0 ↦ ?_⟩
    have hτF := tendsto_nhdsGT_of_pos hτ hτ0
    have h1 : lowerEpiDerivative f x w ≤ epiLowerLimit (fun n ↦ differenceQuotient f x (τs n)) w :=
      le_of_forall_real_le_imp fun α hα ↦ (hlowF α).2
        (outerSetLimit_comp_subset_outerSetLimitAlong hτF ((hlowS τs α).1 hα))
    have h2 : epiUpperLimit (fun n ↦ differenceQuotient f x (τs n)) w ≤ upperEpiDerivative f x w :=
      le_of_forall_real_le_imp fun α hα ↦ (hupS τs α).2
        (innerSetLimitAlong_subset_innerSetLimit_of_tendsto hτF ((hupF α).1 hα))
    have h3 := epiLowerLimit_le_epiUpperLimit (fun n ↦ differenceQuotient f x (τs n)) w
    rw [hl] at h1
    rw [hu] at h2
    exact ⟨le_antisymm (h3.trans h2) h1, le_antisymm h2 (h1.trans h3)⟩
  · rintro ⟨hx, hx', hall⟩
    have hT : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
    -- a fixed sequence `τν ↓ 0`
    have hτ₀ : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n ↦ by positivity
    obtain ⟨hl₀, hu₀⟩ := hall _ hτ₀ tendsto_one_div_add_atTop_nhds_zero_nat
    have hτF₀ := tendsto_nhdsGT_of_pos hτ₀ tendsto_one_div_add_atTop_nhds_zero_nat
    -- lower value
    have hlow_le : lowerEpiDerivative f x w ≤ β := by
      rw [← hl₀]
      exact le_of_forall_real_le_imp fun α hα ↦ (hlowF α).2
        (outerSetLimit_comp_subset_outerSetLimitAlong hτF₀ ((hlowS _ α).1 hα))
    have hlow_ge : β ≤ lowerEpiDerivative f x w := by
      refine le_of_forall_real_le_imp fun α hα ↦ ?_
      obtain ⟨τs, hτs, hτsF, hmem⟩ :=
        exists_seq_mem_innerSetLimit_of_mem_outerSetLimitAlong ((hlowF α).1 hα) hT
      have hτs0 : Tendsto τs atTop (𝓝 0) := hτsF.mono_right nhdsWithin_le_nhds
      obtain ⟨hl, -⟩ := hall τs hτs hτs0
      rw [← hl]
      exact (hlowS τs α).2 (innerSetLimit_subset_outerSetLimit _ hmem)
    have hlow : lowerEpiDerivative f x w = β := le_antisymm hlow_le hlow_ge
    -- upper value
    have hup_le : upperEpiDerivative f x w ≤ β := by
      refine le_of_forall_real_lt_imp fun α hα ↦ ?_
      by_contra hnot
      obtain ⟨τs, hτs, hτsF, hnotmem⟩ :=
        exists_seq_not_mem_outerSetLimit_of_not_mem_innerSetLimitAlong
          (fun hmem ↦ hnot ((hupF α).2 hmem)) hT
      have hτs0 : Tendsto τs atTop (𝓝 0) := hτsF.mono_right nhdsWithin_le_nhds
      obtain ⟨-, hu⟩ := hall τs hτs hτs0
      have hle : epiUpperLimit (fun n ↦ differenceQuotient f x (τs n)) w ≤ α := by
        rw [hu]
        exact hα.le
      exact hnotmem (innerSetLimit_subset_outerSetLimit _ ((hupS τs α).1 hle))
    exact ⟨hx, hx', hlow, le_antisymm hup_le
      (hlow ▸ lowerEpiDerivative_le_upperEpiDerivative f x w)⟩

/-- The display after **Definition 7.23**, as printed: `β` is the
epi-derivative of `f` at `x̄` for `w` exactly when for all sequences `τν ↓ 0`
the quotients satisfy `liminf ≥ β` along every `wν → w` and `limsup ≤ β` along
some `wν → w`. -/
theorem hasEpiDerivative_iff_liminf_limsup {f : E → EReal} {x w : E} {β : EReal} :
    HasEpiDerivative f x w β ↔ f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∀ τs : ℕ → ℝ, (∀ n, 0 < τs n) →
      Tendsto τs atTop (𝓝 0) →
        (∀ ws : ℕ → E, Tendsto ws atTop (𝓝 w) →
          β ≤ liminf (fun n ↦ differenceQuotient f x (τs n) (ws n)) atTop) ∧
        (∃ ws : ℕ → E, Tendsto ws atTop (𝓝 w) ∧
          limsup (fun n ↦ differenceQuotient f x (τs n) (ws n)) atTop ≤ β) := by
  rw [hasEpiDerivative_iff_forall_seq]
  simp only [epiLimits_eq_at_iff_liminf_limsup]

end EpiDerivativeSequences

end RW
