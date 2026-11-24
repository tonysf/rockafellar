/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Monotone composition of normal integrands

Proposition 14.45(b) of Rockafellar–Wets: `f(t, x) = θ(t, g(t, x))` for normal integrands `g`
and `θ : T × ℝ → ℝ̄` with `θ(t, ·)` nondecreasing, under the conventions
`θ(t, ∞) = sup θ(t, ·)` and `θ(t, -∞) = inf θ(t, ·)`.

The printed proof writes `S_f(t) = M(t, S_g(t))`, which fails when `sup θ(t, ·) < ∞` and `g`
takes the value `∞` (points with `g(t, x) = ∞` then lie in `dom f(t, ·)`).  The statement is proved
here through the level sets 14.33: `{x | f(t, x) ≤ β} = {x | g(t, x) ≤ a*(t)}` with
`a*(t) = sup {α | θ(t, α) ≤ β}` when `inf θ(t, ·) ≤ β`, and `= ∅` otherwise.
-/

import RockafellarWets.Chapter14.IntegrandSums

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Classical

noncomputable section

namespace RW

/-- The extension of `θ : ℝ → ℝ̄` to `ℝ̄` by `θ(∞) = sup θ` and `θ(-∞) = inf θ`. -/
def monotoneExtension (θ : ℝ → EReal) (a : EReal) : EReal :=
  if a = ⊥ then ⨅ α, θ α else if a = ⊤ then ⨆ α, θ α else θ a.toReal

section Lemmas

variable {θ : ℝ → EReal}

/-- The upper end `a* = sup {α | θ(α) ≤ β}` of the sublevel set. -/
def sublevelSup (θ : ℝ → EReal) (β : ℝ) : EReal := ⨆ α ∈ {α : ℝ | θ α ≤ β}, (α : EReal)

theorem coe_le_sublevelSup_iff (hl : LowerSemicontinuous θ) (hm : Monotone θ) (β c : ℝ) :
    (c : EReal) ≤ sublevelSup θ β ↔ θ c ≤ β := by
  constructor
  · intro hc
    by_contra hθc
    push_neg at hθc
    have hK : IsClosed {α : ℝ | θ α ≤ β} := hl.isClosed_preimage _
    have hbelow : ∀ k ∈ {α : ℝ | θ α ≤ β}, k ≤ c := fun k hk ↦ by
      by_contra hkc
      push_neg at hkc
      exact absurd ((hm hkc.le).trans hk) (not_le.2 hθc)
    have hseq : ∀ n : ℕ, ∃ k ∈ {α : ℝ | θ α ≤ β}, c - 1 / ((n : ℝ) + 1) < k := by
      intro n
      have hlt : ((c - 1 / ((n : ℝ) + 1) : ℝ) : EReal) < sublevelSup θ β :=
        lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith)) hc
      obtain ⟨k, hk⟩ := lt_iSup_iff.1 hlt
      obtain ⟨hkK, hkc⟩ := lt_iSup_iff.1 hk
      exact ⟨k, hkK, EReal.coe_lt_coe_iff.1 hkc⟩
    choose k hkK hkc using hseq
    have hkt : Tendsto k atTop (𝓝 c) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
        (fun n ↦ (hkc n).le) (fun n ↦ hbelow _ (hkK n))
      have := (tendsto_const_nhds (x := c)).sub tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [sub_zero] at this
    exact absurd (hK.mem_of_tendsto hkt (Eventually.of_forall hkK)) (not_le.2 hθc)
  · intro h
    exact le_iSup₂ (f := fun α (_ : α ∈ {α : ℝ | θ α ≤ β}) ↦ (α : EReal)) c h

theorem iInf_le_monotoneExtension (θ : ℝ → EReal) (a : EReal) :
    (⨅ α, θ α) ≤ monotoneExtension θ a := by
  unfold monotoneExtension
  split_ifs
  · exact le_rfl
  · exact iInf_le_iSup
  · exact iInf_le _ _

theorem monotoneExtension_le_iff (hl : LowerSemicontinuous θ) (hm : Monotone θ) {β : ℝ}
    (hinf : (⨅ α, θ α) ≤ β) (a : EReal) :
    monotoneExtension θ a ≤ β ↔ a ≤ sublevelSup θ β := by
  unfold monotoneExtension
  split_ifs with hbot htop
  · simp [hbot, hinf]
  · subst htop
    rw [top_le_iff, EReal.eq_top_iff_forall_lt, iSup_le_iff]
    constructor
    · intro h y
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one y))
        ((coe_le_sublevelSup_iff hl hm β (y + 1)).2 (h _))
    · intro h α
      exact (coe_le_sublevelSup_iff hl hm β α).1 (h α).le
  · rw [← coe_le_sublevelSup_iff hl hm, EReal.coe_toReal htop hbot]

theorem monotoneExtension_le_iff_of_lt (θ : ℝ → EReal) {β : ℝ} (hinf : (β : EReal) < ⨅ α, θ α)
    (a : EReal) : monotoneExtension θ a ≤ β ↔ False :=
  ⟨fun h ↦ absurd (hinf.trans_le (iInf_le_monotoneExtension θ a)) (not_lt.2 h), False.elim⟩

theorem iInf_eq_iInf_nat_of_monotone (hm : Monotone θ) :
    (⨅ α, θ α) = ⨅ n : ℕ, θ (-(n : ℝ)) := by
  refine le_antisymm (le_iInf fun n ↦ iInf_le _ _) (le_iInf fun α ↦ ?_)
  obtain ⟨n, hn⟩ := exists_nat_ge (-α)
  exact (iInf_le _ n).trans (hm (by linarith))

end Lemmas

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Proposition 14.45(b)**: `f(t, x) = θ(t, g(t, x))` is a normal integrand for normal
integrands `g` and `θ` with `θ(t, ·)` nondecreasing, with `θ(t, ±∞)` the supremum/infimum
of `θ(t, ·)`. -/
theorem IsNormalIntegrand.monotoneExtension_comp {g : T → E → EReal}
    (hg : IsNormalIntegrand g) {θ : T → ℝ → EReal} (hθ : IsNormalIntegrand θ)
    (hmono : ∀ t, Monotone (θ t)) :
    IsNormalIntegrand (fun t x ↦ monotoneExtension (θ t) (g t x)) := by
  refine measurability_of_level_set_mappings.2 fun β ↦ ?_
  have hl : ∀ t, LowerSemicontinuous (θ t) := hθ.lowerSemicontinuous
  set a : T → EReal := fun t ↦ sublevelSup (θ t) β with hadef
  have ham : Measurable a := by
    refine measurable_ereal_of_lt_coe fun c ↦ ?_
    have : {t | a t < c} = {t | θ t c ≤ β}ᶜ := by
      ext t
      simp only [mem_setOf_eq, mem_compl_iff, ← not_le, hadef]
      rw [coe_le_sublevelSup_iff (hl t) (hmono t)]
    rw [this]
    exact (measurableSet_le (hθ.measurable_apply c) measurable_const).compl
  have hT₁ : MeasurableSet {t | (⨅ α, θ t α) ≤ β} := by
    have : {t | (⨅ α, θ t α) ≤ β} = {t | (⨅ n : ℕ, θ t (-(n : ℝ))) ≤ β} := by
      ext t
      rw [mem_setOf_eq, mem_setOf_eq, iInf_eq_iInf_nat_of_monotone (hmono t)]
    rw [this]
    exact measurableSet_le (Measurable.iInf fun n ↦ hθ.measurable_apply _) measurable_const
  obtain ⟨hLc, hLm⟩ := hg.levelSet_measurable_ereal ham
  have key := SvMeasurable.ite hT₁ hLm (svMeasurable_const (∅ : Set E))
  have hset : ∀ t, {x | monotoneExtension (θ t) (g t x) ≤ β} =
      if t ∈ {t | (⨅ α, θ t α) ≤ β} then {x | g t x ≤ a t} else ∅ := by
    intro t
    split_ifs with h
    · ext x
      exact monotoneExtension_le_iff (hl t) (hmono t) h (g t x)
    · ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun hx ↦ (monotoneExtension_le_iff_of_lt (θ t) (not_le.1 h) (g t x)).1 hx
  refine ⟨fun t ↦ ?_, ?_⟩
  · rw [hset t]
    split_ifs
    · exact hLc t
    · exact isClosed_empty
  · rw [funext hset]
    convert key using 2 with t
    congr 1

end RW
