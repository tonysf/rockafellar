/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Function-value characterizations of epi-limits

Proposition 7.2 expresses each epi-limit as an attained minimum over sequences
of arguments. Real levels strictly above a proposed value give neighborhood
tests valid even at either infinity. For attainment we allow extended heights
during selection, so selecting a sequence at height −∞ needs no separate
diagonal argument.
-/
import RockafellarWets.Chapter7.EpiLimits
import RockafellarWets.Chapter5.GraphicalLimitFormulas
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.Uniformity

open Filter Set Topology

namespace RW

section Neighborhoods

variable {E : Type*} [TopologicalSpace E] {f : ℕ → E → EReal}

/-- A real height above a proposed value tests both types of epi-limit using
only function values. Here `P` stands for frequent or eventual occurrence. -/
private theorem le_iff_level_hits
    (P : (ℕ → Prop) → Prop) (hmono : ∀ {p q}, (∀ n, p n → q n) → P p → P q)
    {g : E → EReal} (hg : ∀ x (c : ℝ), g x ≤ c ↔
      ∀ W ∈ 𝓝 (x, c), P (fun n ↦ (epigraph (f n) ∩ W).Nonempty))
    (x : E) (a : EReal) :
    g x ≤ a ↔ ∀ U ∈ 𝓝 x, ∀ b : ℝ, a < b → P (fun n ↦ ∃ y ∈ U, f n y ≤ b) := by
  constructor
  · intro h U hU b hb
    obtain ⟨c, hac, hcb⟩ := EReal.exists_between_coe_real hb
    have hcb' : c < b := EReal.coe_lt_coe_iff.1 hcb
    apply hmono _ ((hg x c).1 (h.trans hac.le) (U ×ˢ Iio b)
      (prod_mem_nhds hU (Iio_mem_nhds hcb')))
    rintro n ⟨⟨y, t⟩, ht, hy, htb⟩
    exact ⟨y, hy, ht.trans (EReal.coe_le_coe_iff.2 (le_of_lt htb))⟩
  · intro h
    by_contra! hbad
    obtain ⟨c, hac, hcg⟩ := EReal.exists_between_coe_real hbad
    apply hcg.not_ge
    apply (hg x c).2
    intro W hW
    obtain ⟨U, hU, V, hV, hsub⟩ := mem_nhds_prod_iff.1 hW
    apply hmono _ (h U hU c hac)
    rintro n ⟨y, hy, hfy⟩
    exact ⟨(y, c), hfy, hsub ⟨hy, mem_of_mem_nhds hV⟩⟩

theorem epiLowerLimit_le_iff_frequently (f : ℕ → E → EReal) (x : E) (a : EReal) :
    epiLowerLimit f x ≤ a ↔ ∀ U ∈ 𝓝 x, ∀ b : ℝ, a < b →
      ∃ᶠ n in atTop, ∃ y ∈ U, f n y ≤ b := by
  apply le_iff_level_hits (fun p ↦ ∃ᶠ n in atTop, p n) (fun h h' ↦ h'.mono h)
  intro z c
  change (z, c) ∈ epigraph (epiLowerLimit f) ↔ _
  rw [epigraph_epiLowerLimit]
  rfl

theorem epiUpperLimit_le_iff_eventually (f : ℕ → E → EReal) (x : E) (a : EReal) :
    epiUpperLimit f x ≤ a ↔ ∀ U ∈ 𝓝 x, ∀ b : ℝ, a < b →
      ∀ᶠ n in atTop, ∃ y ∈ U, f n y ≤ b := by
  apply le_iff_level_hits (fun p ↦ ∀ᶠ n in atTop, p n) (fun h h' ↦ h'.mono h)
  intro z c
  change (z, c) ∈ epigraph (epiUpperLimit f) ↔ _
  rw [epigraph_epiUpperLimit]
  rfl

/-- Passing to extended heights retains an actual point at the lower end of
every limiting epigraph fiber, including fibers with endpoint ±∞. -/
private theorem extended_epigraph_hits (P : (ℕ → Prop) → Prop)
    (hmono : ∀ {p q}, (∀ n, p n → q n) → P p → P q)
    (hall : ∀ {p}, (∀ n, p n) → P p) {x : E} {a : EReal}
    (hhit : ∀ U ∈ 𝓝 x, ∀ b : ℝ, a < b → P (fun n ↦ ∃ y ∈ U, f n y ≤ b)) :
    ∀ W ∈ 𝓝 (x, a), P (fun n ↦ ({p : E × EReal | f n p.1 ≤ p.2} ∩ W).Nonempty) := by
  intro W hW
  obtain ⟨U, hU, V, hV, hsub⟩ := mem_nhds_prod_iff.1 hW
  by_cases ha : a = ⊤
  · subst a
    exact hall fun n ↦ ⟨(x, ⊤), (show f n x ≤ ⊤ from le_top),
      hsub ⟨mem_of_mem_nhds hU, mem_of_mem_nhds hV⟩⟩
  have hcl : a ∈ closure (Ioi a) := by
    rw [closure_Ioi' ⟨⊤, lt_top_iff_ne_top.2 ha⟩]
    exact (show a ≤ a from le_rfl)
  obtain ⟨t, htV, hat⟩ := mem_closure_iff_nhds.1 hcl V hV
  obtain ⟨b, hab, hbt⟩ := EReal.exists_between_coe_real hat
  apply hmono _ (hhit U hU b hab)
  rintro n ⟨y, hyU, hfy⟩
  exact ⟨(y, t), hfy.trans hbt.le, hsub ⟨hyU, htV⟩⟩

/-- Lower epi-limit bound along an arbitrary convergent subsequence of arguments. -/
theorem epiLowerLimit_le_liminf_subsequence {x : E} {φ : ℕ → ℕ} {y : ℕ → E}
    (hφ : StrictMono φ) (hy : Tendsto y atTop (𝓝 x)) :
    epiLowerLimit f x ≤ liminf (fun n ↦ f (φ n) (y n)) atTop := by
  apply (epiLowerLimit_le_iff_frequently ..).2
  intro U hU b hb
  have hhit := (frequently_lt_of_liminf_lt (u := fun n ↦ f (φ n) (y n)) (h := hb))
  apply Frequently.filter_mono _ hφ.tendsto_atTop
  apply (frequently_map (m := φ)).2
  exact (hhit.and_eventually (hy hU)).mono fun n ⟨hn, hUn⟩ ↦ ⟨y n, hUn, hn.le⟩

theorem epiLowerLimit_le_liminf {x : E} {y : ℕ → E} (hy : Tendsto y atTop (𝓝 x)) :
    epiLowerLimit f x ≤ liminf (fun n ↦ f n (y n)) atTop :=
  epiLowerLimit_le_liminf_subsequence strictMono_id hy

theorem epiUpperLimit_le_limsup {x : E} {y : ℕ → E} (hy : Tendsto y atTop (𝓝 x)) :
    epiUpperLimit f x ≤ limsup (fun n ↦ f n (y n)) atTop := by
  apply (epiUpperLimit_le_iff_eventually ..).2
  intro U hU b hb
  filter_upwards [hy hU, eventually_lt_of_limsup_lt hb] with n hn hfn
  exact ⟨y n, hn, hfn.le⟩

end Neighborhoods

section Sequences

variable {E : Type*} [PseudoMetricSpace E]

/-- The lower epi-limit has a minimizing sequence of arguments (Proposition 7.2). -/
theorem exists_tendsto_liminf_eq_epiLowerLimit (f : ℕ → E → EReal) (x : E) :
    ∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧
      liminf (fun n ↦ f n (y n)) atTop = epiLowerLimit f x := by
  letI : MetricSpace EReal := TopologicalSpace.metrizableSpaceMetric EReal
  have hh : (x, epiLowerLimit f x) ∈ outerSetLimit
      (fun n ↦ {p : E × EReal | f n p.1 ≤ p.2}) :=
    extended_epigraph_hits (fun p ↦ ∃ᶠ n in atTop, p n) (fun h h' ↦ h'.mono h)
      (fun h ↦ Frequently.of_forall h) ((epiLowerLimit_le_iff_frequently ..).1 le_rfl)
  obtain ⟨φ, p, hφ, hp, hlim⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hh
  rw [nhds_prod_eq] at hlim
  let y := Function.extend φ (fun k ↦ (p k).1) (fun _ ↦ x)
  have hy : Tendsto y atTop (𝓝 x) := tendsto_extend_of_strictMono hφ hlim.fst
  refine ⟨y, hy, le_antisymm ?_ (epiLowerLimit_le_liminf hy)⟩
  rw [liminf_le_iff]
  intro b hb
  apply Frequently.filter_mono _ hφ.tendsto_atTop
  apply (frequently_map (m := φ)).2
  apply (hlim.snd.eventually_lt_const hb).frequently.mono
  intro k hk
  dsimp only [y]
  rw [hφ.injective.extend_apply]
  exact lt_of_le_of_lt (hp k) hk

/-- The upper epi-limit has a recovery sequence (Proposition 7.2). -/
theorem exists_tendsto_limsup_eq_epiUpperLimit (f : ℕ → E → EReal) (x : E) :
    ∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧
      limsup (fun n ↦ f n (y n)) atTop = epiUpperLimit f x := by
  letI : MetricSpace EReal := TopologicalSpace.metrizableSpaceMetric EReal
  have hh : (x, epiUpperLimit f x) ∈ innerSetLimit
      (fun n ↦ {p : E × EReal | f n p.1 ≤ p.2}) :=
    extended_epigraph_hits (fun p ↦ ∀ᶠ n in atTop, p n) (fun h h' ↦ h'.mono h)
      (fun h ↦ Eventually.of_forall h) ((epiUpperLimit_le_iff_eventually ..).1 le_rfl)
  obtain ⟨p, hp, hlim⟩ := mem_innerSetLimit_iff_exists_seq.1 hh
  rw [nhds_prod_eq] at hlim
  refine ⟨fun n ↦ (p n).1, hlim.fst, le_antisymm ?_ (epiUpperLimit_le_limsup hlim.fst)⟩
  have hle : (fun n ↦ f n (p n).1) ≤ᶠ[atTop] (fun n ↦ (p n).2) := hp
  exact (limsup_le_limsup hle).trans_eq hlim.snd.limsup_eq

/-- **Proposition 7.2**, the attained minimum formula for the lower epi-limit. -/
theorem isLeast_liminf_of_tendsto_epiLowerLimit (f : ℕ → E → EReal) (x : E) :
    IsLeast {a | ∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧
      liminf (fun n ↦ f n (y n)) atTop = a} (epiLowerLimit f x) :=
  ⟨exists_tendsto_liminf_eq_epiLowerLimit f x,
    fun _ ⟨_, hy, heq⟩ ↦ heq ▸ epiLowerLimit_le_liminf hy⟩

/-- **Proposition 7.2**, the attained minimum formula for the upper epi-limit. -/
theorem isLeast_limsup_of_tendsto_epiUpperLimit (f : ℕ → E → EReal) (x : E) :
    IsLeast {a | ∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧
      limsup (fun n ↦ f n (y n)) atTop = a} (epiUpperLimit f x) :=
  ⟨exists_tendsto_limsup_eq_epiUpperLimit f x,
    fun _ ⟨_, hy, heq⟩ ↦ heq ▸ epiUpperLimit_le_limsup hy⟩

/-- Equation 7(3) at a point, including infinite values. -/
theorem epiLimits_eq_at_iff_liminf_limsup {f : ℕ → E → EReal} {x : E} {a : EReal} :
    epiLowerLimit f x = a ∧ epiUpperLimit f x = a ↔
      (∀ y : ℕ → E, Tendsto y atTop (𝓝 x) → a ≤ liminf (fun n ↦ f n (y n)) atTop) ∧
      (∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧ limsup (fun n ↦ f n (y n)) atTop ≤ a) := by
  constructor
  · rintro ⟨hl, hu⟩
    obtain ⟨y, hy, hval⟩ := exists_tendsto_limsup_eq_epiUpperLimit f x
    exact ⟨fun _ hz ↦ hl ▸ epiLowerLimit_le_liminf hz, y, hy, (hval.trans hu).le⟩
  · rintro ⟨hlo, y, hy, hyval⟩
    obtain ⟨z, hz, hval⟩ := exists_tendsto_liminf_eq_epiLowerLimit f x
    have hl := (hlo z hz).trans_eq hval
    have hu := (epiUpperLimit_le_limsup hy).trans hyval
    have hlu := epiLowerLimit_le_epiUpperLimit f x
    exact ⟨le_antisymm (hlu.trans hu) hl, le_antisymm hu (hl.trans hlu)⟩

/-- **Proposition 7.2**, the lower inequality and recovery-sequence
criterion for epi-convergence. -/
theorem epiConverges_iff_liminf_limsup {f : ℕ → E → EReal} {g : E → EReal} :
    EpiConverges f g ↔ ∀ x,
      (∀ y : ℕ → E, Tendsto y atTop (𝓝 x) → g x ≤ liminf (fun n ↦ f n (y n)) atTop) ∧
      (∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧ limsup (fun n ↦ f n (y n)) atTop ≤ g x) := by
  simp_rw [← epiLimits_eq_at_iff_liminf_limsup, epiConverges_iff_epiLimits_eq,
    funext_iff, forall_and]

/-- Along a recovery sequence the function values converge to the epi-limit. -/
theorem EpiConverges.exists_tendsto_values {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (x : E) :
    ∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧ Tendsto (fun n ↦ f n (y n)) atTop (𝓝 (g x)) := by
  obtain ⟨hlo, y, hy, hhi⟩ := epiConverges_iff_liminf_limsup.1 h x
  exact ⟨y, hy, tendsto_of_le_liminf_of_limsup_le (hlo y hy) hhi⟩

end Sequences

end RW
