/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epigraphical limits and minimization on test sets

Proposition 7.29 expresses the outer and inner epigraph inclusions using
infima over compact and open test sets. Real heights suffice even when one
of the infima is infinite.
-/

import RockafellarWets.Chapter4.HitAndMiss
import RockafellarWets.Chapter1.Semicontinuity

open Filter Metric Set Topology

namespace RW

variable {E : Type*}

/-- Infimum over a test set. In particular, the infimum over the empty set is `⊤`. -/
noncomputable def infimumOn (f : E → EReal) (B : Set E) : EReal := ⨅ x ∈ B, f x

theorem infimumOn_le {f : E → EReal} {B : Set E} {x : E} (hx : x ∈ B) :
    infimumOn f B ≤ f x := iInf₂_le x hx

theorem le_infimumOn {f : E → EReal} {B : Set E} {a : EReal}
    (h : ∀ x ∈ B, a ≤ f x) : a ≤ infimumOn f B := le_iInf₂ h

theorem infimumOn_lt_iff {f : E → EReal} {B : Set E} {a : EReal} :
    infimumOn f B < a ↔ ∃ x ∈ B, f x < a := by simp [infimumOn, iInf_lt_iff]

@[simp] theorem infimumOn_univ (f : E → EReal) : infimumOn f univ = ⨅ x, f x := by
  simp [infimumOn]

/-- **Proposition 7.29(a)** in epigraph form. -/
theorem epigraph_outerSetLimit_subset_iff_infimumOn_compact
    [PseudoMetricSpace E] [ProperSpace E]
    {f : ℕ → E → EReal} {g : E → EReal} (hg : LowerSemicontinuous g) :
    outerSetLimit (fun n ↦ epigraph (f n)) ⊆ epigraph g ↔
      ∀ B : Set E, IsCompact B →
        infimumOn g B ≤ liminf (fun n ↦ infimumOn (f n) B) atTop := by
  constructor
  · intro h B hB
    by_contra! hbad
    obtain ⟨a, ha, hag⟩ := EReal.exists_between_coe_real hbad
    have hdis : Disjoint (epigraph g) (B ×ˢ {a}) := by
      rw [Set.disjoint_left]
      rintro ⟨x, t⟩ hxt ⟨hx, ht⟩
      have ht' : t = a := ht
      exact (hag.trans_le (infimumOn_le hx)).not_ge (ht' ▸ hxt)
    have hmiss := (outerSetLimit_subset_iff_eventually_misses_compact
      (isClosed_epigraph_of_lsc_ereal g hg)).1 h _ (hB.prod isCompact_singleton) hdis
    apply ha.not_ge
    apply le_liminf_of_le (by isBoundedDefault)
    filter_upwards [hmiss] with n hn
    apply le_infimumOn
    intro x hx
    by_contra! hxa
    exact Set.disjoint_left.1 hn (show (x, a) ∈ epigraph (f n) from hxa.le)
      ⟨hx, rfl⟩
  · intro h p hp
    obtain ⟨φ, ps, hφ, hps, hto⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hp
    by_contra hbad
    have hlt : (p.2 : EReal) < g p.1 := lt_of_not_ge hbad
    obtain ⟨a, hpa, hag⟩ := EReal.exists_between_coe_real hlt
    obtain ⟨b, hab, hbg⟩ := EReal.exists_between_coe_real hag
    have hnb := hg p.1 b hbg
    obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.1 hnb
    let B := closedBall p.1 (r / 2)
    have hB : (b : EReal) ≤ infimumOn g B := le_infimumOn fun x hx ↦
      (hrB (closedBall_subset_ball (half_lt_self hr) hx)).le
    have ha := eventually_lt_of_lt_liminf (hab.trans_le (hB.trans
      (h B (isCompact_closedBall _ _))))
    have hmem : ∀ᶠ k in atTop, (ps k).1 ∈ B :=
      hto.fst_nhds (closedBall_mem_nhds _ (half_pos hr))
    have hheight : ∀ᶠ k in atTop, (ps k).2 < a :=
      hto.snd_nhds.eventually_lt_const (EReal.coe_lt_coe_iff.1 hpa)
    obtain ⟨k, hk, hkB, hka⟩ :=
      ((hφ.tendsto_atTop.eventually ha).and (hmem.and hheight)).exists
    exact (hk.trans_le ((infimumOn_le hkB).trans (hps k))).not_ge
      (EReal.coe_le_coe_iff.2 hka.le)

/-- **Proposition 7.29(b)** in epigraph form. No semicontinuity of the test
function is needed for the open-set assertion. -/
theorem epigraph_subset_innerSetLimit_iff_infimumOn_open [PseudoMetricSpace E]
    {f : ℕ → E → EReal} {g : E → EReal} :
    epigraph g ⊆ innerSetLimit (fun n ↦ epigraph (f n)) ↔
      ∀ O : Set E, IsOpen O →
        limsup (fun n ↦ infimumOn (f n) O) atTop ≤ infimumOn g O := by
  constructor
  · intro h O hO
    by_contra! hbad
    obtain ⟨a, hga, ha⟩ := EReal.exists_between_coe_real hbad
    obtain ⟨x, hx, hxa⟩ := infimumOn_lt_iff.1 hga
    obtain ⟨b, hxb, hba⟩ := EReal.exists_between_coe_real hxa
    have hhit := (subset_innerSetLimit_iff_eventually_hits_open.1 h)
      (O ×ˢ Iio a) (hO.prod isOpen_Iio) ⟨(x,b), hxb.le, hx, EReal.coe_lt_coe_iff.1 hba⟩
    apply ha.not_ge
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [hhit] with n hn
    obtain ⟨p, hp, hpO, hpheight⟩ := hn
    exact ((infimumOn_le hpO).trans hp).trans (EReal.coe_le_coe_iff.2 hpheight.le)
  · intro h p hp V hV
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
    let O := ball p.1 r
    let a := p.2 + r / 2
    have hpa : p.2 < a := by dsimp [a]; linarith
    have hga : infimumOn g O < (a : EReal) :=
      ((infimumOn_le (mem_ball_self hr)).trans hp).trans_lt (EReal.coe_lt_coe_iff.2 hpa)
    have hlt := eventually_lt_of_limsup_lt ((h O isOpen_ball).trans_lt hga)
    filter_upwards [hlt] with n hn
    obtain ⟨x, hx, hxa⟩ := infimumOn_lt_iff.1 hn
    refine ⟨(x, a), hxa.le, hrV ?_⟩
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨hx, ?_⟩
    rw [Real.dist_eq, abs_of_pos (sub_pos.2 hpa)]
    dsimp [a]
    linarith

end RW
