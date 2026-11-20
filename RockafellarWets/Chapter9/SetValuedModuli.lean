/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Local Lipschitz moduli of set-valued mappings
-/

import RockafellarWets.Chapter9.SetValuedLipschitz

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E : Type*} [MetricSpace E]

/-- Local modulus of an extended distance between image values. This applies
to the truncated inclusion distance, which need not satisfy a triangle inequality. -/
noncomputable def localPairModulusWithin (q : E → E → ℝ≥0∞) (X : Set E) (x : E) : ℝ≥0∞ :=
  ⨅ k : {k : ℝ≥0 // ∃ U ∈ 𝓝[X] x, ∀ a ∈ U, ∀ b ∈ U, q a b ≤ (k : ℝ≥0∞)*edist a b},
    ((k : ℝ≥0) : ℝ≥0∞)

theorem localPairModulusWithin_le {q : E → E → ℝ≥0∞} {X U : Set E} {x : E} {k : ℝ≥0} (hU : U ∈ 𝓝[X] x)
    (hq : ∀ a ∈ U, ∀ b ∈ U, q a b ≤ (k : ℝ≥0∞)*edist a b) :
    localPairModulusWithin q X x ≤ (k : ℝ≥0∞) :=
  iInf_le (fun c : {c : ℝ≥0 // ∃ U ∈ 𝓝[X] x, ∀ a ∈ U, ∀ b ∈ U, q a b ≤ (c : ℝ≥0∞)*edist a b} ↦
    ((c : ℝ≥0) : ℝ≥0∞)) ⟨k,U,hU,hq⟩

theorem exists_local_pair_bound_of_modulus_lt {q : E → E → ℝ≥0∞} {X : Set E} {x : E} {k : ℝ≥0}
    (h : localPairModulusWithin q X x < (k : ℝ≥0∞)) :
    ∃ U ∈ 𝓝[X] x, ∀ a ∈ U, ∀ b ∈ U, q a b ≤ (k : ℝ≥0∞)*edist a b := by
  obtain ⟨c,hc⟩ := iInf_lt_iff.1 h
  obtain ⟨U,hU,hb⟩ := c.2
  exact ⟨U,hU,fun a ha b hb' ↦ (hb a ha b hb').trans (mul_le_mul_left hc.le _)⟩

theorem localPairModulusWithin_eq_limsup (q : E → E → ℝ≥0∞) (X : Set E) (x : E) (hself : ∀ y, q y y = 0) :
    localPairModulusWithin q X x =
      limsup (fun p : E × E ↦ q p.1 p.2 / edist p.1 p.2)
        ((𝓝[X] x ×ˢ 𝓝[X] x) ⊓ 𝓟 {p : E × E | p.1 ≠ p.2}) := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨k,hk,hk'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    have hb := eventually_lt_of_limsup_lt hk
    obtain ⟨U,hU,V,hV,hUV⟩ := mem_prod_iff.mp (eventually_inf_principal.mp hb)
    apply hk'.not_ge (localPairModulusWithin_le (inter_mem hU hV) ?_)
    intro y hy z hz
    rcases eq_or_ne y z with rfl | hyz
    · simp [hself]
    · exact (ENNReal.div_le_iff (edist_eq_zero.not.mpr hyz) (edist_ne_top y z)).mp
        ((hUV (a := (y,z)) ⟨hy.1,hz.2⟩ hyz).le)
  · refine le_iInf fun k ↦ ?_
    obtain ⟨U,hU,h⟩ := k.2
    apply limsup_le_of_le (by isBoundedDefault)
    apply eventually_inf_principal.mpr
    filter_upwards [tendsto_fst.eventually hU,tendsto_snd.eventually hU] with p ha hb _
    exact ENNReal.div_le_of_le_mul (h p.1 ha p.2 hb)

theorem localPairModulusWithin_mono {q r : E → E → ℝ≥0∞} (X : Set E) (x : E)
    (h : ∀ a ∈ X, ∀ b ∈ X, q a b ≤ r a b) :
    localPairModulusWithin q X x ≤ localPairModulusWithin r X x := by
  refine le_iInf fun k ↦ ?_
  obtain ⟨U,hU,hb⟩ := k.2
  exact localPairModulusWithin_le (inter_mem self_mem_nhdsWithin hU)
    (fun a ha b hb' ↦ (h a ha.1 b hb'.1).trans (hb a ha.2 b hb'.2))

variable {F : Type*} [NormedAddCommGroup F]

/-- The radius-infinity modulus in Definition 9.28. -/
noncomputable abbrev svHausdorffLipschitzModulusWithin (S : E → Set F) (X : Set E) (x : E) :=
  localPairModulusWithin (fun a b ↦ hausdorffEDist (S a) (S b)) X x

/-- The auxiliary graphical-inclusion modulus of formula 9(13). -/
noncomputable abbrev svRhoHatLipschitzModulusWithin (S : E → Set F) (X : Set E) (ρ : ℝ≥0) (x : E) :=
  localPairModulusWithin (fun a b ↦ rhoHatEDistance ρ (S a) (S b)) X x

noncomputable abbrev svHausdorffLipschitzModulus (S : E → Set F) (x : E) := svHausdorffLipschitzModulusWithin S univ x

noncomputable abbrev svRhoHatLipschitzModulus (S : E → Set F) (ρ : ℝ≥0) (x : E) :=
  svRhoHatLipschitzModulusWithin S univ ρ x

theorem svHausdorffLipschitzModulusWithin_eq_limsup (S : E → Set F) (X : Set E) (x : E) :
    svHausdorffLipschitzModulusWithin S X x =
      limsup (fun p : E × E ↦ hausdorffEDist (S p.1) (S p.2) / edist p.1 p.2)
        ((𝓝[X] x ×ˢ 𝓝[X] x) ⊓ 𝓟 {p : E × E | p.1 ≠ p.2}) :=
  localPairModulusWithin_eq_limsup _ _ _ fun _ ↦ hausdorffEDist_self

theorem svRhoHatLipschitzModulusWithin_eq_limsup (S : E → Set F) (X : Set E) (ρ : ℝ≥0) (x : E) :
    svRhoHatLipschitzModulusWithin S X ρ x =
      limsup (fun p : E × E ↦ rhoHatEDistance ρ (S p.1) (S p.2) / edist p.1 p.2)
        ((𝓝[X] x ×ˢ 𝓝[X] x) ⊓ 𝓟 {p : E × E | p.1 ≠ p.2}) := by
  apply localPairModulusWithin_eq_limsup
  intro a
  apply nonpos_iff_eq_zero.1
  rw [rhoHatEDistance,sup_le_iff]
  exact ⟨iSup_le fun v ↦ iSup_le fun hv ↦ (infEDist_zero_of_mem hv.1).le,
    iSup_le fun v ↦ iSup_le fun hv ↦ (infEDist_zero_of_mem hv.1).le⟩

end RW
