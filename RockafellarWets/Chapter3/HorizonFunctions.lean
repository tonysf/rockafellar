/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3C: Horizon Functions

This file formalizes the first layer of Section C:
- Definition 3.17: horizon functions
- the basic epigraph inclusion `epi f∞ ⊇ (epi f)∞`
- positive homogeneity of the horizon function
-/

import RockafellarWets.Chapter3.PositiveHomogeneity
import RockafellarWets.Chapter3.SetOperations
import RockafellarWets.Chapter3.PointedCones
import RockafellarWets.Chapter3.NonlinearImages
import RockafellarWets.Chapter1.Semicontinuity

open Set EReal Filter AffineSpace Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 3.17**: the horizon function of `f` is the lower boundary of
the horizon cone of its epigraph. -/
noncomputable def horizonFunction (f : E → EReal) (w : E) : EReal :=
  ⨅ a : {a : ℝ // (w, a) ∈ horizonCone (epigraph f)}, (a : EReal)

/-- Any point of the horizon cone of the epigraph lies on or above the horizon
function. -/
theorem horizonFunction_le_of_mem_horizonCone_epigraph {f : E → EReal} {w : E} {a : ℝ}
    (ha : (w, a) ∈ horizonCone (epigraph f)) :
    horizonFunction f w ≤ (a : EReal) := by
  exact iInf_le
    (fun b : {a : ℝ // (w, a) ∈ horizonCone (epigraph f)} => (b : EReal))
    ⟨a, ha⟩

/-- Every point of the horizon cone of the epigraph belongs to the epigraph of
the horizon function. -/
theorem mem_epigraph_horizonFunction_of_mem_horizonCone_epigraph {f : E → EReal}
    {w : E} {a : ℝ} (ha : (w, a) ∈ horizonCone (epigraph f)) :
    (w, a) ∈ epigraph (horizonFunction f) := by
  rw [mem_epigraph_iff]
  exact horizonFunction_le_of_mem_horizonCone_epigraph ha

/-- The horizon cone of `epi f` is contained in `epi(f∞)`. -/
theorem horizonCone_epigraph_subset_epigraph_horizonFunction (f : E → EReal) :
    horizonCone (epigraph f) ⊆ epigraph (horizonFunction f) := by
  intro p hp
  rcases p with ⟨w, a⟩
  exact mem_epigraph_horizonFunction_of_mem_horizonCone_epigraph hp

/-- Increasing the vertical coordinate preserves membership in the asymptotic
cone of an epigraph. -/
theorem add_nonneg_mem_asymptoticCone_epigraph {f : E → EReal} {w : E} {a d : ℝ}
    (ha : (w, a) ∈ asymptoticCone ℝ (epigraph f)) (hd : 0 ≤ d) :
    (w, a + d) ∈ asymptoticCone ℝ (epigraph f) := by
  rw [mem_asymptoticCone_iff, AffineSpace.asymptoticNhds_eq_smul, ← map₂_smul,
    ← map_prod_eq_map₂,
    frequently_map]
  have hshift :
      Tendsto (fun p : ℝ × (E × ℝ) => (p.1, (p.2.1, p.2.2 + d)))
        (atTop ×ˢ 𝓝 (w, a)) (atTop ×ˢ 𝓝 (w, a + d)) := by
    refine tendsto_fst.prodMk ?_
    have :
        Tendsto (fun u : E × ℝ => (u.1, u.2 + d)) (𝓝 (w, a)) (𝓝 (w, a + d)) := by
      simpa using (continuous_fst.prodMk (continuous_snd.add continuous_const)).continuousAt.tendsto
    exact this.comp tendsto_snd
  have ha' :
      ∃ᶠ p : ℝ × (E × ℝ) in atTop ×ˢ 𝓝 (w, a), p.1 • p.2 ∈ epigraph f ∧ 0 ≤ p.1 := by
    rw [mem_asymptoticCone_iff, AffineSpace.asymptoticNhds_eq_smul, ← map₂_smul,
      ← map_prod_eq_map₂, frequently_map] at ha
    exact ha.and_eventually (tendsto_fst.eventually (eventually_ge_atTop 0))
  exact Tendsto.frequently_map
    (fun p : ℝ × (E × ℝ) => (p.1, (p.2.1, p.2.2 + d))) hshift
    (fun p hp => by
      rcases hp with ⟨hp, hp0⟩
      rcases p with ⟨t, u⟩
      rcases u with ⟨x, b⟩
      simp only [Prod.smul_mk, smul_eq_mul, mem_epigraph_iff] at hp ⊢
      rw [mul_add]
      have htd : 0 ≤ t * d := mul_nonneg hp0 hd
      exact hp.trans <| by
        exact_mod_cast le_add_of_nonneg_right htd)
    ha'

/-- If `epi f` is nonempty, then `epi(f∞)` is contained in `(epi f)∞`. -/
theorem epigraph_horizonFunction_subset_horizonCone_epigraph {f : E → EReal}
    (hf : (epigraph f).Nonempty) :
    epigraph (horizonFunction f) ⊆ horizonCone (epigraph f) := by
  intro p hp
  rcases p with ⟨w, α⟩
  have hα : horizonFunction f w ≤ (α : EReal) := by
    simpa [mem_epigraph_iff] using hp
  have hcone : horizonCone (epigraph f) = asymptoticCone ℝ (epigraph f) :=
    horizonCone_eq_asymptoticCone hf
  let A : Type := {a : ℝ // (w, a) ∈ asymptoticCone ℝ (epigraph f)}
  have hfun :
      horizonFunction f w = ⨅ a : A, (a : EReal) := by
    change horizonFunction f w =
      ⨅ a : {a : ℝ // (w, a) ∈ asymptoticCone ℝ (epigraph f)}, (a : EReal)
    rw [horizonFunction, hcone]
  have hA_nonempty : Nonempty A := by
    by_contra hA
    have hAcone :
        ¬ Nonempty {a : ℝ // (w, a) ∈ horizonCone (epigraph f)} := by
      intro h
      rcases h with ⟨a⟩
      exact hA ⟨⟨a, by simpa [hcone] using a.property⟩⟩
    letI : IsEmpty {a : ℝ // (w, a) ∈ horizonCone (epigraph f)} := not_nonempty_iff.mp hAcone
    have ht : horizonFunction f w = ⊤ := by
      rw [horizonFunction]
      exact iInf_of_empty _
    have : (⊤ : EReal) ≤ (α : EReal) := by simpa [ht] using hα
    simpa using this
  letI : Nonempty A := hA_nonempty
  rw [hcone]
  by_cases hlt : horizonFunction f w < (α : EReal)
  · have hltA : (⨅ a : A, (a : EReal)) < (α : EReal) := by
      simpa [hfun] using hlt
    obtain ⟨b, hb⟩ := exists_lt_of_ciInf_lt hltA
    have hb' : ((b : ℝ) : EReal) < (α : EReal) := hb
    have hb_real : (b : ℝ) < α := by
      exact_mod_cast hb'
    have hmem :
        (w, (b : ℝ) + (α - (b : ℝ))) ∈ asymptoticCone ℝ (epigraph f) :=
      add_nonneg_mem_asymptoticCone_epigraph (a := (b : ℝ)) (d := α - (b : ℝ))
        b.property (sub_nonneg.mpr hb_real.le)
    have hsum : (b : ℝ) + (α - (b : ℝ)) = α := by
      linarith
    simpa [hsum] using hmem
  · have hEq : horizonFunction f w = (α : EReal) := by
      exact le_antisymm hα (le_of_not_gt hlt)
    have happrox :
        ∀ n : ℕ, ∃ a : A, (a : EReal) < ((α + ((n : ℝ) + 1)⁻¹ : ℝ) : EReal) := by
      intro n
      have hltα : (α : EReal) < ((α + ((n : ℝ) + 1)⁻¹ : ℝ) : EReal) := by
        exact_mod_cast (lt_add_of_pos_right α (by positivity : 0 < ((n : ℝ) + 1)⁻¹))
      have hltn : horizonFunction f w <
          ((α + ((n : ℝ) + 1)⁻¹ : ℝ) : EReal) := by
        simpa [hEq] using hltα
      have hltA :
          (⨅ a : A, (a : EReal)) <
            ((α + ((n : ℝ) + 1)⁻¹ : ℝ) : EReal) := by
        simpa [hfun] using hltn
      exact exists_lt_of_ciInf_lt hltA
    choose b hb using happrox
    have hb_lower : ∀ n : ℕ, (α : EReal) ≤ ((b n : A) : EReal) := by
      intro n
      calc
        (α : EReal) = horizonFunction f w := by simpa using hEq.symm
        _ = ⨅ a : A, (a : EReal) := hfun
        _ ≤ ((b n : A) : EReal) := iInf_le _ (b n)
    have hb_lower_real : ∀ n : ℕ, α ≤ ((b n : A) : ℝ) := by
      intro n
      exact_mod_cast hb_lower n
    have hb_upper_real : ∀ n : ℕ, ((b n : A) : ℝ) ≤ α + ((n : ℝ) + 1)⁻¹ := by
      intro n
      exact_mod_cast le_of_lt (hb n)
    have hupper_tendsto :
        Tendsto (fun n : ℕ => α + ((n : ℝ) + 1)⁻¹) atTop (𝓝 α) := by
      simpa [one_div] using
        (tendsto_const_nhds (x := α)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hb_tendsto : Tendsto (fun n : ℕ => ((b n : A) : ℝ)) atTop (𝓝 α) := by
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hupper_tendsto hb_lower_real hb_upper_real
    have hp_tendsto : Tendsto (fun n : ℕ => (w, ((b n : A) : ℝ))) atTop (𝓝 (w, α)) := by
      have :
          Tendsto (fun x : ℝ => (w, x)) (𝓝 α) (𝓝 (w, α)) := by
        simpa using (continuous_const.prodMk continuous_id).continuousAt.tendsto
      exact this.comp hb_tendsto
    have hb_mem :
        ∀ᶠ n in atTop, (w, ((b n : A) : ℝ)) ∈ asymptoticCone ℝ (epigraph f) :=
      Filter.Eventually.of_forall fun n => (b n).property
    exact (isClosed_asymptoticCone (k := ℝ) (s := epigraph f)).mem_of_tendsto hp_tendsto hb_mem

/-- If `epi f` is nonempty, then `epi(f∞) = (epi f)∞`. -/
theorem epigraph_horizonFunction_eq_horizonCone_epigraph {f : E → EReal}
    (hf : (epigraph f).Nonempty) :
    epigraph (horizonFunction f) = horizonCone (epigraph f) := by
  refine le_antisymm (epigraph_horizonFunction_subset_horizonCone_epigraph hf) ?_
  exact horizonCone_epigraph_subset_epigraph_horizonFunction f

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Equality of real epigraphs determines an `EReal`-valued function. -/
theorem eq_of_epigraph_eq {f g : E → EReal} (hfg : epigraph f = epigraph g) :
    f = g := by
  funext x
  apply le_antisymm
  · by_contra h
    have hlt : g x < f x := lt_of_not_ge h
    obtain ⟨a, hga, haf⟩ := EReal.exists_between_coe_real hlt
    have hxg : (x, a) ∈ epigraph g := by
      rw [mem_epigraph_iff]
      exact hga.le
    have hxf : (x, a) ∈ epigraph f := by simpa [hfg] using hxg
    rw [mem_epigraph_iff] at hxf
    exact not_le_of_gt haf hxf
  · by_contra h
    have hlt : f x < g x := lt_of_not_ge h
    obtain ⟨a, hfa, hag⟩ := EReal.exists_between_coe_real hlt
    have hxf : (x, a) ∈ epigraph f := by
      rw [mem_epigraph_iff]
      exact hfa.le
    have hxg : (x, a) ∈ epigraph g := by simpa [hfg] using hxf
    rw [mem_epigraph_iff] at hxg
    exact not_le_of_gt hag hxg

/-- A lower semicontinuous positively homogeneous function coincides with its
horizon function. -/
theorem horizonFunction_eq_self_of_lowerSemicontinuous_of_positivelyHomogeneous
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : G → EReal} (hlsc : LowerSemicontinuous g)
    (hph : PositivelyHomogeneous g) :
    horizonFunction g = g := by
  have hne : (epigraph g).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    rw [mem_epigraph_iff]
    exact hph.map_zero_le_zero
  apply eq_of_epigraph_eq
  calc
    epigraph (horizonFunction g) = horizonCone (epigraph g) :=
      epigraph_horizonFunction_eq_horizonCone_epigraph hne
    _ = epigraph g := by
      exact horizonCone_eq_self_of_isClosed_isCone
        (isClosed_epigraph_of_lsc_ereal g hlsc)
        (isCone_epigraph_of_positivelyHomogeneous hph)

/-- In the empty-epigraph case, the horizon function is the indicator of the
zero cone. -/
theorem horizonFunction_eq_indicatorVA_zero_of_epigraph_empty {f : E → EReal}
    (hf : epigraph f = ∅) :
    horizonFunction f = indicatorVA ({0} : Set E) := by
  funext w
  by_cases hw : w = 0
  · subst hw
    apply le_antisymm
    · simpa [indicatorVA] using horizonFunction_le_of_mem_horizonCone_epigraph
        (f := f) (w := 0) (a := 0) (by simpa [hf])
    · refine le_iInf ?_
      intro a
      have ha0 : (a : ℝ) = 0 := by
        simpa [hf] using a.property
      simpa [indicatorVA, ha0]
  · simp [horizonFunction, hf, indicatorVA, hw]

/-- The horizon cone of the nonnegative half-line is the half-line itself. -/
theorem horizonCone_Ici_zero :
    horizonCone (Set.Ici (0 : ℝ)) = Set.Ici (0 : ℝ) := by
  have hcone : IsCone (Set.Ici (0 : ℝ)) := by
    refine ⟨by simp, ?_⟩
    intro x hx c hc
    exact mul_nonneg hc.le hx
  have hne : (Set.Ici (0 : ℝ)).Nonempty := ⟨0, by simp⟩
  rw [horizonCone_eq_asymptoticCone hne]
  calc
    asymptoticCone ℝ (Set.Ici (0 : ℝ)) = closure (Set.Ici (0 : ℝ)) := by
      exact asymptoticCone_eq_closure_of_forall_smul_mem fun c hc x hx =>
        hcone.2 hx hc
    _ = Set.Ici (0 : ℝ) := isClosed_Ici.closure_eq

/-- Indicator functions commute with taking horizon functions:
`(δ_C)∞ = δ_{C∞}`. -/
theorem horizonFunction_indicatorVA [FiniteDimensional ℝ E] (C : Set E) :
    horizonFunction (indicatorVA C) = indicatorVA (horizonCone C) := by
  funext w
  by_cases hw : w ∈ horizonCone C
  · have hmem_zero :
        (w, (0 : ℝ)) ∈ horizonCone (epigraph (indicatorVA C)) := by
      have hprod :
          (w, (0 : ℝ)) ∈ horizonCone (C ×ˢ Set.Ici (0 : ℝ)) :=
        prod_horizonCone_zero_subset_horizonCone_prod
          (C := C) (D := Set.Ici (0 : ℝ)) ⟨0, by simp⟩ ⟨hw, by simp⟩
      simpa [epigraph_indicatorVA] using hprod
    have hle : horizonFunction (indicatorVA C) w ≤ 0 :=
      horizonFunction_le_of_mem_horizonCone_epigraph hmem_zero
    have hge : 0 ≤ horizonFunction (indicatorVA C) w := by
      rw [horizonFunction]
      refine le_iInf ?_
      intro a
      have hprod :
          (w, (a : ℝ)) ∈ horizonCone (C ×ˢ Set.Ici (0 : ℝ)) := by
        simpa [epigraph_indicatorVA] using a.property
      have ha : (a : ℝ) ∈ horizonCone (Set.Ici (0 : ℝ)) :=
        (horizonCone_prod_subset (C := C) (D := Set.Ici (0 : ℝ)) hprod).2
      have ha_nonneg : 0 ≤ (a : ℝ) := by
        simpa [horizonCone_Ici_zero] using ha
      exact_mod_cast ha_nonneg
    rw [indicatorVA_apply_mem hw]
    exact le_antisymm hle hge
  · have htop : horizonFunction (indicatorVA C) w = ⊤ := by
      rw [horizonFunction]
      have hnone :
          ¬ Nonempty {a : ℝ // (w, a) ∈ horizonCone (epigraph (indicatorVA C))} := by
        rintro ⟨a, ha⟩
        have hprod :
            (w, (a : ℝ)) ∈ horizonCone (C ×ˢ Set.Ici (0 : ℝ)) := by
          simpa [epigraph_indicatorVA] using ha
        have hw' : w ∈ horizonCone C :=
          (horizonCone_prod_subset (C := C) (D := Set.Ici (0 : ℝ)) hprod).1
        exact hw hw'
      letI : IsEmpty {a : ℝ // (w, a) ∈ horizonCone (epigraph (indicatorVA C))} :=
        not_nonempty_iff.mp hnone
      exact iInf_of_empty _
    rw [indicatorVA_apply_not_mem hw, htop]

/-- Epigraph form of `(δ_C)∞ = δ_{C∞}`. -/
theorem epigraph_horizonFunction_indicatorVA [FiniteDimensional ℝ E] (C : Set E) :
    epigraph (horizonFunction (indicatorVA C)) =
      horizonCone C ×ˢ Set.Ici (0 : ℝ) := by
  rw [horizonFunction_indicatorVA, epigraph_indicatorVA]

/-- Effective-domain form of `(δ_C)∞ = δ_{C∞}`. -/
theorem effectiveDomain_horizonFunction_indicatorVA [FiniteDimensional ℝ E] (C : Set E) :
    effectiveDomain (horizonFunction (indicatorVA C)) = horizonCone C := by
  rw [horizonFunction_indicatorVA, effectiveDomain_indicatorVA]

/-- Zero-level-set form of `(δ_C)∞ = δ_{C∞}`. -/
theorem levelSet_zero_horizonFunction_indicatorVA [FiniteDimensional ℝ E] (C : Set E) :
    levelSet (horizonFunction (indicatorVA C)) (0 : EReal) = horizonCone C := by
  rw [horizonFunction_indicatorVA]
  ext x
  by_cases hx : x ∈ horizonCone C <;> simp [levelSet, hx]

/-- For indicator horizons, the effective domain is exactly the zero level set. -/
theorem effectiveDomain_horizonFunction_indicatorVA_eq_levelSet_zero [FiniteDimensional ℝ E]
    (C : Set E) :
    effectiveDomain (horizonFunction (indicatorVA C)) =
      levelSet (horizonFunction (indicatorVA C)) (0 : EReal) := by
  rw [effectiveDomain_horizonFunction_indicatorVA, levelSet_zero_horizonFunction_indicatorVA]

/-- Symmetric form: the zero level set of an indicator horizon is its effective domain. -/
theorem levelSet_zero_horizonFunction_indicatorVA_eq_effectiveDomain [FiniteDimensional ℝ E]
    (C : Set E) :
    levelSet (horizonFunction (indicatorVA C)) (0 : EReal) =
      effectiveDomain (horizonFunction (indicatorVA C)) :=
  (effectiveDomain_horizonFunction_indicatorVA_eq_levelSet_zero C).symm

/-- Pointwise form of `(δ_C)∞ = δ_{C∞}` on horizon directions. -/
theorem horizonFunction_indicatorVA_apply_mem [FiniteDimensional ℝ E]
    {C : Set E} {w : E} (hw : w ∈ horizonCone C) :
    horizonFunction (indicatorVA C) w = 0 := by
  rw [horizonFunction_indicatorVA, indicatorVA_apply_mem hw]

/-- Pointwise form of `(δ_C)∞ = δ_{C∞}` off horizon directions. -/
theorem horizonFunction_indicatorVA_apply_not_mem [FiniteDimensional ℝ E]
    {C : Set E} {w : E} (hw : w ∉ horizonCone C) :
    horizonFunction (indicatorVA C) w = ⊤ := by
  rw [horizonFunction_indicatorVA, indicatorVA_apply_not_mem hw]

/-- The indicator horizon vanishes exactly on the horizon cone. -/
theorem horizonFunction_indicatorVA_eq_zero_iff [FiniteDimensional ℝ E]
    {C : Set E} {w : E} :
    horizonFunction (indicatorVA C) w = 0 ↔ w ∈ horizonCone C := by
  rw [horizonFunction_indicatorVA]
  by_cases hw : w ∈ horizonCone C
  · simp [indicatorVA, hw]
  · simp [indicatorVA, hw]

/-- The indicator horizon is `⊤` exactly off the horizon cone. -/
theorem horizonFunction_indicatorVA_eq_top_iff [FiniteDimensional ℝ E]
    {C : Set E} {w : E} :
    horizonFunction (indicatorVA C) w = ⊤ ↔ w ∉ horizonCone C := by
  rw [horizonFunction_indicatorVA]
  by_cases hw : w ∈ horizonCone C
  · simp [indicatorVA, hw]
  · simp [indicatorVA, hw]

/-- The indicator horizon is finite exactly on the horizon cone. -/
theorem horizonFunction_indicatorVA_lt_top_iff [FiniteDimensional ℝ E]
    {C : Set E} {w : E} :
    horizonFunction (indicatorVA C) w < ⊤ ↔ w ∈ horizonCone C := by
  rw [horizonFunction_indicatorVA]
  by_cases hw : w ∈ horizonCone C
  · simp [indicatorVA, hw]
  · simp [indicatorVA, hw]

/-- The indicator horizon is not `⊤` exactly on the horizon cone. -/
theorem horizonFunction_indicatorVA_ne_top_iff [FiniteDimensional ℝ E]
    {C : Set E} {w : E} :
    horizonFunction (indicatorVA C) w ≠ ⊤ ↔ w ∈ horizonCone C := by
  rw [horizonFunction_indicatorVA]
  by_cases hw : w ∈ horizonCone C
  · simp [indicatorVA, hw]
  · simp [indicatorVA, hw]

/-- The sublevel condition at zero for an indicator horizon is horizon-cone membership. -/
theorem horizonFunction_indicatorVA_le_zero_iff [FiniteDimensional ℝ E]
    {C : Set E} {w : E} :
    horizonFunction (indicatorVA C) w ≤ 0 ↔ w ∈ horizonCone C := by
  rw [horizonFunction_indicatorVA]
  by_cases hw : w ∈ horizonCone C
  · simp [indicatorVA, hw]
  · simp [indicatorVA, hw]

/-- The indicator horizon is strictly positive exactly off the horizon cone. -/
theorem horizonFunction_indicatorVA_pos_iff_not_mem [FiniteDimensional ℝ E]
    {C : Set E} {w : E} :
    0 < horizonFunction (indicatorVA C) w ↔ w ∉ horizonCone C := by
  rw [horizonFunction_indicatorVA]
  by_cases hw : w ∈ horizonCone C
  · simp [indicatorVA, hw]
  · simp [indicatorVA, hw]

/-- Indicator horizons are nonnegative. -/
theorem horizonFunction_indicatorVA_nonneg [FiniteDimensional ℝ E]
    (C : Set E) (w : E) :
    0 ≤ horizonFunction (indicatorVA C) w := by
  rw [horizonFunction_indicatorVA]
  by_cases hw : w ∈ horizonCone C
  · simp [indicatorVA, hw]
  · simp [indicatorVA, hw]

/-- Indicator horizons never take the value `⊥`. -/
theorem horizonFunction_indicatorVA_bot_lt [FiniteDimensional ℝ E]
    (C : Set E) (w : E) :
    (⊥ : EReal) < horizonFunction (indicatorVA C) w := by
  rw [horizonFunction_indicatorVA]
  by_cases hw : w ∈ horizonCone C
  · simp [indicatorVA, hw]
  · simp [indicatorVA, hw]

/-- Finite lower level sets of indicator horizons reduce to horizon-cone membership and
nonnegativity of the level. -/
theorem mem_levelSet_horizonFunction_indicatorVA_coe_iff [FiniteDimensional ℝ E]
    {C : Set E} {w : E} {α : ℝ} :
    w ∈ levelSet (horizonFunction (indicatorVA C)) (α : EReal) ↔
      w ∈ horizonCone C ∧ 0 ≤ α := by
  rw [horizonFunction_indicatorVA]
  by_cases hw : w ∈ horizonCone C
  · simp [levelSet, indicatorVA, hw]
  · simp [levelSet, indicatorVA, hw]

/-- Nonnegative finite lower levels of an indicator horizon are the horizon cone. -/
theorem levelSet_horizonFunction_indicatorVA_coe_of_nonneg [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : 0 ≤ α) :
    levelSet (horizonFunction (indicatorVA C)) (α : EReal) = horizonCone C := by
  ext w
  rw [mem_levelSet_horizonFunction_indicatorVA_coe_iff]
  simp [hα]

/-- Negative finite lower levels of an indicator horizon are empty. -/
theorem levelSet_horizonFunction_indicatorVA_coe_of_neg [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : α < 0) :
    levelSet (horizonFunction (indicatorVA C)) (α : EReal) = ∅ := by
  ext w
  rw [mem_levelSet_horizonFunction_indicatorVA_coe_iff]
  simp [not_le_of_gt hα]

/-- Finite strict lower level sets of indicator horizons reduce to horizon-cone membership and
positivity of the level. -/
theorem mem_strictLevelSet_horizonFunction_indicatorVA_coe_iff [FiniteDimensional ℝ E]
    {C : Set E} {w : E} {α : ℝ} :
    w ∈ strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal) ↔
      w ∈ horizonCone C ∧ 0 < α := by
  rw [horizonFunction_indicatorVA]
  by_cases hw : w ∈ horizonCone C
  · simp [strictLevelSet, indicatorVA, hw]
  · simp [strictLevelSet, indicatorVA, hw]

/-- Positive finite strict lower levels of an indicator horizon are the horizon cone. -/
theorem strictLevelSet_horizonFunction_indicatorVA_coe_of_pos [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : 0 < α) :
    strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal) = horizonCone C := by
  ext w
  rw [mem_strictLevelSet_horizonFunction_indicatorVA_coe_iff]
  simp [hα]

/-- Nonpositive finite strict lower levels of an indicator horizon are empty. -/
theorem strictLevelSet_horizonFunction_indicatorVA_coe_of_nonpos [FiniteDimensional ℝ E]
    (C : Set E) {α : ℝ} (hα : α ≤ 0) :
    strictLevelSet (horizonFunction (indicatorVA C)) (α : EReal) = ∅ := by
  ext w
  rw [mem_strictLevelSet_horizonFunction_indicatorVA_coe_iff]
  simp [not_lt_of_ge hα]

/-- Convex-set specialization: the horizon function of an indicator is sublinear. -/
theorem sublinear_horizonFunction_indicatorVA_of_convex [FiniteDimensional ℝ E]
    {C : Set E} (hC : Convex ℝ C) :
    Sublinear (horizonFunction (indicatorVA C)) := by
  rw [horizonFunction_indicatorVA]
  exact sublinear_indicatorVA_iff.mpr ⟨convex_horizonCone hC, isCone_horizonCone C⟩

/-- Membership form of the effective-domain identity for indicator horizons. -/
theorem mem_effectiveDomain_horizonFunction_indicatorVA_iff [FiniteDimensional ℝ E]
    {C : Set E} {w : E} :
    w ∈ effectiveDomain (horizonFunction (indicatorVA C)) ↔ w ∈ horizonCone C := by
  rw [effectiveDomain_horizonFunction_indicatorVA]

/-- Membership form of the zero-level-set identity for indicator horizons. -/
theorem mem_levelSet_zero_horizonFunction_indicatorVA_iff [FiniteDimensional ℝ E]
    {C : Set E} {w : E} :
    w ∈ levelSet (horizonFunction (indicatorVA C)) (0 : EReal) ↔ w ∈ horizonCone C := by
  rw [levelSet_zero_horizonFunction_indicatorVA]

/-- The effective domain of the horizon function of an indicator is a cone. -/
theorem isCone_effectiveDomain_horizonFunction_indicatorVA [FiniteDimensional ℝ E]
    (C : Set E) :
    IsCone (effectiveDomain (horizonFunction (indicatorVA C))) := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact isCone_horizonCone C

/-- Convex-set specialization: the effective domain of an indicator horizon is
convex. -/
theorem convex_effectiveDomain_horizonFunction_indicatorVA_of_convex
    [FiniteDimensional ℝ E] {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (effectiveDomain (horizonFunction (indicatorVA C))) := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact convex_horizonCone hC

/-- Convex-set specialization: the epigraph of an indicator horizon is convex. -/
theorem convex_epigraph_horizonFunction_indicatorVA_of_convex
    [FiniteDimensional ℝ E] {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (epigraph (horizonFunction (indicatorVA C))) :=
  convex_epigraph_of_sublinear (sublinear_horizonFunction_indicatorVA_of_convex hC)

/-- The epigraph of an indicator horizon is closed. -/
theorem isClosed_epigraph_horizonFunction_indicatorVA [FiniteDimensional ℝ E]
    (C : Set E) :
    IsClosed (epigraph (horizonFunction (indicatorVA C))) := by
  rw [epigraph_horizonFunction_indicatorVA]
  exact (isClosed_horizonCone C).prod isClosed_Ici

/-- The horizon function of an indicator is lower semicontinuous. -/
theorem lowerSemicontinuous_horizonFunction_indicatorVA [FiniteDimensional ℝ E]
    (C : Set E) :
    LowerSemicontinuous (horizonFunction (indicatorVA C)) :=
  lowerSemicontinuous_of_isClosed_epigraph_ereal _
    (isClosed_epigraph_horizonFunction_indicatorVA C)

/-- The effective domain of an indicator horizon is closed. -/
theorem isClosed_effectiveDomain_horizonFunction_indicatorVA [FiniteDimensional ℝ E]
    (C : Set E) :
    IsClosed (effectiveDomain (horizonFunction (indicatorVA C))) := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact isClosed_horizonCone C

/-- The zero level set of an indicator horizon is closed. -/
theorem isClosed_levelSet_zero_horizonFunction_indicatorVA [FiniteDimensional ℝ E]
    (C : Set E) :
    IsClosed (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)) := by
  rw [levelSet_zero_horizonFunction_indicatorVA]
  exact isClosed_horizonCone C

/-- The effective domain of an indicator horizon is nonempty. -/
theorem effectiveDomain_horizonFunction_indicatorVA_nonempty [FiniteDimensional ℝ E]
    (C : Set E) :
    (effectiveDomain (horizonFunction (indicatorVA C))).Nonempty := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact ⟨0, zero_mem_horizonCone C⟩

/-- The zero level set of an indicator horizon is nonempty. -/
theorem levelSet_zero_horizonFunction_indicatorVA_nonempty [FiniteDimensional ℝ E]
    (C : Set E) :
    (levelSet (horizonFunction (indicatorVA C)) (0 : EReal)).Nonempty := by
  rw [levelSet_zero_horizonFunction_indicatorVA]
  exact ⟨0, zero_mem_horizonCone C⟩

/-- The horizon function of an indicator is proper. -/
theorem isProper_horizonFunction_indicatorVA [FiniteDimensional ℝ E]
    (C : Set E) :
    IsProper (horizonFunction (indicatorVA C)) := by
  rw [horizonFunction_indicatorVA]
  exact (indicatorVA_isProper_iff (horizonCone C)).2 ⟨0, zero_mem_horizonCone C⟩

/-- The horizon function of an indicator vanishes at the origin. -/
theorem horizonFunction_indicatorVA_zero [FiniteDimensional ℝ E] (C : Set E) :
    horizonFunction (indicatorVA C) (0 : E) = 0 :=
  horizonFunction_indicatorVA_apply_mem (C := C) (zero_mem_horizonCone C)

/-- The origin lies in the effective domain of an indicator horizon. -/
theorem zero_mem_effectiveDomain_horizonFunction_indicatorVA [FiniteDimensional ℝ E]
    (C : Set E) :
    (0 : E) ∈ effectiveDomain (horizonFunction (indicatorVA C)) := by
  rw [effectiveDomain_horizonFunction_indicatorVA]
  exact zero_mem_horizonCone C

/-- The origin lies in the zero level set of an indicator horizon. -/
theorem zero_mem_levelSet_zero_horizonFunction_indicatorVA [FiniteDimensional ℝ E]
    (C : Set E) :
    (0 : E) ∈ levelSet (horizonFunction (indicatorVA C)) (0 : EReal) := by
  rw [levelSet_zero_horizonFunction_indicatorVA]
  exact zero_mem_horizonCone C

/-- If `epi f` is convex, then so is `epi(f∞)`. This is the convex part of the
epigraphical statement behind Theorem 3.21. -/
theorem convex_epigraph_horizonFunction {f : E → EReal}
    (hconv : Convex ℝ (epigraph f)) :
    Convex ℝ (epigraph (horizonFunction f)) := by
  by_cases hf : (epigraph f).Nonempty
  · simpa [epigraph_horizonFunction_eq_horizonCone_epigraph hf] using convex_horizonCone hconv
  · have hempty : epigraph f = ∅ := Set.not_nonempty_iff_eq_empty.mp hf
    have hcone0 : IsCone ({0} : Set E) := by
      refine ⟨by simp, ?_⟩
      intro x hx c hc
      simpa [Set.mem_singleton_iff.mp hx]
    have hsub : Sublinear (indicatorVA ({0} : Set E)) := by
      exact sublinear_indicatorVA_iff.mpr ⟨convex_singleton 0, hcone0⟩
    simpa [horizonFunction_eq_indicatorVA_zero_of_epigraph_empty hempty] using
      convex_epigraph_of_sublinear (h := indicatorVA ({0} : Set E)) hsub

/-- **Theorem 3.21** (lsc part): the horizon function is lower
semicontinuous. -/
theorem lowerSemicontinuous_horizonFunction (f : E → EReal) :
    LowerSemicontinuous (horizonFunction f) := by
  by_cases hf : (epigraph f).Nonempty
  · apply lowerSemicontinuous_of_isClosed_epigraph_ereal
    simpa [epigraph_horizonFunction_eq_horizonCone_epigraph hf] using
      isClosed_horizonCone (epigraph f)
  · have hempty : epigraph f = ∅ := Set.not_nonempty_iff_eq_empty.mp hf
    simpa [horizonFunction_eq_indicatorVA_zero_of_epigraph_empty hempty] using
      lowerSemicontinuous_indicatorVA (C := ({0} : Set E)) isClosed_singleton

/-- The epigraph of a horizon function is closed. -/
theorem isClosed_epigraph_horizonFunction (f : E → EReal) :
    IsClosed (epigraph (horizonFunction f)) :=
  isClosed_epigraph_of_lsc_ereal _ (lowerSemicontinuous_horizonFunction f)

/-- The origin at height zero belongs to the epigraph of every horizon function. -/
theorem zero_mem_epigraph_horizonFunction (f : E → EReal) :
    ((0 : E), (0 : ℝ)) ∈ epigraph (horizonFunction f) := by
  rw [mem_epigraph_iff]
  exact horizonFunction_le_of_mem_horizonCone_epigraph
    (zero_mem_horizonCone (epigraph f))

/-- The epigraph of every horizon function is nonempty. -/
theorem epigraph_horizonFunction_nonempty (f : E → EReal) :
    (epigraph (horizonFunction f)).Nonempty :=
  ⟨((0 : E), (0 : ℝ)), zero_mem_epigraph_horizonFunction f⟩

/-- Positive scaling of the argument scales the horizon function by at least the
same factor. -/
theorem smul_horizonFunction_le {f : E → EReal} {w : E} {c : ℝ} (hc : 0 < c) :
    (c : EReal) * horizonFunction f w ≤ horizonFunction f (c • w) := by
  refine le_iInf ?_
  intro b
  have hscaled :
      (w, (c⁻¹ : ℝ) * (b : ℝ)) ∈ horizonCone (epigraph f) := by
    have hsmul :
        (c⁻¹ : ℝ) • (c • w, (b : ℝ)) ∈ horizonCone (epigraph f) :=
      (isCone_horizonCone (epigraph f)).2 b.property (inv_pos_of_pos hc)
    simpa [Prod.smul_mk, smul_smul, inv_mul_cancel₀ hc.ne'] using hsmul
  have hbound :
      horizonFunction f w ≤ (((c⁻¹ : ℝ) * (b : ℝ) : ℝ) : EReal) :=
    horizonFunction_le_of_mem_horizonCone_epigraph hscaled
  have hmul :
      (c : EReal) * horizonFunction f w ≤
        ((c : EReal) * ((((c⁻¹ : ℝ) * (b : ℝ) : ℝ) : EReal))) := by
    gcongr
  have hcancel :
      ((c : EReal) * ((((c⁻¹ : ℝ) * (b : ℝ) : ℝ) : EReal))) = (b : EReal) := by
    rw [← EReal.coe_mul]
    have hreal : c * ((c⁻¹ : ℝ) * (b : ℝ)) = (b : ℝ) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    exact_mod_cast hreal
  calc
    (c : EReal) * horizonFunction f w ≤
        ((c : EReal) * ((((c⁻¹ : ℝ) * (b : ℝ) : ℝ) : EReal))) := hmul
    _ = (b : EReal) := hcancel

/-- **Theorem 3.21** (first part): the horizon function is positively
homogeneous. -/
theorem positivelyHomogeneous_horizonFunction (f : E → EReal) :
    PositivelyHomogeneous (horizonFunction f) := by
  refine ⟨?_, ?_⟩
  · have hzero :
    horizonFunction f 0 ≤ (0 : EReal) :=
      horizonFunction_le_of_mem_horizonCone_epigraph
        (zero_mem_horizonCone (epigraph f))
    exact lt_of_le_of_lt hzero (by simpa using (EReal.coe_lt_top (0 : ℝ)))
  · intro w c hc
    apply le_antisymm
    · have hInv :
          (((c⁻¹ : ℝ) : EReal) * horizonFunction f (c • w)) ≤ horizonFunction f w := by
        simpa [smul_smul, hc.ne'] using
          smul_horizonFunction_le (f := f) (w := c • w) (c := c⁻¹) (inv_pos_of_pos hc)
      have hmul :
          (c : EReal) * ((((c⁻¹ : ℝ) : EReal) * horizonFunction f (c • w))) ≤
            (c : EReal) * horizonFunction f w := by
        gcongr
      have hhalf : ((c : EReal) * (((c⁻¹ : ℝ) : EReal))) = 1 := by
        rw [← EReal.coe_mul]
        exact_mod_cast (mul_inv_cancel₀ hc.ne' : c * c⁻¹ = (1 : ℝ))
      calc
        horizonFunction f (c • w)
            = (1 : EReal) * horizonFunction f (c • w) := by rw [one_mul]
        _ = (c : EReal) * ((((c⁻¹ : ℝ) : EReal) * horizonFunction f (c • w))) := by
          rw [← mul_assoc, hhalf]
        _ ≤ (c : EReal) * horizonFunction f w := hmul
    · exact smul_horizonFunction_le (f := f) (w := w) hc

/-- The horizon function is finite above at the origin. -/
theorem horizonFunction_zero_lt_top (f : E → EReal) :
    horizonFunction f (0 : E) < ⊤ :=
  (positivelyHomogeneous_horizonFunction f).1

/-- The origin belongs to the effective domain of every horizon function. -/
theorem zero_mem_effectiveDomain_horizonFunction (f : E → EReal) :
    (0 : E) ∈ effectiveDomain (horizonFunction f) := by
  rw [mem_effectiveDomain_iff]
  exact horizonFunction_zero_lt_top f

/-- The effective domain of every horizon function is nonempty. -/
theorem effectiveDomain_horizonFunction_nonempty (f : E → EReal) :
    (effectiveDomain (horizonFunction f)).Nonempty :=
  ⟨0, zero_mem_effectiveDomain_horizonFunction f⟩

/-- The zero lower level set of a horizon function is a cone. -/
theorem isCone_levelSet_zero_horizonFunction (f : E → EReal) :
    IsCone (levelSet (horizonFunction f) (0 : EReal)) :=
  PositivelyHomogeneous.isCone_levelSet_zero
    (positivelyHomogeneous_horizonFunction f)

/-- Strict positivity of the horizon function away from `0` makes its zero
lower level set the singleton `{0}`. -/
theorem levelSet_horizonFunction_zero_eq_singleton_zero_of_pos
    {f : E → EReal}
    (hpos : ∀ ⦃w : E⦄, w ≠ 0 → 0 < horizonFunction f w) :
    levelSet (horizonFunction f) (0 : EReal) = ({0} : Set E) := by
  apply le_antisymm
  · intro w hw
    by_contra hw0
    have hstrict := hpos hw0
    have hle : horizonFunction f w ≤ 0 := by
      simpa [levelSet] using hw
    exact not_le_of_gt hstrict hle
  · intro w hw
    simp at hw
    subst hw
    simpa [levelSet] using (positivelyHomogeneous_horizonFunction f).map_zero_le_zero

/-- Positivity of the horizon function away from `0` is equivalent to its zero
lower level set being the singleton `{0}`. -/
theorem horizonFunction_pos_iff_levelSet_zero_eq_singleton_zero
    (f : E → EReal) :
    (∀ ⦃w : E⦄, w ≠ 0 → 0 < horizonFunction f w) ↔
      levelSet (horizonFunction f) (0 : EReal) = ({0} : Set E) := by
  constructor
  · exact levelSet_horizonFunction_zero_eq_singleton_zero_of_pos
  · intro hlevel w hw
    have hw_not_level : w ∉ levelSet (horizonFunction f) (0 : EReal) := by
      rw [hlevel]
      simpa using hw
    exact not_le.mp <| by
      intro hle
      exact hw_not_level (by simpa [levelSet] using hle)

/-- A horizon direction of a lower level set yields the corresponding horizontal
direction in the horizon cone of the epigraph. -/
theorem prod_zero_mem_horizonCone_epigraph_of_mem_horizonCone_levelSet
    {f : E → EReal} {α : ℝ} {w : E}
    (hw : w ∈ horizonCone (levelSet f α)) :
    (w, (0 : ℝ)) ∈ horizonCone (epigraph f) := by
  rcases hw with rfl | hw
  · exact (zero_mem_horizonCone (epigraph f) : (0 : E × ℝ) ∈ horizonCone (epigraph f))
  · refine Set.mem_insert_of_mem 0 ?_
    rw [mem_asymptoticCone_iff] at ⊢
    rw [mem_asymptoticCone_iff, AffineSpace.asymptoticNhds_eq_smul, ← map₂_smul,
      ← map_prod_eq_map₂, frequently_map] at hw
    have hg :
        Tendsto (fun p : ℝ × E => (p.2, α / p.1))
          (atTop ×ˢ 𝓝 w) (𝓝 (w, (0 : ℝ))) := by
      have hdiv : Tendsto (fun p : ℝ × E => α / p.1)
          (atTop ×ˢ 𝓝 w) (𝓝 (0 : ℝ)) := by
        simpa [div_eq_mul_inv] using
          (tendsto_const_nhds (x := α)).mul (tendsto_inv_atTop_zero.comp tendsto_fst)
      simpa [nhds_prod_eq] using tendsto_snd.prodMk hdiv
    have hsmul :
        Tendsto (fun p : ℝ × E => p.1 • ((p.2, α / p.1) : E × ℝ))
          (atTop ×ˢ 𝓝 w) (asymptoticNhds ℝ (E × ℝ) (w, (0 : ℝ))) :=
      tendsto_fst.atTop_smul_nhds_tendsto_asymptoticNhds hg
    refine hsmul.frequently ?_
    have hw' :
        ∃ᶠ p : ℝ × E in atTop ×ˢ 𝓝 w, p.1 • p.2 ∈ levelSet f α ∧ 0 < p.1 := by
      exact hw.and_eventually (tendsto_fst.eventually (eventually_gt_atTop (0 : ℝ)))
    refine hw'.mono ?_
    intro p hp
    rcases hp with ⟨hp, hp0⟩
    rcases p with ⟨t, u⟩
    have hp_epi : (t • u, α) ∈ epigraph f := by
      rw [mem_epigraph_iff]
      simpa [levelSet] using hp
    have hreal : t * (α / t) = α := by
      field_simp [hp0.ne']
    have hcalc : t • ((u, α / t) : E × ℝ) = (t • u, α) := by
      ext <;> simp [Prod.smul_mk, smul_eq_mul, hreal]
    simpa [hcalc] using hp_epi

/-- **Proposition 3.23** (inclusion): the horizon cone of a lower level set is
contained in the zero sublevel set of the horizon function. -/
theorem horizonCone_levelSet_subset_levelSet_horizonFunction
    (f : E → EReal) (α : ℝ) :
    horizonCone (levelSet f α) ⊆ levelSet (horizonFunction f) (0 : EReal) := by
  intro w hw
  have hprod :
      (w, (0 : ℝ)) ∈ horizonCone (epigraph f) :=
    prod_zero_mem_horizonCone_epigraph_of_mem_horizonCone_levelSet (f := f) (α := α) hw
  simpa [levelSet] using
    horizonFunction_le_of_mem_horizonCone_epigraph (f := f) (w := w) (a := 0) hprod

/-- **Proposition 3.23** (equality case): for a convex lsc function with a
nonempty lower level set, the horizon cone of that level set is exactly the zero
sublevel set of the horizon function. -/
theorem horizonCone_levelSet_eq_levelSet_horizonFunction
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    {α : ℝ} (hlevel : (levelSet f α).Nonempty) :
    horizonCone (levelSet f α) = levelSet (horizonFunction f) (0 : EReal) := by
  refine le_antisymm
    (horizonCone_levelSet_subset_levelSet_horizonFunction (f := f) α) ?_
  intro w hw
  rcases hlevel with ⟨xbar, hxbar⟩
  have hxbar_epi : (xbar, α) ∈ epigraph f := by
    rw [mem_epigraph_iff]
    simpa [levelSet] using hxbar
  have hep_nonempty : (epigraph f).Nonempty := ⟨(xbar, α), hxbar_epi⟩
  have hwh : (w, (0 : ℝ)) ∈ horizonCone (epigraph f) := by
    have hmem : (w, (0 : ℝ)) ∈ epigraph (horizonFunction f) := by
      rw [mem_epigraph_iff]
      simpa [levelSet] using hw
    simpa [epigraph_horizonFunction_eq_horizonCone_epigraph hep_nonempty] using hmem
  refine mem_horizonCone_of_forall_smul_add_mem (C := levelSet f α) (x := xbar) (w := w) ?_
  intro τ hτ
  have hray :
      τ • (w, (0 : ℝ)) + (xbar, α) ∈ epigraph f :=
    smul_add_mem_of_mem_horizonCone (C := epigraph f) hconv
      (isClosed_epigraph_of_lsc_ereal f hlsc) hxbar_epi hwh hτ
  rw [levelSet]
  rw [mem_epigraph_iff] at hray
  simpa [Prod.smul_mk, smul_eq_mul] using hray

/-- If a convex lsc function has one nonempty bounded lower level set, then it
is level-bounded. This is the consequence highlighted after Proposition 3.23. -/
theorem isLevelBounded_of_nonempty_bounded_levelSet [FiniteDimensional ℝ E]
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    {α : ℝ} (hlevel : (levelSet f α).Nonempty) (hbounded : Bornology.IsBounded (levelSet f α)) :
    IsLevelBounded f := by
  have hzero : levelSet (horizonFunction f) (0 : EReal) = ({0} : Set E) := by
    calc
      levelSet (horizonFunction f) (0 : EReal) = horizonCone (levelSet f α) := by
        symm
        exact horizonCone_levelSet_eq_levelSet_horizonFunction hconv hlsc hlevel
      _ = ({0} : Set E) := (isBounded_iff_horizonCone_eq_singleton_zero).mp hbounded
  intro β
  refine (isBounded_iff_horizonCone_eq_singleton_zero).2 ?_
  apply le_antisymm
  · intro x hx
    have hx0 : x ∈ levelSet (horizonFunction f) (0 : EReal) :=
      horizonCone_levelSet_subset_levelSet_horizonFunction (f := f) β hx
    simpa [hzero] using hx0
  · intro x hx
    simp at hx
    simpa [hx] using (zero_mem_horizonCone (levelSet f β))

/-- A proper function has a nonempty real epigraph. -/
theorem epigraph_nonempty_of_isProper {f : E → EReal} (hf : IsProper f) :
    (epigraph f).Nonempty := by
  rcases hf.1 with ⟨x, hx⟩
  have hbot : f x ≠ ⊥ := ne_of_gt (hf.2 x)
  have htop : f x ≠ ⊤ := ne_of_lt hx
  refine ⟨(x, (f x).toReal), ?_⟩
  rw [mem_epigraph_iff]
  simpa [EReal.coe_toReal htop hbot] using (le_rfl : f x ≤ f x)

/-- Proper-function form of the epigraph identity in Definition 3.17:
`epi(f∞) = (epi f)∞`. -/
theorem epigraph_horizonFunction_eq_horizonCone_epigraph_of_isProper {f : E → EReal}
    (hf : IsProper f) :
    epigraph (horizonFunction f) = horizonCone (epigraph f) :=
  epigraph_horizonFunction_eq_horizonCone_epigraph (epigraph_nonempty_of_isProper hf)

/-- Proper-function membership form of the horizon-function epigraph identity. -/
theorem mem_epigraph_horizonFunction_iff_mem_horizonCone_epigraph_of_isProper
    {f : E → EReal} (hf : IsProper f) {p : E × ℝ} :
    p ∈ epigraph (horizonFunction f) ↔ p ∈ horizonCone (epigraph f) := by
  rw [epigraph_horizonFunction_eq_horizonCone_epigraph_of_isProper hf]

/-- For proper functions, membership of `(w,a)` in `(epi f)∞` is exactly the
bound `f∞(w) ≤ a`. -/
theorem mem_horizonCone_epigraph_iff_horizonFunction_le_of_isProper
    {f : E → EReal} (hf : IsProper f) {w : E} {a : ℝ} :
    (w, a) ∈ horizonCone (epigraph f) ↔ horizonFunction f w ≤ (a : EReal) := by
  constructor
  · exact horizonFunction_le_of_mem_horizonCone_epigraph
  · intro hle
    have hmem : (w, a) ∈ epigraph (horizonFunction f) := by
      rw [mem_epigraph_iff]
      exact hle
    simpa [epigraph_horizonFunction_eq_horizonCone_epigraph_of_isProper hf] using hmem

/-- If `f∞(w) ≤ 0`, then `(w,0)` belongs to the horizon cone of `epi f` as soon
as `epi f` is nonempty. -/
theorem mem_horizonCone_epigraph_zero_of_horizonFunction_nonpos
    {f : E → EReal} (hf : (epigraph f).Nonempty) {w : E}
    (hw : horizonFunction f w ≤ 0) :
    (w, (0 : ℝ)) ∈ horizonCone (epigraph f) := by
  have hmem : (w, (0 : ℝ)) ∈ epigraph (horizonFunction f) := by
    rw [mem_epigraph_iff]
    simpa using hw
  simpa [epigraph_horizonFunction_eq_horizonCone_epigraph hf] using hmem

/-- If a ray lies in a finite lower level set of `f`, then the horizon function
is nonpositive along its direction. -/
theorem horizonFunction_nonpos_of_boundedAbove_on_ray
    {f : E → EReal} {x w : E} {α : ℝ}
    (h : ∀ ⦃τ : ℝ⦄, 0 ≤ τ → f (τ • w + x) ≤ α) :
    horizonFunction f w ≤ 0 := by
  have hwcone : w ∈ horizonCone (levelSet f α) := by
    refine mem_horizonCone_of_forall_smul_add_mem (C := levelSet f α) (x := x) (w := w) ?_
    intro τ hτ
    rw [levelSet]
    exact h hτ
  exact horizonCone_levelSet_subset_levelSet_horizonFunction (f := f) α hwcone

/-- If `f` is proper, lsc, and convex, then any direction `w` with `f∞(w) ≤ 0`
is nonincreasing along every ray. -/
theorem apply_smul_add_le_of_horizonFunction_nonpos
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) {x w : E} (hw : horizonFunction f w ≤ 0)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    f (τ • w + x) ≤ f x := by
  by_cases htop : f x = ⊤
  · simpa [htop] using (le_top : f (τ • w + x) ≤ ⊤)
  · have hbot : f x ≠ ⊥ := ne_of_gt (hproper.2 x)
    have hx_epi : (x, (f x).toReal) ∈ epigraph f := by
      rw [mem_epigraph_iff]
      simpa [EReal.coe_toReal htop hbot] using (le_rfl : f x ≤ f x)
    have hwh : (w, (0 : ℝ)) ∈ horizonCone (epigraph f) :=
      mem_horizonCone_epigraph_zero_of_horizonFunction_nonpos
        (epigraph_nonempty_of_isProper hproper) hw
    have hray :
        τ • (w, (0 : ℝ)) + (x, (f x).toReal) ∈ epigraph f :=
      smul_add_mem_of_mem_horizonCone (C := epigraph f) hconv
        (isClosed_epigraph_of_lsc_ereal f hlsc) hx_epi hwh hτ
    rw [mem_epigraph_iff] at hray
    simpa [Prod.smul_mk, smul_eq_mul, EReal.coe_toReal htop hbot] using hray

/-- **Corollary 3.22**: if a proper lsc convex function is bounded above on one
half-line of direction `w`, then it is nonincreasing on every line parallel to
`w`. -/
theorem monotoneOn_lines_of_boundedAbove_ray
    {f : E → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) {xbar w : E} {α : ℝ}
    (hupper : ∀ ⦃τ : ℝ⦄, 0 ≤ τ → f (τ • w + xbar) ≤ α) :
    ∀ ⦃x : E⦄ ⦃τ τ' : ℝ⦄, τ ≤ τ' → f (τ' • w + x) ≤ f (τ • w + x) := by
  have hw : horizonFunction f w ≤ 0 :=
    horizonFunction_nonpos_of_boundedAbove_on_ray (x := xbar) (w := w) (α := α) hupper
  intro x τ τ' hττ'
  have hδ : 0 ≤ τ' - τ := sub_nonneg.mpr hττ'
  simpa [← add_assoc, ← add_smul, sub_add_cancel] using
    (apply_smul_add_le_of_horizonFunction_nonpos hconv hlsc hproper
      (x := τ • w + x) (w := w) hw (τ := τ' - τ) hδ)

/-- The sequence-to-direction hypothesis in **Corollary 3.22** forces the
corresponding horizon value to be nonpositive.  The book writes
`xν → dir w`; in the closed-ball model a direction is represented by a unit
vector `u : CosmicBoundary E`. -/
theorem horizonFunction_nonpos_of_boundedAbove_cosmicSequence
    {f : E → EReal} {x : ℕ → E} {u : CosmicBoundary E} {α : ℝ}
    (hcosmic :
      Tendsto (fun n ↦ cosmicEmbed (x n)) atTop
        (𝓝 (cosmicDirection u)))
    (hupper : ∀ n, f (x n) ≤ α) :
    horizonFunction f (u : E) ≤ 0 := by
  have hu :
      (u : E) ∈ horizonCone (levelSet f α) :=
    mem_horizonCone_of_tendsto_cosmicDirection
      (C := levelSet f α) (x := x) (u := u)
      (fun n ↦ by simpa [levelSet] using hupper n) hcosmic
  simpa [levelSet] using
    horizonCone_levelSet_subset_levelSet_horizonFunction
      (f := f) α hu

/-- **Corollary 3.22** (sequence-to-direction form): if a sequence converges
cosmically to `dir u` while its function values stay bounded above, then a
proper lsc convex function is nonincreasing on every line parallel to `u`. -/
theorem monotoneOn_lines_of_boundedAbove_cosmicSequence
    {f : E → EReal} (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    {xseq : ℕ → E} {u : CosmicBoundary E} {α : ℝ}
    (hcosmic :
      Tendsto (fun n ↦ cosmicEmbed (xseq n)) atTop
        (𝓝 (cosmicDirection u)))
    (hupper : ∀ n, f (xseq n) ≤ α) :
    ∀ ⦃x : E⦄ ⦃τ τ' : ℝ⦄, τ ≤ τ' →
      f (τ' • (u : E) + x) ≤ f (τ • (u : E) + x) := by
  have hu : horizonFunction f (u : E) ≤ 0 :=
    horizonFunction_nonpos_of_boundedAbove_cosmicSequence hcosmic hupper
  intro x τ τ' hττ'
  have hδ : 0 ≤ τ' - τ := sub_nonneg.mpr hττ'
  simpa [← add_assoc, ← add_smul, sub_add_cancel] using
    (apply_smul_add_le_of_horizonFunction_nonpos hconv hlsc hproper
      (x := τ • (u : E) + x) (w := (u : E)) hu
      (τ := τ' - τ) hδ)

end RW
