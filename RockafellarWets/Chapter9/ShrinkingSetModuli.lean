/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Joint shrinking-radius formulas for graphical Lipschitz moduli
-/

import RockafellarWets.Chapter9.AubinTranslatedDistances

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E : Type*} [MetricSpace E]

/-- A local two-point bound at one positive output radius. -/
noncomputable def shrinkingPairModulusWithin (q : ℝ≥0 → E → E → ℝ≥0∞) (X : Set E) (x : E) : ℝ≥0∞ :=
  ⨅ k : {k : ℝ≥0 // ∃ r : ℝ≥0, 0 < r ∧ ∃ U ∈ 𝓝[X] x,
    ∀ a ∈ U, ∀ b ∈ U, q r a b ≤ (k:ℝ≥0∞)*edist a b}, ((k:ℝ≥0):ℝ≥0∞)

theorem shrinkingPairModulusWithin_le {q : ℝ≥0 → E → E → ℝ≥0∞} {X U : Set E} {x : E}
    {k r : ℝ≥0} (hr : 0 < r) (hU : U ∈ 𝓝[X] x)
    (h : ∀ a ∈ U, ∀ b ∈ U, q r a b ≤ (k:ℝ≥0∞)*edist a b) :
    shrinkingPairModulusWithin q X x ≤ (k:ℝ≥0∞) :=
  iInf_le (fun c : {c : ℝ≥0 // ∃ r : ℝ≥0, 0 < r ∧ ∃ U ∈ 𝓝[X] x,
    ∀ a ∈ U, ∀ b ∈ U, q r a b ≤ (c:ℝ≥0∞)*edist a b} ↦ ((c:ℝ≥0):ℝ≥0∞)) ⟨k,r,hr,U,hU,h⟩

/-- The infimum of constants valid at one positive radius is a joint limsup
as the input pair approaches the base point and the output radius decreases to zero. -/
theorem shrinkingPairModulusWithin_eq_limsup (q : ℝ≥0 → E → E → ℝ≥0∞) (X : Set E) (x : E)
    (hself : ∀ r a, q r a a = 0) (hmono : ∀ a b, Monotone (fun r ↦ q r a b)) :
    shrinkingPairModulusWithin q X x =
      limsup (fun p : (E × E) × ℝ≥0 ↦ q p.2 p.1.1 p.1.2 / edist p.1.1 p.1.2)
        (((𝓝[X] x ×ˢ 𝓝[X] x) ×ˢ 𝓝[>] (0:ℝ≥0)) ⊓ 𝓟 {p : (E × E) × ℝ≥0 | p.1.1 ≠ p.1.2}) := by
  apply le_antisymm
  · by_contra! h
    obtain ⟨k,hk,hk'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    have hb := eventually_lt_of_limsup_lt hk
    obtain ⟨P,hP,R,hR,hPR⟩ := mem_prod_iff.mp (eventually_inf_principal.mp hb)
    obtain ⟨U,hU,V,hV,hUV⟩ := mem_prod_iff.mp hP
    obtain ⟨r,hrR,hr⟩ := ((eventually_mem_set.mpr hR).and self_mem_nhdsWithin).exists
    apply hk'.not_ge (shrinkingPairModulusWithin_le hr (inter_mem hU hV) ?_)
    intro a ha b hb'
    rcases eq_or_ne a b with rfl | hab
    · simp [hself]
    · exact (ENNReal.div_le_iff (edist_eq_zero.not.mpr hab) (edist_ne_top a b)).mp
        ((hPR (a := ((a,b),r)) ⟨hUV ⟨ha.1,hb'.2⟩,hrR⟩ hab).le)
  · refine le_iInf fun k ↦ ?_
    obtain ⟨r,hr,U,hU,H⟩ := k.property
    apply limsup_le_of_le (by isBoundedDefault)
    apply eventually_inf_principal.mpr
    have hrad : ∀ᶠ t : ℝ≥0 in 𝓝[>] (0:ℝ≥0), t < r :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)
    filter_upwards [(tendsto_fst.comp tendsto_fst).eventually hU,
      (tendsto_snd.comp tendsto_fst).eventually hU,tendsto_snd.eventually hrad] with p ha hb hp _
    exact ENNReal.div_le_of_le_mul ((hmono _ _ hp.le).trans (H _ ha _ hb))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {X : Set E} {x : E} {u : F}

/-- The graphical modulus is the infimum of constants valid for one
positive-radius translated inclusion distance. -/
theorem graphicalLipschitzModulusWithin_eq_shrinking_rhoHat :
    graphicalLipschitzModulusWithin S X x u =
      shrinkingPairModulusWithin (fun r a b ↦ rhoHatEDistance r (svTranslate S u a) (svTranslate S u b)) X x := by
  rw [graphicalLipschitzModulusWithin_eq_iInf_rhoHat]
  apply le_antisymm
  · refine le_iInf fun k ↦ ?_
    obtain ⟨r,hr,U,hU,H⟩ := k.property
    obtain ⟨V,hV,hVU⟩ := eventually_nhdsWithin_iff_exists_nhds.mp hU
    have hk : AubinRhoHatEstimate S X x u k.val := ⟨r,hr,V,hV,fun a ha b hb ↦ by
      simpa only [edist_dist,ENNReal.ofReal_mul (p := (k.val:ℝ)) (q := dist a b) k.val.2,ENNReal.ofReal_coe_nnreal] using H a (hVU a ha) b (hVU b hb)⟩
    exact iInf_le (fun c : {c : ℝ≥0 // AubinRhoHatEstimate S X x u c} ↦ ((c:ℝ≥0):ℝ≥0∞)) ⟨k.val,hk⟩
  · refine le_iInf fun k ↦ ?_
    obtain ⟨r,hr,V,hV,H⟩ := k.property
    apply shrinkingPairModulusWithin_le hr (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV))
    intro a ha b hb
    simpa only [edist_dist,ENNReal.ofReal_mul (p := (k.val:ℝ)) (q := dist a b) k.val.2,ENNReal.ofReal_coe_nnreal] using H a ha b hb

/-- **Exercise 9.37**, the shrinking-radius inclusion-distance limsup.
The formula also holds for relative domains and isolated input points. -/
theorem graphicalLipschitzModulusWithin_eq_limsup_rhoHat :
    graphicalLipschitzModulusWithin S X x u =
      limsup (fun p : (E × E) × ℝ≥0 ↦
        rhoHatEDistance p.2 (svTranslate S u p.1.1) (svTranslate S u p.1.2) / edist p.1.1 p.1.2)
        (((𝓝[X] x ×ˢ 𝓝[X] x) ×ˢ 𝓝[>] (0:ℝ≥0)) ⊓ 𝓟 {p : (E × E) × ℝ≥0 | p.1.1 ≠ p.1.2}) := by
  rw [graphicalLipschitzModulusWithin_eq_shrinking_rhoHat]
  apply shrinkingPairModulusWithin_eq_limsup
  · intro r a
    apply nonpos_iff_eq_zero.mp
    rw [rhoHatEDistance,sup_le_iff]
    exact ⟨iSup_le fun v ↦ iSup_le fun hv ↦ (infEDist_zero_of_mem hv.1).le,
      iSup_le fun v ↦ iSup_le fun hv ↦ (infEDist_zero_of_mem hv.1).le⟩
  · intro a b r s hrs
    exact rhoHatEDistance_mono hrs _ _

/-- The translated profile constants have the same exact infimum. -/
theorem graphicalLipschitzModulusWithin_eq_iInf_rho (hx : x ∈ X) (hu : u ∈ S x) :
    graphicalLipschitzModulusWithin S X x u =
      ⨅ k : {k : ℝ≥0 // AubinRhoEstimate S X x u k}, ((k : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · refine le_iInf fun k ↦ ?_
    rw [graphicalLipschitzModulusWithin_eq_iInf_profiles hx hu]
    exact iInf_le (fun a : {a : ℝ≥0 // AubinProfileEstimate S X x u a} ↦ ((a:ℝ≥0):ℝ≥0∞))
      ⟨k.val,aubinProfileEstimate_iff_rhoEstimate.mpr k.property⟩
  · refine le_iInf fun k ↦ ?_
    exact iInf_le (fun a : {a : ℝ≥0 // AubinRhoEstimate S X x u a} ↦ ((a:ℝ≥0):ℝ≥0∞))
      ⟨k.val,aubinProfileEstimate_iff_rhoEstimate.mp (k.property.profileEstimate hx hu)⟩

/-- Nonempty nearby fibers identify the real distance-profile formulation
with the joint positive-radius modulus. -/
theorem graphicalLipschitzModulusWithin_eq_shrinking_rho (hx : x ∈ X) (hu : u ∈ S x)
    (hne : ∀ᶠ a in 𝓝[X] x, (S a).Nonempty) :
    graphicalLipschitzModulusWithin S X x u =
      shrinkingPairModulusWithin (fun r a b ↦ ENNReal.ofReal (rhoDistance r (svTranslate S u a) (svTranslate S u b))) X x := by
  rw [graphicalLipschitzModulusWithin_eq_iInf_rho hx hu]
  apply le_antisymm
  · refine le_iInf fun k ↦ ?_
    obtain ⟨r,hr,U,hU,H⟩ := k.property
    obtain ⟨V,hV,hVU⟩ := eventually_nhdsWithin_iff_exists_nhds.mp (inter_mem hU hne)
    have hk : AubinRhoEstimate S X x u k.val := ⟨r,hr,V,hV,
      fun a ha ↦ (hVU a ha).2,fun a ha b hb ↦ by
        apply (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ (k.val:ℝ)*dist a b from mul_nonneg k.val.2 dist_nonneg)).mp
        simpa only [edist_dist,ENNReal.ofReal_mul (p := (k.val:ℝ)) (q := dist a b) k.val.2,
          ENNReal.ofReal_coe_nnreal] using H a (hVU a ha).1 b (hVU b hb).1⟩
    exact iInf_le (fun c : {c : ℝ≥0 // AubinRhoEstimate S X x u c} ↦ ((c:ℝ≥0):ℝ≥0∞)) ⟨k.val,hk⟩
  · refine le_iInf fun k ↦ ?_
    obtain ⟨r,hr,V,hV,_,H⟩ := k.property
    apply shrinkingPairModulusWithin_le hr (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV))
    intro a ha b hb
    simpa only [edist_dist,ENNReal.ofReal_mul (p := (k.val:ℝ)) (q := dist a b) k.val.2,
      ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (H a ha b hb)

/-- **Exercise 9.37**, the shrinking-radius distance-profile limsup.
Nonempty fibers make real point-to-set distances agree with their extended values. -/
theorem graphicalLipschitzModulusWithin_eq_limsup_rho (hx : x ∈ X) (hu : u ∈ S x)
    (hne : ∀ᶠ a in 𝓝[X] x, (S a).Nonempty) :
    graphicalLipschitzModulusWithin S X x u =
      limsup (fun p : (E × E) × ℝ≥0 ↦
        ENNReal.ofReal (rhoDistance p.2 (svTranslate S u p.1.1) (svTranslate S u p.1.2)) / edist p.1.1 p.1.2)
        (((𝓝[X] x ×ˢ 𝓝[X] x) ×ˢ 𝓝[>] (0:ℝ≥0)) ⊓ 𝓟 {p : (E × E) × ℝ≥0 | p.1.1 ≠ p.1.2}) := by
  rw [graphicalLipschitzModulusWithin_eq_shrinking_rho hx hu hne]
  apply shrinkingPairModulusWithin_eq_limsup
  · intro r a
    simp only [rhoDistance_self,ENNReal.ofReal_zero]
  · intro a b r s hrs
    exact ENNReal.ofReal_le_ofReal (rhoDistance_mono hrs _ _)

end RW
