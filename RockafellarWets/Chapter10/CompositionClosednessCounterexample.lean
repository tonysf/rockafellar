/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closedness missing from the strict-continuity composition claim

In Corollary 10.38 and Exercise 10.39, the Aubin conclusions are local to
graph points. They do not imply the claimed strict continuity of the full
mapping: S(x)=ℝ and F(w)=exp(w) have composition (0,∞), which is not closed.
All intermediate fibers are locally bounded at graph points. Definition 9.28
explicitly requires closed-valuedness near the base point.
-/

import RockafellarWets.Chapter10.CompositionModulusMax
import RockafellarWets.Chapter9.SingleValuedGraphicalDerivatives
import RockafellarWets.Chapter9.SmoothLipschitzModulus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

theorem svStrictlyContinuousAt_const {E F : Type*} [MetricSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {C : Set F} (hne : C.Nonempty) (hc : IsClosed C) (x : E) :
    SvStrictlyContinuousAt (fun _ : E ↦ C) x := by
  refine ⟨mem_univ _,Eventually.of_forall (fun _ ↦ ⟨hne,hc⟩),fun r ↦ ?_⟩
  exact (lipschitzModulusWithin_le (U := univ) univ_mem
    (LipschitzWith.const (distanceProfile r C)).lipschitzOnWith).trans_lt ENNReal.coe_lt_top

theorem svOsc_exponentialMapping : SvOsc (svSingleton Real.exp) :=
  fun x ↦ svOscAt_svSingleton_of_continuousAt Real.continuous_exp.continuousAt

theorem svStrictlyContinuousAt_exponentialMapping (w : ℝ) :
    SvStrictlyContinuousAt (svSingleton Real.exp) w := by
  apply (svStrictlyContinuousAt_iff_osc_aubin (fun _ ↦ isClosed_singleton) (singleton_nonempty _)).mpr
  refine ⟨svOsc_exponentialMapping w,?_⟩
  intro u hu
  rw [mem_singleton_iff] at hu
  subst u
  exact (strictlyContinuousAt_of_contDiffAt Real.contDiff_exp.contDiffAt).hasAubinProperty_singleton

theorem exponentialComposition_eq (x : ℝ) :
    svComp (svSingleton Real.exp) (fun _ : ℝ ↦ (univ : Set ℝ)) x = Ioi 0 := by
  ext u
  simp only [mem_svComp,mem_univ,true_and,svSingleton,mem_singleton_iff,mem_Ioi]
  constructor
  · rintro ⟨w,rfl⟩
    exact Real.exp_pos w
  · intro hu
    exact ⟨Real.log u,(Real.exp_log hu).symm⟩

theorem exponentialComposition_locallyBounded_intermediates {x u : ℝ} (hu : 0 < u) :
    SvLocallyBoundedAt (svCompAux (svSingleton Real.exp) (fun _ : ℝ ↦ (univ : Set ℝ))) (x,u) := by
  refine ⟨univ ×ˢ Ioo (u/2) (2*u),prod_mem_nhds univ_mem (Ioo_mem_nhds (by linarith) (by linarith)),?_⟩
  apply (isBounded_Icc (a := Real.log (u/2)) (b := Real.log (2*u))).subset
  intro w hw
  obtain ⟨p,hp,hw⟩ := mem_svImage.mp hw
  have he : p.2 = Real.exp w := hw.2
  change True ∧ u/2 < p.2 ∧ p.2 < 2*u at hp
  rw [he] at hp
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (by linarith : 0 < u/2) hp.2.1.le
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos w) hp.2.2.le

theorem not_svStrictlyContinuousAt_exponentialComposition (x : ℝ) :
    ¬ SvStrictlyContinuousAt (svComp (svSingleton Real.exp) (fun _ : ℝ ↦ (univ : Set ℝ))) x := by
  intro h
  have hh : ∀ᶠ a in 𝓝 x,
      (svComp (svSingleton Real.exp) (fun _ : ℝ ↦ (univ : Set ℝ)) a).Nonempty ∧
      IsClosed (svComp (svSingleton Real.exp) (fun _ : ℝ ↦ (univ : Set ℝ)) a) := by
    simpa only [nhdsWithin_univ] using h.2.1
  have hc := (mem_of_mem_nhds hh).2
  rw [exponentialComposition_eq] at hc
  have hz : (0:ℝ) ∈ closure (Ioi (0:ℝ)) := by rw [closure_Ioi]; exact (le_rfl : (0:ℝ) ≤ 0)
  have := hc.closure_eq ▸ hz
  exact (lt_irrefl (0:ℝ)) this

/-- All printed hypotheses hold, including bounded intermediate fibers at
every output in the composition, while its strict continuity fails. -/
theorem strict_continuity_composition_counterexample :
    SvOsc (fun _ : ℝ ↦ (univ : Set ℝ)) ∧ SvOsc (svSingleton Real.exp) ∧
    SvStrictlyContinuousAt (fun _ : ℝ ↦ (univ : Set ℝ)) 0 ∧
    (∀ w : ℝ, SvStrictlyContinuousAt (svSingleton Real.exp) w) ∧
    (∀ u ∈ svComp (svSingleton Real.exp) (fun _ : ℝ ↦ (univ : Set ℝ)) 0,
      SvLocallyBoundedAt (svCompAux (svSingleton Real.exp) (fun _ : ℝ ↦ (univ : Set ℝ))) (0,u)) ∧
    ¬ SvStrictlyContinuousAt (svComp (svSingleton Real.exp) (fun _ : ℝ ↦ (univ : Set ℝ))) 0 := by
  exact ⟨fun x ↦ svOscAt_const isClosed_univ x,svOsc_exponentialMapping,
    svStrictlyContinuousAt_const (univ_nonempty : (univ : Set ℝ).Nonempty) isClosed_univ (0:ℝ),
    svStrictlyContinuousAt_exponentialMapping,fun u hu ↦
      exponentialComposition_locallyBounded_intermediates (by simpa only [exponentialComposition_eq] using hu),
    not_svStrictlyContinuousAt_exponentialComposition 0⟩

end RW
