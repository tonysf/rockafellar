/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epi-convergence from extended uniform convergence
-/

import RockafellarWets.Chapter7.ExtendedUniformConvergence
import RockafellarWets.Chapter7.EpiLimits
import RockafellarWets.Chapter5.GraphicalFromUniform

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [PseudoMetricSpace E] {f : ℕ → E → EReal} {g : E → EReal} {X : Set E}

/-- **Proposition 7.15(a).** Uniform convergence on an arbitrary set
preserves relative lower semicontinuity and gives relative epi-convergence,
expressed by convergence of the epigraphical profiles. -/
theorem ERealConvergesUniformlyOn.lowerSemicontinuousOn_and_epiProfile
    (hu : ERealConvergesUniformlyOn f g X) (hf : ∀ n, LowerSemicontinuousOn (f n) X) :
    LowerSemicontinuousOn g X ∧
      GraphicalConvergesOn (fun n ↦ epiProfile (f n)) (epiProfile g) X := by
  have h := erealConvergesUniformlyOn_iff_epiProfile.mp hu
  have ho := fun n ↦ (svOscOn_epiProfile_iff (f n) X).mpr (hf n)
  have hc := fun x (_ : x ∈ X) ↦ isClosed_epiProfile g x
  exact ⟨(svOscOn_epiProfile_iff g X).mp (svOscOn_of_svConvergesUniformlyOn ho h hc),
    graphicalConvergesOn_of_svConvergesUniformlyOn ho h hc⟩

/-- In the whole space the profile conclusion is exactly epigraph convergence. -/
theorem ERealConvergesUniformlyOn.epiConverges_of_lowerSemicontinuous
    (hu : ERealConvergesUniformlyOn f g univ) (hf : ∀ n, LowerSemicontinuous (f n)) :
    EpiConverges f g :=
  epiConverges_iff_graphicalConverges.mpr <| graphicalConvergesOn_univ_iff.mp
    (hu.lowerSemicontinuousOn_and_epiProfile (fun n ↦ (hf n).lowerSemicontinuousOn univ)).2

/-- The finite graph fiber, empty when the value is infinite. -/
def finiteGraphFiber {α : Type*} (h : α → EReal) (x : α) : Set ℝ :=
  {r | (r : EReal) = h x}

/-- Continuous convergence of extended real values also gives graphical
convergence of their finite graph fibers. -/
theorem ConvergesContinuouslyWithinAt.graphicalConvergesWithinAt_finiteGraphFiber
    {x : E} (hx : x ∈ X) (hc : ConvergesContinuouslyWithinAt f g X x) :
    GraphicalConvergesWithinAt (fun n ↦ finiteGraphFiber (f n)) (finiteGraphFiber g) X x := by
  constructor
  · intro t ht
    obtain ⟨z, hz, ht⟩ := mem_graphicalOuterLimitWithin_iff.mp ht
    obtain ⟨φ, r, hφ, hr, hrt⟩ := mem_outerSetLimit_iff_exists_subsequence.mp ht
    have h₁ := (hc z hz.1 hz.2).comp hφ.tendsto_atTop
    have h₂ := continuous_coe_real_ereal.continuousAt.tendsto.comp hrt
    exact tendsto_nhds_unique h₂ (h₁.congr fun n ↦ (hr n).symm)
  · intro t ht
    refine mem_graphicalInnerLimitWithin_iff.mpr ⟨fun _ ↦ x, ⟨fun _ ↦ hx, tendsto_const_nhds⟩, ?_⟩
    have h := hc (fun _ ↦ x) (fun _ ↦ hx) tendsto_const_nhds
    change (t : EReal) = g x at ht
    rw [← ht] at h
    have hr : Tendsto (fun n ↦ (f n x).toReal) atTop (𝓝 t) := by
      simpa using (EReal.tendsto_toReal (EReal.coe_ne_top t) (EReal.coe_ne_bot t)).comp h
    intro V hV
    filter_upwards [hr.eventually_mem hV,
      h.eventually_lt_const (EReal.coe_lt_top t), h.eventually_const_lt (EReal.bot_lt_coe t)]
      with n hn htop hbot
    exact ⟨_, EReal.coe_toReal htop.ne hbot.ne', hn⟩

/-- **Proposition 7.15(b).** A uniform limit of relatively continuous
functions is relatively continuous and is their epi-, hypo-, and graphical
limit. The finite graph convention also covers infinite function values. -/
theorem ERealConvergesUniformlyOn.continuousOn_and_graphicalConvergence
    (hu : ERealConvergesUniformlyOn f g X) (hf : ∀ n, ContinuousOn (f n) X) :
    ContinuousOn g X ∧ GraphicalConvergesOn (fun n ↦ epiProfile (f n)) (epiProfile g) X ∧
      GraphicalConvergesOn (fun n ↦ hypoProfile (f n)) (hypoProfile g) X ∧
      GraphicalConvergesOn (fun n ↦ finiteGraphFiber (f n)) (finiteGraphFiber g) X := by
  obtain ⟨hl, hepi⟩ := hu.lowerSemicontinuousOn_and_epiProfile
    (fun n ↦ (hf n).lowerSemicontinuousOn)
  have h := erealConvergesUniformlyOn_iff_hypoProfile.mp hu
  have ho (n : ℕ) : SvOscOn (hypoProfile (f n)) X := fun x hx ↦
    (svOscWithinAt_hypoProfile_iff _ X x).mpr ((hf n).upperSemicontinuousOn x hx)
  have hcl := fun x (_ : x ∈ X) ↦ isClosed_hypoProfile g x
  have hupper : UpperSemicontinuousOn g X := fun x hx ↦
    (svOscWithinAt_hypoProfile_iff g X x).mp (svOscOn_of_svConvergesUniformlyOn ho h hcl x hx)
  have hc : ContinuousOn g X := continuousOn_iff_lower_upperSemicontinuousOn.mpr ⟨hl, hupper⟩
  have hcont := convergesContinuouslyOn_iff_continuousOn_and_erealConvergesUniformlyOn.mpr
    ⟨hc, fun _ hBX _ r hr ↦ (hu r hr).mono hBX⟩
  exact ⟨hc, hepi, graphicalConvergesOn_of_svConvergesUniformlyOn ho h hcl,
    fun x hx ↦ (hcont x hx).graphicalConvergesWithinAt_finiteGraphFiber hx⟩

end RW
