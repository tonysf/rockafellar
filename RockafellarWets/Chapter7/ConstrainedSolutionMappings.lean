/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fixed constraints and convex solution mappings
-/

import RockafellarWets.Chapter7.OptimalSetContinuity
import RockafellarWets.Chapter2.Defs

open Bornology Filter Metric Set Topology

namespace RW

/-- Extend an objective restricted to a constraint set by the value `+∞`. -/
noncomputable def constrainedObjective {A : Type*} (f : A → EReal) (C : Set A) (x : A) : EReal :=
  by classical exact if x ∈ C then f x else ⊤

theorem lowerSemicontinuous_constrainedObjective {A : Type*} [TopologicalSpace A]
    {f : A → EReal} {C : Set A} (hC : IsClosed C) (hf : LowerSemicontinuousOn f C) :
    LowerSemicontinuous (constrainedObjective f C) := by
  classical
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  rcases eq_or_lt_of_le (le_top (a := a)) with rfl | ha
  · simp
  · obtain ⟨V, hV, heq⟩ := lowerSemicontinuousOn_iff_preimage_Iic.1 hf a
    have hcut : constrainedObjective f C ⁻¹' Iic a = C ∩ f ⁻¹' Iic a := by
      ext x
      by_cases hx : x ∈ C <;> simp [constrainedObjective, hx, ha.not_ge]
    rw [hcut, heq]
    exact hC.inter hV

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

omit [NormedSpace ℝ U] in
/-- **Corollary 7.42**, fixed closed decision constraints and a continuous
cost. The cost is used only on `X × D`, where continuity is assumed. -/
theorem fixedConstraint_paramArgmin_regular {X : Set E} {D : Set U}
    (hX : IsClosed X) (hD : IsClosed D) {f₀ : E × U → ℝ} (hc : ContinuousOn f₀ (X ×ˢ D))
    (hb : ∀ B ⊆ D, IsBounded B → ∀ a : ℝ, IsBounded ((X ×ˢ B) ∩ f₀ ⁻¹' Iic a)) :
    let f := constrainedObjective (fun z ↦ (f₀ z : EReal)) (X ×ˢ D)
    SvOscOn (paramArgmin f) D ∧ ∀ u ∈ D, SvLocallyBoundedWithinAt (paramArgmin f) D u := by
  classical
  let f := constrainedObjective (fun z ↦ (f₀ z : EReal)) (X ×ˢ D)
  change SvOscOn (paramArgmin f) D ∧ _
  suffices h : ∀ u ∈ D, SvLocallyBoundedWithinAt (paramArgmin f) D u ∧
      SvOscWithinAt (paramArgmin f) D u from
    ⟨fun u hu ↦ (h u hu).2, fun u hu ↦ (h u hu).1⟩
  intro u hu
  rcases X.eq_empty_or_nonempty with hXe | ⟨x₀, hx₀⟩
  · have he : ∀ v, paramArgmin f v = ∅ := by
      intro v
      simp [paramArgmin, f, constrainedObjective, hXe, argmin_const_top]
    refine ⟨⟨univ, univ_mem, by simp [svImage, he]⟩, ?_⟩
    intro x hx
    obtain ⟨v, y, hy, _⟩ := (hx univ univ_mem).exists
    simp [he] at hy
  have hlsc : LowerSemicontinuous f := lowerSemicontinuous_constrainedObjective (hX.prod hD)
    (continuous_coe_real_ereal.comp_continuousOn hc).lowerSemicontinuousOn
  have hproper : IsProper f := by
    refine ⟨⟨(x₀,u), ?_⟩, fun z ↦ ?_⟩
    · simp [f, constrainedObjective, hx₀, hu]
    · by_cases hz : z ∈ X ×ˢ D <;> simp [f, constrainedObjective, hz]
  have hlb : IsLevelBoundedInXLocallyUniformly f := by
    intro v a
    let B := D ∩ closedBall v 1
    refine ⟨1, one_pos, (hb B inter_subset_left (isBounded_closedBall.subset inter_subset_right) a).subset ?_⟩
    rintro ⟨x,w⟩ ⟨⟨_, hw⟩, hxw⟩
    have hdom : (x,w) ∈ X ×ˢ D := by
      by_contra hnot
      change f (x,w) ≤ (a : EReal) at hxw
      simp only [f, constrainedObjective, if_neg hnot] at hxw
      exact (EReal.coe_lt_top a).not_ge hxw
    change f (x,w) ≤ (a : EReal) at hxw
    exact ⟨⟨hdom.1, hdom.2, hw⟩, EReal.coe_le_coe_iff.1 (by simpa only [f, constrainedObjective, if_pos hdom] using hxw)⟩
  have hfin : valueFunction f u < ⊤ := (iInf_le (fun x ↦ f (x,u)) x₀).trans_lt
    (by simp [f, constrainedObjective, hx₀, hu])
  apply paramArgmin_regular_of_continuousWithinAt hlsc hlb hfin
  apply continuousWithinAt_valueFunction_of_epiContinuousWithinAt hlsc hproper hlb hu hfin
  refine ⟨(epiLscWithinAt_iff_forall_liminf hu).2 (fun vs _ hvs x xs hxs ↦
    (epiLscAt_iff_forall_liminf.1 ((forall_epiLscAt_iff_lowerSemicontinuous f).2 hlsc u))
      vs hvs x xs hxs), (epiUscWithinAt_iff_exists_limsup hu).2 ?_⟩
  intro vs hDvs hvs x
  refine ⟨fun _ ↦ x, tendsto_const_nhds, ?_⟩
  by_cases hx : x ∈ X
  · have hv : Tendsto (fun n ↦ (x,vs n)) atTop (nhdsWithin (x,u) (X ×ˢ D)) :=
      tendsto_nhdsWithin_of_forall_mem (fun n ↦ ⟨hx, hDvs n⟩) (tendsto_const_nhds.prodMk_nhds hvs)
    have ht := EReal.tendsto_coe.2 ((hc (x,u) ⟨hx, hu⟩).tendsto.comp hv)
    simpa [f, constrainedObjective, hx, hu, hDvs, Function.comp_def] using ht.limsup_eq.le
  · simp [f, constrainedObjective, hx]

omit [FiniteDimensional ℝ E] in
/-- On its effective domain a proper objective has ordinary real values.
Strict convexity of these values makes its minimizer set a subsingleton. -/
theorem argmin_subsingleton_of_strictConvexOn {g : E → EReal} (hbot : ∀ x, ⊥ < g x)
    (hsc : StrictConvexOn ℝ (effectiveDomain g) (fun x ↦ (g x).toReal)) : (argmin g).Subsingleton := by
  intro x hx y hy
  have hmin {w : E} (hw : w ∈ argmin g) : ∀ z ∈ effectiveDomain g, (g w).toReal ≤ (g z).toReal :=
    fun z hz ↦ EReal.toReal_le_toReal (hw.1.trans_le (iInf_le g z)) (hbot w).ne' hz.ne
  exact unique_argmin_of_strictConvexOn hsc.1 hsc (hx.1.trans_lt hx.2) (hy.1.trans_lt hy.2) (hmin hx) (hmin hy)

/-- **Corollary 7.43**, with strict convexity of the real values on each
slice's effective domain. There is one optimizer at each feasible parameter
and the optimal-set mapping is continuous in the interior of its domain. -/
theorem strictConvex_paramArgmin_continuity [FiniteDimensional ℝ U] {f : E × U → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hhor : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : U)))
    (hs : ∀ u, StrictConvexOn ℝ (effectiveDomain (fun x ↦ f (x,u))) (fun x ↦ (f (x,u)).toReal)) :
    (∀ u ∈ svDom (paramArgmin f), ∃ x, paramArgmin f u = {x}) ∧
      ∀ u ∈ interior (svDom (paramArgmin f)), SvContinuousAt (paramArgmin f) u := by
  have hb := isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hhor
  have hdom := (paramArgmin_compact_and_dom hl hp hb).2
  have hsingle : ∀ u ∈ svDom (paramArgmin f), ∃ x, paramArgmin f u = {x} := by
    intro u hu
    exact exists_eq_singleton_iff_nonempty_subsingleton.2 ⟨hu,
      argmin_subsingleton_of_strictConvexOn (fun x ↦ hp.2 (x,u)) (hs u)⟩
  refine ⟨hsingle, fun u hu ↦ ?_⟩
  obtain ⟨x, hx⟩ := hsingle u (interior_subset hu)
  let D := interior (svDom (paramArgmin f))
  have hv := (convex_paramArgmin_interior hl hp hb hc (hdom ▸ hu)).1
  have hrel := svContinuousWithinAt_paramArgmin hl hp hb
    (U := D) (fun v h ↦ (show v ∈ effectiveDomain (valueFunction f) by rw [← hdom]; exact interior_subset h)) hu hv.continuousWithinAt hx
  have hnhds : nhdsWithin u D = 𝓝 u := nhdsWithin_eq_nhds.2 (isOpen_interior.mem_nhds hu)
  simpa [SvContinuousWithinAt, SvOscWithinAt, SvIscWithinAt, svOuterLimitWithin, svInnerLimitWithin,
    SvContinuousAt, SvOscAt, SvIscAt, svOuterLimit, svInnerLimit, hnhds] using hrel

end RW
