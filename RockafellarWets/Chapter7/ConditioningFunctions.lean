/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: The intrinsic conditioning function of a minimization problem
-/

import RockafellarWets.Chapter3.Coercivity
import RockafellarWets.Chapter7.MinimizationCriteria

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- The minimum excess value at distance at least `τ` from the solution set.
The argument `m` is the real minimum of `f` in the results below. -/
noncomputable def conditioningValue (f : E → EReal) (m τ : ℝ) : EReal :=
  infimumOn f {x | τ ≤ infDist x (argmin f)} - (m : EReal)

/-- The generalized inverse of the intrinsic conditioning function. -/
noncomputable def conditioningRadius (f : E → EReal) (m e : ℝ) : ℝ :=
  sSup ((fun x ↦ infDist x (argmin f)) '' levelSet f ((m + e : ℝ) : EReal))

/-- The solution perturbation radius `Ψ` in Theorem 7.64. -/
noncomputable def solutionRadius (f : E → EReal) (m η : ℝ) : ℝ :=
  η + conditioningRadius f m (2 * η)

theorem infimumOn_le_coe_iff_exists_of_isInfCompact {f : E → EReal}
    (hf : LowerSemicontinuous f) (hc : IsInfCompact f) {S : Set E} (hS : IsClosed S) (a : ℝ) :
    infimumOn f S ≤ (a : EReal) ↔ ∃ x ∈ S, f x ≤ (a : EReal) := by
  constructor
  · intro h
    obtain ⟨y, hy, hfy⟩ := infimumOn_lt_iff.mp (h.trans_lt
      (EReal.coe_lt_coe_iff.mpr (lt_add_one a)))
    let K := levelSet f ((a + 1 : ℝ) : EReal) ∩ S
    have hK : IsCompact K := (hc _).inter_right hS
    obtain ⟨x, hx, hmin⟩ := (hf.lowerSemicontinuousOn _).exists_isMinOn
      (s := K) ⟨y, hfy.le, hy⟩ hK
    refine ⟨x, hx.2, le_trans (le_infimumOn fun z hz ↦ ?_) h⟩
    by_cases hza : f z ≤ ((a + 1 : ℝ) : EReal)
    · exact hmin ⟨hza, hz⟩
    · exact (show f x ≤ ((a + 1 : ℝ) : EReal) from hx.1).trans (le_of_not_ge hza)
  · rintro ⟨x, hx, hfx⟩
    exact (infimumOn_le hx).trans hfx

/-- The sublevel condition for the intrinsic conditioning function is
witnessed by a point at least `τ` away in the corresponding sublevel of `f`. -/
theorem conditioningValue_le_iff {f : E → EReal} (hf : LowerSemicontinuous f)
    (hc : IsInfCompact f) (m τ e : ℝ) :
    conditioningValue f m τ ≤ (e : EReal) ↔
      ∃ x ∈ levelSet f ((m + e : ℝ) : EReal), τ ≤ infDist x (argmin f) := by
  rw [conditioningValue, EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _)), ← EReal.coe_add, add_comm e m,
    infimumOn_le_coe_iff_exists_of_isInfCompact hf hc
      (isClosed_le continuous_const (continuous_infDist_pt _))]
  exact exists_congr fun _ ↦ and_comm

theorem conditioningRadius_attained {f : E → EReal} (hc : IsInfCompact f) {m e : ℝ}
    (hne : (levelSet f ((m + e : ℝ) : EReal)).Nonempty) :
    ∃ x ∈ levelSet f ((m + e : ℝ) : EReal), infDist x (argmin f) = conditioningRadius f m e := by
  obtain ⟨x, hx, hmax⟩ := (hc (m+e)).exists_isMaxOn hne (continuous_infDist_pt (argmin f)).continuousOn
  have hgreat : IsGreatest ((fun y ↦ infDist y (argmin f)) '' levelSet f ((m + e : ℝ) : EReal))
      (infDist x (argmin f)) := ⟨mem_image_of_mem _ hx, fun _ ⟨y, hy, heq⟩ ↦ heq ▸ hmax hy⟩
  exact ⟨x, hx, hgreat.csSup_eq.symm⟩

theorem infDist_argmin_le_conditioningRadius {f : E → EReal} (hc : IsInfCompact f)
    {m e : ℝ} {x : E} (hx : x ∈ levelSet f ((m + e : ℝ) : EReal)) :
    infDist x (argmin f) ≤ conditioningRadius f m e :=
  le_csSup ((hc (m+e)).image (continuous_infDist_pt (argmin f))).bddAbove (mem_image_of_mem _ hx)

omit [NormedAddCommGroup E] in
private theorem levelSet_nonempty_at_excess {f : E → EReal} {m e : ℝ}
    (hA : (argmin f).Nonempty) (hm : (⨅ x, f x) = (m : EReal)) (he : 0 ≤ e) :
    (levelSet f ((m + e : ℝ) : EReal)).Nonempty := by
  obtain ⟨x, hx⟩ := hA
  exact ⟨x, (hx.1.trans hm).le.trans (EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_right he))⟩

/-- The sublevel set of `ψ` on the nonnegative half-line is precisely the
closed interval from zero to the generalized inverse. -/
theorem conditioningValue_le_iff_le_radius {f : E → EReal} (hf : LowerSemicontinuous f)
    (hc : IsInfCompact f) {m e : ℝ} (hA : (argmin f).Nonempty)
    (hm : (⨅ x, f x) = (m : EReal)) (he : 0 ≤ e) (τ : ℝ) :
    conditioningValue f m τ ≤ (e : EReal) ↔ τ ≤ conditioningRadius f m e := by
  rw [conditioningValue_le_iff hf hc]
  constructor
  · rintro ⟨x, hx, hτ⟩
    exact hτ.trans (infDist_argmin_le_conditioningRadius hc hx)
  · intro hτ
    obtain ⟨x, hx, hd⟩ := conditioningRadius_attained hc (levelSet_nonempty_at_excess hA hm he)
    exact ⟨x, hx, hτ.trans hd.ge⟩

theorem conditioningValue_nonneg {f : E → EReal} {m : ℝ}
    (hm : (⨅ x, f x) = (m : EReal)) (τ : ℝ) : 0 ≤ conditioningValue f m τ := by
  apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mpr
  rw [zero_add, ← hm]
  exact le_infimumOn fun x _ ↦ iInf_le f x

theorem monotone_conditioningValue (f : E → EReal) (m : ℝ) : Monotone (conditioningValue f m) := by
  intro a b hab
  unfold conditioningValue
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply add_le_add_left
  exact le_infimumOn fun x hx ↦ infimumOn_le (hab.trans hx)

/-- The intrinsic conditioning function is lsc, vanishes at zero and is
strictly positive at every positive distance. -/
theorem conditioningValue_properties {f : E → EReal} (hf : LowerSemicontinuous f)
    (hc : IsInfCompact f) (hA : (argmin f).Nonempty) {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) :
    LowerSemicontinuous (conditioningValue f m) ∧ conditioningValue f m 0 = 0 ∧
      ∀ τ > 0, 0 < conditioningValue f m τ := by
  have h₀ (τ : ℝ) := conditioningValue_nonneg hm τ
  refine ⟨?_, ?_, ?_⟩
  · rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro a
    cases a using EReal.rec with
    | bot =>
      have hempty : (conditioningValue f m) ⁻¹' Iic ⊥ = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun τ h ↦ (lt_of_lt_of_le EReal.bot_lt_zero (h₀ τ)).not_ge h
      rw [hempty]
      exact isClosed_empty
    | top => simp
    | coe e =>
      by_cases he : 0 ≤ e
      · have heq : (conditioningValue f m) ⁻¹' Iic (e : EReal) = Iic (conditioningRadius f m e) :=
          ext fun τ ↦ conditioningValue_le_iff_le_radius hf hc hA hm he τ
        rw [heq]
        exact isClosed_Iic
      · have hempty : (conditioningValue f m) ⁻¹' Iic (e : EReal) = ∅ :=
          eq_empty_iff_forall_notMem.mpr fun τ h ↦ he (EReal.coe_nonneg.mp ((h₀ τ).trans h))
        rw [hempty]
        exact isClosed_empty
  · apply le_antisymm _ (h₀ 0)
    obtain ⟨x, hx⟩ := hA
    exact (conditioningValue_le_iff hf hc m 0 0).mpr ⟨x, by simp [levelSet, hx.1, hm], infDist_nonneg⟩
  · intro τ hτ
    by_contra! h
    obtain ⟨x, hx, hd⟩ := (conditioningValue_le_iff hf hc m τ 0).mp h
    have hxA : x ∈ argmin f := by
      refine ⟨le_antisymm ?_ (iInf_le _ _), hm ▸ EReal.coe_lt_top _⟩
      simpa [levelSet, hm] using hx
    rw [infDist_zero_of_mem hxA] at hd
    exact hτ.not_ge hd

theorem monotoneOn_conditioningRadius {f : E → EReal} (hc : IsInfCompact f)
    (hA : (argmin f).Nonempty) {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) :
    MonotoneOn (conditioningRadius f m) (Ici 0) := by
  intro e he e' _ hee
  obtain ⟨x, hx, hd⟩ := conditioningRadius_attained hc (levelSet_nonempty_at_excess hA hm he)
  exact hd ▸ infDist_argmin_le_conditioningRadius hc (m := m) (e := e')
    (levelSet_monotone f (EReal.coe_le_coe_iff.mpr (add_le_add_right hee m)) hx)

theorem solutionRadius_zero {f : E → EReal} (hc : IsInfCompact f) (hA : (argmin f).Nonempty)
    {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) : solutionRadius f m 0 = 0 := by
  obtain ⟨x, hx, hd⟩ := conditioningRadius_attained hc (levelSet_nonempty_at_excess hA hm (le_refl 0))
  have hxA : x ∈ argmin f := ⟨le_antisymm (by simpa [hm, levelSet] using hx) (iInf_le _ _),
    hm ▸ EReal.coe_lt_top _⟩
  simpa [solutionRadius, ← hd] using infDist_zero_of_mem hxA

theorem strictMonoOn_solutionRadius {f : E → EReal} (hc : IsInfCompact f)
    (hA : (argmin f).Nonempty) {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) :
    StrictMonoOn (solutionRadius f m) (Ici 0) := by
  intro a ha b hb hab
  exact add_lt_add_of_lt_of_le hab ((monotoneOn_conditioningRadius hc hA hm)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ha) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hb) (by linarith))

/-- The generalized-inverse radius tends to zero from the right, even
when it has upward jumps at positive arguments. -/
theorem tendsto_solutionRadius_zero {f : E → EReal} (hf : LowerSemicontinuous f)
    (hc : IsInfCompact f) (hA : (argmin f).Nonempty) {m : ℝ} (hm : (⨅ x, f x) = (m : EReal)) :
    Tendsto (solutionRadius f m) (𝓝[≥] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨b, hb, hbψ⟩ := EReal.exists_between_coe_real ((conditioningValue_properties hf hc hA hm).2.2
    (ε/2) (half_pos hε))
  have hb' : 0 < b := EReal.coe_pos.mp hb
  refine ⟨min (ε/2) (b/2), lt_min (half_pos hε) (half_pos hb'), ?_⟩
  intro η hη hd
  have hη' : 0 ≤ η := hη
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hη'] at hd
  have hrad : conditioningRadius f m (2*η) < ε/2 := by
    by_contra! h
    have hh := (conditioningValue_le_iff_le_radius hf hc hA hm (mul_nonneg (by norm_num) hη') (ε/2)).mpr h
    exact (hh.trans_lt (EReal.coe_lt_coe_iff.mpr
      (by linarith [hd.trans_le (min_le_right _ _)] : 2*η < b))).not_ge hbψ.le
  have hsol : 0 ≤ solutionRadius f m η := (solutionRadius_zero hc hA hm) ▸
    (strictMonoOn_solutionRadius hc hA hm).monotoneOn (by simp) hη hη
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hsol]
  dsimp [solutionRadius]
  linarith [hd.trans_le (min_le_left _ _)]

end RW
