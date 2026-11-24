/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Indicator characterization of set amenability

The equivalences hold for spaces in any universe.  `AmenableExamples` proves the forward
direction for `E : Type` only, so the indicator model is rebuilt here
(`AmenableSetModel.toIndicatorModel`).
-/
import RockafellarWets.Chapter10.FullyAmenableDomains
import RockafellarWets.Chapter10.AmenableExamples
import RockafellarWets.Chapter2.LevelSets

open Set
open scoped InnerProductSpace

noncomputable section
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- At a zero value, a normal to the strict unit sublevel is a normal to
the closure of the full domain of a convex function. -/
theorem normalCone_unit_sublevel_subset_normal_domain_closure {g : E → EReal}
    (hc : Convex ℝ (epigraph g)) (hp : IsProper g) {x : E} (hx : g x = 0) :
    normalCone (levelSet g 1) x ⊆ normalCone (closure (effectiveDomain g)) x := by
  have hxc : x ∈ levelSet g 1 := by simp [levelSet,hx]
  have hxd : x ∈ effectiveDomain g := by simp [effectiveDomain,hx]
  have hlevel := convex_levelSet_of_convex_ereal
    (convex_inequality_of_convex_epigraph_of_ne_bot hc (fun y ↦ (hp.2 y).ne')) 1
  intro v hv
  apply normalCone_subset_closure _ _
  rw [normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph hc) hxd]
  rw [normalCone_eq_of_convex hlevel hxc] at hv
  intro z hz
  have hzval : g z = ((g z).toReal:EReal) := (EReal.coe_toReal (ne_of_lt hz) (hp.2 z).ne').symm
  let r := (g z).toReal
  let t : ℝ := (|r|+1)⁻¹/2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1/2 := by
    dsimp [t]
    exact div_le_div_of_nonneg_right
      (inv_le_one₀ (by positivity) |>.mpr (by linarith [abs_nonneg r])) (by norm_num)
  have htmul : t*(|r|+1) = 1/2 := by dsimp [t]; field_simp
  have htr : t*r ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left (le_abs_self r) ht.le]
  have hcomb : (1-t) • x+t • z ∈ levelSet g 1 := by
    have hh := convex_inequality_of_convex_epigraph_of_ne_bot hc (fun y ↦ (hp.2 y).ne')
      (x := x) (y := z) (a := 1-t) (b := t) (by linarith) ht.le (by ring)
    rw [hx,hzval,mul_zero,zero_add,← EReal.coe_mul] at hh
    exact hh.trans (EReal.coe_le_coe_iff.mpr htr)
  have hn := hv _ hcomb
  have he : (1-t) • x+t • z-x = t • (z-x) := by module
  rw [he,real_inner_smul_right] at hn
  nlinarith

/-- The unit sublevel of the outer function represents the same set as
its indicator near the base point. -/
def AmenableFunctionModel.setOfIndicator {C : Set E} {x : E} {r : ℕ}
    (M : AmenableFunctionModel (indicatorVA C) x r false) : AmenableSetModel C x r false where
  Target := M.Target
  constraint := levelSet M.outer 1
  inner := M.inner
  neighborhood := M.neighborhood
  isOpen := M.isOpen
  mem := M.mem
  base := by
    by_contra hx
    exact M.finite.2 (indicatorVA_apply_not_mem hx)
  closed := (lowerSemicontinuous_iff_isClosed_preimage.mp M.lsc) 1
  convex := convex_levelSet_of_convex_ereal
    (convex_inequality_of_convex_epigraph_of_ne_bot M.convex (fun y ↦ (M.proper.2 y).ne')) 1
  smooth := M.smooth
  eqOn := by
    intro y hy
    change y ∈ C ↔ M.outer (M.inner y) ≤ (1:EReal)
    rw [← M.eqOn y hy]
    by_cases hyC : y ∈ C <;> norm_num [indicatorVA,hyC]
    exact EReal.coe_ne_top (1:ℝ)
  qualification := by
    intro v hv hz
    apply M.qualification v ?_ hz
    apply normalCone_unit_sublevel_subset_normal_domain_closure M.convex M.proper ?_ hv
    rw [← M.eqOn x M.mem]
    have hx : x ∈ C := by
      by_contra hx
      exact M.finite.2 (indicatorVA_apply_not_mem hx)
    exact indicatorVA_apply_mem hx
  polyhedral := by simp

/-- The indicator of the constraint is an outer function for `δ_C`: the forward indicator
equivalence following Definition 10.23, for all smoothness orders and full models.  This is
`AmenableSetModel.indicator` of `AmenableExamples` for `E` in any universe. -/
def AmenableSetModel.toIndicatorModel {C : Set E} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableSetModel C x r full) : AmenableFunctionModel (indicatorVA C) x r full where
  Target := M.Target
  outer := indicatorVA M.constraint
  inner := M.inner
  neighborhood := M.neighborhood
  isOpen := M.isOpen
  mem := M.mem
  finite := by simp [indicatorVA, M.base]
  proper := (indicatorVA_isProper_iff M.constraint).mpr ⟨M.inner x, (M.eqOn x M.mem).mp M.base⟩
  lsc := lowerSemicontinuous_indicatorVA M.closed
  convex := by rw [epigraph_indicatorVA]; exact M.convex.prod (convex_Ici 0)
  smooth := M.smooth
  eqOn := by
    intro y hy
    by_cases hyC : y ∈ C
    · rw [indicatorVA_apply_mem hyC, indicatorVA_apply_mem ((M.eqOn y hy).1 hyC)]
    · rw [indicatorVA_apply_not_mem hyC,
        indicatorVA_apply_not_mem fun h ↦ hyC ((M.eqOn y hy).2 h)]
  qualification := by
    simpa only [effectiveDomain_indicatorVA, M.closed.closure_eq] using M.qualification
  plq := fun h ↦ by
    let q : QuadraticPiece M.Target := ⟨0, by simp, 0, 0⟩
    simpa [q, QuadraticPiece.eval, indicatorVA] using
      isPiecewiseLinearQuadratic_piece (M.polyhedral h) q

/-- **Definition 10.23**, amenability of a set is equivalent to that of its indicator. -/
theorem setAmenableAt_iff_indicator {C : Set E} {x : E} :
    SetAmenableAt C x ↔ AmenableAt (indicatorVA C) x := by
  constructor
  · exact fun h ↦ h.map AmenableSetModel.toIndicatorModel
  · rintro ⟨M⟩
    exact ⟨M.setOfIndicator⟩

/-- The indicator characterization also preserves strong amenability. -/
theorem setStronglyAmenableAt_iff_indicator {C : Set E} {x : E} :
    SetStronglyAmenableAt C x ↔ StronglyAmenableAt (indicatorVA C) x := by
  constructor
  · exact fun h ↦ h.map AmenableSetModel.toIndicatorModel
  · rintro ⟨M⟩
    exact ⟨M.setOfIndicator⟩

/-- The indicator characterization also preserves full amenability. -/
theorem setFullyAmenableAt_iff_indicator {C : Set E} {x : E} :
    SetFullyAmenableAt C x ↔ FullyAmenableAt (indicatorVA C) x := by
  constructor
  · exact fun h ↦ h.map AmenableSetModel.toIndicatorModel
  · intro h
    simpa only [effectiveDomain_indicatorVA] using h.domain

end RW
end
