/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sublinear epi-addition

This file completes the sublinear part of Exercise 3.40(f).  There is one
genuine `EReal` subtlety: Mathlib makes `⊥` absorbing for addition, including
`⊤ + ⊥ = ⊥`.  Consequently, the infimal convolution of two sublinear
functions need not be sublinear if it takes both `⊥` and non-`⊥` values.

The condition below is exact, rather than merely sufficient.  A sublinear
function which takes the value `⊥` anywhere is necessarily identically `⊥`.
Thus the epi-sum of two sublinear functions is sublinear precisely when it
either has no `⊥` values or is identically `⊥`.  In particular, every proper
epi-sum satisfies the book's closure rule.
-/

import RockafellarWets.Chapter3.HomogeneousCompletion

open Set EReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A sublinear `EReal`-valued function which takes the value `⊥` is
identically `⊥`.  This records the exact obstruction caused by Mathlib's
absorbing-bottom addition. -/
theorem Sublinear.eq_bot_of_exists_eq_bot {h : E → EReal}
    (hh : Sublinear h) (hbot : ∃ x, h x = ⊥) :
    h = fun _ => ⊥ := by
  rcases hbot with ⟨y, hy⟩
  funext x
  apply le_antisymm
  · have hsub := hh.2 (x - y) y
    simpa [hy] using hsub
  · exact bot_le

/-- If an epi-sum has no bottom values, the infimum approximation argument
gives the subadditivity required in Exercise 3.40(f). -/
theorem Sublinear.epiSum_of_ne_bot {h₁ h₂ : E → EReal}
    (hh₁ : Sublinear h₁) (hh₂ : Sublinear h₂)
    (hbot : ∀ x, epiSum h₁ h₂ x ≠ ⊥) :
    Sublinear (epiSum h₁ h₂) := by
  refine ⟨hh₁.1.epiSum hh₂.1, ?_⟩
  intro x y
  by_cases htop : epiSum h₁ h₂ x + epiSum h₁ h₂ y = ⊤
  · rw [htop]
    exact le_top
  have hx_top : epiSum h₁ h₂ x ≠ ⊤ := by
    intro hx
    rw [hx, top_add_of_ne_bot (hbot y)] at htop
    exact htop rfl
  have hy_top : epiSum h₁ h₂ y ≠ ⊤ := by
    intro hy
    rw [hy, add_top_of_ne_bot (hbot x)] at htop
    exact htop rfl
  let rx : ℝ := (epiSum h₁ h₂ x).toReal
  let ry : ℝ := (epiSum h₁ h₂ y).toReal
  have hx_coe : (rx : EReal) = epiSum h₁ h₂ x :=
    EReal.coe_toReal hx_top (hbot x)
  have hy_coe : (ry : EReal) = epiSum h₁ h₂ y :=
    EReal.coe_toReal hy_top (hbot y)
  by_contra hle
  have hlt : epiSum h₁ h₂ x + epiSum h₁ h₂ y <
      epiSum h₁ h₂ (x + y) := lt_of_not_ge hle
  have hsum_coe : ((rx + ry : ℝ) : EReal) =
      epiSum h₁ h₂ x + epiSum h₁ h₂ y := by
    rw [← hx_coe, ← hy_coe, EReal.coe_add]
  rw [← hsum_coe] at hlt
  obtain ⟨c, hrc, hck⟩ := EReal.exists_between_coe_real hlt
  let eps : ℝ := (c - (rx + ry)) / 4
  have heps : 0 < eps := by
    dsimp [eps]
    have : rx + ry < c := by exact_mod_cast hrc
    linarith
  have hx_lt : epiSum h₁ h₂ x < ((rx + eps : ℝ) : EReal) := by
    rw [← hx_coe]
    exact_mod_cast lt_add_of_pos_right rx heps
  have hy_lt : epiSum h₁ h₂ y < ((ry + eps : ℝ) : EReal) := by
    rw [← hy_coe]
    exact_mod_cast lt_add_of_pos_right ry heps
  rw [epiSum_apply] at hx_lt hy_lt
  obtain ⟨wx, hwx⟩ := exists_lt_of_ciInf_lt hx_lt
  obtain ⟨wy, hwy⟩ := exists_lt_of_ciInf_lt hy_lt
  have hterm :
      h₁ ((x + y) - (wx + wy)) + h₂ (wx + wy) ≤
        (h₁ (x - wx) + h₂ wx) + (h₁ (y - wy) + h₂ wy) := by
    calc
      h₁ ((x + y) - (wx + wy)) + h₂ (wx + wy)
          ≤ (h₁ (x - wx) + h₁ (y - wy)) +
              (h₂ wx + h₂ wy) := by
            apply add_le_add
            · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                hh₁.2 (x - wx) (y - wy)
            · exact hh₂.2 wx wy
      _ = (h₁ (x - wx) + h₂ wx) +
            (h₁ (y - wy) + h₂ wy) := by
          simp only [add_assoc]
          congr 1
          rw [← add_assoc, add_comm (h₁ (y - wy)) (h₂ wx), add_assoc]
  have happrox :
      (h₁ (x - wx) + h₂ wx) + (h₁ (y - wy) + h₂ wy) <
        ((rx + eps + (ry + eps) : ℝ) : EReal) := by
    simpa [EReal.coe_add] using EReal.add_lt_add hwx hwy
  have hbelow : epiSum h₁ h₂ (x + y) < (c : EReal) := by
    have hiInf : epiSum h₁ h₂ (x + y) ≤
        h₁ ((x + y) - (wx + wy)) + h₂ (wx + wy) := by
      rw [epiSum_apply]
      exact iInf_le _ (wx + wy)
    have hreps : rx + eps + (ry + eps) < c := by
      dsimp [eps]
      have : rx + ry < c := by exact_mod_cast hrc
      linarith
    exact hiInf.trans_lt <| hterm.trans_lt <|
      happrox.trans <| by exact_mod_cast hreps
  exact (not_lt_of_ge hck.le) hbelow

/-- Exact `EReal` form of Exercise 3.40(f): for sublinear inputs, epi-addition
is sublinear exactly in the bottom-regular cases.  The disjunction is logically
necessary because any sublinear function attaining `⊥` is identically `⊥`. -/
theorem Sublinear.epiSum_iff_botRegular {h₁ h₂ : E → EReal}
    (hh₁ : Sublinear h₁) (hh₂ : Sublinear h₂) :
    Sublinear (epiSum h₁ h₂) ↔
      (∀ x, epiSum h₁ h₂ x ≠ ⊥) ∨
        epiSum h₁ h₂ = fun _ => ⊥ := by
  constructor
  · intro hsum
    by_cases hbot : ∃ x, epiSum h₁ h₂ x = ⊥
    · exact Or.inr (hsum.eq_bot_of_exists_eq_bot hbot)
    · push_neg at hbot
      exact Or.inl hbot
  · rintro (hbot | hbot)
    · exact hh₁.epiSum_of_ne_bot hh₂ hbot
    · rw [hbot]
      refine ⟨?_, ?_⟩
      · refine ⟨by simp, ?_⟩
        intro x c hc
        rw [EReal.coe_mul_bot_of_pos hc]
      · simp

/-- Exercise 3.40(f), convenient proper form.  Properness excludes the sole
`EReal` bottom pathology, so no further qualification is needed. -/
theorem Sublinear.epiSum_of_isProper {h₁ h₂ : E → EReal}
    (hh₁ : Sublinear h₁) (hh₂ : Sublinear h₂)
    (hproper : IsProper (epiSum h₁ h₂)) :
    Sublinear (epiSum h₁ h₂) :=
  hh₁.epiSum_of_ne_bot hh₂ fun x => ne_of_gt (hproper.2 x)

/-! ## Why the bottom-regularity condition cannot be omitted -/

namespace EpiSumCounterexample

/-- The horizontal axis in `ℝ²`. -/
def horizontalAxis : Set (ℝ × ℝ) := {x | x.2 = 0}

private theorem convex_horizontalAxis : Convex ℝ horizontalAxis := by
  intro x hx y hy a b ha hb hab
  simp only [horizontalAxis, mem_setOf_eq] at hx hy ⊢
  simp [hx, hy]

private theorem isCone_horizontalAxis : IsCone horizontalAxis := by
  refine ⟨by simp [horizontalAxis], ?_⟩
  intro x hx c hc
  simp only [horizontalAxis, mem_setOf_eq] at hx ⊢
  simp [hx]

/-- The first coordinate, regarded as an `EReal`-valued linear function. -/
def firstCoordinate (x : ℝ × ℝ) : EReal := (x.1 : ℝ)

private theorem sublinear_firstCoordinate : Sublinear firstCoordinate := by
  refine ⟨?_, ?_⟩
  · refine ⟨by simp [firstCoordinate], ?_⟩
    intro x c hc
    simp [firstCoordinate, ← EReal.coe_mul]
  · intro x y
    simp [firstCoordinate, ← EReal.coe_add]

/-- A sublinear function finite and linear on the horizontal axis and `⊤`
off that axis. -/
noncomputable def horizontalLinear (x : ℝ × ℝ) : EReal :=
  firstCoordinate x + indicatorVA horizontalAxis x

private theorem sublinear_horizontalIndicator_aux :
    Sublinear (indicatorVA horizontalAxis) :=
  sublinear_indicatorVA_iff.mpr
    ⟨convex_horizontalAxis, isCone_horizontalAxis⟩

theorem sublinear_horizontalLinear : Sublinear horizontalLinear := by
  simpa [horizontalLinear] using
    sublinear_firstCoordinate.add sublinear_horizontalIndicator_aux

theorem sublinear_horizontalIndicator :
    Sublinear (indicatorVA horizontalAxis) :=
  sublinear_horizontalIndicator_aux

/-- On the horizontal axis, the two summands can cancel spatially while the
linear height tends to `-∞`. -/
theorem epiSum_zero_eq_bot :
    epiSum (indicatorVA horizontalAxis) horizontalLinear (0, 0) = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro r
  rw [epiSum_apply]
  refine (iInf_le
    (fun w : ℝ × ℝ =>
      indicatorVA horizontalAxis ((0, 0) - w) + horizontalLinear w)
    ((r - 1, 0) : ℝ × ℝ)).trans_lt ?_
  calc
    indicatorVA horizontalAxis ((0, 0) - (r - 1, 0)) +
          horizontalLinear (r - 1, 0) = ((r - 1 : ℝ) : EReal) := by
      simp [horizontalLinear, firstCoordinate, horizontalAxis, indicatorVA]
    _ < (r : EReal) := by
      exact_mod_cast sub_one_lt r

/-- Off the horizontal axis there is no feasible decomposition, so the same
epi-sum takes the value `⊤`. -/
theorem epiSum_vertical_eq_top :
    epiSum (indicatorVA horizontalAxis) horizontalLinear (0, 1) = ⊤ := by
  apply top_unique
  rw [epiSum_apply]
  refine le_iInf fun w => ?_
  by_cases hw : w.2 = 0
  · simp [horizontalLinear, firstCoordinate, horizontalAxis, indicatorVA, hw]
  · by_cases hdiff : 1 - w.2 = 0
    · simp [horizontalLinear, firstCoordinate, horizontalAxis, indicatorVA,
        hw, hdiff]
    · simp [horizontalLinear, firstCoordinate, horizontalAxis, indicatorVA,
        hw, hdiff]

/-- Two sublinear inputs can therefore have an epi-sum which is not
sublinear.  This is exactly the mixed `⊤`/`⊥` pathology excluded by
`Sublinear.epiSum_iff_botRegular`. -/
theorem not_sublinear_epiSum :
    ¬ Sublinear
      (epiSum (indicatorVA horizontalAxis) horizontalLinear) := by
  intro h
  have hregular :=
    (sublinear_horizontalIndicator.epiSum_iff_botRegular
      sublinear_horizontalLinear).mp h
  rcases hregular with hne | hall
  · exact hne (0, 0) epiSum_zero_eq_bot
  · have := congrFun hall (0, 1)
    rw [epiSum_vertical_eq_top] at this
    exact top_ne_bot this

end EpiSumCounterexample

end RW
