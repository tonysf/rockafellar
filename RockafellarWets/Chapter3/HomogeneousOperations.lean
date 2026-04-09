/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3F*: Operations on Cones and Positively Homogeneous Functions

This file formalizes the unambiguous operation layer from Exercise 3.40 of
Rockafellar-Wets:
- intersections, sums, linear images and preimages of cones;
- `iSup`, addition, nonnegative scalar multiples and linear precomposition for
  positively homogeneous functions;
- the corresponding sublinear variants for all of those operations except
  pointwise infima.
-/

import RockafellarWets.Chapter3.PositiveHomogeneity

open Set EReal
open scoped Pointwise

namespace RW

section Cones

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Arbitrary intersections of cones are cones. -/
theorem isCone_iInter {ι : Type*} {K : ι → Set E}
    (hK : ∀ i, IsCone (K i)) :
    IsCone (⋂ i, K i) := by
  refine ⟨?_, ?_⟩
  · simp only [mem_iInter]
    intro i
    exact (hK i).1
  intro x hx c hc
  simp only [mem_iInter] at hx ⊢
  intro i
  exact (hK i).2 (hx i) hc

/-- The Minkowski sum of two cones is a cone. -/
theorem isCone_add {K₁ K₂ : Set E}
    (hK₁ : IsCone K₁) (hK₂ : IsCone K₂) :
    IsCone (K₁ + K₂) := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_add]
    exact ⟨0, hK₁.1, 0, hK₂.1, by simp⟩
  · intro x hx c hc
    rcases hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    rw [Set.mem_add]
    exact ⟨c • x₁, hK₁.2 hx₁ hc, c • x₂, hK₂.2 hx₂ hc, by simp [smul_add]⟩

/-- Linear images of cones are cones. -/
theorem LinearMap.isCone_image (L : E →ₗ[ℝ] F) {K : Set E}
    (hK : IsCone K) :
    IsCone (L '' K) := by
  refine ⟨⟨0, hK.1, by simp⟩, ?_⟩
  intro y hy c hc
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨c • x, hK.2 hx hc, by simp⟩

/-- Linear preimages of cones are cones. -/
theorem LinearMap.isCone_preimage (L : E →ₗ[ℝ] F) {K : Set F}
    (hK : IsCone K) :
    IsCone (L ⁻¹' K) := by
  refine ⟨by simpa using hK.1, ?_⟩
  intro x hx c hc
  simpa using hK.2 hx hc

end Cones

section Homogeneous

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The zero function is positively homogeneous. -/
theorem positivelyHomogeneous_zero : PositivelyHomogeneous (fun _ : E => (0 : EReal)) := by
  refine ⟨by simp, ?_⟩
  intro x c hc
  simp

/-- The zero function is sublinear. -/
theorem sublinear_zero : Sublinear (fun _ : E => (0 : EReal)) := by
  refine ⟨positivelyHomogeneous_zero, ?_⟩
  intro x y
  simp

/-- Arbitrary pointwise suprema of positively homogeneous functions are
positively homogeneous. -/
theorem PositivelyHomogeneous.iSup {ι : Sort*} {h : ι → E → EReal}
    (hh : ∀ i, PositivelyHomogeneous (h i)) :
    PositivelyHomogeneous (fun x => ⨆ i, h i x) := by
  refine ⟨?_, ?_⟩
  · have hle : (⨆ i, h i 0) ≤ 0 := by
      refine iSup_le ?_
      intro i
      exact (hh i).map_zero_le_zero
    exact lt_of_le_of_lt hle (by simp : (0 : EReal) < ⊤)
  · intro x c hc
    apply le_antisymm
    · refine iSup_le ?_
      intro i
      calc
        h i (c • x) = (c : EReal) * h i x := (hh i).2 hc
        _ ≤ (c : EReal) * (⨆ j, h j x) := by
              gcongr
              exact le_iSup (fun j => h j x) i
    · have hbound :
          (⨆ i, h i x) ≤
            (((c⁻¹ : ℝ) : EReal) * (⨆ i, h i (c • x))) := by
        refine iSup_le ?_
        intro i
        calc
          h i x = (((c⁻¹ : ℝ) : EReal) * h i (c • x)) := by
                    have hscaled := (hh i).2 (x := c • x) (c := c⁻¹) (inv_pos.mpr hc)
                    simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using hscaled
          _ ≤ (((c⁻¹ : ℝ) : EReal) * (⨆ j, h j (c • x))) := by
                gcongr
                exact le_iSup (fun j => h j (c • x)) i
      have hmul :
          (c : EReal) * (⨆ i, h i x) ≤
            (c : EReal) * ((((c⁻¹ : ℝ) : EReal) * (⨆ i, h i (c • x)))) := by
        gcongr
      have hcancel : (c : EReal) * (((c⁻¹ : ℝ) : EReal)) = 1 := by
        rw [← EReal.coe_mul]
        exact_mod_cast (mul_inv_cancel₀ hc.ne' : c * c⁻¹ = (1 : ℝ))
      calc
        (c : EReal) * (⨆ i, h i x)
            ≤ (c : EReal) * ((((c⁻¹ : ℝ) : EReal) * (⨆ i, h i (c • x)))) := hmul
        _ = ((c : EReal) * (((c⁻¹ : ℝ) : EReal))) * (⨆ i, h i (c • x)) := by
              rw [mul_assoc]
        _ = ⨆ i, h i (c • x) := by rw [hcancel, one_mul]

/-- Binary pointwise suprema of positively homogeneous functions are
positively homogeneous. -/
theorem PositivelyHomogeneous.sup {h₁ h₂ : E → EReal}
    (hh₁ : PositivelyHomogeneous h₁) (hh₂ : PositivelyHomogeneous h₂) :
    PositivelyHomogeneous (fun x => h₁ x ⊔ h₂ x) := by
  have hsup : PositivelyHomogeneous (fun x => ⨆ b : Bool, cond b (h₁ x) (h₂ x)) :=
    PositivelyHomogeneous.iSup (h := fun b x => cond b (h₁ x) (h₂ x))
      (by
        intro b
        cases b
        · simpa using hh₂
        · simpa using hh₁)
  simpa [sup_eq_iSup] using hsup

/-- Sums of positively homogeneous functions are positively homogeneous. -/
theorem PositivelyHomogeneous.add {h₁ h₂ : E → EReal}
    (hh₁ : PositivelyHomogeneous h₁) (hh₂ : PositivelyHomogeneous h₂) :
    PositivelyHomogeneous (fun x => h₁ x + h₂ x) := by
  refine ⟨?_, ?_⟩
  · rcases hh₁.zero_eq_zero_or_bot with h₁0 | h₁0 <;>
      rcases hh₂.zero_eq_zero_or_bot with h₂0 | h₂0 <;>
      simp [h₁0, h₂0]
  · intro x c hc
    calc
      h₁ (c • x) + h₂ (c • x)
          = (c : EReal) * h₁ x + (c : EReal) * h₂ x := by
              rw [hh₁.2 hc, hh₂.2 hc]
      _ = (c : EReal) * (h₁ x + h₂ x) := by
            rw [← EReal.left_distrib_of_nonneg_of_ne_top
              (by exact_mod_cast hc.le) (EReal.coe_ne_top c)]

/-- Nonnegative scalar multiples of positively homogeneous functions are
positively homogeneous. -/
theorem PositivelyHomogeneous.const_mul {h : E → EReal}
    (hh : PositivelyHomogeneous h) {a : ℝ} (ha : 0 ≤ a) :
    PositivelyHomogeneous (fun x => ((a : EReal) * h x)) := by
  refine ⟨?_, ?_⟩
  · rcases hh.zero_eq_zero_or_bot with h0 | h0
    · simp [h0]
    · rcases ha.eq_or_lt with rfl | ha'
      · simp [h0]
      · simp [h0, EReal.coe_mul_bot_of_pos ha']
  · intro x c hc
    calc
      (a : EReal) * h (c • x) = (a : EReal) * ((c : EReal) * h x) := by
        rw [hh.2 hc]
      _ = (c : EReal) * (((a : EReal) * h x)) := by
        simp [mul_assoc, mul_left_comm, mul_comm]

/-- Linear precomposition preserves positive homogeneity. -/
theorem PositivelyHomogeneous.comp_linearMap {h : F → EReal}
    (hh : PositivelyHomogeneous h) (L : E →ₗ[ℝ] F) :
    PositivelyHomogeneous (fun x => h (L x)) := by
  refine ⟨by simpa using hh.1, ?_⟩
  intro x c hc
  simpa using hh.2 (x := L x) (c := c) hc

/-- Arbitrary pointwise suprema of sublinear functions are sublinear. -/
theorem Sublinear.iSup {ι : Sort*} {h : ι → E → EReal}
    (hh : ∀ i, Sublinear (h i)) :
    Sublinear (fun x => ⨆ i, h i x) := by
  refine ⟨PositivelyHomogeneous.iSup (fun i => (hh i).1), ?_⟩
  intro x y
  refine iSup_le ?_
  intro i
  calc
    h i (x + y) ≤ h i x + h i y := (hh i).2 x y
    _ ≤ (⨆ j, h j x) + (⨆ j, h j y) := by
          gcongr <;> exact le_iSup (fun j => h j _) i

/-- Binary pointwise suprema of sublinear functions are sublinear. -/
theorem Sublinear.sup {h₁ h₂ : E → EReal}
    (hh₁ : Sublinear h₁) (hh₂ : Sublinear h₂) :
    Sublinear (fun x => h₁ x ⊔ h₂ x) := by
  have hsup : Sublinear (fun x => ⨆ b : Bool, cond b (h₁ x) (h₂ x)) :=
    Sublinear.iSup (h := fun b x => cond b (h₁ x) (h₂ x))
      (by
        intro b
        cases b
        · simpa using hh₂
        · simpa using hh₁)
  simpa [sup_eq_iSup] using hsup

/-- Sums of sublinear functions are sublinear. -/
theorem Sublinear.add {h₁ h₂ : E → EReal}
    (hh₁ : Sublinear h₁) (hh₂ : Sublinear h₂) :
    Sublinear (fun x => h₁ x + h₂ x) := by
  refine ⟨hh₁.1.add hh₂.1, ?_⟩
  intro x y
  calc
    h₁ (x + y) + h₂ (x + y) ≤ (h₁ x + h₁ y) + (h₂ x + h₂ y) := by
      gcongr
      · exact hh₁.2 x y
      · exact hh₂.2 x y
    _ = (h₁ x + h₂ x) + (h₁ y + h₂ y) := by
          simp [add_left_comm, add_comm]

/-- Nonnegative scalar multiples of sublinear functions are sublinear. -/
theorem Sublinear.const_mul {h : E → EReal}
    (hh : Sublinear h) {a : ℝ} (ha : 0 ≤ a) :
    Sublinear (fun x => ((a : EReal) * h x)) := by
  refine ⟨hh.1.const_mul ha, ?_⟩
  intro x y
  calc
    (a : EReal) * h (x + y) ≤ (a : EReal) * (h x + h y) := by
      gcongr
      exact hh.2 x y
    _ = (a : EReal) * h x + (a : EReal) * h y := by
          rw [EReal.left_distrib_of_nonneg_of_ne_top
            (by exact_mod_cast ha) (EReal.coe_ne_top a)]

/-- Linear precomposition preserves sublinearity. -/
theorem Sublinear.comp_linearMap {h : F → EReal}
    (hh : Sublinear h) (L : E →ₗ[ℝ] F) :
    Sublinear (fun x => h (L x)) := by
  refine ⟨hh.1.comp_linearMap L, ?_⟩
  intro x y
  simpa using hh.2 (L x) (L y)

end Homogeneous

end RW
