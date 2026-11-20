/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A Lipschitz extension preserving infima and constrained minimizers
-/

import RockafellarWets.Chapter9.PaschHausdorffEnvelopes

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- The real function restricted by assigning `+∞` outside its feasible set. -/
noncomputable def restrictedRealFunction (f : E → ℝ) (C : Set E) (x : E) : EReal := by
  classical
  exact if x ∈ C then (f x : EReal) else ⊤

theorem restrictedRealFunction_isProper (f : E → ℝ) {C : Set E} (hC : C.Nonempty) :
    IsProper (restrictedRealFunction f C) := by
  obtain ⟨x,hx⟩ := hC
  refine ⟨⟨x,by simp [restrictedRealFunction,hx]⟩,?_⟩
  intro y
  by_cases hy : y ∈ C <;> simp [restrictedRealFunction,hy]

/-- **Exercise 9.12.** The explicit infimum extension of a real function. -/
noncomputable def lipschitzInfExtension (f : E → ℝ) (C : Set E) (k : ℝ≥0) : E → EReal :=
  paschHausdorffEnvelope (restrictedRealFunction f C) k

theorem lipschitzInfExtension_formula (f : E → ℝ) (C : Set E) (k : ℝ≥0) (x : E) :
    lipschitzInfExtension f C k x = ⨅ y ∈ C, ((f y + k * dist y x : ℝ) : EReal) := by
  unfold lipschitzInfExtension paschHausdorffEnvelope
  apply le_antisymm
  · apply le_iInf
    intro y
    apply le_iInf
    intro hy
    simpa [restrictedRealFunction,hy,EReal.coe_add] using
      (iInf_le (fun z ↦ restrictedRealFunction f C z + ((k * dist z x : ℝ) : EReal)) y)
  · apply le_iInf
    intro y
    by_cases hy : y ∈ C
    · simpa [restrictedRealFunction,hy,EReal.coe_add] using
        (iInf₂_le y hy : (⨅ z ∈ C, ((f z + k * dist z x : ℝ) : EReal)) ≤ _)
    · simp only [restrictedRealFunction,if_neg hy,EReal.top_add_coe,le_top]

/-- The infimum formula is finite and retains the original Lipschitz constant. -/
theorem lipschitzInfExtension_lipschitz {f : E → ℝ} {C : Set E} {k : ℝ≥0}
    (hC : C.Nonempty) (hf : LipschitzOnWith k f C) :
    (∀ x, lipschitzInfExtension f C k x = ((lipschitzInfExtension f C k x).toReal : EReal)) ∧
      LipschitzWith k (fun x ↦ (lipschitzInfExtension f C k x).toReal) := by
  obtain ⟨g,hg,he⟩ := hf.extend_real
  have hminor (x : E) : (g x : EReal) ≤ restrictedRealFunction f C x := by
    by_cases hx : x ∈ C
    · simp [restrictedRealFunction,hx,he hx]
    · simp [restrictedRealFunction,hx]
  exact paschHausdorffEnvelope_lipschitz (restrictedRealFunction_isProper f hC)
    (((EReal.bot_lt_coe (g 0)).trans_le (le_paschHausdorffEnvelope_of_lipschitz hg hminor 0)).ne')

/-- The explicit extension agrees with the function on the prescribed set. -/
theorem lipschitzInfExtension_eq {f : E → ℝ} {C : Set E} {k : ℝ≥0}
    (hf : LipschitzOnWith k f C) {x : E} (hx : x ∈ C) :
    lipschitzInfExtension f C k x = (f x : EReal) := by
  apply le_antisymm
  · simpa [restrictedRealFunction,hx] using
      paschHausdorffEnvelope_le (restrictedRealFunction f C) k x
  · rw [lipschitzInfExtension_formula]
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact EReal.coe_le_coe_iff.mpr (by simpa [dist_comm] using hf.le_add_mul hx hy)

/-- **Exercise 9.12**, equality of optimal values. This equality holds even
before assuming the data satisfy a Lipschitz bound. -/
theorem iInf_lipschitzInfExtension (f : E → ℝ) (C : Set E) (k : ℝ≥0) :
    (⨅ x, lipschitzInfExtension f C k x) = ⨅ x ∈ C, (f x : EReal) := by
  apply le_antisymm
  · apply le_iInf
    intro x
    apply le_iInf
    intro hx
    exact (iInf_le _ x).trans (by
      simpa [restrictedRealFunction,hx] using
        paschHausdorffEnvelope_le (restrictedRealFunction f C) k x)
  · apply le_iInf
    intro x
    rw [lipschitzInfExtension_formula]
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact (iInf₂_le y hy).trans (EReal.coe_le_coe_iff.mpr
      (le_add_of_nonneg_right (mul_nonneg k.coe_nonneg dist_nonneg)))

/-- **Exercise 9.12**, equality of constrained minimizers with the feasible
part of the extension's minimizer set. -/
theorem argmin_lipschitzInfExtension {f : E → ℝ} {C : Set E} {k : ℝ≥0}
    (hf : LipschitzOnWith k f C) :
    {x | x ∈ C ∧ (f x : EReal) = ⨅ y ∈ C, (f y : EReal)} =
      C ∩ argmin (lipschitzInfExtension f C k) := by
  ext x
  constructor
  · rintro ⟨hx,hval⟩
    refine ⟨hx,?_,?_⟩
    · rw [lipschitzInfExtension_eq hf hx,iInf_lipschitzInfExtension,hval]
    · rw [iInf_lipschitzInfExtension,← hval]
      exact EReal.coe_lt_top _
  · rintro ⟨hx,hval,hfin⟩
    refine ⟨hx,?_⟩
    simpa [lipschitzInfExtension_eq hf hx,iInf_lipschitzInfExtension] using hval

end RW
