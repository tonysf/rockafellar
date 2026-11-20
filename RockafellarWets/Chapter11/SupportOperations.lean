/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Elementary support-function operations
-/
import RockafellarWets.Chapter11.SupportConjugates
import RockafellarWets.Chapter10.PLQCalculus

open Set
open scoped InnerProductSpace Pointwise
namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The scaling rule of Corollary 11.24(a), also valid for the empty set. -/
theorem supportFunction_smul (C : Set E) {r : ℝ} (hr : 0 < r) (v : E) :
    supportFunction (r • C) v = (r:EReal) * supportFunction C v := by
  rw [← (sublinear_supportFunction C).1.2 hr]
  apply le_antisymm
  · apply (supportFunction_le_iff _ _ _).mpr
    rintro _ ⟨x,hx,rfl⟩
    simpa only [real_inner_smul_left,real_inner_smul_right] using inner_le_supportFunction hx (r • v)
  · apply (supportFunction_le_iff _ _ _).mpr
    intro x hx
    simpa only [real_inner_smul_left,real_inner_smul_right] using
      inner_le_supportFunction (show r • x ∈ r • C from ⟨x,hx,rfl⟩) v

/-- Support commutes with arbitrary unions, Corollary 11.24(f). -/
theorem supportFunction_iUnion {ι : Sort*} (C : ι → Set E) (v : E) :
    supportFunction (⋃i, C i) v = ⨆i, supportFunction (C i) v := by
  refine le_antisymm ((supportFunction_le_iff _ _ _).mpr ?_) (iSup_le fun i ↦ ?_)
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact (inner_le_supportFunction hi v).trans (le_iSup (fun i ↦ supportFunction (C i) v) i)
  · exact supportFunction_mono (subset_iUnion C i) v

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Linear-image rule, Corollary 11.24(c). Addition is `supportFunction_add`. -/
theorem supportFunction_linear_image (A : E →L[ℝ] F) (C : Set E) (v : F) :
    supportFunction (A '' C) v = supportFunction C (A.adjoint v) := by
  simpa only [ContinuousLinearMap.adjoint_adjoint] using supportFunction_adjoint_image A.adjoint C v

end RW
