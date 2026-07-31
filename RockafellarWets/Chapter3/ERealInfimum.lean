/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite translations of EReal infima

Addition by a finite real number is an order automorphism of `EReal`, even
though unrestricted `EReal` addition is not cancellative.  Packaging this
translation as an `OrderIso` makes its interaction with arbitrary indexed
infima immediate from `OrderIso.map_iInf`.
-/

import Mathlib.Data.EReal.Operations

open EReal

noncomputable section

namespace RW

/-- Translation by a finite real constant as an order automorphism of
`EReal`.  Its inverse is subtraction by the same finite constant. -/
def erealAddRightOrderIso (c : ℝ) : EReal ≃o EReal where
  toFun x := x + c
  invFun x := x - c
  left_inv x := EReal.add_sub_cancel_right (a := x) (b := c)
  right_inv x := EReal.sub_add_cancel (a := x) (b := c)
  map_rel_iff' := (EReal.addLECancellable_coe c).add_le_add_iff_right

@[simp]
theorem erealAddRightOrderIso_apply (c : ℝ) (x : EReal) :
    erealAddRightOrderIso c x = x + c :=
  rfl

@[simp]
theorem erealAddRightOrderIso_symm_apply (c : ℝ) (x : EReal) :
    (erealAddRightOrderIso c).symm x = x - c :=
  rfl

/-- Right addition by a finite real constant commutes with every indexed
infimum in `EReal`.  No nonemptiness or boundedness hypothesis is needed. -/
theorem iInf_add_coe {ι : Sort*} (f : ι → EReal) (c : ℝ) :
    (⨅ i, f i) + c = ⨅ i, f i + c := by
  exact (erealAddRightOrderIso c).map_iInf f

/-- Left addition by a finite real constant commutes with every indexed
infimum in `EReal`.  No nonemptiness or boundedness hypothesis is needed. -/
theorem coe_add_iInf {ι : Sort*} (c : ℝ) (f : ι → EReal) :
    (c : EReal) + (⨅ i, f i) = ⨅ i, (c : EReal) + f i := by
  simpa only [add_comm] using iInf_add_coe f c

end RW
