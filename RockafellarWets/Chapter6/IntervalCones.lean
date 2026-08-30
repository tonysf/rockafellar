/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tangent and normal cones to closed intervals

The one-dimensional component of Example 6.10.  At an endpoint of a
nondegenerate closed interval the tangent cone is the appropriate half-line;
at an interior point it is the whole line; and for a degenerate interval it
is the origin.  The regular and limiting normal cones have the opposite sign
pattern and coincide by Theorem 6.9.
-/

import RockafellarWets.Chapter6.ConvexSets

open Set Topology
open scoped InnerProductSpace

namespace RW

section RadialCones

private theorem radialCone_Icc_left {a b : ℝ} (hab : a < b) :
    radialCone (Icc a b) a = Ici 0 := by
  ext w
  simp only [mem_radialCone, mem_Icc, mem_Ici, smul_eq_mul]
  constructor
  · rintro ⟨lam, hlam, hlow, -⟩
    by_contra hw
    have hwneg : w < 0 := lt_of_not_ge hw
    have : a + lam * w < a := by nlinarith
    exact (not_lt_of_ge hlow) this
  · intro hw
    by_cases hw0 : w = 0
    · subst w
      exact ⟨1, one_pos, by norm_num, by simpa using hab.le⟩
    · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
      refine ⟨(b - a) / w, div_pos (sub_pos.mpr hab) hwpos, ?_⟩
      have hcalc : a + (b - a) / w * w = b := by
        field_simp [hw0]
        ring
      rw [hcalc]
      exact ⟨hab.le, le_rfl⟩

private theorem radialCone_Icc_right {a b : ℝ} (hab : a < b) :
    radialCone (Icc a b) b = Iic 0 := by
  ext w
  simp only [mem_radialCone, mem_Icc, mem_Iic, smul_eq_mul]
  constructor
  · rintro ⟨lam, hlam, -, hupp⟩
    by_contra hw
    have hwpos : 0 < w := lt_of_not_ge hw
    have : b < b + lam * w := by nlinarith
    exact (not_lt_of_ge hupp) this
  · intro hw
    by_cases hw0 : w = 0
    · subst w
      exact ⟨1, one_pos, by simpa using hab.le, by norm_num⟩
    · have hwneg : w < 0 := lt_of_le_of_ne hw hw0
      refine ⟨(a - b) / w, div_pos_of_neg_of_neg (sub_neg.mpr hab) hwneg, ?_⟩
      have hcalc : b + (a - b) / w * w = a := by
        field_simp [hw0]
        ring
      rw [hcalc]
      exact ⟨le_rfl, hab.le⟩

private theorem radialCone_Icc_interior {a b x : ℝ} (hax : a < x) (hxb : x < b) :
    radialCone (Icc a b) x = univ := by
  ext w
  simp only [mem_radialCone, mem_Icc, mem_univ, iff_true, smul_eq_mul]
  rcases lt_trichotomy w 0 with hwneg | rfl | hwpos
  · refine ⟨(a - x) / w, div_pos_of_neg_of_neg (sub_neg.mpr hax) hwneg, ?_⟩
    have hcalc : x + (a - x) / w * w = a := by
      field_simp [ne_of_lt hwneg]
      ring
    rw [hcalc]
    exact ⟨le_rfl, (hax.trans hxb).le⟩
  · exact ⟨1, one_pos, by simpa using hax.le, by simpa using hxb.le⟩
  · refine ⟨(b - x) / w, div_pos (sub_pos.mpr hxb) hwpos, ?_⟩
    have hcalc : x + (b - x) / w * w = b := by
      field_simp [ne_of_gt hwpos]
      ring
    rw [hcalc]
    exact ⟨(hax.trans hxb).le, le_rfl⟩

private theorem radialCone_Icc_self (a : ℝ) : radialCone (Icc a a) a = {0} := by
  rw [Icc_self]
  ext w
  simp only [mem_radialCone, mem_singleton_iff, smul_eq_mul]
  constructor
  · rintro ⟨lam, hlam, h⟩
    have hprod : lam * w = 0 := by linarith
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hlam)
  · rintro rfl
    exact ⟨1, one_pos, by simp⟩

private theorem radialCone_Ici_endpoint (a : ℝ) : radialCone (Ici a) a = Ici 0 := by
  ext w
  simp only [mem_radialCone, mem_Ici, smul_eq_mul]
  constructor
  · rintro ⟨lam, hlam, h⟩
    nlinarith
  · intro hw
    exact ⟨1, one_pos, by linarith⟩

private theorem radialCone_Ici_interior {a x : ℝ} (hax : a < x) :
    radialCone (Ici a) x = univ := by
  ext w
  simp only [mem_radialCone, mem_Ici, mem_univ, iff_true, smul_eq_mul]
  by_cases hw : 0 ≤ w
  · exact ⟨1, one_pos, by linarith⟩
  · have hwneg : w < 0 := lt_of_not_ge hw
    refine ⟨(a - x) / w, div_pos_of_neg_of_neg (sub_neg.mpr hax) hwneg, ?_⟩
    have hcalc : x + (a - x) / w * w = a := by
      field_simp [ne_of_lt hwneg]
      ring
    rw [hcalc]

private theorem radialCone_Iic_endpoint (b : ℝ) : radialCone (Iic b) b = Iic 0 := by
  ext w
  simp only [mem_radialCone, mem_Iic, smul_eq_mul]
  constructor
  · rintro ⟨lam, hlam, h⟩
    nlinarith
  · intro hw
    exact ⟨1, one_pos, by linarith⟩

private theorem radialCone_Iic_interior {b x : ℝ} (hxb : x < b) :
    radialCone (Iic b) x = univ := by
  ext w
  simp only [mem_radialCone, mem_Iic, mem_univ, iff_true, smul_eq_mul]
  by_cases hw : w ≤ 0
  · exact ⟨1, one_pos, by linarith⟩
  · have hwpos : 0 < w := lt_of_not_ge hw
    refine ⟨(b - x) / w, div_pos (sub_pos.mpr hxb) hwpos, ?_⟩
    have hcalc : x + (b - x) / w * w = b := by
      field_simp [ne_of_gt hwpos]
      ring
    rw [hcalc]

end RadialCones

section TangentCones

/-- The tangent cone at the left endpoint of a nondegenerate bounded interval. -/
theorem tangentCone_Icc_left {a b : ℝ} (hab : a < b) :
    tangentCone (Icc a b) a = Ici 0 := by
  rw [tangentCone_eq_closure_radialCone (convex_Icc a b) (left_mem_Icc.mpr hab.le),
    radialCone_Icc_left hab, isClosed_Ici.closure_eq]

/-- The tangent cone at the right endpoint of a nondegenerate bounded interval. -/
theorem tangentCone_Icc_right {a b : ℝ} (hab : a < b) :
    tangentCone (Icc a b) b = Iic 0 := by
  rw [tangentCone_eq_closure_radialCone (convex_Icc a b) (right_mem_Icc.mpr hab.le),
    radialCone_Icc_right hab, isClosed_Iic.closure_eq]

/-- The tangent cone at an interior point of a bounded interval is the whole line. -/
theorem tangentCone_Icc_interior {a b x : ℝ} (hax : a < x) (hxb : x < b) :
    tangentCone (Icc a b) x = univ := by
  rw [tangentCone_eq_closure_radialCone (convex_Icc a b) ⟨hax.le, hxb.le⟩,
    radialCone_Icc_interior hax hxb, isClosed_univ.closure_eq]

/-- The tangent cone of the degenerate interval `Icc a a` at its point. -/
theorem tangentCone_Icc_self (a : ℝ) : tangentCone (Icc a a) a = {0} := by
  rw [tangentCone_eq_closure_radialCone (convex_Icc a a) ⟨le_rfl, le_rfl⟩,
    radialCone_Icc_self, isClosed_singleton.closure_eq]

/-- The tangent cone at the endpoint of a lower closed half-line. -/
theorem tangentCone_Ici_endpoint (a : ℝ) : tangentCone (Ici a) a = Ici 0 := by
  rw [tangentCone_eq_closure_radialCone (convex_Ici a) self_mem_Ici,
    radialCone_Ici_endpoint, isClosed_Ici.closure_eq]

/-- The tangent cone at an interior point of a lower closed half-line. -/
theorem tangentCone_Ici_interior {a x : ℝ} (hax : a < x) :
    tangentCone (Ici a) x = univ := by
  rw [tangentCone_eq_closure_radialCone (convex_Ici a) hax.le,
    radialCone_Ici_interior hax, isClosed_univ.closure_eq]

/-- The tangent cone at the endpoint of an upper closed half-line. -/
theorem tangentCone_Iic_endpoint (b : ℝ) : tangentCone (Iic b) b = Iic 0 := by
  rw [tangentCone_eq_closure_radialCone (convex_Iic b) self_mem_Iic,
    radialCone_Iic_endpoint, isClosed_Iic.closure_eq]

/-- The tangent cone at an interior point of an upper closed half-line. -/
theorem tangentCone_Iic_interior {b x : ℝ} (hxb : x < b) :
    tangentCone (Iic b) x = univ := by
  rw [tangentCone_eq_closure_radialCone (convex_Iic b) hxb.le,
    radialCone_Iic_interior hxb, isClosed_univ.closure_eq]

end TangentCones

section RegularNormalCones

/-- The regular normal cone at the left endpoint of a nondegenerate bounded interval. -/
theorem regularNormalCone_Icc_left {a b : ℝ} (hab : a < b) :
    regularNormalCone (Icc a b) a = Iic 0 := by
  rw [regularNormalCone_eq_of_convex (convex_Icc a b) (left_mem_Icc.mpr hab.le)]
  ext v
  simp only [mem_setOf_eq, mem_Iic]
  constructor
  · intro hv
    have hb := hv b (right_mem_Icc.mpr hab.le)
    simp only [RCLike.inner_apply, conj_trivial] at hb
    nlinarith
  · intro hv y hy
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      mul_nonpos_of_nonpos_of_nonneg hv (sub_nonneg.mpr hy.1)

/-- The regular normal cone at the right endpoint of a nondegenerate bounded interval. -/
theorem regularNormalCone_Icc_right {a b : ℝ} (hab : a < b) :
    regularNormalCone (Icc a b) b = Ici 0 := by
  rw [regularNormalCone_eq_of_convex (convex_Icc a b) (right_mem_Icc.mpr hab.le)]
  ext v
  simp only [mem_setOf_eq, mem_Ici]
  constructor
  · intro hv
    have ha := hv a (left_mem_Icc.mpr hab.le)
    simp only [RCLike.inner_apply, conj_trivial] at ha
    nlinarith
  · intro hv y hy
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy.2) hv

/-- The regular normal cone at an interior point of a bounded interval. -/
theorem regularNormalCone_Icc_interior {a b x : ℝ} (hax : a < x) (hxb : x < b) :
    regularNormalCone (Icc a b) x = {0} := by
  rw [regularNormalCone_eq_of_convex (convex_Icc a b) ⟨hax.le, hxb.le⟩]
  ext v
  simp only [mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro hv
    have ha := hv a ⟨le_rfl, (hax.trans hxb).le⟩
    have hb := hv b ⟨(hax.trans hxb).le, le_rfl⟩
    simp only [RCLike.inner_apply, conj_trivial] at ha hb
    nlinarith
  · rintro rfl y -
    simp

/-- The regular normal cone to the degenerate interval `Icc a a` is the whole line. -/
theorem regularNormalCone_Icc_self (a : ℝ) :
    regularNormalCone (Icc a a) a = univ := by
  rw [Icc_self, regularNormalCone_eq_of_convex (convex_singleton a) (by simp)]
  ext v
  simp

/-- The regular normal cone at the endpoint of a lower closed half-line. -/
theorem regularNormalCone_Ici_endpoint (a : ℝ) :
    regularNormalCone (Ici a) a = Iic 0 := by
  rw [regularNormalCone_eq_of_convex (convex_Ici a) self_mem_Ici]
  ext v
  simp only [mem_setOf_eq, mem_Iic]
  constructor
  · intro hv
    have h := hv (a + 1) (by simp)
    simpa only [RCLike.inner_apply, conj_trivial, add_sub_cancel_left, one_mul] using h
  · intro hv y hy
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      mul_nonpos_of_nonpos_of_nonneg hv (sub_nonneg.mpr hy)

/-- The regular normal cone at an interior point of a lower closed half-line. -/
theorem regularNormalCone_Ici_interior {a x : ℝ} (hax : a < x) :
    regularNormalCone (Ici a) x = {0} := by
  rw [regularNormalCone_eq_of_convex (convex_Ici a) hax.le]
  ext v
  simp only [mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro hv
    have ha := hv a self_mem_Ici
    have hp := hv (x + 1) (by
      simp only [mem_Ici]
      linarith)
    simp only [RCLike.inner_apply, conj_trivial] at ha hp
    nlinarith
  · rintro rfl y -
    simp

/-- The regular normal cone at the endpoint of an upper closed half-line. -/
theorem regularNormalCone_Iic_endpoint (b : ℝ) :
    regularNormalCone (Iic b) b = Ici 0 := by
  rw [regularNormalCone_eq_of_convex (convex_Iic b) self_mem_Iic]
  ext v
  simp only [mem_setOf_eq, mem_Ici]
  constructor
  · intro hv
    have h := hv (b - 1) (by simp)
    simp only [RCLike.inner_apply, conj_trivial] at h
    nlinarith
  · intro hv y hy
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) hv

/-- The regular normal cone at an interior point of an upper closed half-line. -/
theorem regularNormalCone_Iic_interior {b x : ℝ} (hxb : x < b) :
    regularNormalCone (Iic b) x = {0} := by
  rw [regularNormalCone_eq_of_convex (convex_Iic b) hxb.le]
  ext v
  simp only [mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro hv
    have hb := hv b self_mem_Iic
    have hm := hv (x - 1) (by
      simp only [mem_Iic]
      linarith)
    simp only [RCLike.inner_apply, conj_trivial] at hb hm
    nlinarith
  · rintro rfl y -
    simp

end RegularNormalCones

section LimitingNormalCones

/-- The limiting normal cone at the left endpoint of a nondegenerate bounded interval. -/
theorem normalCone_Icc_left {a b : ℝ} (hab : a < b) :
    normalCone (Icc a b) a = Iic 0 := by
  rw [normalCone_eq_regularNormalCone_of_convex (convex_Icc a b)
    (left_mem_Icc.mpr hab.le), regularNormalCone_Icc_left hab]

/-- The limiting normal cone at the right endpoint of a nondegenerate bounded interval. -/
theorem normalCone_Icc_right {a b : ℝ} (hab : a < b) :
    normalCone (Icc a b) b = Ici 0 := by
  rw [normalCone_eq_regularNormalCone_of_convex (convex_Icc a b)
    (right_mem_Icc.mpr hab.le), regularNormalCone_Icc_right hab]

/-- The limiting normal cone at an interior point of a bounded interval. -/
theorem normalCone_Icc_interior {a b x : ℝ} (hax : a < x) (hxb : x < b) :
    normalCone (Icc a b) x = {0} := by
  rw [normalCone_eq_regularNormalCone_of_convex (convex_Icc a b) ⟨hax.le, hxb.le⟩,
    regularNormalCone_Icc_interior hax hxb]

/-- The limiting normal cone to the degenerate interval `Icc a a` is the whole line. -/
theorem normalCone_Icc_self (a : ℝ) : normalCone (Icc a a) a = univ := by
  rw [normalCone_eq_regularNormalCone_of_convex (convex_Icc a a) ⟨le_rfl, le_rfl⟩,
    regularNormalCone_Icc_self]

/-- The limiting normal cone at the endpoint of a lower closed half-line. -/
theorem normalCone_Ici_endpoint (a : ℝ) : normalCone (Ici a) a = Iic 0 := by
  rw [normalCone_eq_regularNormalCone_of_convex (convex_Ici a) self_mem_Ici,
    regularNormalCone_Ici_endpoint]

/-- The limiting normal cone at an interior point of a lower closed half-line. -/
theorem normalCone_Ici_interior {a x : ℝ} (hax : a < x) :
    normalCone (Ici a) x = {0} := by
  rw [normalCone_eq_regularNormalCone_of_convex (convex_Ici a) hax.le,
    regularNormalCone_Ici_interior hax]

/-- The limiting normal cone at the endpoint of an upper closed half-line. -/
theorem normalCone_Iic_endpoint (b : ℝ) : normalCone (Iic b) b = Ici 0 := by
  rw [normalCone_eq_regularNormalCone_of_convex (convex_Iic b) self_mem_Iic,
    regularNormalCone_Iic_endpoint]

/-- The limiting normal cone at an interior point of an upper closed half-line. -/
theorem normalCone_Iic_interior {b x : ℝ} (hxb : x < b) :
    normalCone (Iic b) x = {0} := by
  rw [normalCone_eq_regularNormalCone_of_convex (convex_Iic b) hxb.le,
    regularNormalCone_Iic_interior hxb]

end LimitingNormalCones

section Regularity

/-- Every point of a bounded closed interval is geometrically derivable. -/
theorem isGeometricallyDerivable_Icc {a b x : ℝ} (hx : x ∈ Icc a b) :
    IsGeometricallyDerivable (Icc a b) x :=
  isGeometricallyDerivable_of_convex (convex_Icc a b) hx

/-- Every point of a bounded closed interval is Clarke regular. -/
theorem isClarkeRegularAt_Icc {a b x : ℝ} (hx : x ∈ Icc a b) :
    IsClarkeRegularAt (Icc a b) x :=
  isClarkeRegularAt_of_convex (convex_Icc a b) hx
    (RW.IsClosed.isLocallyClosedAt isClosed_Icc x)

/-- Every point of a lower closed half-line is geometrically derivable. -/
theorem isGeometricallyDerivable_Ici {a x : ℝ} (hx : x ∈ Ici a) :
    IsGeometricallyDerivable (Ici a) x :=
  isGeometricallyDerivable_of_convex (convex_Ici a) hx

/-- Every point of a lower closed half-line is Clarke regular. -/
theorem isClarkeRegularAt_Ici {a x : ℝ} (hx : x ∈ Ici a) :
    IsClarkeRegularAt (Ici a) x :=
  isClarkeRegularAt_of_convex (convex_Ici a) hx
    (RW.IsClosed.isLocallyClosedAt isClosed_Ici x)

/-- Every point of an upper closed half-line is geometrically derivable. -/
theorem isGeometricallyDerivable_Iic {b x : ℝ} (hx : x ∈ Iic b) :
    IsGeometricallyDerivable (Iic b) x :=
  isGeometricallyDerivable_of_convex (convex_Iic b) hx

/-- Every point of an upper closed half-line is Clarke regular. -/
theorem isClarkeRegularAt_Iic {b x : ℝ} (hx : x ∈ Iic b) :
    IsClarkeRegularAt (Iic b) x :=
  isClarkeRegularAt_of_convex (convex_Iic b) hx
    (RW.IsClosed.isLocallyClosedAt isClosed_Iic x)

end Regularity

end RW
