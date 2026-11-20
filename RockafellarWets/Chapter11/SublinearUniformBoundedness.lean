/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform boundedness of sublinear mappings
-/
import RockafellarWets.Chapter11.SublinearNormDuality

open Set Metric Bornology
open scoped InnerProductSpace Pointwise ENNReal NNReal
namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Exercise 11.30: pointwise uniform bounds imply a uniform bound on the inner norms. -/
theorem svInnerNorm_uniform_boundedness {ι : Type*} (H : ι → E → Set F)
    (hh : ∀i, SvSublinear (H i)) (ho : ∀i, SvOsc (H i))
    (hb : ∀w:E, (⨆i, infEDist 0 (H i w)) < ⊤) : (⨆i, svInnerNorm (H i)) < ⊤ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi => simp
  | inr hi =>
    let i0 : ι := Classical.choice hi
    let C : Set E := ⋃i,svImage (svUpperAdjoint (H i)) (closedBall (0:F) 1)
    have hzero : (0:E) ∈ C := mem_iUnion.mpr ⟨i0,mem_svImage.mpr
      ⟨0,by simp,(svUpperAdjoint_properties (H i0)).2.1.1⟩⟩
    have hsupport (w:E) : (supportFunction C w).toENNReal = ⨆i,infEDist 0 (H i w) := by
      rw [show supportFunction C w = ⨆i,supportFunction
        (svImage (svUpperAdjoint (H i)) (closedBall (0:F) 1)) w from supportFunction_iUnion _ w]
      rw [ereal_toENNReal_iSup]
      simp only [← infEDist_eq_supportFunction_svUpperAdjoint (hh _) (ho _),EReal.toENNReal_coe]
    have hbounded : IsBounded C := ((nonempty_bounded_iff_supportFunction_finite C).mpr (fun w ↦ by
      have hnonneg : 0≤supportFunction C w := by simpa using inner_le_supportFunction hzero w
      have htop : supportFunction C w ≠ ⊤ := by
        intro he
        have h := hb w
        rw [← hsupport w,he,EReal.toENNReal_top] at h
        exact lt_irrefl _ h
      exact ⟨_,(EReal.coe_toReal htop (ne_of_gt (EReal.bot_lt_zero.trans_le hnonneg))).symm⟩)).2
    obtain ⟨R,hR⟩ := hbounded.exists_norm_le
    apply lt_of_le_of_lt (b := ENNReal.ofReal R) ?_ ENNReal.ofReal_lt_top
    apply iSup_le
    intro i
    rw [(sublinear_adjoint_norm_duality (hh i) (ho i)).2.2.1]
    apply svOuterNorm_le_iff_ball.mpr
    intro y hy v hv
    have hm : v ∈ C := mem_iUnion.mpr ⟨i,mem_svImage.mpr ⟨y,mem_closedBall_zero_iff.mpr hy,hv⟩⟩
    simpa only [← ENNReal.ofReal_coe_nnreal,coe_nnnorm] using ENNReal.ofReal_le_ofReal (hR v hm)

end RW
