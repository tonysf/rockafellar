/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Support of Euclidean products and extended distances
-/
import RockafellarWets.Chapter11.SupportDualOperations
import RockafellarWets.Chapter8.SupportExamples
import RockafellarWets.Chapter9.HomogeneousMappingNorms
import RockafellarWets.Chapter8.GraphicalDerivatives

open Set Metric
open scoped InnerProductSpace Pointwise ENNReal NNReal
namespace RW

theorem ereal_toENNReal_coe_galoisConnection :
    GaloisConnection EReal.toENNReal (fun x : ℝ≥0∞ ↦ (x:EReal)) := by
  intro x y
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal_eq_max, max_le_iff]
  exact and_iff_right (EReal.coe_ennreal_nonneg y)

theorem ereal_coe_ennreal_iInf {ι : Sort*} (f : ι → ℝ≥0∞) :
    ((⨅i,f i : ℝ≥0∞):EReal) = ⨅i,(f i:EReal) := ereal_toENNReal_coe_galoisConnection.u_iInf

theorem ereal_toENNReal_iSup {ι : Sort*} (f : ι → EReal) :
    (⨆i,f i).toENNReal = ⨆i,(f i).toENNReal := ereal_toENNReal_coe_galoisConnection.l_iSup

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem coe_infEDist_zero (C : Set E) :
    (infEDist 0 C:EReal) = ⨅x∈C,(‖x‖:EReal) := by
  rw [infEDist,ereal_coe_ennreal_iInf]
  apply iInf_congr
  intro x
  rw [ereal_coe_ennreal_iInf]
  apply iInf_congr
  intro hx
  rw [edist_dist,dist_zero_left,EReal.coe_ennreal_ofReal]
  simp only [max_eq_left (norm_nonneg x)]

theorem svInnerNorm_eq_iSup_infEDist (H : E → Set F) :
    svInnerNorm H = ⨆w∈closedBall (0:E) 1, infEDist 0 (H w) := by
  simp only [svInnerNorm,infEDist,edist_dist,dist_zero_left]
  simp only [← ENNReal.ofReal_coe_nnreal,coe_nnnorm]

theorem supportFunction_l2ProdSet (C : Set E) (D : Set F) (p : WithLp 2 (E×F)) :
    supportFunction (l2ProdSet C D) p = supportFunction C p.fst + supportFunction D p.snd := by
  apply le_antisymm
  · apply (supportFunction_le_iff _ _ _).mpr
    intro q hq
    rw [WithLp.prod_inner_apply,EReal.coe_add]
    exact add_le_add (inner_le_supportFunction hq.1 p.fst) (inner_le_supportFunction hq.2 p.snd)
  · apply EReal.add_le_of_forall_lt
    intro a ha b hb
    obtain ⟨x,hx⟩ := lt_iSup_iff.mp ha
    obtain ⟨y,hy⟩ := lt_iSup_iff.mp hb
    exact (add_le_add hx.le hy.le).trans (by
      simpa only [← EReal.coe_add,← WithLp.prod_inner_apply] using
        inner_le_supportFunction (show WithLp.toLp 2 ((x:E),(y:F)) ∈ l2ProdSet C D from ⟨x.property,y.property⟩) p)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Support of the cylinder used in the proof of 11.29. -/
theorem supportFunction_unitCylinder (p : WithLp 2 (E×F)) :
    supportFunction (l2ProdSet (closedBall (0:E) 1) (univ:Set F)) p =
      (‖p.fst‖:EReal)+indicatorVA ({0}:Set F) p.snd := by
  rw [supportFunction_l2ProdSet,(supportFunction_unitBall p.fst).1,supportFunction_univ]

/-- The support of a mapping's ball image as a support of a graph slice. -/
theorem supportFunction_svImage_unitBall (H : E → Set F) (y : F) :
    supportFunction (svImage H (closedBall (0:E) 1)) y =
      supportFunction (l2ProdSet (closedBall (0:E) 1) (univ:Set F) ∩ euclideanSvGraph H)
        (WithLp.toLp 2 (0,y)) := by
  apply le_antisymm
  · apply (supportFunction_le_iff _ _ _).mpr
    intro z hz
    obtain ⟨w,hw,hz⟩ := mem_svImage.mp hz
    have h := inner_le_supportFunction (show WithLp.toLp 2 (w,z) ∈
      l2ProdSet (closedBall (0:E) 1) (univ:Set F) ∩ euclideanSvGraph H from ⟨⟨hw,mem_univ _⟩,hz⟩)
      (WithLp.toLp 2 (0,y))
    simpa [WithLp.prod_inner_apply] using h
  · apply (supportFunction_le_iff _ _ _).mpr
    intro p hp
    have h := inner_le_supportFunction (show p.snd ∈ svImage H (closedBall (0:E) 1) from
      mem_svImage.mpr ⟨p.fst,hp.1.1,hp.2⟩) y
    simpa [WithLp.prod_inner_apply] using h

end RW
