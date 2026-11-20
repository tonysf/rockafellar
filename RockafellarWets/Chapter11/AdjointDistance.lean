/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Distance and support identities for sublinear adjoints
-/
import RockafellarWets.Chapter11.SublinearAdjoints
import RockafellarWets.Chapter11.SupportProducts

open Set Metric Topology
open scoped InnerProductSpace Pointwise ENNReal NNReal
namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The support of the image of the unit ball is the distance to a lower-adjoint fiber. -/
theorem supportFunction_svImage_eq_infEDist_lowerAdjoint {H : E → Set F}
    (hh : SvSublinear H) (ho : SvOsc H) (y : F) :
    supportFunction (svImage H (closedBall (0:E) 1)) y = (infEDist 0 (svLowerAdjoint H y):EReal) := by
  classical
  let C : Set (WithLp 2 (E×F)) := l2ProdSet (closedBall (0:E) 1) univ
  have hc : Convex ℝ C := by
    have hp : Convex ℝ (closedBall (0:E) 1 ×ˢ (univ:Set F)) :=
      (convex_closedBall (0:E) 1).prod convex_univ
    exact hp.linear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearMap
  have hcl : IsClosed C := isClosed_l2ProdSet isClosed_closedBall isClosed_univ
  have h0 : (0:WithLp 2 (E×F)) ∈ interior C := by
    apply mem_interior_iff_mem_nhds.mpr
    have hpre := (WithLp.fstL 2 ℝ E F).continuous.tendsto 0 (closedBall_mem_nhds (0:E) zero_lt_one)
    change {p : WithLp 2 (E×F) | p.fst ∈ closedBall (0:E) 1} ∈ nhds 0 at hpre
    simpa [C,l2ProdSet] using hpre
  rw [supportFunction_svImage_unitBall]
  change supportFunction (C ∩ euclideanSvGraph H) (WithLp.toLp 2 (0,y)) = _
  rw [supportFunction_inter_of_meets_interior hc hh.convex_euclideanSvGraph hcl
    ho.isClosed_euclideanSvGraph (Or.inr ⟨0,h0,hh.1.1⟩),
    supportFunction_cone hh.isCone_euclideanSvGraph,epiSum_apply,coe_infEDist_zero]
  have hformula (p : WithLp 2 (E×F)) :
      supportFunction C (WithLp.toLp 2 (0,y)-p)+indicatorVA (polarCone (euclideanSvGraph H)) p =
        if p.snd=y ∧ p∈polarCone (euclideanSvGraph H) then (‖p.fst‖:EReal) else ⊤ := by
    change supportFunction (l2ProdSet (closedBall (0:E) 1) univ) _ + _ = _
    rw [supportFunction_unitCylinder]
    have hiff : y-p.snd=0 ↔ p.snd=y := by rw [sub_eq_zero]; exact eq_comm
    by_cases hs : p.snd=y <;> by_cases hp : p∈polarCone (euclideanSvGraph H)
    all_goals simp [indicatorVA,hs,hp,hiff]
  simp_rw [hformula]
  apply le_antisymm
  · apply le_iInf₂
    intro v hv
    apply iInf_le_of_le (WithLp.toLp 2 (-v,y))
    have hp := mem_svLowerAdjoint_iff_polarCone.mp hv
    simp [hp]
  · apply le_iInf
    intro p
    split_ifs with hp
    · have hmem : -p.fst ∈ svLowerAdjoint H y := by
        apply mem_svLowerAdjoint_iff_polarCone.mpr
        have he : WithLp.toLp 2 (- -p.fst,y) = p := by
          apply WithLp.ofLp_injective 2
          exact Prod.ext (neg_neg _) hp.1.symm
        rw [he]
        exact hp.2
      calc
        _ ≤ (‖-p.fst‖:EReal) := iInf₂_le_of_le (-p.fst) hmem le_rfl
        _ = (‖p.fst‖:EReal) := by simp
    · exact le_top

/-- The dual distance/support identity in Example 11.29. -/
theorem infEDist_eq_supportFunction_svUpperAdjoint {H : E → Set F}
    (hh : SvSublinear H) (ho : SvOsc H) (w : E) :
    (infEDist 0 (H w):EReal) = supportFunction (svImage (svUpperAdjoint H) (closedBall (0:F) 1)) w := by
  have h := supportFunction_svImage_eq_infEDist_lowerAdjoint (svUpperAdjoint_properties H).2
    (svUpperAdjoint_properties H).1 w
  rw [svLowerAdjoint_svUpperAdjoint hh ho] at h
  exact h.symm

end RW
