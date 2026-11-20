/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polyhedral subgradients of PLQ functions
-/
import RockafellarWets.Chapter10.PLQSubderivatives
import RockafellarWets.Chapter10.PLQOperations
import RockafellarWets.Chapter10.ConvexPolyhedralUnions
import RockafellarWets.Chapter8.RegularSupportDuality

open Set Filter Topology Classical
open scoped InnerProductSpace

namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The regular subdifferential of any PLQ function is polyhedral, including
at a point where this subdifferential is empty. -/
theorem IsPiecewiseLinearQuadratic.isPolyhedral_regularSubdifferential {f : E → EReal}
    (h : IsPiecewiseLinearQuadratic f) {x : E} (hx : x ∈ effectiveDomain f) :
    IsPolyhedral (regularSubdifferential f x) := by
  have hfin : f x = ((f x).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (h.ne_bot x)).symm
  have hdf := h.subderivative_piecewiseLinear hx
  obtain ⟨m,C,q,hC,hdom,hf⟩ := h
  let J (i : Fin m) : Set E := if x ∈ C i then
    (fun v ↦ v-gradient (q i).eval x) ⁻¹' normalCone (C i) x else univ
  have hJ (i : Fin m) : IsPolyhedral (J i) := by
    dsimp [J]
    split_ifs with hi
    · simpa only [ContinuousLinearMap.id_apply,sub_eq_add_neg] using
        ((hC i).isPolyhedral_normalCone hi).affine_preimage (ContinuousLinearMap.id ℝ E)
          (-gradient (q i).eval x)
    · exact IsPolyhedral.univ
  have hvalue (i : Fin m) (hi : x ∈ C i) {w : E} (hw : w ∈ tangentCone (C i) x) :
      subderivative f x w = (⟪gradient (q i).eval x,w⟫_ℝ : EReal) := by
    rw [plqRepresentation_subderivative_on_piece hC hdom hf hi hw,
      inner_gradient_left (((q i).contDiff 1).differentiable (by norm_num) x)]
  have he : regularSubdifferential f x = ⋂ i, J i := by
    ext v
    rw [mem_regularSubdifferential_iff_inner_le_subderivative hfin,mem_iInter]
    constructor
    · intro hv i
      by_cases hi : x ∈ C i
      · simp only [J,if_pos hi,mem_preimage]
        rw [normalCone_eq_regularNormalCone_of_convex (hC i).convex hi,
          mem_regularNormalCone_iff_inner_nonpos hi]
        intro w hw
        have hb := hv w
        rw [hvalue i hi hw,EReal.coe_le_coe_iff] at hb
        simpa [inner_sub_left] using sub_nonpos.mpr hb
      · simp [J,hi]
    · intro hv w
      by_cases ht : subderivative f x w = ⊤
      · rw [ht]; exact le_top
      · have hwdom : w ∈ tangentCone (effectiveDomain f) x := hdf.2 ▸ (show w ∈ effectiveDomain (subderivative f x) from lt_top_iff_ne_top.mpr ht)
        rw [hdom,tangentCone_finite_iUnion] at hwdom
        obtain ⟨i,hwi⟩ := mem_iUnion.mp hwdom
        have hxi : x ∈ C i := by
          obtain ⟨a,t,ha,hat,_⟩ := hwi
          exact (hC i).isClosed.mem_of_tendsto hat (.of_forall ha)
        have hvi : v-gradient (q i).eval x ∈ normalCone (C i) x := by simpa [J,hxi] using hv i
        rw [normalCone_eq_regularNormalCone_of_convex (hC i).convex hxi,
          mem_regularNormalCone_iff_inner_nonpos hxi] at hvi
        rw [hvalue i hxi hwi,EReal.coe_le_coe_iff]
        exact sub_nonpos.mp (by simpa [inner_sub_left] using hvi w hwi)
  rw [he]
  simpa using IsPolyhedral.iInter_finset Finset.univ J (fun i _ ↦ hJ i)

/-- **Proposition 10.21**, all convex subgradient conclusions. -/
theorem IsPiecewiseLinearQuadratic.convex_subgradient_properties {f : E → EReal}
    (h : IsPiecewiseLinearQuadratic f) (hc : Convex ℝ (epigraph f))
    {x : E} (hx : x ∈ effectiveDomain f) :
    (subdifferential f x).Nonempty ∧ IsPolyhedral (subdifferential f x) ∧
      IsPolyhedral (horizonSubdifferential f x) := by
  have hfin : f x = ((f x).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (h.ne_bot x)).symm
  have hp : IsProper f := ⟨⟨x,hx⟩,fun y ↦ lt_of_le_of_ne bot_le (h.ne_bot y).symm⟩
  have hl := isLocallyLscAt_of_isLocallyClosedAt_epigraph hfin
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal f h.lowerSemicontinuous) _)
  have hr := (isSubdifferentiallyRegularAt_of_convex hc hl).1
  refine ⟨hr.subdifferential_nonempty_iff.mpr ?_,?_,?_⟩
  · exact (h.subderivative_piecewiseLinear hx).1.isPiecewiseLinearQuadratic.ne_bot 0
  · rw [subdifferential_eq_regularSubdifferential_of_convex hc hp hfin]
    exact h.isPolyhedral_regularSubdifferential hx
  · rw [horizonSubdifferential_eq_normalCone_domain_of_locallyLsc hc hp hl hfin]
    exact (h.isPolyhedral_effectiveDomain hc).isPolyhedral_normalCone hx

end RW
