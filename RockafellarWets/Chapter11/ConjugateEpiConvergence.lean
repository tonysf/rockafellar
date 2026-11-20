/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuity of conjugation for epi-convergence
-/

import RockafellarWets.Chapter11.MoreauConjugacy
import RockafellarWets.Chapter7.ConvexMoreauCharacterization

open Filter Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The finite real representatives of complementary envelopes at parameter one. -/
theorem moreau_conjugate_one_toReal {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (x : E) :
    (moreauEnvelopeEReal (RW.fenchelConjugate f) 1 x).toReal =
      moreauQuadratic 1 x - (moreauEnvelopeEReal f 1 x).toReal := by
  have ha := moreauEnvelopeEReal_finite hc hl hp one_pos x
  have hb := moreauEnvelopeEReal_finite (convex_epigraph_fenchelConjugate f)
    (lowerSemicontinuous_fenchelConjugate f) (isProper_fenchelConjugate hp hl hc) one_pos x
  have h := moreau_conjugate_decomposition hp hl hc one_pos x
  simp only [inv_one, one_smul] at h
  rw [← EReal.coe_toReal ha.2.ne ha.1.ne',
    ← EReal.coe_toReal hb.2.ne hb.1.ne', ← EReal.coe_add, EReal.coe_eq_coe_iff] at h
  linarith

/-- The forward half of **Theorem 11.34**. -/
theorem EpiConverges.fenchelConjugate {f : ℕ → E → EReal} {g : E → EReal}
    (he : EpiConverges f g) (hp : ∀ n, IsProper (f n))
    (hl : ∀ n, LowerSemicontinuous (f n)) (hc : ∀ n, Convex ℝ (epigraph (f n)))
    (hgp : IsProper g) (hgl : LowerSemicontinuous g) (hgc : Convex ℝ (epigraph g)) :
    EpiConverges (fun n ↦ RW.fenchelConjugate (f n)) (RW.fenchelConjugate g) := by
  apply (convex_epiConverges_iff_tendsto_one_moreauEnvelope
    (fun n ↦ convex_epigraph_fenchelConjugate (f n))
    (fun n ↦ lowerSemicontinuous_fenchelConjugate (f n))
    (fun n ↦ isProper_fenchelConjugate (hp n) (hl n) (hc n))
    (convex_epigraph_fenchelConjugate g) (lowerSemicontinuous_fenchelConjugate g)
    (isProper_fenchelConjugate hgp hgl hgc)).mpr
  refine ⟨1, one_pos, fun x ↦ ?_⟩
  have hthr := eventualProxThreshold_eq_top_of_convex_epiConverges he hc hl hp hgp
  have ht := (tendsto_moreauEnvelopeEReal_of_epiConverges he hl hgp
    (tendsto_const_nhds (x := x)) tendsto_const_nhds one_pos
    (hthr ▸ EReal.coe_lt_top 1)).2
  have ha := moreauEnvelopeEReal_finite hgc hgl hgp one_pos x
  have htr := (EReal.tendsto_toReal ha.2.ne ha.1.ne').comp ht
  have hdiff := (tendsto_const_nhds (x := moreauQuadratic 1 x)).sub htr
  have heq (n : ℕ) := moreau_conjugate_one_toReal (hp n) (hl n) (hc n) x
  have hgoal := moreau_conjugate_one_toReal hgp hgl hgc x
  rw [← hgoal] at hdiff
  have hreal : Tendsto (fun n ↦ (moreauEnvelopeEReal (RW.fenchelConjugate (f n)) 1 x).toReal)
      atTop (𝓝 (moreauEnvelopeEReal (RW.fenchelConjugate g) 1 x).toReal) :=
    hdiff.congr (fun n ↦ (heq n).symm)
  have hcoe := EReal.tendsto_coe.mpr hreal
  have hfinite (n : ℕ) := moreauEnvelopeEReal_finite (convex_epigraph_fenchelConjugate (f n))
    (lowerSemicontinuous_fenchelConjugate (f n))
    (isProper_fenchelConjugate (hp n) (hl n) (hc n)) one_pos x
  have hgfinite := moreauEnvelopeEReal_finite (convex_epigraph_fenchelConjugate g)
    (lowerSemicontinuous_fenchelConjugate g) (isProper_fenchelConjugate hgp hgl hgc) one_pos x
  simpa only [EReal.coe_toReal (hfinite _).2.ne (hfinite _).1.ne',
    EReal.coe_toReal hgfinite.2.ne hgfinite.1.ne'] using hcoe

/-- **Theorem 11.34**, conjugation is continuous and has a continuous inverse
on the proper closed convex functions with the epi-convergence topology. -/
theorem epiConverges_fenchelConjugate_iff {f : ℕ → E → EReal} {g : E → EReal}
    (hp : ∀ n, IsProper (f n)) (hl : ∀ n, LowerSemicontinuous (f n))
    (hc : ∀ n, Convex ℝ (epigraph (f n))) (hgp : IsProper g)
    (hgl : LowerSemicontinuous g) (hgc : Convex ℝ (epigraph g)) :
    EpiConverges (fun n ↦ RW.fenchelConjugate (f n)) (RW.fenchelConjugate g) ↔ EpiConverges f g := by
  constructor
  · intro h
    have h' := h.fenchelConjugate (fun n ↦ isProper_fenchelConjugate (hp n) (hl n) (hc n))
      (fun n ↦ lowerSemicontinuous_fenchelConjugate (f n))
      (fun n ↦ convex_epigraph_fenchelConjugate (f n))
      (isProper_fenchelConjugate hgp hgl hgc) (lowerSemicontinuous_fenchelConjugate g)
      (convex_epigraph_fenchelConjugate g)
    simpa only [fenchelConjugate_fenchelConjugate_eq (hp _) (hl _) (hc _),
      fenchelConjugate_fenchelConjugate_eq hgp hgl hgc] using h'
  · intro h
    exact h.fenchelConjugate hp hl hc hgp hgl hgc

end RW
