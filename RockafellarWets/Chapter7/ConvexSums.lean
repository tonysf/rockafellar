/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Sums of convex functions under varying linear maps
-/

import Mathlib.Analysis.Normed.Operator.Prod
import RockafellarWets.Chapter7.EpigraphAddition
import RockafellarWets.Chapter7.EpiLimitProperties
import RockafellarWets.Chapter7.EpiLimitCharacterization
import RockafellarWets.Chapter4.ConvexIntersections

open Filter Function Set Topology
open scoped Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The auxiliary variable `r` supplies a finite epigraph height for `h`;
the second height is passed through to `g`. -/
private noncomputable def levelConstraintMap (L : E →L[ℝ] F) : (E × ℝ) × ℝ →L[ℝ] F × ℝ :=
  (L.comp (ContinuousLinearMap.fst ℝ E ℝ)).prodMap (ContinuousLinearMap.id ℝ ℝ)

omit [FiniteDimensional ℝ F] in
private theorem continuous_levelConstraintMap :
    Continuous (levelConstraintMap (E := E) (F := F)) :=
  Continuous.prod_mapL ℝ (continuous_id.clm_comp_const (ContinuousLinearMap.fst ℝ E ℝ)) continuous_const

omit [FiniteDimensional ℝ F] in
private theorem image_levelConstraintMap (L : E →L[ℝ] F) (h : E → EReal) :
    levelConstraintMap L '' (epigraph h ×ˢ (univ : Set ℝ)) =
      (L '' effectiveDomain h) ×ˢ (univ : Set ℝ) := by
  ext ⟨u, s⟩
  constructor
  · rintro ⟨⟨⟨x, r⟩, t⟩, ⟨hxr, _⟩, heq⟩
    exact ⟨⟨x, hxr.trans_lt (EReal.coe_lt_top _), congrArg Prod.fst heq⟩, mem_univ _⟩
  · rintro ⟨⟨x, hx, rfl⟩, _⟩
    obtain ⟨r, hr, _⟩ := EReal.exists_between_coe_real (show h x < ⊤ from hx)
    exact ⟨((x, r), s), ⟨hr.le, mem_univ _⟩, rfl⟩

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
private theorem cylinder_sub_epigraph (D : Set F) (g : F → EReal) :
    D ×ˢ (univ : Set ℝ) - epigraph g = (D - effectiveDomain g) ×ˢ (univ : Set ℝ) := by
  ext ⟨u, a⟩
  constructor
  · rintro ⟨⟨y, r⟩, ⟨hy, _⟩, ⟨z, s⟩, hz, heq⟩
    exact ⟨⟨y, hy, z, hz.trans_lt (EReal.coe_lt_top _), congrArg Prod.fst heq⟩, mem_univ _⟩
  · rintro ⟨⟨y, hy, z, hz, rfl⟩, _⟩
    obtain ⟨s, hs, _⟩ := EReal.exists_between_coe_real (show g z < ⊤ from hz)
    exact ⟨(y, a+s), ⟨hy, mem_univ _⟩, (z, s), hs.le, by simp⟩

/-- **Exercise 7.47**, upper epi-limit. Even for improper convex functions,
inf-addition has an exact representation using two finite epigraph heights. -/
theorem epiUpperLimit_infAddition_comp_linear_le
    {g : ℕ → F → EReal} {h : ℕ → E → EReal} {G : F → EReal} {H : E → EReal}
    {L : ℕ → E →L[ℝ] F} {A : E →L[ℝ] F}
    (hg : ∀ n, Convex ℝ (epigraph (g n))) (hh : ∀ n, Convex ℝ (epigraph (h n)))
    (hG : epiUpperLimit g ≤ G) (hH : epiUpperLimit h ≤ H)
    (hL : Tendsto L atTop (𝓝 A))
    (hsep : CannotBeSeparated (effectiveDomain G) (A '' effectiveDomain H)) :
    epiUpperLimit (fun n x ↦ infAddition (g n (L n x)) (h n x)) ≤
      fun x ↦ infAddition (G (A x)) (H x) := by
  let C (n : ℕ) := epigraph (h n) ×ˢ (univ : Set ℝ)
  let C₀ := epigraph H ×ˢ (univ : Set ℝ)
  have hC : C₀ ⊆ innerSetLimit C := by
    have hh' := epigraph_subset_epigraph_iff.mpr hH
    rw [epigraph_epiUpperLimit] at hh'
    simpa only [C, C₀, innerSetLimit_prod_const _ isClosed_univ] using prod_mono hh' (Subset.rfl (s := (univ : Set ℝ)))
  have hD := epigraph_subset_epigraph_iff.mpr hG
  rw [epigraph_epiUpperLimit] at hD
  have hCD : CannotBeSeparated (levelConstraintMap A '' C₀) (epigraph G) := by
    rw [CannotBeSeparated, image_levelConstraintMap, cylinder_sub_epigraph, interior_prod_eq, interior_univ]
    exact ⟨hsep.symm, mem_univ _⟩
  have hfeas := linearConstraintSet_subset_innerSetLimit
    (Lseq := fun n ↦ levelConstraintMap (L n)) (L := levelConstraintMap A)
    (fun n ↦ (hh n).prod convex_univ) hg hC hD
    ((continuous_levelConstraintMap.tendsto _).comp hL) hCD
  let T (p : (E × ℝ) × ℝ) := (p.1.1, p.2 + p.1.2)
  have hT : Continuous T := continuous_fst.fst.prodMk (continuous_snd.add continuous_fst.snd)
  apply epigraph_subset_epigraph_iff.mp
  rw [epigraph_epiUpperLimit]
  rintro ⟨x, a⟩ hx
  obtain ⟨s, r, hgs, hhr, hsum⟩ := (infAddition_le_coe_iff _ _ _).mp hx
  have hp : ((x, r), s) ∈ linearConstraintSet C₀ (levelConstraintMap A) (epigraph G) :=
    ⟨⟨hhr, mem_univ _⟩, hgs⟩
  have hpoint : (x, a) ∈ T '' innerSetLimit
      (fun n ↦ linearConstraintSet (C n) (levelConstraintMap (L n)) (epigraph (g n))) :=
    ⟨_, hfeas hp, Prod.ext rfl hsum⟩
  apply innerSetLimit_mono _ (image_innerSetLimit_subset_innerSetLimit_image hT hpoint)
  rintro n _ ⟨⟨⟨y, r'⟩, s'⟩, ⟨⟨hyr, _⟩, hys⟩, rfl⟩
  exact (infAddition_le_coe_iff _ _ _).mpr ⟨s', r', hys, hyr, rfl⟩

/-- **Exercise 7.47**, convergence with no opposite infinities in the
limiting sum. Finite values of either limit, or proper limits, suffice. -/
theorem epiConverges_infAddition_comp_linear
    {g : ℕ → F → EReal} {h : ℕ → E → EReal} {G : F → EReal} {H : E → EReal}
    {L : ℕ → E →L[ℝ] F} {A : E →L[ℝ] F}
    (hg : ∀ n, Convex ℝ (epigraph (g n))) (hh : ∀ n, Convex ℝ (epigraph (h n)))
    (hG : EpiConverges g G) (hH : EpiConverges h H) (hL : Tendsto L atTop (𝓝 A))
    (hsep : CannotBeSeparated (effectiveDomain G) (A '' effectiveDomain H))
    (hadd : ∀ x, infAddition (G (A x)) (H x) = G (A x) + H x) :
    EpiConverges (fun n x ↦ infAddition (g n (L n x)) (h n x))
      (fun x ↦ infAddition (G (A x)) (H x)) := by
  have hup := epiUpperLimit_infAddition_comp_linear_le hg hh (epiConverges_iff_epiLimits_eq.mp hG).2.le
    (epiConverges_iff_epiLimits_eq.mp hH).2.le hL hsep
  apply epiConverges_iff_liminf_limsup.mpr
  intro x
  constructor
  · intro y hy
    have hAy : Tendsto (fun n ↦ L n (y n)) atTop (𝓝 (A x)) :=
      ((ContinuousLinearMap.apply ℝ F).continuous₂.tendsto (x, A)).comp (hy.prodMk_nhds hL)
    rw [hadd x]
    exact (add_le_add ((epiConverges_iff_liminf_limsup.mp hG _).1 _ hAy)
      ((epiConverges_iff_liminf_limsup.mp hH _).1 _ hy)).trans
      (EReal.le_liminf_add.trans (liminf_le_liminf (.of_forall fun n ↦ add_le_infAddition _ _)))
  · obtain ⟨y, hy, hv⟩ := exists_tendsto_limsup_eq_epiUpperLimit
      (fun n x ↦ infAddition (g n (L n x)) (h n x)) x
    exact ⟨y, hy, hv.le.trans (hup x)⟩

/-- **Exercise 7.47(a).** Precomposition by converging linear maps. -/
theorem epiConverges_comp_linear_of_cannotBeSeparated
    {g : ℕ → F → EReal} {G : F → EReal} {L : ℕ → E →L[ℝ] F} {A : E →L[ℝ] F}
    (hg : ∀ n, Convex ℝ (epigraph (g n))) (hG : EpiConverges g G)
    (hL : Tendsto L atTop (𝓝 A)) (hsep : CannotBeSeparated (effectiveDomain G) (range A)) :
    EpiConverges (fun n x ↦ g n (L n x)) (fun x ↦ G (A x)) := by
  have hzero : Convex ℝ (epigraph (fun _ : E ↦ (0 : EReal))) := by
    have heq : epigraph (fun _ : E ↦ (0 : EReal)) = (univ : Set E) ×ˢ Ici (0 : ℝ) := by
      ext ⟨x, a⟩
      simp [mem_epigraph_iff]
    rw [heq]
    exact convex_univ.prod (convex_Ici _)
  have hepi : EpiConverges (fun _ (_ : E) ↦ (0 : EReal)) (fun _ ↦ 0) := by
    apply epiConverges_iff_liminf_limsup.mpr
    intro x
    exact ⟨fun _ _ ↦ (liminf_const _).ge, fun _ ↦ x, tendsto_const_nhds, (limsup_const _).le⟩
  have hdom : effectiveDomain (fun _ : E ↦ (0 : EReal)) = univ := by ext; simp [effectiveDomain]
  simpa only [infAddition_zero] using epiConverges_infAddition_comp_linear hg (fun _ ↦ hzero) hG hepi hL
    (by rwa [hdom, image_univ]) (fun _ ↦ by simp)

/-- **Exercise 7.47(b).** Ordinary sums are the identity-map case. -/
theorem epiConverges_infAddition_of_cannotBeSeparated
    {g h : ℕ → F → EReal} {G H : F → EReal}
    (hg : ∀ n, Convex ℝ (epigraph (g n))) (hh : ∀ n, Convex ℝ (epigraph (h n)))
    (hG : EpiConverges g G) (hH : EpiConverges h H)
    (hsep : CannotBeSeparated (effectiveDomain G) (effectiveDomain H))
    (hadd : ∀ x, infAddition (G x) (H x) = G x + H x) :
    EpiConverges (fun n x ↦ infAddition (g n x) (h n x)) (fun x ↦ infAddition (G x) (H x)) :=
  epiConverges_infAddition_comp_linear (L := fun _ ↦ ContinuousLinearMap.id ℝ F)
    (A := ContinuousLinearMap.id ℝ F) hg hh hG hH tendsto_const_nhds
    (by simpa using hsep) hadd

end RW
