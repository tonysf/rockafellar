/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost strict convexity and conjugate differentiability
-/

import RockafellarWets.Chapter11.EssentialDifferentiability
import RockafellarWets.Chapter11.SubgradientConjugacy

open Set Filter Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **11.13(b)**: strict convexity on every convex subset of the domain of
the subgradient mapping. All values on such a subset are finite. -/
def IsAlmostStrictlyConvex (f : E → EReal) : Prop :=
  ∀ C : Set E, Convex ℝ C → (∀ x ∈ C, (subdifferential f x).Nonempty) →
    StrictConvexOn ℝ C (fun x ↦ (f x).toReal)

/-- Convex subdifferentials are convex even at points with an empty fiber. -/
theorem convex_subdifferential_of_convex {f : E → EReal} (hp : IsProper f)
    (hc : Convex ℝ (epigraph f)) (x : E) : Convex ℝ (subdifferential f x) := by
  rcases (subdifferential f x).eq_empty_or_nonempty with he | ⟨v,hv⟩
  · rw [he]; exact convex_empty
  · obtain ⟨c,hx⟩ := (mem_subdifferential_iff_exists_seq.mp hv).1
    rw [subdifferential_eq_regularSubdifferential_of_convex hc hp hx]
    exact (subdifferential_properties hx).2.1

private theorem toReal_eq_of_common_subgradient {f : E → EReal} (hp : IsProper f)
    (hc : Convex ℝ (epigraph f)) {x y v : E}
    (hx : v ∈ subdifferential f x) (hy : v ∈ subdifferential f y) :
    (f y).toReal = (f x).toReal+⟪v,y-x⟫_ℝ := by
  obtain ⟨c,hc'⟩ := (mem_subdifferential_iff_exists_seq.mp hx).1
  obtain ⟨d,hd'⟩ := (mem_subdifferential_iff_exists_seq.mp hy).1
  have hxy := (mem_subdifferential_iff_of_convex hc hp hc').mp hx y
  have hyx := (mem_subdifferential_iff_of_convex hc hp hd').mp hy x
  rw [hd',EReal.coe_le_coe_iff,inner_sub_right] at hxy
  rw [hc',EReal.coe_le_coe_iff,inner_sub_right] at hyx
  rw [hc',hd',EReal.toReal_coe,EReal.toReal_coe,inner_sub_right]
  linarith

/-- The central duality in **11.13**: almost strict convexity is precisely
single-valuedness of the conjugate subgradient mapping. -/
theorem isAlmostStrictlyConvex_iff_conjugate_subdifferential_subsingleton
    {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) :
    IsAlmostStrictlyConvex f ↔ ∀ a, (subdifferential (fenchelConjugate f) a).Subsingleton := by
  constructor
  · intro hs a x hx y hy
    by_contra hxy
    let C := subdifferential (fenchelConjugate f) a
    have hC : Convex ℝ C := convex_subdifferential_of_convex
      (isProper_fenchelConjugate hp hl hc) (convex_epigraph_fenchelConjugate f) a
    have hdom : ∀ z ∈ C, (subdifferential f z).Nonempty := fun z hz ↦
      ⟨a,(mem_subdifferential_fenchelConjugate_iff hp hl hc z a).mp hz⟩
    have hstrict := hs C hC hdom
    let z : E := (1/2:ℝ) • x+(1/2:ℝ) • y
    have hz : z ∈ C := hC hx hy (by norm_num) (by norm_num) (by norm_num)
    have ha : a ∈ subdifferential f x := (mem_subdifferential_fenchelConjugate_iff hp hl hc x a).mp hx
    have hb : a ∈ subdifferential f y := (mem_subdifferential_fenchelConjugate_iff hp hl hc y a).mp hy
    have hd : a ∈ subdifferential f z := (mem_subdifferential_fenchelConjugate_iff hp hl hc z a).mp hz
    have hyval := toReal_eq_of_common_subgradient hp hc ha hb
    have hzval := toReal_eq_of_common_subgradient hp hc ha hd
    have hi : ⟪a,z-x⟫_ℝ=(1/2:ℝ)*⟪a,y-x⟫_ℝ := by
      simp only [z,inner_sub_right,inner_add_right,inner_smul_right]
      ring
    have hlt := hstrict.2 hx hy hxy (show (0:ℝ)<1/2 by norm_num)
      (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)+1/2=1 by norm_num)
    change (f z).toReal < (1/2:ℝ)*(f x).toReal+(1/2:ℝ)*(f y).toReal at hlt
    rw [hi] at hzval
    linarith
  · intro hsingle C hC hdom
    refine ⟨hC,?_⟩
    intro x hx y hy hxy a b ha hb hab
    let z := a • x+b • y
    have hz : z ∈ C := hC hx hy ha.le hb.le hab
    obtain ⟨v,hv⟩ := hdom z hz
    obtain ⟨vx,hvx⟩ := hdom x hx
    obtain ⟨vy,hvy⟩ := hdom y hy
    obtain ⟨cx,hfx⟩ := (mem_subdifferential_iff_exists_seq.mp hvx).1
    obtain ⟨cy,hfy⟩ := (mem_subdifferential_iff_exists_seq.mp hvy).1
    obtain ⟨cz,hfz⟩ := (mem_subdifferential_iff_exists_seq.mp hv).1
    change (f z).toReal < a*(f x).toReal+b*(f y).toReal
    rw [hfx,hfy,hfz,EReal.toReal_coe,EReal.toReal_coe,EReal.toReal_coe]
    by_contra hn
    have hn' : a*cx+b*cy ≤ cz := le_of_not_gt hn
    have hs := (mem_subdifferential_iff_of_convex hc hp hfz).mp hv
    have hxx := hs x
    have hyy := hs y
    rw [hfx,EReal.coe_le_coe_iff,inner_sub_right] at hxx
    rw [hfy,EReal.coe_le_coe_iff,inner_sub_right] at hyy
    have hin : ⟪v,z⟫_ℝ=a*⟪v,x⟫_ℝ+b*⟪v,y⟫_ℝ := by
      simp only [z,inner_add_right,inner_smul_right]
    have hbalance : a*(cx-(cz+⟪v,x⟫_ℝ-⟪v,z⟫_ℝ))+
        b*(cy-(cz+⟪v,y⟫_ℝ-⟪v,z⟫_ℝ)) ≤ 0 := by
      calc
        _ = a*cx+b*cy-((a+b)*cz+(a*⟪v,x⟫_ℝ+b*⟪v,y⟫_ℝ)-(a+b)*⟪v,z⟫_ℝ) := by ring
        _ = a*cx+b*cy-cz := by rw [hab,← hin]; ring
        _ ≤ 0 := sub_nonpos.mpr hn'
    have hex : cx=cz+⟪v,x⟫_ℝ-⟪v,z⟫_ℝ := by
      have hbnon := mul_nonneg hb.le (show 0 ≤ cy-(cz+⟪v,y⟫_ℝ-⟪v,z⟫_ℝ) by linarith)
      have hamul : a*(cx-(cz+⟪v,x⟫_ℝ-⟪v,z⟫_ℝ)) ≤ 0 := by linarith
      have hdiff : cx-(cz+⟪v,x⟫_ℝ-⟪v,z⟫_ℝ) ≤ 0 := by
        by_contra! hn
        exact (not_lt_of_ge hamul) (mul_pos ha hn)
      linarith
    have hey : cy=cz+⟪v,y⟫_ℝ-⟪v,z⟫_ℝ := by
      have hanon := mul_nonneg ha.le (show 0 ≤ cx-(cz+⟪v,x⟫_ℝ-⟪v,z⟫_ℝ) by linarith)
      have hbmul : b*(cy-(cz+⟪v,y⟫_ℝ-⟪v,z⟫_ℝ)) ≤ 0 := by linarith
      have hdiff : cy-(cz+⟪v,y⟫_ℝ-⟪v,z⟫_ℝ) ≤ 0 := by
        by_contra! hn
        exact (not_lt_of_ge hbmul) (mul_pos hb hn)
      linarith
    have hxv : v ∈ subdifferential f x := by
      apply (mem_subdifferential_iff_of_convex hc hp hfx).mpr
      intro q
      have he : cx+⟪v,q-x⟫_ℝ = cz+⟪v,q-z⟫_ℝ := by
        rw [inner_sub_right,inner_sub_right,hex]; ring
      rw [he]
      exact hs q
    have hyv : v ∈ subdifferential f y := by
      apply (mem_subdifferential_iff_of_convex hc hp hfy).mpr
      intro q
      have he : cy+⟪v,q-y⟫_ℝ = cz+⟪v,q-z⟫_ℝ := by
        rw [inner_sub_right,inner_sub_right,hey]; ring
      rw [he]
      exact hs q
    exact hxy (hsingle v ((mem_subdifferential_fenchelConjugate_iff hp hl hc x v).mpr hxv)
      ((mem_subdifferential_fenchelConjugate_iff hp hl hc y v).mpr hyv))

/-- **11.13**, the conjugate is almost differentiable exactly when the primal
function is almost strictly convex. -/
theorem isAlmostDifferentiable_conjugate_iff_isAlmostStrictlyConvex
    {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) :
    IsAlmostDifferentiable (fenchelConjugate f) ↔ IsAlmostStrictlyConvex f := by
  rw [isAlmostDifferentiable_iff_subdifferential_subsingleton
    (isProper_fenchelConjugate hp hl hc) (lowerSemicontinuous_fenchelConjugate f)
    (convex_epigraph_fenchelConjugate f),isAlmostStrictlyConvex_iff_conjugate_subdifferential_subsingleton hp hl hc]

/-- **11.13**, the symmetric primal formulation. -/
theorem isAlmostDifferentiable_iff_conjugate_isAlmostStrictlyConvex
    {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) :
    IsAlmostDifferentiable f ↔ IsAlmostStrictlyConvex (fenchelConjugate f) := by
  have h := isAlmostDifferentiable_conjugate_iff_isAlmostStrictlyConvex
    (isProper_fenchelConjugate hp hl hc) (lowerSemicontinuous_fenchelConjugate f)
    (convex_epigraph_fenchelConjugate f)
  rwa [fenchelConjugate_fenchelConjugate_eq hp hl hc] at h

end RW
