/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subgradient inversion under conjugacy
-/
import RockafellarWets.Chapter11.FenchelMoreau
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter10.SeparableSubgradients

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem fenchel_young {f : E → EReal} (hp : IsProper f) (x v : E) :
    (⟪v,x⟫_ℝ:EReal) ≤ f x+fenchelConjugate f v := by
  obtain ⟨y,hy⟩ := hp.1
  have hy' : f y = ((f y).toReal:EReal) := (EReal.coe_toReal hy.ne (hp.2 y).ne').symm
  have hb := bot_lt_fenchelConjugate_of_finite hy' v
  have hh := (EReal.sub_le_iff_le_add (.inl (hp.2 x).ne') (.inr hb.ne')).mp
    (le_fenchelConjugate f x v)
  simpa only [add_comm] using hh

theorem mem_subdifferential_iff_fenchelConjugate_eq {f : E → EReal}
    (hp : IsProper f) (hc : Convex ℝ (epigraph f)) {x v : E} {a : ℝ} (hx : f x = a) :
    v ∈ subdifferential f x ↔ fenchelConjugate f v = ((⟪v,x⟫_ℝ-a:ℝ):EReal) := by
  rw [mem_subdifferential_iff_of_convex hc hp hx]
  constructor
  · intro hv
    apply le_antisymm
    · apply (fenchelConjugate_le_coe_iff _ _ _).mpr
      intro y
      have he : ⟪v,y⟫_ℝ-(⟪v,x⟫_ℝ-a) = a+⟪v,y-x⟫_ℝ := by rw [inner_sub_right]; ring
      rw [he]
      exact hv y
    · simpa only [hx,EReal.coe_sub] using le_fenchelConjugate f x v
  · intro he y
    have hh := (fenchelConjugate_le_coe_iff _ _ _).mp he.le y
    have he' : a+⟪v,y-x⟫_ℝ = ⟪v,y⟫_ℝ-(⟪v,x⟫_ℝ-a) := by rw [inner_sub_right]; ring
    rw [he']
    exact hh

/-- Equality in Fenchel's inequality characterizes convex subgradients. -/
theorem mem_subdifferential_iff_fenchel_equality {f : E → EReal}
    (hp : IsProper f) (hc : Convex ℝ (epigraph f)) (x v : E) :
    v ∈ subdifferential f x ↔ f x+fenchelConjugate f v = (⟪v,x⟫_ℝ:EReal) := by
  constructor
  · intro hv
    obtain ⟨a,hx⟩ := hv.1
    rw [hx,(mem_subdifferential_iff_fenchelConjugate_eq hp hc hx).mp hv,← EReal.coe_add]
    congr 1
    ring
  · intro he
    obtain ⟨a,b,hx,hv⟩ := exists_coe_components_of_add_eq_coe he
    apply (mem_subdifferential_iff_fenchelConjugate_eq hp hc hx).mpr
    rw [hx,hv,← EReal.coe_add] at he
    rw [hv]
    apply congrArg (fun r : ℝ ↦ (r:EReal))
    have he' := EReal.coe_injective he
    linarith

/-- **Proposition 11.3**, subgradient inversion for proper closed convex functions. -/
theorem mem_subdifferential_fenchelConjugate_iff {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (x v : E) :
    x ∈ subdifferential (fenchelConjugate f) v ↔ v ∈ subdifferential f x := by
  rw [mem_subdifferential_iff_fenchel_equality (isProper_fenchelConjugate hp hl hc)
      (convex_epigraph_fenchelConjugate f),fenchelConjugate_fenchelConjugate_eq hp hl hc,
    mem_subdifferential_iff_fenchel_equality hp hc]
  rw [add_comm,real_inner_comm v x]

/-- Both subgradient maps are inverse set-valued relations. -/
theorem subdifferential_fenchelConjugate_eq_inverse {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    subdifferential (fenchelConjugate f) = svInv (subdifferential f) ∧
      subdifferential f = svInv (subdifferential (fenchelConjugate f)) := by
  constructor
  · funext v
    exact Set.ext (fun x ↦ mem_subdifferential_fenchelConjugate_iff hp hl hc x v)
  · funext x
    exact Set.ext (fun v ↦ (mem_subdifferential_fenchelConjugate_iff hp hl hc x v).symm)

end
end RW
