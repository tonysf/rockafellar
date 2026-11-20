/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closed subgradient graphs and maximizing conjugate expressions
-/
import RockafellarWets.Chapter11.SubgradientConjugacy

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Maximizers, excluding an identically negative-infinite maximization problem. -/
def argmax (f : E → EReal) : Set E := {x | f x = ⨆ y, f y ∧ ⊥ < ⨆ y, f y}

theorem ereal_coe_sub_eq_iff_add_eq (r : ℝ) {a b : EReal} (ha : ⊥ < a) (hb : ⊥ < b) :
    (r:EReal)-b = a ↔ a+b = (r:EReal) := by
  cases a <;> cases b <;> simp_all [← EReal.coe_sub,← EReal.coe_add] <;>
    constructor <;> intro h <;> linarith

/-- **Proposition 11.3**, maximizing the dual conjugate expression gives ∂f. -/
theorem subdifferential_eq_argmax_conjugate {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (x : E) :
    subdifferential f x = argmax (fun v ↦ (⟪v,x⟫_ℝ:EReal)-fenchelConjugate f v) := by
  have hpc := isProper_fenchelConjugate hp hl hc
  have he : (⨆ v : E, (⟪v,x⟫_ℝ:EReal)-fenchelConjugate f v) = f x := by
    calc
      _ = fenchelConjugate (fenchelConjugate f) x := by
        apply iSup_congr
        intro v
        rw [real_inner_comm x v]
      _ = _ := congrFun (fenchelConjugate_fenchelConjugate_eq hp hl hc) x
  ext v
  change v ∈ subdifferential f x ↔ _ = (⨆ v : E, _) ∧ _
  rw [he,and_iff_left (hp.2 x),ereal_coe_sub_eq_iff_add_eq _ (hp.2 x) (hpc.2 v)]
  exact mem_subdifferential_iff_fenchel_equality hp hc x v

/-- The symmetric maximizing formula for the conjugate subdifferential. -/
theorem subdifferential_fenchelConjugate_eq_argmax {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (v : E) :
    subdifferential (fenchelConjugate f) v = argmax (fun x ↦ (⟪v,x⟫_ℝ:EReal)-f x) := by
  have he := subdifferential_eq_argmax_conjugate (isProper_fenchelConjugate hp hl hc)
    (lowerSemicontinuous_fenchelConjugate f) (convex_epigraph_fenchelConjugate f) v
  rw [fenchelConjugate_fenchelConjugate_eq hp hl hc] at he
  convert he using 1
  congr 1
  funext x
  rw [real_inner_comm v x]

/-- **Proposition 11.3**, the graph of the subgradient relation is closed. -/
theorem isClosed_graph_subdifferential_of_convex {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    IsClosed (svGraph (subdifferential f)) := by
  have hpc := isProper_fenchelConjugate hp hl hc
  have hsum : LowerSemicontinuous (fun p : E × E ↦ f p.1+fenchelConjugate f p.2) :=
    (hl.comp continuous_fst).add' ((lowerSemicontinuous_fenchelConjugate f).comp continuous_snd)
      (fun p ↦ EReal.continuousAt_add (.inr (hpc.2 p.2).ne') (.inl (hp.2 p.1).ne'))
  have hterm : Continuous (fun p : E × E ↦ ((-⟪p.2,p.1⟫_ℝ:ℝ):EReal)) :=
    continuous_coe_real_ereal.comp (by fun_prop)
  have hgap : LowerSemicontinuous (fun p : E × E ↦ f p.1+fenchelConjugate f p.2-(⟪p.2,p.1⟫_ℝ:EReal)) := by
    simpa only [EReal.coe_neg,sub_eq_add_neg] using hsum.add' hterm.lowerSemicontinuous
      (fun p ↦ EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)))
  have he : svGraph (subdifferential f) =
      {p : E × E | f p.1+fenchelConjugate f p.2-(⟪p.2,p.1⟫_ℝ:EReal) ≤ 0} := by
    ext p
    change p.2 ∈ subdifferential f p.1 ↔ _
    rw [mem_subdifferential_iff_fenchel_equality hp hc]
    simp only [mem_setOf_eq]
    rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _)),zero_add]
    exact ⟨fun h ↦ h.le,fun h ↦ h.antisymm (fenchel_young hp p.1 p.2)⟩
  rw [he]
  exact hgap.isClosed_preimage 0

end
end RW
