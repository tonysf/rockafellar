/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost differentiability and single-valued convex subgradients

The characterization used in Theorem 11.13.
-/

import RockafellarWets.Chapter11.DualMinimization
import RockafellarWets.Chapter9.ConvexLipschitzBounds
import RockafellarWets.Chapter8.SubgradientExistence

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The book's almost differentiability condition: differentiability on the
nonempty interior of the domain and no subgradients on its boundary. -/
def IsAlmostDifferentiable (f : E → EReal) : Prop :=
  (interior (effectiveDomain f)).Nonempty ∧
    (∀ x ∈ interior (effectiveDomain f), DifferentiableAt ℝ (fun y ↦ (f y).toReal) x) ∧
    ∀ x ∈ effectiveDomain f \ interior (effectiveDomain f), subdifferential f x = ∅

/-- Strict differentiability includes local finiteness, hence an interior
domain point. -/
theorem HasStrictGradientAt.mem_interior_effectiveDomain {f : E → EReal} {v x : E}
    (h : HasStrictGradientAt f v x) : x ∈ interior (effectiveDomain f) := by
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [h.1] with y hy
  change f y < ⊤
  rw [hy]
  exact EReal.coe_lt_top _

private theorem convex_locallyLsc_of_finite {f : E → EReal} (hl : LowerSemicontinuous f)
    {x : E} {c : ℝ} (hx : f x = c) : IsLocallyLscAt f x :=
  isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ (hl.lowerSemicontinuousOn univ)
    (mem_univ x) (hx ▸ EReal.coe_ne_bot _) (hx ▸ EReal.coe_ne_top _)

/-- **11.13**, almost differentiability is exactly the single-valuedness of
the subgradient mapping relative to its domain. -/
theorem isAlmostDifferentiable_iff_subdifferential_subsingleton {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    IsAlmostDifferentiable f ↔ ∀ x, (subdifferential f x).Subsingleton := by
  constructor
  · rintro ⟨_,hd,hbd⟩ x
    by_cases hi : x ∈ interior (effectiveDomain f)
    · have hx : f x = ((f x).toReal:EReal) :=
        (EReal.coe_toReal (interior_subset hi).ne (hp.2 x).ne').symm
      have hfin : ∀ᶠ y in 𝓝 x, f y = ((f y).toReal:EReal) := by
        filter_upwards [mem_interior_iff_mem_nhds.mp hi] with y hy
        exact (EReal.coe_toReal hy.ne (hp.2 y).ne').symm
      have hr := (isSubdifferentiallyRegularAt_of_convex hc (convex_locallyLsc_of_finite hl hx)).1
      have hs := hr.hasStrictGradientAt_of_differentiableAt hfin (hd x hi)
      rw [hs.subdifferential_eq]
      exact subsingleton_singleton
    · intro u hu v hv
      obtain ⟨c,hx⟩ := (mem_subdifferential_iff_exists_seq.mp hu).1
      have hdom : x ∈ effectiveDomain f := hx.trans_lt (EReal.coe_lt_top _)
      rw [hbd x ⟨hdom,hi⟩] at hu
      exact False.elim hu
  · intro hsingle
    have hstrict : ∀ x, (subdifferential f x).Nonempty →
        ∃ v, HasStrictGradientAt f v x := by
      intro x hx
      obtain ⟨v,hv⟩ := hx
      exact ⟨v,(subdifferential_eq_singleton_iff_hasStrictGradientAt_of_convex hp hl hc).mp
        ((hsingle x).eq_singleton_of_mem hv)⟩
    have hne : ∃ x, (subdifferential f x).Nonempty := by
      obtain ⟨x,hxt⟩ := hp.1
      have hx : f x = ((f x).toReal:EReal) := (EReal.coe_toReal hxt.ne (hp.2 x).ne').symm
      obtain ⟨ys,_,hs⟩ := exists_attentive_seq_regularSubdifferential_nonempty
        (convex_locallyLsc_of_finite hl hx) hx
      exact ⟨ys 0,(hs 0).2⟩
    refine ⟨?_,?_,?_⟩
    · obtain ⟨x,hx⟩ := hne
      obtain ⟨v,hv⟩ := hstrict x hx
      exact ⟨x,hv.mem_interior_effectiveDomain⟩
    · intro x hx
      obtain ⟨v,hv⟩ := hstrict x (subdifferential_nonempty_of_convex_interior hc hp hx)
      exact hv.2.hasFDerivAt.differentiableAt
    · rintro x ⟨hx,hnot⟩
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨z,hz⟩ := hstrict x ⟨v,hv⟩
      exact hnot hz.mem_interior_effectiveDomain

end RW
