/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Epi-convergence of maxima of convex functions
-/

import RockafellarWets.Chapter7.EpiLimits
import RockafellarWets.Chapter3.Pointwise
import RockafellarWets.Chapter4.ConvexSystemConvergence

open Set Topology
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Epigraph differences fill the entire vertical line over each point of
the domain difference. -/
theorem sub_epigraph_eq_domain_prod (f g : E → EReal) :
    epigraph f - epigraph g = (effectiveDomain f - effectiveDomain g) ×ˢ (univ : Set ℝ) := by
  ext ⟨x, a⟩
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    exact ⟨⟨p.1, hp.trans_lt (EReal.coe_lt_top _), q.1, hq.trans_lt (EReal.coe_lt_top _),
      congrArg Prod.fst hpq⟩, mem_univ _⟩
  · rintro ⟨⟨y, hy, z, hz, rfl⟩, _⟩
    obtain ⟨r, hfr, _⟩ := EReal.exists_between_coe_real (show f y < ⊤ from hy)
    obtain ⟨s, hgs, _⟩ := EReal.exists_between_coe_real (show g z < ⊤ from hz)
    let b := max s (r - a)
    have hr : r ≤ a + b := by dsimp [b]; linarith [le_max_right s (r - a)]
    refine ⟨(y, a + b), hfr.le.trans (EReal.coe_le_coe_iff.mpr hr),
      (z, b), hgs.le.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)), ?_⟩
    simp

omit [NormedSpace ℝ E] in
theorem cannotBeSeparated_epigraph_iff {f g : E → EReal} :
    CannotBeSeparated (epigraph f) (epigraph g) ↔
      CannotBeSeparated (effectiveDomain f) (effectiveDomain g) := by
  simp [CannotBeSeparated, sub_epigraph_eq_domain_prod, interior_prod_eq]

variable [FiniteDimensional ℝ E]

/-- **Proposition 7.48.** The domain qualification transfers the upper
epi-limit estimate to the maximum. -/
theorem epiUpperLimit_sup_le_of_cannotBeSeparated
    {f h : ℕ → E → EReal} {g k : E → EReal}
    (hf : ∀ n, Convex ℝ (epigraph (f n))) (hh : ∀ n, Convex ℝ (epigraph (h n)))
    (hfg : epiUpperLimit f ≤ g) (hhk : epiUpperLimit h ≤ k)
    (hd : CannotBeSeparated (effectiveDomain g) (effectiveDomain k)) :
    epiUpperLimit (fun n x ↦ f n x ⊔ h n x) ≤ fun x ↦ g x ⊔ k x := by
  have hsubf := epigraph_subset_epigraph_iff.mpr hfg
  have hsubh := epigraph_subset_epigraph_iff.mpr hhk
  rw [epigraph_epiUpperLimit] at hsubf hsubh
  have hsep : CannotBeSeparated (innerSetLimit (fun n ↦ epigraph (f n)))
      (innerSetLimit (fun n ↦ epigraph (h n))) :=
    interior_mono (Set.sub_subset_sub hsubf hsubh) (cannotBeSeparated_epigraph_iff.mpr hd)
  apply epigraph_subset_epigraph_iff.mp
  simp only [epigraph_epiUpperLimit, epigraph_sup]
  exact (inter_subset_inter hsubf hsubh).trans (inter_innerSetLimit_subset_of_cannotBeSeparated hf hh hsep)

/-- **Proposition 7.48**, epi-convergence form. -/
theorem epiConverges_sup_of_cannotBeSeparated {f h : ℕ → E → EReal} {g k : E → EReal}
    (hf : ∀ n, Convex ℝ (epigraph (f n))) (hh : ∀ n, Convex ℝ (epigraph (h n)))
    (hfg : EpiConverges f g) (hhk : EpiConverges h k)
    (hd : CannotBeSeparated (effectiveDomain g) (effectiveDomain k)) :
    EpiConverges (fun n x ↦ f n x ⊔ h n x) (fun x ↦ g x ⊔ k x) := by
  unfold EpiConverges
  simpa only [epigraph_sup] using PKConverges.inter_of_cannotBeSeparated hfg hhk hf hh
    (cannotBeSeparated_epigraph_iff.mpr hd)

end RW
