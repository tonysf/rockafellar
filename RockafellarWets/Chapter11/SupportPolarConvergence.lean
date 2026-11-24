/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convergence of supports and polar cones
-/

import RockafellarWets.Chapter11.ConjugateEpiClusterLimits
import RockafellarWets.Chapter11.SupportConjugates
import RockafellarWets.Chapter7.EpiLimitProperties

open Bornology Filter Metric Set Topology
open scoped InnerProductSpace
namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem proper_indicator {C : Set E} (hne : C.Nonempty) : IsProper (indicatorVA C) := by
  obtain ⟨c,hc⟩ := hne
  refine ⟨⟨c,by simp [indicatorVA,hc]⟩,fun x ↦ ?_⟩
  by_cases hx : x ∈ C <;> simp [indicatorVA,hx]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Set convergence is epi-convergence of the indicator functions. -/
theorem epiConverges_indicatorVA_iff (C : ℕ → Set E) (D : Set E) :
    EpiConverges (fun n ↦ indicatorVA (C n)) (indicatorVA D) ↔ PKConverges C D := by
  rw [epiConverges_iff_epiLimits_eq]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨((indicatorVA_epiLimit_iff C D).2.mp hb.symm).symm,
      ((indicatorVA_epiLimit_iff C D).1.mp ha.symm).symm⟩
  · intro h
    exact ⟨((indicatorVA_epiLimit_iff C D).1.mpr h.2.symm).symm,
      ((indicatorVA_epiLimit_iff C D).2.mpr h.1.symm).symm⟩

/-- **Corollary 11.35(a)**, convergence of sets and support functions. -/
theorem epiConverges_supportFunction_iff {C : ℕ → Set E} {D : Set E}
    (hn : ∀ n, (C n).Nonempty) (hl : ∀ n, IsClosed (C n))
    (hc : ∀ n, Convex ℝ (C n)) (hD : D.Nonempty) (hDl : IsClosed D)
    (hDc : Convex ℝ D) :
    EpiConverges (fun n ↦ supportFunction (C n)) (supportFunction D) ↔ PKConverges C D := by
  have h := epiConverges_fenchelConjugate_iff
    (fun n ↦ proper_indicator (hn n))
    (fun n ↦ lowerSemicontinuous_indicatorVA (hl n))
    (fun n ↦ by rw [epigraph_indicatorVA]; exact (hc n).prod (convex_Ici 0))
    (proper_indicator hD) (lowerSemicontinuous_indicatorVA hDl)
    (by rw [epigraph_indicatorVA]; exact hDc.prod (convex_Ici 0))
  simpa only [fenchelConjugate_indicatorVA,epiConverges_indicatorVA_iff] using h

omit [FiniteDimensional ℝ E] in
/-- Bounded sets have everywhere finite upper support values. -/
theorem supportFunction_lt_top_of_isBounded {C : Set E} (hb : IsBounded C) (v : E) :
    supportFunction C v < ⊤ := by
  obtain ⟨R,hR⟩ := hb.exists_norm_le
  apply lt_of_le_of_lt ((supportFunction_le_iff _ _ ((R*‖v‖:ℝ):EReal)).mpr ?_)
    (EReal.coe_lt_top _)
  intro x hx
  exact EReal.coe_le_coe_iff.mpr ((real_inner_le_norm x v).trans
    (mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg v)))

/-- The bounded-set clause of **11.35(a)**. In fact boundedness of the limit
set alone suffices; the approximating closed convex sets may be unbounded. -/
theorem pkConverges_iff_tendsto_supportFunction {C : ℕ → Set E} {D : Set E}
    (hn : ∀ n, (C n).Nonempty) (hl : ∀ n, IsClosed (C n))
    (hc : ∀ n, Convex ℝ (C n)) (hD : D.Nonempty) (hDl : IsClosed D)
    (hDc : Convex ℝ D) (hDb : IsBounded D) :
    PKConverges C D ↔
      ∀ v, Tendsto (fun n ↦ supportFunction (C n) v) atTop (𝓝 (supportFunction D v)) := by
  have hd : effectiveDomain (supportFunction D) = univ := by
    ext v
    simp only [mem_effectiveDomain_iff,mem_univ,iff_true]
    exact supportFunction_lt_top_of_isBounded hDb v
  have hcv (n : ℕ) : Convex ℝ (epigraph (supportFunction (C n))) :=
    convex_epigraph_of_sublinear (sublinear_supportFunction (C n))
  rw [← epiConverges_supportFunction_iff hn hl hc hD hDl hDc]
  constructor
  · intro h v
    have hv : v ∉ frontier (effectiveDomain (supportFunction D)) := by rw [hd,frontier_univ]; simp
    exact h.convergesContinuouslyWithinAt_of_notMem_frontier hcv hv univ
      (fun _ ↦ v) (fun _ ↦ mem_univ v) tendsto_const_nhds
  · intro h
    apply epiConverges_of_convex_of_tendsto_on_dense hcv
      (convex_epigraph_of_sublinear (sublinear_supportFunction D))
      (lowerSemicontinuous_supportFunction D)
      (by rw [hd,interior_univ]; exact univ_nonempty) dense_univ
    exact fun v _ ↦ h v

/-- **Corollary 11.35(b)**, convergence of polar cones. -/
theorem pkConverges_polarCone_iff {K : ℕ → Set E} {L : Set E}
    (hk : ∀ n, IsCone (K n)) (hl : ∀ n, IsClosed (K n))
    (hc : ∀ n, Convex ℝ (K n)) (hLk : IsCone L) (hLl : IsClosed L)
    (hLc : Convex ℝ L) :
    PKConverges (fun n ↦ polarCone (K n)) (polarCone L) ↔ PKConverges K L := by
  have h := epiConverges_fenchelConjugate_iff
    (fun n ↦ proper_indicator ⟨0,(hk n).1⟩)
    (fun n ↦ lowerSemicontinuous_indicatorVA (hl n))
    (fun n ↦ by rw [epigraph_indicatorVA]; exact (hc n).prod (convex_Ici 0))
    (proper_indicator ⟨0,hLk.1⟩) (lowerSemicontinuous_indicatorVA hLl)
    (by rw [epigraph_indicatorVA]; exact hLc.prod (convex_Ici 0))
  simpa only [fenchelConjugate_indicatorVA_cone (hk _),fenchelConjugate_indicatorVA_cone hLk,
    epiConverges_indicatorVA_iff] using h

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Indicators reverse inclusion. -/
theorem indicatorVA_le_indicatorVA_iff {C D : Set E} :
    indicatorVA C ≤ indicatorVA D ↔ D ⊆ C := by
  constructor
  · intro h x hx
    by_contra hxC
    have hle := h x
    simp [indicatorVA, hx, hxC] at hle
  · intro h x
    by_cases hx : x ∈ D
    · simp [indicatorVA, hx, h hx]
    · simp [indicatorVA, hx]

/-- **Corollary 11.35(a)**, the one-sided equivalences, under the printed
hypothesis that the distances from the origin have a finite upper limit. -/
theorem supportFunction_epiLimit_inclusions {C : ℕ → Set E} {D : Set E}
    (hn : ∀ n, (C n).Nonempty) (hl : ∀ n, IsClosed (C n))
    (hc : ∀ n, Convex ℝ (C n)) (hD : D.Nonempty) (hDl : IsClosed D)
    (hDc : Convex ℝ D)
    (hd : limsup (fun n ↦ (infDist (0 : E) (C n) : EReal)) atTop < ⊤) :
    (outerSetLimit C ⊆ D ↔
      epiUpperLimit (fun n ↦ supportFunction (C n)) ≤ supportFunction D) ∧
    (D ⊆ innerSetLimit C ↔
      supportFunction D ≤ epiLowerLimit (fun n ↦ supportFunction (C n))) := by
  obtain ⟨R,hR,_⟩ := EReal.exists_between_coe_real hd
  have hev : ∀ᶠ n in atTop, (infDist (0 : E) (C n) : EReal) < R :=
    eventually_lt_of_limsup_lt hR (by isBoundedDefault)
  have hB : IsBounded (closedBall (0 : E) R) := isBounded_closedBall
  have hi : limsup (fun n ↦ infimumOn (indicatorVA (C n)) (closedBall (0 : E) R)) atTop < ⊤ := by
    have hle : ∀ᶠ n in atTop, infimumOn (indicatorVA (C n)) (closedBall (0 : E) R) ≤ 0 := by
      filter_upwards [hev] with n hn'
      obtain ⟨c,hcC,hcd⟩ := (infDist_lt_iff (hn n)).mp (EReal.coe_lt_coe_iff.mp hn')
      have hcB : c ∈ closedBall (0 : E) R := by
        rw [mem_closedBall, dist_comm]; exact hcd.le
      exact (iInf₂_le c hcB).trans (by simp [indicatorVA, hcC])
    exact (limsup_le_of_le (by isBoundedDefault) hle).trans_lt EReal.zero_lt_top
  have hbot : ∀ x, ⊥ < epiLowerLimit (fun n ↦ indicatorVA (C n)) x := by
    rw [(epiLimits_indicatorVA C).1]
    intro x
    by_cases hx : x ∈ outerSetLimit C <;> simp [indicatorVA, hx]
  have h := conjugate_epiLimit_inequalities (f := fun n ↦ indicatorVA (C n))
    (g := indicatorVA D) (fun n ↦ proper_indicator (hn n))
    (fun n ↦ lowerSemicontinuous_indicatorVA (hl n))
    (fun n ↦ by rw [epigraph_indicatorVA]; exact (hc n).prod (convex_Ici 0))
    (proper_indicator hD) (lowerSemicontinuous_indicatorVA hDl)
    (by rw [epigraph_indicatorVA]; exact hDc.prod (convex_Ici 0)) hbot hB hi
  simpa only [fenchelConjugate_indicatorVA, (epiLimits_indicatorVA C).1,
    (epiLimits_indicatorVA C).2, indicatorVA_le_indicatorVA_iff] using h

/-- **Corollary 11.35(b)**, the one-sided inclusions for polar cones. -/
theorem polarCone_setLimit_inclusions {K : ℕ → Set E} {L : Set E}
    (hk : ∀ n, IsCone (K n)) (hl : ∀ n, IsClosed (K n))
    (hc : ∀ n, Convex ℝ (K n)) (hLk : IsCone L) (hLl : IsClosed L)
    (hLc : Convex ℝ L) :
    (outerSetLimit K ⊆ L ↔ polarCone L ⊆ innerSetLimit (fun n ↦ polarCone (K n))) ∧
    (L ⊆ innerSetLimit K ↔ outerSetLimit (fun n ↦ polarCone (K n)) ⊆ polarCone L) := by
  have hd : limsup (fun n ↦ (infDist (0 : E) (K n) : EReal)) atTop < ⊤ := by
    have hz : (fun n ↦ (infDist (0 : E) (K n) : EReal)) = fun _ ↦ 0 :=
      funext fun n ↦ by rw [infDist_zero_of_mem (hk n).1, EReal.coe_zero]
    rw [hz, limsup_const]
    exact EReal.zero_lt_top
  have h := supportFunction_epiLimit_inclusions (fun n ↦ ⟨0,(hk n).1⟩) hl hc ⟨0,hLk.1⟩ hLl hLc hd
  simpa only [supportFunction_cone (hk _), supportFunction_cone hLk,
    (epiLimits_indicatorVA _).1, (epiLimits_indicatorVA _).2,
    indicatorVA_le_indicatorVA_iff] using h

end RW
