/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform descent near a nonstationary Clarke subgradient
-/

import RockafellarWets.Chapter10.LevelSetNormals
import RockafellarWets.Chapter9.LipschitzSubderivatives
import RockafellarWets.Chapter9.EpiLipschitzSets
import RockafellarWets.Chapter9.MollifierSubgradients
import RockafellarWets.Chapter2.Separation

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}

/-- Strict separation of a compact set from zero supplies a uniform negative
inner-product bound. -/
theorem exists_uniform_negative_inner {C : Set E} (hne : C.Nonempty)
    (hc : IsCompact C) (hz : (0:E) ∉ convexHull ℝ C) :
    ∃ w : E, w ≠ 0 ∧ ∃ a : ℝ, a < 0 ∧ ∀ v ∈ C, ⟪v,w⟫_ℝ < a := by
  obtain ⟨φ,a,b,hab,ha,hb⟩ := strict_separation_of_convex_compact
    (convex_convexHull ℝ C) (hne.mono (subset_convexHull ℝ C))
    (isCompact_convexHull hc) (convex_singleton (0:E)) (singleton_nonempty 0)
    isClosed_singleton (by simpa using hz)
  let w := (InnerProductSpace.toDual ℝ E).symm φ
  have he (v : E) : ⟪v,w⟫_ℝ = φ v := by rw [real_inner_comm]; simp [w]
  have ha0 : a < 0 := hab.trans (by simpa using hb 0 rfl)
  have hw : w ≠ 0 := by
    intro hw
    obtain ⟨v,hv⟩ := hne
    have := (ha v (subset_convexHull ℝ C hv)).trans ha0
    rw [← he v,hw,inner_zero_right] at this
    exact (lt_irrefl 0) this
  exact ⟨w,hw,a,ha0,fun v hv ↦ by rw [he]; exact ha v (subset_convexHull ℝ C hv)⟩

/-- A strict negative functional on all nonzero elements proves pointedness. -/
theorem isPointed_of_inner_neg {K : Set E} {w : E}
    (h : ∀ v ∈ K, v ≠ 0 → ⟪v,w⟫_ℝ < 0) : IsPointed K := by
  intro n z hz hsum i
  have hn (j : Fin n) : ⟪z j,w⟫_ℝ ≤ 0 := by
    by_cases hj : z j = 0
    · simp [hj]
    · exact (h (z j) (hz j) hj).le
  have hs : ∑ j : Fin n, ⟪z j,w⟫_ℝ = 0 := by rw [← sum_inner,hsum,inner_zero_left]
  have hi : ⟪z i,w⟫_ℝ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun j _ ↦ hn j)).mp hs i (Finset.mem_univ i)
  by_contra hne
  exact (h (z i) (hz i) hne).ne hi

theorem isPointed_positiveHull_of_inner_neg {C : Set E} {w : E}
    (h : ∀ v ∈ C, ⟪v,w⟫_ℝ < 0) : IsPointed (positiveHull C) := by
  apply isPointed_of_inner_neg (w := w)
  rintro v (rfl | ⟨a,ha,z,hz,rfl⟩) hv
  · exact (hv rfl).elim
  · rw [real_inner_smul_left]
    exact mul_neg_of_pos_of_neg ha (h z hz)

/-- The uniform forward estimate underlying formula 10(1). -/
theorem StrictlyContinuousAt.exists_uniform_descent (hf : StrictlyContinuousAt f x)
    (hz : (0:E) ∉ convexHull ℝ (subdifferential (fun y ↦ (f y:EReal)) x)) :
    ∃ w : E, w ≠ 0 ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ U ∈ 𝓝 x, ∃ δ > 0,
      ∀ y ∈ U, ∀ t ∈ Ioo (0:ℝ) δ, f (y+t • w) ≤ f y-lam*t := by
  have he : ERealStrictlyContinuousAt (fun y ↦ (f y:EReal)) x :=
    ⟨by simp,by simpa only [EReal.toReal_coe] using hf⟩
  obtain ⟨hne,hc⟩ := he.subdifferential_nonempty_compact
  obtain ⟨w,hw,a,ha,hbound⟩ := exists_uniform_negative_inner hne hc hz
  have hs : regularSubderivative (fun y ↦ (f y:EReal)) x w ≤ (a:EReal) := by
    rw [he.regularSubderivative_eq_supportFunction]
    exact (supportFunction_le_iff _ _ _).mpr (fun v hv ↦ EReal.coe_le_coe_iff.mpr (hbound v hv).le)
  have hlt : regularSubderivative (fun y ↦ (f y:EReal)) x w < ((a/2:ℝ):EReal) :=
    hs.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  rw [he.regularSubderivative_eq_limsup_differenceQuotient] at hlt
  obtain ⟨U,hU,T,hT,hUT⟩ := mem_prod_iff.mp (eventually_lt_of_limsup_lt hlt)
  obtain ⟨δ,hδ,hδT⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hT
  refine ⟨w,hw,-a/2,by linarith,U,hU,δ,hδ,?_⟩
  intro y hy t ht
  have hq := hUT (a := (y,t)) ⟨hy,hδT ht⟩
  change differenceQuotient (fun z ↦ (f z:EReal)) y t w < ((a/2:ℝ):EReal) at hq
  rw [differenceQuotient_eq_coe (f := fun z ↦ (f z:EReal)) rfl rfl,
    EReal.coe_lt_coe_iff,inv_mul_lt_iff₀ ht.1] at hq
  linarith

/-- **Example 10.4**, the two uniform estimates in formula 10(1). -/
theorem StrictlyContinuousAt.exists_uniform_two_sided_descent (hf : StrictlyContinuousAt f x)
    (hz : (0:E) ∉ convexHull ℝ (subdifferential (fun y ↦ (f y:EReal)) x)) :
    ∃ w : E, w ≠ 0 ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ V ∈ 𝓝 x, ∃ δ > 0,
      ∀ y ∈ V, ∀ t ∈ Ioo (0:ℝ) δ,
        f (y+t • w) ≤ f y-lam*t ∧ f y+lam*t ≤ f (y-t • w) := by
  obtain ⟨w,hw,lam,hl,U,hU,d,hd,hstep⟩ := hf.exists_uniform_descent hz
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  let δ := min d (r/(2*(‖w‖+1)))
  have hδ : 0 < δ := lt_min hd (div_pos hr (by positivity))
  refine ⟨w,hw,lam,hl,ball x (r/2),ball_mem_nhds x (half_pos hr),δ,hδ,?_⟩
  intro y hy t ht
  have htd : t < d := ht.2.trans_le (min_le_left _ _)
  have htn : t*‖w‖ < r/2 := by
    have hb := (lt_div_iff₀ (show 0 < 2*(‖w‖+1) by positivity)).mp
      (ht.2.trans_le (min_le_right _ _))
    nlinarith [ht.1]
  have hym : y-t • w ∈ ball x r := by
    have hdv : dist (y-t • w) y = t*‖w‖ := by
      rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
    exact (dist_triangle (y-t • w) y x).trans_lt (by
      rw [hdv]
      have hy' : dist y x < r/2 := hy
      linarith)
  have hyU : y ∈ U := hrU ((show dist y x < r/2 from hy).trans (half_lt_self hr))
  have hb := hstep (y-t • w) (hrU hym) t ⟨ht.1,htd⟩
  rw [sub_add_cancel] at hb
  exact ⟨hstep y hyU t ⟨ht.1,htd⟩,by linarith⟩

end RW
