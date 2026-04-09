/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3B: Linear Images of Horizon Cones

This file formalizes Theorem 3.10 from Rockafellar-Wets:
- linear images under a kernel/horizon nondegeneracy condition are closed;
- horizon cones commute with such linear images.
-/

import RockafellarWets.Chapter3.HorizonCones
import Mathlib.Topology.MetricSpace.Sequences

open Set Bornology Filter Topology

namespace RW

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Sequential form of membership in an asymptotic cone: points of the asymptotic
cone are limits of normalized points of the set. -/
theorem exists_seq_pos_smul_of_mem_asymptoticCone [FiniteDimensional ℝ E]
    {C : Set E} {v : E} (hv : v ∈ asymptoticCone ℝ C) :
    ∃ c : ℕ → ℝ, ∃ u : ℕ → E,
      Tendsto c atTop atTop ∧ Tendsto u atTop (𝓝 v) ∧
      (∀ n, 0 < c n) ∧ (∀ n, c n • u n ∈ C) := by
  rw [mem_asymptoticCone_iff, AffineSpace.asymptoticNhds_eq_smul,
    ← map₂_smul, ← map_prod_eq_map₂, frequently_map] at hv
  have hv' :
      ∃ᶠ z : ℝ × E in atTop ×ˢ 𝓝 v, 0 < z.1 ∧ z.1 • z.2 ∈ C := by
    have hpos : ∀ᶠ z : ℝ × E in atTop ×ˢ 𝓝 v, 0 < z.1 := by
      simpa using (tendsto_fst : Tendsto (fun z : ℝ × E => z.1) (atTop ×ˢ 𝓝 v) atTop).eventually
        (eventually_gt_atTop (0 : ℝ))
    exact (hv.and_eventually hpos).mono fun _ hz => ⟨hz.2, hz.1⟩
  rcases frequently_iff_seq_forall.mp hv' with ⟨z, hz_tendsto, hz_mem⟩
  refine ⟨fun n => (z n).1, fun n => (z n).2, ?_, ?_, ?_, ?_⟩
  · exact tendsto_fst.comp hz_tendsto
  · exact tendsto_snd.comp hz_tendsto
  · intro n
    exact (hz_mem n).1
  · intro n
    exact (hz_mem n).2

/-- Converse sequential criterion for asymptotic cones. -/
theorem mem_asymptoticCone_of_seq_smul {C : Set E} {v : E}
    {c : ℕ → ℝ} {u : ℕ → E}
    (hc : Tendsto c atTop atTop) (hu : Tendsto u atTop (𝓝 v))
    (hmem : ∀ n, c n • u n ∈ C) :
    v ∈ asymptoticCone ℝ C := by
  rw [mem_asymptoticCone_iff]
  exact (hc.atTop_smul_nhds_tendsto_asymptoticNhds hu).frequently
    (Frequently.of_forall hmem)

/-- Linear maps send asymptotic directions to asymptotic directions of the image. -/
theorem linearMap_image_asymptoticCone_subset [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] F) {C : Set E} :
    L '' asymptoticCone ℝ C ⊆ asymptoticCone ℝ (L '' C) := by
  intro w hw
  rcases hw with ⟨v, hv, rfl⟩
  rcases exists_seq_pos_smul_of_mem_asymptoticCone (C := C) hv with
    ⟨c, u, hc, hu, hcpos, hmem⟩
  refine mem_asymptoticCone_of_seq_smul
    hc ((L.continuous_of_finiteDimensional.tendsto v).comp hu) ?_
  intro n
  exact ⟨c n • u n, hmem n, by simp⟩

/-- General inclusion in Theorem 3.10: `L(C∞) ⊆ L(C)∞`. -/
theorem linearMap_image_horizonCone_subset [FiniteDimensional ℝ E]
    (L : E →ₗ[ℝ] F) {C : Set E} :
    L '' horizonCone C ⊆ horizonCone (L '' C) := by
  intro w hw
  rcases hw with ⟨v, hv, rfl⟩
  have hv' : v = 0 ∨ v ∈ asymptoticCone ℝ C := by
    simpa [horizonCone] using hv
  rcases hv' with rfl | hv
  · simp [zero_mem_horizonCone]
  · exact Set.mem_insert_of_mem 0 <| linearMap_image_asymptoticCone_subset L ⟨_, hv, rfl⟩

/-- Auxiliary lemma: if a sequence consists of bounded positive scalings of points in `C`,
its horizon directions already belong to `horizonCone C`. -/
theorem horizonCone_range_smul_subset {C : Set E} {a : ℕ → ℝ} {x : ℕ → E}
    [FiniteDimensional ℝ E]
    (hx : ∀ n, x n ∈ C) (ha_pos : ∀ n, 0 < a n)
    (ha_bdd : IsBounded (Set.range a)) :
    horizonCone (Set.range fun n => a n • x n) ⊆ horizonCone C := by
  intro v hv
  have hv' : v = 0 ∨ v ∈ asymptoticCone ℝ (Set.range fun n => a n • x n) := by
    simpa [horizonCone] using hv
  rcases hv' with rfl | hv
  · exact zero_mem_horizonCone C
  · rcases exists_seq_pos_smul_of_mem_asymptoticCone (C := Set.range fun n => a n • x n) hv with
      ⟨c, u, hc, hu, hcpos, hcu⟩
    choose m hm using hcu
    obtain ⟨M, hM⟩ := ha_bdd.exists_norm_le
    let R : ℝ := max M 1
    have hRpos : 0 < R := by
      dsimp [R]
      positivity
    have ha_le : ∀ n, a (m n) ≤ R := by
      intro n
      have hnorm : ‖a (m n)‖ ≤ M := hM _ ⟨m n, rfl⟩
      have hnonneg : 0 ≤ a (m n) := (ha_pos _).le
      exact le_trans (by simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hnorm)
        (le_max_left _ _)
    have hdivR : Tendsto (fun n => c n / R) atTop atTop := by
      simpa [div_eq_mul_inv, mul_comm] using hc.atTop_mul_const (inv_pos.mpr hRpos)
    have hdiv :
        Tendsto (fun n => c n / a (m n)) atTop atTop := by
      have hc_nonneg : ∀ᶠ n in atTop, 0 ≤ c n := hc.eventually (eventually_ge_atTop (0 : ℝ))
      refine tendsto_atTop_mono' atTop ?_ hdivR
      filter_upwards [hc_nonneg] with n hcn
      have hapos : 0 < a (m n) := ha_pos _
      have hle : a (m n) ≤ R := ha_le n
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hinv : R⁻¹ ≤ (a (m n))⁻¹ := by
        exact (inv_le_inv₀ hRpos hapos).2 hle
      nlinarith [hcn, hinv]
    have hmem :
        ∀ n, (c n / a (m n)) • u n ∈ C := by
      intro n
      have hEq := hm n
      have hScaled := congrArg ((a (m n))⁻¹ • ·) hEq
      have hEq' : (c n / a (m n)) • u n = x (m n) := by
        simpa [smul_smul, div_eq_mul_inv, inv_mul_cancel₀ (ha_pos _).ne', one_smul, mul_comm] using
          hScaled.symm
      simpa [hEq'] using hx (m n)
    exact Set.mem_insert_of_mem 0 <| mem_asymptoticCone_of_seq_smul hdiv hu hmem

/-- If bounded positive rescalings of points in `C` have bounded image under `L`,
then the rescaled points themselves are bounded, provided the kernel of `L`
meets `horizonCone C` only at `0`. -/
theorem isBounded_range_smul_of_image_bounded [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : Set E} {L : E →ₗ[ℝ] F} {a : ℕ → ℝ} {x : ℕ → E}
    (hx : ∀ n, x n ∈ C) (ha_pos : ∀ n, 0 < a n)
    (ha_bdd : IsBounded (Set.range a))
    (hker : ∀ ⦃v : E⦄, v ∈ horizonCone C → L v = 0 → v = 0)
    (hLbdd : IsBounded (Set.range fun n => a n • L (x n))) :
    IsBounded (Set.range fun n => a n • x n) := by
  by_contra hbad
  rcases (not_bounded_iff_exists_ne_zero_mem_asymptoticCone
    (s := Set.range fun n => a n • x n)).mp hbad with ⟨v, hv0, hv⟩
  have hvC : v ∈ horizonCone C :=
    horizonCone_range_smul_subset hx ha_pos ha_bdd (Set.mem_insert_of_mem 0 hv)
  have hLv_mem : L v ∈ horizonCone (Set.range fun n => a n • L (x n)) := by
    have hEq :
        L '' Set.range (fun n => a n • x n) = Set.range (fun n => a n • L (x n)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, by simp⟩
      · rintro ⟨n, rfl⟩
        exact ⟨a n • x n, ⟨n, rfl⟩, by simp⟩
    have : L v ∈ horizonCone (L '' Set.range fun n => a n • x n) :=
      linearMap_image_horizonCone_subset L ⟨v, Set.mem_insert_of_mem 0 hv, rfl⟩
    simpa [hEq] using this
  have hLv0 : L v = 0 := by
    have hzero :
        horizonCone (Set.range fun n => a n • L (x n)) = ({0} : Set F) :=
      (isBounded_iff_horizonCone_eq_singleton_zero (C := Set.range fun n => a n • L (x n))).mp hLbdd
    simpa [hzero] using hLv_mem
  exact hv0 (hker hvC hLv0)

/-- **Theorem 3.10**: under the kernel/horizon nondegeneracy hypothesis, the
linear image of a closed set is closed. -/
theorem isClosed_linearImage_of_horizonCone_ker_trivial
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {L : E →ₗ[ℝ] F} {C : Set E} (hC : IsClosed C)
    (hker : ∀ ⦃v : E⦄, v ∈ horizonCone C → L v = 0 → v = 0) :
    IsClosed (L '' C) := by
  rw [isClosed_iff_frequently]
  intro u hu
  have hu_cl : u ∈ closure (L '' C) := mem_closure_iff_frequently.mpr hu
  rw [mem_closure_iff_seq_limit] at hu_cl
  rcases hu_cl with ⟨uSeq, hu_mem, hu_tendsto⟩
  choose xSeq hxSeq_mem hxSeq_eq using fun n => hu_mem n
  have hxbd : IsBounded (Set.range xSeq) := by
    have hLbdd : IsBounded (Set.range uSeq) := Metric.isBounded_range_of_tendsto _ hu_tendsto
    have hEqL : Set.range (fun n => L (xSeq n)) = Set.range uSeq := by
      ext y
      constructor
      · rintro ⟨n, rfl⟩
        simp [hxSeq_eq n]
      · rintro ⟨n, rfl⟩
        exact ⟨n, by simp [hxSeq_eq n]⟩
    have hLbdd' : IsBounded (Set.range fun n => L (xSeq n)) := by
      simpa [hEqL] using hLbdd
    simpa [one_smul] using
      isBounded_range_smul_of_image_bounded
        (C := C) (L := L) (a := fun _ => (1 : ℝ)) (x := xSeq)
        hxSeq_mem (fun _ => by norm_num)
        (by simp [Set.range_const])
        hker (by simpa [one_smul] using hLbdd')
  rcases tendsto_subseq_of_bounded hxbd (fun n => Set.mem_range_self n) with
    ⟨x, -, φ, hφ, hφ_tendsto⟩
  have hxC : x ∈ C := hC.mem_of_tendsto hφ_tendsto (Eventually.of_forall fun n => hxSeq_mem (φ n))
  have hLx :
      Tendsto (fun n => L (xSeq (φ n))) atTop (𝓝 (L x)) :=
    (L.continuous_of_finiteDimensional.tendsto x).comp hφ_tendsto
  have hu_sub :
      Tendsto (fun n => L (xSeq (φ n))) atTop (𝓝 u) := by
    have : Tendsto (fun n => uSeq (φ n)) atTop (𝓝 u) :=
      hu_tendsto.comp hφ.tendsto_atTop
    simpa [hxSeq_eq] using this
  have hEq : L x = u := tendsto_nhds_unique hLx hu_sub
  exact ⟨x, hxC, hEq⟩

/-- **Theorem 3.10**: under the kernel/horizon nondegeneracy hypothesis, one
has `L(C∞) = L(C)∞`. -/
theorem linearImage_horizonCone_eq [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {L : E →ₗ[ℝ] F} {C : Set E}
    (hker : ∀ ⦃v : E⦄, v ∈ horizonCone C → L v = 0 → v = 0) :
    L '' horizonCone C = horizonCone (L '' C) := by
  refine le_antisymm (linearMap_image_horizonCone_subset L) ?_
  intro w hw
  have hw' : w = 0 ∨ w ∈ asymptoticCone ℝ (L '' C) := by
    simpa [horizonCone] using hw
  rcases hw' with rfl | hw
  · exact ⟨0, zero_mem_horizonCone C, by simp⟩
  · rcases exists_seq_pos_smul_of_mem_asymptoticCone (C := L '' C) hw with
      ⟨c, u, hc, hu, hcpos, hcu⟩
    choose x hxC hxEq using fun n => hcu n
    let y : ℕ → E := fun n => (c n)⁻¹ • x n
    have hybdd : IsBounded (Set.range y) := by
      have ha_bdd : IsBounded (Set.range fun n => (c n)⁻¹) :=
        Metric.isBounded_range_of_tendsto _ hc.inv_tendsto_atTop
      have hLu_bdd : IsBounded (Set.range u) := Metric.isBounded_range_of_tendsto _ hu
      have hEqRange :
          Set.range (fun n => (c n)⁻¹ • L (x n)) = Set.range u := by
        ext z
        constructor
        · rintro ⟨n, rfl⟩
          refine ⟨n, ?_⟩
          have hScaled := congrArg ((c n)⁻¹ • ·) (hxEq n)
          simpa [smul_smul, inv_mul_cancel₀ (hcpos _).ne', one_smul, div_eq_mul_inv] using
            hScaled.symm
        · rintro ⟨n, rfl⟩
          refine ⟨n, ?_⟩
          have hScaled := congrArg ((c n)⁻¹ • ·) (hxEq n)
          simpa [smul_smul, inv_mul_cancel₀ (hcpos _).ne', one_smul, div_eq_mul_inv] using hScaled
      simpa [y, hEqRange] using
        isBounded_range_smul_of_image_bounded
          (C := C) (L := L) (a := fun n => (c n)⁻¹) (x := x)
          hxC (fun n => inv_pos.mpr (hcpos n)) ha_bdd hker (by simpa [hEqRange] using hLu_bdd)
    rcases tendsto_subseq_of_bounded hybdd (fun n => Set.mem_range_self n) with
      ⟨v, -, φ, hφ, hφ_tendsto⟩
    have hv_hc : v ∈ horizonCone C := by
      have hy_sub : Tendsto (fun n => y (φ n)) atTop (𝓝 v) := by
        simpa using hφ_tendsto
      have hmem : ∀ n, (c (φ n)) • y (φ n) ∈ C := by
        intro n
        have hEq : (c (φ n)) • y (φ n) = x (φ n) := by
          dsimp [y]
          rw [smul_smul, mul_inv_cancel₀ (hcpos _).ne', one_smul]
        exact hEq ▸ hxC (φ n)
      have hc_sub : Tendsto (fun n => c (φ n)) atTop atTop := hc.comp hφ.tendsto_atTop
      exact Set.mem_insert_of_mem 0 <| mem_asymptoticCone_of_seq_smul hc_sub hy_sub hmem
    have hLv : L v = w := by
      have hy_sub : Tendsto (fun n => y (φ n)) atTop (𝓝 v) := by
        simpa using hφ_tendsto
      have hL_tendsto :
          Tendsto (fun n => L (y (φ n))) atTop (𝓝 (L v)) :=
        (L.continuous_of_finiteDimensional.tendsto v).comp hy_sub
      have hu_sub :
          Tendsto (fun n => L (y (φ n))) atTop (𝓝 w) := by
        have hEqSub : (fun n => L (y (φ n))) = fun n => u (φ n) := by
          funext n
          dsimp [y]
          have hScaled := congrArg ((c (φ n))⁻¹ • ·) (hxEq (φ n))
          simpa [smul_smul, inv_mul_cancel₀ (hcpos _).ne', one_smul, div_eq_mul_inv] using hScaled
        simpa [hEqSub] using hu.comp hφ.tendsto_atTop
      exact tendsto_nhds_unique hL_tendsto hu_sub
    exact ⟨v, hv_hc, hLv⟩

end RW
