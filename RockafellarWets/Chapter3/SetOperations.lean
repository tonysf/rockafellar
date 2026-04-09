/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3B: Products and Sums of Sets

This file formalizes the set-operation layer from Chapter 3 of
Rockafellar & Wets, "Variational Analysis":
- Exercise 3.11: products of sets
- Exercise 3.12: sums of sets
-/

import RockafellarWets.Chapter3.LinearImages

open scoped Pointwise
open Set Bornology Filter Topology

namespace RW

section Products

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Exercise 3.11** (general inclusion, binary version): the horizon cone of
the product of two sets is contained in the product of their horizon cones. -/
theorem horizonCone_prod_subset
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : Set E} {D : Set F} :
    horizonCone (C ×ˢ D) ⊆ horizonCone C ×ˢ horizonCone D := by
  intro w hw
  have hw' : w = 0 ∨ w ∈ asymptoticCone ℝ (C ×ˢ D) := by
    simpa [horizonCone] using hw
  rcases hw' with rfl | hw
  · exact ⟨zero_mem_horizonCone C, zero_mem_horizonCone D⟩
  · rcases exists_seq_pos_smul_of_mem_asymptoticCone (C := C ×ˢ D) hw with
      ⟨c, u, hc, hu, hcpos, hmem⟩
    have hufst : Tendsto (fun n => (u n).1) atTop (𝓝 w.1) := by
      exact (continuous_fst.continuousAt.tendsto).comp hu
    have husnd : Tendsto (fun n => (u n).2) atTop (𝓝 w.2) := by
      exact (continuous_snd.continuousAt.tendsto).comp hu
    have hfst :
        w.1 ∈ asymptoticCone ℝ C := by
      refine mem_asymptoticCone_of_seq_smul hc hufst ?_
      intro n
      exact (hmem n).1
    have hsnd :
        w.2 ∈ asymptoticCone ℝ D := by
      refine mem_asymptoticCone_of_seq_smul hc husnd ?_
      intro n
      exact (hmem n).2
    exact ⟨Set.mem_insert_of_mem 0 hfst, Set.mem_insert_of_mem 0 hsnd⟩

/-- If the second factor is nonempty, then every pair `(u, 0)` with
`u ∈ horizonCone C` belongs to the horizon cone of `C × D`. -/
theorem prod_horizonCone_zero_subset_horizonCone_prod
    [FiniteDimensional ℝ E]
    {C : Set E} {D : Set F} (hDne : D.Nonempty) :
    horizonCone C ×ˢ ({0} : Set F) ⊆ horizonCone (C ×ˢ D) := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  have hv0 : v = 0 := by simpa using hv
  subst v
  rcases hDne with ⟨y, hy⟩
  have hu' : u = 0 ∨ u ∈ asymptoticCone ℝ C := by
    simpa [horizonCone] using hu
  rcases hu' with rfl | hu
  · exact zero_mem_horizonCone (C ×ˢ D)
  · rcases exists_seq_pos_smul_of_mem_asymptoticCone (C := C) hu with
      ⟨c, x, hc, hx, hcpos, hmem⟩
    have hy0 : Tendsto (fun n => (c n)⁻¹ • y) atTop (𝓝 (0 : F)) := by
      simpa using hc.inv_tendsto_atTop.smul_const y
    have hxy :
        Tendsto (fun n => (x n, (c n)⁻¹ • y)) atTop (𝓝 (u, (0 : F))) :=
      by simpa [nhds_prod_eq] using hx.prodMk hy0
    have hmem' :
        ∀ n, c n • (x n, (c n)⁻¹ • y) ∈ C ×ˢ D := by
      intro n
      refine ⟨hmem n, ?_⟩
      simpa [smul_smul, mul_inv_cancel₀ (hcpos n).ne', one_smul] using hy
    exact Set.mem_insert_of_mem 0 <|
      mem_asymptoticCone_of_seq_smul hc hxy hmem'

/-- **Exercise 3.11** (equality, convex case; binary version): for nonempty
convex sets, the horizon cone of the product is the product of the horizon
cones. -/
theorem horizonCone_prod_eq_of_convex_nonempty
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : Set E} {D : Set F}
    (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) :
    horizonCone (C ×ˢ D) = horizonCone C ×ˢ horizonCone D := by
  refine le_antisymm horizonCone_prod_subset ?_
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  rcases hCne with ⟨x, hx⟩
  rcases hDne with ⟨y, hy⟩
  have hray :
      ∀ ⦃τ : ℝ⦄, 0 ≤ τ → τ • (u, v) + (x, y) ∈ closure (C ×ˢ D) := by
    intro τ hτ
    have hxτ : τ • u + x ∈ closure C :=
      smul_add_mem_closure_of_mem_horizonCone hC (subset_closure hx) hu hτ
    have hyτ : τ • v + y ∈ closure D :=
      smul_add_mem_closure_of_mem_horizonCone hD (subset_closure hy) hv hτ
    simpa [closure_prod_eq] using show (τ • u + x, τ • v + y) ∈ closure C ×ˢ closure D from
      ⟨hxτ, hyτ⟩
  have hclosure :
      (u, v) ∈ horizonCone (closure (C ×ˢ D)) :=
    mem_horizonCone_of_forall_smul_add_mem (C := closure (C ×ˢ D)) (x := (x, y))
      (w := (u, v)) hray
  simpa [horizonCone_closure] using hclosure

/-- **Exercise 3.11** (equality, one bounded factor; binary version): if the
second factor is nonempty and bounded, the product horizon cone only records
the first factor. -/
theorem horizonCone_prod_eq_of_bounded_right
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {C : Set E} {D : Set F}
    (hDne : D.Nonempty) (hDbdd : IsBounded D) :
    horizonCone (C ×ˢ D) = horizonCone C ×ˢ ({0} : Set F) := by
  have hDzero : horizonCone D = ({0} : Set F) :=
    (isBounded_iff_horizonCone_eq_singleton_zero (C := D)).mp hDbdd
  refine le_antisymm ?_ (prod_horizonCone_zero_subset_horizonCone_prod hDne)
  intro w hw
  have hw' : w ∈ horizonCone C ×ˢ horizonCone D :=
    horizonCone_prod_subset hw
  exact ⟨hw'.1, by simpa [hDzero] using hw'.2⟩

end Products

section Sums

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private def addLinearMap : E × E →ₗ[ℝ] E :=
  LinearMap.fst ℝ E E + LinearMap.snd ℝ E E

private theorem addLinearMap_apply (p : E × E) :
    addLinearMap p = p.1 + p.2 := by
  rfl

variable [FiniteDimensional ℝ E]

private theorem addLinearMap_hker
    {C D : Set E}
    (hker : ∀ ⦃u v : E⦄, u ∈ horizonCone C → v ∈ horizonCone D →
      u + v = 0 → u = 0 ∧ v = 0) :
    ∀ ⦃w : E × E⦄, w ∈ horizonCone (C ×ˢ D) → addLinearMap w = 0 → w = 0 := by
  intro w hw hsum
  have hw' : w.1 ∈ horizonCone C ∧ w.2 ∈ horizonCone D :=
    horizonCone_prod_subset hw
  have hzero : w.1 = 0 ∧ w.2 = 0 := by
    apply hker hw'.1 hw'.2
    simpa [addLinearMap_apply] using hsum
  ext <;> simp [hzero.1, hzero.2]

/-- **Exercise 3.12** (closedness criterion, binary version): if there is no
nontrivial cancellation between horizon directions of two closed sets, then
their sum is closed. -/
theorem isClosed_add_of_horizonCone_no_cancel
    {C D : Set E} (hC : IsClosed C) (hD : IsClosed D)
    (hker : ∀ ⦃u v : E⦄, u ∈ horizonCone C → v ∈ horizonCone D →
      u + v = 0 → u = 0 ∧ v = 0) :
    IsClosed (C + D) := by
  have hprod : IsClosed (C ×ˢ D) := hC.prod hD
  simpa [addLinearMap, Set.add_image_prod] using
    isClosed_linearImage_of_horizonCone_ker_trivial
      (L := addLinearMap) (C := C ×ˢ D) hprod (addLinearMap_hker hker)

/-- **Exercise 3.12** (horizon-cone inclusion, binary version): under the same
noncancellation hypothesis, the horizon cone of the sum is contained in the
sum of the horizon cones. -/
theorem horizonCone_add_subset_of_horizonCone_no_cancel
    {C D : Set E}
    (hker : ∀ ⦃u v : E⦄, u ∈ horizonCone C → v ∈ horizonCone D →
      u + v = 0 → u = 0 ∧ v = 0) :
    horizonCone (C + D) ⊆ horizonCone C + horizonCone D := by
  have himage :
      addLinearMap '' horizonCone (C ×ˢ D) ⊆ horizonCone C + horizonCone D := by
    rintro x ⟨w, hw, rfl⟩
    have hw' : w.1 ∈ horizonCone C ∧ w.2 ∈ horizonCone D :=
      horizonCone_prod_subset hw
    exact Set.mem_add.2 ⟨w.1, hw'.1, w.2, hw'.2, by simp [addLinearMap_apply]⟩
  have heq :
      addLinearMap '' horizonCone (C ×ˢ D) =
        horizonCone (addLinearMap '' (C ×ˢ D)) :=
    linearImage_horizonCone_eq (L := addLinearMap) (C := C ×ˢ D) (addLinearMap_hker hker)
  have htmp :
      horizonCone (addLinearMap '' (C ×ˢ D)) ⊆ horizonCone C + horizonCone D := by
    rw [← heq]
    exact himage
  simpa [addLinearMap, Set.add_image_prod] using htmp

/-- **Exercise 3.12** (equality, convex case; binary version): under the same
noncancellation hypothesis, convex nonempty factors satisfy
`(C + D)∞ = C∞ + D∞`. -/
theorem horizonCone_add_eq_of_convex_nonempty_of_horizonCone_no_cancel
    {C D : Set E}
    (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hker : ∀ ⦃u v : E⦄, u ∈ horizonCone C → v ∈ horizonCone D →
      u + v = 0 → u = 0 ∧ v = 0) :
    horizonCone (C + D) = horizonCone C + horizonCone D := by
  calc
    horizonCone (C + D)
        = horizonCone (addLinearMap '' (C ×ˢ D)) := by
            simp [addLinearMap]
    _ = addLinearMap '' horizonCone (C ×ˢ D) := by
          symm
          exact linearImage_horizonCone_eq (L := addLinearMap) (C := C ×ˢ D)
            (addLinearMap_hker hker)
    _ = addLinearMap '' (horizonCone C ×ˢ horizonCone D) := by
          rw [horizonCone_prod_eq_of_convex_nonempty hC hD hCne hDne]
    _ = horizonCone C + horizonCone D := by
          simp [addLinearMap]

/-- **Exercise 3.12** (bounded perturbations): adding a nonempty bounded set
does not change the horizon cone. -/
theorem horizonCone_add_eq_of_bounded_right
    {C D : Set E}
    (hDne : D.Nonempty) (hDbdd : IsBounded D) :
    horizonCone (C + D) = horizonCone C := by
  have hprod :
      horizonCone (C ×ˢ D) = horizonCone C ×ˢ ({0} : Set E) :=
    horizonCone_prod_eq_of_bounded_right (C := C) (D := D) hDne hDbdd
  have hker :
      ∀ ⦃w : E × E⦄, w ∈ horizonCone (C ×ˢ D) → addLinearMap w = 0 → w = 0 := by
    intro w hw hsum
    have hw' : w ∈ horizonCone C ×ˢ ({0} : Set E) := by
      simpa [hprod] using hw
    have hv0 : w.2 = 0 := by
      simpa using hw'.2
    have hu0 : w.1 = 0 := by
      simpa [addLinearMap_apply, hv0] using hsum
    ext <;> assumption
  calc
    horizonCone (C + D)
        = horizonCone (addLinearMap '' (C ×ˢ D)) := by
            simp [addLinearMap]
    _ = addLinearMap '' horizonCone (C ×ˢ D) := by
          symm
          exact linearImage_horizonCone_eq (L := addLinearMap) (C := C ×ˢ D) hker
    _ = addLinearMap '' (horizonCone C ×ˢ ({0} : Set E)) := by
          rw [hprod]
    _ = horizonCone C + ({0} : Set E) := by
          simp [addLinearMap]
    _ = horizonCone C := by simp

/-- **Exercise 3.12** (bounded perturbations, closedness): adding a bounded
closed set preserves closedness. -/
theorem isClosed_add_of_bounded_right
    {C D : Set E} (hC : IsClosed C) (hD : IsClosed D)
    (hDbdd : IsBounded D) :
    IsClosed (C + D) := by
  have hker :
      ∀ ⦃u v : E⦄, u ∈ horizonCone C → v ∈ horizonCone D →
        u + v = 0 → u = 0 ∧ v = 0 := by
    intro u v hu hv huv
    have hDzero : horizonCone D = ({0} : Set E) :=
      (isBounded_iff_horizonCone_eq_singleton_zero (C := D)).mp hDbdd
    have hv0 : v = 0 := by
      simpa [hDzero] using hv
    subst v
    exact ⟨by simpa using huv, rfl⟩
  exact isClosed_add_of_horizonCone_no_cancel hC hD hker

end Sums

end RW
