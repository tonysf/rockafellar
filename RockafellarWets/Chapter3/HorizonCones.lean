/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3B: Horizon Cones

This file formalizes the first basic results from Chapter 3 of
Rockafellar & Wets, "Variational Analysis":
- Theorem 3.5: boundedness criterion via the horizon cone
- Theorem 3.6: convexity of the horizon cone of a convex set
- Theorem 3.6: rays in horizon directions stay in a closed convex set
-/

import RockafellarWets.Chapter3.Defs

open Set Bornology Filter Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 3.5**: A set is bounded iff its horizon cone is the zero cone. -/
theorem isBounded_iff_horizonCone_eq_singleton_zero [FiniteDimensional ℝ E]
    {C : Set E} :
    IsBounded C ↔ horizonCone C = ({0} : Set E) := by
  constructor
  · intro hC
    have hsubset : asymptoticCone ℝ C ⊆ ({0} : Set E) :=
      (isBounded_iff_asymptoticCone_subset_singleton (s := C)).mp hC
    apply le_antisymm
    · rintro x (rfl | hx)
      · simp
      · exact hsubset hx
    · intro x hx
      simp at hx
      simp [horizonCone, hx]
  · intro hC
    refine (isBounded_iff_asymptoticCone_subset_singleton (s := C)).mpr ?_
    intro x hx
    have hx' : x ∈ horizonCone C := by
      exact Set.mem_insert_of_mem 0 hx
    rwa [hC] at hx'

/-- **Theorem 3.6**: The horizon cone of a convex set is convex. -/
theorem convex_horizonCone {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (horizonCone C) := by
  by_cases hne : C.Nonempty
  · simpa [horizonCone, zero_mem_asymptoticCone.mpr hne] using hC.asymptoticCone
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [horizonCone, hCempty]

/-- If every ray in the direction `w` starting from `x` lies in `C`, then `w`
belongs to the horizon cone of `C`. -/
theorem mem_horizonCone_of_forall_smul_add_mem
    {C : Set E} {x w : E}
    (h : ∀ ⦃τ : ℝ⦄, 0 ≤ τ → τ • w + x ∈ C) :
    w ∈ horizonCone C := by
  refine Set.mem_insert_of_mem 0 ?_
  rw [mem_asymptoticCone_iff]
  let ψ : ℝ → E := fun τ => w + τ⁻¹ • x
  have hψ : Tendsto ψ atTop (𝓝 w) := by
    have hx : Tendsto (fun τ : ℝ => τ⁻¹ • x) atTop (𝓝 (0 : E)) := by
      simpa using
        ((tendsto_inv_atTop_zero : Tendsto (fun τ : ℝ => τ⁻¹) atTop (𝓝 (0 : ℝ))).smul_const x)
    simpa [ψ] using (tendsto_const_nhds (x := w)).add hx
  have hsmul : Tendsto (fun τ : ℝ => τ • ψ τ) atTop (AffineSpace.asymptoticNhds ℝ E w) := by
    simpa using
      (Filter.Tendsto.atTop_smul_nhds_tendsto_asymptoticNhds
        (k := ℝ) (V := E) (f := fun τ : ℝ => τ) (g := ψ) (v := w) tendsto_id hψ)
  refine hsmul.frequently ?_
  have h_event : ∀ᶠ τ : ℝ in atTop, τ • ψ τ ∈ C := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
    have hmem : τ • w + x ∈ C := h hτ.le
    have hcalc : τ • ψ τ = τ • w + x := by
      simp [ψ, smul_add, smul_smul, hτ.ne']
    simpa [hcalc] using hmem
  exact h_event.frequently

/-- If `w` lies in the horizon cone of a convex set `C`, then every ray in the
direction `w` starting from a point of `closure C` stays in `closure C`. -/
theorem smul_add_mem_closure_of_mem_horizonCone
    {C : Set E} (hC : Convex ℝ C) {x w : E}
    (hx : x ∈ closure C) (hw : w ∈ horizonCone C) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ • w + x ∈ closure C := by
  have hw_cl : w ∈ horizonCone (closure C) := by
    simpa [horizonCone_closure C] using hw
  have hw' : w ∈ asymptoticCone ℝ (closure C) := by
    simpa [horizonCone_eq_asymptoticCone (show (closure C).Nonempty from ⟨x, hx⟩)] using hw_cl
  simpa [vadd_eq_add] using
    hC.closure.smul_vadd_mem_of_isClosed_of_mem_asymptoticCone
      isClosed_closure hτ hw' hx

/-- **Theorem 3.6** (closed-case ray characterization, one direction): if `w`
lies in the horizon cone of a closed convex set `C`, then every ray in the
direction `w` starting from a point of `C` stays in `C`. -/
theorem smul_add_mem_of_mem_horizonCone
    {C : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C) {x w : E}
    (hx : x ∈ C) (hw : w ∈ horizonCone C) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ • w + x ∈ C := by
  simpa [hC_closed.closure_eq] using
    smul_add_mem_closure_of_mem_horizonCone hC
      (x := x) (w := w) (by simpa [hC_closed.closure_eq] using hx) hw hτ

/-- Horizon cones are monotone with respect to set inclusion. -/
theorem horizonCone_mono {C D : Set E} (hCD : C ⊆ D) :
    horizonCone C ⊆ horizonCone D := by
  intro w hw
  rcases hw with rfl | hw
  · exact zero_mem_horizonCone D
  · exact Set.mem_insert_of_mem 0 <| asymptoticCone_mono hCD hw

/-- **Proposition 3.9** (intersection inclusion): the horizon cone of an
arbitrary intersection is contained in the intersection of the horizon cones. -/
theorem horizonCone_iInter_subset_iInter_horizonCone {ι : Type*}
    (C : ι → Set E) :
    horizonCone (⋂ i, C i) ⊆ ⋂ i, horizonCone (C i) := by
  intro w hw
  refine Set.mem_iInter.2 ?_
  intro i
  exact horizonCone_mono (show (⋂ i, C i) ⊆ C i from by
    intro x hx
    exact Set.mem_iInter.mp hx i) hw

/-- **Proposition 3.9** (union inclusion): the union of the individual horizon
cones is contained in the horizon cone of the union. -/
theorem iUnion_horizonCone_subset_horizonCone_iUnion {ι : Type*}
    (C : ι → Set E) :
    (Set.iUnion fun i => horizonCone (C i)) ⊆ horizonCone (Set.iUnion C) := by
  intro w hw
  rw [Set.mem_iUnion] at hw
  rcases hw with ⟨i, hw⟩
  exact horizonCone_mono (Set.subset_iUnion C i) hw

/-- The horizon cone of a finite union is the union of the horizon cones. -/
theorem horizonCone_iUnion_eq_iUnion_horizonCone {ι : Type*} [Finite ι] [Nonempty ι]
    (C : ι → Set E) :
    horizonCone (⋃ i, C i) = ⋃ i, horizonCone (C i) := by
  ext w
  by_cases hw : w = 0
  · subst hw
    simp
  · simp [horizonCone, hw, asymptoticCone_iUnion_of_finite, Set.mem_iUnion]

/-- The horizon cone of a nonempty intersection of closed convex sets is the
intersection of the individual horizon cones. -/
theorem horizonCone_iInter_eq_iInter_horizonCone {ι : Type*} {C : ι → Set E}
    (hconv : ∀ i, Convex ℝ (C i)) (hclosed : ∀ i, IsClosed (C i))
    (hne : (⋂ i, C i).Nonempty) :
    horizonCone (⋂ i, C i) = ⋂ i, horizonCone (C i) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    refine Set.mem_iInter.2 ?_
    intro i
    exact horizonCone_mono (show (⋂ i, C i) ⊆ C i from by
      intro x hx
      have hx' : ∀ j, x ∈ C j := by
        simpa [Set.mem_iInter] using hx
      exact hx' i) hw
  · rcases hne with ⟨x, hx⟩
    have hx' : ∀ i, x ∈ C i := by
      simpa [Set.mem_iInter] using hx
    intro w hw
    have hw' : ∀ i, w ∈ horizonCone (C i) := by
      simpa [Set.mem_iInter] using hw
    refine mem_horizonCone_of_forall_smul_add_mem (C := ⋂ i, C i) (x := x) (w := w) ?_
    intro τ hτ
    refine Set.mem_iInter.2 ?_
    intro i
    exact smul_add_mem_of_mem_horizonCone (C := C i) (hconv i) (hclosed i) (hx' i) (hw' i) hτ

/-- The horizon cone of a nonempty intersection of two closed convex sets is
the intersection of the individual horizon cones. -/
theorem horizonCone_inter_eq_inter_horizonCone
    {C D : Set E} (hconvC : Convex ℝ C) (hconvD : Convex ℝ D)
    (hclosedC : IsClosed C) (hclosedD : IsClosed D)
    (hne : (C ∩ D).Nonempty) :
    horizonCone (C ∩ D) = horizonCone C ∩ horizonCone D := by
  let S : Bool → Set E := fun b => if b then C else D
  have hinter : (⋂ b, S b) = C ∩ D := by
    ext x
    simp [S, and_comm]
  have hhoriz :
      (⋂ b, horizonCone (S b)) = horizonCone C ∩ horizonCone D := by
    ext w
    simp [S, and_comm]
  have hmain :
      horizonCone (⋂ b, S b) = ⋂ b, horizonCone (S b) := by
    apply horizonCone_iInter_eq_iInter_horizonCone
    · intro b
      by_cases hb : b
      · simp [S, hb, hconvC]
      · simp [S, hb, hconvD]
    · intro b
      by_cases hb : b
      · simp [S, hb, hclosedC]
      · simp [S, hb, hclosedD]
    · simpa [hinter] using hne
  rw [← hinter, hmain, hhoriz]

end RW
