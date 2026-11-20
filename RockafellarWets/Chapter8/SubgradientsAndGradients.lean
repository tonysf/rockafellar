/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Subgradients and gradients
-/

import RockafellarWets.Chapter8.HorizonSubgradientSequences
import RockafellarWets.Chapter8.SubgradientRelationships
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Filter Function Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Exercise 8.8(a).** Differentiability at the single base point
determines its regular subdifferential and gives a limiting subgradient. -/
theorem regularSubdifferential_of_hasGradientAt {k : E → ℝ} {x u : E} (hk : HasGradientAt k u x) :
    regularSubdifferential (fun y ↦ (k y : EReal)) x = {u} ∧ u ∈ subdifferential (fun y ↦ (k y : EReal)) x := by
  have hm := mem_regularSubdifferential_iff_exists_hasGradientAt (f := fun y ↦ (k y : EReal)) (x := x) (v := u) rfl
  have hu : u ∈ regularSubdifferential (fun y ↦ (k y : EReal)) x :=
    hm.mpr ⟨k, .of_forall fun _ ↦ le_rfl, rfl, hk⟩
  refine ⟨Subset.antisymm ?_ (singleton_subset_iff.mpr hu), regularSubdifferential_subset_subdifferential _ _ hu⟩
  intro v hv
  obtain ⟨h, hle, hx, hh⟩ := (mem_regularSubdifferential_iff_exists_hasGradientAt (f := fun y ↦ (k y : EReal)) rfl).mp hv
  have hmin : IsLocalMin (fun y ↦ k y - h y) x := by
    filter_upwards [hle] with y hy
    change k x - h x ≤ k y - h y
    rw [hx, sub_self]
    exact sub_nonneg.mpr (EReal.coe_le_coe_iff.mp hy)
  have hz := hmin.hasFDerivAt_eq_zero (hk.hasFDerivAt.sub hh.hasFDerivAt)
  exact (InnerProductSpace.toDual ℝ E).injective (sub_eq_zero.mp hz).symm

private theorem regularSubgradient_add {g : E → EReal} {k : E → ℝ} {x u v : E}
    (hg : v ∈ regularSubdifferential g x) (hk : HasGradientAt k u x) :
    v + u ∈ regularSubdifferential (fun y ↦ g y + (k y : EReal)) x := by
  let c := hg.choose
  have hc : g x = (c : EReal) := hg.choose_spec.1
  have hsum : g x + (k x : EReal) = ((c + k x : ℝ) : EReal) := by rw [hc, EReal.coe_add]
  obtain ⟨h, hle, hx, hh⟩ := (mem_regularSubdifferential_iff_exists_hasGradientAt hc).mp hg
  apply (mem_regularSubdifferential_iff_exists_hasGradientAt (f := fun z ↦ g z + (k z : EReal)) hsum).mpr
  refine ⟨fun y ↦ h y + k y, ?_, by simp only [hx], ?_⟩
  · filter_upwards [hle] with y hy
    rw [EReal.coe_add]
    exact add_le_add_left hy _
  · rw [hasGradientAt_iff_hasFDerivAt, map_add]
    exact hh.hasFDerivAt.add hk.hasFDerivAt

/-- Passing to a tail puts all the terms in the neighborhood where the
smooth perturbation is differentiable. Argument and value convergence
are recorded together with convergence of the translated gradients. -/
private theorem regularSubgradient_sequence_add {g : E → EReal} {k : E → ℝ} {x : E} {c : ℝ}
    (hx : g x = c) (hk : ContDiffAt ℝ 1 k x) {y v : ℕ → E}
    (hy : Tendsto y atTop (attentiveNhds g x)) (hv : ∀ n, v n ∈ regularSubdifferential g (y n)) :
    ∃ N : ℕ, Tendsto (fun n ↦ y (n+N)) atTop (attentiveNhds (fun z ↦ g z + (k z : EReal)) x) ∧
      (∀ n, v (n+N) + gradient k (y (n+N)) ∈ regularSubdifferential (fun z ↦ g z + (k z : EReal)) (y (n+N))) ∧
      Tendsto (fun n ↦ gradient k (y (n+N))) atTop (𝓝 (gradient k x)) := by
  obtain ⟨hyx, hval⟩ := tendsto_attentiveNhds_iff.mp hy
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hyx.eventually (hk.eventually (by simp)))
  have hNto := tendsto_add_atTop_nat N
  have hgrad : ContinuousAt (gradient k) x := (InnerProductSpace.toDual ℝ E).symm.continuous.continuousAt.comp
    (hk.continuousAt_fderiv one_ne_zero)
  refine ⟨N, tendsto_attentiveNhds_iff.mpr ⟨hyx.comp hNto, ?_⟩,
    fun n ↦ regularSubgradient_add (hv _) ((hN _ (Nat.le_add_left N n)).differentiableAt one_ne_zero).hasGradientAt,
    (hgrad.tendsto.comp hyx).comp hNto⟩
  have hkval := EReal.tendsto_coe.mpr (hk.continuousAt.tendsto.comp hyx)
  rw [hx] at hval ⊢
  exact ((EReal.continuousAt_add_coe_coe c (k x)).tendsto.comp (hval.prodMk_nhds hkval)).comp hNto

private theorem limitingSubgradient_add {g : E → EReal} {k : E → ℝ} {x v : E} {c : ℝ}
    (hx : g x = c) (hk : ContDiffAt ℝ 1 k x) (hv : v ∈ subdifferential g x) :
    v + gradient k x ∈ subdifferential (fun z ↦ g z + (k z : EReal)) x := by
  obtain ⟨-, y, u, hy, hval, hu, hlim⟩ := mem_subdifferential_iff_exists_seq.mp hv
  obtain ⟨N, hN, hreg, hgrad⟩ := regularSubgradient_sequence_add hx hk (tendsto_attentiveNhds_iff.mpr ⟨hy,hval⟩) hu
  obtain ⟨ha, hb⟩ := tendsto_attentiveNhds_iff.mp hN
  exact mem_subdifferential_iff_exists_seq.mpr ⟨⟨c + k x, by rw [hx, EReal.coe_add]⟩, _, _, ha, hb, hreg,
    (hlim.comp (tendsto_add_atTop_nat N)).add hgrad⟩

private theorem horizonSubgradient_add {g : E → EReal} {k : E → ℝ} {x v : E} {c : ℝ}
    (hx : g x = c) (hk : ContDiffAt ℝ 1 k x) (hv : v ∈ horizonSubdifferential g x) :
    v ∈ horizonSubdifferential (fun z ↦ g z + (k z : EReal)) x := by
  have hsum : g x + (k x : EReal) = ((c + k x : ℝ) : EReal) := by rw [hx, EReal.coe_add]
  rw [mem_horizonSubdifferential_iff_zero_or_scaledSeq (f := fun z ↦ g z + (k z : EReal)) hsum]
  rcases (mem_horizonSubdifferential_iff_zero_or_scaledSeq hx).mp hv with rfl | ⟨y, u, t, hy, hu, hpos, ht, hlim⟩
  · exact Or.inl rfl
  obtain ⟨N, hN, hreg, hgrad⟩ := regularSubgradient_sequence_add hx hk hy hu
  have hNto := tendsto_add_atTop_nat N
  have hzero := (ht.comp hNto).smul hgrad
  refine Or.inr ⟨_, _, fun n ↦ t (n+N), hN, hreg, fun n ↦ hpos _, ht.comp hNto, ?_⟩
  simpa only [Function.comp_def, zero_smul, add_zero, smul_add] using (hlim.comp hNto).add hzero

/-- **Exercise 8.8(c).** Smooth perturbation translates the regular and
limiting subdifferentials by the gradient, and preserves the horizon subdifferential. -/
theorem subdifferentials_add_smooth {g : E → EReal} {k : E → ℝ} {x : E} {c : ℝ}
    (hx : g x = c) (hk : ContDiffAt ℝ 1 k x) :
    let f := fun y ↦ g y + (k y : EReal)
    regularSubdifferential f x = (fun u ↦ u + gradient k x) '' regularSubdifferential g x ∧
      subdifferential f x = (fun u ↦ u + gradient k x) '' subdifferential g x ∧
      horizonSubdifferential f x = horizonSubdifferential g x := by
  let f := fun y ↦ g y + (k y : EReal)
  have hfx : f x = ((c + k x : ℝ) : EReal) := by simp only [f, hx, EReal.coe_add]
  have undo : (fun y ↦ f y + ((-k y : ℝ) : EReal)) = g := by
    funext y
    simp only [f, add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  have hkgrad := (hk.differentiableAt one_ne_zero).hasGradientAt
  have hneg : HasGradientAt (fun y ↦ -k y) (-gradient k x) x := by
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact hkgrad.hasFDerivAt.neg
  have hkneg : gradient (fun y ↦ -k y) x = -gradient k x :=
    ((hk.neg.differentiableAt one_ne_zero).hasGradientAt).unique hneg
  refine ⟨Subset.antisymm ?_ ?_, Subset.antisymm ?_ ?_, Subset.antisymm ?_ ?_⟩
  · intro u hu
    have h := regularSubgradient_add hu hneg
    rw [undo] at h
    exact ⟨u + -gradient k x, h, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact regularSubgradient_add hu hkgrad
  · intro u hu
    have h := limitingSubgradient_add hfx hk.neg hu
    rw [undo, hkneg] at h
    exact ⟨u + -gradient k x, h, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact limitingSubgradient_add hx hk hu
  · intro u hu
    have h := horizonSubgradient_add hfx hk.neg hu
    rwa [undo] at h
  · exact fun _ hu ↦ horizonSubgradient_add hx hk hu

/-- **Exercise 8.8(b).** Local continuous differentiability gives a singleton
limiting subdifferential, a zero horizon subdifferential and a singleton cosmic set. -/
theorem subdifferentials_of_smooth {k : E → ℝ} {x : E} (hk : ContDiffAt ℝ 1 k x) :
    let f := fun y ↦ (k y : EReal)
    subdifferential f x = {gradient k x} ∧ horizonSubdifferential f x = {0} ∧
      cosmicSet (subdifferential f x) (horizonSubdifferential f x) = {cosmicEmbed (gradient k x)} := by
  let g := fun _ : E ↦ (0 : EReal)
  have hg (y : E) : HasGradientAt (fun _ : E ↦ (0 : ℝ)) 0 y := by
    rw [hasGradientAt_iff_hasFDerivAt, map_zero]
    exact hasFDerivAt_const _ _
  have hreg (y : E) : regularSubdifferential g y = {0} := (regularSubdifferential_of_hasGradientAt (hg y)).1
  have hs : subdifferential g x = {0} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr (regularSubdifferential_of_hasGradientAt (hg x)).2)
    intro v hv
    obtain ⟨-, y, u, -, -, hu, hlim⟩ := mem_subdifferential_iff_exists_seq.mp hv
    have hz : ∀ n, u n = 0 := fun n ↦ by simpa only [hreg, mem_singleton_iff] using hu n
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n ↦ (hz n).symm)
  have hh : horizonSubdifferential g x = {0} := by
    ext v
    rw [mem_horizonSubdifferential_iff_zero_or_scaledSeq (f := g) (c := 0) rfl]
    refine ⟨fun h ↦ ?_, Or.inl⟩
    rcases h with hv | ⟨y, u, t, -, hu, -, -, hlim⟩
    · exact hv
    have hz : ∀ n, u n = 0 := fun n ↦ by simpa only [hreg, mem_singleton_iff] using hu n
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n ↦ by simp [hz])
  obtain ⟨-, hs', hh'⟩ := subdifferentials_add_smooth (g := g) (c := 0) rfl hk
  simp only [g, zero_add] at hs' hh' hs hh
  rw [hs, image_singleton, zero_add] at hs'
  rw [hh] at hh'
  exact ⟨hs', hh', by rw [hs', hh', cosmicSet_singleton_zero]⟩

end RW
