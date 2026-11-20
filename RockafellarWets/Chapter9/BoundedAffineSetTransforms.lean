/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bounded sets and horizon obstructions for affine transformations
-/

import RockafellarWets.Chapter9.AffineSetTransforms
import RockafellarWets.Chapter4.PompeiuHausdorffProperties

open Filter Metric Set Topology
open scoped NNReal ENNReal Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {A : E → F ≃L[ℝ] F} {a : E → F} {C : Set F} {X : Set E} {x : E} {L kA ka : ℝ≥0}

/-- A bounded original set gives a uniform full-fiber transport estimate. -/
theorem affineSetTransform_lipschitzOnWith (hC : C.Nonempty) (hc : IsClosed C)
    (hbound : C ⊆ closedBall (0:F) (L:ℝ))
    (hA : LipschitzOnWith kA (fun z ↦ (A z : F →L[ℝ] F)) X)
    (ha : LipschitzOnWith ka a X) :
    SvLipschitzOnWith (L*kA+ka) (affineSetTransform A a C) X := by
  apply (svLipschitzOnWith_iff_transport (fun y _ ↦ affineSetTransform_nonempty_closed hC hc y)).mpr
  rintro b hb c hc' v ⟨z,hz,rfl⟩
  refine ⟨A c z+a c,mem_image_of_mem _ hz,?_⟩
  have hzbound : ‖z‖ ≤ (L:ℝ) := mem_closedBall_zero_iff.mp (hbound hz)
  have hop : dist (A b z) (A c z) ≤ dist (A b : F →L[ℝ] F) (A c : F →L[ℝ] F)*‖z‖ := by
    simpa only [dist_eq_norm,ContinuousLinearMap.sub_apply] using
      ((A b : F →L[ℝ] F)-(A c : F →L[ℝ] F)).le_opNorm z
  calc
    _ ≤ dist (A b z) (A c z)+dist (a b) (a c) := dist_add_add_le _ _ _ _
    _ ≤ (kA:ℝ)*dist b c*(L:ℝ)+(ka:ℝ)*dist b c :=
      add_le_add (hop.trans (mul_le_mul (hA.dist_le_mul b hb c hc') hzbound (norm_nonneg _) (by positivity)))
        (ha.dist_le_mul b hb c hc')
    _ = _ := by simp only [NNReal.coe_add,NNReal.coe_mul]; ring

/-- **Example 9.32**, the exact full Hausdorff-modulus bound when the fixed
set lies in the radius-`L` ball. -/
theorem affineSetTransform_hausdorffModulus_le (hC : C.Nonempty) (hc : IsClosed C)
    (hbound : C ⊆ closedBall (0:F) (L:ℝ))
    (hA : StrictlyContinuousAt (fun z ↦ (A z : F →L[ℝ] F)) x)
    (ha : StrictlyContinuousAt a x) :
    svHausdorffLipschitzModulus (affineSetTransform A a C) x ≤
      (L:ℝ≥0∞)*lipschitzModulus (fun z ↦ (A z : F →L[ℝ] F)) x + lipschitzModulus a x := by
  let LA := (lipschitzModulus (fun z ↦ (A z : F →L[ℝ] F)) x).toNNReal
  let La := (lipschitzModulus a x).toNNReal
  have hLA : (LA:ℝ≥0∞) = lipschitzModulus (fun z ↦ (A z : F →L[ℝ] F)) x := ENNReal.coe_toNNReal hA.ne
  have hLa : (La:ℝ≥0∞) = lipschitzModulus a x := ENNReal.coe_toNNReal ha.ne
  have hb (ε : ℝ≥0) (hε : 0 < ε) :
      svHausdorffLipschitzModulus (affineSetTransform A a C) x ≤
        ((L*(LA+ε)+(La+ε):ℝ≥0):ℝ≥0∞) := by
    have hα : lipschitzModulus (fun z ↦ (A z : F →L[ℝ] F)) x < ((LA+ε:ℝ≥0):ℝ≥0∞) := by
      rw [← hLA,ENNReal.coe_lt_coe]; exact lt_add_of_pos_right _ hε
    have hβ : lipschitzModulus a x < ((La+ε:ℝ≥0):ℝ≥0∞) := by
      rw [← hLa,ENNReal.coe_lt_coe]; exact lt_add_of_pos_right _ hε
    obtain ⟨V,hV,HA⟩ := exists_lipschitzOnWith_of_modulus_lt hα
    obtain ⟨W,hW,Ha⟩ := exists_lipschitzOnWith_of_modulus_lt hβ
    have H := affineSetTransform_lipschitzOnWith hC hc hbound (HA.mono inter_subset_left) (Ha.mono inter_subset_right)
    apply localPairModulusWithin_le (by simpa only [nhdsWithin_univ] using inter_mem hV hW)
    intro b hb c hc'
    simpa only [ENNReal.ofReal_mul (p := ((L*(LA+ε)+(La+ε):ℝ≥0):ℝ)) (q := dist b c) (by positivity),
      ENNReal.ofReal_coe_nnreal,edist_dist] using H.2 b hb c hc'
  have hlim : Tendsto (fun ε : ℝ≥0 ↦ ((L*(LA+ε)+(La+ε):ℝ≥0):ℝ≥0∞))
      (𝓝[>] (0:ℝ≥0)) (𝓝 ((L*LA+La:ℝ≥0):ℝ≥0∞)) := by
    have hcont : Continuous (fun ε : ℝ≥0 ↦ ((L*(LA+ε)+(La+ε):ℝ≥0):ℝ≥0∞)) := by fun_prop
    simpa only [add_zero] using (hcont.continuousAt (x := (0:ℝ≥0))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0:ℝ≥0)))
  have he : ∀ᶠ ε : ℝ≥0 in 𝓝[>] (0:ℝ≥0), 0 < ε := self_mem_nhdsWithin
  have hh := ge_of_tendsto hlim (he.mono fun ε hε ↦ hb ε hε)
  simpa only [ENNReal.coe_add,ENNReal.coe_mul,hLA,hLa] using hh

/-- Bounded fixed sets give full Lipschitz continuity on every compact
convex parameter set where both parameters are strictly continuous. -/
theorem affineSetTransform_svLipschitzOn (hC : C.Nonempty) (hc : IsClosed C) (hb : Bornology.IsBounded C)
    (hX : IsCompact X) (hconv : Convex ℝ X)
    (hA : ∀ y ∈ X, StrictlyContinuousAt (fun z ↦ (A z : F →L[ℝ] F)) y)
    (ha : ∀ y ∈ X, StrictlyContinuousAt a y) :
    SvLipschitzOn (affineSetTransform A a C) X := by
  obtain ⟨r,hr⟩ := hb.subset_closedBall (0:F)
  let L : ℝ≥0 := ⟨max r 0,le_max_right _ _⟩
  have hbound : C ⊆ closedBall (0:F) (L:ℝ) := hr.trans (closedBall_subset_closedBall (le_max_left _ _))
  rcases X.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0,⟨fun _ h ↦ h.elim,fun _ h ↦ h.elim⟩⟩
  · obtain ⟨_,_,kA,_,_,HA⟩ := exists_max_modulus_of_compact_convex hconv hX hne hA
    obtain ⟨_,_,ka,_,_,Ha⟩ := exists_max_modulus_of_compact_convex hconv hX hne ha
    exact ⟨L*kA+ka,affineSetTransform_lipschitzOnWith hC hc hbound HA Ha⟩

/-- The horizon cone of an invertible affine image is the linear image of
the original horizon cone. -/
theorem horizonCone_affineSetTransform (x : E) :
    horizonCone (affineSetTransform A a C x) = (A x) '' horizonCone C := by
  have heq : affineSetTransform A a C x = (A x '' C) + {a x} := by
    ext v
    simp only [affineSetTransform,mem_image,Set.mem_add,mem_singleton_iff]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨A x z,⟨z,hz,rfl⟩,a x,rfl,rfl⟩
    · rintro ⟨w,⟨z,hz,rfl⟩,b,rfl,rfl⟩
      exact ⟨z,hz,rfl⟩
  rw [heq,horizonCone_add_eq_of_bounded_right (singleton_nonempty _) Bornology.isBounded_singleton]
  symm
  exact linearImage_horizonCone_eq (L := (A x).toLinearMap) (fun _ _ hv ↦ (A x).injective (by simpa using hv))

/-- **Example 9.32**, the obstruction at infinity: a Lipschitz family has
one common transformed horizon cone on its whole parameter set. -/
theorem SvLipschitzOn.affineSetTransform_horizon_eq
    (h : SvLipschitzOn (affineSetTransform A a C) X) {b c : E} (hb : b ∈ X) (hc : c ∈ X) :
    (A b) '' horizonCone C = (A c) '' horizonCone C := by
  obtain ⟨k,H⟩ := h
  by_contra hn
  have hn' : horizonCone (affineSetTransform A a C b) ≠ horizonCone (affineSetTransform A a C c) := by
    simpa only [horizonCone_affineSetTransform] using hn
  have he := hausdorffEDist_eq_top_of_horizonCone_ne (H.1 b hb).2 (H.1 c hc).2
    (H.1 b hb).1 (H.1 c hc).1 hn'
  have hfin := H.2 b hb c hc
  rw [he] at hfin
  exact ENNReal.ofReal_ne_top (top_unique hfin)

end RW
