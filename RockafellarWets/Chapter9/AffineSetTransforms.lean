/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invertible affine transformations acting on a set
-/

import RockafellarWets.Chapter9.GraphConvexModulus
import RockafellarWets.Chapter9.AubinAbsoluteLocalization
import Mathlib.Analysis.Normed.Ring.Units

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {A : E → F ≃L[ℝ] F} {a : E → F} {C : Set F} {x : E}

/-- The image of a fixed set under a parameter-dependent invertible affine map. -/
def affineSetTransform (A : E → F ≃L[ℝ] F) (a : E → F) (C : Set F) (x : E) : Set F :=
  (fun z ↦ A x z + a x) '' C

theorem affineSetTransform_nonempty_closed (hC : C.Nonempty) (hc : IsClosed C) (x : E) :
    (affineSetTransform A a C x).Nonempty ∧ IsClosed (affineSetTransform A a C x) := by
  refine ⟨hC.image _,?_⟩
  exact ((A x).toHomeomorph.trans (Homeomorph.addRight (a x))).isClosedMap _ hc

/-- Operator inversion is continuous along a continuous family of invertible maps. -/
theorem continuousAt_affineTransform_inverse
    (hA : ContinuousAt (fun z ↦ (A z : F →L[ℝ] F)) x) :
    ContinuousAt (fun z ↦ ((A z).symm : F →L[ℝ] F)) x := by
  let q := (ContinuousLinearEquiv.unitsEquiv ℝ F).symm (A x)
  have hq : (q : F →L[ℝ] F) = (A x : F →L[ℝ] F) := rfl
  have hi : ContinuousAt Ring.inverse (A x : F →L[ℝ] F) := hq ▸ NormedRing.inverse_continuousAt q
  have hh := hi.comp (f := fun z : E ↦ (A z : F →L[ℝ] F)) hA
  simpa only [Function.comp_def,ContinuousLinearMap.ringInverse_equiv,ContinuousLinearMap.inverse_equiv] using hh

/-- Matching the same original point in two transformed fibers gives the
pointwise estimate underlying formula 9(15). -/
theorem affineSetTransform_transport {b c : E} {r : ℝ≥0} {v : F}
    (hv : v ∈ affineSetTransform A a C b ∩ closedBall (0:F) (r:ℝ)) :
    ∃ w ∈ affineSetTransform A a C c,
      dist v w ≤ ‖((A b).symm : F →L[ℝ] F)‖ * ((r:ℝ)+‖a b‖) *
        dist (A b : F →L[ℝ] F) (A c : F →L[ℝ] F) + dist (a b) (a c) := by
  obtain ⟨⟨z,hz,rfl⟩,hv⟩ := hv
  refine ⟨A c z + a c,mem_image_of_mem _ hz,?_⟩
  have hzbound : ‖z‖ ≤ ‖((A b).symm : F →L[ℝ] F)‖*((r:ℝ)+‖a b‖) := by
    calc
      ‖z‖ = ‖(A b).symm ((A b z+a b)-a b)‖ := by simp
      _ ≤ ‖((A b).symm : F →L[ℝ] F)‖ * ‖(A b z+a b)-a b‖ := ((A b).symm : F →L[ℝ] F).le_opNorm _
      _ ≤ ‖((A b).symm : F →L[ℝ] F)‖ * ((r:ℝ)+‖a b‖) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (mem_closedBall_zero_iff.mp hv) le_rfl)) (norm_nonneg _)
  calc
    _ ≤ dist (A b z) (A c z) + dist (a b) (a c) := dist_add_add_le _ _ _ _
    _ ≤ dist (A b : F →L[ℝ] F) (A c : F →L[ℝ] F)*‖z‖ + dist (a b) (a c) := by
      refine add_le_add ?_ le_rfl
      simpa only [dist_eq_norm,ContinuousLinearMap.sub_apply] using
        ((A b : F →L[ℝ] F)-(A c : F →L[ℝ] F)).le_opNorm z
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hzbound (dist_nonneg (x := (A b : F →L[ℝ] F)) (y := (A c : F →L[ℝ] F)))
      simpa only [mul_comm] using add_le_add hh (le_refl (dist (a b) (a c)))

/-- **Example 9.32**, formula 9(15): the inverse norm controls the exact
truncated-inclusion modulus of the transformed set. -/
theorem affineSetTransform_rhoHatModulus_le
    (hA : StrictlyContinuousAt (fun z ↦ (A z : F →L[ℝ] F)) x)
    (ha : StrictlyContinuousAt a x) (r : ℝ≥0) :
    svRhoHatLipschitzModulus (affineSetTransform A a C) r x ≤
      (‖((A x).symm : F →L[ℝ] F)‖₊ : ℝ≥0∞)*((r:ℝ≥0∞)+(‖a x‖₊:ℝ≥0∞))*
        lipschitzModulus (fun z ↦ (A z : F →L[ℝ] F)) x + lipschitzModulus a x := by
  let LA := (lipschitzModulus (fun z ↦ (A z : F →L[ℝ] F)) x).toNNReal
  let La := (lipschitzModulus a x).toNNReal
  let M : ℝ≥0 := ‖((A x).symm : F →L[ℝ] F)‖₊*(r+‖a x‖₊)
  have hLA : (LA:ℝ≥0∞) = lipschitzModulus (fun z ↦ (A z : F →L[ℝ] F)) x := ENNReal.coe_toNNReal hA.ne
  have hLa : (La:ℝ≥0∞) = lipschitzModulus a x := ENNReal.coe_toNNReal ha.ne
  have hcoeff : ContinuousAt (fun y ↦ ‖((A y).symm : F →L[ℝ] F)‖₊*(r+‖a y‖₊)) x :=
    (continuousAt_affineTransform_inverse hA.continuousAt).nnnorm.mul
      (continuousAt_const.add ha.continuousAt.nnnorm)
  have hb (ε : ℝ≥0) (hε : 0 < ε) :
      svRhoHatLipschitzModulus (affineSetTransform A a C) r x ≤
        (((M+ε)*(LA+ε)+(La+ε):ℝ≥0):ℝ≥0∞) := by
    have hα : lipschitzModulus (fun z ↦ (A z : F →L[ℝ] F)) x < ((LA+ε:ℝ≥0):ℝ≥0∞) := by
      rw [← hLA,ENNReal.coe_lt_coe]; exact lt_add_of_pos_right _ hε
    have hβ : lipschitzModulus a x < ((La+ε:ℝ≥0):ℝ≥0∞) := by
      rw [← hLa,ENNReal.coe_lt_coe]; exact lt_add_of_pos_right _ hε
    obtain ⟨V,hV,HA⟩ := exists_lipschitzOnWith_of_modulus_lt hα
    obtain ⟨W,hW,Ha⟩ := exists_lipschitzOnWith_of_modulus_lt hβ
    have hB : {y | ‖((A y).symm : F →L[ℝ] F)‖₊*(r+‖a y‖₊) < M+ε} ∈ 𝓝 x :=
      hcoeff.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε))
    let U := (V ∩ W) ∩ {y | ‖((A y).symm : F →L[ℝ] F)‖₊*(r+‖a y‖₊) < M+ε}
    have hU : U ∈ 𝓝 x := inter_mem (inter_mem hV hW) hB
    have ht : RhoTransport ((M+ε)*(LA+ε)+(La+ε)) r (affineSetTransform A a C) U := by
      intro b hb c hc v hv
      obtain ⟨w,hw,hd⟩ := affineSetTransform_transport hv
      refine ⟨w,hw,hd.trans ?_⟩
      have hf : ‖((A b).symm : F →L[ℝ] F)‖*((r:ℝ)+‖a b‖) ≤ ((M+ε:ℝ≥0):ℝ) := by
        exact_mod_cast hb.2.le
      calc
        _ ≤ ((M+ε:ℝ≥0):ℝ)*(((LA+ε:ℝ≥0):ℝ)*dist b c) + ((La+ε:ℝ≥0):ℝ)*dist b c :=
          add_le_add (mul_le_mul hf (HA.dist_le_mul b hb.1.1 c hc.1.1) dist_nonneg (by positivity))
            (Ha.dist_le_mul b hb.1.2 c hc.1.2)
        _ = _ := by simp only [NNReal.coe_add,NNReal.coe_mul]; ring
    exact ht.svRhoHatModulus_le hU
  have hlim : Tendsto (fun ε : ℝ≥0 ↦ (((M+ε)*(LA+ε)+(La+ε):ℝ≥0):ℝ≥0∞))
      (𝓝[>] (0:ℝ≥0)) (𝓝 ((M*LA+La:ℝ≥0):ℝ≥0∞)) := by
    have hc : Continuous (fun ε : ℝ≥0 ↦ (((M+ε)*(LA+ε)+(La+ε):ℝ≥0):ℝ≥0∞)) := by fun_prop
    simpa only [add_zero] using (hc.continuousAt (x := (0:ℝ≥0))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ≥0)))
  have he : ∀ᶠ ε : ℝ≥0 in 𝓝[>] (0:ℝ≥0), 0 < ε := self_mem_nhdsWithin
  have hh := ge_of_tendsto hlim (he.mono fun ε hε ↦ hb ε hε)
  simpa only [M,ENNReal.coe_add,ENNReal.coe_mul,hLA,hLa] using hh

/-- The transformed mapping is strictly continuous wherever both parameters
are strictly continuous and the fixed set is nonempty and closed. -/
theorem affineSetTransform_svStrictlyContinuousAt (hC : C.Nonempty) (hc : IsClosed C)
    (hA : StrictlyContinuousAt (fun z ↦ (A z : F →L[ℝ] F)) x)
    (ha : StrictlyContinuousAt a x) : SvStrictlyContinuousAt (affineSetTransform A a C) x := by
  have hS : NonemptyClosedValuedOn (affineSetTransform A a C) univ :=
    fun y _ ↦ affineSetTransform_nonempty_closed hC hc y
  apply (svStrictlyContinuousWithinAt_iff_local_rhoHatDistance (mem_univ x) hS).mpr
  intro r
  have hfin : svRhoHatLipschitzModulus (affineSetTransform A a C) r x < ⊤ :=
    (affineSetTransform_rhoHatModulus_le hA ha r).trans_lt (by
      apply ENNReal.add_lt_top.mpr
      exact ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top,ENNReal.coe_lt_top⟩)) hA,ha⟩)
  obtain ⟨k,hk,_⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hfin
  obtain ⟨U,hU,H⟩ := exists_local_pair_bound_of_modulus_lt hk
  refine ⟨k,U,hU,fun b hb c hc ↦ ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ (k:ℝ)*dist b c from mul_nonneg k.2 dist_nonneg)).mp
  rw [ofReal_rhoHatDistance r (hS b (mem_univ b)).1 (hS c (mem_univ c)).1]
  simpa only [edist_dist,ENNReal.ofReal_mul (p := (k:ℝ)) (q := dist b c) k.2,
    ENNReal.ofReal_coe_nnreal] using H b hb c hc

/-- The compact convex consequence in Example 9.32. -/
theorem affineSetTransform_svSubLipschitzOn (hC : C.Nonempty) (hc : IsClosed C) {X : Set E}
    (hX : IsCompact X) (hconv : Convex ℝ X)
    (hA : ∀ y ∈ X, StrictlyContinuousAt (fun z ↦ (A z : F →L[ℝ] F)) y)
    (ha : ∀ y ∈ X, StrictlyContinuousAt a y) :
    SvSubLipschitzOn (affineSetTransform A a C) X :=
  svSubLipschitzOn_of_compact_convex hconv hX fun y hy ↦
    affineSetTransform_svStrictlyContinuousAt hC hc (hA y hy) (ha y hy)

end RW
