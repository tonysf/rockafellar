/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Translated set-distance characterizations of the Aubin property
-/

import RockafellarWets.Chapter9.AubinDistanceCriteria

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [MetricSpace E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {X : Set E} {x : E} {u : F} {k l : ℝ≥0}

/-- Translate the output point of interest to zero. -/
def svTranslate (S : E → Set F) (u : F) (a : E) : Set F := (fun v ↦ v-u) '' S a

private theorem output_sub_isometry (u : F) : Isometry (fun v : F ↦ v-u) :=
  Isometry.of_dist_eq fun a b ↦ dist_sub_right a b u

private theorem infDist_svTranslate (S : E → Set F) (u v : F) (a : E) :
    infDist v (svTranslate S u a) = infDist (v+u) (S a) := by
  simpa only [svTranslate,add_sub_cancel_right] using
    infDist_image (t := S a) (x := v+u) (output_sub_isometry u)

/-- The local translated distance-profile inequality of Exercise 9.37(d).
Nonempty fibers are explicit because `rhoDistance` uses real distances. -/
def AubinRhoEstimate (S : E → Set F) (X : Set E) (x : E) (u : F) (k : ℝ≥0) : Prop :=
  ∃ r : ℝ≥0, 0 < r ∧ ∃ V ∈ 𝓝 x, (∀ a ∈ X ∩ V, (S a).Nonempty) ∧
    ∀ a ∈ X ∩ V, ∀ b ∈ X ∩ V,
      rhoDistance r (svTranslate S u a) (svTranslate S u b) ≤ k*dist a b

/-- The local translated inclusion-distance inequality of Exercise 9.37(e).
The extended distance retains the intended meaning for empty fibers. -/
def AubinRhoHatEstimate (S : E → Set F) (X : Set E) (x : E) (u : F) (k : ℝ≥0) : Prop :=
  ∃ r : ℝ≥0, 0 < r ∧ ∃ V ∈ 𝓝 x,
    ∀ a ∈ X ∩ V, ∀ b ∈ X ∩ V,
      rhoHatEDistance r (svTranslate S u a) (svTranslate S u b) ≤ ENNReal.ofReal (k*dist a b)

/-- **Exercise 9.37(c,d).** Translation identifies the profile criteria with
exactly the same constant. -/
theorem aubinProfileEstimate_iff_rhoEstimate :
    AubinProfileEstimate S X x u k ↔ AubinRhoEstimate S X x u k := by
  constructor
  · rintro ⟨V,hV,W,hW,hn,H⟩
    obtain ⟨r,hr,hrW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hW
    refine ⟨⟨r,hr.le⟩,hr,V,hV,hn,fun a ha b hb ↦ ?_⟩
    apply (rhoDistance_le_iff (mul_nonneg k.2 dist_nonneg) _ _ _).mpr
    intro v hv
    have hvW : v+u ∈ W := hrW (by simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_right,sub_zero] using hv)
    simpa only [Real.dist_eq,infDist_svTranslate] using (H (v+u) hvW).dist_le_mul a ha b hb
  · rintro ⟨r,hr,V,hV,hn,H⟩
    refine ⟨V,hV,ball u (r:ℝ),ball_mem_nhds _ (by exact_mod_cast hr),hn,fun v hv ↦ ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have hv' : v-u ∈ closedBall (0:F) (r:ℝ) := by
      simpa only [mem_closedBall,dist_zero_right,← dist_eq_norm] using (show dist v u ≤ r from hv.le)
    have hd := (rhoDistance_le_iff (mul_nonneg k.2 dist_nonneg) r _ _).mp (H a ha b hb) (v-u) hv'
    simpa only [Real.dist_eq,infDist_svTranslate,sub_add_cancel] using hd

/-- A realized graphical constant is also a translated inclusion constant. -/
theorem AubinEstimate.rhoHatEstimate (h : AubinEstimate S X x u k) :
    AubinRhoHatEstimate S X x u k := by
  obtain ⟨V,hV,W,hW,H⟩ := h
  obtain ⟨r,hr,hrW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hW
  refine ⟨⟨r,hr.le⟩,hr,V,hV,fun a ha b hb ↦ ?_⟩
  apply (rhoHatEDistance_le_iff _ _ _).mpr
  have htransport {a b : E} (ha : a ∈ X ∩ V) (hb : b ∈ X ∩ V) :
      svTranslate S u a ∩ closedBall (0:F) r ⊆ cthickening ((k:ℝ)*dist a b) (svTranslate S u b) := by
    rintro z ⟨⟨v,hv,rfl⟩,hz⟩
    have hvW : v ∈ W := hrW (by simpa only [mem_closedBall,dist_zero_right,← dist_eq_norm] using hz)
    obtain ⟨w,hw,hd⟩ := H a ha b hb v ⟨hv,hvW⟩
    apply mem_cthickening_iff.mpr
    exact (infEDist_le_edist_of_mem (mem_image_of_mem _ hw)).trans (by
      rw [edist_dist,dist_sub_right]
      exact ENNReal.ofReal_le_ofReal hd)
  exact ⟨htransport ha hb,by simpa only [dist_comm b a] using htransport hb ha⟩

/-- An arbitrarily larger translated inclusion constant realizes the
geometric Aubin estimate, so no global fiber closedness is needed. -/
theorem AubinRhoHatEstimate.aubinEstimate_of_lt (h : AubinRhoHatEstimate S X x u k)
    (hkl : k < l) : AubinEstimate S X x u l := by
  obtain ⟨r,hr,V,hV,H⟩ := h
  refine ⟨V,hV,ball u (r:ℝ),ball_mem_nhds _ (by exact_mod_cast hr),fun a ha b hb v hv ↦ ?_⟩
  rcases eq_or_ne a b with rfl | hab
  · exact ⟨v,hv.1,by simp⟩
  have hv' : v-u ∈ svTranslate S u a ∩ closedBall (0:F) (r:ℝ) :=
    ⟨mem_image_of_mem _ hv.1,by
      simpa only [mem_closedBall,dist_zero_right,← dist_eq_norm] using (show dist v u ≤ r from hv.2.le)⟩
  have hd := (rhoHatEDistance_le_iff r _ _).mp (H a ha b hb) |>.1 hv'
  rw [mem_cthickening_iff] at hd
  have hlt : ENNReal.ofReal ((k:ℝ)*dist a b) < ENNReal.ofReal ((l:ℝ)*dist a b) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg k.2 dist_nonneg)).mpr
      (mul_lt_mul_of_pos_right (show (k:ℝ) < l from hkl) (dist_pos.mpr hab))
  obtain ⟨z,⟨w,hw,rfl⟩,hzw⟩ := infEDist_lt_iff.mp (hd.trans_lt hlt)
  refine ⟨w,hw,?_⟩
  rw [edist_dist,dist_sub_right] at hzw
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp hzw).le

/-- **Exercise 9.37(a,d).** The distance-profile set distance characterizes
the Aubin property after translating the output point to zero. -/
theorem hasAubinPropertyWithinAt_iff_rhoEstimate (hx : x ∈ X) (hu : u ∈ S x)
    (hcl : IsLocallyClosedAt (svGraph S) (x,u)) :
    HasAubinPropertyWithinAt S X x u ↔ ∃ k, AubinRhoEstimate S X x u k := by
  rw [hasAubinPropertyWithinAt_iff_profile hx hu hcl]
  exact exists_congr fun _ ↦ aubinProfileEstimate_iff_rhoEstimate

/-- **Exercise 9.37(a,e).** The extended inclusion set distance characterizes
the Aubin property after translating the output point to zero. -/
theorem hasAubinPropertyWithinAt_iff_rhoHatEstimate (hx : x ∈ X) (hu : u ∈ S x)
    (hcl : IsLocallyClosedAt (svGraph S) (x,u)) :
    HasAubinPropertyWithinAt S X x u ↔ ∃ k, AubinRhoHatEstimate S X x u k := by
  constructor
  · rintro ⟨_,_,_,k,hk⟩
    exact ⟨k,hk.rhoHatEstimate⟩
  · rintro ⟨k,hk⟩
    exact ⟨hx,hu,hcl,k+1,hk.aubinEstimate_of_lt (lt_add_of_pos_right _ zero_lt_one)⟩

/-- The infimum of the translated inclusion constants is the graphical modulus. -/
theorem graphicalLipschitzModulusWithin_eq_iInf_rhoHat :
    graphicalLipschitzModulusWithin S X x u =
      ⨅ k : {k : ℝ≥0 // AubinRhoHatEstimate S X x u k}, ((k : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · refine le_iInf fun k ↦ ?_
    by_contra! h
    obtain ⟨l,hkl,hl⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    exact hl.not_ge (k.property.aubinEstimate_of_lt (ENNReal.coe_lt_coe.mp hkl) |>.modulus_le)
  · refine le_iInf fun k ↦ ?_
    exact iInf_le (fun a : {a : ℝ≥0 // AubinRhoHatEstimate S X x u a} ↦ ((a:ℝ≥0):ℝ≥0∞))
      ⟨k.val,k.property.rhoHatEstimate⟩

end RW
