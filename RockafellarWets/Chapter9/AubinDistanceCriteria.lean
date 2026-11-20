/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Distance profiles for the Aubin property
-/

import RockafellarWets.Chapter9.AubinProperty
import RockafellarWets.Chapter9.SetValuedModuli
import RockafellarWets.Chapter5.SemicontinuityCriteria

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

variable {E F : Type*} [MetricSpace E] [MetricSpace F]
  {S : E → Set F} {X : Set E} {x : E} {u : F} {k l : ℝ≥0}

/-- The nearby distance functions have a common Lipschitz constant. Fibers
are nonempty on the input neighborhood, so the real distance has its usual value. -/
def AubinProfileEstimate (S : E → Set F) (X : Set E) (x : E) (u : F) (k : ℝ≥0) : Prop :=
  ∃ V ∈ 𝓝 x, ∃ W ∈ 𝓝 u, (∀ a ∈ X ∩ V, (S a).Nonempty) ∧
    ∀ v ∈ W, LipschitzOnWith k (fun a ↦ infDist v (S a)) (X ∩ V)

/-- Every realized Aubin constant bounds the nearby distance profiles with
that same constant. Approximate nearest points suffice for nonclosed fibers. -/
theorem AubinEstimate.profileEstimate (h : AubinEstimate S X x u k) (hx : x ∈ X) (hu : u ∈ S x) :
    AubinProfileEstimate S X x u k := by
  obtain ⟨V,hV,W,hW,H⟩ := h
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp hW
  let d := r / (8*((k:ℝ)+1))
  have hd : 0 < d := by dsimp [d]; positivity
  let V' := V ∩ ball x d
  have hV' : V' ∈ 𝓝 x := inter_mem hV (ball_mem_nhds _ hd)
  have hxV : x ∈ X ∩ V := ⟨hx,mem_of_mem_nhds hV⟩
  have hsmall {a : E} (ha : a ∈ X ∩ V') : (k:ℝ)*dist x a < r/8 := by
    have hh : dist x a < d := by simpa only [dist_comm x a] using ha.2.2
    have hp := mul_lt_mul_of_pos_left hh (show 0 < (k:ℝ)+1 by positivity)
    have he : ((k:ℝ)+1)*d = r/8 := by dsimp [d]; field_simp
    rw [he] at hp
    nlinarith [dist_nonneg (x := x) (y := a)]
  have hnear {a : E} (ha : a ∈ X ∩ V') : ∃ w ∈ S a, dist u w < r/8 := by
    obtain ⟨w,hw,hwD⟩ := H x hxV a ⟨ha.1,ha.2.1⟩ u ⟨hu,mem_of_mem_nhds hW⟩
    exact ⟨w,hw,hwD.trans_lt (hsmall ha)⟩
  have hn {a : E} (ha : a ∈ X ∩ V') : (S a).Nonempty := by
    obtain ⟨w,hw,_⟩ := hnear ha
    exact ⟨w,hw⟩
  refine ⟨V',hV',ball u (r/8),ball_mem_nhds _ (by positivity),fun _ ha ↦ hn ha,fun v hv ↦ ?_⟩
  have hb {a b : E} (ha : a ∈ X ∩ V') (hb : b ∈ X ∩ V') :
      infDist v (S b) ≤ infDist v (S a) + (k:ℝ)*dist a b := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hv' : dist v u < r/8 := hv
    obtain ⟨w,hw,hwD⟩ := hnear ha
    have hinf : infDist v (S a) < r/4 :=
      (infDist_le_dist_of_mem hw).trans_lt ((dist_triangle v u w).trans_lt (by linarith))
    obtain ⟨p,hp,hpD⟩ := (infDist_lt_iff (hn ha)).mp
      (lt_add_of_pos_right _ (lt_min hε (by positivity : 0 < r/4)))
    have hpW : p ∈ W := hrW (show dist p u < r from (dist_triangle p v u).trans_lt (by
      rw [dist_comm p v]; linarith [min_le_right ε (r/4)]))
    obtain ⟨q,hq,hqD⟩ := H a ⟨ha.1,ha.2.1⟩ b ⟨hb.1,hb.2.1⟩ p ⟨hp,hpW⟩
    exact (infDist_le_dist_of_mem hq).trans ((dist_triangle v p q).trans (by linarith [min_le_left ε (r/4)]))
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb'
  rw [Real.dist_eq,abs_sub_le_iff]
  have hba := hb hb' ha
  rw [dist_comm b a] at hba
  exact ⟨by linarith,by linarith [hb ha hb']⟩

/-- An arbitrarily larger constant realizes the geometric inclusion associated
with a distance-profile estimate. Equality of the constants need not be attained. -/
theorem AubinProfileEstimate.aubinEstimate_of_lt (h : AubinProfileEstimate S X x u k) (hkl : k < l) :
    AubinEstimate S X x u l := by
  obtain ⟨V,hV,W,hW,hn,H⟩ := h
  refine ⟨V,hV,W,hW,fun a ha b hb v hv ↦ ?_⟩
  rcases eq_or_ne a b with rfl | hab
  · exact ⟨v,hv.1,by simp⟩
  have hD := (H v hv.2).dist_le_mul a ha b hb
  rw [infDist_zero_of_mem hv.1,dist_zero_left,Real.norm_eq_abs,abs_of_nonneg infDist_nonneg] at hD
  have hlt := hD.trans_lt (mul_lt_mul_of_pos_right (show (k:ℝ) < l from hkl) (dist_pos.mpr hab))
  obtain ⟨w,hw,hwD⟩ := (infDist_lt_iff (hn b hb)).mp hlt
  exact ⟨w,hw,hwD.le⟩

/-- **Exercise 9.37(a,c).** Uniform local Lipschitz continuity of the distance
profiles characterizes the Aubin property. -/
theorem hasAubinPropertyWithinAt_iff_profile (hx : x ∈ X) (hu : u ∈ S x)
    (hcl : IsLocallyClosedAt (svGraph S) (x,u)) :
    HasAubinPropertyWithinAt S X x u ↔ ∃ k, AubinProfileEstimate S X x u k := by
  constructor
  · rintro ⟨_,_,_,k,hk⟩
    exact ⟨k,hk.profileEstimate hx hu⟩
  · rintro ⟨k,hk⟩
    exact ⟨hx,hu,hcl,k+1,hk.aubinEstimate_of_lt (lt_add_of_pos_right _ zero_lt_one)⟩

/-- The infimum of the distance-profile constants is exactly the graphical
Lipschitz modulus, including when the infimum is zero or infinity. -/
theorem graphicalLipschitzModulusWithin_eq_iInf_profiles (hx : x ∈ X) (hu : u ∈ S x) :
    graphicalLipschitzModulusWithin S X x u =
      ⨅ k : {k : ℝ≥0 // AubinProfileEstimate S X x u k}, ((k : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · apply le_iInf
    intro k
    by_contra! h
    obtain ⟨l,hkl,hl⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    have hkl' : k.val < l := ENNReal.coe_lt_coe.mp hkl
    exact hl.not_ge (k.property.aubinEstimate_of_lt hkl' |>.modulus_le)
  · apply le_iInf
    intro k
    exact iInf_le (fun a : {a : ℝ≥0 // AubinProfileEstimate S X x u a} ↦ ((a:ℝ≥0):ℝ≥0∞))
      ⟨k.val,k.property.profileEstimate hx hu⟩

/-- Joint strict continuity follows from the uniform distance-profile bound.
The product metric gives the explicit constant `k + 1`. -/
theorem AubinProfileEstimate.strictlyContinuousWithinAt (h : AubinProfileEstimate S X x u k)
    (hx : x ∈ X) :
    StrictlyContinuousWithinAt (fun p : E × F ↦ infDist p.2 (S p.1)) (X ×ˢ univ) (x,u) := by
  obtain ⟨V,hV,W,hW,_,H⟩ := h
  refine strictlyContinuousWithinAt_iff.mpr ⟨⟨hx,mem_univ u⟩,k+1,(X ∩ V) ×ˢ W,?_,?_⟩
  · apply mem_nhdsWithin_prod_iff.mpr
    exact ⟨X ∩ V,inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV),
      W,by simpa only [nhdsWithin_univ] using hW,Subset.rfl⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    have h₁ := (H a.2 ha.2).dist_le_mul a.1 ha.1 b.1 hb.1
    have h₂ := (lipschitz_infDist_pt (S b.1)).dist_le_mul a.2 b.2
    calc
      _ ≤ dist (infDist a.2 (S a.1)) (infDist a.2 (S b.1)) +
          dist (infDist a.2 (S b.1)) (infDist b.2 (S b.1)) := dist_triangle _ _ _
      _ ≤ (k:ℝ)*dist a.1 b.1 + dist a.2 b.2 := by simpa using add_le_add h₁ h₂
      _ ≤ ((k+1:ℝ≥0):ℝ)*dist a b := by
        rw [Prod.dist_eq,NNReal.coe_add,NNReal.coe_one]
        calc
          _ ≤ (k:ℝ)*max (dist a.1 b.1) (dist a.2 b.2) + max (dist a.1 b.1) (dist a.2 b.2) :=
            add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) k.2) (le_max_right _ _)
          _ = _ := by ring

/-- **Exercise 9.37(b,c).** The uniform profile criterion is equivalent to
joint strict continuity when nearby fibers are nonempty. This hypothesis
keeps the real-valued `infDist` from assigning zero to empty fibers. -/
theorem exists_profile_iff_joint_strictContinuity
    (hx : x ∈ X) (hne : ∀ a ∈ X, (S a).Nonempty) :
    (∃ k, AubinProfileEstimate S X x u k) ↔
      StrictlyContinuousWithinAt (fun p : E × F ↦ infDist p.2 (S p.1)) (X ×ˢ univ) (x,u) := by
  constructor
  · rintro ⟨k,hk⟩
    exact hk.strictlyContinuousWithinAt hx
  · intro h
    obtain ⟨_,k,U,hU,H⟩ := strictlyContinuousWithinAt_iff.mp h
    obtain ⟨A,hA,W,hW,hsub⟩ := mem_nhdsWithin_prod_iff.mp hU
    obtain ⟨V,hV,hVA⟩ := eventually_nhdsWithin_iff_exists_nhds.mp hA
    refine ⟨k,V,hV,W,by simpa only [nhdsWithin_univ] using hW,
      fun a ha ↦ hne a ha.1,fun v hv ↦ LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_⟩
    simpa only [dist_prod_same_right] using
      H.dist_le_mul (a,v) (hsub ⟨hVA a ha,hv⟩) (b,v) (hsub ⟨hVA b hb,hv⟩)

end RW
