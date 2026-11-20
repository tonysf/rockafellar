/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Opposite infinite slopes in the amenable sum rule

The closed quadratic perspective and a negative square root on independent
coordinates satisfy the domain-normal qualification in 10.26(a). Their sum
has slope `-∞` in a direction where inf-addition of the two slopes is `+∞`.
-/

import RockafellarWets.Chapter10.Amenability
import RockafellarWets.Chapter10.PLQCalculus
import RockafellarWets.Chapter10.SumDirectionalCounterexample

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

abbrev AmenableCounterPlane := WithLp 2 (ℝ × ℝ)
abbrev AmenableCounterSpace := WithLp 2 (AmenableCounterPlane × ℝ)

/-- The support representation of the closed quadratic perspective. -/
noncomputable def quadraticPerspective : AmenableCounterPlane → EReal :=
  supportFunction (range fun a : ℝ ↦ WithLp.toLp 2 (2*a,-a^2))

noncomputable def amenableCounterFirst (q : AmenableCounterSpace) : EReal :=
  quadraticPerspective q.fst

noncomputable def amenableCounterSecond (q : AmenableCounterSpace) : EReal :=
  negativeRoot q.snd

def amenableCounterDirection : AmenableCounterSpace :=
  WithLp.toLp 2 (WithLp.toLp 2 (1,0),1)

@[simp] theorem quadraticPerspective_zero : quadraticPerspective 0 = 0 :=
  supportFunction_zero (range_nonempty _)

@[simp] theorem amenableCounterFirst_zero : amenableCounterFirst 0 = 0 :=
  quadraticPerspective_zero

@[simp] theorem amenableCounterSecond_zero : amenableCounterSecond 0 = 0 :=
  negativeRoot_zero

/-- Both summands are closed proper convex functions, hence strongly amenable. -/
theorem amenableCounter_stronglyAmenable :
    StronglyAmenableAt amenableCounterFirst 0 ∧
      StronglyAmenableAt amenableCounterSecond 0 := by
  have hp : IsProper quadraticPerspective := isProper_supportFunction (range_nonempty _)
  have hc : Convex ℝ (epigraph quadraticPerspective) :=
    ((sublinear_iff_convex_isCone_epigraph_of_isProper hp).mp
      (sublinear_supportFunction _)).1
  constructor
  · apply stronglyAmenableAt_of_convex
    · exact ⟨⟨0,by simp⟩,fun q ↦ hp.2 q.fst⟩
    · exact (lowerSemicontinuous_supportFunction _).comp
        (WithLp.continuous_fst 2 _ _)
    · simpa only [map_zero,add_zero] using
        convex_epigraph_compAffine hc (WithLp.fstL 2 ℝ AmenableCounterPlane ℝ) 0
    · change amenableCounterFirst 0 < ⊤; simp
  · apply stronglyAmenableAt_of_convex
    · exact ⟨⟨0,by simp⟩,fun q ↦ negativeRoot_isProper.2 q.snd⟩
    · exact negativeRoot_lowerSemicontinuous.comp
        (WithLp.continuous_snd 2 _ _)
    · simpa only [map_zero,add_zero] using convex_epigraph_compAffine
        convex_epigraph_negativeRoot (WithLp.sndL 2 ℝ AmenableCounterPlane ℝ) 0
    · change amenableCounterSecond 0 < ⊤; simp

/-- Independent coordinates ensure the exact domain-normal qualification. -/
theorem amenableCounter_domain_normal_qualification
    {u v : AmenableCounterSpace}
    (hu : u ∈ normalCone (effectiveDomain amenableCounterFirst) 0)
    (hv : v ∈ normalCone (effectiveDomain amenableCounterSecond) 0)
    (he : u+v=0) : u=0 ∧ v=0 := by
  have hf : effectiveDomain amenableCounterFirst =
      l2ProdSet (effectiveDomain quadraticPerspective) univ := by ext q; simp [effectiveDomain,amenableCounterFirst,l2ProdSet]
  have hg : effectiveDomain amenableCounterSecond =
      l2ProdSet univ (effectiveDomain negativeRoot) := by ext q; simp [effectiveDomain,amenableCounterSecond,l2ProdSet]
  rw [hf,show (0:AmenableCounterSpace)=WithLp.toLp 2 (0,0) from rfl,
    normalCone_l2ProdSet,normalCone_univ] at hu
  rw [hg,show (0:AmenableCounterSpace)=WithLp.toLp 2 (0,0) from rfl,
    normalCone_l2ProdSet,normalCone_univ] at hv
  have hus : u.snd=0 := hu.2
  have hvf : v.fst=0 := hv.1
  have huf : u.fst=0 := by simpa [hvf] using congrArg (fun q : AmenableCounterSpace ↦ q.fst) he
  have hvs : v.snd=0 := by simpa [hus] using congrArg (fun q : AmenableCounterSpace ↦ q.snd) he
  exact ⟨WithLp.ofLp_injective 2 (Prod.ext huf hus),WithLp.ofLp_injective 2 (Prod.ext hvf hvs)⟩

private theorem amenableCounter_linear_minorant (a : ℝ) (q : AmenableCounterSpace) :
    (⟪WithLp.toLp 2 (WithLp.toLp 2 (2*a,-a^2),(0:ℝ)),q⟫_ℝ : EReal) ≤
      amenableCounterFirst q := by
  simpa only [WithLp.prod_inner_apply,inner_zero_left,add_zero,amenableCounterFirst,quadraticPerspective] using
    inner_le_supportFunction (D := range fun b : ℝ ↦ WithLp.toLp 2 (2*b,-b^2)) (mem_range_self a) q.fst

/-- The perspective contributes an infinite positive directional slope. -/
theorem amenableCounterFirst_subderivative :
    subderivative amenableCounterFirst 0 amenableCounterDirection = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro M
  let a : ℝ := (M+1)/2
  let v : AmenableCounterSpace := WithLp.toLp 2 (WithLp.toLp 2 (2*a,-a^2),0)
  have hv : v ∈ regularSubdifferential amenableCounterFirst 0 := by
    refine ⟨0,amenableCounterFirst_zero,fun ε hε ↦ Eventually.of_forall fun z ↦ ?_⟩
    simp only [sub_zero,zero_add]
    exact (EReal.coe_le_coe_iff.mpr (sub_le_self _ (mul_nonneg hε.le (norm_nonneg _)))).trans
      (amenableCounter_linear_minorant a z)
  have hb := inner_le_subderivative_of_mem_regularSubdifferential hv amenableCounterDirection
  have hi : ⟪v,amenableCounterDirection⟫_ℝ=M+1 := by
    simp only [v,amenableCounterDirection,WithLp.prod_inner_apply]
    change 1*(2*a)+0*(-a^2)+1*0=M+1
    dsimp [a]; ring
  rw [hi] at hb
  exact (EReal.coe_lt_coe_iff.mpr (by linarith : M<M+1)).trans_le hb

/-- The domain-restricted negative root has the same downward cusp slope. -/
theorem negativeRoot_hasSemiderivative_one : HasSemiderivative negativeRoot 0 1 ⊥ := by
  refine ⟨by simp,by simp,?_⟩
  have ht := positiveRoot_hasSemiderivative_one.2.2.neg
  apply ht.congr'
  filter_upwards [prod_mem_prod (self_mem_nhdsWithin : Ioi (0:ℝ) ∈ 𝓝[>] 0)
    (Ioi_mem_nhds (zero_lt_one : (0:ℝ)<1))] with p hp
  have hz : 0 ≤ 0+p.1 • p.2 := by simpa using (mul_pos hp.1 hp.2).le
  rw [differenceQuotient_eq_coe negativeRoot_zero (show negativeRoot (0+p.1 • p.2)=((-√(0+p.1 • p.2):ℝ):EReal) from if_pos hz),
    differenceQuotient_eq_coe positiveRoot_zero rfl]
  simp only [abs_of_nonneg hz,sub_zero,mul_neg,EReal.coe_neg]

/-- The independent square-root coordinate contributes the opposite infinity. -/
theorem amenableCounterSecond_subderivative :
    subderivative amenableCounterSecond 0 amenableCounterDirection = ⊥ := by
  let A := WithLp.sndL 2 ℝ AmenableCounterPlane ℝ
  have hs : Function.Surjective (fderiv ℝ A 0) := by
    rw [A.fderiv]
    exact fun y ↦ ⟨WithLp.toLp 2 (0,y),rfl⟩
  have he := subderivative_comp_eq_of_surjective A.contDiff negativeRoot_zero hs amenableCounterDirection
  rw [A.fderiv] at he
  exact he.trans negativeRoot_hasSemiderivative_one.subderivative_eq

/-- A finite upper estimate on the curved path used below. -/
theorem quadraticPerspective_curved_path_le {s : ℝ} (hs : 0 < s) :
    quadraticPerspective (WithLp.toLp 2 (s^4,s^5)) ≤ ((s^3:ℝ):EReal) := by
  apply (supportFunction_le_iff _ _ _).mpr
  rintro _ ⟨a,rfl⟩
  rw [WithLp.prod_inner_apply,EReal.coe_le_coe_iff]
  change s^4*(2*a)+s^5*(-a^2) ≤ s^3
  nlinarith [mul_nonneg (pow_nonneg hs.le 3) (sq_nonneg (a*s-1))]

/-- Along a curved approach to the horizontal perspective direction, the
negative square root dominates the perspective cost. -/
theorem amenableCounter_sum_subderivative :
    subderivative (amenableCounterFirst+amenableCounterSecond) 0 amenableCounterDirection = ⊥ := by
  let s (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  let t (n : ℕ) : ℝ := (s n)^4
  let w (n : ℕ) : AmenableCounterSpace := WithLp.toLp 2 (WithLp.toLp 2 (1,s n),1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have ht (n : ℕ) : 0 < t n := pow_pos (hs n) 4
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht0 : Tendsto t atTop (𝓝 0) := by simpa only [zero_pow (by decide : 4≠0)] using hs0.pow 4
  have hw : Tendsto w atTop (𝓝 amenableCounterDirection) := by
    have h1 : Tendsto (fun n ↦ WithLp.toLp 2 ((1:ℝ),s n)) atTop
        (𝓝 (WithLp.toLp 2 ((1:ℝ),0))) :=
      (WithLp.prod_continuous_toLp 2 ℝ ℝ).continuousAt.tendsto.comp
        (tendsto_const_nhds.prodMk_nhds hs0)
    exact (WithLp.prod_continuous_toLp 2 AmenableCounterPlane ℝ).continuousAt.tendsto.comp
      (h1.prodMk_nhds tendsto_const_nhds)
  have htwithin : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht0,Eventually.of_forall ht⟩
  have hpair := htwithin.prodMk hw
  have h0 : (amenableCounterFirst+amenableCounterSecond) 0 = ((0:ℝ):EReal) := by simp
  have hbound (n : ℕ) : differenceQuotient (amenableCounterFirst+amenableCounterSecond)
      0 (t n) (w n) ≤ ((-(n:ℝ):ℝ):EReal) := by
    apply (differenceQuotient_le_coe_iff h0 (ht n)).mpr
    have hp := quadraticPerspective_curved_path_le (hs n)
    have hg : negativeRoot ((s n)^4) = ((-(s n)^2:ℝ):EReal) := by
      rw [negativeRoot,if_pos (by positivity),show (s n)^4=((s n)^2)^2 by ring,
        Real.sqrt_sq (sq_nonneg (s n))]
    have hfst : (0+t n • w n).fst = WithLp.toLp 2 ((s n)^4,(s n)^5) := by
      apply WithLp.ofLp_injective 2
      apply Prod.ext <;> change _ = _ <;> dsimp [t,w] <;> simp only [zero_add,mul_one] <;> ring
    have hsnd : (0+t n • w n).snd = (s n)^4 := by change 0+t n*1=(s n)^4; simp [t]
    change quadraticPerspective (0+t n • w n).fst+negativeRoot (0+t n • w n).snd ≤ _
    rw [hfst,hsnd,hg]
    apply (add_le_add hp (le_refl (((-(s n)^2:ℝ):EReal)))).trans
    rw [← EReal.coe_add,EReal.coe_le_coe_iff,zero_add]
    have he : (s n)^3+(-(s n)^2) = (s n)^4*(((n:ℝ)+1)-((n:ℝ)+1)^2) := by
      dsimp [s]
      field_simp
      <;> ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (ht n))
    nlinarith [show (0:ℝ)≤n from Nat.cast_nonneg n]
  have hn : Tendsto (fun n : ℕ ↦ ((-(n:ℝ):ℝ):EReal)) atTop (𝓝 (⊥:EReal)) := by
    simpa only [EReal.coe_neg,EReal.neg_top] using
      (EReal.tendsto_coe_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).neg
  apply le_bot_iff.mp
  calc
    subderivative (amenableCounterFirst+amenableCounterSecond) 0 amenableCounterDirection
        ≤ liminf (fun n ↦ differenceQuotient (amenableCounterFirst+amenableCounterSecond) 0 (t n) (w n)) atTop := by
      unfold subderivative
      change _ ≤ liminf ((fun p : ℝ × AmenableCounterSpace ↦
        differenceQuotient (amenableCounterFirst+amenableCounterSecond) 0 p.1 p.2) ∘ fun n ↦ (t n,w n)) atTop
      rw [liminf_comp]
      exact liminf_le_liminf_of_le hpair
    _ ≤ liminf (fun n : ℕ ↦ ((-(n:ℝ):ℝ):EReal)) atTop := liminf_le_liminf (Eventually.of_forall hbound)
    _ = ⊥ := hn.liminf_eq

/-- **Counterexample to the unrestricted derivative equality in 10.26(a).**
The two functions are strongly amenable and satisfy the printed qualification.
Inf-addition of their opposite infinite slopes is not the slope of their sum. -/
theorem stronglyAmenable_sum_infAddition_counterexample :
    StronglyAmenableAt amenableCounterFirst 0 ∧ StronglyAmenableAt amenableCounterSecond 0 ∧
    amenableCounterFirst 0 = 0 ∧ amenableCounterSecond 0 = 0 ∧
    (∀ u ∈ normalCone (effectiveDomain amenableCounterFirst) 0,
      ∀ v ∈ normalCone (effectiveDomain amenableCounterSecond) 0, u+v=0 → u=0 ∧ v=0) ∧
    subderivative amenableCounterFirst 0 amenableCounterDirection = ⊤ ∧
    subderivative amenableCounterSecond 0 amenableCounterDirection = ⊥ ∧
    subderivative (amenableCounterFirst+amenableCounterSecond) 0 amenableCounterDirection = ⊥ ∧
    subderivative (amenableCounterFirst+amenableCounterSecond) 0 amenableCounterDirection ≠
      infAddition (subderivative amenableCounterFirst 0 amenableCounterDirection)
        (subderivative amenableCounterSecond 0 amenableCounterDirection) := by
  refine ⟨amenableCounter_stronglyAmenable.1,amenableCounter_stronglyAmenable.2,
    amenableCounterFirst_zero,amenableCounterSecond_zero,
    fun _ hu _ hv he ↦ amenableCounter_domain_normal_qualification hu hv he,
    amenableCounterFirst_subderivative,amenableCounterSecond_subderivative,
    amenableCounter_sum_subderivative,?_⟩
  rw [amenableCounterFirst_subderivative,amenableCounterSecond_subderivative,
    amenableCounter_sum_subderivative]
  simp [infAddition]

end RW
