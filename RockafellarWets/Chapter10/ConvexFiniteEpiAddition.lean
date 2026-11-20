/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convex finite epi-addition
-/

import RockafellarWets.Chapter10.FiniteEpiSumSubgradients

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

set_option maxHeartbeats 1000000

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem convex_epigraph_separablePi {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hc : ∀ i, Convex ℝ (epigraph (f i))) :
    Convex ℝ (epigraph (separablePi f)) := by
  classical
  intro p hp' q hq' t s ht hs hts
  have hpx : separablePi f p.1 = ((separablePi f p.1).toReal:EReal) :=
    (EReal.coe_toReal ((hp'.trans_lt (EReal.coe_lt_top _)).ne) ((isProper_separablePi hp).2 _).ne').symm
  have hqx : separablePi f q.1 = ((separablePi f q.1).toReal:EReal) :=
    (EReal.coe_toReal ((hq'.trans_lt (EReal.coe_lt_top _)).ne) ((isProper_separablePi hp).2 _).ne').symm
  obtain ⟨a,ha⟩ := separablePi_finite_components hpx
  obtain ⟨b,hb⟩ := separablePi_finite_components hqx
  have hpa : ∑ i, a i ≤ p.2 := EReal.coe_le_coe_iff.mp ((separablePi_eq_coe ha) ▸ hp')
  have hqb : ∑ i, b i ≤ q.2 := EReal.coe_le_coe_iff.mp ((separablePi_eq_coe hb) ▸ hq')
  have hbound (i : ι) : f i (t • p.1 i+s • q.1 i) ≤ ((t*a i+s*b i:ℝ):EReal) :=
    hc i (show (p.1 i,a i) ∈ epigraph (f i) from (ha i).le)
      (show (q.1 i,b i) ∈ epigraph (f i) from (hb i).le) ht hs hts
  change (∑ i, f i ((t • p.1+s • q.1) i)) ≤ ((t*p.2+s*q.2:ℝ):EReal)
  calc
    _ ≤ ∑ i, ((t*a i+s*b i:ℝ):EReal) := Finset.sum_le_sum (fun i _ ↦ hbound i)
    _ = ((∑ i, (t*a i+s*b i) : ℝ):EReal) :=
      separablePi_eq_coe (f := fun i (_ : E) ↦ ((t*a i+s*b i:ℝ):EReal)) (x := p.1) (fun _ ↦ rfl)
    _ ≤ _ := by
      apply EReal.coe_le_coe_iff.mpr
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left hpa ht) (mul_le_mul_of_nonneg_left hqb hs)

theorem convex_epigraph_finiteEpiSumIntegrand {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hc : ∀ i, Convex ℝ (epigraph (f i))) :
    Convex ℝ (epigraph (finiteEpiSumIntegrand f)) := by
  classical
  intro p hp' q hq' t s ht hs hts
  obtain ⟨hpS,hpV⟩ := (finiteEpiSumIntegrand_le_iff hp p.1.fst p.1.snd p.2).mp hp'
  obtain ⟨hqS,hqV⟩ := (finiteEpiSumIntegrand_le_iff hp q.1.fst q.1.snd q.2).mp hq'
  apply (finiteEpiSumIntegrand_le_iff hp (t • p.1.fst+s • q.1.fst)
    (t • p.1.snd+s • q.1.snd) (t*p.2+s*q.2)).mpr
  constructor
  · simp only [PiLp.add_apply,PiLp.smul_apply,Finset.sum_add_distrib,← Finset.smul_sum,hpS,hqS]
  · exact convex_epigraph_separablePi hp hc
      (show (p.1.fst,p.2) ∈ epigraph (separablePi f) from hpV)
      (show (q.1.fst,q.2) ∈ epigraph (separablePi f) from hqV) ht hs hts

/-- **Exercise 10.18**, convexity is preserved by finite epi-addition. -/
theorem convex_epigraph_finiteEpiSumValue {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hc : ∀ i, Convex ℝ (epigraph (f i))) (hb : HasBoundedEpiSumDecompositions f) :
    Convex ℝ (epigraph (finiteEpiSumValue f)) :=
  convex_epigraph_parametricValue (convex_epigraph_finiteEpiSumIntegrand hp hc)
    (lowerSemicontinuous_finiteEpiSumIntegrand hp hf) (isParametricallyLevelBounded_finiteEpiSumIntegrand hp hb)

/-- **Exercise 10.18**, every optimal convex decomposition gives the same
intersection of limiting subdifferentials. -/
theorem subdifferential_finiteEpiSum_eq_at_decomposition {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hc : ∀ i, Convex ℝ (epigraph (f i))) (hb : HasBoundedEpiSumDecompositions f)
    {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) {a : PiLp 2 (fun _ : ι ↦ E)}
    (ha : a ∈ epiSumDecompositions f x) :
    subdifferential (finiteEpiSumValue f) x = {y | ∀ i, y ∈ subdifferential (f i) (a i)} := by
  have hmin : a ∈ parametricMinimizers (finiteEpiSumIntegrand f) x := by
    rwa [parametricMinimizers_finiteEpiSumIntegrand hp]
  have he := subdifferential_parametricValue_eq_at_minimizer (f := finiteEpiSumIntegrand f) (u := x) (x := a)
    (convex_epigraph_finiteEpiSumIntegrand hp hc) (lowerSemicontinuous_finiteEpiSumIntegrand hp hf)
    (isParametricallyLevelBounded_finiteEpiSumIntegrand hp hb) hx hmin
  obtain ⟨c,hcval⟩ := separablePi_finite_components (ha.2.1.trans hx)
  refine he.trans (Set.ext fun y ↦ ?_)
  exact subgradient_finiteEpiSumIntegrand_iff hp hf hcval ha.1

private theorem horizonSubgradient_finiteEpiSumIntegrand_of_convex
    {f : ι → E → EReal} (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hc : ∀ i, Convex ℝ (epigraph (f i)))
    {a : PiLp 2 (fun _ : ι ↦ E)} {x y : E} {c : ι → ℝ}
    (ha : ∀ i, f i (a i) = c i) (hs : (∑ i, a i) = x)
    (hy : ∀ i, y ∈ horizonSubdifferential (f i) (a i)) :
    WithLp.toLp 2 ((0 : PiLp 2 (fun _ : ι ↦ E)),y) ∈
      horizonSubdifferential (finiteEpiSumIntegrand f) (WithLp.toLp 2 (a,x)) := by
  have hconv := convex_epigraph_finiteEpiSumIntegrand hp hc
  have hproper := isProper_finiteEpiSumIntegrand hp
  have hl := lowerSemicontinuous_finiteEpiSumIntegrand hp hf
  have hval : finiteEpiSumIntegrand f (WithLp.toLp 2 (a,x)) = ((∑ i, c i : ℝ):EReal) := by
    rw [finiteEpiSumIntegrand_apply,hs,sub_self,indicatorVA_apply_mem (mem_singleton 0),add_zero]
    exact separablePi_eq_coe ha
  rw [horizonSubdifferential_eq_normalCone_domain_of_locallyLsc hconv hproper
    (locallyLscAt_of_lowerSemicontinuous_finite hl hval) hval,
    normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph hconv)
      (show WithLp.toLp 2 (a,x) ∈ effectiveDomain (finiteEpiSumIntegrand f) from hval.trans_lt (EReal.coe_lt_top _))]
  intro q hq
  have hqval : finiteEpiSumIntegrand f q = ((finiteEpiSumIntegrand f q).toReal:EReal) :=
    (EReal.coe_toReal hq.ne (hproper.2 q).ne').symm
  have hq' := (finiteEpiSumIntegrand_le_iff hp q.fst q.snd _).mp hqval.le
  have hsumval : separablePi f q.fst = ((separablePi f q.fst).toReal:EReal) :=
    (EReal.coe_toReal (hq'.2.trans_lt (EReal.coe_lt_top _)).ne ((isProper_separablePi hp).2 _).ne').symm
  obtain ⟨d,hd⟩ := separablePi_finite_components hsumval
  change ⟪(0 : PiLp 2 (fun _ : ι ↦ E)),q.fst-a⟫_ℝ+⟪y,q.snd-x⟫_ℝ ≤ 0
  rw [inner_zero_left,zero_add,← hq'.1,← hs,← Finset.sum_sub_distrib,inner_sum]
  apply Finset.sum_nonpos
  intro i _
  have hi := hy i
  rw [horizonSubdifferential_eq_normalCone_domain_of_locallyLsc (hc i) (hp i)
    (locallyLscAt_of_lowerSemicontinuous_finite (hf i) (ha i)) (ha i),
    normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph (hc i))
      (show a i ∈ effectiveDomain (f i) from (ha i).trans_lt (EReal.coe_lt_top _))] at hi
  exact hi (q.fst i) ((hd i).trans_lt (EReal.coe_lt_top _))

/-- **Exercise 10.18**, every convex optimal decomposition also gives the
same intersection of horizon subdifferentials. -/
theorem horizonSubdifferential_finiteEpiSum_eq_at_decomposition {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hc : ∀ i, Convex ℝ (epigraph (f i))) (hb : HasBoundedEpiSumDecompositions f)
    {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) {a : PiLp 2 (fun _ : ι ↦ E)}
    (ha : a ∈ epiSumDecompositions f x) :
    horizonSubdifferential (finiteEpiSumValue f) x =
      {y | ∀ i, y ∈ horizonSubdifferential (f i) (a i)} := by
  have hmin : a ∈ parametricMinimizers (finiteEpiSumIntegrand f) x := by
    rwa [parametricMinimizers_finiteEpiSumIntegrand hp]
  have he := horizonSubdifferential_parametricValue_eq_at_minimizer (f := finiteEpiSumIntegrand f) (u := x) (x := a)
    (convex_epigraph_finiteEpiSumIntegrand hp hc) (lowerSemicontinuous_finiteEpiSumIntegrand hp hf)
    (isProper_finiteEpiSumIntegrand hp) (isParametricallyLevelBounded_finiteEpiSumIntegrand hp hb) hx hmin
  obtain ⟨c,hcval⟩ := separablePi_finite_components (ha.2.1.trans hx)
  refine he.trans (Set.ext fun y ↦ ?_)
  exact ⟨horizonSubgradient_finiteEpiSumIntegrand hp hf hcval ha.1,
    horizonSubgradient_finiteEpiSumIntegrand_of_convex hp hf hc hcval ha.1⟩

theorem convex_finiteEpiSum_multiplier_equalities {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hc : ∀ i, Convex ℝ (epigraph (f i))) (hb : HasBoundedEpiSumDecompositions f)
    {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) :
    subdifferential (finiteEpiSumValue f) x = epiSumMultipliers f x ∧
    horizonSubdifferential (finiteEpiSumValue f) x = horizonEpiSumMultipliers f x := by
  refine ⟨Subset.antisymm (subdifferentials_finiteEpiSum_subset hp hf hb hx).2.1 ?_,
    Subset.antisymm (subdifferentials_finiteEpiSum_subset hp hf hb hx).2.2 ?_⟩
  · rintro y ⟨a,ha,hy⟩
    rwa [subdifferential_finiteEpiSum_eq_at_decomposition hp hf hc hb hx ha]
  · rintro y ⟨a,ha,hy⟩
    rwa [horizonSubdifferential_finiteEpiSum_eq_at_decomposition hp hf hc hb hx ha]

end

end RW
