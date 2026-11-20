/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Graphical derivatives under single-valued addition
-/

import RockafellarWets.Chapter10.InnerCompositionSemiderivatives
import RockafellarWets.Chapter9.StrictGraphicalDerivatives
import RockafellarWets.Chapter6.RegularTangentChangeOfCoordinates

open Filter Metric Set Topology
open scoped Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {S : E → Set F} {f : E → F} {x w : E} {u z : F}

theorem mem_svAdd_single {a : E} {v : F} :
    v ∈ svAdd S (svSingleton f) a ↔ v-f a ∈ S a := by
  change v ∈ S a+{f a} ↔ _
  constructor
  · rintro ⟨b,hb,c,hc,hbc⟩
    have hc' : c = f a := hc
    rw [← hbc,hc',add_sub_cancel_right]
    exact hb
  · intro h
    exact ⟨v-f a,h,f a,rfl,sub_add_cancel _ _⟩

theorem mappingDifferenceQuotient_svAdd_single (S : E → Set F) (f : E → F)
    (x : E) (u : F) (t : ℝ) (w : E) :
    mappingDifferenceQuotient (svAdd S (svSingleton f)) x (u+f x) t w =
      (fun q ↦ q+t⁻¹ • (f (x+t • w)-f x)) '' mappingDifferenceQuotient S x u t w := by
  ext v
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨t⁻¹ • ((a-f (x+t • w))-u),⟨a-f (x+t • w),mem_svAdd_single.mp ha,rfl⟩,?_⟩
    dsimp only
    rw [← smul_add]
    congr 1
    abel
  · rintro ⟨q,⟨a,ha,rfl⟩,rfl⟩
    refine ⟨a+f (x+t • w),mem_svAdd_single.mpr (by simpa only [add_sub_cancel_right] using ha),?_⟩
    dsimp only
    rw [← smul_add]
    congr 1
    abel

theorem mem_mappingDifferenceQuotient_svAdd_single {t : ℝ} {v : F} :
    v ∈ mappingDifferenceQuotient (svAdd S (svSingleton f)) x (u+f x) t w ↔
      v-t⁻¹ • (f (x+t • w)-f x) ∈ mappingDifferenceQuotient S x u t w := by
  rw [mappingDifferenceQuotient_svAdd_single]
  constructor
  · rintro ⟨q,hq,rfl⟩
    simpa only [add_sub_cancel_right] using hq
  · intro h
    exact ⟨_,h,sub_add_cancel _ _⟩

/-- **Exercise 10.43(a)**. The rule holds without closedness or any
regularity assumption on the set-valued summand. -/
theorem graphicalDerivative_svAdd_single (hf : HasDirectionalSemiderivative f x w z) :
    graphicalDerivative (svAdd S (svSingleton f)) x (u+f x) w =
      (fun v ↦ v+z) '' graphicalDerivative S x u w := by
  ext v
  constructor
  · intro hv
    change (w,v) ∈ svGraph (graphicalDerivative (svAdd S (svSingleton f)) x (u+f x)) at hv
    rw [svGraph_graphicalDerivative_eq_outerLimit,mem_outerSetLimitAlong_iff_exists_seq] at hv
    obtain ⟨t,q,ht,hq,hqv⟩ := hv
    have hr := Filter.Tendsto.comp hf (ht.prodMk hqv.fst_nhds)
    refine ⟨v-z,?_,sub_add_cancel _ _⟩
    change (w,v-z) ∈ svGraph (graphicalDerivative S x u)
    rw [svGraph_graphicalDerivative_eq_outerLimit]
    apply mem_outerSetLimitAlong_of_eventually_mem ht
      (hqv.fst_nhds.prodMk_nhds (hqv.snd_nhds.sub hr))
    exact Eventually.of_forall fun n ↦ mem_mappingDifferenceQuotient_svAdd_single.mp (hq n)
  · rintro ⟨v,hv,rfl⟩
    change (w,v) ∈ svGraph (graphicalDerivative S x u) at hv
    rw [svGraph_graphicalDerivative_eq_outerLimit,mem_outerSetLimitAlong_iff_exists_seq] at hv
    obtain ⟨t,q,ht,hq,hqv⟩ := hv
    have hr := Filter.Tendsto.comp hf (ht.prodMk hqv.fst_nhds)
    change (w,v+z) ∈ svGraph (graphicalDerivative (svAdd S (svSingleton f)) x (u+f x))
    rw [svGraph_graphicalDerivative_eq_outerLimit]
    apply mem_outerSetLimitAlong_of_eventually_mem ht
      (hqv.fst_nhds.prodMk_nhds (hqv.snd_nhds.add hr))
    apply Eventually.of_forall
    intro n
    apply mem_mappingDifferenceQuotient_svAdd_single.mpr
    simpa only [Function.comp_def,add_sub_cancel_right] using hq n

/-- Strict derivatives transport moving-base quotient errors. -/
theorem HasStrictFDerivAt.tendsto_moving_quotient {A : E →L[ℝ] F}
    (hf : HasStrictFDerivAt f A x) {t : ℕ → ℝ} {a v : ℕ → E}
    (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 x)) (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n ↦ (t n)⁻¹ • (f (a n+t n • v n)-f (a n))) atTop (𝓝 (A w)) := by
  have hend : Tendsto (fun n ↦ a n+t n • v n) atTop (𝓝 x) := by simpa using ha.add (ht0.smul hv)
  apply RW.HasStrictFDerivAt.tendsto_scaled_sub hf hend ha
  simpa only [add_sub_cancel_left,inv_smul_smul₀ (ht _).ne'] using hv

/-- **Exercise 10.43(b)**, the strict graphical derivative formula. -/
theorem strictGraphicalDerivative_svAdd_single {A : E →L[ℝ] F} (hf : HasStrictFDerivAt f A x) :
    strictGraphicalDerivative (svAdd S (svSingleton f)) x (u+f x) w =
      (fun v ↦ v+A w) '' strictGraphicalDerivative S x u w := by
  ext z
  constructor
  · intro hz
    obtain ⟨t,a,b,v,q,ht,ht0,hab,ha,hb,hv,hq,hm⟩ := mem_strictGraphicalDerivative_iff_sequences.mp hz
    have hr := RW.HasStrictFDerivAt.tendsto_moving_quotient hf ht ht0 ha hv
    refine ⟨z-A w,mem_strictGraphicalDerivative_iff_sequences.mpr ?_,sub_add_cancel _ _⟩
    refine ⟨t,a,fun n ↦ b n-f (a n),v,
      fun n ↦ q n-(t n)⁻¹ • (f (a n+t n • v n)-f (a n)),ht,ht0,
      fun n ↦ mem_svAdd_single.mp (hab n),ha,?_,hv,hq.sub hr,?_⟩
    · simpa only [add_sub_cancel_right] using hb.sub (hf.continuousAt.tendsto.comp ha)
    · intro n
      apply mem_mappingDifferenceQuotient_svAdd_single.mp
      simpa only [sub_add_cancel] using hm n
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨t,a,b,v,q,ht,ht0,hab,ha,hb,hv,hq,hm⟩ := mem_strictGraphicalDerivative_iff_sequences.mp hz
    have hr := RW.HasStrictFDerivAt.tendsto_moving_quotient hf ht ht0 ha hv
    apply mem_strictGraphicalDerivative_iff_sequences.mpr
    refine ⟨t,a,fun n ↦ b n+f (a n),v,
      fun n ↦ q n+(t n)⁻¹ • (f (a n+t n • v n)-f (a n)),ht,ht0,
      fun n ↦ mem_svAdd_single.mpr (by simpa only [add_sub_cancel_right] using hab n),ha,
      hb.add (hf.continuousAt.tendsto.comp ha),hv,hq.add hr,?_⟩
    intro n
    apply mem_mappingDifferenceQuotient_svAdd_single.mpr
    simpa only [add_sub_cancel_right] using hm n

end RW
