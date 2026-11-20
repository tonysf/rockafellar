/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semiderivatives of inner compositions
-/

import RockafellarWets.Chapter10.InnerCompositionRegularity
import RockafellarWets.Chapter10.SemiderivativeCalculus

open Filter Metric Set Topology
open scoped NNReal

namespace RW

theorem mem_outerSetLimitAlong_of_eventually_mem {I V : Type*} [TopologicalSpace V]
    {l : Filter I} {C : I → Set V} {a : ℕ → I} {b : ℕ → V} {v : V}
    (ha : Tendsto a atTop l) (hb : Tendsto b atTop (𝓝 v))
    (hm : ∀ᶠ n in atTop, b n ∈ C (a n)) : v ∈ outerSetLimitAlong l C := by
  intro U hU
  rw [frequently_iff]
  intro A hA
  obtain ⟨n,hn,hmn,hUn⟩ := ((ha.eventually hA).and (hm.and (hb.eventually hU))).exists
  exact ⟨a n,hn,b n,hmn,hUn⟩

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {S : F → Set G} {f : E → F} {x w : E} {u : G} {z : F}

theorem mappingDifferenceQuotient_inner_comp (S : F → Set G) (f : E → F)
    (x : E) (u : G) (t : ℝ) (w : E) :
    mappingDifferenceQuotient (fun a ↦ S (f a)) x u t w =
      mappingDifferenceQuotient S (f x) u t (t⁻¹ • (f (x+t • w)-f x)) := by
  by_cases ht : t = 0
  · simp only [ht,mappingDifferenceQuotient,zero_smul,add_zero,inv_zero]
  · simp only [mappingDifferenceQuotient,smul_smul,mul_inv_cancel₀ ht,one_smul,add_sub_cancel]

/-- The easy graphical derivative inclusion needs only the indicated
directional semiderivative, and no regularity of the outer mapping. -/
theorem graphicalDerivative_inner_comp_subset
    (hf : HasDirectionalSemiderivative f x w z) :
    graphicalDerivative (fun a ↦ S (f a)) x u w ⊆ graphicalDerivative S (f x) u z := by
  intro v hv
  change (w,v) ∈ svGraph (graphicalDerivative (fun a ↦ S (f a)) x u) at hv
  rw [svGraph_graphicalDerivative_eq_outerLimit,mem_outerSetLimitAlong_iff_exists_seq] at hv
  obtain ⟨t,q,ht,hq,hqv⟩ := hv
  change (z,v) ∈ svGraph (graphicalDerivative S (f x) u)
  rw [svGraph_graphicalDerivative_eq_outerLimit]
  have hfq := Filter.Tendsto.comp hf (ht.prodMk hqv.fst_nhds)
  apply mem_outerSetLimitAlong_of_eventually_mem ht (hfq.prodMk_nhds hqv.snd_nhds)
  apply Eventually.of_forall
  intro n
  change (q n).2 ∈ mappingDifferenceQuotient S (f x) u (t n) ((t n)⁻¹ • (f (x+t n • (q n).1)-f x))
  rw [← mappingDifferenceQuotient_inner_comp]
  exact hq n

/-- The Aubin property supplies the reverse inclusion, proving the
directional chain identity in 10.40. -/
theorem graphicalDerivative_inner_comp_eq [ProperSpace G]
    (hf : HasDirectionalSemiderivative f x w z) (ha : HasAubinPropertyAt S (f x) u) :
    graphicalDerivative (fun a ↦ S (f a)) x u w = graphicalDerivative S (f x) u z := by
  apply Subset.antisymm (graphicalDerivative_inner_comp_subset hf)
  intro v hv
  obtain ⟨k,hk⟩ := ha.2.2.2
  rw [hk.graphicalDerivative_eq_outer_fixed z,mem_outerSetLimitAlong_iff_exists_seq] at hv
  obtain ⟨t,q,ht,hq,hqv⟩ := hv
  let r (n : ℕ) := (t n)⁻¹ • (f (x+t n • w)-f x)
  have hr : Tendsto r atTop (𝓝 z) := Filter.Tendsto.comp hf (ht.prodMk tendsto_const_nhds)
  have H := hk.eventually_transport_quotients ht (tendsto_const_nhds (x := z)) hr hqv (.of_forall hq)
  obtain ⟨N,hN⟩ := eventually_atTop.mp H
  let φ (n : ℕ) := n+N
  have hφ : Tendsto φ atTop atTop := tendsto_add_atTop_nat N
  choose b hb hd using fun n ↦ hN (φ n) (by dsimp [φ]; omega)
  have hbv : Tendsto b atTop (𝓝 v) := (hqv.comp hφ).congr_dist
    (squeeze_zero (fun _ ↦ dist_nonneg) hd (by
      simpa using ((tendsto_const_nhds (x := z)).dist (hr.comp hφ)).const_mul (k:ℝ)))
  change (w,v) ∈ svGraph (graphicalDerivative (fun a ↦ S (f a)) x u)
  rw [svGraph_graphicalDerivative_eq_outerLimit]
  apply mem_outerSetLimitAlong_of_eventually_mem (ht.comp hφ) (tendsto_const_nhds.prodMk_nhds hbv)
  apply Eventually.of_forall
  intro n
  change b n ∈ mappingDifferenceQuotient (fun a ↦ S (f a)) x u (t (φ n)) w
  rw [mappingDifferenceQuotient_inner_comp]
  exact hb n

/-- Full set-valued semidifferentiability under a semidifferentiable inner
map, the remaining semidifferentiability assertion of 10.40. -/
theorem HasMappingSemiderivative.inner_comp {A : E → F} {H : F → Set G}
    (hs : HasMappingSemiderivative S (f x) u H)
    (hf : ∀ w, HasDirectionalSemiderivative f x w (A w)) :
    HasMappingSemiderivative (fun a ↦ S (f a)) x u (fun w ↦ H (A w)) := by
  intro w
  apply pkConvergesAlong_iff_forall_seq.mpr
  intro p hp
  have hq := Filter.Tendsto.comp (hf w) hp
  have hs' := (pkConvergesAlong_iff_forall_seq.mp (hs (A w)))
    (fun n ↦ ((p n).1,(p n).1⁻¹ • (f (x+(p n).1 • (p n).2)-f x)))
    (hp.fst.prodMk hq)
  convert hs' using 1
  funext n
  exact mappingDifferenceQuotient_inner_comp S f x u (p n).1 (p n).2

end RW
