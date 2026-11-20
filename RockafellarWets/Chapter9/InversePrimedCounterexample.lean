/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A closed-graph counterexample to the unrestricted primed converse in 9.46

The discrete counterexample from Definition 9.27 is first restricted to its
closed discrete domain, then transported to the Euclidean plane and inverted.
It satisfies the outer-semicontinuity and range hypotheses of Proposition
9.46, as well as both primed geometric estimates, but its inverse fails the
distance-profile definition of sub-Lipschitz continuity.
-/

import RockafellarWets.Chapter9.BoundedInverseEstimates
import RockafellarWets.Chapter9.SubLipschitzTransportCounterexample
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

noncomputable section

private def discreteCounterGraphPoint (q : ℕ × Bool) : (ℝ × ℝ) × ℝ :=
  (transportCounterPoint q.1 q.2,transportCounterValue (transportCounterPoint q.1 q.2))

/-- The restricted graph is closed: a convergent sequence has an eventually
constant natural-number first coordinate, leaving only two possible points. -/
theorem isClosed_restrictedTransportCounterGraph :
    IsClosed (svGraph (svRestrict transportCounterMap transportCounterDomain)) := by
  classical
  have heq : svGraph (svRestrict transportCounterMap transportCounterDomain) =
      range discreteCounterGraphPoint := by
    ext q
    constructor
    · rintro ⟨hv,⟨j,hj⟩⟩
      refine ⟨j,Prod.ext hj ?_⟩
      exact (congrArg transportCounterValue hj).trans hv.symm
    · rintro ⟨j,rfl⟩
      exact ⟨rfl,⟨j,rfl⟩⟩
  rw [heq]
  apply IsSeqClosed.isClosed
  intro z q hz ht
  choose j hj using hz
  have hn : Tendsto (fun n ↦ ((j n).1:ℝ)) atTop (nhds q.1.1) := by
    have he (n : ℕ) : (z n).1.1 = ((j n).1:ℝ) := by rw [← hj n]; rfl
    simpa only [he] using ht.fst_nhds.fst_nhds
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hn.cauchySeq 1 one_pos
  have hindex (n : ℕ) (hn : N ≤ n) : (j n).1 = (j N).1 := by
    by_contra hne
    have hne' : ((j n).1:ℤ) ≠ ((j N).1:ℤ) := by exact_mod_cast hne
    have hsep := Int.pairwise_one_le_dist hne'
    have hsep' : 1 ≤ dist ((j n).1:ℝ) ((j N).1:ℝ) := by
      simpa only [Int.dist_eq,Int.cast_natCast,Real.dist_eq] using hsep
    exact (hN n hn).not_ge hsep'
  let K := range (fun b : Bool ↦ discreteCounterGraphPoint ((j N).1,b))
  have hK : IsClosed K := (finite_range _).isClosed
  have hseq : ∀ᶠ n in atTop, z n ∈ K := by
    filter_upwards [eventually_ge_atTop N] with n hn
    refine ⟨(j n).2,?_⟩
    rw [← hj n]
    exact congrArg discreteCounterGraphPoint (Prod.ext (hindex n hn).symm rfl)
  obtain ⟨b,hb⟩ := hK.mem_of_tendsto ht hseq
  exact ⟨((j N).1,b),hb⟩

/-- The discrete parameter set, now in the genuine Euclidean plane. -/
def inversePrimedCounterDomain : Set (WithLp 2 (ℝ × ℝ)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ) ⁻¹' transportCounterDomain

private def euclideanTransportCounterMap (u : WithLp 2 (ℝ × ℝ)) : Set ℝ :=
  transportCounterMap ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ) u)

/-- The outer-semicontinuous mapping whose inverse violates 9.46(a'). -/
def inversePrimedCounterMap : ℝ → Set (WithLp 2 (ℝ × ℝ)) :=
  svInv (svRestrict euclideanTransportCounterMap inversePrimedCounterDomain)

private theorem inversePrimed_fiber {u : WithLp 2 (ℝ × ℝ)} (hu : u ∈ inversePrimedCounterDomain) :
    svInv inversePrimedCounterMap u = transportCounterMap ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ) u) :=
  svRestrict_apply hu

/-- This example satisfies the actual closed-graph hypothesis in 9.46. -/
theorem svOsc_inversePrimedCounterMap : SvOsc inversePrimedCounterMap := by
  apply svOsc_svInv_iff.mpr
  apply isClosed_svGraph_iff_svOsc.mp
  have heq : svGraph (svRestrict euclideanTransportCounterMap inversePrimedCounterDomain) =
      (fun q : WithLp 2 (ℝ × ℝ) × ℝ ↦ ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ) q.1,q.2)) ⁻¹'
        svGraph (svRestrict transportCounterMap transportCounterDomain) := rfl
  rw [heq]
  exact isClosed_restrictedTransportCounterGraph.preimage
    (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).continuous.comp continuous_fst).prodMk continuous_snd)

theorem range_inversePrimedCounterMap : svRange inversePrimedCounterMap = inversePrimedCounterDomain := by
  ext u
  change (∃ x : ℝ, x ∈ euclideanTransportCounterMap u ∧ u ∈ inversePrimedCounterDomain) ↔ _
  exact ⟨fun ⟨_,_,hu⟩ ↦ hu,fun hu ↦ ⟨transportCounterValue ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ) u),rfl,hu⟩⟩

/-- All bounded-region metric estimates in 9.46(b') hold. -/
theorem inversePrimedCounterMap_boundedMetric :
    BoundedInverseMetricEstimate inversePrimedCounterMap inversePrimedCounterDomain := by
  intro ρ
  obtain ⟨k,hk⟩ := transportCounterMap_has_all_transport ρ
  let L := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toContinuousLinearMap
  let K : ℝ≥0 := k*‖L‖₊+1
  have ht : InverseTransportEstimate inversePrimedCounterMap inversePrimedCounterDomain
      inversePrimedCounterDomain (closedBall 0 (ρ:ℝ)) K := by
    intro a ha b hb x hx hax
    have hv : x ∈ transportCounterMap (L a) := hax.1
    obtain ⟨y,hy,hd⟩ := hk (L a) ha (L b) hb x ⟨hv,hx⟩
    refine ⟨y,⟨hy,hb⟩,?_⟩
    have hdist := L.lipschitz.dist_le_mul a b
    calc
      dist x y ≤ (k:ℝ)*dist (L a) (L b) := hd
      _ ≤ (k:ℝ)*(‖L‖*dist a b) := mul_le_mul_of_nonneg_left hdist k.2
      _ ≤ (K:ℝ)*dist a b := by dsimp [K]; nlinarith [dist_nonneg (x := a) (y := b)]
  exact ⟨K,ht.metricEstimate (by dsimp [K]; positivity)⟩

/-- Consequently all bounded-region openness estimates in 9.46(c') hold. -/
theorem inversePrimedCounterMap_boundedOpen :
    BoundedInverseOpenEstimate inversePrimedCounterMap inversePrimedCounterDomain :=
  boundedInverseMetricEstimate_iff_open.mp inversePrimedCounterMap_boundedMetric

/-- The inverse still fails the distance-profile definition of 9.46(a'). -/
theorem inversePrimedCounterMap_not_subLipschitz :
    ¬ SvSubLipschitzOn (svInv inversePrimedCounterMap) inversePrimedCounterDomain := by
  intro h
  apply transportCounterMap_not_subLipschitz
  refine ⟨fun a _ ↦ ⟨singleton_nonempty _,isClosed_singleton⟩,fun ρ ↦ ?_⟩
  obtain ⟨k,hk⟩ := h.2 ρ
  let J := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap
  have hmem {a : ℝ × ℝ} (ha : a ∈ transportCounterDomain) : J a ∈ inversePrimedCounterDomain := by
    change (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ) ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm a) ∈ transportCounterDomain
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  have hfib {a : ℝ × ℝ} (ha : a ∈ transportCounterDomain) :
      svInv inversePrimedCounterMap (J a) = transportCounterMap a := by
    rw [inversePrimed_fiber (hmem ha)]
    change transportCounterMap ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ) ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm a)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨k*‖J‖₊,svRhoLipschitzOnWith_iff_rhoDistance.mpr (fun a ha b hb ↦ ?_)⟩
  have hh := (svRhoLipschitzOnWith_iff_rhoDistance.mp hk) (J a) (hmem ha) (J b) (hmem hb)
  rw [hfib ha,hfib hb] at hh
  have hdist := J.lipschitz.dist_le_mul a b
  calc
    _ ≤ (k:ℝ)*dist (J a) (J b) := hh
    _ ≤ (k:ℝ)*(‖J‖*dist a b) := mul_le_mul_of_nonneg_left hdist k.2
    _ = ↑(k*‖J‖₊)*dist a b := by simp only [NNReal.coe_mul,coe_nnnorm,mul_assoc]

/-- A counterexample to the unrestricted primed equivalence, with all the
printed outer-semicontinuity and range hypotheses, in Euclidean spaces. -/
theorem inverse_primed_converse_closedGraph_counterexample :
    SvOsc inversePrimedCounterMap ∧
      inversePrimedCounterDomain = svRange inversePrimedCounterMap ∧
      BoundedInverseMetricEstimate inversePrimedCounterMap inversePrimedCounterDomain ∧
      BoundedInverseOpenEstimate inversePrimedCounterMap inversePrimedCounterDomain ∧
      ¬ SvSubLipschitzOn (svInv inversePrimedCounterMap) inversePrimedCounterDomain :=
  ⟨svOsc_inversePrimedCounterMap,range_inversePrimedCounterMap.symm,
    inversePrimedCounterMap_boundedMetric,inversePrimedCounterMap_boundedOpen,
    inversePrimedCounterMap_not_subLipschitz⟩

end

end RW
