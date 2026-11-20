/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The neighborhood in the upper-C¹ conclusion of 10.58

A second minimizer can appear outside the decision neighborhood where
smoothness is assumed. The proof of 10.58 shrinks the parameter neighborhood
before forming the common compact family. This example shows why.
-/
import RockafellarWets.Chapter10.ParametricEpigraphProjection
import RockafellarWets.Chapter10.SubsmoothFunctions

open Bornology Filter Metric Set Topology

namespace RW
noncomputable section

private abbrev Plane := WithLp 2 (ℝ × ℝ)
private def exceptionalPoint : Plane := WithLp.toLp 2 ((1:ℝ),(1:ℝ))
private def cost (q : Plane) : ℝ := if q = exceptionalPoint then -1 else q.fst^2
private def objective (q : Plane) : EReal := cost q

private theorem atPair (x u : ℝ) : cost (WithLp.toLp 2 (x,u)) =
    if x = 1 ∧ u = 1 then -1 else x^2 := by simp [cost,exceptionalPoint]

private theorem lsc_objective : LowerSemicontinuous objective := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  let S : Set Plane := {q | ((q.fst^2:ℝ):EReal) ≤ a}
  have hS : IsClosed S := isClosed_le (continuous_coe_real_ereal.comp ((WithLp.continuous_fst 2 ℝ ℝ).pow 2)) continuous_const
  by_cases h : ((-1:ℝ):EReal) ≤ a
  · have he : objective ⁻¹' Iic a = S ∪ {exceptionalPoint} := by
      ext q
      by_cases hq : q = exceptionalPoint <;> simp [objective,cost,hq,S]
      simpa using h
    rw [he]; exact hS.union isClosed_singleton
  · have he : objective ⁻¹' Iic a = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      apply h
      apply le_trans _ hq
      change ((-1:ℝ):EReal) ≤ ((cost q:ℝ):EReal)
      rw [EReal.coe_le_coe_iff]
      by_cases he : q = exceptionalPoint <;> simp [cost,he] <;> linarith [sq_nonneg q.fst]
    rw [he]; exact isClosed_empty

private theorem bounded_objective : IsParametricallyLevelBounded objective := by
  intro u a
  refine ⟨1,one_pos,?_⟩
  apply ((isBounded_Icc (a := -(|a|+2)) (b := |a|+2)).prod (isBounded_closedBall (x := u) (r := 1))).subset
  rintro ⟨x,v⟩ hp
  have hle : ((cost (WithLp.toLp 2 (x,v)):ℝ):EReal) ≤ (a:EReal) := hp.2
  rw [EReal.coe_le_coe_iff,atPair] at hle
  refine ⟨?_,hp.1.2⟩
  change -(|a|+2) ≤ x ∧ x ≤ |a|+2
  split at hle
  · rename_i hh
    rw [hh.1]
    constructor <;> linarith [abs_nonneg a]
  · constructor <;> nlinarith [sq_nonneg (x-1),sq_nonneg (x+1),le_abs_self a,abs_nonneg a]

private theorem value_objective (u : ℝ) : parametricValue objective u = ((if u = 1 then -1 else 0 : ℝ):EReal) := by
  change (⨅ x : ℝ, ((cost (WithLp.toLp 2 (x,u)):ℝ):EReal)) = _
  by_cases hu : u = 1
  · rw [if_pos hu]
    refine le_antisymm ((iInf_le _ 1).trans ?_) (le_iInf fun x ↦ ?_)
    · simp [atPair,hu]
    · rw [atPair,EReal.coe_le_coe_iff]; split <;> linarith [sq_nonneg x]
  · rw [if_neg hu]
    refine le_antisymm ((iInf_le _ 0).trans ?_) (le_iInf fun x ↦ ?_)
    · simp [atPair,hu]
    · rw [atPair,EReal.coe_le_coe_iff]; simpa [hu] using sq_nonneg x

/-- The printed hypotheses of 10.58 hold with `W = univ` and `V` the
complement of the exceptional decision. The value has a downward jump at
parameter one and hence cannot be upper-C¹ on that entire `W`. -/
theorem parametric_subsmoothness_neighborhood_counterexample :
    ∃ (f : WithLp 2 (ℝ × ℝ) → ℝ) (V : Set ℝ), IsOpen V ∧
      IsProper (fun q ↦ (f q:EReal)) ∧ LowerSemicontinuous (fun q ↦ (f q:EReal)) ∧
      IsParametricallyLevelBounded (fun q ↦ (f q:EReal)) ∧
      parametricValue (fun q ↦ (f q:EReal)) 0 = 0 ∧
      parametricMinimizers (fun q ↦ (f q:EReal)) 0 ⊆ V ∧
      (∀ x ∈ V, ∀ u : ℝ, HasDerivAt (fun v ↦ f (WithLp.toLp 2 (x,v))) 0 u) ∧
      ContinuousOn (fun p : ℝ × ℝ ↦ f (WithLp.toLp 2 p)) (V ×ˢ univ) ∧
      ¬ IsUpperCOn 1 (fun u ↦ (parametricValue (fun q ↦ (f q:EReal)) u).toReal) univ := by
  let V : Set ℝ := {1}ᶜ
  refine ⟨cost,V,isClosed_singleton.isOpen_compl,
    ⟨⟨0,EReal.coe_lt_top _⟩,fun _ ↦ EReal.bot_lt_coe _⟩,lsc_objective,bounded_objective,?_,?_,?_,?_,?_⟩
  · simpa [objective] using value_objective 0
  · intro x hx hbad
    have hval := (mem_parametricMinimizers.mp hx).1
    change objective (WithLp.toLp 2 (x,0)) = parametricValue objective 0 at hval
    have hx1 : x = 1 := hbad
    norm_num [value_objective,objective,atPair,hx1] at hval
  · intro x hx u
    have he : (fun v : ℝ ↦ cost (WithLp.toLp 2 (x,v))) = fun _ ↦ x^2 := by
      funext v; simp [atPair,show x ≠ 1 from hx]
    rw [he]; exact hasDerivAt_const _ _
  · apply ((continuous_fst.pow 2 : Continuous (fun p : ℝ × ℝ ↦ p.1^2)).continuousOn).congr
    rintro ⟨x,u⟩ hp
    simp [atPair,show x ≠ 1 from hp.1]
  · intro h
    change IsLowerCOn 1 (fun u ↦ -(parametricValue objective u).toReal) univ at h
    have hc := (h.strictlyContinuousAt le_rfl (mem_univ (1:ℝ))).continuousAt
    have hlim : Tendsto (fun _ : ℝ ↦ (0:ℝ)) (𝓝[>] (1:ℝ)) (𝓝 1) := by
      have H := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1:ℝ)))
      simp only [value_objective,EReal.toReal_coe,if_true,neg_neg] at H
      apply H.congr'
      filter_upwards [self_mem_nhdsWithin (a := (1:ℝ)) (s := Ioi 1)] with u hu
      simp [ne_of_gt (show 1 < u from hu)]
    exact zero_ne_one (tendsto_nhds_unique (tendsto_const_nhds (x := (0:ℝ))) hlim)

end
end RW
