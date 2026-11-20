/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Single-valued Lipschitz localizations
-/

import RockafellarWets.Chapter9.GraphLipschitzLocalization

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A single-valued Lipschitz branch representing the complete graph locally. -/
def HasLipschitzSingleValuedLocalization (S : E → Set F) (x : E) (u : F) : Prop :=
  ∃ (g : E → F) (r s : ℝ) (k : ℝ≥0), 0 < r ∧ 0 < s ∧ g x = u ∧
    LipschitzOnWith k g (ball x r) ∧ ∀ a ∈ ball x r, S a ∩ ball u s = {g a}

/-- Inner semicontinuity at the one selected graph point supplies the
nonempty nearby branch required by a local graph Lipschitz estimate. -/
theorem hasLipschitzSingleValuedLocalization_of_localGraphLipschitz {S : E → Set F} {x : E} {u : F}
    (hu : u ∈ S x) (hi : u ∈ svInnerLimit S x) {k : ℝ≥0}
    (hk : LocalGraphLipschitzBound (svGraph S) (x,u) k) :
    HasLipschitzSingleValuedLocalization S x u := by
  classical
  obtain ⟨δ,hδ,hbound⟩ := hk
  have hnear := hi (ball u (δ/2)) (ball_mem_nhds u (by positivity))
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min ε (δ/2)
  have hr : 0 < r := lt_min hε (by positivity)
  have hrδ : r ≤ δ := (min_le_right ε (δ/2)).trans (by linarith)
  have hδhalf : δ/2 ≤ δ := by linarith
  have hex (a : E) : ∃ v : F, a ∈ ball x r → v ∈ S a ∩ ball u (δ/2) := by
    by_cases ha : a ∈ ball x r
    · obtain ⟨v,hv⟩ := hεsub (ball_subset_ball (min_le_left ε (δ/2)) ha)
      exact ⟨v,fun _ ↦ hv⟩
    · exact ⟨u,fun h ↦ (ha h).elim⟩
  choose g hg using hex
  have hgraph {a : E} (ha : a ∈ ball x r) {v : F} (hv : v ∈ S a ∩ ball u (δ/2)) :
      (a,v) ∈ svGraph S ∩ ball (x,u) δ := by
    refine ⟨hv.1,?_⟩
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball hrδ ha,ball_subset_ball hδhalf hv.2⟩
  have hfiber (a : E) (ha : a ∈ ball x r) : S a ∩ ball u (δ/2) = {g a} := by
    apply Subset.antisymm
    · intro v hv
      apply mem_singleton_iff.mpr
      have h := hbound (a,v) (hgraph ha hv) (a,g a) (hgraph ha (hg a ha))
      simpa only [dist_self,mul_zero,dist_le_zero] using h
    · exact singleton_subset_iff.mpr (hg a ha)
  have hx : x ∈ ball x r := mem_ball_self hr
  have hgx : g x = u := by
    have h : u ∈ S x ∩ ball u (δ/2) := ⟨hu,mem_ball_self (by positivity)⟩
    rw [hfiber x hx] at h
    exact (mem_singleton_iff.mp h).symm
  refine ⟨g,r,δ/2,k,hr,by positivity,hgx,?_,hfiber⟩
  exact LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦
    hbound (a,g a) (hgraph ha (hg a ha)) (b,g b) (hgraph hb (hg b hb))

theorem HasLipschitzSingleValuedLocalization.exists_localGraphLipschitzBound
    {S : E → Set F} {x : E} {u : F} (h : HasLipschitzSingleValuedLocalization S x u) :
    ∃ k : ℝ≥0, LocalGraphLipschitzBound (svGraph S) (x,u) k := by
  obtain ⟨g,r,s,k,hr,hs,_,hlip,hfiber⟩ := h
  refine ⟨k,min r s,lt_min hr hs,?_⟩
  have hpoint {p : E × F} (hp : p ∈ svGraph S ∩ ball (x,u) (min r s)) :
      p.1 ∈ ball x r ∧ p.2 = g p.1 := by
    have hp' := hp.2
    rw [← ball_prod_same] at hp'
    have hx := ball_subset_ball (min_le_left r s) hp'.1
    have hu := ball_subset_ball (min_le_right r s) hp'.2
    refine ⟨hx,?_⟩
    exact mem_singleton_iff.mp ((hfiber p.1 hx) ▸ (show p.2 ∈ S p.1 ∩ ball u s from ⟨hp.1,hu⟩))
  intro p hp q hq
  obtain ⟨hpx,hpu⟩ := hpoint hp
  obtain ⟨hqx,hqu⟩ := hpoint hq
  rw [hpu,hqu]
  exact hlip.dist_le_mul _ hpx _ hqx

/-- **Theorem 9.54(a)**, the localization criterion. Only inner
semicontinuity at the selected base value is needed for this equivalence. -/
theorem hasLipschitzSingleValuedLocalization_iff_strictGraphicalDerivative_zero
    {S : E → Set F} {x : E} {u : F} (hu : u ∈ S x) (hi : u ∈ svInnerLimit S x) :
    HasLipschitzSingleValuedLocalization S x u ↔ strictGraphicalDerivative S x u 0 = {0} := by
  rw [strictGraphicalDerivative_zero_iff_localGraphLipschitz hu]
  exact ⟨fun h ↦ h.exists_localGraphLipschitzBound,
    fun ⟨k,hk⟩ ↦ hasLipschitzSingleValuedLocalization_of_localGraphLipschitz hu hi hk⟩

end RW
