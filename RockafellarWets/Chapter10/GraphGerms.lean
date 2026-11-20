/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Locality of graphical calculus and exact Aubin estimates
-/

import RockafellarWets.Chapter10.MappingGerms

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

section Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {S T : E → Set F} {X : Set E} {x : E} {u : F} {k : ℝ≥0}

/-- The exact constant in an Aubin estimate depends only on the graph germ. -/
theorem AubinEstimate.congr_graph_nhds (h : AubinEstimate S X x u k)
    (he : svGraph S =ᶠ[𝓝 (x,u)] svGraph T) : AubinEstimate T X x u k := by
  obtain ⟨V,hV,W,hW,H⟩ := h
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_prod_iff.mp
    (show {p | svGraph S p = svGraph T p} ∈ 𝓝 x ×ˢ 𝓝 u by simpa only [nhds_prod_eq] using he)
  obtain ⟨r,hr,hrB⟩ := Metric.mem_nhds_iff.mp hB
  let δ : ℝ := r/(4*((k:ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨V ∩ A ∩ ball x δ,inter_mem (inter_mem hV hA) (ball_mem_nhds _ hδ),
    W ∩ ball u (r/2),inter_mem hW (ball_mem_nhds _ (by positivity)),?_⟩
  intro a ha b hb v hv
  have hvB : v ∈ B := hrB (mem_ball.mpr ((mem_ball.mp hv.2.2).trans (show r/2 < r by linarith)))
  have heva : (v ∈ S a) = (v ∈ T a) := hAB (a := (a,v)) ⟨ha.2.1.2,hvB⟩
  have hva : v ∈ S a := heva.symm ▸ hv.1
  obtain ⟨z,hz,hd⟩ := H a ⟨ha.1,ha.2.1.1⟩ b ⟨hb.1,hb.2.1.1⟩ v ⟨hva,hv.2.1⟩
  have hab : dist a b < 2*δ := by
    have ht := dist_triangle a x b
    rw [dist_comm x b] at ht
    linarith [mem_ball.mp ha.2.2,mem_ball.mp hb.2.2]
  have hkd : (k:ℝ)*dist a b < r/2 := by
    have hδeq : 4*((k:ℝ)+1)*δ = r := by dsimp [δ]; field_simp
    have hlt : dist a b < 2*δ := hab
    have hle := mul_le_mul_of_nonneg_left hlt.le (show (0:ℝ)≤k from k.2)
    nlinarith [k.2]
  have hzu : dist z u < r := by
    have ht := dist_triangle z v u
    rw [dist_comm z v] at ht
    linarith [mem_ball.mp hv.2.2]
  have hezb : (z ∈ S b) = (z ∈ T b) := hAB (a := (b,z)) ⟨hb.2.1.2,hrB (mem_ball.mpr hzu)⟩
  exact ⟨z,hezb ▸ hz,hd⟩

theorem HasAubinPropertyWithinAt.congr_graph_nhds (h : HasAubinPropertyWithinAt S X x u)
    (he : svGraph S =ᶠ[𝓝 (x,u)] svGraph T) : HasAubinPropertyWithinAt T X x u := by
  obtain ⟨hx,hu,hc,k,hk⟩ := h
  have he0 : (u ∈ S x) = (u ∈ T x) := he.eq_of_nhds
  exact ⟨hx,he0 ▸ hu,hc.congr_nhds he,k,hk.congr_graph_nhds he⟩

theorem graphicalLipschitzModulusWithin_congr_graph_nhds
    (he : svGraph S =ᶠ[𝓝 (x,u)] svGraph T) :
    graphicalLipschitzModulusWithin S X x u = graphicalLipschitzModulusWithin T X x u := by
  apply le_antisymm
  · exact le_iInf fun k ↦ (k.2.congr_graph_nhds he.symm).modulus_le
  · exact le_iInf fun k ↦ (k.2.congr_graph_nhds he).modulus_le

end Metric

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S T : E → Set F} {x : E} {u : F}

theorem euclideanSvGraph_congr_graph_nhds (he : svGraph S =ᶠ[𝓝 (x,u)] svGraph T) :
    euclideanSvGraph S =ᶠ[𝓝 (WithLp.toLp 2 (x,u))] euclideanSvGraph T :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous.tendsto (WithLp.toLp 2 (x,u))).eventually he

theorem coderivative_congr_graph_nhds (he : svGraph S =ᶠ[𝓝 (x,u)] svGraph T) :
    coderivative S x u = coderivative T x u := by
  unfold coderivative
  rw [normalCone_congr_nhds (euclideanSvGraph_congr_graph_nhds he)]

theorem regularCoderivative_congr_graph_nhds (he : svGraph S =ᶠ[𝓝 (x,u)] svGraph T) :
    regularCoderivative S x u = regularCoderivative T x u := by
  unfold regularCoderivative
  rw [regularNormalCone_congr_nhds (euclideanSvGraph_congr_graph_nhds he)]

theorem graphicalDerivative_congr_graph_nhds (he : svGraph S =ᶠ[𝓝 (x,u)] svGraph T) :
    graphicalDerivative S x u = graphicalDerivative T x u := by
  unfold graphicalDerivative
  rw [tangentCone_congr_nhds (euclideanSvGraph_congr_graph_nhds he)]

theorem strictGraphicalDerivative_congr_graph_nhds (he : svGraph S =ᶠ[𝓝 (x,u)] svGraph T) :
    strictGraphicalDerivative S x u = strictGraphicalDerivative T x u := by
  unfold strictGraphicalDerivative
  rw [strictTangentCone_congr_nhds he]

theorem IsGraphicallyRegularAt.congr_graph_nhds (hr : IsGraphicallyRegularAt S x u)
    (he : svGraph S =ᶠ[𝓝 (x,u)] svGraph T) : IsGraphicallyRegularAt T x u := by
  have hg := euclideanSvGraph_congr_graph_nhds he
  refine ⟨hr.1.congr_nhds hg,?_⟩
  rw [← normalCone_congr_nhds hg,← regularNormalCone_congr_nhds hg]
  exact hr.2

end RW
