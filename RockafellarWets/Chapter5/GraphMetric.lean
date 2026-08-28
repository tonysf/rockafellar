/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Quantification of Graphical Convergence

Theorem 5.50 and the paragraphs around it.

Graphical convergence is *defined* here as Painleve--Kuratowski convergence of
the graphs, so the passage from Chapter 4's hyperspace to the space
`osc-maps≢∅` of the theorem is not a translation but an identification: an
outer semicontinuous mapping with nonempty domain is exactly a nonempty closed
subset of `IRⁿ × IRᵐ`, by 5.7 and `svOfGraph`.  Everything the book asks for
therefore transports along `S ↦ gph S`: the metric and its convergence
characterization from 4.42, the localized pseudo-metrics and their threshold
form from 4.36, properness -- hence local compactness -- from 4.43, and
separability from 4.45.

The one clause that is not transport is the parenthetical that `dl̂ρ` fails
the triangle inequality on mappings as it does on sets.  Chapter 4's witness
lives in `IR`, and it is carried into graphs by the mappings supported at a
single point of the domain, `x ↦ if x = 0 then A else ∅`, whose graph is
`{0} × A`.  Because `a ↦ (0, a)` is an isometry of `IR` into `IR × IR` for
the product norm, all the localized distances are unchanged.
-/

import RockafellarWets.Chapter4.FiniteSetApproximation
import RockafellarWets.Chapter4.IntegratedSetDistance
import RockafellarWets.Chapter5.GraphicalCompactness

open Filter Metric Set Topology
open scoped NNReal

namespace RW

section Space

variable {E F : Type*}

theorem svGraph_nonempty_iff (S : E → Set F) :
    (svGraph S).Nonempty ↔ (svDom S).Nonempty := by
  constructor
  · rintro ⟨⟨x, u⟩, hu⟩
    exact ⟨x, ⟨u, hu⟩⟩
  · rintro ⟨x, u, hu⟩
    exact ⟨(x, u), hu⟩

theorem svGraph_injective : Function.Injective (svGraph : (E → Set F) → Set (E × F)) := by
  intro S T h
  funext x
  ext u
  exact Set.ext_iff.1 h (x, u)

end Space

section Model

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The space `osc-maps≢∅(IRⁿ, IRᵐ)` of Theorem 5.50: outer semicontinuous
mappings with nonempty domain, carrying the graph distance
`dl(T, S) = dl(gph S, gph T)`. -/
@[ext]
structure OscMapModel (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] where
  /-- The underlying set-valued mapping. -/
  toFun : E → Set F
  /-- Membership of `osc-maps` is outer semicontinuity. -/
  svOsc' : SvOsc toFun
  /-- The subscript `≢∅` of the book: the domain is not empty. -/
  dom_nonempty : (svDom toFun).Nonempty

namespace OscMapModel

variable (S T : OscMapModel E F)

/-- The graph of a point of `osc-maps≢∅`, a nonempty closed subset of the
product. -/
def graph : Set (E × F) := svGraph S.toFun

theorem isClosed_graph : IsClosed S.graph := isClosed_svGraph_iff_svOsc.2 S.svOsc'

theorem graph_nonempty : S.graph.Nonempty :=
  (svGraph_nonempty_iff _).2 S.dom_nonempty

theorem graph_injective : Function.Injective (graph : OscMapModel E F → Set (E × F)) := by
  intro S T h
  ext1
  exact svGraph_injective h

/-- **Theorem 5.50**, metric clause: the graph distance is a metric on
`osc-maps≢∅`. -/
noncomputable instance : MetricSpace (OscMapModel E F) where
  dist S T := integratedSetDistance S.graph T.graph
  dist_self S := integratedSetDistance_self _
  dist_comm S T := integratedSetDistance_comm _ _
  dist_triangle S T U := integratedSetDistance_triangle _ _ _
  eq_of_dist_eq_zero {S T} h :=
    graph_injective (eq_of_integratedSetDistance_eq_zero S.isClosed_graph
      T.isClosed_graph S.graph_nonempty T.graph_nonempty h)

@[simp]
theorem dist_eq : dist S T = integratedSetDistance S.graph T.graph := rfl

/-- The identification of `osc-maps≢∅(IRⁿ, IRᵐ)` with the hyperspace
`cl-sets≠∅(IRⁿ × IRᵐ)`: a mapping is osc with nonempty domain exactly when its
graph is closed and nonempty, and `svOfGraph` inverts the passage to graphs.
The graph distance is the hyperspace distance by definition, so this is an
isometry. -/
noncomputable def isometryEquivSetMetricModel :
    OscMapModel E F ≃ᵢ SetMetricModel (E × F) where
  toFun S := ⟨⟨S.graph, S.isClosed_graph, S.graph_nonempty⟩⟩
  invFun C :=
    { toFun := svOfGraph C.carrier
      svOsc' := isClosed_svGraph_iff_svOsc.1 (by
        rw [svGraph_svOfGraph]; exact C.isClosed_carrier)
      dom_nonempty := (svGraph_nonempty_iff _).1 (by
        rw [svGraph_svOfGraph]; exact C.nonempty_carrier) }
  left_inv S := by
    ext1
    rfl
  right_inv C := by
    apply SetMetricModel.carrier_injective
    exact svGraph_svOfGraph C.carrier
  isometry_toFun S T := by
    simp only [edist_dist, dist_eq, SetMetricModel.dist_eq]
    rfl

/-- **Theorem 5.50**, convergence clause: convergence in the graph metric is
graphical convergence. -/
theorem tendsto_iff_graphicalConverges {u : ℕ → OscMapModel E F}
    {S : OscMapModel E F} :
    Tendsto u atTop (nhds S) ↔
      GraphicalConverges (fun n ↦ (u n).toFun) S.toFun := by
  have hgr : GraphicalConverges (fun n ↦ (u n).toFun) S.toFun ↔
      PKConverges (fun n ↦ (u n).graph) S.graph := Iff.rfl
  rw [hgr, pkConverges_iff_tendsto_integratedSetDistance
    S.isClosed_graph S.graph_nonempty fun n ↦ (u n).graph_nonempty,
    tendsto_iff_dist_tendsto_zero]
  rfl

/-- **Theorem 5.50**, `dl` clause in the book's notation: graphical
convergence is the vanishing of the graph distances. -/
theorem graphicalConverges_iff_tendsto_dist {u : ℕ → OscMapModel E F}
    {S : OscMapModel E F} :
    GraphicalConverges (fun n ↦ (u n).toFun) S.toFun ↔
      Tendsto (fun n ↦ dist (u n) S) atTop (nhds 0) :=
  tendsto_iff_graphicalConverges.symm.trans tendsto_iff_dist_tendsto_zero

/-- **Theorem 5.50**, local compactness clause, from 4.43 through the
identification with the hyperspace. -/
instance : ProperSpace (OscMapModel E F) := by
  refine ⟨fun x r ↦ ?_⟩
  have h : closedBall x r =
      isometryEquivSetMetricModel.symm '' closedBall
        (isometryEquivSetMetricModel x) r := by
    rw [isometryEquivSetMetricModel.symm.image_closedBall,
      IsometryEquiv.symm_apply_apply]
  rw [h]
  exact (isCompact_closedBall _ _).image
    isometryEquivSetMetricModel.symm.continuous

theorem locallyCompactSpace : LocallyCompactSpace (OscMapModel E F) :=
  inferInstance

/-- **Theorem 5.50**, completeness clause, from properness. -/
theorem completeSpace : CompleteSpace (OscMapModel E F) := inferInstance

/-- **Theorem 5.50**, separability clause: a proper metric space is second
countable, and 4.45 is what makes the hyperspace proper. -/
theorem separableSpace : TopologicalSpace.SeparableSpace (OscMapModel E F) :=
  inferInstance

/-- Formula 5(14): the localized graph distance `dlρ(T, S) = dlρ(gph S, gph T)`. -/
noncomputable def rhoGraphDistance (ρ : ℝ≥0) (S T : OscMapModel E F) : ℝ :=
  rhoDistance ρ S.graph T.graph

/-- Formula 5(14): the truncated-inclusion graph distance
`dl̂ρ(T, S) = dl̂ρ(gph S, gph T)`. -/
noncomputable def rhoHatGraphDistance (ρ : ℝ≥0) (S T : OscMapModel E F) : ℝ :=
  rhoHatDistance ρ S.graph T.graph

/-- **Theorem 5.50**, pseudo-metric clause: each `dlρ` is a pseudo-metric on
`osc-maps≢∅`. -/
noncomputable def rhoGraphPseudoMetric (ρ : ℝ≥0) :
    PseudoMetric (OscMapModel E F) ℝ where
  toFun S T := rhoGraphDistance ρ S T
  refl' S := rhoDistance_self ρ S.graph
  symm' S T := rhoDistance_comm ρ S.graph T.graph
  triangle' S T U := rhoDistance_triangle ρ S.graph T.graph U.graph

/-- **Theorem 5.50**, `dlρ` clause: graphical convergence is the vanishing of
the localized graph distances at all radii above any fixed threshold. -/
theorem graphicalConverges_iff_tendsto_rhoGraphDistance_from
    {u : ℕ → OscMapModel E F} {S : OscMapModel E F} (r₀ : ℝ≥0) :
    GraphicalConverges (fun n ↦ (u n).toFun) S.toFun ↔
      ∀ ρ : ℝ≥0, r₀ ≤ ρ →
        Tendsto (fun n ↦ rhoGraphDistance ρ (u n) S) atTop (nhds 0) :=
  pkConverges_iff_tendsto_rhoDistance_from S.isClosed_graph S.graph_nonempty
    (fun n ↦ (u n).graph_nonempty) r₀

/-- **Theorem 5.50**, `dl̂ρ` clause. -/
theorem graphicalConverges_iff_tendsto_rhoHatGraphDistance_from
    {u : ℕ → OscMapModel E F} {S : OscMapModel E F} (r₀ : ℝ≥0) :
    GraphicalConverges (fun n ↦ (u n).toFun) S.toFun ↔
      ∀ ρ : ℝ≥0, r₀ ≤ ρ →
        Tendsto (fun n ↦ rhoHatGraphDistance ρ (u n) S) atTop (nhds 0) :=
  pkConverges_iff_tendsto_rhoHatDistance_from S.isClosed_graph S.graph_nonempty
    (fun n ↦ (u n).graph_nonempty) r₀

end OscMapModel

end Model

section NoTriangle

/-- The mapping supported at the origin of the domain, with graph `{0} × A`.
This is the vehicle that carries Chapter 4's one-dimensional witnesses into
graphs, the embedding `a ↦ (0, a)` being an isometry for the product norm. -/
noncomputable def svAtZero (A : Set ℝ) : ℝ → Set ℝ :=
  fun x ↦ if x = 0 then A else ∅

theorem svGraph_svAtZero (A : Set ℝ) :
    svGraph (svAtZero A) = ({0} : Set ℝ) ×ˢ A := by
  ext ⟨x, a⟩
  simp only [svGraph, svAtZero, mem_setOf_eq, mem_prod, mem_singleton_iff]
  by_cases hx : x = 0 <;> simp [hx]

theorem isometry_mk_zero : Isometry (Prod.mk (0 : ℝ) : ℝ → ℝ × ℝ) :=
  Isometry.of_dist_eq fun a b ↦ by
    simp [Prod.dist_eq]

theorem preimage_mk_zero_closedBall (ρ : ℝ) :
    (Prod.mk (0 : ℝ)) ⁻¹' closedBall (0 : ℝ × ℝ) ρ = closedBall (0 : ℝ) ρ := by
  simpa using isometry_mk_zero.preimage_closedBall (0 : ℝ) ρ

theorem rhoHatEDistance_prod_singleton (ρ : ℝ≥0) (A B : Set ℝ) :
    rhoHatEDistance ρ (({0} : Set ℝ) ×ˢ A) (({0} : Set ℝ) ×ˢ B)
      = rhoHatEDistance ρ A B := by
  have hint : ∀ C : Set ℝ, (Prod.mk (0 : ℝ) '' C) ∩ closedBall 0 (ρ : ℝ)
      = Prod.mk (0 : ℝ) '' (C ∩ closedBall 0 (ρ : ℝ)) := by
    intro C
    rw [← preimage_mk_zero_closedBall (ρ : ℝ), Set.image_inter_preimage]
  simp only [singleton_prod, rhoHatEDistance, hint, iSup_image,
    Metric.infEDist_image isometry_mk_zero]

theorem rhoHatDistance_prod_singleton (ρ : ℝ≥0) (A B : Set ℝ) :
    rhoHatDistance ρ (({0} : Set ℝ) ×ˢ A) (({0} : Set ℝ) ×ˢ B)
      = rhoHatDistance ρ A B := by
  simp only [rhoHatDistance, rhoHatEDistance_prod_singleton]

theorem svOsc_svAtZero {A : Set ℝ} (hA : IsClosed A) : SvOsc (svAtZero A) :=
  isClosed_svGraph_iff_svOsc.1 <| by
    rw [svGraph_svAtZero]; exact isClosed_singleton.prod hA

/-- The point of `osc-maps≢∅(IR, IR)` whose graph is `{0} × A`. -/
noncomputable def oscMapAtZero {A : Set ℝ} (hA : IsClosed A) (hAne : A.Nonempty) :
    OscMapModel ℝ ℝ where
  toFun := svAtZero A
  svOsc' := svOsc_svAtZero hA
  dom_nonempty := ⟨0, by simpa [svDom, svAtZero] using hAne⟩

@[simp]
theorem graph_oscMapAtZero {A : Set ℝ} (hA : IsClosed A) (hAne : A.Nonempty) :
    (oscMapAtZero hA hAne).graph = ({0} : Set ℝ) ×ˢ A :=
  svGraph_svAtZero A

/-- **Theorem 5.50**, the parenthetical: `dl̂ρ` is *not* a pseudo-metric on
`osc-maps≢∅`, the triangle inequality failing for the mappings supported at
the origin whose values are Chapter 4's witness sets. -/
theorem not_rhoHatGraphDistance_triangle :
    ¬ ∀ (ρ : ℝ≥0) (S T U : OscMapModel ℝ ℝ),
        OscMapModel.rhoHatGraphDistance ρ S U ≤
          OscMapModel.rhoHatGraphDistance ρ S T +
            OscMapModel.rhoHatGraphDistance ρ T U := by
  intro h
  refine not_rhoHatDistance_triangle ?_
  have hmid : IsClosed ({-(6 / 5), 6 / 5} : Set ℝ) :=
    (Set.toFinite ({-(6 / 5), 6 / 5} : Set ℝ)).isClosed
  have := h 1 (oscMapAtZero isClosed_singleton (singleton_nonempty (1 : ℝ)))
    (oscMapAtZero hmid ⟨-(6 / 5), by simp⟩)
    (oscMapAtZero isClosed_singleton (singleton_nonempty (-1 : ℝ)))
  simpa only [OscMapModel.rhoHatGraphDistance, graph_oscMapAtZero,
    rhoHatDistance_prod_singleton] using this

end NoTriangle

section Closure

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G]

/-- The localized uniform distances see only the closures of their arguments,
distance functions being closure-invariant. -/
theorem rhoDistance_closure (ρ : ℝ≥0) (C D : Set G) :
    rhoDistance ρ (closure C) (closure D) = rhoDistance ρ C D := by
  have hprof : ∀ A : Set G, distanceProfile ρ (closure A) = distanceProfile ρ A := by
    intro A
    ext z
    exact infDist_closure
  rw [rhoDistance, rhoDistance, hprof, hprof]

/-- The integrated distance likewise sees only the closures. -/
theorem integratedSetDistance_closure (C D : Set G) :
    integratedSetDistance (closure C) (closure D) = integratedSetDistance C D := by
  simp only [integratedSetDistance, rhoDistanceReal, rhoDistance_closure]

/-- The remark after 5.50: on the larger space of *all* set-valued mappings
the graph distance is only a pseudo-metric, since it cannot separate a mapping
from the one whose graph is the closure of its own. -/
theorem exists_ne_integratedSetDistance_svGraph_eq_zero :
    ∃ S T : ℝ → Set ℝ, S ≠ T ∧
      integratedSetDistance (svGraph S) (svGraph T) = 0 := by
  refine ⟨fun _ ↦ Ioo (0 : ℝ) 1, fun _ ↦ Icc (0 : ℝ) 1, ?_, ?_⟩
  · intro hST
    have := congrFun hST 0
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    rw [← this] at h1
    exact absurd h1 (by norm_num)
  · have hgS : svGraph (fun _ : ℝ ↦ Ioo (0 : ℝ) 1) = (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1 := by
      ext ⟨x, a⟩; simp [svGraph]
    have hgT : svGraph (fun _ : ℝ ↦ Icc (0 : ℝ) 1) = (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1 := by
      ext ⟨x, a⟩; simp [svGraph]
    have hcl : closure ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) = (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1 := by
      rw [closure_prod_eq, closure_univ, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    have hclT : closure ((univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1) = (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1 :=
      (isClosed_univ.prod isClosed_Icc).closure_eq
    rw [hgS, hgT, ← integratedSetDistance_closure, hcl, hclT,
      integratedSetDistance_self]

end Closure

end RW
