/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform convergence of finite convex functions on compact subsets
-/

import RockafellarWets.Chapter7.ConvexEpiConvergence
import RockafellarWets.Chapter7.EpiLimitProperties
import Mathlib.Analysis.Convex.Continuous

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Corollary 7.18.** Real-valued convex functions converging pointwise on
a dense subset of an open convex set converge uniformly on each compact
subset of that open set. Values outside the open set play no role. -/
theorem tendstoUniformlyOn_of_convexOn_of_dense
    {O D B : Set E} (hO : IsOpen O) {f : ℕ → E → ℝ} {g : E → ℝ}
    (hf : ∀ n, ConvexOn ℝ O (f n)) (hg : ConvexOn ℝ O g)
    (hDO : D ⊆ O) (hOD : O ⊆ closure D)
    (hlim : ∀ x ∈ D, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (hB : IsCompact B) (hBO : B ⊆ O) : TendstoUniformlyOn f g atTop B := by
  classical
  rcases B.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact tendstoUniformlyOn_empty
  let extFn := fun (v : E → ℝ) (x : E) ↦ if x ∈ O then (v x : EReal) else ⊤
  have hepi (v : E → ℝ) : epigraph (extFn v) = {p : E × ℝ | p.1 ∈ O ∧ v p.1 ≤ p.2} := by
    ext ⟨x, t⟩
    by_cases hx : x ∈ O <;> simp [mem_epigraph_iff, extFn, hx]
  let G := epiClosure (extFn g)
  have hgraph : epigraph G = closure (epigraph (extFn g)) := epigraph_epiClosure _
  have hGcv : Convex ℝ (epigraph G) := by rw [hgraph, hepi]; exact hg.convex_epigraph.closure
  have hGcl : LowerSemicontinuous G :=
    lowerSemicontinuous_of_isClosed_epigraph_ereal G (hgraph ▸ isClosed_closure)
  have hinside (x : E) (hx : x ∈ O) : G x = (g x : EReal) := by
    have hbelow : G x ≤ (g x : EReal) := by
      change (x, g x) ∈ epigraph G
      rw [hgraph, hepi]
      exact subset_closure ⟨hx, le_rfl⟩
    refine hbelow.antisymm (le_of_not_gt fun hlt ↦ ?_)
    obtain ⟨t, hGt, htg⟩ := EReal.exists_between_coe_real hlt
    have hmem : (x, t) ∈ epigraph G := hGt.le
    rw [hgraph, hepi] at hmem
    obtain ⟨p, hp, hpx⟩ := mem_closure_iff_seq_limit.mp hmem
    have hxp : Tendsto (fun n ↦ (p n).1) atTop (𝓝[O] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hpx.fst_nhds, Eventually.of_forall fun n ↦ (hp n).1⟩
    have hgt := le_of_tendsto_of_tendsto' (((hg.continuousOn hO) x hx).tendsto.comp hxp) hpx.snd_nhds
      (fun n ↦ (hp n).2)
    exact (EReal.coe_lt_coe_iff.mp htg).not_ge hgt
  have hout (x : E) (hx : x ∉ closure O) : G x = ⊤ := by
    by_contra hn
    obtain ⟨t, ht, -⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hn)
    have hmem : (x, t) ∈ epigraph G := ht.le
    rw [hgraph, hepi] at hmem
    have hsub : {p : E × ℝ | p.1 ∈ O ∧ g p.1 ≤ p.2} ⊆ Prod.fst ⁻¹' closure O :=
      fun _ hp ↦ subset_closure hp.1
    exact hx (closure_minimal hsub (isClosed_closure.preimage continuous_fst) hmem)
  have hdom : O ⊆ interior (effectiveDomain G) := hO.subset_interior_iff.mpr
    (fun x hx ↦ (hinside x hx).trans_lt (EReal.coe_lt_top _))
  have hdense : Dense (D ∪ (closure O)ᶜ) := by
    intro x
    rw [closure_union]
    by_cases hx : x ∈ closure O
    · exact Or.inl (closure_minimal hOD isClosed_closure hx)
    · exact Or.inr (subset_closure hx)
  have hfcv (n : ℕ) : Convex ℝ (epigraph (extFn (f n))) := by
    rw [hepi]
    exact (hf n).convex_epigraph
  have hep := epiConverges_of_convex_of_tendsto_on_dense hfcv hGcv hGcl
    ⟨x₀, hdom (hBO hx₀)⟩ hdense (by
      intro x hx
      rcases hx with hx | hx
      · simpa [extFn, hDO hx, hinside x (hDO hx)] using
          continuous_coe_real_ereal.continuousAt.tendsto.comp (hlim x hx)
      · have hxo : x ∉ O := fun hxO ↦ hx (subset_closure hxO)
        simp [extFn, hxo, hout x hx])
  have hdis : Disjoint B (frontier (effectiveDomain G)) :=
    disjoint_interior_frontier.mono_left (hBO.trans hdom)
  have hu := hep.erealConvergesUniformlyOn_of_disjoint_frontier hfcv hB hdis
  obtain ⟨M, hM⟩ := hB.bddAbove_image (continuous_abs.comp_continuousOn ((hg.continuousOn hO).mono hBO))
  apply ERealConvergesUniformlyOn.tendstoUniformlyOn_of_bounded (M := max 0 M) _
    (le_max_left ..) (fun x hx ↦ (hM (mem_image_of_mem _ hx)).trans (le_max_right ..))
  intro ρ hρ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hu ρ hρ) ε hε] with n hn
  intro x hx
  simpa [hinside x (hBO hx), extFn, hBO hx] using hn x hx

end RW
