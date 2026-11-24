/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: the printed dimension in Theorem 13.48

Theorem 13.48 asserts that the solution mapping `S(w, u) = {x ∣ F(w, x) + ∂f(x) ∋ u}` is
graphically Lipschitzian "of dimension `d + 2n`".  By Definition 9.66 that is the full dimension of
`ℝᵈ × ℝⁿ × ℝⁿ`, the complementary dimension is `0`, and the graph of the mapping would be a
neighborhood of the base point (`svGraph_mem_nhds_of_graphicallyLipschitzianAt_full`).  This fails
already for `f = 0` and `F(w, x) = x`, where `S(w, u) = {u}`
(`VariationalConditionPerturbationCounterexample.not_graphicallyLipschitzianAt_full_variational`).
`perturbation_of_solutions_to_variational_conditions` proves the correct dimension `d + n`; the
printed `d + 2n` is a misprint, like "proto-differentiable at `(w̄, v̄)`" for `(w̄, ū)` in the same
statement, and neither correction adds a hypothesis.
-/

import RockafellarWets.Chapter13.VariationalConditionPerturbation

open Filter Set Topology Metric

namespace RW

section Dimension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Definition 9.66** with full dimension: a mapping `S : E ⇉ F` that is graphically
Lipschitzian of dimension `dim E + dim F` at `(x̄, ū)` has complementary dimension `0`, so its graph
is a neighborhood of `(x̄, ū)`. -/
theorem svGraph_mem_nhds_of_graphicallyLipschitzianAt_full {S : E → Set F} {x : E} {u : F}
    (h : GraphicallyLipschitzianAt S x u (Module.finrank ℝ E + Module.finrank ℝ F)) :
    svGraph S ∈ 𝓝 (x, u) := by
  obtain ⟨-, e, he, Φ, Ψ, g, -, -, hgraph⟩ := h
  have he0 : e = 0 := by omega
  subst he0
  filter_upwards [hgraph] with z hz
  exact hz.2 (Subsingleton.elim _ _)

end Dimension

namespace VariationalConditionPerturbationCounterexample

section Variational

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The constant function `0` has `∂0(y) = {0}`. -/
theorem subdifferential_zero_fun (y : E) : subdifferential (fun _ : E ↦ (0 : EReal)) y = {0} := by
  have h := (subdifferentials_of_smooth (k := fun _ : E ↦ (0 : ℝ)) (x := y) contDiffAt_const).1
  simpa using h

omit [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] in
/-- For `f = 0` and `F(w, x) = x`, `S(w, u) = {u}`. -/
theorem mem_variational_zero_iff (p : WithLp 2 (W × E)) (y : E) :
    y ∈ variationalSolutionMapping (fun q : WithLp 2 (W × E) ↦ q.snd) (fun _ : E ↦ (0 : EReal)) p ↔
      y = p.snd := by
  change p.snd - (WithLp.toLp 2 (p.fst, y) : WithLp 2 (W × E)).snd ∈
    subdifferential (fun _ : E ↦ (0 : EReal)) y ↔ _
  rw [subdifferential_zero_fun, mem_singleton_iff, sub_eq_zero]
  exact eq_comm

omit [FiniteDimensional ℝ W] in
/-- **Theorem 13.48**, the printed dimension.  For `f = 0` and `F(w, x) = x` the solution mapping
is `S(w, u) = {u}`; when `n ≥ 1` it is not graphically Lipschitzian of dimension `d + 2n` (the full
dimension of `ℝᵈ × ℝⁿ × ℝⁿ`) at any point of its graph, since its graph is not a neighborhood of
any of its points. -/
theorem not_graphicallyLipschitzianAt_full_variational [Nontrivial E] (w : W) (u : E) :
    u ∈ variationalSolutionMapping (fun q : WithLp 2 (W × E) ↦ q.snd) (fun _ : E ↦ (0 : EReal))
        (WithLp.toLp 2 (w, u)) ∧
      ¬ GraphicallyLipschitzianAt
        (variationalSolutionMapping (fun q : WithLp 2 (W × E) ↦ q.snd) (fun _ : E ↦ (0 : EReal)))
        (WithLp.toLp 2 (w, u)) u
        (Module.finrank ℝ (WithLp 2 (W × E)) + Module.finrank ℝ E) := by
  refine ⟨(mem_variational_zero_iff _ _).2 rfl, fun h ↦ ?_⟩
  have hn := svGraph_mem_nhds_of_graphicallyLipschitzianAt_full h
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have hpath : Tendsto (fun t : ℝ ↦ ((WithLp.toLp 2 (w, u) : WithLp 2 (W × E)), u + t • e))
      (𝓝[≠] 0) (𝓝 ((WithLp.toLp 2 (w, u) : WithLp 2 (W × E)), u)) := by
    refine Tendsto.prodMk_nhds tendsto_const_nhds ?_
    have hc : Continuous fun t : ℝ ↦ u + t • e := by fun_prop
    have := hc.tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, htne⟩ := ((hpath.eventually hn).and self_mem_nhdsWithin).exists
  have hmem := (mem_variational_zero_iff (W := W) (WithLp.toLp 2 (w, u)) (u + t • e)).1 ht
  have h0 : t • e = 0 := by simpa using hmem
  rcases smul_eq_zero.1 h0 with h0 | h0
  · exact htne h0
  · exact he h0

end Variational

end VariationalConditionPerturbationCounterexample
end RW
