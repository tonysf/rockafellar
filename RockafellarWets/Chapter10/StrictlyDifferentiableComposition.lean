/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: composition of a set-valued mapping with a strictly differentiable mapping

**Exercise 10.53** for `S = S₀ ∘ F` with `S₀` osc, `ū ∈ S(x̄)`, `F` strictly differentiable at `x̄`
with derivative `L`, and `S₀` graphically regular at `F(x̄)` for `ū`: under the qualification that
the only `y ∈ D*S₀(F(x̄)|ū)(0)` with `L*y = 0` is `y = 0`, `S` is graphically regular at `x̄`
for `ū` and `D*S(x̄|ū) = D*F(x̄) ∘ D*S₀(F(x̄)|ū)`, i.e. `D*S(x̄|ū)(w) = L* D*S₀(F(x̄)|ū)(w)`
(`comp_graphicallyRegular_of_hasStrictFDerivAt`).  This is the regular case of root's 10.40
(`inner_comp_regular_and_coderivative_eq`), every `yF` being regular by strict differentiability.

The qualification is the one 10.50 requires for the book's guide (`gph S = G⁻¹(gph S₀)` with
`G(x, u) = (F(x), u)`), and it cannot be dropped: for `F(x) = (x, 0)` and `S₀(p) = {0}` on the
closed convex set `{p | p₁² ≤ p₂}` (empty elsewhere), `S₀` is osc and graphically regular and `F`
is strictly differentiable, but `1 ∈ D*S(0|0)(1)` while `1 ∉ D*F(0)(D*S₀(F(0)|0)(1))`
(`comp_coderivative_counterexample`).
-/

import RockafellarWets.Chapter10.InnerCompositionRegularity
import RockafellarWets.Chapter10.LipschitzConstraintNormals
import RockafellarWets.Chapter10.StrictlyContinuousMaxima
import RockafellarWets.Chapter8.GraphicalRegularity
import RockafellarWets.Chapter6.ElementaryCones
import RockafellarWets.Chapter6.ConvexSets

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace Pointwise

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- **Exercise 10.53**, with the qualification required by 10.50: `S = S₀ ∘ F` is graphically
regular at `x̄` for `ū` and `D*S(x̄|ū) = D*F(x̄) ∘ D*S₀(F(x̄)|ū)`. -/
theorem comp_graphicallyRegular_of_hasStrictFDerivAt {S : F → Set G} {f : E → F}
    {L : E →L[ℝ] F} {x : E} {u : G} (hS : SvOsc S) (hf : HasStrictFDerivAt f L x)
    (hu : u ∈ S (f x)) (hrS : IsGraphicallyRegularAt S (f x) u)
    (hQ : ∀ z ∈ coderivative S (f x) u 0, L.adjoint z = 0 → z = 0) :
    IsGraphicallyRegularAt (fun a ↦ S (f a)) x u ∧
      coderivative (fun a ↦ S (f a)) x u =
        svComp (coderivative (svSingleton f) x (f x)) (coderivative S (f x) u) ∧
      ∀ w, coderivative (fun a ↦ S (f a)) x u w = L.adjoint '' coderivative S (f x) u w := by
  have hsc := strictlyContinuousAt_of_hasStrictFDerivAt hf
  obtain ⟨hreg, heq⟩ := inner_comp_regular_and_coderivative_eq hS hsc hu (by
      intro z hz h0
      rw [(hasStrictGradientAt_inner_of_hasStrictFDerivAt hf z).subdifferential_eq,
        mem_singleton_iff] at h0
      exact hQ z hz h0.symm) hrS
    (fun _ z _ ↦ isSubdifferentiallyRegularAt_inner_of_hasStrictFDerivAt hf z)
  refine ⟨hreg, heq, fun w ↦ ?_⟩
  rw [heq, coderivative_singleton_of_hasStrictFDerivAt hf]
  ext v
  rw [mem_svComp, mem_image]
  constructor
  · rintro ⟨z, hz, hv⟩
    exact ⟨z, hz, (mem_singleton_iff.1 hv).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, mem_singleton _⟩

section Counterexample

/-- The inner map `x ↦ (x, 0)` of the 10.53 counterexample. -/
def compCounterexInner (a : ℝ) : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2 (a, 0)

/-- The outer mapping of the 10.53 counterexample: `{0}` on `{p | p₁² ≤ p₂}`, empty elsewhere. -/
def compCounterexOuter (p : WithLp 2 (ℝ × ℝ)) : Set ℝ := {u | p.fst ^ 2 ≤ p.snd ∧ u = 0}

theorem svGraphConvex_compCounterexOuter : SvGraphConvex compCounterexOuter := by
  rintro ⟨p, a⟩ ⟨hp, ha⟩ ⟨q, b⟩ ⟨hq, hb⟩ s t hs ht hst
  change (s • a + t • b) ∈ compCounterexOuter (s • p + t • q)
  refine ⟨?_, ?_⟩
  · simp only [WithLp.add_fst, WithLp.add_snd, WithLp.smul_fst, WithLp.smul_snd, smul_eq_mul]
    nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.fst - q.fst)),
      mul_le_mul_of_nonneg_left hp hs, mul_le_mul_of_nonneg_left hq ht]
  · have ha' : a = 0 := ha
    have hb' : b = 0 := hb
    rw [ha', hb', smul_zero, smul_zero, add_zero]

theorem isClosed_svGraph_compCounterexOuter : IsClosed (svGraph compCounterexOuter) := by
  have h : svGraph compCounterexOuter =
      {p : WithLp 2 (ℝ × ℝ) × ℝ | p.1.fst ^ 2 ≤ p.1.snd} ∩ {p | p.2 = 0} := rfl
  have hc1 : Continuous fun p : WithLp 2 (ℝ × ℝ) × ℝ ↦ p.1.fst :=
    (WithLp.fstL 2 ℝ ℝ ℝ).continuous.comp continuous_fst
  have hc2 : Continuous fun p : WithLp 2 (ℝ × ℝ) × ℝ ↦ p.1.snd :=
    (WithLp.sndL 2 ℝ ℝ ℝ).continuous.comp continuous_fst
  rw [h]
  exact (isClosed_le (hc1.pow 2) hc2).inter (isClosed_eq continuous_snd continuous_const)

theorem hasStrictFDerivAt_compCounterexInner (a : ℝ) :
    ∃ L : ℝ →L[ℝ] WithLp 2 (ℝ × ℝ), HasStrictFDerivAt compCounterexInner L a := by
  have h := (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.hasStrictFDerivAt.comp a
    ((hasStrictFDerivAt_id a).prodMk (hasStrictFDerivAt_const (0 : ℝ) a))
  exact ⟨_, h⟩

/-- The qualification in 10.53 cannot be dropped: `S₀ = compCounterexOuter` is osc and graphically regular at
`(F(0), 0)` and `F = compCounterexInner` is strictly differentiable, but `1 ∈ D*S(0|0)(1)` for
`S = S₀ ∘ F`, while `1 ∉ D*F(0)(D*S₀(F(0)|0)(1))`. -/
theorem comp_coderivative_counterexample :
    SvOsc compCounterexOuter ∧ IsGraphicallyRegularAt compCounterexOuter (compCounterexInner 0) 0 ∧
      (∃ L : ℝ →L[ℝ] WithLp 2 (ℝ × ℝ), HasStrictFDerivAt compCounterexInner L 0) ∧
      (1 : ℝ) ∈ coderivative (fun a ↦ compCounterexOuter (compCounterexInner a)) 0 0 1 ∧
      (1 : ℝ) ∉ svComp (coderivative (svSingleton compCounterexInner) 0 (compCounterexInner 0))
        (coderivative compCounterexOuter (compCounterexInner 0) 0) 1 := by
  have hosc : SvOsc compCounterexOuter := isClosed_svGraph_iff_svOsc.1 isClosed_svGraph_compCounterexOuter
  have h0 : (0 : ℝ) ∈ compCounterexOuter (compCounterexInner 0) := ⟨by simp [compCounterexInner], rfl⟩
  refine ⟨hosc, isGraphicallyRegularAt_of_graphConvex_of_osc svGraphConvex_compCounterexOuter hosc h0,
    hasStrictFDerivAt_compCounterexInner 0, ?_, ?_⟩
  · have hgraph : euclideanSvGraph (fun a ↦ compCounterexOuter (compCounterexInner a)) =
        {WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))} := by
      ext q
      rw [mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : q.fst ^ 2 ≤ 0 := h1
        have hq1 : q.fst = 0 := by nlinarith [sq_nonneg q.fst]
        apply WithLp.ofLp_injective 2
        exact Prod.ext hq1 h2
      · rintro rfl
        exact ⟨by simp [compCounterexInner], rfl⟩
    show WithLp.toLp 2 ((1 : ℝ), -(1 : ℝ)) ∈
      normalCone (euclideanSvGraph (fun a ↦ compCounterexOuter (compCounterexInner a))) (WithLp.toLp 2 (0, 0))
    rw [hgraph, normalCone_singleton]
    trivial
  · intro hmem
    obtain ⟨z, hz, h1⟩ := mem_svComp.1 hmem
    have hsc : StrictlyContinuousAt compCounterexInner 0 :=
      strictlyContinuousAt_of_hasStrictFDerivAt (hasStrictFDerivAt_compCounterexInner 0).choose_spec
    have hfun : (fun a ↦ ((⟪z, compCounterexInner a⟫_ℝ : ℝ) : EReal)) =
        fun a ↦ ((⟪z.fst, id a⟫_ℝ : ℝ) : EReal) := by
      funext a
      change ((⟪z.fst, a⟫_ℝ + ⟪z.snd, (0 : ℝ)⟫_ℝ : ℝ) : EReal) = _
      rw [inner_zero_right, add_zero]
      rfl
    rw [coderivative_svSingleton_eq_subdifferential hsc z, hfun,
      (hasStrictGradientAt_inner_of_hasStrictFDerivAt (hasStrictFDerivAt_id (0 : ℝ))
        z.fst).subdifferential_eq, ContinuousLinearMap.adjoint_id, mem_singleton_iff] at h1
    have hC : Convex ℝ (euclideanSvGraph compCounterexOuter) :=
      svGraphConvex_compCounterexOuter.linear_preimage
        (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (ℝ × ℝ)) ℝ).toLinearMap
    have hx : WithLp.toLp 2 (compCounterexInner 0, (0 : ℝ)) ∈ euclideanSvGraph compCounterexOuter := h0
    have hz' : WithLp.toLp 2 (z, -(1 : ℝ)) ∈
        normalCone (euclideanSvGraph compCounterexOuter) (WithLp.toLp 2 (compCounterexInner 0, (0 : ℝ))) := hz
    rw [normalCone_eq_of_convex hC hx] at hz'
    have key : ∀ t : ℝ, t * z.fst + t ^ 2 * z.snd ≤ 0 := by
      intro t
      have hq : WithLp.toLp 2 (WithLp.toLp 2 (t, t ^ 2), (0 : ℝ)) ∈ euclideanSvGraph compCounterexOuter :=
        ⟨le_refl _, rfl⟩
      have h := hz' _ hq
      have he : WithLp.toLp 2 (WithLp.toLp 2 (t, t ^ 2), (0 : ℝ)) -
          WithLp.toLp 2 (compCounterexInner 0, (0 : ℝ)) = WithLp.toLp 2 (WithLp.toLp 2 (t, t ^ 2), (0 : ℝ)) := by
        rw [sub_eq_self]
        apply WithLp.ofLp_injective 2
        exact Prod.ext (WithLp.ofLp_injective 2 (Prod.ext rfl rfl)) rfl
      rw [he] at h
      change ⟪z, WithLp.toLp 2 (t, t ^ 2)⟫_ℝ + ⟪-(1 : ℝ), (0 : ℝ)⟫_ℝ ≤ 0 at h
      change ⟪z.fst, t⟫_ℝ + ⟪z.snd, t ^ 2⟫_ℝ + ⟪-(1 : ℝ), (0 : ℝ)⟫_ℝ ≤ 0 at h
      rw [inner_zero_right, add_zero, real_inner_eq_mul', real_inner_eq_mul'] at h
      linarith
    rw [ContinuousLinearMap.id_apply] at h1
    rw [← h1] at key
    set b := z.snd
    have hb := abs_nonneg b
    have ht : 0 < 1 / (|b| + 1) := by positivity
    have htb : |b| * (1 / (|b| + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    have k := key (1 / (|b| + 1))
    have hnb : -|b| * (1 / (|b| + 1)) ^ 2 ≤ (1 / (|b| + 1)) ^ 2 * b := by
      nlinarith [neg_abs_le b, sq_nonneg (1 / (|b| + 1))]
    nlinarith [mul_pos ht (sub_pos.2 htb)]

end Counterexample

end RW
