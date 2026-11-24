/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Normality test for convex integrands

Proposition 14.39 of Rockafellar–Wets.  The key fact is that the epigraph of a convex function is
the closure of the part of it lying over any subset `Q ⊆ dom f` dense in `dom f`
(`epigraph_subset_closure_of_dense`).  The book derives this from Theorem 2.35 on relative interiors;
here it is proved directly: `f` is bounded above on the convex hull `Δ` of finitely many points of `Q`
with the same affine span as `dom f`, so `f ≤ (1 - λ) f(x) + λ M` on the relative ball
`(1 - λ) x + λ (B(c, r) ∩ aff Δ)` around a point `c` of the relative interior of `Δ`, which contains
points of `Q`.

Scope (Adapted): the closing sentence "every lsc convex integrand is a normal integrand" belongs to
the preceding test and so needs its interior condition; no statement is weakened.  Read without that
scope it is false, as the book's own example after 14.28 shows: it is convex in `x`
(`exists_lsc_convex_measurable_not_normal`).  Nonempty domains do not help either:
`f(t, ·) = δ_{c(t)}` with `c(t) = (t, 1_D(t))`, `D ⊆ ℝ` not Borel, is lsc and convex in `x` and
measurable in `t` for each `x`, yet not normal (`convex_normality_counterexample`).
-/

import RockafellarWets.Chapter14.MeasurableSelections
import RockafellarWets.Chapter14.NormalIntegrands
import RockafellarWets.Chapter7.ConvexEpiConvergence
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Rat.Denumerable

open Set Filter Topology Metric
open scoped ENNReal NNReal

noncomputable section

namespace RW

section Density

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Points `x` over which a convex function is approximated by values on a dense subset of its
domain: the epigraph of a convex `f` lies in the closure of its part over any `Q ⊆ dom f` that is
dense in `dom f`. -/
theorem epigraph_subset_closure_of_dense {f : E → EReal} (hconv : Convex ℝ (epigraph f))
    {Q : Set E} (hQ : Q ⊆ effectiveDomain f) (hdense : effectiveDomain f ⊆ closure Q) :
    epigraph f ⊆ closure {p : E × ℝ | p.1 ∈ Q ∧ f p.1 ≤ p.2} := by
  rintro ⟨x, α⟩ hxα
  have hfx : f x ≤ (α : EReal) := hxα
  have hxD : x ∈ effectiveDomain f := lt_of_le_of_lt hfx (EReal.coe_lt_top α)
  have hDconv : Convex ℝ (effectiveDomain f) := convex_effectiveDomain_of_convex_epigraph hconv
  have hseg : ∀ (y z : E) (β γ : ℝ), f y ≤ β → f z ≤ γ → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → f (a • y + b • z) ≤ ((a * β + b * γ : ℝ) : EReal) := by
    intro y z β γ hy hz a b ha hb hab
    have := hconv (show (y, β) ∈ epigraph f from hy) (show (z, γ) ∈ epigraph f from hz) ha hb hab
    simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using this
  have hsub : ∀ M : ℝ, Convex ℝ {y | f y ≤ (M : EReal)} := by
    intro M y hy z hz a b ha hb hab
    have := hseg y z M M hy hz a b ha hb hab
    rwa [← add_mul, hab, one_mul] at this
  set A := affineSpan ℝ Q
  have hQA : Q ⊆ A := subset_affineSpan ℝ Q
  have hDA : effectiveDomain f ⊆ A :=
    hdense.trans (A.closed_of_finiteDimensional.closure_subset_iff.2 hQA)
  obtain ⟨F, hFQ, hFspan, hFind⟩ := exists_affineIndependent ℝ E Q
  have hFfin : F.Finite := finite_set_of_fin_dim_affineIndependent ℝ hFind
  have hQne : Q.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hdense
    exact hdense hxD
  have hFne : F.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, AffineSubspace.span_empty] at hFspan
    obtain ⟨q, hq⟩ := hQne
    have hqA : q ∈ affineSpan ℝ Q := hQA hq
    rw [← hFspan] at hqA
    exact AffineSubspace.notMem_bot ℝ E q hqA
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ q ∈ F, f q ≤ (M : EReal) := by
    obtain ⟨M, hM⟩ := (hFfin.image fun q ↦ (f q).toReal).bddAbove
    refine ⟨M, fun q hq ↦ ?_⟩
    have hq' : f q ≠ ⊤ := (hQ (hFQ hq)).ne
    calc f q ≤ ((f q).toReal : EReal) := EReal.le_coe_toReal hq'
      _ ≤ M := EReal.coe_le_coe_iff.2 (hM ⟨q, hq, rfl⟩)
  set Δ := convexHull ℝ F
  have hΔM : ∀ y ∈ Δ, f y ≤ (M : EReal) := fun y hy ↦ convexHull_min (fun q hq ↦ hM q hq)
    (hsub M) hy
  have hΔD : Δ ⊆ effectiveDomain f := convexHull_min (hFQ.trans hQ) hDconv
  have hΔspan : affineSpan ℝ Δ = A := by rw [affineSpan_convexHull, hFspan]
  obtain ⟨c, hc⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ F) hFne.convexHull
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.1 hc
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  have hrel : ∀ z ∈ A, dist z (y : E) < r → z ∈ Δ := by
    intro z hzA hz
    have hzA' : z ∈ affineSpan ℝ Δ := by rw [hΔspan]; exact hzA
    have h1 := hball (show (⟨z, hzA'⟩ : affineSpan ℝ Δ) ∈ ball y r from hz)
    have h2 : (⟨z, hzA'⟩ : affineSpan ℝ Δ) ∈ (Subtype.val ⁻¹' Δ : Set (affineSpan ℝ Δ)) :=
      interior_subset h1
    exact h2
  set c₀ : E := (y : E)
  have hc₀Δ : c₀ ∈ Δ := by
    have h2 : y ∈ (Subtype.val ⁻¹' Δ : Set (affineSpan ℝ Δ)) := interior_subset hy
    exact h2
  have hc₀D : c₀ ∈ effectiveDomain f := hΔD hc₀Δ
  have hc₀M : f c₀ ≤ (M : EReal) := hΔM c₀ hc₀Δ
  rw [Metric.mem_closure_iff]
  intro ε hε
  set L : ℝ := r + dist x c₀ + |α - M| + 1 with hL
  have hL0 : 0 < L := by positivity
  set lam : ℝ := min 1 (ε / (2 * L)) with hlam
  have hlam0 : 0 < lam := lt_min one_pos (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hlamL : lam * L ≤ ε / 2 := by
    have : lam ≤ ε / (2 * L) := min_le_right _ _
    calc lam * L ≤ ε / (2 * L) * L := by gcongr
      _ = ε / 2 := by field_simp
  set z : E := (1 - lam) • x + lam • c₀
  have hzD : z ∈ effectiveDomain f := hDconv hxD hc₀D (by linarith) hlam0.le (by ring)
  obtain ⟨q, hqQ, hqd⟩ := Metric.mem_closure_iff.1 (hdense hzD) (lam * r) (by positivity)
  set c' : E := lam⁻¹ • (q - x) + x
  have hqc' : (1 - lam) • x + lam • c' = q := by
    simp only [c', smul_add, smul_smul, mul_inv_cancel₀ hlam0.ne', one_smul, sub_smul]
    abel
  have hc'A : c' ∈ A := by
    have hxA : x ∈ A := hDA hxD
    have hqA : q ∈ A := hQA hqQ
    have hdir : lam⁻¹ • (q - x) ∈ A.direction :=
      A.direction.smul_mem _ (AffineSubspace.vsub_mem_direction hqA hxA)
    exact AffineSubspace.vadd_mem_of_mem_direction hdir hxA
  have hc'eq : c' - c₀ = lam⁻¹ • (q - z) := by
    simp only [c', z, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hlam0.ne', one_smul,
      mul_sub, mul_one]
    module
  have hc'c : dist c' c₀ < r := by
    rw [dist_eq_norm, hc'eq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hlam0,
      ← dist_eq_norm, dist_comm]
    calc lam⁻¹ * dist z q < lam⁻¹ * (lam * r) := by gcongr
      _ = r := by field_simp
  have hc'M : f c' ≤ (M : EReal) := hΔM c' (hrel c' hc'A hc'c)
  have hfq : f q ≤ (((1 - lam) * α + lam * M : ℝ) : EReal) := by
    rw [← hqc']
    exact hseg x c' α M hfx hc'M (1 - lam) lam (by linarith) hlam0.le (by ring)
  refine ⟨(q, (1 - lam) * α + lam * M), ⟨hqQ, hfq⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · have hxz : dist x z = lam * dist x c₀ := by
      rw [dist_eq_norm, dist_eq_norm]
      have : x - z = lam • (x - c₀) := by simp only [z]; module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
    calc dist x q ≤ dist x z + dist z q := dist_triangle _ _ _
      _ < lam * dist x c₀ + lam * r := by rw [hxz]; linarith
      _ ≤ lam * L := by
          rw [← mul_add]
          gcongr
          rw [hL]
          linarith [abs_nonneg (α - M)]
      _ < ε := by linarith
  · rw [Real.dist_eq]
    have : α - ((1 - lam) * α + lam * M) = lam * (α - M) := by ring
    rw [this, abs_mul, abs_of_pos hlam0]
    calc lam * |α - M| ≤ lam * L := by
          gcongr
          rw [hL]
          linarith [dist_nonneg (x := x) (y := c₀)]
      _ < ε := by linarith

end Density

section Proposition1439

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Proposition 14.39 (normality test for convex integrands).** If every `f(t, ·)` is lsc and
convex, then `f` is a normal integrand if and only if there are measurable `xν : T → E` with
(a) `t ↦ f(t, xν(t))` measurable and (b) `{xν(t)} ∩ D_f(t)` dense in `D_f(t)` for every `t`. -/
theorem normality_test_for_convex_integrands {f : T → E → EReal}
    (hlsc : ∀ t, LowerSemicontinuous (f t)) (hconv : ∀ t, Convex ℝ (epigraph (f t))) :
    IsNormalIntegrand f ↔ ∃ x : ℕ → T → E, (∀ ν, Measurable (x ν)) ∧
      (∀ ν, Measurable fun t ↦ f t (x ν t)) ∧
      ∀ t, effectiveDomain (f t) ⊆ closure ((range fun ν ↦ x ν t) ∩ effectiveDomain (f t)) := by
  have hreal : ∀ (g : E → EReal) (x₀ : E), g x₀ < ⊤ → ∃ α : ℝ, g x₀ ≤ α := by
    intro g x₀ hx
    exact ⟨(g x₀).toReal, EReal.le_coe_toReal hx.ne⟩
  constructor
  · intro hf
    obtain ⟨y, hym, hy⟩ := hf.2.exists_castaingRepresentation hf.1
    refine ⟨fun ν t ↦ (y ν t).1, fun ν ↦ measurable_fst.comp (hym ν),
      fun ν ↦ hf.measurable_comp (measurable_fst.comp (hym ν)), fun t x₀ hx₀ ↦ ?_⟩
    obtain ⟨α, hα⟩ := hreal _ x₀ hx₀
    have hdom : t ∈ svDom (epiMapping f) := ⟨(x₀, α), hα⟩
    have hmem : (x₀, α) ∈ closure (range fun n ↦ y n t) := by
      rw [← hy t hdom]
      exact hα
    rw [Metric.mem_closure_iff] at hmem ⊢
    intro ε hε
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hmem ε hε
    have hyS : y n t ∈ epiMapping f t := by
      rw [hy t hdom]
      exact subset_closure ⟨n, rfl⟩
    refine ⟨(y n t).1, ⟨⟨n, rfl⟩, lt_of_le_of_lt hyS (EReal.coe_lt_top _)⟩, ?_⟩
    calc dist x₀ (y n t).1 ≤ dist ((x₀, α) : E × ℝ) (y n t) := by
          rw [Prod.dist_eq]
          exact le_max_left _ _
      _ < ε := hn
  · rintro ⟨x, hxm, ha, hb⟩
    have hSc : ∀ t, IsClosed (epiMapping f t) := fun t ↦
      (lsc_iff_epigraph_closed_ereal _).1 (hlsc t)
    refine ⟨hSc, ?_⟩
    let e : ℕ ≃ ℕ × ℚ := (Denumerable.eqv (ℕ × ℚ)).symm
    refine ((castaing_representations hSc).2).2 ⟨?_, fun n t ↦ (x (e n).1 t, ((e n).2 : ℝ)),
      fun n ↦ (hxm _).prodMk measurable_const, fun n ↦ ?_, fun t ↦ ?_⟩
    · have heq : svDom (epiMapping f) = ⋃ ν, {t | f t (x ν t) < ⊤} := by
        ext t
        simp only [mem_iUnion, mem_setOf_eq]
        constructor
        · rintro ⟨⟨x₀, α⟩, hx₀⟩
          have hx₀D : x₀ ∈ effectiveDomain (f t) := lt_of_le_of_lt hx₀ (EReal.coe_lt_top α)
          obtain ⟨_, -, ⟨ν, rfl⟩, hν⟩ := mem_closure_iff_nhds.1 (hb t hx₀D) univ univ_mem
          exact ⟨ν, hν⟩
        · rintro ⟨ν, hν⟩
          obtain ⟨α, hα⟩ := hreal _ _ hν
          exact ⟨(x ν t, α), hα⟩
      rw [heq]
      exact MeasurableSet.iUnion fun ν ↦ measurableSet_lt (ha ν) measurable_const
    · show MeasurableSet {t | f t (x (e n).1 t) ≤ (((e n).2 : ℝ) : EReal)}
      exact measurableSet_le (ha _) measurable_const
    · intro p hp
      have hdense := epigraph_subset_closure_of_dense (hconv t)
        (Q := (range fun ν ↦ x ν t) ∩ effectiveDomain (f t)) inter_subset_right (hb t) hp
      refine closure_minimal (fun q hq ↦ ?_) isClosed_closure hdense
      obtain ⟨⟨⟨ν, hν⟩, -⟩, hfq⟩ := hq
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show q.2 < q.2 + ε / 2 by linarith)
      refine ⟨(q.1, (r : ℝ)), ⟨?_, e.symm (ν, r), ?_⟩, ?_⟩
      · show f t q.1 ≤ ((r : ℝ) : EReal)
        exact hfq.trans (EReal.coe_le_coe_iff.2 hr1.le)
      · simp only [Equiv.apply_symm_apply, hν]
      · show max (dist q.1 q.1) (dist q.2 (r : ℝ)) < ε
        rw [dist_self, Real.dist_eq]
        refine max_lt hε ?_
        rw [abs_lt]
        constructor <;> linarith

/-- **Proposition 14.39**, the simpler test: when `int D_f(t) ≠ ∅` whenever `D_f(t) ≠ ∅`, an lsc
convex integrand is normal if and only if `f(t, x)` is measurable in `t` for each `x`. -/
theorem normality_test_for_convex_integrands_of_interior {f : T → E → EReal}
    (hlsc : ∀ t, LowerSemicontinuous (f t)) (hconv : ∀ t, Convex ℝ (epigraph (f t)))
    (hint : ∀ t, (effectiveDomain (f t)).Nonempty → (interior (effectiveDomain (f t))).Nonempty) :
    IsNormalIntegrand f ↔ ∀ x, Measurable fun t ↦ f t x := by
  refine ⟨fun hf ↦ hf.measurable_apply, fun hm ↦ ?_⟩
  rw [normality_test_for_convex_integrands hlsc hconv]
  set D := TopologicalSpace.denseSeq E
  have hD := TopologicalSpace.denseRange_denseSeq E
  refine ⟨fun ν _ ↦ D ν, fun _ ↦ measurable_const, fun ν ↦ hm (D ν), fun t ↦ ?_⟩
  rcases (effectiveDomain (f t)).eq_empty_or_nonempty with h | h
  · rw [h]
    exact empty_subset _
  have hDc := convex_effectiveDomain_of_convex_epigraph (hconv t)
  calc effectiveDomain (f t) ⊆ closure (interior (effectiveDomain (f t))) := by
        rw [hDc.closure_interior_eq_closure_of_nonempty_interior (hint t h)]
        exact subset_closure
    _ ⊆ closure (closure (interior (effectiveDomain (f t)) ∩ range D)) :=
        closure_mono (hD.open_subset_closure_inter isOpen_interior)
    _ ⊆ closure ((range fun ν ↦ D ν) ∩ effectiveDomain (f t)) := by
        rw [closure_closure]
        exact closure_mono fun y hy ↦ ⟨hy.2, interior_subset hy.1⟩

/-- The interior condition in the simpler test of 14.39 cannot be dropped: `f(t, ·) = δ_{c(t)}`
with `c(t) = (t, 1_D(t))` for a non-Borel `D ⊆ ℝ` is lsc and convex in `x` and measurable in `t`
for each `x`, but is not a normal integrand. -/
theorem convex_normality_counterexample :
    ∃ f : ℝ → ℝ × ℝ → EReal, (∀ t, LowerSemicontinuous (f t)) ∧
      (∀ t, Convex ℝ (epigraph (f t))) ∧ (∀ x, Measurable fun t ↦ f t x) ∧
      ¬ IsNormalIntegrand f := by
  classical
  obtain ⟨D, hD⟩ := exists_not_measurableSet_real
  set c : ℝ → ℝ × ℝ := fun t ↦ (t, D.indicator (fun _ ↦ (1 : ℝ)) t)
  refine ⟨fun t ↦ indicatorVA {c t}, fun t ↦ ?_, fun t ↦ ?_, fun x ↦ ?_, fun hf ↦ ?_⟩
  · rw [lsc_iff_epigraph_closed_ereal, epigraph_indicatorVA]
    exact isClosed_singleton.prod isClosed_Ici
  · rw [epigraph_indicatorVA]
    exact (convex_singleton _).prod (convex_Ici 0)
  · by_cases hx : x = c x.1
    · have : (fun t ↦ indicatorVA {c t} x) = fun t ↦ if t = x.1 then 0 else ⊤ := by
        funext t
        simp only [indicatorVA, mem_singleton_iff]
        by_cases ht : t = x.1
        · subst ht
          simp [← hx]
        · rw [if_neg ht, if_neg]
          intro h
          exact ht (by rw [h])
      rw [this]
      exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const
    · have : (fun t ↦ indicatorVA {c t} x) = fun _ ↦ ⊤ := by
        funext t
        simp only [indicatorVA, mem_singleton_iff]
        rw [if_neg]
        intro h
        apply hx
        rw [h]
      rw [this]
      exact measurable_const
  · have hO : IsOpen (((univ : Set ℝ) ×ˢ Ioo (1 / 2 : ℝ) (3 / 2)) ×ˢ (univ : Set ℝ)) :=
      IsOpen.prod (IsOpen.prod isOpen_univ isOpen_Ioo) isOpen_univ
    have hm := hf.2 _ hO
    have heq : svPreimage (epiMapping fun t ↦ indicatorVA {c t})
        (((univ : Set ℝ) ×ˢ Ioo (1 / 2 : ℝ) (3 / 2)) ×ˢ (univ : Set ℝ)) = D := by
      ext t
      simp only [svPreimage, mem_setOf_eq, epiMapping, epigraph_indicatorVA]
      constructor
      · rintro ⟨⟨⟨a, b⟩, β⟩, ⟨hab, -⟩, ⟨-, hb⟩, -⟩
        rw [mem_singleton_iff] at hab
        simp only [c, Prod.mk.injEq] at hab
        have hb' : b ∈ Ioo (1 / 2 : ℝ) (3 / 2) := hb
        rw [hab.2] at hb'
        by_contra htD
        rw [indicator_of_notMem htD] at hb'
        norm_num at hb'
      · intro htD
        refine ⟨(c t, 0), ⟨mem_singleton _, self_mem_Ici⟩, ⟨mem_univ _, ?_⟩, mem_univ _⟩
        simp only [c, indicator_of_mem htD]
        norm_num
    rw [heq] at hm
    exact hD hm

/-- The book's own example after 14.28 (`exists_lsc_measurable_not_normal`) is convex in `x`:
`f(t, x) = 0` if `t = x ∈ D` and `∞` otherwise, for a non-Borel `D ⊆ ℝ`, is lsc and convex in `x`
(each `f(t, ·)` is the indicator of a set with at most one point) and measurable in `t` for each
`x`, but is not a normal integrand.  So the closing sentence of 14.39, "every lsc convex integrand
is a normal integrand", holds only within the scope of the preceding sentence
(`normality_test_for_convex_integrands_of_interior`). -/
theorem exists_lsc_convex_measurable_not_normal :
    ∃ f : ℝ → ℝ → EReal, (∀ t, LowerSemicontinuous (f t)) ∧
      (∀ t, Convex ℝ (epigraph (f t))) ∧ (∀ x, Measurable fun t ↦ f t x) ∧
      ¬ IsNormalIntegrand f := by
  classical
  obtain ⟨D, hD⟩ := exists_not_measurableSet_real
  set f : ℝ → ℝ → EReal := fun t x ↦ if t = x ∧ x ∈ D then 0 else ⊤ with hfdef
  have hind : ∀ t, f t = indicatorVA {x | t = x ∧ x ∈ D} := fun t ↦ by
    funext x
    simp only [hfdef, indicatorVA, mem_setOf_eq]
    split_ifs <;> rfl
  have hsub : ∀ t, ({x | t = x ∧ x ∈ D} : Set ℝ).Subsingleton := fun t ↦
    Set.subsingleton_singleton.anti fun x hx ↦ hx.1.symm
  have hnot : ¬ Measurable fun t ↦ f t t := by
    intro hm
    have : (fun t ↦ f t t) ⁻¹' {0} = D := by
      ext t
      simp [hfdef]
    exact hD (this ▸ hm (measurableSet_singleton 0))
  refine ⟨f, fun t ↦ ?_, fun t ↦ ?_, fun x ↦ ?_, fun hf ↦ hnot (hf.measurable_comp measurable_id)⟩
  · rw [hind t]
    exact lowerSemicontinuous_indicatorVA (hsub t).isClosed
  · rw [hind t, epigraph_indicatorVA]
    exact (hsub t).convex.prod (convex_Ici 0)
  · exact Measurable.ite ((measurableSet_singleton x).inter (MeasurableSet.const _))
      measurable_const measurable_const

end Proposition1439

end RW
