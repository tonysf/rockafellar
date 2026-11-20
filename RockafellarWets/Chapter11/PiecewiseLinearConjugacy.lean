/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 11: piecewise linear functions in conjugacy

**Theorem 11.14(a)**: a proper, lsc, convex `f` is piecewise linear iff `f*` is
(`isPiecewiseLinear_fenchelConjugate_iff`).  As in the book, a convex piecewise linear function
has a polyhedral epigraph (2.49, `IsPiecewiseLinear.hasPolyhedralEpigraph`); writing it with
finitely many point generators `(aᵢ, cᵢ)` and direction generators `(aⱼ, cⱼ)` (3.54) gives
`f*(v) = max_i (⟪v, aᵢ⟫ - cᵢ)` on the polyhedral set `{v | ⟪v, aⱼ⟫ ≤ cⱼ}` and `∞` off it
(`HasPolyhedralEpigraph.isPiecewiseLinear_fenchelConjugate`); the converse uses `f** = f`.

**Corollary 11.17** (polyhedral sets in duality): a nonempty closed convex set `C` is polyhedral
iff its support function `σ_C` is piecewise linear (`isPolyhedral_iff_isPiecewiseLinear_supportFunction`;
for `C = ∅` the support function is `-∞` everywhere, which is not piecewise linear although `∅`
is polyhedral), and a closed convex cone `K` is polyhedral iff its polar `K*` is
(`isPolyhedral_iff_isPolyhedral_polarCone`).  As in the book these specialize 11.14 to
`δ_C* = σ_C` and `δ_K* = δ_{K*}` (11.4), using that `δ_C` is piecewise linear iff `C` is
polyhedral.
-/

import RockafellarWets.Chapter10.ConvexPolyhedralUnions
import RockafellarWets.Chapter3.PolyhedralGeneration
import RockafellarWets.Chapter11.FenchelMoreau
import RockafellarWets.Chapter11.SupportConjugates
import RockafellarWets.Chapter10.DistanceSubsmoothness

open Set Filter
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A closed half-space `{x | ⟪a, x⟫ ≤ b}` is polyhedral. -/
theorem isPolyhedral_inner_le (a : E) (b : ℝ) : IsPolyhedral {x : E | ⟪a, x⟫_ℝ ≤ b} := by
  simpa using (IsHPolyhedral.halfspace (innerSL ℝ a) b).isPolyhedral

/-- **2.49** (one direction): a piecewise linear function with convex epigraph has a polyhedral
epigraph. -/
theorem IsPiecewiseLinear.hasPolyhedralEpigraph {f : E → EReal} (hf : IsPiecewiseLinear f)
    (hc : Convex ℝ (epigraph f)) : HasPolyhedralEpigraph f := by
  obtain ⟨m, C, a, b, hC, hdom, hval⟩ := hf
  set P : Fin m → Set (E × ℝ) := fun i ↦
    (Prod.fst ⁻¹' C i) ∩ {p | ⟪a i, p.1⟫_ℝ - p.2 ≤ -b i} with hPdef
  have hP : ∀ i, IsPolyhedral (P i) := fun i ↦ by
    have h1 : IsPolyhedral (Prod.fst ⁻¹' C i : Set (E × ℝ)) :=
      (hC i).linear_preimage (LinearMap.fst ℝ E ℝ)
    have h2 : IsPolyhedral {p : E × ℝ | ⟪a i, p.1⟫_ℝ - p.2 ≤ -b i} := by
      simpa using (IsHPolyhedral.halfspace (((innerSL ℝ (a i)).comp
        (ContinuousLinearMap.fst ℝ E ℝ)) - ContinuousLinearMap.snd ℝ E ℝ) (-b i)).isPolyhedral
    exact h1.inter h2
  have he : epigraph f = ⋃ i, P i := by
    ext ⟨x, α⟩
    rw [mem_epigraph_iff, mem_iUnion]
    constructor
    · intro hx
      have hxd : x ∈ effectiveDomain f := lt_of_le_of_lt hx (EReal.coe_lt_top α)
      rw [hdom] at hxd
      obtain ⟨i, hi⟩ := mem_iUnion.1 hxd
      refine ⟨i, hi, ?_⟩
      have h := hval i x hi
      rw [h, EReal.coe_le_coe_iff] at hx
      show ⟪a i, x⟫_ℝ - α ≤ -b i
      linarith
    · rintro ⟨i, hi, hle⟩
      have hle' : ⟪a i, x⟫_ℝ - α ≤ -b i := hle
      rw [hval i x hi, EReal.coe_le_coe_iff]
      linarith
  -- transport to the Euclidean product, where the convex-union lemma is stated
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ
  have hQ : ∀ i, IsPolyhedral (e.symm '' P i) := fun i ↦
    (hP i).linear_image e.symm.toLinearEquiv.toLinearMap
  have hU : (⋃ i, e.symm '' P i) = e.symm '' epigraph f := by
    rw [he, image_iUnion]
  have hUc : Convex ℝ (⋃ i, e.symm '' P i) := by
    rw [hU]
    exact hc.linear_image e.symm.toLinearEquiv.toLinearMap
  have hpoly := (isPolyhedral_iUnion_of_convex hQ hUc).linear_image e.toLinearEquiv.toLinearMap
  rw [hU, ← image_comp] at hpoly
  have hid : (⇑e.toLinearEquiv.toLinearMap ∘ ⇑e.symm) = id := by
    funext p
    exact e.apply_symm_apply p
  rw [hid, image_id] at hpoly
  exact hpoly

/-- The conjugate of a proper function with polyhedral epigraph is piecewise linear: from point
generators `(aᵢ, cᵢ)` and direction generators `(aⱼ, cⱼ)` of the epigraph,
`f*(v) = max_i (⟪v, aᵢ⟫ - cᵢ)` on `{v | ⟪v, aⱼ⟫ ≤ cⱼ}` and `f*(v) = ∞` elsewhere. -/
theorem HasPolyhedralEpigraph.isPiecewiseLinear_fenchelConjugate {f : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hp : IsProper f) :
    IsPiecewiseLinear (fenchelConjugate f) := by
  classical
  obtain ⟨s, t, hst⟩ := hasPolyhedralEpigraph_iff_hasFiniteEpigraphGeneratorFormula.mp hf
  have hray : ∀ p ∈ s, ∀ d ∈ t, ∀ r : ℝ, 0 ≤ r →
      f (p.1 + r • d.1) ≤ ((p.2 + r * d.2 : ℝ) : EReal) := by
    intro p hps d hd r hr
    rw [← mem_epigraph_iff]
    refine (hst (x := p.1 + r • d.1) (a := p.2 + r * d.2)).2
      ⟨fun q ↦ if q = p then 1 else 0, Finsupp.single d r, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro q _
      show 0 ≤ (if q = p then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · simp [hps]
    · intro q hq
      have h := Finsupp.support_single_subset hq
      rw [Finset.mem_singleton.1 h]
      exact Finset.mem_coe.2 hd
    · intro q
      rw [Finsupp.single_apply]
      split_ifs <;> linarith
    · simp [hps, Finsupp.sum_single_index]
    · simp [polyhedralGeneratorCost, hps, Finsupp.sum_single_index]
  have hgen : ∀ p ∈ s, f p.1 ≤ (p.2 : EReal) := by
    intro p hps
    rw [← mem_epigraph_iff]
    refine (hst (x := p.1) (a := p.2)).2
      ⟨fun q ↦ if q = p then 1 else 0, 0, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro q _
      show 0 ≤ (if q = p then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · simp [hps]
    · simp
    · intro q
      simp
    · simp [hps]
    · simp [polyhedralGeneratorCost, hps]
  have hs : s.Nonempty := by
    obtain ⟨x₀, hx₀⟩ := hp.1
    have hmem : (x₀, (f x₀).toReal) ∈ epigraph f := by
      rw [mem_epigraph_iff, EReal.coe_toReal hx₀.ne (hp.2 x₀).ne']
    obtain ⟨w, c, ⟨-, hw1, -⟩, -⟩ := hst.1 hmem
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hw1
    exact zero_ne_one hw1
  set M : E → ℝ := fun v ↦ s.sup' hs (fun p ↦ ⟪v, p.1⟫_ℝ - p.2) with hMdef
  set D : Set E := {v | ∀ d ∈ t, ⟪v, d.1⟫_ℝ ≤ d.2} with hDdef
  have hupper : ∀ v ∈ D, fenchelConjugate f v ≤ (M v : EReal) := by
    intro v hv
    rw [fenchelConjugate_le_iff]
    intro x
    by_cases hxt : f x = ⊤
    · rw [hxt]
      simp
    · have hfx : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hxt (hp.2 x).ne').symm
      set a := (f x).toReal with ha
      have hmem : (x, a) ∈ epigraph f := by rw [mem_epigraph_iff, hfx]
      obtain ⟨w, c, ⟨hw0, hw1, hcsub, hc0, hxeq⟩, hcost⟩ := hst.1 hmem
      rw [hfx, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      have hinner : ⟪v, x⟫_ℝ = ∑ p ∈ s, w p * ⟪v, p.1⟫_ℝ +
          ∑ d ∈ c.support, c d * ⟪v, d.1⟫_ℝ := by
        rw [← hxeq, inner_add_right, inner_sum, Finsupp.sum, inner_sum]
        simp [inner_smul_right]
      have hcost' : a = ∑ p ∈ s, w p * p.2 + ∑ d ∈ c.support, c d * d.2 := by
        rw [← hcost]
        rfl
      have h1 : ∑ p ∈ s, w p * (⟪v, p.1⟫_ℝ - p.2) ≤ M v := by
        calc ∑ p ∈ s, w p * (⟪v, p.1⟫_ℝ - p.2) ≤ ∑ p ∈ s, w p * M v :=
              Finset.sum_le_sum fun p hps ↦ mul_le_mul_of_nonneg_left
                (Finset.le_sup' (fun p ↦ ⟪v, p.1⟫_ℝ - p.2) hps) (hw0 p hps)
          _ = M v := by rw [← Finset.sum_mul, hw1, one_mul]
      have h2 : ∑ d ∈ c.support, c d * (⟪v, d.1⟫_ℝ - d.2) ≤ 0 :=
        Finset.sum_nonpos fun d hd ↦ mul_nonpos_of_nonneg_of_nonpos (hc0 d)
          (sub_nonpos.2 (hv d (hcsub (Finset.mem_coe.2 hd))))
      have h3 : ⟪v, x⟫_ℝ - a = ∑ p ∈ s, w p * (⟪v, p.1⟫_ℝ - p.2) +
          ∑ d ∈ c.support, c d * (⟪v, d.1⟫_ℝ - d.2) := by
        rw [hinner, hcost']
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring
      linarith
  have hlower : ∀ v, (M v : EReal) ≤ fenchelConjugate f v := by
    intro v
    obtain ⟨p, hps, hpM⟩ := Finset.exists_mem_eq_sup' hs (fun p ↦ ⟪v, p.1⟫_ℝ - p.2)
    have hMp : M v = ⟪v, p.1⟫_ℝ - p.2 := hpM
    rw [hMp]
    refine le_trans ?_ (le_fenchelConjugate f p.1 v)
    rw [EReal.coe_sub]
    exact EReal.sub_le_sub le_rfl (hgen p hps)
  have hout : ∀ v ∉ D, fenchelConjugate f v = ⊤ := by
    intro v hv
    simp only [hDdef, mem_setOf_eq, not_forall, not_le] at hv
    obtain ⟨d, hd, hlt⟩ := hv
    obtain ⟨p, hps⟩ := hs
    rw [EReal.eq_top_iff_forall_lt]
    intro y
    have hδ0 : 0 < ⟪v, d.1⟫_ℝ - d.2 := by linarith
    set r := max 0 ((y - (⟪v, p.1⟫_ℝ - p.2) + 1) / (⟪v, d.1⟫_ℝ - d.2)) with hr
    have hr0 : 0 ≤ r := le_max_left _ _
    have hrδ : y - (⟪v, p.1⟫_ℝ - p.2) + 1 ≤ r * (⟪v, d.1⟫_ℝ - d.2) := by
      have h := le_max_right 0 ((y - (⟪v, p.1⟫_ℝ - p.2) + 1) / (⟪v, d.1⟫_ℝ - d.2))
      rwa [← hr, div_le_iff₀ hδ0] at h
    have hval := hray p hps d hd r hr0
    calc (y : EReal) < ((⟪v, p.1 + r • d.1⟫_ℝ - (p.2 + r * d.2) : ℝ) : EReal) := by
          rw [EReal.coe_lt_coe_iff, inner_add_right, inner_smul_right]
          nlinarith
      _ ≤ (⟪v, p.1 + r • d.1⟫_ℝ : EReal) - f (p.1 + r • d.1) := by
          rw [EReal.coe_sub]
          exact EReal.sub_le_sub le_rfl hval
      _ ≤ fenchelConjugate f v := le_fenchelConjugate f _ v
  have hvalD : ∀ v ∈ D, fenchelConjugate f v = (M v : EReal) := fun v hv ↦
    le_antisymm (hupper v hv) (hlower v)
  set m := s.card
  let g : Fin m → E × ℝ := fun i ↦ (s.equivFin.symm i : E × ℝ)
  have hg : ∀ i, g i ∈ s := fun i ↦ (s.equivFin.symm i).2
  have hg_surj : ∀ p ∈ s, ∃ i, g i = p := fun p hps ↦
    ⟨s.equivFin ⟨p, hps⟩, by simp [g]⟩
  have hD : IsPolyhedral D := by
    have h := IsPolyhedral.iInter_finset t (fun d ↦ {v : E | ⟪d.1, v⟫_ℝ ≤ d.2})
      (fun d _ ↦ isPolyhedral_inner_le d.1 d.2)
    convert h using 1
    ext v
    simp [hDdef, real_inner_comm]
  refine ⟨m, fun i ↦ D ∩ {v | ∀ q ∈ s, ⟪v, q.1⟫_ℝ - q.2 ≤ ⟪v, (g i).1⟫_ℝ - (g i).2},
    fun i ↦ (g i).1, fun i ↦ -(g i).2, fun i ↦ ?_, ?_, ?_⟩
  · have h2 : IsPolyhedral {v : E | ∀ q ∈ s, ⟪v, q.1⟫_ℝ - q.2 ≤ ⟪v, (g i).1⟫_ℝ - (g i).2} := by
      have h := IsPolyhedral.iInter_finset s
        (fun q ↦ {v : E | ⟪q.1 - (g i).1, v⟫_ℝ ≤ q.2 - (g i).2})
        (fun q _ ↦ isPolyhedral_inner_le _ _)
      convert h using 1
      ext v
      simp only [mem_setOf_eq, mem_iInter]
      refine forall₂_congr fun q _ ↦ ?_
      rw [inner_sub_left, real_inner_comm q.1, real_inner_comm (g i).1]
      constructor <;> intro h <;> linarith
    exact hD.inter h2
  · ext v
    simp only [effectiveDomain, mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hlt
      have hvD : v ∈ D := by
        by_contra hvD
        rw [hout v hvD] at hlt
        exact lt_irrefl _ hlt
      obtain ⟨p, hps, hpM⟩ := Finset.exists_mem_eq_sup' hs (fun p ↦ ⟪v, p.1⟫_ℝ - p.2)
      obtain ⟨i, rfl⟩ := hg_surj p hps
      exact ⟨i, hvD, fun q hq ↦ by
        rw [← hpM]
        exact Finset.le_sup' (fun p ↦ ⟪v, p.1⟫_ℝ - p.2) hq⟩
    · rintro ⟨i, hvD, -⟩
      rw [hvalD v hvD]
      exact EReal.coe_lt_top _
  · rintro i v ⟨hvD, hvi⟩
    rw [hvalD v hvD, EReal.coe_eq_coe_iff]
    have hle : M v ≤ ⟪v, (g i).1⟫_ℝ - (g i).2 := Finset.sup'_le hs _ hvi
    have hge : ⟪v, (g i).1⟫_ℝ - (g i).2 ≤ M v :=
      Finset.le_sup' (fun p ↦ ⟪v, p.1⟫_ℝ - p.2) (hg i)
    rw [real_inner_comm]
    linarith

/-- **Theorem 11.14(a)** (piecewise linear functions in conjugacy): a proper, lsc, convex `f`
is piecewise linear if and only if `f*` is. -/
theorem isPiecewiseLinear_fenchelConjugate_iff {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    IsPiecewiseLinear (fenchelConjugate f) ↔ IsPiecewiseLinear f := by
  obtain ⟨hp', -, hc', hbi⟩ := fenchelConjugate_properties hp hl hc
  constructor
  · intro h
    have h' := (h.hasPolyhedralEpigraph hc').isPiecewiseLinear_fenchelConjugate hp'
    rwa [hbi] at h'
  · intro h
    exact (h.hasPolyhedralEpigraph hc).isPiecewiseLinear_fenchelConjugate hp

/-- The indicator of a set is piecewise linear iff the set is polyhedral (convex case). -/
theorem isPiecewiseLinear_indicatorVA_iff {C : Set E} (hc : Convex ℝ C) :
    IsPiecewiseLinear (indicatorVA C) ↔ IsPolyhedral C := by
  constructor
  · rintro ⟨m, D, a, b, hD, hdom, -⟩
    rw [effectiveDomain_indicatorVA] at hdom
    rw [hdom] at hc ⊢
    exact isPolyhedral_iUnion_of_convex hD hc
  · intro hC
    refine ⟨1, fun _ ↦ C, fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ hC, ?_, ?_⟩
    · rw [effectiveDomain_indicatorVA]
      ext x
      simp
    · intro _ x hx
      simp [indicatorVA, hx]

/-- **Corollary 11.17(a)**: a nonempty closed convex set is polyhedral iff its support function
is piecewise linear. -/
theorem isPolyhedral_iff_isPiecewiseLinear_supportFunction {C : Set E} (hne : C.Nonempty)
    (hcl : IsClosed C) (hc : Convex ℝ C) :
    IsPolyhedral C ↔ IsPiecewiseLinear (supportFunction C) := by
  have hcon : Convex ℝ (epigraph (indicatorVA C)) := by
    rw [epigraph_indicatorVA]
    exact hc.prod (convex_Ici _)
  rw [← fenchelConjugate_indicatorVA, isPiecewiseLinear_fenchelConjugate_iff
    (isProper_indicatorVA hne) (lowerSemicontinuous_indicatorVA hcl) hcon,
    isPiecewiseLinear_indicatorVA_iff hc]

/-- **Corollary 11.17(b)**: a closed convex cone is polyhedral iff its polar cone is. -/
theorem isPolyhedral_iff_isPolyhedral_polarCone {K : Set E} (hk : IsCone K) (hcl : IsClosed K)
    (hc : Convex ℝ K) : IsPolyhedral K ↔ IsPolyhedral (polarCone K) := by
  have hcon : Convex ℝ (epigraph (indicatorVA K)) := by
    rw [epigraph_indicatorVA]
    exact hc.prod (convex_Ici _)
  have hpc : Convex ℝ (polarCone K) := by
    intro u hu v hv a b ha hb hab w hw
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]
    nlinarith [hu w hw, hv w hw]
  rw [← isPiecewiseLinear_indicatorVA_iff hc, ← isPiecewiseLinear_indicatorVA_iff hpc,
    ← fenchelConjugate_indicatorVA_cone hk, isPiecewiseLinear_fenchelConjugate_iff
      (isProper_indicatorVA ⟨0, hk.1⟩) (lowerSemicontinuous_indicatorVA hcl) hcon]

end RW
