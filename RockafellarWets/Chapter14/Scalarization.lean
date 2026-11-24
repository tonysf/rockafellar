/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Scalarization of normal integrands

Proposition 14.40 (scalarization of normal integrands) and Corollary 14.41 (alternative
interpretation of normality) of Rockafellar–Wets.  For `D ⊂ ℝⁿ`, `p_D(t) = inf_{x ∈ D} f(t, x)`
is `infOn (f t) D`.  Rational balls have centers in a countable dense family and positive
rational radii.  Following the remark after 14.40, normality follows from measurability of
`p_D` for any family of sets `D` providing a neighborhood base at every point; the countable
reduction uses the Lindelöf property of `ℝⁿ × ℝ`.
-/

import RockafellarWets.Chapter14.IntegrandExamples

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Classical

noncomputable section

namespace RW

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- `p_D = inf_{x ∈ D} g(x)`. -/
def infOn (g : E → EReal) (D : Set E) : EReal := ⨅ x ∈ D, g x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem infOn_eq_iInf_ite (g : E → EReal) (D : Set E) :
    infOn g D = ⨅ x, if x ∈ D then g x else ⊤ := by
  refine le_antisymm (le_iInf fun x ↦ ?_) (le_iInf₂ fun x hx ↦ ?_)
  · split_ifs with hx
    · exact iInf₂_le x hx
    · exact le_top
  · have := iInf_le (fun x ↦ if x ∈ D then g x else ⊤) x
    simpa [hx] using this

omit [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- `{t | p_D(t) < b} = S_f⁻¹(D × (a, b))` for `a < b`. -/
theorem svPreimage_epiMapping_prod_Ioo [TopologicalSpace E] (g : T → E → EReal) (D : Set E) {a b : ℝ}
    (hab : a < b) :
    svPreimage (epiMapping g) (D ×ˢ Ioo a b) = {t | infOn (g t) D < b} := by
  ext t
  simp only [mem_svPreimage, mem_setOf_eq]
  constructor
  · rintro ⟨⟨x, γ⟩, hxγ, hxD, hγ⟩
    have h1 : g t x ≤ γ := hxγ
    exact lt_of_le_of_lt ((iInf₂_le x hxD).trans h1) (EReal.coe_lt_coe_iff.2 hγ.2)
  · intro h
    obtain ⟨x, hx⟩ := iInf_lt_iff.1 h
    obtain ⟨hxD, hxb⟩ := iInf_lt_iff.1 hx
    have hmax : max (g t x) (a : EReal) < b := max_lt hxb (EReal.coe_lt_coe_iff.2 hab)
    obtain ⟨γ, hγ1, hγ2⟩ := EReal.exists_between_coe_real hmax
    refine ⟨(x, γ), (le_max_left _ _).trans hγ1.le, hxD,
      EReal.coe_lt_coe_iff.1 ((le_max_right _ _).trans_lt hγ1), EReal.coe_lt_coe_iff.1 hγ2⟩

/-- The scalarization criterion behind 14.40 and 14.41: an integrand that is lsc in `x` is normal
as soon as `p_D` is measurable for every member `D` of a family of sets providing, at every
point, neighborhoods containing the point in their interior. -/
theorem isNormalIntegrand_of_measurable_infOn {f : T → E → EReal}
    (hlsc : ∀ t, LowerSemicontinuous (f t)) (N : E → Set (Set E))
    (hN : ∀ x, ∀ U ∈ 𝓝 x, ∃ D ∈ N x, D ⊆ U ∧ x ∈ interior D)
    (hmeas : ∀ x, ∀ D ∈ N x, Measurable fun t ↦ infOn (f t) D) : IsNormalIntegrand f := by
  refine ⟨fun t ↦ (lsc_iff_epigraph_closed_ereal _).1 (hlsc t), fun O hO ↦ ?_⟩
  have hchoice : ∀ p : O, ∃ D ∈ N p.1.1, ∃ ε > 0,
      D ×ˢ Ioo (p.1.2 - ε) (p.1.2 + ε) ⊆ O ∧ p.1.1 ∈ interior D := by
    rintro ⟨⟨x, γ⟩, hp⟩
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 (hO.mem_nhds hp)
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
    obtain ⟨D, hD, hDU, hxD⟩ := hN x U hU
    refine ⟨D, hD, ε, hε, fun q hq ↦ hUV ⟨hDU hq.1, hεV ?_⟩, hxD⟩
    rw [Real.ball_eq_Ioo]
    exact hq.2
  choose D hD ε hε hsub hint using hchoice
  set V : O → Set (E × ℝ) := fun p ↦ interior (D p) ×ˢ Ioo (p.1.2 - ε p) (p.1.2 + ε p)
  have hVopen : ∀ p, IsOpen (V p) := fun p ↦ isOpen_interior.prod isOpen_Ioo
  obtain ⟨S, hScount, hSunion⟩ := isOpen_iUnion_countable V hVopen
  have hcover : O = ⋃ p ∈ S, D p ×ˢ Ioo (p.1.2 - ε p) (p.1.2 + ε p) := by
    apply Subset.antisymm
    · intro q hq
      have hq' : q ∈ ⋃ p, V p := mem_iUnion.2 ⟨⟨q, hq⟩, hint ⟨q, hq⟩, by
        simp only [mem_Ioo]
        constructor <;> linarith [hε ⟨q, hq⟩]⟩
      rw [← hSunion] at hq'
      obtain ⟨p, hpS, hqp⟩ := mem_iUnion₂.1 hq'
      exact mem_iUnion₂.2 ⟨p, hpS, interior_subset hqp.1, hqp.2⟩
    · exact iUnion₂_subset fun p _ ↦ hsub p
  rw [hcover]
  have : svPreimage (epiMapping f) (⋃ p ∈ S, D p ×ˢ Ioo (p.1.2 - ε p) (p.1.2 + ε p)) =
      ⋃ p ∈ S, {t | infOn (f t) (D p) < ((p.1.2 + ε p : ℝ) : EReal)} := by
    ext t
    simp only [mem_svPreimage, mem_iUnion, inter_iUnion, nonempty_iUnion, exists_prop]
    constructor
    · rintro ⟨p, hpS, hne⟩
      refine ⟨p, hpS, ?_⟩
      have := svPreimage_epiMapping_prod_Ioo f (D p) (by linarith [hε p] :
        p.1.2 - ε p < p.1.2 + ε p)
      rw [Set.ext_iff] at this
      exact (this t).1 hne
    · rintro ⟨p, hpS, hlt⟩
      refine ⟨p, hpS, ?_⟩
      have := svPreimage_epiMapping_prod_Ioo f (D p) (by linarith [hε p] :
        p.1.2 - ε p < p.1.2 + ε p)
      rw [Set.ext_iff] at this
      exact (this t).2 hlt
  rw [this]
  exact MeasurableSet.biUnion hScount fun p _ ↦
    (hmeas p.1.1 (D p) (hD p)) measurableSet_Iio

section Proposition1440

variable [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem infOn_iUnion {ι : Sort*} (g : E → EReal) (B : ι → Set E) :
    infOn g (⋃ i, B i) = ⨅ i, infOn g (B i) := by
  refine le_antisymm (le_iInf fun i ↦ le_iInf₂ fun x hx ↦ iInf₂_le x (mem_iUnion.2 ⟨i, hx⟩))
    (le_iInf₂ fun x hx ↦ ?_)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hx
  exact (iInf_le _ i).trans (iInf₂_le x hi)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Proposition 14.40 (scalarization of normal integrands)**.  For `f` lsc in `x` and any
countable dense family `d` (standing in for `ℚⁿ`), normality of `f` is equivalent to
measurability of all `p_D` for `D` in each of the collections (a) open sets, (b) open balls,
(c) rational open balls, (d) closed sets, (e) compact sets, (f) closed balls, (g) rational closed
balls. -/
theorem scalarization_of_normal_integrands {f : T → E → EReal}
    (hlsc : ∀ t, LowerSemicontinuous (f t)) {ι : Type*} [Countable ι] {d : ι → E}
    (hd : DenseRange d) :
    List.TFAE
      [IsNormalIntegrand f,
        ∀ O : Set E, IsOpen O → Measurable fun t ↦ infOn (f t) O,
        ∀ (x : E) (r : ℝ), 0 < r → Measurable fun t ↦ infOn (f t) (ball x r),
        ∀ (i : ι) (q : ℚ), 0 < q → Measurable fun t ↦ infOn (f t) (ball (d i) q),
        ∀ C : Set E, IsClosed C → Measurable fun t ↦ infOn (f t) C,
        ∀ K : Set E, IsCompact K → Measurable fun t ↦ infOn (f t) K,
        ∀ (x : E) (r : ℝ), 0 < r → Measurable fun t ↦ infOn (f t) (closedBall x r),
        ∀ (i : ι) (q : ℚ), 0 < q → Measurable fun t ↦ infOn (f t) (closedBall (d i) q)] := by
  tfae_have 1 → 5 := by
    intro hf C hC
    have h := (hf.restrict (svMeasurable_const C) (fun _ ↦ hC)).1.measurable_iInf
    have heq : (fun t ↦ infOn (f t) C) = fun t ↦ ⨅ x, if x ∈ C then f t x else ⊤ :=
      funext fun t ↦ infOn_eq_iInf_ite _ _
    rw [heq]
    convert h using 3 with t x
  tfae_have 5 → 6 := fun h K hK ↦ h K hK.isClosed
  tfae_have 6 → 7 := fun h x r _ ↦ h _ (isCompact_closedBall x r)
  tfae_have 7 → 8 := fun h i q hq ↦ h _ _ (by exact_mod_cast hq)
  tfae_have 8 → 2 := by
    intro h O hO
    have hO' : O = ⋃ p : ι × ℚ, ⋃ (_ : 0 < p.2 ∧ closedBall (d p.1) p.2 ⊆ O),
        closedBall (d p.1) p.2 := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨i, q, hq, hxb, hsub⟩ := exists_rat_ball_subset hd hO hx
        exact mem_iUnion₂.2 ⟨(i, q), ⟨hq, hsub⟩, ball_subset_closedBall hxb⟩
      · exact iUnion₂_subset fun p hp ↦ hp.2
    have heq : (fun t ↦ infOn (f t) O) = fun t ↦ ⨅ p : ι × ℚ,
        ⨅ (_ : 0 < p.2 ∧ closedBall (d p.1) p.2 ⊆ O), infOn (f t) (closedBall (d p.1) p.2) := by
      funext t
      conv_lhs => rw [hO']
      rw [infOn_iUnion]
      congr 1
      funext p
      rw [infOn_iUnion]
    rw [heq]
    exact Measurable.iInf fun p ↦ Measurable.iInf fun hp ↦ h _ _ hp.1
  tfae_have 2 → 3 := fun h x r _ ↦ h _ isOpen_ball
  tfae_have 3 → 4 := fun h i q hq ↦ h _ _ (by exact_mod_cast hq)
  tfae_have 4 → 1 := by
    intro h
    refine isNormalIntegrand_of_measurable_infOn hlsc
      (fun x ↦ {D | ∃ i, ∃ q : ℚ, 0 < q ∧ D = ball (d i) q}) (fun x U hU ↦ ?_) ?_
    · obtain ⟨i, q, hq, hxb, hsub⟩ := exists_rat_ball_subset hd isOpen_interior
        (mem_interior_iff_mem_nhds.2 hU)
      refine ⟨ball (d i) q, ⟨i, q, hq, rfl⟩, (ball_subset_closedBall.trans hsub).trans
        interior_subset, ?_⟩
      rw [isOpen_ball.interior_eq]
      exact hxb
    · rintro x _ ⟨i, q, hq, rfl⟩
      exact h i q hq
  tfae_finish

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Corollary 14.41 (alternative interpretation of normality)**: `f` is a normal integrand if
and only if (a) `f(t, x)` is lsc in `x` and (b) for each `x` there is `ε > 0` such that
`t ↦ inf {f(t, x') | x' ∈ IB(x, δ)}` is measurable for every `δ ∈ (0, ε)`. -/
theorem alternative_interpretation_of_normality {f : T → E → EReal} :
    IsNormalIntegrand f ↔ (∀ t, LowerSemicontinuous (f t)) ∧
      ∀ x : E, ∃ ε > 0, ∀ δ, 0 < δ → δ < ε →
        Measurable fun t ↦ infOn (f t) (closedBall x δ) := by
  constructor
  · intro hf
    refine ⟨hf.lowerSemicontinuous, fun x ↦ ⟨1, one_pos, fun δ hδ _ ↦ ?_⟩⟩
    have h := ((scalarization_of_normal_integrands hf.lowerSemicontinuous
      (TopologicalSpace.denseRange_denseSeq E)).out 0 6).1 hf
    · exact h x δ hδ
  · rintro ⟨hlsc, hb⟩
    choose ε hε hmeas using hb
    refine isNormalIntegrand_of_measurable_infOn hlsc
      (fun x ↦ {D | ∃ δ, 0 < δ ∧ δ < ε x ∧ D = closedBall x δ}) (fun x U hU ↦ ?_) ?_
    · obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
      set δ := min r (ε x) / 2 with hδdef
      have hmin : 0 < min r (ε x) := lt_min hr (hε x)
      have hδ : 0 < δ := by rw [hδdef]; positivity
      have hδr : δ < r := by
        have := min_le_left r (ε x)
        linarith
      have hδε : δ < ε x := by
        have := min_le_right r (ε x)
        have := hε x
        linarith
      refine ⟨closedBall x δ, ⟨δ, hδ, hδε, rfl⟩, (closedBall_subset_ball hδr).trans hrU, ?_⟩
      exact interior_mono ball_subset_closedBall (by rw [isOpen_ball.interior_eq]; exact mem_ball_self hδ)
    · rintro x _ ⟨δ, hδ, hδε, rfl⟩
      exact hmeas x δ hδ hδε

end Proposition1440

end RW
