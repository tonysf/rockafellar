/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Conjugate and support integrands

Theorem 14.50 (conjugate integrands), Example 14.51 (support integrands) and Exercise 14.52
(envelope representations through convexity) of Rockafellar–Wets.  The conjugate is taken in
the `x` argument with `t` fixed, `f*(t, ·) = fenchelConjugate (f t)`, formula 14(11).
-/

import RockafellarWets.Chapter14.IntegrandSums
import RockafellarWets.Chapter11.SupportConjugates
import RockafellarWets.Chapter11.FenchelMoreau
import RockafellarWets.Chapter11.ConjugateGeometry
import RockafellarWets.Chapter11.ConvexMarginalGeometry
import RockafellarWets.Chapter11.ConvexHullEpigraphClosure
import RockafellarWets.Chapter14.HullsAndPolars
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal Classical InnerProductSpace

noncomputable section

namespace RW

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Piecewise

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A normal integrand modified to `-∞` off a measurable set is still normal. -/
theorem IsNormalIntegrand.ite_bot {A : Set T} (hA : MeasurableSet A) {g : T → E → EReal}
    (hg : IsNormalIntegrand g) : IsNormalIntegrand (fun t x ↦ if t ∈ A then g t x else ⊥) := by
  have hepi : ∀ t, epigraph (fun x ↦ if t ∈ A then g t x else ⊥) =
      if t ∈ A then epiMapping g t else univ := by
    intro t
    split_ifs with h
    · rfl
    · ext p
      simp [epigraph]
  refine ⟨fun t ↦ by rw [hepi t]; split_ifs; exacts [hg.1 t, isClosed_univ], ?_⟩
  rw [show epiMapping (fun t x ↦ if t ∈ A then g t x else ⊥) = _ from funext hepi]
  exact SvMeasurable.ite hA hg.2 (svMeasurable_const _)

end Piecewise

section Theorem1450

/-- The affine integrands `t ↦ ⟪v(t), x⟫ - α(t)` of measurable `v`, `α` are Carathéodory. -/
theorem isCaratheodory_affine {v : T → E} (hv : Measurable v) {α : T → ℝ} (hα : Measurable α) :
    IsCaratheodory (fun t x ↦ ⟪v t, x⟫_ℝ - α t) :=
  ⟨fun _ ↦ (hv.inner measurable_const).sub hα,
    fun _ ↦ (continuous_const.inner continuous_id).sub continuous_const⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The conjugate as a supremum over a dense subset of the epigraph. -/
theorem fenchelConjugate_eq_iSup_of_dense {g : E → EReal}
    {z : ℕ → E × ℝ} (hz : epigraph g = _root_.closure (range z)) (v : E) :
    fenchelConjugate g v = ⨆ n, ((⟪(z n).1, v⟫_ℝ - (z n).2 : ℝ) : EReal) := by
  have hzmem : ∀ n, z n ∈ epigraph g := fun n ↦ hz ▸ subset_closure ⟨n, rfl⟩
  apply le_antisymm
  · set M := ⨆ n, ((⟪(z n).1, v⟫_ℝ - (z n).2 : ℝ) : EReal)
    have hcl : ∀ p ∈ epigraph g, ((⟪p.1, v⟫_ℝ - p.2 : ℝ) : EReal) ≤ M := by
      have hclosed : IsClosed {p : E × ℝ | ((⟪p.1, v⟫_ℝ - p.2 : ℝ) : EReal) ≤ M} :=
        isClosed_le (continuous_coe_real_ereal.comp
          ((continuous_fst.inner continuous_const).sub continuous_snd)) continuous_const
      intro p hp
      rw [hz] at hp
      exact closure_minimal (by rintro _ ⟨n, rfl⟩; exact le_iSup (fun n ↦
        ((⟪(z n).1, v⟫_ℝ - (z n).2 : ℝ) : EReal)) n) hclosed hp
    refine iSup_le fun x ↦ ?_
    induction h : g x with
    | bot =>
      rw [EReal.sub_bot (EReal.coe_ne_bot _), top_le_iff, EReal.eq_top_iff_forall_lt]
      intro y
      have hmem : ((x, ⟪v, x⟫_ℝ - (y + 1)) : E × ℝ) ∈ epigraph g := by
        change g x ≤ _
        rw [h]
        exact bot_le
      have := hcl _ hmem
      simp only [real_inner_comm x v, sub_sub_cancel] at this
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one y)) this
    | coe r =>
      have hmem : ((x, r) : E × ℝ) ∈ epigraph g := by
        change g x ≤ _
        rw [h]
      have := hcl _ hmem
      rw [← EReal.coe_sub]
      simpa [real_inner_comm x v] using this
    | top =>
      rw [EReal.sub_top]
      exact bot_le
  · refine iSup_le fun n ↦ ?_
    have h1 : g (z n).1 ≤ (z n).2 := hzmem n
    calc ((⟪(z n).1, v⟫_ℝ - (z n).2 : ℝ) : EReal)
        = (⟪v, (z n).1⟫_ℝ : EReal) - ((z n).2 : EReal) := by
          rw [real_inner_comm, EReal.coe_sub]
      _ ≤ (⟪v, (z n).1⟫_ℝ : EReal) - g (z n).1 := EReal.sub_le_sub le_rfl h1
      _ ≤ fenchelConjugate g v := le_fenchelConjugate g (z n).1 v

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem fenchelConjugate_eq_bot_of_epigraph_empty {g : E → EReal} (h : epigraph g = ∅) :
    fenchelConjugate g = fun _ ↦ ⊥ := by
  have htop : ∀ x, g x = ⊤ := by
    intro x
    by_contra hx
    obtain ⟨r, hr⟩ : ∃ r : ℝ, g x < r := by
      induction h' : g x with
      | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
      | coe a => exact ⟨a + 1, EReal.coe_lt_coe_iff.2 (lt_add_one a)⟩
      | top => exact absurd h' hx
    have : ((x, r) : E × ℝ) ∈ epigraph g := hr.le
    rw [h] at this
    exact this
  funext v
  refine le_antisymm (iSup_le fun x ↦ ?_) bot_le
  rw [htop x, EReal.sub_top]

/-- **Theorem 14.50 (conjugate integrands)**: the conjugate of a normal integrand is a normal
integrand, as the countable supremum of the affine integrands `⟪xν(t), v⟫ - αν(t)` of a
Castaing representation of `S_f` (and `-∞` off `dom S_f`). -/
theorem IsNormalIntegrand.fenchelConjugate {f : T → E → EReal} (hf : IsNormalIntegrand f) :
    IsNormalIntegrand (fun t ↦ RW.fenchelConjugate (f t)) := by
  obtain ⟨z, hz⟩ := hf.2.exists_castaingRepresentation hf.1
  have hdom := hf.2.measurableSet_svDom
  set g : ℕ → T → E → EReal := fun n t v ↦
    if t ∈ svDom (epiMapping f) then ((⟪(z n t).1, v⟫_ℝ - (z n t).2 : ℝ) : EReal) else ⊥
  have hg : ∀ n, IsNormalIntegrand (g n) := fun n ↦
    (isCaratheodory_affine (hz.1 n).fst (hz.1 n).snd).isNormalIntegrand.ite_bot hdom
  have heq : (fun t ↦ RW.fenchelConjugate (f t)) = fun t v ↦ ⨆ n, g n t v := by
    funext t v
    by_cases ht : t ∈ svDom (epiMapping f)
    · simp only [g, ht, if_true]
      exact fenchelConjugate_eq_iSup_of_dense (hz.2 t ht) v
    · simp only [g, ht, if_false, iSup_const]
      have hempty : epigraph (f t) = ∅ := not_nonempty_iff_eq_empty.1 ht
      rw [fenchelConjugate_eq_bot_of_epigraph_empty hempty]
  rw [heq]
  exact IsNormalIntegrand.iSup hg

/-- **Theorem 14.50 (conjugate integrands)**: the conjugate `f*` and biconjugate `f**` of a
normal integrand are normal integrands. -/
theorem conjugate_integrands {f : T → E → EReal} (hf : IsNormalIntegrand f) :
    IsNormalIntegrand (fun t ↦ RW.fenchelConjugate (f t)) ∧
      IsNormalIntegrand (fun t ↦ RW.fenchelConjugate (RW.fenchelConjugate (f t))) :=
  ⟨hf.fenchelConjugate, hf.fenchelConjugate.fenchelConjugate⟩

end Theorem1450


section Example1451

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem supportFunction_closure (D : Set E) [FiniteDimensional ℝ E] :
    supportFunction (_root_.closure D) = supportFunction D :=
  le_antisymm ((supportFunction_mono (closure_mono (subset_convexHull ℝ D))).trans_eq
    (supportFunction_closure_convexHull D)) (supportFunction_mono subset_closure)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem convex_epigraph_supportFunction (D : Set E) : Convex ℝ (epigraph (supportFunction D)) := by
  rw [← fenchelConjugate_indicatorVA]
  exact convex_epigraph_fenchelConjugate _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The support function of a nonempty bounded set is finite and Lipschitz. -/
theorem continuous_toReal_supportFunction {D : Set E} (hD : D.Nonempty)
    (hb : Bornology.IsBounded D) : Continuous fun v ↦ (supportFunction D v).toReal := by
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR _ hD.some_mem)
  obtain ⟨x₀, hx₀⟩ := hD
  have hfin : ∀ v, supportFunction D v ≠ ⊤ ∧ supportFunction D v ≠ ⊥ := by
    intro v
    refine ⟨?_, ?_⟩
    · refine ne_top_of_le_ne_top (EReal.coe_ne_top (R * ‖v‖)) ?_
      refine (supportFunction_le_iff _ _ _).2 fun x hx ↦ EReal.coe_le_coe_iff.2 ?_
      calc ⟪x, v⟫_ℝ ≤ ‖x‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ R * ‖v‖ := by gcongr; exact hR x hx
    · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (inner_le_supportFunction hx₀ v)
  have hlip : ∀ v w, (supportFunction D v).toReal ≤ (supportFunction D w).toReal + R * ‖v - w‖ := by
    intro v w
    have key : supportFunction D v ≤ ((supportFunction D w).toReal + R * ‖v - w‖ : ℝ) := by
      refine (supportFunction_le_iff _ _ _).2 fun x hx ↦ ?_
      have h1 : (⟪x, w⟫_ℝ : EReal) ≤ ((supportFunction D w).toReal : EReal) := by
        rw [EReal.coe_toReal (hfin w).1 (hfin w).2]
        exact inner_le_supportFunction hx w
      have h2 : ⟪x, v - w⟫_ℝ ≤ R * ‖v - w‖ :=
        (real_inner_le_norm _ _).trans (by gcongr; exact hR x hx)
      rw [EReal.coe_le_coe_iff] at h1 ⊢
      have : ⟪x, v⟫_ℝ = ⟪x, w⟫_ℝ + ⟪x, v - w⟫_ℝ := by
        rw [← inner_add_right, add_sub_cancel]
      linarith
    have := EReal.toReal_le_toReal key (hfin v).2 (EReal.coe_ne_top _)
    simpa using this
  refine (LipschitzWith.of_le_add_mul (Real.toNNReal R) fun v w ↦ ?_).continuous
  rw [Real.coe_toNNReal R hR0, dist_eq_norm]
  exact hlip v w

/-- **Example 14.51 (support integrands)**: (i) if `S` is measurable, `σ_S` is a convex normal
integrand; (ii) if `σ_S` is a normal integrand and `S` is closed-convex-valued, `S` is measurable;
(iii) for compact-convex-valued `S`, measurability of `S` is equivalent to measurability of
`t ↦ σ_S(t, v)` for every `v`. -/
theorem support_integrands {S : T → Set E} :
    (SvMeasurable S → IsNormalIntegrand (fun t ↦ supportFunction (S t)) ∧
        ∀ t, Convex ℝ (epigraph (supportFunction (S t)))) ∧
      (IsNormalIntegrand (fun t ↦ supportFunction (S t)) → (∀ t, IsClosed (S t)) →
        (∀ t, Convex ℝ (S t)) → SvMeasurable S) ∧
      ((∀ t, IsCompact (S t)) → (∀ t, Convex ℝ (S t)) →
        (SvMeasurable S ↔ ∀ v, Measurable fun t ↦ supportFunction (S t) v)) := by
  have hii : IsNormalIntegrand (fun t ↦ supportFunction (S t)) → (∀ t, IsClosed (S t)) →
      (∀ t, Convex ℝ (S t)) → SvMeasurable S := by
    intro hσ hc hconv
    have h := hσ.fenchelConjugate
    have heq : (fun t ↦ RW.fenchelConjugate (supportFunction (S t))) =
        fun t ↦ indicatorVA (S t) :=
      funext fun t ↦ fenchelConjugate_supportFunction_of_closed_convex (hconv t) (hc t)
    rw [heq] at h
    exact (isNormalIntegrand_indicatorVA_iff.1 h).2
  refine ⟨fun hS ↦ ⟨?_, fun t ↦ convex_epigraph_supportFunction _⟩, hii, fun hcpt hconv ↦ ?_⟩
  · have hδ : IsNormalIntegrand (fun t ↦ indicatorVA (_root_.closure (S t))) :=
      isNormalIntegrand_indicatorVA_iff.2 ⟨fun _ ↦ isClosed_closure, hS.closure⟩
    have h := hδ.fenchelConjugate
    have heq : (fun t ↦ RW.fenchelConjugate (indicatorVA (_root_.closure (S t)))) =
        fun t ↦ supportFunction (S t) := by
      funext t
      rw [fenchelConjugate_indicatorVA, supportFunction_closure]
    rwa [heq] at h
  · constructor
    · intro hS v
      have hσ : IsNormalIntegrand (fun t ↦ supportFunction (S t)) := by
        have hδ : IsNormalIntegrand (fun t ↦ indicatorVA (_root_.closure (S t))) :=
          isNormalIntegrand_indicatorVA_iff.2 ⟨fun _ ↦ isClosed_closure, hS.closure⟩
        have h := hδ.fenchelConjugate
        have heq : (fun t ↦ RW.fenchelConjugate (indicatorVA (_root_.closure (S t)))) =
            fun t ↦ supportFunction (S t) := by
          funext t
          rw [fenchelConjugate_indicatorVA, supportFunction_closure]
        rwa [heq] at h
      exact hσ.measurable_apply v
    · intro hmeas
      refine hii ?_ (fun t ↦ (hcpt t).isClosed) hconv
      have hT₁ : MeasurableSet {t | (S t).Nonempty} := by
        have : {t | (S t).Nonempty} = (fun t ↦ supportFunction (S t) 0) ⁻¹' {0} := by
          ext t
          simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff]
          constructor
          · exact fun h ↦ supportFunction_zero h
          · intro h
            by_contra hne
            rw [not_nonempty_iff_eq_empty] at hne
            rw [hne, supportFunction_empty] at h
            exact EReal.bot_ne_zero h
        rw [this]
        exact hmeas 0 (measurableSet_singleton 0)
      have hcar : IsCaratheodory (fun t v ↦ (supportFunction (S t) v).toReal) := by
        refine ⟨fun v ↦ (hmeas v).ereal_toReal, fun t ↦ ?_⟩
        rcases (S t).eq_empty_or_nonempty with he | hne
        · simp only [he, supportFunction_empty, EReal.toReal_bot]
          exact continuous_const
        · exact continuous_toReal_supportFunction hne (hcpt t).isBounded
      have h := hcar.isNormalIntegrand.ite_bot hT₁
      convert h using 2 with t
      funext v
      split_ifs with hne
      · have hfin1 : supportFunction (S t) v ≠ ⊤ := by
          obtain ⟨R, hR⟩ := (hcpt t).isBounded.exists_norm_le
          refine ne_top_of_le_ne_top (EReal.coe_ne_top (R * ‖v‖)) ?_
          refine (supportFunction_le_iff _ _ _).2 fun x hx ↦ EReal.coe_le_coe_iff.2 ?_
          calc ⟪x, v⟫_ℝ ≤ ‖x‖ * ‖v‖ := real_inner_le_norm _ _
            _ ≤ R * ‖v‖ := by gcongr; exact hR x hx
        have hfin2 : supportFunction (S t) v ≠ ⊥ :=
          ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (inner_le_supportFunction hne.some_mem v)
        exact (EReal.coe_toReal hfin1 hfin2).symm
      · rw [not_nonempty_iff_eq_empty.1 hne, supportFunction_empty]

end Example1451


section Exercise1452

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem convex_epigraph_affine (v : E) (α : ℝ) :
    Convex ℝ (epigraph (fun x : E ↦ ((⟪v, x⟫_ℝ - α : ℝ) : EReal))) := by
  have : epigraph (fun x : E ↦ ((⟪v, x⟫_ℝ - α : ℝ) : EReal)) =
      {p : E × ℝ | ⟪v, p.1⟫_ℝ - α ≤ p.2} := by
    ext p
    change ((⟪v, p.1⟫_ℝ - α : ℝ) : EReal) ≤ (p.2 : EReal) ↔ _
    exact EReal.coe_le_coe_iff
  rw [this]
  intro p hp q hq a b ha hb hab
  simp only [mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    inner_add_right, inner_smul_right, smul_eq_mul] at hp hq ⊢
  have h1 := mul_le_mul_of_nonneg_left hp ha
  have h2 := mul_le_mul_of_nonneg_left hq hb
  have h3 : a * α + b * α = α := by rw [← add_mul, hab, one_mul]
  nlinarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- A lsc convex function that never takes `-∞` is its own biconjugate. -/
theorem fenchelConjugate_fenchelConjugate_eq_of_ne_bot {g : E → EReal}
    (hl : LowerSemicontinuous g) (hc : Convex ℝ (epigraph g)) (hb : ∀ x, g x ≠ ⊥) :
    RW.fenchelConjugate (RW.fenchelConjugate g) = g := by
  by_cases hdom : ∃ x, g x < ⊤
  · exact fenchelConjugate_fenchelConjugate_eq ⟨hdom, fun x ↦ (hb x).bot_lt⟩ hl hc
  · push_neg at hdom
    have htop : g = fun _ ↦ ⊤ := funext fun x ↦ top_le_iff.1 (hdom x)
    have hempty : epigraph g = ∅ := by
      ext p
      simp [epigraph, htop]
    rw [fenchelConjugate_eq_bot_of_epigraph_empty hempty]
    funext x
    rw [htop]
    refine top_le_iff.1 (le_iSup_of_le 0 ?_)
    simp

/-- **Exercise 14.52(a) (envelope representations through convexity)**: a function that never
takes `-∞` is a convex normal integrand if and only if it is the supremum of countably many
affine integrands `⟪vν(t), x⟫ - αν(t)` with measurable `vν`, `αν`. -/
theorem envelope_representation_integrands {f : T → E → EReal} (hb : ∀ t x, f t x ≠ ⊥) :
    (IsNormalIntegrand f ∧ ∀ t, Convex ℝ (epigraph (f t))) ↔
      ∃ (v : ℕ → T → E) (α : ℕ → T → ℝ), (∀ n, Measurable (v n)) ∧ (∀ n, Measurable (α n)) ∧
        ∀ t x, f t x = ⨆ n, ((⟪v n t, x⟫_ℝ - α n t : ℝ) : EReal) := by
  constructor
  · rintro ⟨hf, hconv⟩
    have hf' := hf.fenchelConjugate
    obtain ⟨z, hz⟩ := hf'.2.exists_castaingRepresentation hf'.1
    refine ⟨fun n t ↦ (z n t).1, fun n t ↦ (z n t).2, fun n ↦ (hz.1 n).fst,
      fun n ↦ (hz.1 n).snd, fun t x ↦ ?_⟩
    have hdom : t ∈ svDom (epiMapping fun t ↦ RW.fenchelConjugate (f t)) := by
      by_cases hd : ∃ x, f t x < ⊤
      · obtain ⟨⟨v₀, hv₀⟩, -⟩ := isProper_fenchelConjugate_of_convex
          ⟨hd, fun x ↦ (hb t x).bot_lt⟩ (hconv t)
        obtain ⟨r, hr⟩ : ∃ r : ℝ, RW.fenchelConjugate (f t) v₀ < r := by
          induction h : RW.fenchelConjugate (f t) v₀ with
          | bot => exact ⟨0, EReal.bot_lt_coe 0⟩
          | coe a => exact ⟨a + 1, EReal.coe_lt_coe_iff.2 (lt_add_one a)⟩
          | top => rw [h] at hv₀; exact absurd hv₀ (lt_irrefl _)
        exact ⟨(v₀, r), hr.le⟩
      · push_neg at hd
        have htop : f t = fun _ ↦ ⊤ := funext fun x ↦ top_le_iff.1 (hd x)
        have hempty : epigraph (f t) = ∅ := by
          ext p
          simp [epigraph, htop]
        refine ⟨(0, 0), ?_⟩
        change RW.fenchelConjugate (f t) 0 ≤ ((0 : ℝ) : EReal)
        rw [fenchelConjugate_eq_bot_of_epigraph_empty hempty]
        exact bot_le
    have h := fenchelConjugate_eq_iSup_of_dense (hz.2 t hdom) x
    rw [fenchelConjugate_fenchelConjugate_eq_of_ne_bot (hf.lowerSemicontinuous t) (hconv t)
      (hb t)] at h
    exact h
  · rintro ⟨v, α, hv, hα, hf⟩
    have heq : f = fun t x ↦ ⨆ n, ((⟪v n t, x⟫_ℝ - α n t : ℝ) : EReal) :=
      funext fun t ↦ funext fun x ↦ hf t x
    rw [heq]
    refine ⟨IsNormalIntegrand.iSup fun n ↦ (isCaratheodory_affine (hv n) (hα n)).isNormalIntegrand,
      fun t ↦ ?_⟩
    rw [epigraph_iSup]
    exact convex_iInter fun n ↦ convex_epigraph_affine (v n t) (α n t)

/-- **Exercise 14.52(b)**: `S` is closed-convex-valued and measurable if and only if
`S(t) = {x | ⟪vν(t), x⟫ ≤ αν(t) for all ν}` for countably many measurable `vν`, `αν`. -/
theorem envelope_representation_mappings {S : T → Set E} :
    ((∀ t, IsClosed (S t)) ∧ (∀ t, Convex ℝ (S t)) ∧ SvMeasurable S) ↔
      ∃ (v : ℕ → T → E) (α : ℕ → T → ℝ), (∀ n, Measurable (v n)) ∧ (∀ n, Measurable (α n)) ∧
        ∀ t, S t = {x | ∀ n, ⟪v n t, x⟫_ℝ ≤ α n t} := by
  constructor
  · rintro ⟨hc, hconv, hm⟩
    have hδ : IsNormalIntegrand (fun t ↦ indicatorVA (S t)) :=
      isNormalIntegrand_indicatorVA_iff.2 ⟨hc, hm⟩
    have hδc : ∀ t, Convex ℝ (epigraph (indicatorVA (S t))) := fun t ↦ by
      rw [epigraph_indicatorVA]
      exact (hconv t).prod (convex_Ici 0)
    have hδb : ∀ t x, indicatorVA (S t) x ≠ ⊥ := fun t x ↦ by
      by_cases hx : x ∈ S t <;> simp [indicatorVA, hx]
    obtain ⟨v, α, hv, hα, hrep⟩ := (envelope_representation_integrands hδb).1 ⟨hδ, hδc⟩
    refine ⟨v, α, hv, hα, fun t ↦ ?_⟩
    ext x
    have h := hrep t x
    simp only [mem_setOf_eq]
    constructor
    · intro hx n
      rw [indicatorVA_apply_mem hx] at h
      have h1 : ((⟪v n t, x⟫_ℝ - α n t : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := by
        rw [EReal.coe_zero, h]
        exact le_iSup (fun n ↦ ((⟪v n t, x⟫_ℝ - α n t : ℝ) : EReal)) n
      have := EReal.coe_le_coe_iff.1 h1
      linarith
    · intro hx
      by_contra hxS
      rw [indicatorVA_apply_not_mem hxS] at h
      have hle : (⨆ n, ((⟪v n t, x⟫_ℝ - α n t : ℝ) : EReal)) ≤ 0 :=
        iSup_le fun n ↦ EReal.coe_le_coe_iff.2 (by linarith [hx n])
      rw [← h] at hle
      exact absurd hle (by simp)
  · rintro ⟨v, α, hv, hα, hS⟩
    have hhalf : ∀ n, (∀ t, IsClosed {x | ⟪v n t, x⟫_ℝ - α n t ∈ Iic (0 : ℝ)}) ∧
        SvMeasurable (fun t ↦ {x | ⟪v n t, x⟫_ℝ - α n t ∈ Iic (0 : ℝ)}) := fun n ↦
      (isCaratheodory_affine (hv n) (hα n)).svMeasurable_preimage
        (S := fun _ ↦ Iic (0 : ℝ)) (svMeasurable_const _) (fun _ ↦ isClosed_Iic)
    have hset : ∀ t, S t = ⋂ n, {x | ⟪v n t, x⟫_ℝ - α n t ∈ Iic (0 : ℝ)} := by
      intro t
      rw [hS t]
      ext x
      simp
    refine ⟨fun t ↦ by rw [hset t]; exact isClosed_iInter fun n ↦ (hhalf n).1 t,
      fun t ↦ ?_, ?_⟩
    · rw [hS t]
      refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab n ↦ ?_
      simp only [mem_setOf_eq] at hx hy
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      have h1 := mul_le_mul_of_nonneg_left (hx n) ha.le
      have h2 := mul_le_mul_of_nonneg_left (hy n) hb.le
      have h3 : a * α n t + b * α n t = α n t := by rw [← add_mul, hab, one_mul]
      linarith
    · rw [funext hset]
      exact SvMeasurable.iInter (fun n ↦ (hhalf n).2) fun n ↦ (hhalf n).1

end Exercise1452


section Exercise1449

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Exercise 14.49 (convexification of normal integrands)**: `g(t, ·) = cl con f(t, ·)` is a
normal integrand whenever `f` is (`S_g = cl con S_f`, by 14.12(a) and 14.2). -/
theorem IsNormalIntegrand.epiClosure_convexHullFunction
    {f : T → E → EReal} (hf : IsNormalIntegrand f) :
    IsNormalIntegrand (fun t ↦ epiClosure (convexHullFunction (f t))) := by
  have hepi : ∀ t, epigraph (epiClosure (convexHullFunction (f t))) =
      _root_.closure (_root_.convexHull ℝ (epiMapping f t)) := fun t ↦
    epigraph_epiClosure_convexHullFunction (f t)
  refine ⟨fun t ↦ by rw [hepi t]; exact isClosed_closure, ?_⟩
  rw [show epiMapping (fun t ↦ epiClosure (convexHullFunction (f t))) = _ from funext hepi]
  exact hf.2.convexHull.closure

end Exercise1449

end RW
