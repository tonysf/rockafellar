/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Approximation by simple integrands

Exercise 14.55 of Rockafellar–Wets.  A simple integrand is measurable in `t`, has finitely
many values, and `rge D_f = ⋃_t dom f(t, ·)` is finite.  Approximants of a normal integrand are
the lower envelopes `fν(t, ·)` of the finite sets `Dν ∩ (S_f(t) + ν⁻¹ IB)` (as in 14.22), whose
epigraphs `Sν(t) + ({0} × ℝ₊)` converge to `S_f(t)`.
-/

import RockafellarWets.Chapter14.IntegrandOperations
import RockafellarWets.Chapter14.MeasurableLimits

open Set Filter Topology Metric TopologicalSpace
open scoped ENNReal NNReal

noncomputable section

namespace RW

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A **simple integrand**: measurable in `t`, with finitely many values and finite
`rge D_f = ⋃_t dom f(t, ·)`. -/
def IsSimpleIntegrand (f : T → E → EReal) : Prop :=
  (⋃ t, effectiveDomain (f t)).Finite ∧ (range (Function.uncurry f)).Finite ∧
    ∀ x, Measurable fun t ↦ f t x

/-- **Exercise 14.55**, first part: every simple integrand is a normal integrand. -/
theorem IsSimpleIntegrand.isNormalIntegrand {f : T → E → EReal} (hf : IsSimpleIntegrand f) :
    IsNormalIntegrand f := by
  obtain ⟨hF, -, hmeas⟩ := hf
  set F := ⋃ t, effectiveDomain (f t)
  refine measurability_of_level_set_mappings.2 fun α ↦ ?_
  have hsub : ∀ t, {x | f t x ≤ α} ⊆ F := fun t x hx ↦
    mem_iUnion.2 ⟨t, lt_of_le_of_lt hx (EReal.coe_lt_top α)⟩
  refine ⟨fun t ↦ (hF.subset (hsub t)).isClosed, fun O _ ↦ ?_⟩
  have : svPreimage (fun t ↦ {x | f t x ≤ α}) O = ⋃ x ∈ F ∩ O, {t | f t x ≤ α} := by
    ext t
    simp only [mem_svPreimage, mem_iUnion, mem_inter_iff, mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨x, hx, hxO⟩
      exact ⟨x, ⟨hsub t hx, hxO⟩, hx⟩
    · rintro ⟨x, ⟨-, hxO⟩, hx⟩
      exact ⟨x, hx, hxO⟩
  rw [this]
  exact MeasurableSet.biUnion (hF.subset inter_subset_left).countable fun x _ ↦
    measurableSet_le (hmeas x) measurable_const

section Approximation

/-- The lower envelope of the vertical fibers of a set `A ⊂ ℝⁿ × ℝ`. -/
def fiberInf (A : Set (E × ℝ)) (x : E) : EReal := ⨅ a ∈ {a : ℝ | (x, a) ∈ A}, (a : EReal)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem fiberInf_le_coe_iff_of_finite {A : Set (E × ℝ)} (hA : A.Finite) (x : E) (β : ℝ) :
    fiberInf A x ≤ β ↔ ∃ α : ℝ, α ≤ β ∧ (x, α) ∈ A := by
  constructor
  · intro h
    have hfin : {a : ℝ | (x, a) ∈ A}.Finite :=
      (hA.image Prod.snd).subset fun a ha ↦ ⟨(x, a), ha, rfl⟩
    rcases {a : ℝ | (x, a) ∈ A}.eq_empty_or_nonempty with he | hne
    · simp [fiberInf, he] at h
    · obtain ⟨a₀, ha₀, hmin⟩ := Set.exists_min_image _ id hfin hne
      refine ⟨a₀, ?_, ha₀⟩
      have heq : fiberInf A x = a₀ := by
        refine le_antisymm (iInf₂_le a₀ ha₀) (le_iInf₂ fun a ha ↦ EReal.coe_le_coe_iff.2 ?_)
        exact hmin a ha
      rw [heq] at h
      exact EReal.coe_le_coe_iff.1 h
  · rintro ⟨α, hαβ, hα⟩
    exact (iInf₂_le α hα).trans (EReal.coe_le_coe_iff.2 hαβ)


omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem fiberInf_mem_of_finite {A : Set (E × ℝ)} (hA : A.Finite) (x : E) :
    fiberInf A x ∈ insert ⊤ ((fun p : E × ℝ ↦ (p.2 : EReal)) '' A) := by
  have hfin : {a : ℝ | (x, a) ∈ A}.Finite :=
    (hA.image Prod.snd).subset fun a ha ↦ ⟨(x, a), ha, rfl⟩
  rcases {a : ℝ | (x, a) ∈ A}.eq_empty_or_nonempty with he | hne
  · left
    simp [fiberInf, he]
  · right
    obtain ⟨a₀, ha₀, hmin⟩ := Set.exists_min_image _ id hfin hne
    refine ⟨(x, a₀), ha₀, ?_⟩
    exact le_antisymm (le_iInf₂ fun a ha ↦ EReal.coe_le_coe_iff.2 (hmin a ha)) (iInf₂_le a₀ ha₀)

variable [MeasurableSpace E] [BorelSpace E]

/-- **Exercise 14.55 (approximation by simple integrands)**: an integrand is normal if and only if
it is, for every `t`, the epi-limit of a sequence of simple integrands. -/
theorem approximation_by_simple_integrands {f : T → E → EReal} :
    IsNormalIntegrand f ↔ ∃ g : ℕ → T → E → EReal, (∀ n, IsSimpleIntegrand (g n)) ∧
      ∀ t, EpiConverges (fun n ↦ g n t) (f t) := by
  constructor
  · intro hf
    set r : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hr
    have hrpos : ∀ n, 0 < r n := fun n ↦ by positivity
    have hrt : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hnet : ∀ n : ℕ, ∃ D ⊆ closedBall (0 : E × ℝ) n, D.Finite ∧
        closedBall (0 : E × ℝ) n ⊆ ⋃ z ∈ D, ball z (r n) :=
      fun n ↦ finite_cover_balls_of_compact (isCompact_closedBall _ _) (hrpos n)
    choose D hDsub hDfin hDcover using hnet
    set A : ℕ → T → Set (E × ℝ) := fun n t ↦ D n ∩ Metric.cthickening (r n) (epigraph (f t))
      with hAdef
    have hAfin : ∀ n t, (A n t).Finite := fun n t ↦ (hDfin n).subset inter_subset_left
    have hepi : ∀ n t, epigraph (fiberInf (A n t)) = {p : E × ℝ | ∃ α : ℝ, α ≤ p.2 ∧ (p.1, α) ∈ A n t} := by
      intro n t
      ext ⟨x, β⟩
      exact fiberInf_le_coe_iff_of_finite (hAfin n t) x β
    have hmemA : ∀ n t p, p ∈ A n t ↔ p ∈ D n ∧ infEDist p (epigraph (f t)) ≤ ENNReal.ofReal (r n) :=
      fun n t p ↦ Iff.rfl
    refine ⟨fun n t ↦ fiberInf (A n t), fun n ↦ ⟨?_, ?_, fun x ↦ ?_⟩, fun t ↦ ?_⟩
    · -- finite domain range
      refine ((hDfin n).image Prod.fst).subset (iUnion_subset fun t x hx ↦ ?_)
      obtain ⟨β, hβ⟩ : ∃ β : ℝ, fiberInf (A n t) x ≤ β := by
        have hx' : fiberInf (A n t) x < ⊤ := hx
        induction h : fiberInf (A n t) x with
        | bot => exact ⟨0, bot_le⟩
        | coe a => exact ⟨a, le_rfl⟩
        | top => rw [h] at hx'; exact absurd hx' (lt_irrefl _)
      obtain ⟨α, -, hα⟩ := (fiberInf_le_coe_iff_of_finite (hAfin n t) x β).1 hβ
      exact ⟨(x, α), hα.1, rfl⟩
    · -- finite range of values
      refine ((((hDfin n).image fun p : E × ℝ ↦ (p.2 : EReal))).insert ⊤).subset ?_
      rintro _ ⟨⟨t, x⟩, rfl⟩
      rcases fiberInf_mem_of_finite (hAfin n t) x with h | ⟨p, hp, hpe⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, hp.1, hpe⟩
    · -- measurability in t
      refine measurable_ereal_of_le_coe fun β ↦ ?_
      have : {t | fiberInf (A n t) x ≤ β} = ⋃ p ∈ {p ∈ D n | p.1 = x ∧ p.2 ≤ β},
          {t | infEDist p (epigraph (f t)) ≤ ENNReal.ofReal (r n)} := by
        ext t
        simp only [mem_setOf_eq, fiberInf_le_coe_iff_of_finite (hAfin n t), mem_iUnion,
          exists_prop]
        constructor
        · rintro ⟨α, hαβ, hα⟩
          exact ⟨(x, α), ⟨hα.1, rfl, hαβ⟩, hα.2⟩
        · rintro ⟨⟨y, α⟩, ⟨hpD, rfl, hαβ⟩, hpe⟩
          exact ⟨α, hαβ, hpD, hpe⟩
      rw [this]
      exact MeasurableSet.biUnion ((hDfin n).subset (sep_subset _ _)).countable fun p _ ↦
        measurableSet_le (hf.2.measurable_infEDist p) measurable_const
    · -- epi-convergence
      change PKConverges (fun n ↦ epigraph (fiberInf (A n t))) (epigraph (f t))
      refine pkConverges_of_outer_subset_of_subset_inner ?_ ?_
      · intro q hq
        rw [← (hf.1 t).closure_eq, Metric.mem_closure_iff]
        intro ε hε
        have hfreq := hq (ball q (ε / 3)) (ball_mem_nhds q (by positivity))
        have hev : ∀ᶠ n in atTop, r n < ε / 3 := hrt.eventually (gt_mem_nhds (by positivity))
        obtain ⟨n, ⟨⟨y, γ⟩, hyγ, hyq⟩, hrn⟩ := (hfreq.and_eventually hev).exists
        have hyγ' : ((y, γ) : E × ℝ) ∈ epigraph (fiberInf (A n t)) := hyγ
        rw [hepi n t] at hyγ'
        obtain ⟨α, hαγ, hα⟩ := hyγ'
        have hth : ((y, α) : E × ℝ) ∈ thickening (ε / 3) (epigraph (f t)) :=
          cthickening_subset_thickening' (by positivity) hrn _ hα.2
        obtain ⟨⟨y', α'⟩, hy'α', hdist⟩ := mem_thickening_iff.1 hth
        have hdist' := hdist
        rw [Prod.dist_eq] at hdist'
        have h1 : dist y y' < ε / 3 := lt_of_le_of_lt (le_max_left _ _) hdist'
        have h2 : dist α α' < ε / 3 := lt_of_le_of_lt (le_max_right _ _) hdist'
        have hyq' := hyq
        rw [mem_ball, Prod.dist_eq] at hyq'
        have h3 : dist y q.1 < ε / 3 := lt_of_le_of_lt (le_max_left _ _) hyq'
        have h4 : dist γ q.2 < ε / 3 := lt_of_le_of_lt (le_max_right _ _) hyq'
        refine ⟨(y', γ + ε / 3), ?_, ?_⟩
        · change f t y' ≤ ((γ + ε / 3 : ℝ) : EReal)
          have : α' ≤ γ + ε / 3 := by
            rw [Real.dist_eq, abs_lt] at h2
            linarith
          exact (show f t y' ≤ α' from hy'α').trans (EReal.coe_le_coe_iff.2 this)
        · rw [Prod.dist_eq, max_lt_iff]
          constructor
          · calc dist q.1 y' ≤ dist q.1 y + dist y y' := dist_triangle _ _ _
              _ < ε / 3 + ε / 3 := by rw [dist_comm] at h3; linarith
              _ < ε := by linarith
          · rw [Real.dist_eq, abs_lt] at h4 ⊢
            constructor <;> linarith
      · intro q hq
        rw [mem_innerSetLimit_iff_eventually_ball]
        intro ε hε
        obtain ⟨N, hN⟩ := exists_nat_ge (dist q 0)
        filter_upwards [hrt.eventually (gt_mem_nhds hε), eventually_ge_atTop N] with n hrn hn
        have hqball : q ∈ closedBall (0 : E × ℝ) n := by
          rw [mem_closedBall]
          exact hN.trans (by exact_mod_cast hn)
        obtain ⟨z, hzD, hqz⟩ := mem_iUnion₂.1 (hDcover n hqball)
        have hqz' : dist q z < r n := hqz
        refine ⟨z, ?_, ?_⟩
        · show z ∈ epigraph (fiberInf (A n t))
          rw [hepi n t]
          refine ⟨z.2, le_rfl, hzD, ?_⟩
          exact mem_cthickening_of_dist_le z q (r n) _ hq (by rw [dist_comm]; exact hqz'.le)
        · rw [mem_ball, dist_comm]
          linarith
  · rintro ⟨g, hg, hconv⟩
    exact IsNormalIntegrand.of_epiConverges (fun n ↦ (hg n).isNormalIntegrand) hconv

end Approximation

end RW
