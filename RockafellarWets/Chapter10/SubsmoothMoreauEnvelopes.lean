/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: subsmoothness of Moreau envelopes

**Example 10.32**: let `f : E → ℝ̄` be proper, lsc and prox-bounded, and `0 < λ < λ_f`.  Then
`-e_λ f` is lower-`C^∞` on `E` (`neg_moreauEnvelope_isLowerCOn`), hence lower-`C²`,
semidifferentiable, strictly continuous and regular, and with `P = P_λ f`:

* `∂[-e_λ f](x̄) = con {λ⁻¹ (y - x̄) | y ∈ P(x̄)}` (`subdifferential_neg_moreauEnvelope`);
* `d[-e_λ f](x̄)(w) = λ⁻¹ max_{y ∈ P(x̄)} ⟪y - x̄, w⟫` (`subderivative_neg_moreauEnvelope`);
* `lip[-e_λ f](x̄) = λ⁻¹ max_{y ∈ P(x̄)} |y - x̄|` (`lipschitzModulus_neg_moreauEnvelope`);
* `∂[e_λ f](x̄) ⊂ {λ⁻¹ (x̄ - y) | y ∈ P(x̄)}` (`subdifferential_moreauEnvelope_subset`).

**Gap in the book's proof (repaired).**  The book represents `-e_λ f(x) = max_{y ∈ Y}
[-f(y) - (1/2λ)|y - x|²]` with `y` as the index; but for `f` only lsc, the term `-f(y)` does
not depend continuously on the index `y`, which Definition 10.29 requires (all derivatives of
order `≥ 1` do).  We index instead by the compact set of epigraph points `(y, β)` of `f` with
`|y| ≤ R` and `m ≤ β ≤ α` (`exists_moreau_representation`), using
`f_{(y, β)}(x) = -β - (1/2λ)|y - x|²`, which is jointly smooth in `(β, y, x)`; the maximum is
attained exactly at `(y, f(y))` with `y ∈ P_λ f(x)`.  The nonemptiness, local boundedness and
local upper bounds of 1.25 come from `paramArgmin_nonempty` and 5.23(b).
-/

import RockafellarWets.Chapter10.SubsmoothCalculus
import RockafellarWets.Chapter5.ProximalMappings
import RockafellarWets.Chapter5.OptimalSetMappings
import RockafellarWets.Chapter1.Semicontinuity

open Filter Function Metric Set Topology InnerProductSpace
open scoped NNReal ENNReal InnerProductSpace ContDiff

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {lam : ℝ}

/-- The real values of the Moreau envelope `e_λ f`. -/
noncomputable def moreauEnvelopeReal (f : E → EReal) (lam : ℝ) (x : E) : ℝ :=
  (moreauEnvelopeEReal f lam x).toReal

theorem proximalMappingEReal_nonempty_of_lt_proxThreshold (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hlam : 0 < lam) (hthr : (lam : EReal) < proxThreshold f)
    (x : E) : (proximalMappingEReal f lam x).Nonempty := by
  rw [← proxMappingEReal_eq_proximalMappingEReal, proxMappingEReal_eq_paramArgmin]
  exact paramArgmin_nonempty (lowerSemicontinuous_proxIntegrand hl lam) (isProper_proxIntegrand hp)
    (isLevelBoundedInXLocallyUniformly_proxIntegrand hlam hthr)
    (valueFunction_proxIntegrand_lt_top hp lam x)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- At a proximal point the envelope is finite and equals the proximal objective. -/
theorem moreauEnvelope_eq_of_mem_proximalMapping (hp : IsProper f) {x y : E}
    (hy : y ∈ proximalMappingEReal f lam x) :
    f y = ((f y).toReal : EReal) ∧
      moreauEnvelopeEReal f lam x = (((f y).toReal + (1 / (2 * lam)) * ‖y - x‖ ^ 2 : ℝ) : EReal) := by
  rw [mem_proximalMappingEReal_iff] at hy
  obtain ⟨heq, hlt⟩ := hy
  have hfy_bot : f y ≠ ⊥ := ne_of_gt (hp.2 y)
  have hfy_top : f y ≠ ⊤ := by
    intro h
    rw [← heq, proximalObjectiveEReal, h, EReal.top_add_coe] at hlt
    exact lt_irrefl _ hlt
  have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hfy_top hfy_bot).symm
  refine ⟨hfy, ?_⟩
  rw [← heq, proximalObjectiveEReal, hfy, EReal.toReal_coe, ← EReal.coe_add]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem moreauEnvelope_le (x w : E) :
    moreauEnvelopeEReal f lam x ≤ f w + (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal) :=
  iInf_le (fun w ↦ f w + (((1 / (2 * lam)) * ‖w - x‖ ^ 2 : ℝ) : EReal)) w

/-- The jointly smooth model `((β, y), x) ↦ -β - (1/2λ)|y - x|²`. -/
noncomputable def moreauModel (lam : ℝ) (q : (ℝ × E) × E) : ℝ :=
  -q.1.1 - (1 / (2 * lam)) * ‖q.1.2 - q.2‖ ^ 2

omit [FiniteDimensional ℝ E] in
theorem contDiff_moreauModel (lam : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (moreauModel (E := E) lam) := by
  unfold moreauModel
  exact (contDiff_fst.comp contDiff_fst).neg.sub (contDiff_const.mul
    (((contDiff_snd.comp contDiff_fst).sub contDiff_snd).norm_sq ℝ))

/-- The gradient of `x ↦ -β - (1/2λ)|y - x|²` is `λ⁻¹ (y - x)`. -/
theorem hasGradientAt_moreauModel (hlam : 0 < lam) (β : ℝ) (y x : E) :
    HasGradientAt (fun z ↦ moreauModel lam ((β, y), z)) (lam⁻¹ • (y - x)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun z : E ↦ y - z) (-ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_sub y
  have h2 := (h1.norm_sq.const_mul (1 / (2 * lam))).const_sub (-β)
  have hfun : (fun z ↦ moreauModel lam ((β, y), z)) =
      fun z ↦ -β - (1 / (2 * lam)) * ‖y - z‖ ^ 2 := rfl
  rw [hfun]
  convert h2 using 1
  ext w
  simp
  field_simp
  ring

/-- **Example 10.32** (representation): around each `x̄`, `-e_λ f` is the maximum of
`-β - (1/2λ)|y - x|²` over a compact set `T` of epigraph points `(y, β)` of `f`, attained at
`(y, f(y))` for `y ∈ P_λ f(x)`. -/
theorem exists_moreau_representation (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hlam : 0 < lam) (hthr : (lam : EReal) < proxThreshold f) (x₀ : E) :
    ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ ∃ T : Set (E × ℝ), IsCompact T ∧
      (∀ q ∈ T, f q.1 ≤ (q.2 : EReal)) ∧
      (∀ x ∈ V, ∀ y ∈ proximalMappingEReal f lam x, (y, (f y).toReal) ∈ T) ∧
      (∀ x ∈ V, ∀ q ∈ T,
        moreauModel lam ((q.2, q.1), x) ≤ -moreauEnvelopeReal f lam x) ∧
      ∀ x ∈ V, ∃ q ∈ T, moreauModel lam ((q.2, q.1), x) = -moreauEnvelopeReal f lam x := by
  obtain ⟨W₁, hW₁, hbdd⟩ := svLocallyBounded_proxMappingEReal hp hlam hthr x₀
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
  obtain ⟨α, hα⟩ := exists_eventually_valueFunction_proxIntegrand_le hp hlam x₀
  set R' := max R 0 with hR'
  have hY : (closedBall (0 : E) R').Nonempty := nonempty_closedBall.2 (le_max_right _ _)
  obtain ⟨a, -, hamin⟩ := (hl.lowerSemicontinuousOn _).exists_isMinOn hY (isCompact_closedBall 0 R')
  have hfa_bot : f a ≠ ⊥ := ne_of_gt (hp.2 a)
  obtain ⟨m, hm⟩ : ∃ m : ℝ, ∀ y ∈ closedBall (0 : E) R', (m : EReal) ≤ f y := by
    by_cases hfa : f a = ⊤
    · refine ⟨0, fun y hy ↦ ?_⟩
      have h1 := isMinOn_iff.1 hamin y hy
      rw [hfa] at h1
      exact le_top.trans h1
    · refine ⟨(f a).toReal, fun y hy ↦ ?_⟩
      rw [EReal.coe_toReal hfa hfa_bot]
      exact isMinOn_iff.1 hamin y hy
  set V := interior (W₁ ∩ {x | moreauEnvelopeEReal f lam x ≤ (α : EReal)}) with hVdef
  have hV : IsOpen V := isOpen_interior
  have hx₀V : x₀ ∈ V := mem_interior_iff_mem_nhds.2 (inter_mem hW₁ hα)
  set T : Set (E × ℝ) := (closedBall (0 : E) R' ×ˢ Icc m α) ∩ epigraph f with hTdef
  have hT : IsCompact T := ((isCompact_closedBall 0 R').prod isCompact_Icc).inter_right
    (isClosed_epigraph_of_lsc_ereal f hl)
  have hmemT : ∀ x ∈ V, ∀ y ∈ proximalMappingEReal f lam x, (y, (f y).toReal) ∈ T := by
    intro x hx y hy
    have hxW := (interior_subset hx).1
    have hxα : moreauEnvelopeEReal f lam x ≤ (α : EReal) := (interior_subset hx).2
    obtain ⟨hfy, he⟩ := moreauEnvelope_eq_of_mem_proximalMapping hp hy
    have hyR : y ∈ closedBall (0 : E) R' :=
      closedBall_subset_closedBall (le_max_left _ _) (hR (mem_svImage.2 ⟨x, hxW, hy⟩))
    refine ⟨⟨hyR, ?_, ?_⟩, ?_⟩
    · have h1 := hm y hyR
      rw [hfy] at h1
      exact EReal.coe_le_coe_iff.1 h1
    · rw [he, EReal.coe_le_coe_iff] at hxα
      have hd : 0 ≤ (1 / (2 * lam)) * ‖y - x‖ ^ 2 := by positivity
      linarith
    · show f y ≤ (((f y).toReal : ℝ) : EReal)
      rw [← hfy]
  refine ⟨V, hV, hx₀V, T, hT, fun q hq ↦ hq.2, hmemT, fun x hx q hq ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨y, hy⟩ := proximalMappingEReal_nonempty_of_lt_proxThreshold hp hl hlam hthr x
    obtain ⟨-, he⟩ := moreauEnvelope_eq_of_mem_proximalMapping hp hy
    have h1 := moreauEnvelope_le (f := f) (lam := lam) x q.1
    have h2 : f q.1 ≤ (q.2 : EReal) := hq.2
    have h3 : moreauEnvelopeEReal f lam x ≤ ((q.2 + (1 / (2 * lam)) * ‖q.1 - x‖ ^ 2 : ℝ) : EReal) := by
      refine h1.trans ?_
      rw [EReal.coe_add]
      exact add_le_add h2 le_rfl
    rw [he, EReal.coe_le_coe_iff] at h3
    unfold moreauModel moreauEnvelopeReal
    rw [he, EReal.toReal_coe]
    linarith
  · obtain ⟨y, hy⟩ := proximalMappingEReal_nonempty_of_lt_proxThreshold hp hl hlam hthr x
    obtain ⟨-, he⟩ := moreauEnvelope_eq_of_mem_proximalMapping hp hy
    refine ⟨(y, (f y).toReal), hmemT x hx y hy, ?_⟩
    unfold moreauModel moreauEnvelopeReal
    rw [he, EReal.toReal_coe]
    ring

/-- The representation of `-e_λ f` near `x₀` as a `LowerRepresentation`. -/
noncomputable def moreauRepresentation {V : Set E} {T : Set (E × ℝ)} (hT : IsCompact T)
    (hle : ∀ x ∈ V, ∀ q ∈ T, moreauModel lam ((q.2, q.1), x) ≤ -moreauEnvelopeReal f lam x)
    (heq : ∀ x ∈ V, ∃ q ∈ T, moreauModel lam ((q.2, q.1), x) = -moreauEnvelopeReal f lam x) :
    LowerRepresentation ⊤ (fun x ↦ -moreauEnvelopeReal f lam x) V :=
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  LowerRepresentation.ofParam T (fun q ↦ (((q : E × ℝ).2, (q : E × ℝ).1) : ℝ × E))
    ((continuous_snd.comp continuous_subtype_val).prodMk (continuous_fst.comp continuous_subtype_val))
    (moreauModel lam) (contDiff_moreauModel lam) (fun q x hx ↦ hle x hx q q.2)
    (fun x hx ↦ by
      obtain ⟨q, hq, hval⟩ := heq x hx
      exact ⟨⟨q, hq⟩, hval⟩)

/-- **Example 10.32**: `-e_λ f` is lower-`C^∞` on `E`. -/
theorem neg_moreauEnvelope_isLowerCOn (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hlam : 0 < lam) (hthr : (lam : EReal) < proxThreshold f) :
    IsLowerCOn ⊤ (fun x ↦ -moreauEnvelopeReal f lam x) univ := by
  intro x₀ _
  obtain ⟨V, hV, hx₀V, T, hT, -, -, hle, heq⟩ := exists_moreau_representation hp hl hlam hthr x₀
  exact ⟨V, hV, hx₀V, subset_univ _, ⟨moreauRepresentation hT hle heq⟩⟩

/-- **Example 10.32**: `-e_λ f` is semidifferentiable, strictly continuous and regular. -/
theorem neg_moreauEnvelope_properties (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hlam : 0 < lam) (hthr : (lam : EReal) < proxThreshold f) (x : E) :
    ERealStrictlyContinuousAt (fun y ↦ ((-moreauEnvelopeReal f lam y : ℝ) : EReal)) x ∧
      IsSubdifferentiallyRegularAt (fun y ↦ ((-moreauEnvelopeReal f lam y : ℝ) : EReal)) x ∧
      SemidifferentiableAt (fun y ↦ ((-moreauEnvelopeReal f lam y : ℝ) : EReal)) x := by
  have h := neg_moreauEnvelope_isLowerCOn hp hl hlam hthr
  exact ⟨(h.strictlyContinuous_regular le_top x (mem_univ x)).1,
    (h.strictlyContinuous_regular le_top x (mem_univ x)).2,
    h.semidifferentiableAt le_top x (mem_univ x)⟩

section Formulas

variable (hp : IsProper f) (hl : LowerSemicontinuous f) (hlam : 0 < lam)
  (hthr : (lam : EReal) < proxThreshold f)

include hp hl hlam hthr in
/-- The active indices of the representation at `x₀` are the points `(y, f(y))` with
`y ∈ P_λ f(x₀)`, and the gradients there are `λ⁻¹ (y - x₀)`. -/
private theorem moreau_active_data (x₀ : E) :
    ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧
      ∃ R : LowerRepresentation ⊤ (fun x ↦ -moreauEnvelopeReal f lam x) V,
        (∀ t : R.T, ∃ y : E, ∃ β : ℝ, R.F t = (fun z ↦ moreauModel lam ((β, y), z)) ∧
          (t ∈ R.active x₀ → y ∈ proximalMappingEReal f lam x₀)) ∧
        (∀ y ∈ proximalMappingEReal f lam x₀, ∃ t ∈ R.active x₀,
          R.F t = fun z ↦ moreauModel lam (((f y).toReal, y), z)) := by
  obtain ⟨V, hV, hx₀V, T, hT, hTepi, hTmem, hle, heq⟩ := exists_moreau_representation hp hl hlam hthr x₀
  refine ⟨V, hV, hx₀V, moreauRepresentation hT hle heq, fun t ↦ ?_, fun y hy ↦ ?_⟩
  · set q : T := t with hq
    refine ⟨(q : E × ℝ).1, (q : E × ℝ).2, rfl, fun hact ↦ ?_⟩
    have hact' : moreauModel lam (((q : E × ℝ).2, (q : E × ℝ).1), x₀) =
        -moreauEnvelopeReal f lam x₀ := hact
    obtain ⟨y₀, hy₀⟩ := proximalMappingEReal_nonempty_of_lt_proxThreshold hp hl hlam hthr x₀
    obtain ⟨-, he⟩ := moreauEnvelope_eq_of_mem_proximalMapping hp hy₀
    set β := (q : E × ℝ).2
    set y := (q : E × ℝ).1
    have hfyβ : f y ≤ (β : EReal) := hTepi q q.2
    have h1 := moreauEnvelope_le (f := f) (lam := lam) x₀ y
    have hval : moreauEnvelopeReal f lam x₀ = β + (1 / (2 * lam)) * ‖y - x₀‖ ^ 2 := by
      unfold moreauModel at hact'
      linarith
    have hA : (f y₀).toReal + (1 / (2 * lam)) * ‖y₀ - x₀‖ ^ 2 =
        β + (1 / (2 * lam)) * ‖y - x₀‖ ^ 2 := by
      rw [← hval, moreauEnvelopeReal, he, EReal.toReal_coe]
    have heR : moreauEnvelopeEReal f lam x₀ =
        ((β + (1 / (2 * lam)) * ‖y - x₀‖ ^ 2 : ℝ) : EReal) := by
      rw [he, hA]
    have hle2 : f y + (((1 / (2 * lam)) * ‖y - x₀‖ ^ 2 : ℝ) : EReal) ≤
        moreauEnvelopeEReal f lam x₀ := by
      rw [heR, EReal.coe_add]
      exact add_le_add hfyβ le_rfl
    rw [mem_proximalMappingEReal_iff]
    refine ⟨le_antisymm hle2 h1, ?_⟩
    rw [heR]
    exact EReal.coe_lt_top _
  · refine ⟨(⟨(y, (f y).toReal), hTmem x₀ hx₀V y hy⟩ : T), ?_, rfl⟩
    show moreauModel lam (((f y).toReal, y), x₀) = -moreauEnvelopeReal f lam x₀
    obtain ⟨-, he⟩ := moreauEnvelope_eq_of_mem_proximalMapping hp hy
    unfold moreauModel moreauEnvelopeReal
    rw [he, EReal.toReal_coe]
    ring

include hp hl hlam hthr in
/-- **Example 10.32**: `∂[-e_λ f](x̄) = con {λ⁻¹ (y - x̄) | y ∈ P_λ f(x̄)}`. -/
theorem subdifferential_neg_moreauEnvelope (x₀ : E) :
    subdifferential (fun x ↦ ((-moreauEnvelopeReal f lam x : ℝ) : EReal)) x₀ =
      convexHull ℝ ((fun y ↦ lam⁻¹ • (y - x₀)) '' proximalMappingEReal f lam x₀) := by
  obtain ⟨V, hV, hx₀V, R, hdata, hsurj⟩ := moreau_active_data hp hl hlam hthr x₀
  rw [R.subdifferential_eq_convexHull le_top hV hx₀V]
  congr 1
  ext v
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨y, β, hF, hP⟩ := hdata t
    refine ⟨y, hP ht, ?_⟩
    dsimp only
    rw [hF, (hasGradientAt_moreauModel hlam β y x₀).gradient]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, ht, hF⟩ := hsurj y hy
    refine ⟨t, ht, ?_⟩
    dsimp only
    rw [hF, (hasGradientAt_moreauModel hlam _ y x₀).gradient]

include hp hl hlam hthr in
/-- **Example 10.32**: `d[-e_λ f](x̄)(w) = λ⁻¹ max_{y ∈ P_λ f(x̄)} ⟪y - x̄, w⟫`. -/
theorem subderivative_neg_moreauEnvelope (x₀ w : E) :
    ∃ y ∈ proximalMappingEReal f lam x₀,
      subderivative (fun x ↦ ((-moreauEnvelopeReal f lam x : ℝ) : EReal)) x₀ w =
        ((lam⁻¹ * ⟪y - x₀, w⟫_ℝ : ℝ) : EReal) ∧
      ∀ y' ∈ proximalMappingEReal f lam x₀, ⟪y' - x₀, w⟫_ℝ ≤ ⟪y - x₀, w⟫_ℝ := by
  obtain ⟨V, hV, hx₀V, R, hdata, hsurj⟩ := moreau_active_data hp hl hlam hthr x₀
  obtain ⟨⟨t, ht, hval⟩, hmax⟩ := R.isGreatest_dirMax le_top hx₀V w
  obtain ⟨y, β, hF, hP⟩ := hdata t
  have hder : ∀ (β' : ℝ) (y' : E), fderiv ℝ (fun z ↦ moreauModel lam ((β', y'), z)) x₀ w =
      lam⁻¹ * ⟪y' - x₀, w⟫_ℝ := fun β' y' ↦ by
    rw [(hasGradientAt_moreauModel hlam β' y' x₀).hasFDerivAt.fderiv, toDual_apply_apply,
      real_inner_smul_left]
  refine ⟨y, hP ht, ?_, fun y' hy' ↦ ?_⟩
  · rw [R.subderivative_eq le_top hV hx₀V w, ← show fderiv ℝ (R.F t) x₀ w = R.dirMax x₀ w from hval,
      hF, hder]
  · obtain ⟨t', ht', hF'⟩ := hsurj y' hy'
    have h1 := hmax ⟨t', ht', rfl⟩
    rw [← show fderiv ℝ (R.F t) x₀ w = R.dirMax x₀ w from hval] at h1
    simp only at h1
    rw [hF', hF, hder, hder] at h1
    have hl0 : 0 < lam⁻¹ := inv_pos.2 hlam
    exact le_of_mul_le_mul_left h1 hl0

include hp hl hlam hthr in
/-- **Example 10.32**: `lip[-e_λ f](x̄) = λ⁻¹ max_{y ∈ P_λ f(x̄)} |y - x̄|`. -/
theorem lipschitzModulus_neg_moreauEnvelope (x₀ : E) :
    ∃ y ∈ proximalMappingEReal f lam x₀,
      lipschitzModulus (fun x ↦ -moreauEnvelopeReal f lam x) x₀ = (‖lam⁻¹ • (y - x₀)‖₊ : ℝ≥0∞) ∧
      ∀ y' ∈ proximalMappingEReal f lam x₀, ‖y' - x₀‖ ≤ ‖y - x₀‖ := by
  obtain ⟨V, hV, hx₀V, R, hdata, hsurj⟩ := moreau_active_data hp hl hlam hthr x₀
  obtain ⟨t, ht, hlip, hmax⟩ := R.lipschitzModulus_eq le_top hV hx₀V
  obtain ⟨y, β, hF, hP⟩ := hdata t
  refine ⟨y, hP ht, ?_, fun y' hy' ↦ ?_⟩
  · rw [hlip, hF, (hasGradientAt_moreauModel hlam β y x₀).gradient]
  · obtain ⟨t', ht', hF'⟩ := hsurj y' hy'
    have h1 := hmax t' ht'
    rw [hF', hF, (hasGradientAt_moreauModel hlam _ y' x₀).gradient,
      (hasGradientAt_moreauModel hlam β y x₀).gradient, norm_smul, norm_smul] at h1
    have hl0 : 0 < ‖lam⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hlam.ne')
    exact le_of_mul_le_mul_left h1 hl0

include hp hl hlam hthr in
/-- **Example 10.32**: `∂[e_λ f](x̄) ⊂ {λ⁻¹ (x̄ - y) | y ∈ P_λ f(x̄)}`. -/
theorem subdifferential_moreauEnvelope_subset (x₀ : E) :
    subdifferential (fun x ↦ ((moreauEnvelopeReal f lam x : ℝ) : EReal)) x₀ ⊆
      (fun y ↦ lam⁻¹ • (x₀ - y)) '' proximalMappingEReal f lam x₀ := by
  obtain ⟨V, hV, hx₀V, R, hdata, -⟩ := moreau_active_data hp hl hlam hthr x₀
  have hsub := R.neg_subdifferential_neg_subset le_top hV hx₀V
  have hfun : (fun x ↦ -(((-moreauEnvelopeReal f lam x : ℝ) : ℝ) : EReal)) =
      fun x ↦ ((moreauEnvelopeReal f lam x : ℝ) : EReal) := funext fun x ↦ by
    rw [EReal.coe_neg, neg_neg]
  rw [hfun] at hsub
  intro v hv
  have h1 : -v ∈ R.gradSet x₀ := hsub (Set.neg_mem_neg.2 hv)
  obtain ⟨t, ht, hgrad⟩ := h1
  obtain ⟨y, β, hF, hP⟩ := hdata t
  refine ⟨y, hP ht, ?_⟩
  dsimp only at hgrad
  rw [hF, (hasGradientAt_moreauModel hlam β y x₀).gradient] at hgrad
  rw [← neg_neg v, ← hgrad, ← smul_neg, neg_sub]

end Formulas

end RW
