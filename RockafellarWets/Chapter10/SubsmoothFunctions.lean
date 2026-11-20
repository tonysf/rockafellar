/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: subsmooth functions

**Definition 10.29**: `f` is lower-`Cᵏ` on an open set `O` (`IsLowerCOn k f O`) if around each
point of `O` there is a representation `f(x) = max_{t ∈ T} f_t(x)` (`LowerRepresentation`)
with `T` a compact space, every `f_t` of class `Cᵏ`, and `f_t(x)` together with all its
derivatives through order `k` continuous jointly in `(t, x)`; upper-`Cᵏ` means that `-f` is
lower-`Cᵏ` (`IsUpperCOn`).  `Cᵏ` functions are lower-`Cᵏ` (`ContDiffOn.isLowerCOn`), and so are
finite maxima of `Cᵏ` functions (`isLowerCOn_finite_max`).

**Theorem 10.31** for lower-`C¹` functions: `f` is strictly continuous and subdifferentially
regular on `O` (`IsLowerCOn.strictlyContinuous_regular`), hence semidifferentiable with the
properties of Theorem 9.16.  For a local representation on `V` and `x̄ ∈ V`, with active set
`T(x̄) = argmax_t f_t(x̄)` (`LowerRepresentation.active`):

* `df(x̄)(w) = max_{t ∈ T(x̄)} ⟪∇f_t(x̄), w⟫` (`subderivative_eq`, `isGreatest_dirMax`);
* `∂f(x̄) = con {∇f_t(x̄) | t ∈ T(x̄)}` (`subdifferential_eq_convexHull`);
* `lip f(x̄) = max_{t ∈ T(x̄)} |∇f_t(x̄)|` (`lipschitzModulus_eq`);
* `-∂(-f)(x̄) ⊂ {∇f_t(x̄) | t ∈ T(x̄)}` (`neg_subdifferential_neg_subset`), where `-∂(-f)(x̄)`
  is the set of limits of gradients at points of differentiability (Exercise 9.21);
* `f` is strictly differentiable wherever it is differentiable, `∇f` is continuous relative to
  the set `D` of such points, and `O \ D` is negligible (`IsLowerCOn.differentiability`).

The proof follows the book: the one-sided directional derivative of the max representation is
`max_{t ∈ T(x)} ⟪∇f_t(x), w⟫` and is usc in `x`, so Theorem 9.16 applies.  The index space is an
arbitrary compact space, so the compactness arguments use the tube lemma
(`eventually_forall_active`) rather than sequences.  This also repairs one step of the book's
estimate of `df(x)(w)` from above: there the mean value point `x + μτw` need not have the
maximizing index `t ∈ T(x + τw)` among its own active indices, so the bound
`⟪∇f_t(x + μτw), w⟫ ≤ k(x + μτw, w)` is not justified as written; the two-point version of the
tube lemma gives the needed bound `⟪∇f_t(y), w⟫ ≤ k(x, w) + ε` for `y` near `x` and `t` active
at any point near `x`.

**Proposition 10.30**: `f` is `C¹` on `O` iff it is both lower-`C¹` and upper-`C¹`
(`contDiffOn_one_iff_isLowerCOn_isUpperCOn`).  As in the book, differentiability follows from
the two one-sided expansions; continuity of the gradient comes from 10.31 (via 9.18–9.19).
-/

import RockafellarWets.Chapter9.SmoothnessCriteria
import RockafellarWets.Chapter9.SubgradientModulus
import RockafellarWets.Chapter9.Rademacher
import RockafellarWets.Chapter8.SupportFunctions
import RockafellarWets.Chapter8.SubderivativeFormulas
import RockafellarWets.Chapter8.RegularSubgradientBridge
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Filter Function Metric Set Topology InnerProductSpace MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A local representation `f(x) = max_{t ∈ T} f_t(x)` on `V` as in Definition 10.29: `T` is
a compact space, every `f_t` is of class `Cᵏ` on `V`, and `f_t(x)` and its derivatives through
order `k` depend continuously on `(t, x) ∈ T × V`. -/
structure LowerRepresentation (k : ℕ∞) (f : E → ℝ) (V : Set E) where
  /-- The compact index space. -/
  T : Type u
  [topologicalSpace : TopologicalSpace T]
  [compactSpace : CompactSpace T]
  /-- The functions `f_t`. -/
  F : T → E → ℝ
  contDiffOn : ∀ t, ContDiffOn ℝ k (F t) V
  continuousOn_iteratedFDeriv : ∀ j : ℕ, (j : ℕ∞) ≤ k →
    ContinuousOn (fun p : T × E ↦ iteratedFDeriv ℝ j (F p.1) p.2) (univ ×ˢ V)
  le : ∀ t, ∀ x ∈ V, F t x ≤ f x
  exists_eq : ∀ x ∈ V, ∃ t, F t x = f x

attribute [instance] LowerRepresentation.topologicalSpace LowerRepresentation.compactSpace

/-- **Definition 10.29**: `f` is lower-`Cᵏ` on `O`. -/
def IsLowerCOn (k : ℕ∞) (f : E → ℝ) (O : Set E) : Prop :=
  ∀ x ∈ O, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧ Nonempty (LowerRepresentation k f V)

/-- **Definition 10.29**: `f` is upper-`Cᵏ` on `O` when `-f` is lower-`Cᵏ`. -/
def IsUpperCOn (k : ℕ∞) (f : E → ℝ) (O : Set E) : Prop :=
  IsLowerCOn k (fun x ↦ -f x) O

omit [FiniteDimensional ℝ E] in
private theorem continuousOn_iteratedFDeriv_of_contDiffOn {k : ℕ∞} {g : E → ℝ} {O : Set E}
    (hO : IsOpen O) (hg : ContDiffOn ℝ k g O) {j : ℕ} (hj : (j : ℕ∞) ≤ k) :
    ContinuousOn (fun y ↦ iteratedFDeriv ℝ j g y) O := by
  have h := hg.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast hj) hO.uniqueDiffOn
  exact h.congr fun y hy ↦ (iteratedFDerivWithin_of_isOpen j hO hy).symm

omit [FiniteDimensional ℝ E] in
/-- A `Cᵏ` function is lower-`Cᵏ` (a representation with a single index). -/
theorem ContDiffOn.isLowerCOn {k : ℕ∞} {f : E → ℝ} {O : Set E} (hO : IsOpen O)
    (hf : ContDiffOn ℝ k f O) : IsLowerCOn k f O := by
  intro x hx
  refine ⟨O, hO, hx, Subset.rfl, ⟨LowerRepresentation.mk PUnit (fun _ ↦ f) (fun _ ↦ hf)
    (fun j hj ↦ ?_) (fun _ _ _ ↦ le_rfl) (fun _ _ ↦ ⟨PUnit.unit, rfl⟩)⟩⟩
  exact (continuousOn_iteratedFDeriv_of_contDiffOn hO hf hj).comp continuousOn_snd
    fun p hp ↦ hp.2

omit [FiniteDimensional ℝ E] in
/-- A finite maximum of `Cᵏ` functions is lower-`Cᵏ` (the case of a finite discrete index
space in Definition 10.29). -/
theorem isLowerCOn_finite_max {k : ℕ∞} {ι : Type u} [Fintype ι] [Nonempty ι] {g : ι → E → ℝ}
    {O : Set E} (hO : IsOpen O) (hg : ∀ i, ContDiffOn ℝ k (g i) O) :
    IsLowerCOn k (fun x ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ g i x) O := by
  intro x hx
  letI : TopologicalSpace ι := ⊥
  haveI : DiscreteTopology ι := ⟨rfl⟩
  refine ⟨O, hO, hx, Subset.rfl, ⟨LowerRepresentation.mk ι g hg (fun j hj ↦ ?_)
    (fun i y _ ↦ Finset.le_sup' (fun i ↦ g i y) (Finset.mem_univ i)) (fun y _ ↦ ?_)⟩⟩
  · rw [continuousOn_prod_of_discrete_left]
    intro i
    have h := continuousOn_iteratedFDeriv_of_contDiffOn hO (hg i) hj
    exact h.mono fun y hy ↦ by simpa using hy
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i ↦ g i y)
    exact ⟨i, hi.symm⟩

namespace LowerRepresentation

variable {k : ℕ∞} {f : E → ℝ} {V : Set E} (R : LowerRepresentation k f V)

omit [FiniteDimensional ℝ E] in
theorem continuousOn_val : ContinuousOn (fun p : R.T × E ↦ R.F p.1 p.2) (univ ×ˢ V) := by
  have h := R.continuousOn_iteratedFDeriv 0 (zero_le _)
  have e : (fun p : R.T × E ↦ R.F p.1 p.2) = fun p ↦
      (continuousMultilinearCurryFin0 ℝ E ℝ) (iteratedFDeriv ℝ 0 (R.F p.1) p.2) := by
    funext p
    simp [iteratedFDeriv_zero_apply]
  rw [e]
  exact (continuousMultilinearCurryFin0 ℝ E ℝ).continuous.comp_continuousOn h

omit [FiniteDimensional ℝ E] in
theorem continuousOn_fderiv (hk : 1 ≤ k) :
    ContinuousOn (fun p : R.T × E ↦ fderiv ℝ (R.F p.1) p.2) (univ ×ˢ V) := by
  have h := R.continuousOn_iteratedFDeriv 1 (by exact_mod_cast hk)
  have e : (fun p : R.T × E ↦ fderiv ℝ (R.F p.1) p.2) = fun p ↦
      (continuousMultilinearCurryFin1 ℝ E ℝ) (iteratedFDeriv ℝ 1 (R.F p.1) p.2) := by
    funext p
    ext v
    simp [iteratedFDeriv_one_apply, Fin.snoc]
  rw [e]
  exact (continuousMultilinearCurryFin1 ℝ E ℝ).continuous.comp_continuousOn h

omit [FiniteDimensional ℝ E] in
theorem differentiableAt (hk : 1 ≤ k) (hV : IsOpen V) (t : R.T) {x : E} (hx : x ∈ V) :
    DifferentiableAt ℝ (R.F t) x :=
  ((R.contDiffOn t).differentiableOn (by exact_mod_cast (zero_lt_one.trans_le hk).ne') x
    hx).differentiableAt
    (hV.mem_nhds hx)

/-- On closed balls inside `V` the gradients are uniformly bounded and `f` is Lipschitz. -/
theorem exists_lipschitzOnWith (hk : 1 ≤ k) (hV : IsOpen V) {x : E} {r : ℝ}
    (hr : closedBall x r ⊆ V) :
    ∃ L : ℝ≥0, (∀ t, ∀ y ∈ closedBall x r, ‖fderiv ℝ (R.F t) y‖ ≤ L) ∧
      LipschitzOnWith L f (closedBall x r) := by
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall x r)).exists_bound_of_continuousOn
    ((R.continuousOn_fderiv hk).mono (prod_mono Subset.rfl hr))
  have hb : ∀ t, ∀ y ∈ closedBall x r, ‖fderiv ℝ (R.F t) y‖ ≤ C.toNNReal := fun t y hy ↦
    (hC (t, y) ⟨trivial, hy⟩).trans (Real.le_coe_toNNReal C)
  refine ⟨C.toNNReal, hb, ?_⟩
  have hFL : ∀ t, LipschitzOnWith C.toNNReal (R.F t) (closedBall x r) := fun t ↦
    (convex_closedBall x r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      (fun y hy ↦ R.differentiableAt hk hV t (hr hy))
      (fun y hy ↦ by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hb t y hy)
  refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' ↦ ?_
  obtain ⟨t, ht⟩ := R.exists_eq y (hr hy)
  obtain ⟨t', ht'⟩ := R.exists_eq y' (hr hy')
  have h1 := (hFL t).dist_le_mul y hy y' hy'
  have h2 := (hFL t').dist_le_mul y' hy' y hy
  rw [Real.dist_eq, abs_le] at h1 h2 ⊢
  rw [dist_comm y' y] at h2
  have h3 := R.le t y' (hr hy')
  have h4 := R.le t' y (hr hy)
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

include R in
theorem strictlyContinuousAt (hk : 1 ≤ k) (hV : IsOpen V) {x : E} (hx : x ∈ V) :
    StrictlyContinuousAt f x := by
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV x hx
  obtain ⟨L, -, hL⟩ := R.exists_lipschitzOnWith hk hV
    ((closedBall_subset_ball (half_lt_self hr)).trans hrV)
  exact strictlyContinuousAt_iff.2 ⟨L, closedBall x (r / 2), closedBall_mem_nhds x (half_pos hr), hL⟩

include R in
theorem continuousAt (hk : 1 ≤ k) (hV : IsOpen V) {x : E} (hx : x ∈ V) : ContinuousAt f x := by
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV x hx
  obtain ⟨L, -, hL⟩ := R.exists_lipschitzOnWith hk hV
    ((closedBall_subset_ball (half_lt_self hr)).trans hrV)
  exact hL.continuousOn.continuousAt (closedBall_mem_nhds x (half_pos hr))

/-- The active indices `T(x) = argmax_t f_t(x)`. -/
def active (x : E) : Set R.T := {t | R.F t x = f x}

omit [FiniteDimensional ℝ E] in
theorem continuous_F_apply {x : E} (hx : x ∈ V) : Continuous fun t ↦ R.F t x :=
  R.continuousOn_val.comp_continuous (continuous_id.prodMk continuous_const) fun _ ↦ ⟨trivial, hx⟩

omit [FiniteDimensional ℝ E] in
theorem isCompact_active {x : E} (hx : x ∈ V) : IsCompact (R.active x) :=
  (isClosed_eq (R.continuous_F_apply hx) continuous_const).isCompact

omit [FiniteDimensional ℝ E] in
theorem active_nonempty {x : E} (hx : x ∈ V) : (R.active x).Nonempty := R.exists_eq x hx

/-- **Tube lemma** for the active indices: a condition on `Ψ(t, y)`, continuous in `(t, y)`,
that holds at `x` for all active `t ∈ T(x)` holds for all `y` near `x` and all `t` active at
any point `y''` near `x`. -/
theorem eventually_forall_active (hk : 1 ≤ k) (hV : IsOpen V) {x : E} (hx : x ∈ V)
    {Z : Type*} [TopologicalSpace Z] {Ψ : R.T → E → Z}
    (hΨ : ContinuousOn (fun p : R.T × E ↦ Ψ p.1 p.2) (univ ×ˢ V)) {W : Set Z} (hW : IsOpen W)
    (hmem : ∀ t ∈ R.active x, Ψ t x ∈ W) :
    ∀ᶠ q : E × E in 𝓝 (x, x), ∀ t, t ∈ R.active q.2 → Ψ t q.1 ∈ W := by
  have hfc := R.continuousAt hk hV hx
  have hn : ∀ t : R.T, univ ×ˢ V ∈ 𝓝 (t, x) := fun t ↦ prod_mem_nhds univ_mem (hV.mem_nhds hx)
  have h := isCompact_univ.eventually_forall_of_forall_eventually (x₀ := (x, x))
    (P := fun (q : E × E) (t : R.T) ↦ t ∈ R.active q.2 → Ψ t q.1 ∈ W) fun t _ ↦ ?_
  · exact h.mono fun q hq t ↦ hq t (mem_univ t)
  by_cases ht : t ∈ R.active x
  · have h1 : ContinuousAt (fun p : R.T × E ↦ Ψ p.1 p.2) (t, x) := hΨ.continuousAt (hn t)
    have hc : ContinuousAt (fun z : (E × E) × R.T ↦ Ψ z.2 z.1.1) ((x, x), t) :=
      h1.comp_of_eq (continuous_snd.prodMk (continuous_fst.comp continuous_fst)).continuousAt rfl
    filter_upwards [hc.preimage_mem_nhds (hW.mem_nhds (hmem t ht))] with z hz _
    exact hz
  · have hlt : R.F t x < f x := lt_of_le_of_ne (R.le t x hx) ht
    have h1 : ContinuousAt (fun p : R.T × E ↦ R.F p.1 p.2) (t, x) :=
      R.continuousOn_val.continuousAt (hn t)
    have h2 : ContinuousAt (fun z : (E × E) × R.T ↦ f z.1.2) ((x, x), t) :=
      hfc.comp (f := fun z : (E × E) × R.T ↦ z.1.2) (continuous_snd.comp continuous_fst).continuousAt
    have hc : ContinuousAt (fun z : (E × E) × R.T ↦ f z.1.2 - R.F z.2 z.1.2) ((x, x), t) :=
      h2.sub (h1.comp_of_eq
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst)).continuousAt rfl)
    filter_upwards [hc.preimage_mem_nhds (Ioi_mem_nhds (sub_pos.2 hlt))] with z hz hact
    have hz' : R.F z.2 z.1.2 < f z.1.2 := sub_pos.1 hz
    exact absurd (show R.F z.2 z.1.2 = f z.1.2 from hact) (ne_of_lt hz')

/-- The maximal directional derivative `k(x, w) = max_{t ∈ T(x)} ⟪∇f_t(x), w⟫`. -/
noncomputable def dirMax (x w : E) : ℝ := sSup ((fun t ↦ fderiv ℝ (R.F t) x w) '' R.active x)

omit [FiniteDimensional ℝ E] in
theorem continuousOn_fderiv_apply (hk : 1 ≤ k) (w : E) :
    ContinuousOn (fun p : R.T × E ↦ fderiv ℝ (R.F p.1) p.2 w) (univ ×ˢ V) :=
  (R.continuousOn_fderiv hk).clm_apply continuousOn_const

omit [FiniteDimensional ℝ E] in
theorem isGreatest_dirMax (hk : 1 ≤ k) {x : E} (hx : x ∈ V) (w : E) :
    IsGreatest ((fun t ↦ fderiv ℝ (R.F t) x w) '' R.active x) (R.dirMax x w) := by
  have hc : Continuous fun t ↦ fderiv ℝ (R.F t) x w :=
    (R.continuousOn_fderiv_apply hk w).comp_continuous (continuous_id.prodMk continuous_const)
      fun _ ↦ ⟨trivial, hx⟩
  exact ((R.isCompact_active hx).image hc).isGreatest_sSup ((R.active_nonempty hx).image _)

/-- The difference quotients of `f` converge to `k(x, w)`. -/
theorem tendsto_slope (hk : 1 ≤ k) (hV : IsOpen V) {x : E} (hx : x ∈ V) (w : E) :
    Tendsto (fun τ : ℝ ↦ τ⁻¹ * (f (x + τ • w) - f x)) (𝓝[>] 0) (𝓝 (R.dirMax x w)) := by
  have hpath : Tendsto (fun τ : ℝ ↦ x + τ • w) (𝓝 0) (𝓝 x) := by
    have h := ((continuous_const.add (continuous_id.smul continuous_const) :
      Continuous fun τ : ℝ ↦ x + τ • w)).tendsto 0
    simpa using h
  have hpathV : ∀ᶠ τ in 𝓝[>] (0 : ℝ), x + τ • w ∈ V :=
    (hpath.mono_left nhdsWithin_le_nhds).eventually (hV.mem_nhds hx)
  obtain ⟨⟨t₀, ht₀, hval⟩, hmax⟩ := R.isGreatest_dirMax hk hx w
  rw [tendsto_order]
  constructor
  · intro a ha
    have hlim := ((R.differentiableAt hk hV t₀ hx).hasFDerivAt.hasLineDerivAt w).tendsto_slope_zero_right
    simp only [smul_eq_mul] at hlim
    rw [show fderiv ℝ (R.F t₀) x w = R.dirMax x w from hval] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds ha), hpathV, self_mem_nhdsWithin] with τ h1 h2 h3
    have h0 : R.F t₀ x = f x := ht₀
    have hle : R.F t₀ (x + τ • w) - R.F t₀ x ≤ f (x + τ • w) - f x := by
      have := R.le t₀ _ h2
      linarith
    calc a < τ⁻¹ * (R.F t₀ (x + τ • w) - R.F t₀ x) := h1
      _ ≤ τ⁻¹ * (f (x + τ • w) - f x) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (le_of_lt h3))
  · intro a ha
    set ε := (a - R.dirMax x w) / 2 with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    have htube := R.eventually_forall_active hk hV hx (Ψ := fun t y ↦ fderiv ℝ (R.F t) y w)
      (R.continuousOn_fderiv_apply hk w) (W := Iio (R.dirMax x w + ε)) isOpen_Iio
      (fun t ht ↦ (hmax ⟨t, ht, rfl⟩).trans_lt (lt_add_of_pos_right _ hε))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 htube
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV x hx
    set δ' := min δ r with hδ'def
    have hδ' : 0 < δ' := lt_min hδ hr
    have hc : 0 < δ' / (‖w‖ + 1) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hc] with τ hτ
    have hseg : ∀ s ∈ Icc (0 : ℝ) τ, x + s • w ∈ ball x δ' := by
      intro s hs
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs.1]
      have h1 : τ * (‖w‖ + 1) < δ' := (lt_div_iff₀ (by positivity)).1 hτ.2
      have h2 : s * ‖w‖ ≤ τ * ‖w‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      nlinarith [norm_nonneg w, hτ.1]
    have hsegV : ∀ s ∈ Icc (0 : ℝ) τ, x + s • w ∈ V := fun s hs ↦
      hrV (ball_subset_ball (min_le_right _ _) (hseg s hs))
    have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨le_of_lt hτ.1, le_rfl⟩
    obtain ⟨t, ht⟩ := R.exists_eq (x + τ • w) (hsegV τ hτmem)
    have hgc : ContinuousOn (fun s : ℝ ↦ R.F t (x + s • w)) (Icc 0 τ) :=
      (R.contDiffOn t).continuousOn.comp
        ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn) hsegV
    have hgd : ∀ s ∈ Ioo (0 : ℝ) τ, HasDerivAt (fun s : ℝ ↦ R.F t (x + s • w))
        (fderiv ℝ (R.F t) (x + s • w) w) s := by
      intro s hs
      have h1 := (R.differentiableAt hk hV t (hsegV s (Ioo_subset_Icc_self hs))).hasFDerivAt
      have h2 := h1.comp_hasDerivAt s (((hasDerivAt_id s).smul_const w).const_add x)
      simpa using h2
    obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ ↦ R.F t (x + s • w))
      (fun s ↦ fderiv ℝ (R.F t) (x + s • w) w) hτ.1 hgc hgd
    simp only [zero_smul, add_zero, sub_zero] at hcd
    have hq := hball (x + c • w, x + τ • w) (by
      rw [← ball_prod_same]
      exact ⟨ball_subset_ball (min_le_left _ _) (hseg c (Ioo_subset_Icc_self hc')),
        ball_subset_ball (min_le_left _ _) (hseg τ hτmem)⟩) t ht
    simp only [mem_Iio] at hq
    have hfx : R.F t x ≤ f x := R.le t x hx
    have hft : R.F t (x + τ • w) = f (x + τ • w) := ht
    have hτpos : 0 < τ := hτ.1
    calc τ⁻¹ * (f (x + τ • w) - f x) ≤ τ⁻¹ * (R.F t (x + τ • w) - R.F t x) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hτpos.le)
          rw [hft]
          linarith
      _ = fderiv ℝ (R.F t) (x + c • w) w := by
          rw [hcd]
          field_simp
      _ < R.dirMax x w + ε := hq
      _ < a := by rw [hεdef]; linarith

theorem hasOneSidedDirDeriv (hk : 1 ≤ k) (hV : IsOpen V) {x : E} (hx : x ∈ V) (w : E) :
    HasOneSidedDirDeriv (fun y ↦ (f y : EReal)) x w (R.dirMax x w) := by
  refine ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _, ?_⟩
  have h := (continuous_coe_real_ereal.tendsto _).comp (R.tendsto_slope hk hV hx w)
  refine h.congr fun τ ↦ ?_
  simp only [Function.comp_apply]
  rw [differenceQuotient_eq_coe (f := fun y ↦ (f y : EReal)) rfl rfl]

/-- `k(·, w)` is upper semicontinuous on `V`. -/
theorem upperSemicontinuousOn_dirMax (hk : 1 ≤ k) (hV : IsOpen V) (w : E) :
    UpperSemicontinuousOn (fun x ↦ R.dirMax x w) V := by
  intro x hx a ha
  obtain ⟨-, hmax⟩ := R.isGreatest_dirMax hk hx w
  have htube := R.eventually_forall_active hk hV hx (Ψ := fun t y ↦ fderiv ℝ (R.F t) y w)
    (R.continuousOn_fderiv_apply hk w) (W := Iio a) isOpen_Iio
    (fun t ht ↦ (hmax ⟨t, ht, rfl⟩).trans_lt ha)
  have hdiag : Tendsto (fun y : E ↦ (y, y)) (𝓝 x) (𝓝 (x, x)) :=
    (continuous_id.prodMk continuous_id).tendsto x
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hdiag.eventually htube), self_mem_nhdsWithin]
    with y hy hyV
  obtain ⟨⟨t, ht, hval⟩, -⟩ := R.isGreatest_dirMax hk hyV w
  have h := hy t ht
  simp only [mem_Iio] at h
  rw [← hval]
  exact h

include R in
/-- **Theorem 10.31**: `f` is strictly continuous and regular on `V`. -/
theorem strictlyContinuous_regular (hk : 1 ≤ k) (hV : IsOpen V) :
    ∀ x ∈ V, ERealStrictlyContinuousAt (fun y ↦ (f y : EReal)) x ∧
      IsSubdifferentiallyRegularAt (fun y ↦ (f y : EReal)) x :=
  (strictlyContinuous_regular_iff_hasOneSidedDirDeriv_usc hV).2
    ⟨fun y w ↦ R.dirMax y w, fun _ hy w ↦ R.hasOneSidedDirDeriv hk hV hy w,
      fun w ↦ R.upperSemicontinuousOn_dirMax hk hV w⟩

/-- **Theorem 10.31**: `df(x̄)(w) = max_{t ∈ T(x̄)} ⟪∇f_t(x̄), w⟫`. -/
theorem subderivative_eq (hk : 1 ≤ k) (hV : IsOpen V) {x : E} (hx : x ∈ V) (w : E) :
    subderivative (fun y ↦ (f y : EReal)) x w = R.dirMax x w := by
  obtain ⟨-, hprops, -⟩ := strictlyContinuous_regular_properties (R.strictlyContinuous_regular hk hV)
  have h1 := ((hprops x hx w).1).hasOneSidedDirDeriv
  exact tendsto_nhds_unique h1.2.2 (R.hasOneSidedDirDeriv hk hV hx w).2.2

/-- The gradients of the active functions, `{∇f_t(x) | t ∈ T(x)}`. -/
def gradSet (x : E) : Set E := (fun t ↦ gradient (R.F t) x) '' R.active x

omit [FiniteDimensional ℝ E] in
private theorem inner_gradient_eq (g : E → ℝ) (y w : E) [CompleteSpace E] :
    ⟪gradient g y, w⟫_ℝ = fderiv ℝ g y w := by
  rw [gradient, toDual_symm_apply]

theorem isCompact_gradSet (hk : 1 ≤ k) {x : E} (hx : x ∈ V) : IsCompact (R.gradSet x) := by
  have hc : Continuous fun t ↦ gradient (R.F t) x :=
    (toDual ℝ E).symm.continuous.comp ((R.continuousOn_fderiv hk).comp_continuous
      (continuous_id.prodMk continuous_const) fun _ ↦ ⟨trivial, hx⟩)
  exact (R.isCompact_active hx).image hc

theorem supportFunction_gradSet (hk : 1 ≤ k) {x : E} (hx : x ∈ V) (w : E) :
    supportFunction (R.gradSet x) w = R.dirMax x w := by
  obtain ⟨⟨t₀, ht₀, hval⟩, hmax⟩ := R.isGreatest_dirMax hk hx w
  apply le_antisymm
  · refine iSup_le fun ⟨v, hv⟩ ↦ ?_
    obtain ⟨t, ht, rfl⟩ := hv
    rw [inner_gradient_eq]
    exact EReal.coe_le_coe_iff.2 (hmax ⟨t, ht, rfl⟩)
  · refine le_trans ?_ (le_iSup (fun v : R.gradSet x ↦ ((⟪(v : E), w⟫_ℝ : ℝ) : EReal))
      ⟨gradient (R.F t₀) x, t₀, ht₀, rfl⟩)
    rw [inner_gradient_eq, show fderiv ℝ (R.F t₀) x w = R.dirMax x w from hval]

/-- **Theorem 10.31**: `∂f(x̄) = con {∇f_t(x̄) | t ∈ T(x̄)}`. -/
theorem subdifferential_eq_convexHull (hk : 1 ≤ k) (hV : IsOpen V) {x : E} (hx : x ∈ V) :
    subdifferential (fun y ↦ (f y : EReal)) x = convexHull ℝ (R.gradSet x) := by
  obtain ⟨-, hreg⟩ := R.strictlyContinuous_regular hk hV x hx
  apply Subset.antisymm
  · intro v hv
    rw [hreg.subdifferential_eq_regularSubdifferential] at hv
    have hmin : v ∈ linearMinorantSet (supportFunction (R.gradSet x)) := fun w ↦ by
      rw [R.supportFunction_gradSet hk hx w, ← R.subderivative_eq hk hV hx w]
      exact inner_le_subderivative_of_mem_regularSubdifferential hv w
    rwa [linearMinorantSet_supportFunction,
      (isCompact_convexHull (R.isCompact_gradSet hk hx)).isClosed.closure_eq] at hmin
  · have hcx : Convex ℝ (subdifferential (fun y ↦ (f y : EReal)) x) := by
      rw [hreg.subdifferential_eq_regularSubdifferential]
      exact (subdifferential_properties (f := fun y ↦ (f y : EReal)) (x := x) (c := f x) rfl).2.1
    refine convexHull_min ?_ hcx
    rintro _ ⟨t, ht, rfl⟩
    apply regularSubdifferential_subset_subdifferential
    refine (mem_regularSubdifferential_iff_exists_hasGradientAt (f := fun y ↦ (f y : EReal))
      (c := f x) rfl).2 ⟨R.F t, ?_, ht, (R.differentiableAt hk hV t hx).hasGradientAt⟩
    filter_upwards [hV.mem_nhds hx] with y hy
    exact EReal.coe_le_coe_iff.2 (R.le t y hy)

/-- **Theorem 10.31**: `lip f(x̄) = max_{t ∈ T(x̄)} |∇f_t(x̄)|`. -/
theorem lipschitzModulus_eq (hk : 1 ≤ k) (hV : IsOpen V) {x : E} (hx : x ∈ V) :
    ∃ t ∈ R.active x, lipschitzModulus f x = (‖gradient (R.F t) x‖₊ : ℝ≥0∞) ∧
      ∀ t' ∈ R.active x, ‖gradient (R.F t') x‖ ≤ ‖gradient (R.F t) x‖ := by
  obtain ⟨hsc, -⟩ := R.strictlyContinuous_regular hk hV x hx
  have hf' : (fun y ↦ ((f y : EReal)).toReal) = f := funext fun y ↦ EReal.toReal_coe _
  obtain ⟨u, hu, hlip, hmax⟩ := hsc.exists_subgradient_norm_eq_modulus
  rw [hf'] at hlip
  have hc : Continuous fun t ↦ ‖gradient (R.F t) x‖ :=
    continuous_norm.comp ((toDual ℝ E).symm.continuous.comp ((R.continuousOn_fderiv hk).comp_continuous
      (continuous_id.prodMk continuous_const) fun _ ↦ ⟨trivial, hx⟩))
  obtain ⟨t, ht, htmax⟩ := (R.isCompact_active hx).exists_isMaxOn (R.active_nonempty hx) hc.continuousOn
  rw [isMaxOn_iff] at htmax
  have hsub := R.subdifferential_eq_convexHull hk hV hx
  refine ⟨t, ht, ?_, fun t' ht' ↦ htmax t' ht'⟩
  have h1 : ‖u‖ ≤ ‖gradient (R.F t) x‖ := by
    rw [hsub] at hu
    have hball : R.gradSet x ⊆ closedBall 0 ‖gradient (R.F t) x‖ := by
      rintro _ ⟨t', ht', rfl⟩
      rw [mem_closedBall_zero_iff]
      exact htmax t' ht'
    have h := convexHull_min hball (convex_closedBall 0 _) hu
    rwa [mem_closedBall_zero_iff] at h
  have h2 : ‖gradient (R.F t) x‖ ≤ ‖u‖ :=
    hmax _ (by rw [hsub]; exact subset_convexHull ℝ _ ⟨t, ht, rfl⟩)
  rw [hlip]
  congr 1
  ext
  simp only [coe_nnnorm]
  linarith

/-- At a point of differentiability every active gradient equals `∇f`. -/
theorem gradient_eq_of_differentiableAt (hk : 1 ≤ k) (hV : IsOpen V) {y : E} (hy : y ∈ V)
    (hd : DifferentiableAt ℝ f y) {t : R.T} (ht : t ∈ R.active y) :
    gradient f y = gradient (R.F t) y := by
  have hmin : IsLocalMin (fun z ↦ f z - R.F t z) y := by
    filter_upwards [hV.mem_nhds hy] with z hz
    have h1 := R.le t z hz
    have h2 : R.F t y = f y := ht
    show f y - R.F t y ≤ f z - R.F t z
    linarith
  have h0 := hmin.hasFDerivAt_eq_zero (hd.hasFDerivAt.sub (R.differentiableAt hk hV t hy).hasFDerivAt)
  rw [sub_eq_zero] at h0
  simp [gradient, h0]

/-- **Theorem 10.31**: `-∂(-f)(x̄) ⊂ {∇f_t(x̄) | t ∈ T(x̄)}`. -/
theorem neg_subdifferential_neg_subset (hk : 1 ≤ k) (hV : IsOpen V) {x : E} (hx : x ∈ V) :
    -subdifferential (fun y ↦ -((f y : ℝ) : EReal)) x ⊆ R.gradSet x := by
  have hf' : (fun y ↦ ((f y : EReal)).toReal) = f := funext fun y ↦ EReal.toReal_coe _
  have h := neg_subdifferential_neg_eq hV (R.strictlyContinuous_regular hk hV) hx
  simp only [hf'] at h
  rw [h]
  rintro v ⟨xs, hxs, hdiff, hgrad⟩
  by_contra hv
  have hopen : IsOpen (R.gradSet x)ᶜ := (R.isCompact_gradSet hk hx).isClosed.isOpen_compl
  obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.1 hopen v hv
  have hW : IsOpen (closedBall v (η / 2))ᶜ := isClosed_closedBall.isOpen_compl
  have hΨ : ContinuousOn (fun p : R.T × E ↦ gradient (R.F p.1) p.2) (univ ×ˢ V) :=
    (toDual ℝ E).symm.continuous.comp_continuousOn (R.continuousOn_fderiv hk)
  have htube := R.eventually_forall_active hk hV hx (Ψ := fun t y ↦ gradient (R.F t) y) hΨ hW
    (fun t ht ↦ by
      intro hmem
      have h1 : gradient (R.F t) x ∈ ball v η :=
        closedBall_subset_ball (half_lt_self hη) hmem
      exact hηsub h1 ⟨t, ht, rfl⟩)
  have hdiag : Tendsto (fun y : E ↦ (y, y)) (𝓝 x) (𝓝 (x, x)) :=
    (continuous_id.prodMk continuous_id).tendsto x
  have hev := hxs.eventually ((hdiag.eventually htube).and (hV.mem_nhds hx))
  have hclose := hgrad.eventually (ball_mem_nhds v (half_pos hη))
  obtain ⟨n, ⟨hn1, hn2⟩, hn3⟩ := (hev.and hclose).exists
  obtain ⟨t, ht⟩ := R.exists_eq (xs n) hn2
  have heq := R.gradient_eq_of_differentiableAt hk hV hn2 (hdiff n) ht
  have h1 : gradient (R.F t) (xs n) ∈ (closedBall v (η / 2))ᶜ := hn1 t ht
  rw [← heq] at h1
  exact h1 (ball_subset_closedBall hn3)

end LowerRepresentation

/-- **Theorem 10.31**: a lower-`C¹` function is strictly continuous and subdifferentially
regular on `O`, hence semidifferentiable with all the properties of Theorem 9.16
(`strictlyContinuous_regular_properties`). -/
theorem IsLowerCOn.strictlyContinuous_regular {k : ℕ∞} {f : E → ℝ} {O : Set E}
    (hf : IsLowerCOn k f O) (hk : 1 ≤ k) :
    ∀ x ∈ O, ERealStrictlyContinuousAt (fun y ↦ (f y : EReal)) x ∧
      IsSubdifferentiallyRegularAt (fun y ↦ (f y : EReal)) x := by
  intro x hx
  obtain ⟨V, hV, hxV, -, ⟨R⟩⟩ := hf x hx
  exact R.strictlyContinuous_regular hk hV x hxV

theorem IsLowerCOn.strictlyContinuousAt {k : ℕ∞} {f : E → ℝ} {O : Set E}
    (hf : IsLowerCOn k f O) (hk : 1 ≤ k) {x : E} (hx : x ∈ O) : StrictlyContinuousAt f x := by
  obtain ⟨V, hV, hxV, -, ⟨R⟩⟩ := hf x hx
  exact R.strictlyContinuousAt hk hV hxV

/-- **Theorem 10.31**: a lower-`C¹` function is strictly differentiable wherever it is
differentiable, its gradient is continuous relative to the set `D` of such points, and the
complement `O \ D` is negligible for every additive Haar measure. -/
theorem IsLowerCOn.differentiability [MeasurableSpace E] [BorelSpace E] {k : ℕ∞} {f : E → ℝ}
    {O : Set E} (hf : IsLowerCOn k f O) (hk : 1 ≤ k) (μ : Measure E) [μ.IsAddHaarMeasure] :
    (∀ x ∈ O, DifferentiableAt ℝ f x → HasStrictFDerivAt f (fderiv ℝ f x) x) ∧
      ContinuousOn (gradient f) {x | x ∈ O ∧ DifferentiableAt ℝ f x} ∧
      μ (O \ {x | DifferentiableAt ℝ f x}) = 0 := by
  have h := hf.strictlyContinuous_regular hk
  have hf' : (fun y ↦ ((f y : EReal)).toReal) = f := funext fun y ↦ EReal.toReal_coe _
  have hstrict : ∀ x ∈ O, DifferentiableAt ℝ f x → HasStrictGradientAt (fun y ↦ (f y : EReal))
      (gradient f x) x := by
    intro x hx hd
    have h1 := (h x hx).2.hasStrictGradientAt_of_differentiableAt
      (Eventually.of_forall fun y ↦ by simp) (by rwa [hf'])
    rwa [hf'] at h1
  refine ⟨fun x hx hd ↦ ?_, ?_, ?_⟩
  · have h2 := (hstrict x hx hd).2
    rw [hf'] at h2
    have h3 : innerSL ℝ (gradient f x) = fderiv ℝ f x := by
      ext w
      simp [gradient, toDual_symm_apply]
    rwa [h3] at h2
  · have hgrad : ∀ x ∈ {x | x ∈ O ∧ DifferentiableAt ℝ f x},
        HasStrictGradientAt (fun y ↦ (f y : EReal)) (gradient f x) x :=
      fun x hx ↦ hstrict x hx.1 hx.2
    intro x hx
    refine tendsto_of_eventually_mem_subdifferential (hgrad x hx).eRealStrictlyContinuousAt
      (hgrad x hx).subdifferential_eq nhdsWithin_le_nhds ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [(hgrad z hz).subdifferential_eq]
    exact mem_singleton _
  · refine measure_mono_null (fun x hx ↦ ?_)
      (ae_iff.1 (ae_differentiableAt_of_strictlyContinuousAt f μ))
    simp only [mem_setOf_eq, Classical.not_imp]
    exact ⟨hf.strictlyContinuousAt hk hx.1, hx.2⟩

/-- **Theorem 10.31**: a lower-`C¹` function is semidifferentiable on `O`. -/
theorem IsLowerCOn.semidifferentiableAt {k : ℕ∞} {f : E → ℝ} {O : Set E}
    (hf : IsLowerCOn k f O) (hk : 1 ≤ k) :
    ∀ x ∈ O, SemidifferentiableAt (fun y ↦ (f y : EReal)) x :=
  (strictlyContinuous_regular_properties (hf.strictlyContinuous_regular hk)).1

/-- **Proposition 10.30**: `f` is `C¹` on the open set `O` if and only if it is both lower-`C¹`
and upper-`C¹` on `O`. -/
theorem contDiffOn_one_iff_isLowerCOn_isUpperCOn {f : E → ℝ} {O : Set E} (hO : IsOpen O) :
    ContDiffOn ℝ 1 f O ↔ IsLowerCOn 1 f O ∧ IsUpperCOn 1 f O := by
  constructor
  · intro h
    exact ⟨ContDiffOn.isLowerCOn hO h, ContDiffOn.isLowerCOn hO h.neg⟩
  · rintro ⟨hl, hu⟩
    have hL := hl.strictlyContinuous_regular le_rfl
    have hU := hu.strictlyContinuous_regular le_rfl
    have hf' : (fun y ↦ ((f y : EReal)).toReal) = f := funext fun y ↦ EReal.toReal_coe _
    have hstrict : ∀ x ∈ O, StrictlyDifferentiableAt (fun y ↦ (f y : EReal)) x := by
      intro x hx
      obtain ⟨hscU, hregU⟩ := hU x hx
      obtain ⟨⟨u, hu'⟩, -⟩ := hscU.subdifferential_nonempty_compact
      rw [hregU.subdifferential_eq_regularSubdifferential] at hu'
      have hneg : (fun y ↦ ((-f y : ℝ) : EReal)) = fun y ↦ -((f y : ℝ) : EReal) :=
        funext fun y ↦ EReal.coe_neg _
      rw [hneg] at hu'
      exact ⟨-u, hasStrictGradientAt_of_regular_of_mem_regularSubdifferential_neg (hL x hx).2 hu'⟩
    have htfae := tfae_contDiffOn (f := fun y ↦ (f y : EReal)) hO
      (fun x _ ↦ ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _⟩)
    have h := (htfae.out 0 1).1 hstrict
    rwa [hf'] at h

end RW
