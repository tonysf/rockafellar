/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The horizon subgradient graph of a normal integrand need not be measurable

Theorem 14.56 of Rockafellar–Wets asserts, for every proper normal integrand `f` on a measurable
space `(T, A)`, that `t ↦ gph ∂f(t, ·)` and `t ↦ gph ∂^∞f(t, ·)` are measurable.  The first
mapping is measurable in general (`svMeasurable_svGraph_subdifferential`), and both are when `A` is
complete for an s-finite measure (`svMeasurable_svGraph_subdifferential_of_isComplete`).  Here the
second one is shown to fail without completeness, already for the Borel σ-field of the Baire space
`ℕ → ℕ` and a proper normal integrand on `ℝ²` (`horizon_graph_counterexample`).

The integrand is `f(t, x) = dip(x₁) + ψ(x₀) H_t(x₁)`, where `ψ(s) = (1 - √s)⁺` for `s > 0` and
`ψ(s) = 0` for `s ≤ 0`, `H_t = 2^{-|σ|}` on the Cantor gaps `J σ` with `σ` in the tree coded by `t`
(`RW.SuslinDiagonal.onSet`) and `H_t = 0` elsewhere, and `dip` is the lsc function of
`RW.CantorGaps`.

* A regular subgradient `w` at `y` has `w₀ ≥ -H(y₁)/√y₀` when `y₀ > 0` and `w₀ ≥ 0` otherwise, so a
  horizon subgradient `v` with `v₀ < 0` comes from points with `y₀ ↓ 0` inside gaps; attentive
  convergence then forces the gap heights to vanish and `dip` to converge (`horizon_analysis`).
* Conversely, gaps of unbounded depth converging to a point where `dip` vanishes produce `-e₀` as a
  horizon subgradient, by the concavity of `√` (`neg_e0_mem_horizonSubdifferential`).

So `t` lies in the preimage of the open set `ℝ² × {v ∣ v₀ < 0}` under `t ↦ gph ∂^∞f(t, ·)` exactly
when the tree coded by `t` has a branch in the witness space, i.e. when `t` lies in the non-Borel
Suslin diagonal (`svPreimage_horizon_eq_diagonal`).
-/

import RockafellarWets.Chapter14.CantorGaps
import RockafellarWets.Chapter14.IntegrandOperations
import RockafellarWets.Chapter14.SubgradientMeasurability
import RockafellarWets.Chapter8.HorizonSubgradientSequences

open Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RW.HorizonGraph

open RW.SuslinDiagonal RW.CantorGaps

/-! ### The plane -/

/-- The Euclidean plane `ℝ²`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The point `(a, b)` of the plane. -/
def pt (a b : ℝ) : E2 := WithLp.toLp 2 ![a, b]

@[simp]
theorem pt_zero (a b : ℝ) : pt a b 0 = a := by
  simp [pt]

@[simp]
theorem pt_one (a b : ℝ) : pt a b 1 = b := by
  simp [pt]

theorem continuous_pt : Continuous fun p : ℝ × ℝ ↦ pt p.1 p.2 := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd

theorem continuous_coord (i : Fin 2) : Continuous fun u : E2 ↦ u i :=
  PiLp.continuous_apply 2 _ i

/-- The first basis vector. -/
def e0 : E2 := EuclideanSpace.single 0 1

theorem inner_e0 (v : E2) : ⟪v, e0⟫_ℝ = v 0 := by
  simp [e0, EuclideanSpace.inner_single_right]

theorem norm_e0 : ‖e0‖ = 1 := by
  simp [e0, EuclideanSpace.norm_single]

@[simp]
theorem e0_zero : e0 0 = 1 := by
  simp [e0]

@[simp]
theorem e0_one : e0 1 = 0 := by
  simp [e0]

/-! ### The steep profile -/

/-- The profile `ψ(s) = (1 - √s)⁺` for `s > 0`, `ψ(s) = 0` for `s ≤ 0`. -/
def steep (s : ℝ) : ℝ := if 0 < s then max 0 (1 - Real.sqrt s) else 0

theorem steep_nonneg (s : ℝ) : 0 ≤ steep s := by
  unfold steep
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem steep_le_one (s : ℝ) : steep s ≤ 1 := by
  unfold steep
  split_ifs
  · exact max_le zero_le_one (by linarith [Real.sqrt_nonneg s])
  · exact zero_le_one

theorem steep_of_nonpos {s : ℝ} (hs : s ≤ 0) : steep s = 0 := by
  simp [steep, not_lt.2 hs]

theorem steep_of_mem_Ioo {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : steep s = 1 - Real.sqrt s := by
  have : Real.sqrt s < 1 := by
    have := Real.sqrt_lt_sqrt h0.le h1
    rwa [Real.sqrt_one] at this
  rw [steep, if_pos h0, max_eq_right (by linarith)]

theorem steep_sub_le {y s : ℝ} (hy : 0 < y) (hs : 0 < s) :
    steep (y - s) ≤ steep y + s / Real.sqrt y := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hq : 0 ≤ s / Real.sqrt y := by positivity
  by_cases h : 0 < y - s
  · rw [steep, if_pos h, steep, if_pos hy]
    refine max_le (by positivity) ?_
    have key : Real.sqrt y - Real.sqrt (y - s) ≤ s / Real.sqrt y := by
      rw [le_div_iff₀ hsy]
      have h1 := Real.sq_sqrt hy.le
      have h2 := Real.sq_sqrt h.le
      have h3 := Real.sqrt_nonneg (y - s)
      have hba : Real.sqrt (y - s) ≤ Real.sqrt y := Real.sqrt_le_sqrt (by linarith)
      nlinarith [mul_nonneg h3 (sub_nonneg.2 hba)]
    linarith [le_max_right 0 (1 - Real.sqrt y)]
  · rw [steep_of_nonpos (not_lt.1 h)]
    linarith [steep_nonneg y]

theorem tendsto_steep {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < a n) :
    Tendsto (fun n ↦ steep (a n)) atTop (𝓝 1) := by
  have hc : Continuous fun s : ℝ ↦ max 0 (1 - Real.sqrt s) :=
    continuous_const.max (continuous_const.sub Real.continuous_sqrt)
  have := (hc.tendsto 0).comp ha
  simp only [Real.sqrt_zero, sub_zero, max_eq_right zero_le_one] at this
  refine this.congr' ?_
  filter_upwards [hpos] with n hn
  simp [steep, hn]

/-! ### Regular and horizon subgradients of `x ↦ φ(x₁) + ψ(x₀) H(x₁)` -/

/-- The integrand `x ↦ φ(x₁) + ψ(x₀) H(x₁)`. -/
def gadget (φ H : ℝ → ℝ) (x : E2) : EReal := ((φ (x 1) + steep (x 0) * H (x 1) : ℝ) : EReal)

/-- A one-sided growth bound along `-e` bounds regular subgradients in the direction `e` from
below. -/
theorem neg_le_inner_of_mem_regularSubdifferential {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {F : E → EReal} {y w e : E} (hw : w ∈ regularSubdifferential F y)
    (he : ‖e‖ = 1) {K : ℝ}
    (hK : ∀ c : ℝ, F y = c → ∀ s : ℝ, 0 < s → F (y - s • e) ≤ ((c + K * s : ℝ) : EReal)) :
    -K ≤ ⟪w, e⟫_ℝ := by
  obtain ⟨c, hc, hreg⟩ := hw
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  have ht : Tendsto (fun s : ℝ ↦ y - s • e) (𝓝[>] 0) (𝓝 y) := by
    have h : Continuous fun s : ℝ ↦ y - s • e :=
      continuous_const.sub (continuous_id.smul continuous_const)
    have := h.tendsto 0
    rw [zero_smul, sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨s, hs, hs0⟩ :=
    ((ht.eventually (hreg (ε / 2) (by positivity))).and self_mem_nhdsWithin).exists
  have hs0' : 0 < s := hs0
  have h3 := hs.trans (hK c hc s hs0')
  rw [EReal.coe_le_coe_iff] at h3
  have hsub : y - s • e - y = -(s • e) := by abel
  rw [hsub, inner_neg_right, inner_smul_right, norm_neg, norm_smul, he, Real.norm_eq_abs,
    abs_of_pos hs0', mul_one] at h3
  have h4 : s * (-⟪w, e⟫_ℝ - ε / 2) ≤ s * K := by nlinarith
  have := le_of_mul_le_mul_left h4 hs0'
  linarith

/-- **Horizon subgradients with negative first coordinate.**  For `φ` lsc and `0 ≤ H ≤ 1`, a
horizon subgradient `v` of `x ↦ φ(x₁) + ψ(x₀) H(x₁)` at `x` with `v₀ < 0` forces `x₀ = 0` and comes
from points `z_k → x₁` with `H(z_k) > 0`, `H(z_k) → 0` and `φ(z_k) → φ(x₁)`. -/
theorem horizon_analysis {φ H : ℝ → ℝ} (hφ : LowerSemicontinuous φ) (hH0 : ∀ z, 0 ≤ H z)
    (hH1 : ∀ z, H z ≤ 1) {x v : E2} (hv : v ∈ horizonSubdifferential (gadget φ H) x)
    (hv0 : v 0 < 0) :
    x 0 = 0 ∧ ∃ z : ℕ → ℝ, Tendsto z atTop (𝓝 (x 1)) ∧ (∀ᶠ k in atTop, 0 < H (z k)) ∧
      Tendsto (fun k ↦ H (z k)) atTop (𝓝 0) ∧ Tendsto (fun k ↦ φ (z k)) atTop (𝓝 (φ (x 1))) := by
  have hFx : gadget φ H x = ((φ (x 1) + steep (x 0) * H (x 1) : ℝ) : EReal) := rfl
  rw [mem_horizonSubdifferential_iff_zero_or_scaledSeq hFx] at hv
  rcases hv with rfl | ⟨y, w, t, hy, hw, ht, ht0, htw⟩
  · simp at hv0
  rw [tendsto_attentiveNhds_iff] at hy
  obtain ⟨hyx, hFy⟩ := hy
  set K : E2 → ℝ := fun u ↦ if 0 < u 0 then H (u 1) / Real.sqrt (u 0) else 0 with hKdef
  have hKb : ∀ n, -K (y n) ≤ w n 0 := by
    intro n
    have h := neg_le_inner_of_mem_regularSubdifferential (hw n) norm_e0 (K := K (y n)) ?_
    · rwa [inner_e0] at h
    intro c hc s hs
    have hc' : φ (y n 1) + steep (y n 0) * H (y n 1) = c := EReal.coe_injective hc
    have h1 : (y n - s • e0) 1 = y n 1 := by simp
    have h0 : (y n - s • e0) 0 = y n 0 - s := by simp
    simp only [gadget, EReal.coe_le_coe_iff, h1, h0, ← hc']
    by_cases hpos : 0 < y n 0
    · have h := mul_le_mul_of_nonneg_right (steep_sub_le hpos hs) (hH0 (y n 1))
      simp only [hKdef, if_pos hpos]
      have e : (steep (y n 0) + s / Real.sqrt (y n 0)) * H (y n 1) =
          steep (y n 0) * H (y n 1) + H (y n 1) / Real.sqrt (y n 0) * s := by ring
      linarith
    · rw [steep_of_nonpos (by linarith : y n 0 - s ≤ 0), steep_of_nonpos (not_lt.1 hpos)]
      simp [hKdef, if_neg hpos]
  have htw0 : Tendsto (fun n ↦ t n * w n 0) atTop (𝓝 (v 0)) := by
    have := ((continuous_coord 0).tendsto v).comp htw
    simpa [Function.comp_def] using this
  have hev : ∀ᶠ n in atTop, t n * w n 0 < v 0 / 2 :=
    htw0.eventually (gt_mem_nhds (by linarith))
  have hgood : ∀ᶠ n in atTop,
      0 < y n 0 ∧ 0 < H (y n 1) ∧ Real.sqrt (y n 0) ≤ 2 * t n / (-v 0) := by
    filter_upwards [hev] with n hn
    have hb := hKb n
    have htn := ht n
    have hK : 0 < K (y n) := by
      by_contra hK
      push_neg at hK
      have : 0 ≤ t n * w n 0 := mul_nonneg htn.le (by linarith)
      linarith
    by_cases hpos : 0 < y n 0
    · simp only [hKdef, if_pos hpos] at hK hb
      have hsq := Real.sqrt_pos.2 hpos
      refine ⟨hpos, (div_pos_iff_of_pos_right hsq).1 hK, ?_⟩
      have h1 : -(1 / Real.sqrt (y n 0)) ≤ w n 0 :=
        le_trans (neg_le_neg (div_le_div_of_nonneg_right (hH1 _) hsq.le)) hb
      have h2 : t n * (-(1 / Real.sqrt (y n 0))) < v 0 / 2 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 htn.le) hn
      have h3 : -(v 0) / 2 < t n / Real.sqrt (y n 0) := by
        have : t n * (-(1 / Real.sqrt (y n 0))) = -(t n / Real.sqrt (y n 0)) := by ring
        linarith
      rw [lt_div_iff₀ hsq] at h3
      rw [le_div_iff₀ (by linarith)]
      linarith
    · simp only [hKdef, if_neg hpos] at hK
      exact absurd hK (lt_irrefl 0)
  have hy0 : Tendsto (fun n ↦ y n 0) atTop (𝓝 0) := by
    have hb : Tendsto (fun n ↦ (2 * t n / (-v 0)) ^ 2) atTop (𝓝 0) := by
      have := ((ht0.const_mul 2).div_const (-v 0)).pow 2
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb ?_ ?_
    · filter_upwards [hgood] with n hn
      exact hn.1.le
    · filter_upwards [hgood] with n hn
      obtain ⟨hpos, -, hsq⟩ := hn
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
      rwa [Real.sq_sqrt hpos.le] at this
  have hx0 : x 0 = 0 := tendsto_nhds_unique (((continuous_coord 0).tendsto x).comp hyx) hy0
  have hy1 : Tendsto (fun n ↦ y n 1) atTop (𝓝 (x 1)) := ((continuous_coord 1).tendsto x).comp hyx
  have hFr : Tendsto (fun n ↦ φ (y n 1) + steep (y n 0) * H (y n 1)) atTop (𝓝 (φ (x 1))) := by
    have hFy' : Tendsto (fun n ↦ ((φ (y n 1) + steep (y n 0) * H (y n 1) : ℝ) : EReal)) atTop
        (𝓝 ((φ (x 1) + steep (x 0) * H (x 1) : ℝ) : EReal)) := hFy
    have := EReal.tendsto_coe.1 hFy'
    rwa [hx0, steep_of_nonpos le_rfl, zero_mul, add_zero] at this
  have hsteep : Tendsto (fun n ↦ steep (y n 0)) atTop (𝓝 1) :=
    tendsto_steep hy0 (hgood.mono fun n hn ↦ hn.1)
  have hp0 : ∀ n, 0 ≤ steep (y n 0) * H (y n 1) := fun n ↦ mul_nonneg (steep_nonneg _) (hH0 _)
  have hlow : ∀ ε > 0, ∀ᶠ n in atTop, φ (x 1) - ε < φ (y n 1) := fun ε hε ↦
    hy1.eventually (hφ (x 1) _ (by linarith))
  have hp : Tendsto (fun n ↦ steep (y n 0) * H (y n 1)) atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      exact Eventually.of_forall fun n ↦ lt_of_lt_of_le ha (hp0 n)
    · intro a ha
      filter_upwards [hFr.eventually (gt_mem_nhds (show φ (x 1) < φ (x 1) + a / 2 by linarith)),
        hlow (a / 2) (by linarith)] with n h1 h2
      linarith
  have hφc : Tendsto (fun n ↦ φ (y n 1)) atTop (𝓝 (φ (x 1))) := by
    have := hFr.sub hp
    simpa using this
  have hHc : Tendsto (fun n ↦ H (y n 1)) atTop (𝓝 0) := by
    have := hp.div hsteep one_ne_zero
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [hsteep.eventually_ne one_ne_zero] with n hn
    exact mul_div_cancel_left₀ _ hn
  exact ⟨hx0, fun n ↦ y n 1, hy1, hgood.mono fun n hn ↦ hn.2.1, hHc, hφc⟩

/-- **Horizon subgradient `-e₀`.**  If `z_k → ζ` with `H(z_k) > 0`, `H(z_k) → 0`, `φ(z_k) → φ(ζ)`,
and near each `z_k` the function `H` is constant and `φ` is minimal, then `-e₀` is a horizon
subgradient of `x ↦ φ(x₁) + ψ(x₀) H(x₁)` at `(0, ζ)`. -/
theorem neg_e0_mem_horizonSubdifferential {φ H : ℝ → ℝ} (hH1 : ∀ z, H z ≤ 1) {ζ : ℝ}
    {z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 ζ)) (hHpos : ∀ k, 0 < H (z k))
    (hH : Tendsto (fun k ↦ H (z k)) atTop (𝓝 0)) (hφ : Tendsto (fun k ↦ φ (z k)) atTop (𝓝 (φ ζ)))
    (hloc : ∀ k, ∀ᶠ u in 𝓝 (z k), φ (z k) ≤ φ u ∧ H u = H (z k)) :
    -e0 ∈ horizonSubdifferential (gadget φ H) (pt 0 ζ) := by
  have hFx : gadget φ H (pt 0 ζ) = ((φ ζ : ℝ) : EReal) := by
    simp [gadget, steep_of_nonpos]
  rw [mem_horizonSubdifferential_iff_zero_or_scaledSeq hFx]
  right
  set μ : ℕ → ℝ := fun k ↦ (k : ℝ) + 1 with hμ
  have hμpos : ∀ k, 0 < μ k := fun k ↦ by positivity
  have hμ1 : ∀ k, 1 ≤ μ k := fun k ↦ by simp [hμ]
  set r : ℕ → ℝ := fun k ↦ H (z k) / (2 * μ k) with hr
  have hrpos : ∀ k, 0 < r k := fun k ↦ div_pos (hHpos k) (by linarith [hμpos k])
  have hrle : ∀ k, r k ≤ H (z k) / 2 := fun k ↦ by
    rw [hr]
    exact div_le_div_of_nonneg_left (hHpos k).le (by norm_num) (by linarith [hμ1 k])
  set s : ℕ → ℝ := fun k ↦ r k ^ 2 with hs
  have hs0 : ∀ k, 0 < s k := fun k ↦ by have := hrpos k; positivity
  have hs1 : ∀ k, s k < 1 := fun k ↦ by
    have h1 := hrle k
    have h2 := hH1 (z k)
    have h3 := hrpos k
    simp only [hs]
    nlinarith
  refine ⟨fun k ↦ pt (s k) (z k), fun k ↦ -(μ k) • e0, fun k ↦ (μ k)⁻¹, ?_, fun k ↦ ?_,
    fun k ↦ inv_pos.2 (hμpos k), ?_, ?_⟩
  · rw [tendsto_attentiveNhds_iff]
    have hr0 : Tendsto r atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using hH.div_const 2) (fun k ↦ (hrpos k).le) hrle
    have hs0' : Tendsto s atTop (𝓝 0) := by
      simpa [hs] using hr0.pow 2
    constructor
    · have := (continuous_pt.tendsto (0, ζ)).comp (hs0'.prodMk_nhds hz)
      simpa [Function.comp_def] using this
    · rw [hFx]
      have hprod : Tendsto (fun k ↦ steep (s k) * H (z k)) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hH
          (fun k ↦ mul_nonneg (steep_nonneg _) (hHpos k).le) (fun k ↦ ?_)
        have := mul_le_mul_of_nonneg_right (steep_le_one (s k)) (hHpos k).le
        linarith
      have hsum := hφ.add hprod
      rw [add_zero] at hsum
      have : (gadget φ H ∘ fun k ↦ pt (s k) (z k)) =
          fun k ↦ ((φ (z k) + steep (s k) * H (z k) : ℝ) : EReal) := by
        funext k
        simp [gadget]
      rw [this, EReal.tendsto_coe]
      exact hsum
  · refine ⟨φ (z k) + steep (s k) * H (z k), by simp [gadget], fun ε hε ↦ ?_⟩
    have hev1 : ∀ᶠ u in 𝓝 (pt (s k) (z k)), φ (z k) ≤ φ (u 1) ∧ H (u 1) = H (z k) := by
      have h := (continuous_coord 1).continuousAt (x := pt (s k) (z k))
      rw [ContinuousAt, pt_one] at h
      exact h.eventually (hloc k)
    have hev2 : ∀ᶠ u in 𝓝 (pt (s k) (z k)), 0 < u 0 ∧ u 0 < 1 := by
      have h := (continuous_coord 0).continuousAt (x := pt (s k) (z k))
      rw [ContinuousAt, pt_zero] at h
      exact h.eventually (Ioo_mem_nhds (hs0 k) (hs1 k))
    filter_upwards [hev1, hev2] with u ⟨hφu, hHu⟩ ⟨hu0, hu1⟩
    simp only [gadget]
    rw [EReal.coe_le_coe_iff]
    have hin : ⟪-(μ k) • e0, u - pt (s k) (z k)⟫_ℝ = -(μ k) * (u 0 - s k) := by
      rw [real_inner_smul_left, real_inner_comm, inner_e0]
      simp
    rw [hin, hHu, steep_of_mem_Ioo hu0 hu1, steep_of_mem_Ioo (hs0 k) (hs1 k)]
    have hsq : Real.sqrt (s k) = r k := by
      simp only [hs]
      exact Real.sqrt_sq (hrpos k).le
    have hHr : H (z k) = 2 * μ k * r k := by
      simp only [hr]
      rw [mul_div_assoc', mul_div_cancel_left₀ _ (mul_pos two_pos (hμpos k)).ne']
    have hnorm : 0 ≤ ε * ‖u - pt (s k) (z k)‖ := by positivity
    have hsk : s k = r k ^ 2 := rfl
    rw [hsq, hHr, hsk]
    have ha : Real.sqrt (u 0) ^ 2 = u 0 := Real.sq_sqrt hu0.le
    have hmu : μ k * u 0 = μ k * Real.sqrt (u 0) ^ 2 := by rw [ha]
    have hkey := mul_nonneg (hμpos k).le (sq_nonneg (Real.sqrt (u 0) - r k))
    rw [hsk] at hnorm
    nlinarith [hkey, hmu, hφu, hnorm]
  · have : Tendsto μ atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact this.inv_tendsto_atTop
  · have : ∀ k, (μ k)⁻¹ • (-(μ k) • e0) = -e0 := fun k ↦ by
      rw [smul_smul, mul_neg, inv_mul_cancel₀ (hμpos k).ne', neg_one_smul]
    simp only [this]
    exact tendsto_const_nhds

/-! ### The counterexample integrand -/

section Integrand

/-- Gap heights `2^{-|σ|}`. -/
def height (σ : List Bool) : ℝ := (1 / 2 : ℝ) ^ σ.length

theorem height_pos (σ : List Bool) : 0 < height σ := by
  unfold height
  positivity

theorem height_le_one (σ : List Bool) : height σ ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

open scoped Classical in
/-- `H_t(z) = 2^{-|σ|}` on the gaps `J σ` with `σ` in the tree coded by `t`, and `0` elsewhere. -/
def gapHeight (t : ℕ → ℕ) (z : ℝ) : ℝ :=
  ⨆ σ : List Bool, if σ ∈ onSet t ∧ z ∈ J σ then height σ else 0

open scoped Classical in
theorem bddAbove_gapHeight (t : ℕ → ℕ) (z : ℝ) :
    BddAbove (range fun σ : List Bool ↦ if σ ∈ onSet t ∧ z ∈ J σ then height σ else 0) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨σ, rfl⟩
  dsimp only
  split_ifs
  · exact height_le_one σ
  · exact zero_le_one

theorem gapHeight_eq_of_mem {t : ℕ → ℕ} {z : ℝ} {σ : List Bool} (hσ : σ ∈ onSet t)
    (hz : z ∈ J σ) : gapHeight t z = height σ := by
  unfold gapHeight
  apply le_antisymm
  · refine ciSup_le fun τ ↦ ?_
    split_ifs with h
    · have : τ = σ := by
        by_contra hne
        exact Set.disjoint_left.1 (disjoint_J hne) h.2 hz
      rw [this]
    · exact (height_pos σ).le
  · exact le_ciSup_of_le (bddAbove_gapHeight t z) σ (by rw [if_pos ⟨hσ, hz⟩])

theorem gapHeight_eq_zero {t : ℕ → ℕ} {z : ℝ} (h : ∀ σ ∈ onSet t, z ∉ J σ) :
    gapHeight t z = 0 := by
  unfold gapHeight
  have : ∀ σ : List Bool, ¬(σ ∈ onSet t ∧ z ∈ J σ) := fun σ hσ ↦ h σ hσ.1 hσ.2
  simp only [this, if_false, ciSup_const]

theorem gapHeight_nonneg (t : ℕ → ℕ) (z : ℝ) : 0 ≤ gapHeight t z := by
  refine le_ciSup_of_le (bddAbove_gapHeight t z) [] ?_
  split_ifs
  · exact (height_pos _).le
  · exact le_rfl

theorem gapHeight_le_one (t : ℕ → ℕ) (z : ℝ) : gapHeight t z ≤ 1 := by
  refine ciSup_le fun σ ↦ ?_
  split_ifs
  · exact height_le_one σ
  · exact zero_le_one

theorem exists_of_gapHeight_pos {t : ℕ → ℕ} {z : ℝ} (h : 0 < gapHeight t z) :
    ∃ σ ∈ onSet t, z ∈ J σ ∧ gapHeight t z = height σ := by
  by_contra hne
  push_neg at hne
  have : ∀ σ ∈ onSet t, z ∉ J σ := fun σ hσ hz ↦ hne σ hσ hz (gapHeight_eq_of_mem hσ hz)
  rw [gapHeight_eq_zero this] at h
  exact lt_irrefl 0 h

/-- The counterexample integrand `f(t, x) = dip(x₁) + ψ(x₀) H_t(x₁)` on `(ℕ → ℕ) × ℝ²`. -/
def integrand (t : ℕ → ℕ) : E2 → EReal := gadget dip (gapHeight t)

open scoped Classical in
/-- The gadget on a single gap. -/
def bump (σ : List Bool) (x : E2) : ℝ :=
  if 0 < x 0 ∧ x 1 ∈ J σ then height σ * max 0 (1 - Real.sqrt (x 0)) else 0

open scoped Classical in
/-- The integrand restricted to a single gap, switched on by the parameter. -/
def piece (σ : List Bool) (t : ℕ → ℕ) (x : E2) : EReal :=
  ((dip (x 1) + if σ ∈ onSet t then bump σ x else 0 : ℝ) : EReal)

theorem bump_nonneg (σ : List Bool) (x : E2) : 0 ≤ bump σ x := by
  unfold bump
  split_ifs
  · exact mul_nonneg (height_pos σ).le (le_max_left _ _)
  · exact le_rfl

theorem lowerSemicontinuous_ite_of_isOpen {X : Type*} [TopologicalSpace X] (p : X → Prop)
    [DecidablePred p] (hV : IsOpen {x | p x}) {g : X → ℝ} (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) : LowerSemicontinuous fun x ↦ if p x then g x else 0 := by
  intro x y hy
  dsimp only at hy ⊢
  by_cases hx : p x
  · rw [if_pos hx] at hy
    filter_upwards [hV.mem_nhds hx, hg.continuousAt.eventually (lt_mem_nhds hy)] with x' hx' hlt
    rw [if_pos hx']
    exact hlt
  · rw [if_neg hx] at hy
    refine Eventually.of_forall fun x' ↦ ?_
    split_ifs
    · exact hy.trans_le (hg0 x')
    · exact hy

open scoped Classical in
theorem lowerSemicontinuous_bump (σ : List Bool) : LowerSemicontinuous (bump σ) := by
  have hJ : IsOpen (J σ) := isOpen_Ioo
  have hV : IsOpen {x : E2 | 0 < x 0 ∧ x 1 ∈ J σ} :=
    (isOpen_lt continuous_const (continuous_coord 0)).inter (hJ.preimage (continuous_coord 1))
  exact lowerSemicontinuous_ite_of_isOpen (fun x : E2 ↦ 0 < x 0 ∧ x 1 ∈ J σ) hV
    (continuous_const.mul (continuous_const.max (continuous_const.sub
      (Real.continuous_sqrt.comp (continuous_coord 0)))))
    fun x ↦ mul_nonneg (height_pos σ).le (le_max_left _ _)

open scoped Classical in
theorem isNormalIntegrand_piece (σ : List Bool) : IsNormalIntegrand (piece σ) := by
  set A := {t : ℕ → ℕ | σ ∈ onSet t}
  set G₁ : E2 → EReal := fun x ↦ ((dip (x 1) + bump σ x : ℝ) : EReal)
  set G₀ : E2 → EReal := fun x ↦ ((dip (x 1) : ℝ) : EReal)
  have hdip : LowerSemicontinuous fun x : E2 ↦ dip (x 1) :=
    lowerSemicontinuous_dip.comp (continuous_coord 1)
  have hG₁ : LowerSemicontinuous G₁ :=
    continuous_coe_real_ereal.comp_lowerSemicontinuous (hdip.add (lowerSemicontinuous_bump σ))
      EReal.coe_strictMono.monotone
  have hG₀ : LowerSemicontinuous G₀ :=
    continuous_coe_real_ereal.comp_lowerSemicontinuous hdip EReal.coe_strictMono.monotone
  have heq : piece σ = fun t ↦ if t ∈ A then G₁ else G₀ := by
    funext t x
    simp only [piece, G₁, G₀, A, mem_setOf_eq]
    split_ifs <;> simp
  rw [heq]
  refine ⟨fun t ↦ ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact (lsc_iff_epigraph_closed_ereal _).1 hG₁
    · exact (lsc_iff_epigraph_closed_ereal _).1 hG₀
  · have : epiMapping (fun t ↦ if t ∈ A then G₁ else G₀) =
        fun t ↦ if t ∈ A then epigraph G₁ else epigraph G₀ := by
      funext t
      unfold epiMapping
      dsimp only
      split_ifs <;> rfl
    rw [this]
    convert SvMeasurable.ite (measurableSet_mem_onSet σ) (svMeasurable_const (epigraph G₁))
      (svMeasurable_const (epigraph G₀)) using 1

theorem steep_mul_height_eq_bump {σ : List Bool} {x : E2} (hJ : x 1 ∈ J σ) :
    steep (x 0) * height σ = bump σ x := by
  by_cases hx : 0 < x 0
  · simp only [steep, bump, if_pos hx, if_pos (And.intro hx hJ)]
    ring
  · simp [steep, bump, hx]

open scoped Classical in
theorem integrand_eq_iSup : integrand = fun t x ↦ ⨆ σ, piece σ t x := by
  funext t x
  apply le_antisymm
  · by_cases h : ∃ σ ∈ onSet t, x 1 ∈ J σ
    · obtain ⟨σ₀, hσ₀, hJ⟩ := h
      refine le_iSup_of_le σ₀ (le_of_eq ?_)
      simp only [integrand, gadget, piece, if_pos hσ₀, gapHeight_eq_of_mem hσ₀ hJ,
        steep_mul_height_eq_bump hJ]
    · push_neg at h
      refine le_iSup_of_le [] ?_
      simp only [integrand, gadget, piece, gapHeight_eq_zero h, mul_zero, add_zero]
      rw [EReal.coe_le_coe_iff]
      have : 0 ≤ (if [] ∈ onSet t then bump [] x else 0) := by
        split_ifs
        · exact bump_nonneg _ _
        · exact le_rfl
      linarith
  · refine iSup_le fun σ ↦ ?_
    simp only [integrand, gadget, piece]
    rw [EReal.coe_le_coe_iff]
    have hp := mul_nonneg (steep_nonneg (x 0)) (gapHeight_nonneg t (x 1))
    by_cases hσ : σ ∈ onSet t
    · rw [if_pos hσ]
      by_cases hJ : x 1 ∈ J σ
      · rw [gapHeight_eq_of_mem hσ hJ, steep_mul_height_eq_bump hJ]
      · have : bump σ x = 0 := by simp [bump, hJ]
        rw [this]
        linarith
    · rw [if_neg hσ]
      linarith

/-- The counterexample integrand is a normal integrand (a countable supremum of normal pieces,
14.44(a)). -/
theorem isNormalIntegrand_integrand : IsNormalIntegrand integrand := by
  rw [integrand_eq_iSup]
  exact IsNormalIntegrand.iSup isNormalIntegrand_piece

theorem isProper_integrand (t : ℕ → ℕ) : IsProper (integrand t) :=
  ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩

/-- The preimage of `ℝ² × {v ∣ v₀ < 0}` under `t ↦ gph ∂^∞f(t, ·)` is the Suslin diagonal. -/
theorem svPreimage_horizon_eq_diagonal :
    svPreimage (fun t ↦ svGraph (horizonSubdifferential (integrand t)))
      (univ ×ˢ {v : E2 | v 0 < 0}) = SuslinDiagonal.diagonal := by
  ext t
  rw [mem_svPreimage, diagonal_eq]
  constructor
  · rintro ⟨⟨x, v⟩, hv, -, hv0⟩
    simp only [mem_svGraph] at hv
    simp only [mem_setOf_eq] at hv0
    obtain ⟨-, z, hz, hHpos, hH, hφ⟩ :=
      horizon_analysis lowerSemicontinuous_dip (gapHeight_nonneg t) (gapHeight_le_one t) hv hv0
    obtain ⟨N, hN⟩ := eventually_atTop.1 hHpos
    have hσ : ∀ k, ∃ σ ∈ onSet t, z (k + N) ∈ J σ ∧ gapHeight t (z (k + N)) = height σ :=
      fun k ↦ exists_of_gapHeight_pos (hN _ (Nat.le_add_left N k))
    choose σ hσO hσJ hσH using hσ
    have hHs : Tendsto (fun k ↦ height (σ k)) atTop (𝓝 0) := by
      have := hH.comp (tendsto_add_atTop_nat N)
      exact this.congr fun k ↦ hσH k
    have hlen : Tendsto (fun k ↦ (σ k).length) atTop atTop := by
      rw [tendsto_atTop]
      intro M
      have : ∀ᶠ k in atTop, height (σ k) < (1 / 2 : ℝ) ^ M :=
        hHs.eventually (gt_mem_nhds (by positivity))
      filter_upwards [this] with k hk
      by_contra hlt
      push_neg at hlt
      have : (1 / 2 : ℝ) ^ M ≤ (1 / 2 : ℝ) ^ (σ k).length :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt.le
      exact absurd hk (not_lt.2 this)
    have hz' : Tendsto (fun k ↦ z (k + N)) atTop (𝓝 (x 1)) := hz.comp (tendsto_add_atTop_nat N)
    obtain ⟨b, hb, hpre⟩ := exists_point_of_tendsto (fun k ↦ J_subset_I _ (hσJ k)) hlen hz'
    refine ⟨b, ?_, fun m ↦ ?_⟩
    · have hdip : dip (x 1) = 0 := by
        have h1 := hφ.comp (tendsto_add_atTop_nat N)
        have h2 : (fun k ↦ dip (z k)) ∘ (fun k ↦ k + N) = fun _ ↦ 0 :=
          funext fun k ↦ dip_eq_zero_of_mem_J (hσJ k)
        rw [h2] at h1
        exact (tendsto_nhds_unique h1 tendsto_const_nhds)
      rw [hb] at hdip
      exact (dip_point_eq_zero_iff b).1 hdip
    · obtain ⟨k, hk⟩ := (hpre m).exists
      rw [← hk]
      exact take_mem_onSet (hσO k) m
  · rintro ⟨b, hbW, hpre⟩
    set z : ℕ → ℝ := fun k ↦ left (pre b k) + 3 / 2 * (1 / 3 : ℝ) ^ (k + 1) with hzdef
    have hzJ : ∀ k, z k ∈ J (pre b k) := fun k ↦ by
      have := pow_pos (by norm_num : (0 : ℝ) < 1 / 3) (k + 1)
      simp only [J, length_pre, mem_Ioo, hzdef]
      constructor <;> linarith
    have hHz : ∀ k, gapHeight t (z k) = height (pre b k) := fun k ↦
      gapHeight_eq_of_mem (hpre k) (hzJ k)
    have hzlim : Tendsto z atTop (𝓝 (point b)) := by
      have hb : ∀ k, |z k - point b| ≤ (1 / 3 : ℝ) ^ k := fun k ↦ by
        have := abs_sub_le_of_mem_I (J_subset_I _ (hzJ k)) (point_mem_I b k)
        rwa [length_pre] at this
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun k ↦ dist_nonneg)
        (fun k ↦ by rw [Real.dist_eq]; exact hb k)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))
    have hdipz : ∀ k, dip (z k) = 0 := fun k ↦ dip_eq_zero_of_mem_J (hzJ k)
    have hneg := neg_e0_mem_horizonSubdifferential (φ := dip) (H := gapHeight t)
      (gapHeight_le_one t) hzlim (fun k ↦ by rw [hHz]; exact height_pos _)
      (by
        simp only [hHz, height, length_pre]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      (by
        simp only [hdipz, (dip_point_eq_zero_iff b).2 hbW]
        exact tendsto_const_nhds)
      (fun k ↦ by
        have hopen : IsOpen (J (pre b k)) := isOpen_Ioo
        filter_upwards [hopen.mem_nhds (hzJ k)] with u hu
        exact ⟨by rw [hdipz k, dip_eq_zero_of_mem_J hu],
          by rw [gapHeight_eq_of_mem (hpre k) hu, hHz]⟩)
    exact ⟨(pt 0 (point b), -e0), hneg, mem_univ _, by simp⟩

end Integrand

/-- **The graphical part of Theorem 14.56 needs completeness.**  On the Baire space `ℕ → ℕ` with
its Borel σ-field there is a proper normal integrand `f` on `ℝ²` such that `t ↦ gph ∂f(t, ·)` is
measurable (as always, `svMeasurable_svGraph_subdifferential`) but `t ↦ gph ∂^∞f(t, ·)` is not:
the preimage of the open set `ℝ² × {v ∣ v₀ < 0}` is the non-Borel Suslin diagonal. -/
theorem horizon_graph_counterexample :
    ∃ f : (ℕ → ℕ) → E2 → EReal, IsNormalIntegrand f ∧ (∀ t, IsProper (f t)) ∧
      SvMeasurable (fun t ↦ svGraph (subdifferential (f t))) ∧
      ¬ SvMeasurable (fun t ↦ svGraph (horizonSubdifferential (f t))) := by
  refine ⟨integrand, isNormalIntegrand_integrand, isProper_integrand,
    svMeasurable_svGraph_subdifferential isNormalIntegrand_integrand, fun h ↦ ?_⟩
  have hO : IsOpen ((univ : Set E2) ×ˢ {v : E2 | v 0 < 0}) :=
    isOpen_univ.prod (isOpen_lt (continuous_coord 0) continuous_const)
  have := h _ hO
  rw [svPreimage_horizon_eq_diagonal] at this
  exact not_measurableSet_diagonal this

end RW.HorizonGraph
