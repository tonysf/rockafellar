/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Approximation of Normal Vectors

Exercise 6.18.  A normal vector to a closed set is approximated by *proximal*
normals at nearby points, and, when the set is only the outer limit of a
sequence of closed sets, by proximal normals to a subsequence of those sets.

Part (a) is the projection step of the Guide.  Moving from `x̄` a small
distance `δ` in the direction of a *regular* normal `v̄` and taking any nearest
point `x ∈ P_C(x̄ + δv̄)`, the displacement `v = δ⁻¹(x̄ + δv̄ - x)` is a proximal
normal at `x` by construction, since `x + δv = x̄ + δv̄`.  The nearest-point
inequality gives `|x - x̄|² ≤ 2δ⟪v̄, x - x̄⟫`, while `|x - x̄| ≤ 2δ|v̄|` keeps `x`
inside the neighbourhood where the little-o inequality 6(4) applies; together
they force `δ|v - v̄| = |x - x̄| = o(δ)`.  No normalization of `v̄` is needed:
the term `δ²|v̄|²` cancels on the two sides of the nearest-point inequality, so
the Guide's reduction to `|v̄| = 1` can be skipped.  The passage from regular
normals to normal vectors is Definition 6.3 plus one triangle inequality.

Part (b) never assumes that `Cν` converges; only the printed hypothesis
`limsup_ν Cν = C` is used.  For a proximal normal `v̄`, with `x̄ ∈ P_C(x̄ + τv̄)`,
the compactness theorem 4.18 extracts a subsequence converging to some `D`,
the extraction being arranged to retain `x̄ ∈ D`.  Being an outer limit of a
subsequence, `D ⊆ limsup_ν Cν = C`, so the nearest-point property survives the
restriction: `x̄ ∈ P_D(x̄ + τv̄)`.  Example 5.35 then turns `P_{Cν} →g P_D` into
the required sequences.  A general normal vector is reached from there by (a)
together with the closedness of the outer limit of the graphs; that closedness
replaces the Guide's diagonalization.

The parenthetical clause of (b), that the index set is `ℕ` itself when `Cν → C`
actually holds, is recorded at the end of the file.  It is the same argument
run with `D = C`, so that no subsequence is taken and the graphical *inner*
limit appears in place of the outer one; the finitely many indices before the
inner limit takes effect are filled in from the nonemptiness of the `Cν`.

The book claims only the outer inclusion `N_C ⊂ g-limsup_ν N_{Cν}`, and the
example printed after 6.18 shows that it can be strict, so nothing here
asserts graphical convergence of the normal cone mappings.
-/

import RockafellarWets.Chapter4.SetConvergenceCompactness
import RockafellarWets.Chapter6.ProximalNormals

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section NormalApproximation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A proximal normal is attached to a point of the set. -/
private theorem mem_of_mem_proximalNormalCone {C : Set E} {x v : E}
    (hv : v ∈ proximalNormalCone C x) : x ∈ C := by
  obtain ⟨τ, -, hproj⟩ := hv
  exact hproj.1

/-- Every proximal normal is a normal vector, by Example 6.16 and 6(7). -/
private theorem proximalNormalCone_subset_normalCone (C : Set E) (x : E) :
    proximalNormalCone C x ⊆ normalCone C x := fun _ hv ↦
  regularNormalCone_subset_normalCone C x
    (proximalNormalCone_subset_regularNormalCone hv)

/-- Graphical outer limits are monotone in the mappings. -/
private theorem graphicalOuterLimit_mono {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {Sseq Tseq : ℕ → X → Set Y}
    (h : ∀ n x, Sseq n x ⊆ Tseq n x) (x : X) :
    graphicalOuterLimit Sseq x ⊆ graphicalOuterLimit Tseq x := fun _ hu ↦
  outerSetLimit_mono (fun n ↦ svGraph_subset_svGraph_iff.2 (h n)) hu

/-! ### Exercise 6.18(a): proximal normals approximate normal vectors -/

section PartA

variable [FiniteDimensional ℝ E]

/-- The projection step of the Guide to 6.18(a).  Take one step of length `δ`
from `x₀ ∈ C` in the direction `v₀` and project back: any nearest point `x`
carries the proximal normal `v` obtained by rescaling the displacement, and
the displayed identity and three estimates are what the `ε`-statement needs.

Nothing is assumed about `v₀` beyond `x₀ ∈ C`; the regularity of `v₀` enters
only when the quadratic inequality is combined with 6(4). -/
theorem exists_mem_proximalNormalCone_projection_step {C : Set E} (hC : IsClosed C)
    {x₀ : E} (hx₀ : x₀ ∈ C) (v₀ : E) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x v : E, x ∈ C ∧ v ∈ proximalNormalCone C x ∧
      x + δ • v = x₀ + δ • v₀ ∧
      ‖x - x₀‖ ≤ 2 * (δ * ‖v₀‖) ∧
      ‖x - x₀‖ ^ 2 ≤ 2 * δ * ⟪v₀, x - x₀⟫_ℝ ∧
      δ * ‖v - v₀‖ = ‖x - x₀‖ := by
  have hδne : δ ≠ 0 := ne_of_gt hδ
  obtain ⟨x, hxproj⟩ := projMapping_nonempty hC ⟨x₀, hx₀⟩ (x₀ + δ • v₀)
  obtain ⟨hxC, hxmin⟩ := hxproj
  have hz₀ : ‖x₀ - (x₀ + δ • v₀)‖ = δ * ‖v₀‖ := by
    have h : x₀ - (x₀ + δ • v₀) = -(δ • v₀) := by module
    rw [h, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
  have hxle : ‖x - (x₀ + δ • v₀)‖ ≤ δ * ‖v₀‖ := by
    rw [← hz₀]
    exact hxmin x₀ hx₀
  have hxv : x + δ • (δ⁻¹ • ((x₀ + δ • v₀) - x)) = x₀ + δ • v₀ := by
    rw [smul_smul, mul_inv_cancel₀ hδne, one_smul]
    abel
  refine ⟨x, δ⁻¹ • ((x₀ + δ • v₀) - x), hxC, ⟨δ, hδ, ?_⟩, hxv, ?_, ?_, ?_⟩
  · rw [hxv]
    exact ⟨hxC, hxmin⟩
  · have htri : ‖x - x₀‖ ≤ ‖x - (x₀ + δ • v₀)‖ + ‖(x₀ + δ • v₀) - x₀‖ := by
      simp only [← dist_eq_norm]
      exact dist_triangle _ _ _
    have hlast : ‖(x₀ + δ • v₀) - x₀‖ = δ * ‖v₀‖ := by
      have h : (x₀ + δ • v₀) - x₀ = δ • v₀ := by module
      rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    rw [hlast] at htri
    linarith
  · have hsq : ‖x - (x₀ + δ • v₀)‖ ^ 2 ≤ (δ * ‖v₀‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hxle
    have hexp : ‖x - (x₀ + δ • v₀)‖ ^ 2
        = ‖x - x₀‖ ^ 2 - 2 * (δ * ⟪v₀, x - x₀⟫_ℝ) + (δ * ‖v₀‖) ^ 2 := by
      have h : x - (x₀ + δ • v₀) = (x - x₀) - δ • v₀ := by module
      rw [h, norm_sub_sq_real, real_inner_smul_right, real_inner_comm (x - x₀) v₀,
        norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    rw [hexp] at hsq
    linarith
  · have h : δ⁻¹ • ((x₀ + δ • v₀) - x) - v₀ = δ⁻¹ • (x₀ - x) := by
      match_scalars <;> field_simp
      ring
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hδ), ← mul_assoc,
      mul_inv_cancel₀ hδne, one_mul, norm_sub_rev]

/-- **Exercise 6.18(a)** for a regular normal.  This is the heart of the
matter: the projection step is run with a step length small enough that the
little-o inequality 6(4) applies at the projected point. -/
theorem exists_mem_proximalNormalCone_close_of_mem_regularNormalCone
    {C : Set E} (hC : IsClosed C) {x₀ v₀ : E}
    (hv₀ : v₀ ∈ regularNormalCone C x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ x v : E, x ∈ C ∧ v ∈ proximalNormalCone C x ∧
      ‖x - x₀‖ < ε ∧ ‖v - v₀‖ < ε := by
  obtain ⟨hx₀, hreg⟩ := mem_regularNormalCone_iff.1 hv₀
  obtain ⟨ρ, hρ, hlo⟩ := hreg (ε / 4) (by positivity)
  have hMpos : (0 : ℝ) < ‖v₀‖ + 1 := by positivity
  have hMne : ‖v₀‖ + 1 ≠ 0 := ne_of_gt hMpos
  have hrpos : (0 : ℝ) < min ρ ε := lt_min hρ hε
  set δ : ℝ := min ρ ε / (4 * (‖v₀‖ + 1)) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    exact div_pos hrpos (by positivity)
  have hδM : δ * (‖v₀‖ + 1) = min ρ ε / 4 := by
    rw [hδdef]
    field_simp
  obtain ⟨x, v, hxC, hprox, -, hdist, hquad, hvnorm⟩ :=
    exists_mem_proximalNormalCone_projection_step hC hx₀ v₀ hδ
  have hsmall : ‖x - x₀‖ < min ρ ε := by
    have h1 : δ * ‖v₀‖ ≤ δ * (‖v₀‖ + 1) := by nlinarith
    linarith
  have hxρ : ‖x - x₀‖ < ρ := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hxε : ‖x - x₀‖ < ε := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hlo' : ⟪v₀, x - x₀⟫_ℝ ≤ ε / 4 * ‖x - x₀‖ := hlo x hxC hxρ
  have hstep : ‖x - x₀‖ ^ 2 ≤ δ * ε / 2 * ‖x - x₀‖ := by
    have h2 : 2 * δ * ⟪v₀, x - x₀⟫_ℝ ≤ 2 * δ * (ε / 4 * ‖x - x₀‖) :=
      mul_le_mul_of_nonneg_left hlo' (by positivity)
    linarith
  have hkey : ‖x - x₀‖ ≤ δ * ε / 2 := by
    rcases eq_or_lt_of_le (norm_nonneg (x - x₀)) with h0 | h0
    · rw [← h0]
      positivity
    · refine le_of_mul_le_mul_right ?_ h0
      nlinarith
  refine ⟨x, v, hxC, hprox, hxε, ?_⟩
  have hmul : δ * ‖v - v₀‖ ≤ δ * (ε / 2) := by
    rw [hvnorm]
    linarith
  have := le_of_mul_le_mul_left hmul hδ
  linarith

/-- **Exercise 6.18(a)**.  Definition 6.3 supplies regular normals at points
arbitrarily close to `x̄`, and the regular case is applied at one of them. -/
theorem exists_mem_proximalNormalCone_close_of_mem_normalCone
    {C : Set E} (hC : IsClosed C) {xbar vbar : E}
    (hvbar : vbar ∈ normalCone C xbar) {ε : ℝ} (hε : 0 < ε) :
    ∃ x v : E, x ∈ C ∧ v ∈ proximalNormalCone C x ∧
      ‖x - xbar‖ < ε ∧ ‖v - vbar‖ < ε := by
  obtain ⟨-, xs, vs, -, hxsto, hvs, hvsto⟩ := hvbar
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hxsto (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hvsto (ε / 2) (by positivity)
  have hx : ‖xs (max N₁ N₂) - xbar‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hN₁ _ (le_max_left _ _)
  have hv : ‖vs (max N₁ N₂) - vbar‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hN₂ _ (le_max_right _ _)
  obtain ⟨x, v, hxC, hprox, hxlt, hvlt⟩ :=
    exists_mem_proximalNormalCone_close_of_mem_regularNormalCone hC
      (hvs (max N₁ N₂)) (half_pos hε)
  refine ⟨x, v, hxC, hprox, ?_, ?_⟩
  · have htri : ‖x - xbar‖ ≤ ‖x - xs (max N₁ N₂)‖ + ‖xs (max N₁ N₂) - xbar‖ := by
      simp only [← dist_eq_norm]
      exact dist_triangle _ _ _
    linarith
  · have htri : ‖v - vbar‖ ≤ ‖v - vs (max N₁ N₂)‖ + ‖vs (max N₁ N₂) - vbar‖ := by
      simp only [← dist_eq_norm]
      exact dist_triangle _ _ _
    linarith

/-- **Exercise 6.18(a)** with the conclusion `v ∈ N_C(x)` recorded explicitly:
the approximating vector is a proximal normal, hence by Example 6.16 and 6(7)
also a regular normal and a normal vector at the approximating point. -/
theorem exists_mem_proximalNormalCone_mem_normalCone_close_of_mem_normalCone
    {C : Set E} (hC : IsClosed C) {xbar vbar : E}
    (hvbar : vbar ∈ normalCone C xbar) {ε : ℝ} (hε : 0 < ε) :
    ∃ x v : E, x ∈ C ∧ v ∈ proximalNormalCone C x ∧
      v ∈ regularNormalCone C x ∧ v ∈ normalCone C x ∧
      ‖x - xbar‖ < ε ∧ ‖v - vbar‖ < ε := by
  obtain ⟨x, v, hxC, hprox, hxlt, hvlt⟩ :=
    exists_mem_proximalNormalCone_close_of_mem_normalCone hC hvbar hε
  exact ⟨x, v, hxC, hprox, proximalNormalCone_subset_regularNormalCone hprox,
    proximalNormalCone_subset_normalCone C x hprox, hxlt, hvlt⟩

/-- **Exercise 6.18(a)** in the printed ball form: for every `ε > 0` there are
`x ∈ IB(x̄, ε) ∩ C` and a proximal normal `v ∈ IB(v̄, ε)` to `C` at `x`.

The printed hypothesis `x̄ ∈ C` is already carried by `v̄ ∈ N_C(x̄)`, which is
why it is not consumed by the proof. -/
theorem exists_proximalNormal_close_of_mem_normalCone
    {C : Set E} (hC : IsClosed C) {xbar vbar : E} (_hxbar : xbar ∈ C)
    (hvbar : vbar ∈ normalCone C xbar) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ C ∩ Metric.ball xbar ε,
      (proximalNormalCone C x ∩ Metric.ball vbar ε).Nonempty := by
  obtain ⟨x, v, hxC, hprox, hxlt, hvlt⟩ :=
    exists_mem_proximalNormalCone_close_of_mem_normalCone hC hvbar hε
  exact ⟨x, ⟨hxC, by rwa [Metric.mem_ball, dist_eq_norm]⟩,
    v, hprox, by rwa [Metric.mem_ball, dist_eq_norm]⟩

/-- **Exercise 6.18(a)** exactly as printed: there are `x ∈ IB(x̄, ε) ∩ C` and
`v ∈ IB(v̄, ε) ∩ N_C(x)` such that `v` is a proximal normal to `C` at `x`. -/
theorem exists_proximalNormal_mem_normalCone_close_of_mem_normalCone
    {C : Set E} (hC : IsClosed C) {xbar vbar : E} (_hxbar : xbar ∈ C)
    (hvbar : vbar ∈ normalCone C xbar) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ C ∩ Metric.ball xbar ε,
      ∃ v ∈ normalCone C x ∩ Metric.ball vbar ε, v ∈ proximalNormalCone C x := by
  obtain ⟨x, v, hxC, hprox, -, hnorm, hxlt, hvlt⟩ :=
    exists_mem_proximalNormalCone_mem_normalCone_close_of_mem_normalCone hC hvbar hε
  exact ⟨x, ⟨hxC, by rwa [Metric.mem_ball, dist_eq_norm]⟩,
    v, ⟨hnorm, by rwa [Metric.mem_ball, dist_eq_norm]⟩, hprox⟩

/-- The density form of **6.18(a)**: every normal vector is the limit of
proximal normals at points of `C` converging to `x̄`. -/
theorem exists_seq_mem_proximalNormalCone_tendsto_of_mem_normalCone
    {C : Set E} (hC : IsClosed C) {xbar vbar : E}
    (hvbar : vbar ∈ normalCone C xbar) :
    ∃ xs vs : ℕ → E, (∀ n, xs n ∈ C) ∧
      (∀ n, vs n ∈ proximalNormalCone C (xs n)) ∧
      Tendsto xs atTop (nhds xbar) ∧ Tendsto vs atTop (nhds vbar) := by
  have hpick : ∀ n : ℕ, ∃ q : E × E, q.1 ∈ C ∧ q.2 ∈ proximalNormalCone C q.1 ∧
      ‖q.1 - xbar‖ < 1 / ((n : ℝ) + 1) ∧ ‖q.2 - vbar‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨x, v, hxC, hprox, hxlt, hvlt⟩ :=
      exists_mem_proximalNormalCone_close_of_mem_normalCone hC hvbar
        (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    exact ⟨(x, v), hxC, hprox, hxlt, hvlt⟩
  choose q hq₁ hq₂ hq₃ hq₄ using hpick
  refine ⟨fun n ↦ (q n).1, fun n ↦ (q n).2, hq₁, hq₂, ?_, ?_⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_eq_norm]
    exact (hq₃ n).le
  · rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_eq_norm]
    exact (hq₄ n).le

end PartA

/-! ### Exercise 6.18(b): normals along a sequence of sets

The main results assume of `Cseq` only the printed hypothesis
`limsup_ν Cν = C`, written `outerSetLimit Cseq = C`.  Painleve--Kuratowski
convergence of `Cseq` is never used for them: assuming it would lose the point
of 6.18(b), which is precisely that an outer limit suffices.  The
parenthetical clause of the exercise, that the index set may be taken to be
`ℕ` itself when `Cν → C` actually holds, is recorded separately at the end. -/

section PartB

variable [FiniteDimensional ℝ E]

/-- The step common to both halves of 6.18(b).  Once a set `D` has been
produced for which `x̄` is a nearest point of `D` to `x̄ + τv̄`, Example 5.35
turns `Dν → D` into proximal normals `vν → v̄` at points `xν → x̄`.  The
membership is only eventual, an inner set limit providing nothing better. -/
private theorem exists_eventually_mem_proximalNormalCone_of_mem_projMapping
    {Dseq : ℕ → Set E} {D : Set E} (hDseq : ∀ n, IsClosed (Dseq n))
    (hconv : PKConverges Dseq D) {xbar vbar : E} {τ : ℝ} (hτ : 0 < τ)
    (hproj : xbar ∈ projMapping D (xbar + τ • vbar)) :
    ∃ xs vs : ℕ → E,
      (∀ᶠ n in atTop, vs n ∈ proximalNormalCone (Dseq n) (xs n)) ∧
      Tendsto xs atTop (nhds xbar) ∧ Tendsto vs atTop (nhds vbar) := by
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have hmem : ((xbar + τ • vbar, xbar) : E × E) ∈
      innerSetLimit (fun n ↦ svGraph (projMapping (Dseq n))) :=
    svGraph_projMapping_subset_innerSetLimit hDseq hconv hproj
  obtain ⟨p, hpev, hpto⟩ := mem_innerSetLimit_iff_exists_seq.1 hmem
  have hfst : Tendsto (fun n ↦ (p n).1) atTop (nhds (xbar + τ • vbar)) :=
    (continuous_fst.tendsto _).comp hpto
  have hsnd : Tendsto (fun n ↦ (p n).2) atTop (nhds xbar) :=
    (continuous_snd.tendsto _).comp hpto
  refine ⟨fun n ↦ (p n).2, fun n ↦ τ⁻¹ • ((p n).1 - (p n).2), ?_, hsnd, ?_⟩
  · filter_upwards [hpev] with n hn
    refine ⟨τ, hτ, ?_⟩
    have hcenter : (p n).2 + τ • (τ⁻¹ • ((p n).1 - (p n).2)) = (p n).1 := by
      rw [smul_smul, mul_inv_cancel₀ hτne, one_smul]
      abel
    rw [hcenter]
    exact hn
  · have hlim : τ⁻¹ • ((xbar + τ • vbar) - xbar) = vbar := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hτne, one_smul]
    rw [← hlim]
    exact (hfst.sub hsnd).const_smul τ⁻¹

/-- **Exercise 6.18(b)** for a proximal normal, which is the case the Guide
isolates.  Theorem 4.18 extracts a Painleve--Kuratowski convergent
subsequence, the extraction being arranged so that its limit `D` still
contains `x̄`; the outer-limit hypothesis gives `D ⊆ C`, so `x̄` remains a
nearest point of `D` to `x̄ + τv̄`.  The eventual membership supplied by
Example 5.35 is turned into a genuine subsequence by shifting the indices. -/
theorem exists_subsequence_mem_proximalNormalCone_tendsto_of_mem_proximalNormalCone
    {Cseq : ℕ → Set E} {C : Set E} (hCseq : ∀ n, IsClosed (Cseq n))
    (houter : outerSetLimit Cseq = C) {xbar vbar : E}
    (hvbar : vbar ∈ proximalNormalCone C xbar) :
    ∃ (φ : ℕ → ℕ) (xs vs : ℕ → E), StrictMono φ ∧
      (∀ n, xs n ∈ Cseq (φ n)) ∧
      (∀ n, vs n ∈ proximalNormalCone (Cseq (φ n)) (xs n)) ∧
      Tendsto xs atTop (nhds xbar) ∧ Tendsto vs atTop (nhds vbar) := by
  obtain ⟨τ, hτ, hproj⟩ := hvbar
  have hxbarOuter : xbar ∈ outerSetLimit Cseq := by
    rw [houter]
    exact hproj.1
  obtain ⟨ψ, y, hψ, hyC, hyx⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hxbarOuter
  obtain ⟨φ₀, D, hφ₀, hconv⟩ := exists_pkConvergent_subsequence (fun n ↦ Cseq (ψ n))
  have hconv' : PKConverges (fun n ↦ Cseq (ψ (φ₀ n))) D := hconv
  have hxbarD : xbar ∈ D := by
    rw [← hconv'.outer_eq]
    exact mem_outerSetLimit_iff_exists_subsequence.2
      ⟨id, fun n ↦ y (φ₀ n), strictMono_id, fun n ↦ hyC (φ₀ n),
        hyx.comp hφ₀.tendsto_atTop⟩
  have hDC : D ⊆ C := by
    have h₁ : outerSetLimit (fun n ↦ Cseq (ψ (φ₀ n))) ⊆
        outerSetLimit (fun n ↦ Cseq (ψ n)) :=
      outerSetLimit_subsequence_subset (C := fun n ↦ Cseq (ψ n)) hφ₀
    have h₂ : outerSetLimit (fun n ↦ Cseq (ψ n)) ⊆ outerSetLimit Cseq :=
      outerSetLimit_subsequence_subset (C := Cseq) hψ
    rw [← hconv'.outer_eq, ← houter]
    exact h₁.trans h₂
  have hprojD : xbar ∈ projMapping D (xbar + τ • vbar) :=
    ⟨hxbarD, fun w hw ↦ hproj.2 w (hDC hw)⟩
  obtain ⟨xs, vs, hev, hxto, hvto⟩ :=
    exists_eventually_mem_proximalNormalCone_of_mem_projMapping
      (Dseq := fun n ↦ Cseq (ψ (φ₀ n))) (fun n ↦ hCseq _) hconv' hτ hprojD
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hshift : Tendsto (fun n : ℕ ↦ n + N) atTop atTop := tendsto_add_atTop_nat N
  exact ⟨fun n ↦ ψ (φ₀ (n + N)), fun n ↦ xs (n + N), fun n ↦ vs (n + N),
    fun a b hab ↦ hψ (hφ₀ (Nat.add_lt_add_right hab N)),
    fun n ↦ mem_of_mem_proximalNormalCone (hN (n + N) (Nat.le_add_left N n)),
    fun n ↦ hN (n + N) (Nat.le_add_left N n), hxto.comp hshift, hvto.comp hshift⟩

/-- The graphical reading of the proximal case of 6.18(b). -/
theorem mem_graphicalOuterLimit_proximalNormalCone_of_mem_proximalNormalCone
    {Cseq : ℕ → Set E} {C : Set E} (hCseq : ∀ n, IsClosed (Cseq n))
    (houter : outerSetLimit Cseq = C) {xbar vbar : E}
    (hvbar : vbar ∈ proximalNormalCone C xbar) :
    vbar ∈ graphicalOuterLimit (fun n ↦ proximalNormalCone (Cseq n)) xbar := by
  obtain ⟨φ, xs, vs, hφ, -, hvs, hxto, hvto⟩ :=
    exists_subsequence_mem_proximalNormalCone_tendsto_of_mem_proximalNormalCone
      hCseq houter hvbar
  exact mem_graphicalOuterLimit_iff.2 ⟨φ, xs, vs, hφ, hvs, hxto, hvto⟩

/-- **Exercise 6.18(b)**, graphical form.  A general normal vector is reduced
to the proximal case by the density statement of 6.18(a) together with the
closedness of the outer limit of the graphs; this replaces the Guide's
diagonalization. -/
theorem mem_graphicalOuterLimit_proximalNormalCone_of_mem_normalCone
    {Cseq : ℕ → Set E} {C : Set E} (hC : IsClosed C)
    (hCseq : ∀ n, IsClosed (Cseq n)) (houter : outerSetLimit Cseq = C)
    {xbar vbar : E} (hvbar : vbar ∈ normalCone C xbar) :
    vbar ∈ graphicalOuterLimit (fun n ↦ proximalNormalCone (Cseq n)) xbar := by
  obtain ⟨xs, vs, -, hvs, hxto, hvto⟩ :=
    exists_seq_mem_proximalNormalCone_tendsto_of_mem_normalCone hC hvbar
  have hstep : ∀ n, ((xs n, vs n) : E × E) ∈
      outerSetLimit (fun k ↦ svGraph (proximalNormalCone (Cseq k))) := fun n ↦
    mem_graphicalOuterLimit_proximalNormalCone_of_mem_proximalNormalCone
      hCseq houter (hvs n)
  change ((xbar, vbar) : E × E) ∈
    outerSetLimit (fun k ↦ svGraph (proximalNormalCone (Cseq k)))
  exact (isClosed_outerSetLimit _).mem_of_tendsto (hxto.prodMk_nhds hvto)
    (Eventually.of_forall hstep)

/-- **Exercise 6.18(b)** as printed.  Only `limsup_ν Cν = C` is assumed of the
sequence; the sets `Cν` are closed and nonempty as in the statement, though
nonemptiness is never needed, since `x̄ ∈ C = limsup_ν Cν` already produces
points of infinitely many `Cν`.  Likewise `x̄ ∈ C` is carried by `v̄ ∈ N_C(x̄)`.

The approximating vectors are proximal normals, hence in particular normal
vectors to the corresponding `Cν`. -/
theorem exists_subsequence_mem_proximalNormalCone_tendsto_of_mem_normalCone
    {Cseq : ℕ → Set E} {C : Set E} (hC : IsClosed C)
    (hCseq : ∀ n, IsClosed (Cseq n)) (_hCseqNe : ∀ n, (Cseq n).Nonempty)
    (houter : outerSetLimit Cseq = C) {xbar vbar : E} (_hxbar : xbar ∈ C)
    (hvbar : vbar ∈ normalCone C xbar) :
    ∃ (φ : ℕ → ℕ) (xs vs : ℕ → E), StrictMono φ ∧
      (∀ n, xs n ∈ Cseq (φ n)) ∧
      (∀ n, vs n ∈ proximalNormalCone (Cseq (φ n)) (xs n)) ∧
      (∀ n, vs n ∈ normalCone (Cseq (φ n)) (xs n)) ∧
      Tendsto xs atTop (nhds xbar) ∧ Tendsto vs atTop (nhds vbar) := by
  obtain ⟨φ, xs, vs, hφ, hvs, hxto, hvto⟩ := mem_graphicalOuterLimit_iff.1
    (mem_graphicalOuterLimit_proximalNormalCone_of_mem_normalCone hC hCseq houter hvbar)
  exact ⟨φ, xs, vs, hφ, fun n ↦ mem_of_mem_proximalNormalCone (hvs n), hvs,
    fun n ↦ proximalNormalCone_subset_normalCone _ _ (hvs n), hxto, hvto⟩

/-- **Exercise 6.18(b)**, the displayed inclusion in its stronger proximal
form: `N_C ⊂ g-limsup_ν P-N_{Cν}`. -/
theorem normalCone_subset_graphicalOuterLimit_proximalNormalCone
    {Cseq : ℕ → Set E} {C : Set E} (hC : IsClosed C)
    (hCseq : ∀ n, IsClosed (Cseq n)) (houter : outerSetLimit Cseq = C) (xbar : E) :
    normalCone C xbar ⊆
      graphicalOuterLimit (fun n ↦ proximalNormalCone (Cseq n)) xbar := fun _ hv ↦
  mem_graphicalOuterLimit_proximalNormalCone_of_mem_normalCone hC hCseq houter hv

/-- **Exercise 6.18(b)**, the displayed inclusion `N_C ⊂ g-limsup_ν N_{Cν}`.
It follows from the proximal form, proximal normals being normal vectors.
The reverse inclusion is false in general: the example printed after 6.18
exhibits a strictly larger graphical outer limit. -/
theorem normalCone_subset_graphicalOuterLimit_normalCone
    {Cseq : ℕ → Set E} {C : Set E} (hC : IsClosed C)
    (hCseq : ∀ n, IsClosed (Cseq n)) (houter : outerSetLimit Cseq = C) (xbar : E) :
    normalCone C xbar ⊆ graphicalOuterLimit (fun n ↦ normalCone (Cseq n)) xbar :=
  (normalCone_subset_graphicalOuterLimit_proximalNormalCone hC hCseq houter xbar).trans
    (graphicalOuterLimit_mono
      (fun n x ↦ proximalNormalCone_subset_normalCone (Cseq n) x) xbar)

/-! #### The parenthetical clause of 6.18(b)

When `Cν → C` actually holds, no extraction is needed: the index set `N` is
`ℕ` itself.  The proof is the same one, run with `D = C` so that no
subsequence is taken, and the inner set limit replaces the outer one.
Nonemptiness of the `Cν` is genuinely used here, to fill in the finitely many
indices before the inner limit takes effect.

This is still not graphical convergence of the normal cone mappings: the
example printed after 6.18 has `Cν → C` and yet a strictly larger graphical
outer limit of the `N_{Cν}`. -/

/-- Under `Cν → C`, a proximal normal to the limit is a graphical *inner*
limit of proximal normals along the full sequence. -/
theorem mem_graphicalInnerLimit_proximalNormalCone_of_mem_proximalNormalCone
    {Cseq : ℕ → Set E} {C : Set E} (hCseq : ∀ n, IsClosed (Cseq n))
    (hconv : PKConverges Cseq C) {xbar vbar : E}
    (hvbar : vbar ∈ proximalNormalCone C xbar) :
    vbar ∈ graphicalInnerLimit (fun n ↦ proximalNormalCone (Cseq n)) xbar := by
  obtain ⟨τ, hτ, hproj⟩ := hvbar
  obtain ⟨xs, vs, hev, hxto, hvto⟩ :=
    exists_eventually_mem_proximalNormalCone_of_mem_projMapping hCseq hconv hτ hproj
  exact mem_graphicalInnerLimit_iff.2 ⟨xs, vs, hev, hxto, hvto⟩

/-- Under `Cν → C`, every normal vector to the limit is a graphical inner
limit of proximal normals along the full sequence.  As in the outer case, the
passage from proximal normals to all normal vectors is 6.18(a) together with
closedness of the limit of the graphs. -/
theorem mem_graphicalInnerLimit_proximalNormalCone_of_mem_normalCone
    {Cseq : ℕ → Set E} {C : Set E} (hCseq : ∀ n, IsClosed (Cseq n))
    (hconv : PKConverges Cseq C) {xbar vbar : E}
    (hvbar : vbar ∈ normalCone C xbar) :
    vbar ∈ graphicalInnerLimit (fun n ↦ proximalNormalCone (Cseq n)) xbar := by
  obtain ⟨xs, vs, -, hvs, hxto, hvto⟩ :=
    exists_seq_mem_proximalNormalCone_tendsto_of_mem_normalCone hconv.isClosed hvbar
  have hstep : ∀ n, ((xs n, vs n) : E × E) ∈
      innerSetLimit (fun k ↦ svGraph (proximalNormalCone (Cseq k))) := fun n ↦
    mem_graphicalInnerLimit_proximalNormalCone_of_mem_proximalNormalCone
      hCseq hconv (hvs n)
  change ((xbar, vbar) : E × E) ∈
    innerSetLimit (fun k ↦ svGraph (proximalNormalCone (Cseq k)))
  exact (isClosed_innerSetLimit _).mem_of_tendsto (hxto.prodMk_nhds hvto)
    (Eventually.of_forall hstep)

/-- The parenthetical clause of **Exercise 6.18(b)**: when `Cν → C` actually
holds, the index set of the exercise may be taken to be `ℕ` itself, so that
the approximating points and proximal normals run along the whole sequence. -/
theorem exists_seq_mem_proximalNormalCone_tendsto_of_pkConverges
    {Cseq : ℕ → Set E} {C : Set E} (hCseq : ∀ n, IsClosed (Cseq n))
    (hCseqNe : ∀ n, (Cseq n).Nonempty) (hconv : PKConverges Cseq C)
    {xbar vbar : E} (hvbar : vbar ∈ normalCone C xbar) :
    ∃ xs vs : ℕ → E, (∀ n, xs n ∈ Cseq n) ∧
      (∀ n, vs n ∈ proximalNormalCone (Cseq n) (xs n)) ∧
      (∀ n, vs n ∈ normalCone (Cseq n) (xs n)) ∧
      Tendsto xs atTop (nhds xbar) ∧ Tendsto vs atTop (nhds vbar) := by
  obtain ⟨ys, ws, hev, hyto, hwto⟩ := mem_graphicalInnerLimit_iff.1
    (mem_graphicalInnerLimit_proximalNormalCone_of_mem_normalCone hCseq hconv hvbar)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  choose z hz using hCseqNe
  have hprox : ∀ n, (if N ≤ n then ws n else 0) ∈
      proximalNormalCone (Cseq n) (if N ≤ n then ys n else z n) := by
    intro n
    by_cases hn : N ≤ n
    · simp only [if_pos hn]
      exact hN n hn
    · simp only [if_neg hn]
      exact (isCone_proximalNormalCone (hz n)).1
  have hxeq : ys =ᶠ[atTop] fun n ↦ if N ≤ n then ys n else z n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [if_pos hn]
  have hveq : ws =ᶠ[atTop] fun n ↦ if N ≤ n then ws n else (0 : E) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [if_pos hn]
  exact ⟨fun n ↦ if N ≤ n then ys n else z n, fun n ↦ if N ≤ n then ws n else 0,
    fun n ↦ mem_of_mem_proximalNormalCone (hprox n), hprox,
    fun n ↦ proximalNormalCone_subset_normalCone _ _ (hprox n),
    hyto.congr' hxeq, hwto.congr' hveq⟩

/-- Under `Cν → C`, the inclusion of 6.18(b) holds with the graphical inner
limit, which is the sharper statement, the inner limit being contained in the
outer one. -/
theorem normalCone_subset_graphicalInnerLimit_proximalNormalCone
    {Cseq : ℕ → Set E} {C : Set E} (hCseq : ∀ n, IsClosed (Cseq n))
    (hconv : PKConverges Cseq C) (xbar : E) :
    normalCone C xbar ⊆
      graphicalInnerLimit (fun n ↦ proximalNormalCone (Cseq n)) xbar := fun _ hv ↦
  mem_graphicalInnerLimit_proximalNormalCone_of_mem_normalCone hCseq hconv hv

end PartB

end NormalApproximation

end RW
