/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Graphical convergence of monotone mappings

Theorem 12.32, Corollary 12.33 and Exercise 12.34.

The proofs follow the book.  Monotonicity passes to graphical inner limits
by taking limits in the monotonicity inequality.  For maximal monotone
mappings everything goes through the resolvents `(I + λTν)⁻¹`, which are
single-valued and Lipschitz with constant one on the whole space by 12.12.
Instead of transporting graphical convergence through the linear map
`J_λ(x, v) = (x + λv, x)` and invoking 5.40, the estimates are done directly:
a graph point `(x, v)` of the limit is approached by graph points `(xν, vν)`,
whose images `xν + λν vν` are mapped by the resolvents back to `xν`, and the
Lipschitz bound does the rest.  This handles a moving parameter `λν → λ` and
moving arguments at once, and the uniform convergence on bounded sets follows
by a compactness argument.

**Correction.**  The second sentence of Theorem 12.32 (maximality of the
limit) and Exercise 12.34(b) need the limit mapping to have nonempty domain,
equivalently the sequence must not escape to the horizon.  The constant
mappings `x ↦ {ν}` on `ℝ` are maximal monotone and converge graphically, and
pointwise with asymptotic equi-outer semicontinuity, to the mapping with empty
graph, which is monotone but not maximal monotone
(`graphicalConverges_escapingConstants`, `not_svMaximalMonotone_empty`).  The
book's proof tacitly uses a graph point of the limit when it claims that the
limit resolvent is defined everywhere; under that hypothesis the statements
are proved as printed.
-/

import RockafellarWets.Chapter12.ResolventMaximality
import RockafellarWets.Chapter5.GraphicalCompactness
import RockafellarWets.Chapter5.GraphicalPointwise
import RockafellarWets.Chapter4.SetLimitExamples

open Bornology Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section Subsequences

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

/-- Passing to a subsequence can only enlarge the graphical inner limit. -/
theorem graphicalInnerLimit_subset_comp {T : ℕ → E → Set F} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (x : E) : graphicalInnerLimit T x ⊆ graphicalInnerLimit (fun n ↦ T (φ n)) x := by
  intro v hv
  obtain ⟨y, w, hw, hy, hwv⟩ := mem_graphicalInnerLimit_iff.1 hv
  exact mem_graphicalInnerLimit_iff.2 ⟨y ∘ φ, w ∘ φ, hφ.tendsto_atTop.eventually hw,
    hy.comp hφ.tendsto_atTop, hwv.comp hφ.tendsto_atTop⟩

/-- Passing to a subsequence can only shrink the graphical outer limit. -/
theorem graphicalOuterLimit_comp_subset {T : ℕ → E → Set F} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (x : E) : graphicalOuterLimit (fun n ↦ T (φ n)) x ⊆ graphicalOuterLimit T x := by
  intro v hv
  obtain ⟨ψ, y, w, hψ, hw, hy, hwv⟩ := mem_graphicalOuterLimit_iff.1 hv
  exact mem_graphicalOuterLimit_iff.2 ⟨φ ∘ ψ, y, w, hφ.comp hψ, hw, hy, hwv⟩

/-- A graphically convergent sequence converges along every subsequence to the
same limit. -/
theorem GraphicalConverges.comp {T : ℕ → E → Set F} {T₀ : E → Set F}
    (h : GraphicalConverges T T₀) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    GraphicalConverges (fun n ↦ T (φ n)) T₀ := by
  obtain ⟨hout, hin⟩ := graphicalConverges_iff.1 h
  exact graphicalConverges_iff.2 ⟨fun x ↦ (graphicalOuterLimit_comp_subset hφ x).trans (hout x),
    fun x ↦ (hin x).trans (graphicalInnerLimit_subset_comp hφ x)⟩

/-- Maps that are Lipschitz with constant one, evaluated along two sequences
with a common limit, have the same limits. -/
theorem tendsto_of_lipschitzWith_one {f : ℕ → E → F} (hf : ∀ n, LipschitzWith 1 (f n))
    {z ζ : ℕ → E} {z₀ : E} (hz : Tendsto z atTop (𝓝 z₀)) (hζ : Tendsto ζ atTop (𝓝 z₀))
    {b : F} (hb : Tendsto (fun n ↦ f n (ζ n)) atTop (𝓝 b)) :
    Tendsto (fun n ↦ f n (z n)) atTop (𝓝 b) := by
  rw [tendsto_iff_dist_tendsto_zero] at hb ⊢
  have hzζ : Tendsto (fun n ↦ dist (z n) (ζ n)) atTop (𝓝 0) := by
    simpa using hz.dist hζ
  refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) (by simpa using hzζ.add hb)
  calc dist (f n (z n)) b ≤ dist (f n (z n)) (f n (ζ n)) + dist (f n (ζ n)) b :=
        dist_triangle _ _ _
    _ ≤ dist (z n) (ζ n) + dist (f n (ζ n)) b := by
        gcongr
        simpa using (hf n).dist_le_mul (z n) (ζ n)

/-- Convergence along every subsequence and every convergent sequence of
arguments gives uniform convergence on bounded sets of a proper space. -/
theorem tendstoUniformlyOn_of_forall_subseq [ProperSpace E] {f : ℕ → E → F} {g : E → F}
    (hg : Continuous g)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ (z : ℕ → E) (z₀ : E), Tendsto z atTop (𝓝 z₀) →
      Tendsto (fun n ↦ f (φ n) (z n)) atTop (𝓝 (g z₀)))
    {B : Set E} (hB : IsBounded B) : TendstoUniformlyOn f g atTop B := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hcon
  have hpick : ∀ n, ∃ x ∈ B, ε ≤ dist (g x) (f (φ n) x) := by
    intro n
    have := hφP n
    push_neg at this
    exact this
  choose z hzB hzε using hpick
  obtain ⟨z₀, -, ψ, hψ, hzψ⟩ := tendsto_subseq_of_bounded hB hzB
  have h1 : Tendsto (fun n ↦ f (φ (ψ n)) (z (ψ n))) atTop (𝓝 (g z₀)) :=
    h (φ ∘ ψ) (hφ.comp hψ) (z ∘ ψ) z₀ hzψ
  have h2 : Tendsto (fun n ↦ g (z (ψ n))) atTop (𝓝 (g z₀)) := (hg.tendsto z₀).comp hzψ
  have h3 : Tendsto (fun n ↦ dist (g (z (ψ n))) (f (φ (ψ n)) (z (ψ n)))) atTop (𝓝 0) := by
    simpa using h2.dist h1
  obtain ⟨n, hn⟩ := (h3.eventually_lt_const hε).exists
  exact (hzε (ψ n)).not_gt hn

end Subsequences

section Monotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Theorem 12.32**, first assertion, in the stronger form for inner limits:
the graphical inner limit of monotone mappings is monotone. -/
theorem svMonotone_graphicalInnerLimit {T : ℕ → E → Set E} (hT : ∀ n, SvMonotone (T n)) :
    SvMonotone (graphicalInnerLimit T) := by
  intro x₀ v₀ h₀ x₁ v₁ h₁
  obtain ⟨y₀, w₀, hw₀, hy₀, hv₀⟩ := mem_graphicalInnerLimit_iff.1 h₀
  obtain ⟨y₁, w₁, hw₁, hy₁, hv₁⟩ := mem_graphicalInnerLimit_iff.1 h₁
  have hlim : Tendsto (fun n ↦ ⟪w₁ n - w₀ n, y₁ n - y₀ n⟫_ℝ) atTop
      (𝓝 ⟪v₁ - v₀, x₁ - x₀⟫_ℝ) := (hv₁.sub hv₀).inner (hy₁.sub hy₀)
  refine ge_of_tendsto hlim ?_
  filter_upwards [hw₀, hw₁] with n h₀n h₁n
  exact hT n h₀n h₁n

/-- **Theorem 12.32**, first assertion: a graphical limit of monotone mappings
is monotone. -/
theorem GraphicalConverges.svMonotone {T : ℕ → E → Set E} {T₀ : E → Set E}
    (h : GraphicalConverges T T₀) (hT : ∀ n, SvMonotone (T n)) : SvMonotone T₀ :=
  (svMonotone_graphicalInnerLimit hT).mono (graphicalConverges_iff.1 h).2

end Monotone

section Resolvents

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The resolvent maps `x + λv` back to `x` when `v ∈ T(x)`. -/
theorem SvMaximalMonotone.resolventMap_add_smul {T : E → Set E} (hT : SvMaximalMonotone T)
    {lam : ℝ} (hlam : 0 < lam) {x v : E} (hv : v ∈ T x) : resolventMap T lam (x + lam • v) = x :=
  (hT.resolventMap_eq_iff hlam).2 ⟨v, hv, rfl⟩

/-- The graph point `(P z, λ⁻¹(z - P z))` given by the resolvent `P = (I + λT)⁻¹`. -/
theorem SvMaximalMonotone.inv_smul_sub_resolventMap_mem {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) (z : E) :
    lam⁻¹ • (z - resolventMap T lam z) ∈ T (resolventMap T lam z) := by
  obtain ⟨v, hv, hz⟩ := (hT.resolventMap_eq_iff (z := z) (x := resolventMap T lam z) hlam).1 rfl
  have e : lam⁻¹ • (z - resolventMap T lam z) = v := by
    rw [sub_eq_iff_eq_add'.2 hz.symm, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  rw [e]
  exact hv

/-- **Theorem 12.32**, the estimate behind the resolvent characterization: if
the graph of a maximal monotone `T₀` lies in the graphical inner limit of
maximal monotone mappings `Tν`, then `(I + λν Tν)⁻¹(zν) → (I + λT₀)⁻¹(z)`
whenever `λν → λ > 0` and `zν → z`. -/
theorem tendsto_resolventMap_of_subset_graphicalInnerLimit {T : ℕ → E → Set E}
    {T₀ : E → Set E} (hT : ∀ n, SvMaximalMonotone (T n)) (hT₀ : SvMaximalMonotone T₀)
    (hinner : ∀ x, T₀ x ⊆ graphicalInnerLimit T x) {lam : ℕ → ℝ} {lam₀ : ℝ}
    (hlam : ∀ n, 0 < lam n) (hlam₀ : 0 < lam₀) (hlim : Tendsto lam atTop (𝓝 lam₀))
    {z : ℕ → E} {z₀ : E} (hz : Tendsto z atTop (𝓝 z₀)) :
    Tendsto (fun n ↦ resolventMap (T n) (lam n) (z n)) atTop
      (𝓝 (resolventMap T₀ lam₀ z₀)) := by
  obtain ⟨v, hv, hxv⟩ :=
    (hT₀.resolventMap_eq_iff (z := z₀) (x := resolventMap T₀ lam₀ z₀) hlam₀).1 rfl
  obtain ⟨y, w, hw, hy, hwv⟩ := mem_graphicalInnerLimit_iff.1 (hinner _ hv)
  have hζ : Tendsto (fun n ↦ y n + lam n • w n) atTop (𝓝 z₀) := by
    rw [← hxv]
    exact hy.add (hlim.smul hwv)
  refine tendsto_of_lipschitzWith_one (fun n ↦ (hT n).lipschitzWith_resolventMap (hlam n))
    hz hζ (hy.congr' ?_)
  filter_upwards [hw] with n hn
  exact ((hT n).resolventMap_add_smul (hlam n) hn).symm

/-- **Theorem 12.32**, the converse direction: pointwise convergence of the
resolvents for a single `λ > 0` gives graphical convergence. -/
theorem graphicalConverges_of_tendsto_resolventMap {T : ℕ → E → Set E} {T₀ : E → Set E}
    (hT : ∀ n, SvMaximalMonotone (T n)) (hT₀ : SvMaximalMonotone T₀) {lam : ℝ}
    (hlam : 0 < lam)
    (h : ∀ z, Tendsto (fun n ↦ resolventMap (T n) lam z) atTop (𝓝 (resolventMap T₀ lam z))) :
    GraphicalConverges T T₀ := by
  refine graphicalConverges_iff.2 ⟨fun x v hv ↦ ?_, fun x v hv ↦ ?_⟩
  · obtain ⟨φ, y, w, hφ, hw, hy, hwv⟩ := mem_graphicalOuterLimit_iff.1 hv
    have hz : Tendsto (fun n ↦ y n + lam • w n) atTop (𝓝 (x + lam • v)) :=
      hy.add (hwv.const_smul lam)
    have hlim : Tendsto y atTop (𝓝 (resolventMap T₀ lam (x + lam • v))) := by
      refine (tendsto_of_lipschitzWith_one
        (fun n ↦ (hT (φ n)).lipschitzWith_resolventMap hlam) hz tendsto_const_nhds
        ((h (x + lam • v)).comp hφ.tendsto_atTop)).congr fun n ↦ ?_
      exact (hT (φ n)).resolventMap_add_smul hlam (hw n)
    have hx : resolventMap T₀ lam (x + lam • v) = x := tendsto_nhds_unique hlim hy
    obtain ⟨v', hv', hxv'⟩ := (hT₀.resolventMap_eq_iff hlam).1 hx
    have hvv : v' = v := smul_right_injective E hlam.ne' (add_left_cancel hxv')
    rw [← hvv]
    exact hv'
  · have hPx : resolventMap T₀ lam (x + lam • v) = x := hT₀.resolventMap_add_smul hlam hv
    have h1 := h (x + lam • v)
    rw [hPx] at h1
    refine mem_graphicalInnerLimit_iff.2 ⟨fun n ↦ resolventMap (T n) lam (x + lam • v),
      fun n ↦ lam⁻¹ • (x + lam • v - resolventMap (T n) lam (x + lam • v)),
      Eventually.of_forall fun n ↦ (hT n).inv_smul_sub_resolventMap_mem hlam _, h1, ?_⟩
    have e : lam⁻¹ • (x + lam • v - x) = v := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    simpa only [e] using ((tendsto_const_nhds (x := x + lam • v)).sub h1).const_smul lam⁻¹

/-- **Theorem 12.32**, maximality of the limit.  A graphical limit of maximal
monotone mappings with nonempty domain is maximal monotone.  The hypothesis
on the domain is needed, see `graphicalConverges_escapingConstants`. -/
theorem GraphicalConverges.svMaximalMonotone {T : ℕ → E → Set E} {T₀ : E → Set E}
    (h : GraphicalConverges T T₀) (hT : ∀ n, SvMaximalMonotone (T n))
    (hne : (svDom T₀).Nonempty) : SvMaximalMonotone T₀ := by
  have hmono : SvMonotone T₀ := h.svMonotone fun n ↦ (hT n).1
  refine svMaximalMonotone_of_svDom_svResolvent hmono one_pos (eq_univ_of_forall fun z ↦ ?_)
  obtain ⟨x₀, v₀, hv₀⟩ := hne
  obtain ⟨y, w, hw, hy, hwv⟩ :=
    mem_graphicalInnerLimit_iff.1 ((graphicalConverges_iff.1 h).2 x₀ hv₀)
  set P : ℕ → E := fun n ↦ resolventMap (T n) 1 z with hPdef
  have ha : Tendsto (fun n ↦ ‖z - (y n + w n)‖ + ‖y n - x₀‖) atTop
      (𝓝 (‖z - (x₀ + v₀)‖ + ‖x₀ - x₀‖)) :=
    ((tendsto_const_nhds.sub (hy.add hwv)).norm).add ((hy.sub tendsto_const_nhds).norm)
  set L := ‖z - (x₀ + v₀)‖ + ‖x₀ - x₀‖
  have hbd : ∀ᶠ n in atTop, P n ∈ closedBall x₀ (L + 1) := by
    filter_upwards [hw, ha.eventually_lt_const (lt_add_one L)] with n hn hlt
    rw [mem_closedBall, dist_eq_norm]
    have hres : resolventMap (T n) 1 (y n + (1 : ℝ) • w n) = y n :=
      (hT n).resolventMap_add_smul one_pos hn
    rw [one_smul] at hres
    have hlip := ((hT n).lipschitzWith_resolventMap one_pos).norm_sub_le z (y n + w n)
    rw [hres, NNReal.coe_one, one_mul] at hlip
    calc ‖P n - x₀‖ = ‖(P n - y n) + (y n - x₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖P n - y n‖ + ‖y n - x₀‖ := norm_add_le _ _
      _ ≤ ‖z - (y n + w n)‖ + ‖y n - x₀‖ := by gcongr
      _ ≤ L + 1 := hlt.le
  obtain ⟨a, -, φ, hφ, hPφ⟩ :=
    tendsto_subseq_of_frequently_bounded isBounded_closedBall hbd.frequently
  have hmem : z - a ∈ T₀ a := by
    refine (graphicalConverges_iff.1 h).1 a (mem_graphicalOuterLimit_iff.2
      ⟨φ, P ∘ φ, fun n ↦ z - P (φ n), hφ, fun n ↦ ?_, hPφ, tendsto_const_nhds.sub hPφ⟩)
    have := (hT (φ n)).inv_smul_sub_resolventMap_mem one_pos z
    rwa [inv_one, one_smul] at this
  exact ⟨a, mem_svResolvent.2 ⟨z - a, hmem, by rw [one_smul, add_sub_cancel]⟩⟩

/-- **Theorem 12.32**, the resolvent characterization: for maximal monotone `Tν`
and `T` and any `λ > 0`, `Tν →g T` exactly when `(I + λTν)⁻¹ → (I + λT)⁻¹`
pointwise, here for the single-valued resolvents. -/
theorem graphicalConverges_iff_tendsto_resolventMap {T : ℕ → E → Set E} {T₀ : E → Set E}
    (hT : ∀ n, SvMaximalMonotone (T n)) (hT₀ : SvMaximalMonotone T₀) {lam : ℝ}
    (hlam : 0 < lam) :
    GraphicalConverges T T₀ ↔
      ∀ z, Tendsto (fun n ↦ resolventMap (T n) lam z) atTop (𝓝 (resolventMap T₀ lam z)) :=
  ⟨fun h _ ↦ tendsto_resolventMap_of_subset_graphicalInnerLimit hT hT₀
      (graphicalConverges_iff.1 h).2 (fun _ ↦ hlam) hlam tendsto_const_nhds tendsto_const_nhds,
    graphicalConverges_of_tendsto_resolventMap hT hT₀ hlam⟩

/-- **Theorem 12.32**, the resolvent characterization in the printed set-valued
form: `Tν →g T ⇔ (I + λTν)⁻¹ →p (I + λT)⁻¹`. -/
theorem graphicalConverges_iff_pointwiseConverges_svResolvent {T : ℕ → E → Set E}
    {T₀ : E → Set E} (hT : ∀ n, SvMaximalMonotone (T n)) (hT₀ : SvMaximalMonotone T₀)
    {lam : ℝ} (hlam : 0 < lam) :
    GraphicalConverges T T₀ ↔
      PointwiseConverges (fun n ↦ svResolvent (T n) lam) (svResolvent T₀ lam) := by
  have e : ∀ n z, svResolvent (T n) lam z = {resolventMap (T n) lam z} :=
    fun n z ↦ (hT n).svResolvent_eq_singleton_resolventMap hlam z
  have e₀ : ∀ z, svResolvent T₀ lam z = {resolventMap T₀ lam z} :=
    hT₀.svResolvent_eq_singleton_resolventMap hlam
  rw [graphicalConverges_iff_tendsto_resolventMap hT hT₀ hlam, PointwiseConverges]
  simp only [e, e₀]
  exact forall_congr' fun z ↦ pkConverges_singleton_iff.symm

/-- **Theorem 12.32**, uniform convergence: if `Tν →g T` for maximal monotone
mappings and `λν → λ` with `λ, λν > 0`, then `(I + λν Tν)⁻¹ → (I + λT)⁻¹`
uniformly on every bounded set. -/
theorem GraphicalConverges.tendstoUniformlyOn_resolventMap {T : ℕ → E → Set E}
    {T₀ : E → Set E} (h : GraphicalConverges T T₀) (hT : ∀ n, SvMaximalMonotone (T n))
    (hT₀ : SvMaximalMonotone T₀) {lam : ℕ → ℝ} {lam₀ : ℝ} (hlam : ∀ n, 0 < lam n)
    (hlam₀ : 0 < lam₀) (hlim : Tendsto lam atTop (𝓝 lam₀)) {B : Set E} (hB : IsBounded B) :
    TendstoUniformlyOn (fun n ↦ resolventMap (T n) (lam n)) (resolventMap T₀ lam₀) atTop B :=
  tendstoUniformlyOn_of_forall_subseq (hT₀.lipschitzWith_resolventMap hlam₀).continuous
    (fun φ hφ _ _ hz ↦ tendsto_resolventMap_of_subset_graphicalInnerLimit (fun n ↦ hT (φ n))
      hT₀ (graphicalConverges_iff.1 (h.comp hφ)).2 (fun n ↦ hlam (φ n)) hlam₀
      (hlim.comp hφ.tendsto_atTop) hz) hB

/-- **Theorem 12.32**, collected.  A graphical limit of monotone mappings is
monotone; a graphical limit of maximal monotone mappings with nonempty domain
is maximal monotone; for maximal monotone `Tν` and `T`, graphical convergence
is pointwise convergence of the resolvents `(I + λTν)⁻¹` for any `λ > 0`, and
then the resolvents converge uniformly on bounded sets along any `λν → λ`. -/
theorem graphical_convergence_of_monotone_mappings {T : ℕ → E → Set E} {T₀ : E → Set E} :
    ((∀ n, SvMonotone (T n)) → GraphicalConverges T T₀ → SvMonotone T₀) ∧
    ((∀ n, SvMaximalMonotone (T n)) → GraphicalConverges T T₀ → (svDom T₀).Nonempty →
      SvMaximalMonotone T₀) ∧
    ((∀ n, SvMaximalMonotone (T n)) → SvMaximalMonotone T₀ → ∀ lam : ℝ, 0 < lam →
      (GraphicalConverges T T₀ ↔
        PointwiseConverges (fun n ↦ svResolvent (T n) lam) (svResolvent T₀ lam))) ∧
    ((∀ n, SvMaximalMonotone (T n)) → SvMaximalMonotone T₀ → GraphicalConverges T T₀ →
      ∀ (lam : ℕ → ℝ) (lam₀ : ℝ), (∀ n, 0 < lam n) → 0 < lam₀ →
        Tendsto lam atTop (𝓝 lam₀) → ∀ B : Set E, IsBounded B →
          TendstoUniformlyOn (fun n ↦ resolventMap (T n) (lam n)) (resolventMap T₀ lam₀)
            atTop B) :=
  ⟨fun hT h ↦ h.svMonotone hT, fun hT h hne ↦ h.svMaximalMonotone hT hne,
    fun hT hT₀ _ hlam ↦ graphicalConverges_iff_pointwiseConverges_svResolvent hT hT₀ hlam,
    fun hT hT₀ h _ _ hlam hlam₀ hlim _ hB ↦
      h.tendstoUniformlyOn_resolventMap hT hT₀ hlam hlam₀ hlim hB⟩

/-- **Corollary 12.33 (convergent subsequences).**  A sequence of maximal
monotone mappings that does not escape to the horizon has a subsequence
converging graphically to a maximal monotone mapping. -/
theorem exists_graphicalConverges_svMaximalMonotone {T : ℕ → E → Set E}
    (hT : ∀ n, SvMaximalMonotone (T n)) (hesc : ¬ SvEscapesToHorizon T) :
    ∃ (φ : ℕ → ℕ) (T₀ : E → Set E), StrictMono φ ∧ SvMaximalMonotone T₀ ∧
      GraphicalConverges (fun n ↦ T (φ n)) T₀ := by
  rcases svEscapesToHorizon_or_exists_graphicalConverges_subsequence T with
    h | ⟨φ, S, hφ, hS, hconv⟩
  · exact absurd h hesc
  · exact ⟨φ, S, hφ, hconv.svMaximalMonotone (fun n ↦ hT (φ n)) hS, hconv⟩

/-- **Exercise 12.34(a).**  If `g-lim inf Tν ⊃ T` with `Tν` monotone and `T`
maximal monotone, then `Tν →g T`. -/
theorem graphicalConverges_of_subset_graphicalInnerLimit {T : ℕ → E → Set E}
    {T₀ : E → Set E} (hT : ∀ n, SvMonotone (T n)) (hT₀ : SvMaximalMonotone T₀)
    (h : ∀ x, T₀ x ⊆ graphicalInnerLimit T x) : GraphicalConverges T T₀ := by
  refine graphicalConverges_iff.2 ⟨fun x v hv ↦ ?_, h⟩
  obtain ⟨φ, y, w, hφ, hw, hy, hwv⟩ := mem_graphicalOuterLimit_iff.1 hv
  obtain ⟨ψ, S, hψ, hS⟩ := exists_graphicalConverges_subsequence (fun n ↦ T (φ n))
  have hSmono : SvMonotone S := hS.svMonotone fun n ↦ hT (φ (ψ n))
  have hsub : ∀ x, T₀ x ⊆ S x := fun x ↦
    ((h x).trans (graphicalInnerLimit_subset_comp (hφ.comp hψ) x)).trans
      ((graphicalInnerLimit_subset _ x).trans ((graphicalConverges_iff.1 hS).1 x))
  have hST : S = T₀ := hT₀.eq_of_subset hSmono hsub
  have hmem : v ∈ graphicalOuterLimit (fun n ↦ T (φ (ψ n))) x :=
    mem_graphicalOuterLimit_iff.2 ⟨id, y ∘ ψ, w ∘ ψ, strictMono_id, fun n ↦ hw (ψ n),
      hy.comp hψ.tendsto_atTop, hwv.comp hψ.tendsto_atTop⟩
  rw [← hST]
  exact (graphicalConverges_iff.1 hS).1 x hmem

/-- **Exercise 12.34(b).**  If `Tν →p T` with `Tν` maximal monotone and the
sequence asymptotically equi-osc everywhere, then `T` is maximal monotone,
provided its domain is nonempty (see `pointwiseConverges_escapingConstants`). -/
theorem svMaximalMonotone_of_pointwiseConverges {T : ℕ → E → Set E} {T₀ : E → Set E}
    (hT : ∀ n, SvMaximalMonotone (T n)) (hosc : ∀ x, SvAsymptoticallyEquiOscAt T x)
    (h : PointwiseConverges T T₀) (hne : (svDom T₀).Nonempty) : SvMaximalMonotone T₀ :=
  ((graphicalConverges_iff_pointwiseConverges hosc).2 h).svMaximalMonotone hT hne

end Resolvents

section Counterexample

/-- The empty mapping is monotone but not maximal monotone. -/
theorem not_svMaximalMonotone_empty {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ¬ SvMaximalMonotone (fun _ : E ↦ (∅ : Set E)) := by
  rintro ⟨-, h⟩
  obtain ⟨_, _, hv, -⟩ := h 0 0 (notMem_empty _)
  exact notMem_empty _ hv

/-- The constant mappings `x ↦ {ν}` on `ℝ`, which escape to the horizon. -/
def escapingConstants (n : ℕ) : ℝ → Set ℝ := fun _ ↦ {(n : ℝ)}

/-- Each constant mapping `x ↦ {ν}` is maximal monotone. -/
theorem svMaximalMonotone_escapingConstants (n : ℕ) :
    SvMaximalMonotone (escapingConstants n) :=
  svMaximalMonotone_singleton_of_continuous (F := fun _ : ℝ ↦ (n : ℝ)) continuous_const
    (svMonotone_singleton_iff.2 fun _ _ ↦ by simp)

/-- The values `{ν}` eventually avoid every bounded set. -/
theorem eventually_escapingConstants_inter_closedBall_eq_empty (ρ : ℝ) :
    ∀ᶠ n in atTop, ∀ x, escapingConstants n x ∩ closedBall 0 ρ = ∅ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ρ
  filter_upwards [eventually_ge_atTop N] with n hn x
  refine eq_empty_of_forall_notMem fun u ⟨hu, hρ⟩ ↦ ?_
  rw [escapingConstants, mem_singleton_iff] at hu
  rw [mem_closedBall_zero_iff, hu, Real.norm_natCast] at hρ
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- **Correction to 12.32**: the maximal monotone mappings `x ↦ {ν}` converge
graphically to the empty mapping, which is not maximal monotone. -/
theorem graphicalConverges_escapingConstants :
    GraphicalConverges escapingConstants (fun _ ↦ ∅) := by
  refine graphicalConverges_iff.2 ⟨fun x v hv ↦ ?_, fun _ _ hv ↦ (notMem_empty _ hv).elim⟩
  obtain ⟨φ, y, w, hφ, hw, -, hwv⟩ := mem_graphicalOuterLimit_iff.1 hv
  obtain ⟨n, hn⟩ := ((hφ.tendsto_atTop.eventually
    (eventually_escapingConstants_inter_closedBall_eq_empty (‖v‖ + 1))).and
      (hwv.eventually (closedBall_mem_nhds v one_pos))).exists
  refine (Set.eq_empty_iff_forall_notMem.1 (hn.1 (y n)) (w n) ⟨hw n, ?_⟩).elim
  rw [mem_closedBall_zero_iff]
  have h1 := hn.2
  rw [dist_eq_norm] at h1
  calc ‖w n‖ = ‖(w n - v) + v‖ := by rw [sub_add_cancel]
    _ ≤ ‖w n - v‖ + ‖v‖ := norm_add_le _ _
    _ ≤ ‖v‖ + 1 := by linarith

/-- **Correction to 12.34(b)**: the mappings `x ↦ {ν}` are asymptotically
equi-osc everywhere and converge pointwise to the empty mapping. -/
theorem pointwiseConverges_escapingConstants :
    (∀ x, SvAsymptoticallyEquiOscAt escapingConstants x) ∧
      PointwiseConverges escapingConstants (fun _ ↦ ∅) := by
  refine ⟨fun x ε _ ρ _ ↦ ⟨univ, univ_mem, ?_⟩, ?_⟩
  · filter_upwards [eventually_escapingConstants_inter_closedBall_eq_empty ρ] with n hn y _
    rw [hn y]
    exact empty_subset _
  · have hg := graphicalConverges_escapingConstants
    refine pointwiseConverges_iff.2 ⟨fun x v hv ↦ ?_, fun _ _ hv ↦ (notMem_empty _ hv).elim⟩
    exact (graphicalConverges_iff.1 hg).1 x (pointwiseOuterLimit_subset_graphicalOuterLimit _ x hv)

end Counterexample

end RW
