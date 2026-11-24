/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Yosida regularization

Example 12.13.  For any mapping `T` and `λ > 0`, the Yosida
`λ`-regularization is `(λI + T⁻¹)⁻¹ = (I + λ⁻¹T⁻¹)⁻¹ ∘ λ⁻¹I`; this identity is
`svYosida_eq_svComp` in `Resolvents`.  As `λ ↘ 0` it converges graphically to
`cl T`, the mapping whose graph is `cl(gph T)`, hence to `T` when `T` is
outer semicontinuous, for instance maximal monotone.  For maximal monotone `T`
it is maximal monotone, single-valued and globally Lipschitz with constant
`λ⁻¹`.

The graph of `(λI + T⁻¹)⁻¹` is the image of `gph T` under
`(x, v) ↦ (x + λv, v)`, which tends to the identity uniformly on bounded sets.
Graphical convergence is proved along the filter `λ ↘ 0` (`𝓝[>] 0`) and along
every sequence of positive parameters tending to `0`.

The text after Theorem 12.15 is also recorded for maximal monotone `T`:
`(Pλ(z), Qλ(z)) = (x, v) ⟺ z = x + λv, (x, v) ∈ gph T` for the resolvent
`Pλ = (I + λT)⁻¹` and `Qλ = (λI + T⁻¹)⁻¹`.
-/

import RockafellarWets.Chapter12.ResolventMaximality
import RockafellarWets.Chapter5.GraphicalLimits
import RockafellarWets.Chapter5.HorizonSetLimitsAlong

open Set Filter Topology Metric
open scoped InnerProductSpace Pointwise NNReal

namespace RW

section Yosida

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The closure `cl T` of a mapping, whose graph is `cl(gph T)`. -/
def svClosure (T : E → Set E) : E → Set E :=
  fun x ↦ {v | (x, v) ∈ closure (svGraph T)}

omit [InnerProductSpace ℝ E] in
theorem svGraph_svClosure (T : E → Set E) : svGraph (svClosure T) = closure (svGraph T) := by
  ext ⟨x, v⟩
  rfl

omit [InnerProductSpace ℝ E] in
theorem svClosure_eq_of_svOsc {T : E → Set E} (hT : SvOsc T) : svClosure T = T := by
  funext x
  ext v
  simp only [svClosure, (isClosed_svGraph_iff_svOsc.2 hT).closure_eq, mem_setOf_eq, mem_svGraph]

/-- The graph of the Yosida regularization is the image of `gph T` under
`(x, v) ↦ (x + λv, v)`. -/
theorem svGraph_svYosida (T : E → Set E) (lam : ℝ) :
    svGraph (svYosida T lam) = (fun p : E × E ↦ (p.1 + lam • p.2, p.2)) '' svGraph T := by
  ext ⟨z, v⟩
  simp only [mem_svGraph, mem_svYosida, mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, v, hx, add_comm _ _, rfl⟩
  · rintro ⟨x, v', hx, rfl, rfl⟩
    exact ⟨x, hx, add_comm _ _⟩

private theorem closure_subset_innerSetLimitAlong_yosida (T : E → Set E) :
    closure (svGraph T) ⊆
      innerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun lam ↦ svGraph (svYosida T lam)) := by
  intro q hq V hV
  rcases _root_.mem_nhds_iff.1 hV with ⟨U, hUV, hUopen, hqU⟩
  rcases mem_closure_iff.1 hq U hUopen hqU with ⟨p, hpU, hpT⟩
  have hcont : Continuous fun lam : ℝ ↦ (p.1 + lam • p.2, p.2) := by fun_prop
  have hev : ∀ᶠ lam in 𝓝 (0 : ℝ), (p.1 + lam • p.2, p.2) ∈ U :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hUopen.mem_nhds hpU)
  filter_upwards [nhdsWithin_le_nhds hev] with lam hlam
  refine ⟨(p.1 + lam • p.2, p.2), ?_, hUV hlam⟩
  rw [svGraph_svYosida]
  exact ⟨p, hpT, rfl⟩

private theorem outerSetLimitAlong_yosida_subset_closure (T : E → Set E) :
    outerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun lam ↦ svGraph (svYosida T lam)) ⊆
      closure (svGraph T) := by
  intro q hq
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ := ε / 2 with hδ
  have hδpos : 0 < δ := half_pos hε
  set η := δ / (‖q.2‖ + δ + 1) with hη
  have hηpos : 0 < η := div_pos hδpos (by positivity)
  have hηb : η * (‖q.2‖ + δ) < δ := by
    rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg q.2]
  have hfreq := hq (ball q δ) (ball_mem_nhds q hδpos)
  have hev : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ Ioo 0 η := Ioo_mem_nhdsGT hηpos
  obtain ⟨lam, ⟨r, hrY, hrV⟩, hlam0, hlamη⟩ := (hfreq.and_eventually hev).exists
  have hrY' : r ∈ svGraph (svYosida T lam) := hrY
  rw [svGraph_svYosida] at hrY'
  obtain ⟨p, hpT, rfl⟩ := hrY'
  refine ⟨p, hpT, ?_⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff] at hrV
  obtain ⟨h₁, h₂⟩ := hrV
  simp only at h₁ h₂
  have hnorm : ‖p.2‖ < ‖q.2‖ + δ := by
    have := norm_le_norm_add_norm_sub' p.2 q.2
    rw [dist_eq_norm] at h₂
    linarith
  have hshift : dist (p.1 + lam • p.2) p.1 ≤ η * (‖q.2‖ + δ) := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
    exact mul_le_mul hlamη.le hnorm.le (norm_nonneg _) hηpos.le
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · calc dist q.1 p.1 ≤ dist q.1 (p.1 + lam • p.2) + dist (p.1 + lam • p.2) p.1 :=
          dist_triangle _ _ _
      _ < δ + δ := by rw [dist_comm] at h₁; linarith
      _ = ε := by rw [hδ]; ring
  · rw [dist_comm]
    linarith

/-- **Example 12.13.** As `λ ↘ 0`, the Yosida regularizations converge
graphically to `cl T`: the graphs converge to `cl(gph T)` along `𝓝[>] 0`. -/
theorem pkConvergesAlong_svYosida (T : E → Set E) :
    PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun lam ↦ svGraph (svYosida T lam)) (closure (svGraph T)) := by
  have h₁ := closure_subset_innerSetLimitAlong_yosida T
  have h₂ := outerSetLimitAlong_yosida_subset_closure T
  have h₃ := innerSetLimitAlong_subset_outerSetLimitAlong (l := 𝓝[>] (0 : ℝ))
    (fun lam ↦ svGraph (svYosida T lam))
  exact ⟨Subset.antisymm (h₃.trans h₂) h₁, Subset.antisymm h₂ (h₁.trans h₃)⟩

/-- **Example 12.13**, along sequences: for positive `λν → 0`, the Yosida
regularizations converge graphically to `cl T`. -/
theorem graphicalConverges_svYosida (T : E → Set E) {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n)
    (hlim : Tendsto lam atTop (𝓝 0)) :
    GraphicalConverges (fun n ↦ svYosida T (lam n)) (svClosure T) := by
  have ht : Tendsto lam atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hpos⟩
  have h := pkConvergesAlong_svYosida T
  have hin : closure (svGraph T) ⊆ innerSetLimit (fun n ↦ svGraph (svYosida T (lam n))) := by
    intro q hq V hV
    have hq' : q ∈ innerSetLimitAlong (𝓝[>] (0 : ℝ)) (fun lam ↦ svGraph (svYosida T lam)) := by
      rw [h.inner_eq]
      exact hq
    exact ht.eventually (hq' V hV)
  have hout : outerSetLimit (fun n ↦ svGraph (svYosida T (lam n))) ⊆ closure (svGraph T) := by
    intro q hq
    rw [← h.outer_eq]
    intro V hV
    exact ht.frequently (hq V hV)
  have hio := innerSetLimit_subset_outerSetLimit (fun n ↦ svGraph (svYosida T (lam n)))
  unfold GraphicalConverges PKConverges
  rw [svGraph_svClosure]
  exact ⟨Subset.antisymm (hio.trans hout) hin, Subset.antisymm hout (hin.trans hio)⟩

/-- **Example 12.13.** For outer semicontinuous `T`, the Yosida
regularizations converge graphically to `T` as `λ ↘ 0`. -/
theorem pkConvergesAlong_svYosida_of_svOsc {T : E → Set E} (hT : SvOsc T) :
    PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun lam ↦ svGraph (svYosida T lam)) (svGraph T) := by
  have h := pkConvergesAlong_svYosida T
  rwa [(isClosed_svGraph_iff_svOsc.2 hT).closure_eq] at h

/-- **Example 12.13**, along sequences, for outer semicontinuous `T`. -/
theorem graphicalConverges_svYosida_of_svOsc {T : E → Set E} (hT : SvOsc T) {lam : ℕ → ℝ}
    (hpos : ∀ n, 0 < lam n) (hlim : Tendsto lam atTop (𝓝 0)) :
    GraphicalConverges (fun n ↦ svYosida T (lam n)) T := by
  have h := graphicalConverges_svYosida T hpos hlim
  rwa [svClosure_eq_of_svOsc hT] at h

/-- **Example 12.13**, for maximal monotone `T`, along `𝓝[>] 0`. -/
theorem SvMaximalMonotone.pkConvergesAlong_svYosida {T : E → Set E} (hT : SvMaximalMonotone T) :
    PKConvergesAlong (𝓝[>] (0 : ℝ)) (fun lam ↦ svGraph (svYosida T lam)) (svGraph T) :=
  pkConvergesAlong_svYosida_of_svOsc hT.svOsc

/-- **Example 12.13**, for maximal monotone `T`, along sequences. -/
theorem SvMaximalMonotone.graphicalConverges_svYosida {T : E → Set E} (hT : SvMaximalMonotone T)
    {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n) (hlim : Tendsto lam atTop (𝓝 0)) :
    GraphicalConverges (fun n ↦ svYosida T (lam n)) T :=
  graphicalConverges_svYosida_of_svOsc hT.svOsc hpos hlim

/-- The single-valued Yosida regularization `z ↦ (I + λ⁻¹T⁻¹)⁻¹(λ⁻¹z)`. -/
noncomputable def yosidaMap (T : E → Set E) (lam : ℝ) (z : E) : E :=
  resolventMap (svInv T) lam⁻¹ (lam⁻¹ • z)

/-- The Yosida regularization of a monotone mapping is monotone, as the
inverse of the monotone mapping `λI + T⁻¹`. -/
theorem SvMonotone.svMonotone_svYosida {T : E → Set E} (hT : SvMonotone T) {lam : ℝ}
    (hlam : 0 ≤ lam) : SvMonotone (svYosida T lam) := by
  have hI : SvMonotone (fun v : E ↦ ({lam • v} : Set E)) := by
    refine svMonotone_singleton_iff.2 fun v₀ v₁ ↦ ?_
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg hlam real_inner_self_nonneg
  exact (hI.add hT.inv).inv

variable [FiniteDimensional ℝ E]

/-- **Example 12.13.** For maximal monotone `T` and `λ > 0`, the Yosida
regularization is single-valued. -/
theorem SvMaximalMonotone.svYosida_eq_fun {T : E → Set E} (hT : SvMaximalMonotone T) {lam : ℝ}
    (hlam : 0 < lam) : svYosida T lam = fun z ↦ ({yosidaMap T lam z} : Set E) := by
  rw [svYosida_eq_svComp T hlam.ne', hT.inv.svResolvent_eq_fun (inv_pos.2 hlam)]
  funext z
  ext v
  simp only [mem_svComp, mem_singleton_iff, exists_eq_left, yosidaMap]

/-- **Lemma 12.14** for the single-valued maps: `Qλ = λ⁻¹(I - Pλ)`. -/
theorem SvMaximalMonotone.yosidaMap_eq {T : E → Set E} (hT : SvMaximalMonotone T) {lam : ℝ}
    (hlam : 0 < lam) (z : E) : yosidaMap T lam z = lam⁻¹ • (z - resolventMap T lam z) := by
  have h := congrFun (svYosida_eq_smul_sub_svResolvent T hlam.ne') z
  rw [hT.svYosida_eq_fun hlam, hT.svResolvent_eq_singleton_resolventMap hlam z,
    singleton_sub_singleton, smul_set_singleton] at h
  exact singleton_eq_singleton_iff.1 h

/-- **Example 12.13.** For maximal monotone `T` and `λ > 0`, the Yosida
regularization is globally Lipschitz with constant `λ⁻¹`. -/
theorem SvMaximalMonotone.lipschitzWith_yosidaMap {T : E → Set E} (hT : SvMaximalMonotone T)
    {lam : ℝ} (hlam : 0 < lam) : LipschitzWith (Real.toNNReal lam⁻¹) (yosidaMap T lam) := by
  have h₁ := hT.inv.lipschitzWith_resolventMap (inv_pos.2 hlam)
  have h₂ : LipschitzWith (Real.toNNReal lam⁻¹) (fun z : E ↦ lam⁻¹ • z) := by
    have := lipschitzWith_smul (β := E) lam⁻¹
    have he : ‖lam⁻¹‖₊ = Real.toNNReal lam⁻¹ := by
      ext
      simp [hlam.le, abs_of_pos hlam]
    rwa [he] at this
  have := h₁.comp h₂
  rwa [one_mul] at this

/-- **Example 12.13.** For maximal monotone `T` and `λ > 0`, the Yosida
regularization is maximal monotone. -/
theorem SvMaximalMonotone.svMaximalMonotone_svYosida {T : E → Set E} (hT : SvMaximalMonotone T)
    {lam : ℝ} (hlam : 0 < lam) : SvMaximalMonotone (svYosida T lam) := by
  have hmono := hT.1.svMonotone_svYosida hlam.le
  rw [hT.svYosida_eq_fun hlam] at hmono ⊢
  exact svMaximalMonotone_singleton_of_continuous (hT.lipschitzWith_yosidaMap hlam).continuous hmono

/-- The `λ`-form of the Minty parameterization after Theorem 12.15:
`(Pλ(z), Qλ(z)) = (x, v) ⟺ z = x + λv, (x, v) ∈ gph T`. -/
theorem SvMaximalMonotone.resolventMap_yosidaMap_eq_iff {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) {z x v : E} :
    (resolventMap T lam z = x ∧ yosidaMap T lam z = v) ↔ z = x + lam • v ∧ v ∈ T x := by
  have hQ : ∀ w, yosidaMap T lam z = w ↔ ∃ y, w ∈ T y ∧ lam • w + y = z := by
    intro w
    rw [← mem_svYosida, hT.svYosida_eq_fun hlam, mem_singleton_iff, eq_comm]
  rw [hT.resolventMap_eq_iff hlam, hQ]
  constructor
  · rintro ⟨⟨v', hv', hz'⟩, ⟨y, hy, hz⟩⟩
    have hP : resolventMap T lam z = y := (hT.resolventMap_eq_iff hlam).2 ⟨v, hy, by
      rw [← hz, add_comm]⟩
    have hP' : resolventMap T lam z = x := (hT.resolventMap_eq_iff hlam).2 ⟨v', hv', hz'⟩
    have hxy : y = x := hP.symm.trans hP'
    subst hxy
    exact ⟨by rw [← hz, add_comm], hy⟩
  · rintro ⟨rfl, hv⟩
    exact ⟨⟨v, hv, rfl⟩, ⟨x, hv, add_comm _ _⟩⟩

end Yosida

end RW
