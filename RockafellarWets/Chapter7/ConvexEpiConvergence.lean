/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epigraphical limits of convex functions
-/

import RockafellarWets.Chapter7.EpiLimitCharacterization
import RockafellarWets.Chapter7.ExtendedUniformConvergence
import RockafellarWets.Chapter4.ConvexInternalApproximation
import RockafellarWets.Chapter4.ConvexLimits
import RockafellarWets.Chapter3.ConvexHullFunctionSharp
import RockafellarWets.Chapter3.Parametric
import Mathlib.Analysis.Normed.Affine.Convex

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Theorem 7.17.** The upper epi-limit of convex functions is convex. -/
theorem convex_epigraph_epiUpperLimit {f : ℕ → E → EReal}
    (hf : ∀ n, Convex ℝ (epigraph (f n))) :
    Convex ℝ (epigraph (epiUpperLimit f)) := by
  rw [epigraph_epiUpperLimit]
  exact convex_innerSetLimit _ hf

/-- An epi-limit inherits convexity from the approximating epigraphs. -/
theorem EpiConverges.convex_epigraph {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hf : ∀ n, Convex ℝ (epigraph (f n))) :
    Convex ℝ (epigraph g) := PKConverges.convex h hf

theorem convex_effectiveDomain_of_convex_epigraph {g : E → EReal}
    (hg : Convex ℝ (epigraph g)) : Convex ℝ (effectiveDomain g) := by
  have h : effectiveDomain g = Prod.fst '' epigraph g := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, -⟩ := EReal.exists_between_coe_real (show g x < ⊤ from hx)
      exact ⟨(x, t), ht.le, rfl⟩
    · rintro ⟨⟨z, t⟩, hz, rfl⟩
      exact (show g z ≤ (t : EReal) from hz).trans_lt (EReal.coe_lt_top t)
  rw [h]
  exact hg.linear_image (LinearMap.fst ℝ E ℝ)

variable [FiniteDimensional ℝ E]

/-- Above an interior point of the effective domain, a strict epigraph point
lies in the ordinary interior, including when the value is minus infinity.
The finite vertices of a surrounding simplex have a common upper bound. -/
theorem mem_interior_epigraph_of_mem_interior_effectiveDomain {g : E → EReal}
    (hg : Convex ℝ (epigraph g)) {x : E} (hx : x ∈ interior (effectiveDomain g))
    {t : ℝ} (ht : g x < (t : EReal)) : (x, t) ∈ interior (epigraph g) := by
  classical
  obtain ⟨b, hxb, hb⟩ := exists_mem_interior_convexHull_affineBasis
    (mem_interior_iff_mem_nhds.mp hx)
  have hvert : ∀ i, ∃ r : ℝ, g (b i) ≤ (r : EReal) := by
    intro i
    have hdom := hb (subset_convexHull ℝ _ (mem_range_self i))
    obtain ⟨r, hr, -⟩ := EReal.exists_between_coe_real (show g (b i) < ⊤ from hdom)
    exact ⟨r, hr.le⟩
  choose r hr using hvert
  obtain ⟨M, hM⟩ := (finite_range r).bddAbove
  have hlev : convexHull ℝ (range b) ⊆ levelSet g M := by
    apply convexHull_min _ (convex_levelSet_of_convex_epigraph hg M)
    rintro _ ⟨i, rfl⟩
    exact (hr i).trans (EReal.coe_le_coe_iff.mpr (hM (mem_range_self i)))
  let u := max M t + 1
  have hMu : M < u := by dsimp [u]; linarith [le_max_left M t]
  have htu : t < u := by dsimp [u]; linarith [le_max_right M t]
  have hu : (x, u) ∈ interior (epigraph g) := by
    apply interior_mono (s := interior (convexHull ℝ (range b)) ×ˢ Ioi M)
      (fun p hp ↦ (hlev (interior_subset hp.1)).trans (EReal.coe_le_coe_iff.mpr hp.2.le))
    rw [(isOpen_interior.prod isOpen_Ioi).interior_eq]
    exact ⟨hxb, hMu⟩
  obtain ⟨s, hs, hst⟩ := EReal.exists_between_coe_real ht
  have hst' := EReal.coe_lt_coe_iff.mp hst
  let a := (u - t) / (u - s)
  let c := (t - s) / (u - s)
  have hden : 0 < u - s := by linarith
  have ha : 0 ≤ a := div_nonneg (by linarith) hden.le
  have hc : 0 < c := div_pos (by linarith) hden
  have hac : a + c = 1 := by dsimp [a, c]; field_simp [hden.ne']; ring
  have hcomb := hg.combo_self_interior_mem_interior (show (x, s) ∈ epigraph g from hs.le)
    hu ha hc hac
  convert hcomb using 1
  ext
  · change x = a • x + c • x
    rw [← add_smul, hac, one_smul]
  · change t = a * s + c * u
    dsimp [a, c]
    field_simp [hden.ne']
    ring

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- In a closed set it suffices to test an open set above a dense set of
horizontal coordinates. -/
private theorem subset_closed_of_open_of_dense_coordinates {D : Set E} (hD : Dense D)
    {U T : Set (E × ℝ)} (hU : IsOpen U) (hT : IsClosed T)
    (h : ∀ p ∈ U, p.1 ∈ D → p ∈ T) : U ⊆ T := by
  intro p hp
  by_contra hp'
  obtain ⟨q, hqD, hq⟩ := (hD.prod (dense_univ : Dense (univ : Set ℝ))).exists_mem_open
    (hU.inter hT.isOpen_compl) ⟨p, hp, hp'⟩
  exact hq.2 (h q hq.1 hqD.1)

/-- **Theorem 7.17(b) ⇒ (a).** Dense pointwise convergence fixes both epi-limits.
Each subsequential inner limit is convex and contains the candidate epigraph.
Its interior cannot extend outside that epigraph, since compact internal
approximation would then contradict convergence at a nearby dense point. -/
theorem epiConverges_of_convex_of_tendsto_on_dense {f : ℕ → E → EReal} {g : E → EReal}
    (hf : ∀ n, Convex ℝ (epigraph (f n))) (hg : Convex ℝ (epigraph g))
    (hgc : LowerSemicontinuous g) (hdom : (interior (effectiveDomain g)).Nonempty)
    {D : Set E} (hD : Dense D) (hlim : ∀ x ∈ D, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    EpiConverges f g := by
  have hclosed := isClosed_epigraph_of_lsc_ereal g hgc
  obtain ⟨x₀, hx₀⟩ := hdom
  obtain ⟨t₀, ht₀, -⟩ := EReal.exists_between_coe_real
    (interior_subset (s := effectiveDomain g) hx₀ : g x₀ < ⊤)
  have hne : (interior (epigraph g)).Nonempty :=
    ⟨(x₀, t₀), mem_interior_epigraph_of_mem_interior_effectiveDomain hg hx₀ ht₀⟩
  have hinner : epigraph g ⊆ innerSetLimit (fun n ↦ epigraph (f n)) := by
    rw [← hclosed.closure_eq, ← hg.closure_interior_eq_closure_of_nonempty_interior hne]
    apply closure_minimal _ (isClosed_innerSetLimit _)
    apply subset_closed_of_open_of_dense_coordinates hD isOpen_interior (isClosed_innerSetLimit _)
    rintro ⟨x, t⟩ hp hx
    have ht : g x < (t : EReal) :=
      (show g x ≤ (t : EReal) from interior_subset (s := epigraph g) hp).lt_of_ne
        (fun he ↦ graphPoint_not_mem_interior_epigraph he.symm hp)
    intro V hV
    filter_upwards [(tendsto_order.mp (hlim x hx)).2 _ ht] with n hn
    exact ⟨(x, t), hn.le, mem_of_mem_nhds hV⟩
  have houter : outerSetLimit (fun n ↦ epigraph (f n)) ⊆ epigraph g := by
    intro p hp
    obtain ⟨φ, q, hφ, hq, hqp⟩ := mem_outerSetLimit_iff_exists_subsequence.mp hp
    let C := fun n ↦ epigraph (f (φ n))
    have hsub : epigraph g ⊆ innerSetLimit C := hinner.trans (innerSetLimit_subset_subsequence hφ)
    have hcv := convex_innerSetLimit C (fun n ↦ hf (φ n))
    have hsub' : innerSetLimit C ⊆ epigraph g := by
      rw [← (isClosed_innerSetLimit C).closure_eq, ← hcv.closure_interior_eq_closure_of_nonempty_interior
        (hne.mono (interior_mono hsub))]
      apply closure_minimal _ hclosed
      apply subset_closed_of_open_of_dense_coordinates hD isOpen_interior hclosed
      rintro ⟨x, t⟩ hx hxd
      have hev := eventually_compact_subset_interior_innerSetLimit C (fun n ↦ hf (φ n))
        (isCompact_singleton (x := (x, t))) (singleton_subset_iff.mpr hx)
      exact le_of_tendsto_of_tendsto ((hlim x hxd).comp hφ.tendsto_atTop)
        (tendsto_const_nhds (x := (t : EReal))) (hev.mono fun n hn ↦
          show f (φ n) x ≤ (t : EReal) from interior_subset (s := C n) (hn (mem_singleton _)))
    apply hsub'
    intro V hV
    filter_upwards [hqp.eventually_mem hV] with n hn
    exact ⟨q n, hq n, hn⟩
  have hio := innerSetLimit_subset_outerSetLimit (fun n ↦ epigraph (f n))
  exact ⟨(hio.trans houter).antisymm hinner, houter.antisymm (hinner.trans hio)⟩

/-- At a point away from the boundary of the effective domain, epi-convergence
of convex functions gives convergence along every incoming sequence. -/
theorem EpiConverges.convergesContinuouslyWithinAt_of_notMem_frontier
    {f : ℕ → E → EReal} {g : E → EReal} (h : EpiConverges f g)
    (hf : ∀ n, Convex ℝ (epigraph (f n))) {x : E} (hx : x ∉ frontier (effectiveDomain g))
    (X : Set E) : ConvergesContinuouslyWithinAt f g X x := by
  intro z _ hz
  apply tendsto_order.mpr
  constructor
  · exact (le_liminf_iff).mp ((epiConverges_iff_liminf_limsup.mp h x).1 z hz)
  · intro v hv
    obtain ⟨t, ht, htv⟩ := EReal.exists_between_coe_real hv
    have hxdom : x ∈ effectiveDomain g := ht.trans (EReal.coe_lt_top t)
    have hxint : x ∈ interior (effectiveDomain g) := by
      by_contra hn
      exact hx ⟨subset_closure hxdom, hn⟩
    have hp := mem_interior_epigraph_of_mem_interior_effectiveDomain (h.convex_epigraph hf) hxint ht
    obtain ⟨K, hKn, hK, hKi⟩ := exists_mem_nhds_isCompact_mapsTo continuous_id
      (isOpen_interior.mem_nhds hp)
    have hEv := eventually_compact_subset_interior_of_inner_eq _ hf h.1 hK hKi
    have hzn : Tendsto (fun n ↦ (z n, t)) atTop (𝓝 (x, t)) := hz.prodMk_nhds tendsto_const_nhds
    filter_upwards [hEv, hzn.eventually_mem hKn] with n hn hzn'
    exact (show f n (z n) ≤ (t : EReal) from interior_subset (s := epigraph (f n)) (hn hzn')).trans_lt htv

/-- **Theorem 7.17(a) ⇒ (c).** Compact sets may have points both inside and
outside the effective domain as long as they avoid its boundary. -/
theorem EpiConverges.erealConvergesUniformlyOn_of_disjoint_frontier
    {f : ℕ → E → EReal} {g : E → EReal} (h : EpiConverges f g)
    (hf : ∀ n, Convex ℝ (epigraph (f n))) {B : Set E}
    (hB : IsCompact B) (hd : Disjoint B (frontier (effectiveDomain g))) :
    ERealConvergesUniformlyOn f g B :=
  (convergesContinuouslyOn_iff_continuousOn_and_erealConvergesUniformlyOn.mp
    (fun _ hx ↦ h.convergesContinuouslyWithinAt_of_notMem_frontier hf
      (Set.disjoint_left.mp hd hx) B)).2 B (Subset.rfl) hB

omit [FiniteDimensional ℝ E] in
/-- **Theorem 7.17(c) ⇒ (b).** The complement of the domain frontier is
dense. Uniform convergence on its singleton subsets gives pointwise convergence. -/
theorem exists_dense_tendsto_of_uniform_away_from_frontier
    {f : ℕ → E → EReal} {g : E → EReal} (hg : Convex ℝ (epigraph g))
    (hdom : (interior (effectiveDomain g)).Nonempty)
    (h : ∀ B, IsCompact B → Disjoint B (frontier (effectiveDomain g)) →
      ERealConvergesUniformlyOn f g B) :
    ∃ D : Set E, Dense D ∧ ∀ x ∈ D, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  have hfront : frontier (effectiveDomain g) = frontier (closure (effectiveDomain g)) := by
    simp only [frontier, closure_closure,
      (convex_effectiveDomain_of_convex_epigraph hg).interior_closure_eq_interior_of_nonempty_interior hdom]
  refine ⟨(frontier (effectiveDomain g))ᶜ, ?_, ?_⟩
  · rw [hfront, ← interior_eq_empty_iff_dense_compl]
    exact interior_frontier isClosed_closure
  intro x hx
  have hsing := h {x} isCompact_singleton (Set.disjoint_singleton_left.mpr hx)
  have hp := erealConvergesUniformlyOn_iff_epiProfile.mp hsing
  apply (pkConverges_epiProfile_iff_tendsto ..).mp
  apply (pkConverges_iff_eventually_inclusions (isClosed_epiProfile g x)).mpr
  intro ε hε ρ hρ
  filter_upwards [hp ε hε ρ hρ] with n hn
  exact hn x (mem_singleton _)

/-- **Theorem 7.17.** For an lsc convex candidate whose effective domain has
nonempty interior, dense pointwise convergence is equivalent to epi-convergence. -/
theorem epiConverges_iff_tendsto_on_dense_of_convex
    {f : ℕ → E → EReal} {g : E → EReal}
    (hf : ∀ n, Convex ℝ (epigraph (f n))) (hg : Convex ℝ (epigraph g))
    (hgc : LowerSemicontinuous g) (hdom : (interior (effectiveDomain g)).Nonempty) :
    EpiConverges f g ↔ ∃ D : Set E, Dense D ∧ ∀ x ∈ D, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) :=
  ⟨fun h ↦ exists_dense_tendsto_of_uniform_away_from_frontier hg hdom
    (fun _ ↦ h.erealConvergesUniformlyOn_of_disjoint_frontier hf),
    fun ⟨_, hD, hlim⟩ ↦ epiConverges_of_convex_of_tendsto_on_dense hf hg hgc hdom hD hlim⟩

/-- The third equivalent condition in Theorem 7.17. -/
theorem epiConverges_iff_uniform_away_from_frontier_of_convex
    {f : ℕ → E → EReal} {g : E → EReal}
    (hf : ∀ n, Convex ℝ (epigraph (f n))) (hg : Convex ℝ (epigraph g))
    (hgc : LowerSemicontinuous g) (hdom : (interior (effectiveDomain g)).Nonempty) :
    EpiConverges f g ↔ ∀ B, IsCompact B → Disjoint B (frontier (effectiveDomain g)) →
      ERealConvergesUniformlyOn f g B :=
  ⟨fun h _ ↦ h.erealConvergesUniformlyOn_of_disjoint_frontier hf,
    fun h ↦ (epiConverges_iff_tendsto_on_dense_of_convex hf hg hgc hdom).mpr
      (exists_dense_tendsto_of_uniform_away_from_frontier hg hdom h)⟩

end RW
