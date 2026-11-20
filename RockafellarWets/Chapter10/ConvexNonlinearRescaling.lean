/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exact convex nonlinear rescaling

The ordinary formula in 10.19(b) needs a zero-outer-multiplier condition
on its horizon branch. The corrected formula is exact.
-/

import RockafellarWets.Chapter10.MonotoneNonlinearRescaling

open Set
open scoped Pointwise InnerProductSpace

namespace RW
noncomputable section

set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem convex_epigraph_heightFunction {θ : ℝ → EReal} (hθ : Convex ℝ (epigraph θ)) :
    Convex ℝ (epigraph (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst)) := by
  intro p hp q hq t s ht hs hts
  exact hθ (show (p.1.fst,p.2) ∈ epigraph θ from hp)
    (show (q.1.fst,q.2) ∈ epigraph θ from hq) ht hs hts

theorem convex_epigraph_rescalingHeightIntegrand {f : E → EReal} {θ : ℝ → EReal}
    (hpθ : IsProper θ) (hcf : Convex ℝ (epigraph f)) (hcθ : Convex ℝ (epigraph θ)) :
    Convex ℝ (epigraph (rescalingHeightIntegrand f θ)) := by
  intro p hp q hq t s ht hs hts
  obtain ⟨hpF,hpT⟩ := (rescalingHeightIntegrand_le_iff hpθ p.1.fst p.1.snd p.2).mp hp
  obtain ⟨hqF,hqT⟩ := (rescalingHeightIntegrand_le_iff hpθ q.1.fst q.1.snd q.2).mp hq
  apply (rescalingHeightIntegrand_le_iff hpθ (t*p.1.fst+s*q.1.fst)
    (t • p.1.snd+s • q.1.snd) (t*p.2+s*q.2)).mpr
  exact ⟨hcf (show (p.1.snd,p.1.fst) ∈ epigraph f from hpF)
      (show (q.1.snd,q.1.fst) ∈ epigraph f from hqF) ht hs hts,
    hcθ (show (p.1.fst,p.2) ∈ epigraph θ from hpT)
      (show (q.1.fst,q.2) ∈ epigraph θ from hqT) ht hs hts⟩

theorem rescalingHeightIntegrand_subgradients_of_convex {f : E → EReal} {θ : ℝ → EReal}
    {x : E} {c d : ℝ} (hf : LowerSemicontinuous f) (hpθ : IsProper θ) (hθ : LowerSemicontinuous θ)
    (hcf : Convex ℝ (epigraph f)) (hcθ : Convex ℝ (epigraph θ))
    (hx : f x = c) (hc : θ c = d)
    (hQ : 0 ∉ subdifferential f x ∨ horizonSubdifferential θ c = {0}) :
    {v | WithLp.toLp 2 ((0:ℝ),v) ∈ subdifferential (rescalingHeightIntegrand f θ) (WithLp.toLp 2 (c,x))}
      = rescalingSubgradientSet (subdifferential θ c) f x ∧
    {v | WithLp.toLp 2 ((0:ℝ),v) ∈ horizonSubdifferential (rescalingHeightIntegrand f θ) (WithLp.toLp 2 (c,x))}
      = rescalingSubgradientSet (horizonSubdifferential θ c) f x := by
  have hC : IsClosed (rescalingHeightConstraint f) := (isClosed_euclideanEpigraph hf).preimage
    (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ E).continuous
  have hg : LowerSemicontinuous (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst) := hθ.comp (WithLp.fstL 2 ℝ ℝ E).continuous
  have hmem : WithLp.toLp 2 (c,x) ∈ rescalingHeightConstraint f := hx.le
  have hqual := rescaling_height_qualification hθ hx hc hQ
  have hgc : Convex ℝ (epigraph (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst)) :=
    convex_epigraph_heightFunction (E := E) hcθ
  have hloc : IsLocallyLscAt (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst) (WithLp.toLp 2 (c,x)) :=
    locallyLscAt_of_lowerSemicontinuous_finite (g := fun q : WithLp 2 (ℝ × E) ↦ θ q.fst)
      (z := WithLp.toLp 2 (c,x)) hg hc
  have hr : IsSubdifferentiallyRegularAt (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst) (WithLp.toLp 2 (c,x)) :=
    (isSubdifferentiallyRegularAt_of_convex hgc hloc).1
  have hconvC : Convex ℝ (rescalingHeightConstraint f) :=
    (convex_preimage_continuousLinearEquiv (l2ProdEquiv E) hcf).linear_preimage
      (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ E).toLinearMap
  have hR : IsClarkeRegularAt (rescalingHeightConstraint f) (WithLp.toLp 2 (c,x)) :=
    isClarkeRegularAt_of_convex hconvC hmem (RW.IsClosed.isLocallyClosedAt hC _)
  have hsub := subdifferential_indicator_add_eq hr hC hg (isProper_heightFunction hpθ) hmem hR hqual
  have hhor := horizonSubdifferential_indicator_add_eq hr hC hg (isProper_heightFunction hpθ) hmem hR hqual
  rw [← rescalingHeightIntegrand_eq_indicator_add f θ,subdifferential_heightFunction hc x] at hsub
  rw [← rescalingHeightIntegrand_eq_indicator_add f θ,horizonSubdifferential_heightFunction hθ hc x] at hhor
  exact ⟨Set.ext (fun v ↦ (Set.ext_iff.mp hsub (WithLp.toLp 2 ((0:ℝ),v))).trans
      (horizontal_normal_add_height_iff hf hx _)),
    Set.ext (fun v ↦ (Set.ext_iff.mp hhor (WithLp.toLp 2 ((0:ℝ),v))).trans
      (horizontal_normal_add_height_iff hf hx _))⟩

/-- **Theorem 10.19(b)**, corrected exact convex formulas. The ordinary
horizon branch is present precisely when zero is an outer subgradient. -/
theorem nonlinearRescaling_monotone_convex_equalities {f : E → EReal} {θ : ℝ → EReal}
    {x : E} {c d : ℝ} (hp : IsProper f) (hf : LowerSemicontinuous f)
    (hpθ : IsProper θ) (hθ : LowerSemicontinuous θ)
    (hcf : Convex ℝ (epigraph f)) (hcθ : Convex ℝ (epigraph θ))
    (hm : Monotone θ) (hsup : (⨆ a : ℝ, θ a) = ⊤)
    (hx : f x = c) (hc : θ c = d) (hstrict : ∀ a : ℝ, c < a → θ c < θ a)
    (hQ : 0 ∉ subdifferential f x ∨ horizonSubdifferential θ c = {0}) :
    Convex ℝ (epigraph (extendedRescaling θ f)) ∧
    subdifferential (extendedRescaling θ f) x = rescalingSubgradientSet (subdifferential θ c) f x ∧
    horizonSubdifferential (extendedRescaling θ f) x = rescalingSubgradientSet (horizonSubdifferential θ c) f x := by
  have hl := lowerSemicontinuous_rescalingHeightIntegrand hp hf hpθ hθ
  have hb := isParametricallyLevelBounded_rescalingHeightIntegrand hp hf hpθ hm hsup
  have he := parametricValue_rescalingHeightIntegrand hp hpθ hm
  have hu : parametricValue (rescalingHeightIntegrand f θ) x = d := by
    rw [he,extendedRescaling_of_finite hx,hc]
  have hmin : c ∈ parametricMinimizers (rescalingHeightIntegrand f θ) x := by
    rw [parametricMinimizers_rescalingHeightIntegrand hp hpθ hm hx hc hstrict]
    exact mem_singleton c
  have hconv := convex_epigraph_rescalingHeightIntegrand hpθ hcf hcθ
  obtain ⟨hs,hh⟩ := rescalingHeightIntegrand_subgradients_of_convex hf hpθ hθ hcf hcθ hx hc hQ
  refine ⟨he ▸ convex_epigraph_parametricValue hconv hl hb,?_,?_⟩
  · rw [← he]
    exact (subdifferential_parametricValue_eq_at_minimizer (f := rescalingHeightIntegrand f θ)
      (u := x) (x := c) hconv hl hb hu hmin).trans hs
  · rw [← he]
    exact (horizonSubdifferential_parametricValue_eq_at_minimizer (f := rescalingHeightIntegrand f θ)
      (u := x) (x := c) hconv hl (isProper_rescalingHeightIntegrand hpθ hx hc) hb hu hmin).trans hh

/-- For a monotone convex scalar function, horizon multipliers are nonnegative. -/
theorem nonneg_horizonSubgradient_of_monotone_convex {θ : ℝ → EReal} {c d t : ℝ}
    (hθ : LowerSemicontinuous θ) (hcθ : Convex ℝ (epigraph θ)) (hm : Monotone θ)
    (hc : θ c = d) (ht : t ∈ horizonSubdifferential θ c) : 0 ≤ t := by
  have hn := horizontal_normal_of_mem_horizonSubdifferential hc ht
  have hce : Convex ℝ (euclideanEpigraph θ) := convex_preimage_continuousLinearEquiv (l2ProdEquiv ℝ) hcθ
  rw [normalCone_eq_of_convex hce
    (show WithLp.toLp 2 (c,d) ∈ euclideanEpigraph θ from hc.le)] at hn
  have hy : WithLp.toLp 2 (c-1,d) ∈ euclideanEpigraph θ := (hm (by linarith : c-1 ≤ c)).trans hc.le
  have hh := hn (WithLp.toLp 2 (c-1,d)) hy
  change (c-1-c)*t+(d-d)*0 ≤ 0 at hh
  linarith

/-- When the zero multiplier is present, the union notation is exact. -/
theorem rescalingSubgradientSet_eq_printed {f : E → EReal} {x : E} {c : ℝ} {Λ : Set ℝ}
    (hx : f x = c) (hz : 0 ∈ Λ) (hn : ∀ t ∈ Λ, 0 ≤ t) :
    rescalingSubgradientSet Λ f x =
      {v | ∃ t ∈ Λ, ∃ w ∈ subdifferential f x, v = t • w} ∪ horizonSubdifferential f x := by
  apply Subset.antisymm (rescalingSubgradientSet_subset_printed _ _ _)
  rintro v (⟨t,ht,w,hw,rfl⟩ | hv)
  · rcases eq_or_lt_of_le (hn t ht) with he | he
    · subst t
      exact Or.inr ⟨hz,by simpa only [zero_smul] using
        (mem_horizonSubdifferential_iff_zero_or_scaledSeq hx).mpr (Or.inl (rfl : (0:E) = 0))⟩
    · exact Or.inl ⟨t,ht,he,w,hw,rfl⟩
  · exact Or.inr ⟨hz,hv⟩

/-- The printed horizon equality in 10.19(b) is valid without correction. -/
theorem nonlinearRescaling_monotone_convex_horizon {f : E → EReal} {θ : ℝ → EReal}
    {x : E} {c d : ℝ} (hp : IsProper f) (hf : LowerSemicontinuous f)
    (hpθ : IsProper θ) (hθ : LowerSemicontinuous θ)
    (hcf : Convex ℝ (epigraph f)) (hcθ : Convex ℝ (epigraph θ))
    (hm : Monotone θ) (hsup : (⨆ a : ℝ, θ a) = ⊤)
    (hx : f x = c) (hc : θ c = d) (hstrict : ∀ a : ℝ, c < a → θ c < θ a)
    (hQ : 0 ∉ subdifferential f x ∨ horizonSubdifferential θ c = {0}) :
    horizonSubdifferential (extendedRescaling θ f) x =
      {v | ∃ t ∈ horizonSubdifferential θ c, ∃ w ∈ subdifferential f x, v = t • w} ∪ horizonSubdifferential f x := by
  rw [(nonlinearRescaling_monotone_convex_equalities hp hf hpθ hθ hcf hcθ hm hsup hx hc hstrict hQ).2.2]
  exact rescalingSubgradientSet_eq_printed hx
    ((mem_horizonSubdifferential_iff_zero_or_scaledSeq hc).mpr (Or.inl rfl))
    (fun _ ht ↦ nonneg_horizonSubgradient_of_monotone_convex hθ hcθ hm hc ht)

end
end RW
