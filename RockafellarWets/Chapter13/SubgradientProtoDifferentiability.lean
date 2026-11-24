/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Proto-differentiability of subgradient mappings

Theorem 13.40.
-/

import RockafellarWets.Chapter13.SubgradientLipschitzGeometry
import RockafellarWets.Chapter13.SecondOrderChainRule
import RockafellarWets.Chapter12.ResolventMaximality
import RockafellarWets.Chapter12.ConvexSubgradientMappings
import RockafellarWets.Chapter8.SubgradientExistence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Module

open Filter Set Topology Metric MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Graphs parametrized by equi-Lipschitz mappings -/

section ParametrizedGraphs

variable {ι : Type*} {l : Filter ι}

/-- The graph `{(w, z) ∣ w + λz ∈ Dᵢ, gᵢ(w + λz) = z}`, the image of the graph of `gᵢ` on `Dᵢ`
under the linear change of coordinates `(u, z) ↦ (u - λz, z)`. -/
def lipschitzParamGraph (D : ι → Set E) (g : ι → E → E) (lam : ℝ) (i : ι) : Set (E × E) :=
  {p | p.1 + lam • p.2 ∈ D i ∧ g i (p.1 + lam • p.2) = p.2}

omit [FiniteDimensional ℝ E] in
theorem norm_add_smul_sub_le (a b : E × E) (lam : ℝ) :
    ‖(a.1 + lam • a.2) - (b.1 + lam • b.2)‖ ≤ (1 + |lam|) * dist a b := by
  have h1 : ‖a.1 - b.1‖ ≤ dist a b := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
  have h2 : ‖a.2 - b.2‖ ≤ dist a b := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_right _ _
  calc ‖(a.1 + lam • a.2) - (b.1 + lam • b.2)‖ = ‖(a.1 - b.1) + lam • (a.2 - b.2)‖ := by
        congr 1; rw [smul_sub]; abel
    _ ≤ ‖a.1 - b.1‖ + |lam| * ‖a.2 - b.2‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_eq_abs]
    _ ≤ dist a b + |lam| * dist a b := by gcongr
    _ = (1 + |lam|) * dist a b := by ring

omit [FiniteDimensional ℝ E] in
/-- Pointwise convergence of equi-Lipschitz parametrizations gives graphical convergence of the
parametrized graphs. -/
theorem pkConvergesAlong_lipschitzParamGraph_of_tendsto [l.NeBot] {D : ι → Set E} {g : ι → E → E}
    {lam L : ℝ} (hL0 : 0 ≤ L) (hD : ∀ R, ∀ᶠ i in l, closedBall (0 : E) R ⊆ D i)
    (hL : ∀ᶠ i in l, ∀ u ∈ D i, ∀ u' ∈ D i, ‖g i u - g i u'‖ ≤ L * ‖u - u'‖)
    {g₀ : E → E} (hg : ∀ u, Tendsto (fun i ↦ g i u) l (𝓝 (g₀ u))) :
    PKConvergesAlong l (lipschitzParamGraph D g lam) {p | g₀ (p.1 + lam • p.2) = p.2} := by
  set K := {p : E × E | g₀ (p.1 + lam • p.2) = p.2}
  have hin : ∀ u : E, ∀ᶠ i in l, u ∈ D i := fun u ↦
    (hD ‖u‖).mono fun i hi ↦ hi (by rw [mem_closedBall, dist_zero_right])
  have hKin : K ⊆ innerSetLimitAlong l (lipschitzParamGraph D g lam) := by
    intro p hp V hV
    set u := p.1 + lam • p.2
    have hlim : Tendsto (fun i ↦ (u - lam • g i u, g i u)) l (𝓝 (u - lam • g₀ u, g₀ u)) :=
      (tendsto_const_nhds.sub ((hg u).const_smul lam)).prodMk_nhds (hg u)
    have hp' : (u - lam • g₀ u, g₀ u) = p := by
      have h : g₀ u = p.2 := hp
      rw [h]; ext <;> simp [u]
    rw [hp'] at hlim
    filter_upwards [hlim.eventually hV, hin u] with i hi hiD
    exact ⟨_, ⟨by simp only [sub_add_cancel]; exact hiD, by simp only [sub_add_cancel]⟩, hi⟩
  have hKout : outerSetLimitAlong l (lipschitzParamGraph D g lam) ⊆ K := by
    intro p hp
    by_contra hne
    set u := p.1 + lam • p.2
    have hδ : 0 < ‖g₀ u - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    set δ := ‖g₀ u - p.2‖
    set r := δ / (2 * (L * (1 + |lam|) + 1))
    have hr : 0 < r := by positivity
    have hrδ : (L * (1 + |lam|) + 1) * r = δ / 2 := by
      simp only [r]; field_simp
    have hfreq := hp (ball p r) (ball_mem_nhds p hr)
    have hev : ∀ᶠ i in l, ‖g i u - g₀ u‖ < δ / 2 ∧ u ∈ D i ∧
        ∀ u ∈ D i, ∀ u' ∈ D i, ‖g i u - g i u'‖ ≤ L * ‖u - u'‖ := by
      have h1 : ∀ᶠ i in l, dist (g i u) (g₀ u) < δ / 2 :=
        (hg u).eventually (ball_mem_nhds _ (by positivity))
      filter_upwards [h1, hin u, hL] with i hi1 hi2 hi3
      exact ⟨by rwa [← dist_eq_norm], hi2, hi3⟩
    obtain ⟨i, ⟨q, ⟨hqD, hqg⟩, hqV⟩, hi1, hiu, hiL⟩ := (hfreq.and_eventually hev).exists
    rw [mem_ball] at hqV
    have hdu : ‖(q.1 + lam • q.2) - u‖ ≤ (1 + |lam|) * r :=
      (norm_add_smul_sub_le q p lam).trans (by gcongr)
    have hgq := hiL _ hiu _ hqD
    have hz : ‖q.2 - p.2‖ < r := by
      rw [← dist_eq_norm]
      exact lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hqV
    have : δ < δ := by
      calc δ = ‖g₀ u - p.2‖ := rfl
        _ = ‖(g₀ u - g i u) + (g i u - g i (q.1 + lam • q.2)) + (q.2 - p.2)‖ := by
            rw [hqg]; congr 1; abel
        _ ≤ ‖g₀ u - g i u‖ + ‖g i u - g i (q.1 + lam • q.2)‖ + ‖q.2 - p.2‖ :=
            norm_add₃_le
        _ < δ / 2 + L * ((1 + |lam|) * r) + r := by
            have h1 : ‖g₀ u - g i u‖ < δ / 2 := by rwa [norm_sub_rev]
            have h2 : ‖g i u - g i (q.1 + lam • q.2)‖ ≤ L * ((1 + |lam|) * r) := by
              refine hgq.trans (mul_le_mul_of_nonneg_left ?_ hL0)
              rw [norm_sub_rev]; exact hdu
            linarith
        _ = δ := by linarith
    exact lt_irrefl _ this
  have hio := innerSetLimitAlong_subset_outerSetLimitAlong (l := l)
    (lipschitzParamGraph D g lam)
  exact ⟨Subset.antisymm (hio.trans hKout) hKin, Subset.antisymm hKout (hKin.trans hio)⟩

omit [FiniteDimensional ℝ E] in
/-- Graphical convergence of parametrized graphs forces pointwise convergence of equi-Lipschitz
parametrizations vanishing at the origin. -/
theorem tendsto_of_pkConvergesAlong_lipschitzParamGraph [FiniteDimensional ℝ E] [l.NeBot]
    {D : ι → Set E} {g : ι → E → E} {lam L : ℝ} (hL0 : 0 ≤ L)
    (hD : ∀ R, ∀ᶠ i in l, closedBall (0 : E) R ⊆ D i)
    (hL : ∀ᶠ i in l, ∀ u ∈ D i, ∀ u' ∈ D i, ‖g i u - g i u'‖ ≤ L * ‖u - u'‖)
    (h0 : ∀ᶠ i in l, g i 0 = 0) {K : Set (E × E)}
    (hK : PKConvergesAlong l (lipschitzParamGraph D g lam) K) (u : E) :
    ∃ z, Tendsto (fun i ↦ g i u) l (𝓝 z) := by
  have hin : ∀ u : E, ∀ᶠ i in l, u ∈ D i := fun u ↦
    (hD ‖u‖).mono fun i hi ↦ hi (by rw [mem_closedBall, dist_zero_right])
  have hbd : ∀ᶠ i in l, g i u ∈ closedBall (0 : E) (L * ‖u‖) := by
    filter_upwards [hin u, hin 0, hL, h0] with i hu h0' hiL hg0
    rw [mem_closedBall, dist_zero_right]
    have := hiL u hu 0 h0'
    rwa [hg0, sub_zero, sub_zero] at this
  obtain ⟨z, -, hz⟩ := (isCompact_closedBall (0 : E) (L * ‖u‖)).exists_mapClusterPt_of_frequently
    hbd.frequently
  refine ⟨z, ?_⟩
  -- the cluster point gives a point of the outer, hence inner, limit
  have hout : (u - lam • z, z) ∈ outerSetLimitAlong l (lipschitzParamGraph D g lam) := by
    intro V hV
    have hψ : Continuous fun y : E ↦ (u - lam • y, y) :=
      (continuous_const.sub (continuous_const.smul continuous_id)).prodMk continuous_id
    have hV' : (fun y : E ↦ (u - lam • y, y)) ⁻¹' V ∈ 𝓝 z := hψ.continuousAt.preimage_mem_nhds hV
    have hfr := mapClusterPt_iff_frequently.1 hz _ hV'
    exact (hfr.and_eventually (hin u)).mono fun i ⟨hiV, hiu⟩ ↦
      ⟨_, ⟨by simp only [sub_add_cancel]; exact hiu, by simp only [sub_add_cancel]⟩, hiV⟩
  rw [hK.outer_eq, ← hK.inner_eq] at hout
  rw [Metric.tendsto_nhds]
  intro η hη
  set r := η / (2 * (L * (1 + |lam|) + 1))
  have hr : 0 < r := by positivity
  have hrη : (L * (1 + |lam|) + 1) * r = η / 2 := by simp only [r]; field_simp
  filter_upwards [hout (ball _ r) (ball_mem_nhds _ hr), hin u, hL]
    with i ⟨q, ⟨hqD, hqg⟩, hqV⟩ hiu hiL
  rw [mem_ball] at hqV
  have hdu : ‖(q.1 + lam • q.2) - u‖ ≤ (1 + |lam|) * r := by
    have h := norm_add_smul_sub_le q (u - lam • z, z) lam
    simp only [sub_add_cancel] at h
    exact h.trans (by gcongr)
  have hz' : ‖q.2 - z‖ < r := by
    rw [← dist_eq_norm]
    exact lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hqV
  have hgq := hiL _ hiu _ hqD
  rw [dist_eq_norm]
  calc ‖g i u - z‖ = ‖(g i u - g i (q.1 + lam • q.2)) + (q.2 - z)‖ := by rw [hqg]; congr 1; abel
    _ ≤ ‖g i u - g i (q.1 + lam • q.2)‖ + ‖q.2 - z‖ := norm_add_le _ _
    _ < L * ((1 + |lam|) * r) + r := by
        have h2 : ‖g i u - g i (q.1 + lam • q.2)‖ ≤ L * ((1 + |lam|) * r) := by
          refine hgq.trans (mul_le_mul_of_nonneg_left ?_ hL0)
          rw [norm_sub_rev]; exact hdu
        linarith
    _ = η / 2 := by linarith
    _ < η := by linarith

end ParametrizedGraphs

/-! ### The data of Proposition 13.37 -/

section Core

/-- The conclusion of Proposition 13.37 for given `ε` and `λ₀`. -/
def ProxEnvelopeModel (f : E → EReal) (x : E) (ε lam₀ : ℝ) : Prop :=
  ∀ lam, 0 < lam → lam < lam₀ → ∃ P : E → E,
    IsOpen (proxRange f x ε lam) ∧ x ∈ proxRange f x ε lam ∧ P x = x ∧
    (∀ u ∈ proxRange f x ε lam, proximalMappingEReal f lam u = {P u}) ∧
    (∀ u ∈ proxRange f x ε lam, ∀ u' ∈ proxRange f x ε lam,
      0 ≤ ⟪P u' - P u, u' - u⟫_ℝ ∧ ‖P u' - P u‖ ≤ 2 * ‖u' - u‖) ∧
    (∀ u ∈ proxRange f x ε lam, moreauEnvelopeEReal f lam u ≠ ⊥ ∧
      moreauEnvelopeEReal f lam u ≠ ⊤ ∧
      HasFDerivAt (fun z ↦ (moreauEnvelopeEReal f lam z).toReal)
        (innerSL ℝ (lam⁻¹ • (u - P u))) u) ∧
    (∀ u ∈ proxRange f x ε lam, ∀ u' ∈ proxRange f x ε lam,
      ‖lam⁻¹ • (u' - P u') - lam⁻¹ • (u - P u)‖ ≤ 3 / lam * ‖u' - u‖) ∧
    (∀ u ∈ proxRange f x ε lam, ∀ w,
      lam⁻¹ • (u - P u) = w ↔ ∃ y, w ∈ proxLocalization f x ε y ∧ u = y + lam • w)

/-- Proposition 13.37 in the form of `ProxEnvelopeModel`. -/
theorem IsProxRegularAt.exists_proxEnvelopeModel {f : E → EReal} {x : E}
    (hpr : IsProxRegularAt f x 0) (hpb : IsProxBounded f) :
    ∃ ε > 0, ∃ lam₀ > 0, ProxEnvelopeModel f x ε lam₀ :=
  proximal_mappings_and_moreau_envelopes hpr hpb

/-- The data used in the proof of Theorem 13.40, for `f` prox-regular at `x̄` for `0` and
prox-bounded: a parameter `λ` with `λμ ≤ 1/2` for a constant `μ` of the global prox-regularity
inequality, the proximal mapping `P = P_λ f` on `U = rge(I + λT)`, the envelope `e = e_λ f`, the
description of the localization `T` of `∂f` through `G = λ⁻¹(I - P) = ∇e`, the values of `f` along
`gph T`, and the global inequalities. -/
structure ProxCore (f : E → EReal) (x : E) (ε : ℝ) where
  lam : ℝ
  mu : ℝ
  c : ℝ
  δ₀ : ℝ
  P : E → E
  hlam : 0 < lam
  hmu : 0 < mu
  hlammu : lam * mu ≤ 1 / 2
  hδ₀ : 0 < δ₀
  hfx : f x = c
  hUo : IsOpen (proxRange f x ε lam)
  hball : ball x δ₀ ⊆ proxRange f x ε lam
  hPx : P x = x
  hPLip : ∀ u ∈ proxRange f x ε lam, ∀ u' ∈ proxRange f x ε lam, ‖P u' - P u‖ ≤ 2 * ‖u' - u‖
  hGLip : ∀ u ∈ proxRange f x ε lam, ∀ u' ∈ proxRange f x ε lam,
    ‖lam⁻¹ • (u' - P u') - lam⁻¹ • (u - P u)‖ ≤ 3 / lam * ‖u' - u‖
  hderiv : ∀ u ∈ proxRange f x ε lam, HasFDerivAt (fun z ↦ (moreauEnvelopeEReal f lam z).toReal)
    (innerSL ℝ (lam⁻¹ • (u - P u))) u
  he : (moreauEnvelopeEReal f lam x).toReal = c
  hval : ∀ u ∈ proxRange f x ε lam, f (P u) =
    (((moreauEnvelopeEReal f lam u).toReal - lam / 2 * ‖lam⁻¹ • (u - P u)‖ ^ 2 : ℝ) : EReal)
  hgraph : ∀ y w, w ∈ proxLocalization f x ε y ↔
    y + lam • w ∈ proxRange f x ε lam ∧ lam⁻¹ • ((y + lam • w) - P (y + lam • w)) = w
  hineq : ∀ u ∈ ball x δ₀, ∀ x', f (P u) +
    ((⟪lam⁻¹ • (u - P u), x' - P u⟫_ℝ - mu / 2 * ‖x' - P u‖ ^ 2 : ℝ) : EReal) ≤ f x'
  hlow : ∀ x', ((c - mu / 2 * ‖x' - x‖ ^ 2 : ℝ) : EReal) ≤ f x'

omit [FiniteDimensional ℝ E] in
/-- The data `ProxCore` exist for the `ε` of any instance of Proposition 13.37. -/
theorem ProxCore.nonempty {f : E → EReal} {x : E} (hpr : IsProxRegularAt f x 0)
    (hpb : IsProxBounded f) {ε lam₀ : ℝ} (hlam₀ : 0 < lam₀) (H : ProxEnvelopeModel f x ε lam₀) :
    Nonempty (ProxCore f x ε) := by
  obtain ⟨ε₂, hε₂, μ, hμ, hglob⟩ := hpr.exists_global_inequality hpb
  obtain ⟨⟨hx1, hx2, -⟩, h0, -⟩ := hpr
  set lam := min lam₀ (1 / μ) / 2 with hlam_def
  have hlam : 0 < lam := by positivity
  have hlamlt : lam < lam₀ := by
    have := min_le_left lam₀ (1 / μ); simp only [hlam_def]; linarith
  have hlammu : lam * μ ≤ 1 / 2 := by
    have h1 : min lam₀ (1 / μ) ≤ 1 / μ := min_le_right _ _
    have h2 : lam ≤ 1 / μ / 2 := by simp only [hlam_def]; linarith
    calc lam * μ ≤ 1 / μ / 2 * μ := mul_le_mul_of_nonneg_right h2 hμ.le
      _ = 1 / 2 := by field_simp
  obtain ⟨P, hUo, hxU, hPx, hPsingle, hPmono, hdiff, hGLip, hgr⟩ := H lam hlam hlamlt
  set U := proxRange f x ε lam with hU
  set c := (f x).toReal with hc_def
  have hc : f x = (c : EReal) := (EReal.coe_toReal hx2 hx1).symm
  set G : E → E := fun u ↦ lam⁻¹ • (u - P u) with hG
  -- values of `f` along the graph
  have hval : ∀ u ∈ U, f (P u) =
      (((moreauEnvelopeEReal f lam u).toReal - lam / 2 * ‖G u‖ ^ 2 : ℝ) : EReal) := by
    intro u hu
    have hmem : P u ∈ proximalMappingEReal f lam u := by rw [hPsingle u hu]; exact mem_singleton _
    obtain ⟨hobj, -⟩ := mem_proximalMappingEReal_iff.1 hmem
    obtain ⟨he1, he2, -⟩ := hdiff u hu
    have he : moreauEnvelopeEReal f lam u = ((moreauEnvelopeEReal f lam u).toReal : EReal) :=
      (EReal.coe_toReal he2 he1).symm
    have hnorm : lam / 2 * ‖G u‖ ^ 2 = 1 / (2 * lam) * ‖P u - u‖ ^ 2 := by
      simp only [hG, norm_smul, norm_inv, Real.norm_of_nonneg hlam.le, norm_sub_rev u (P u)]
      field_simp
    rw [proximalObjectiveEReal, he] at hobj
    rw [hnorm]
    rcases ereal_trichotomy (f (P u)) with h' | h' | ⟨r, hr⟩
    · rw [h', EReal.bot_add] at hobj; exact absurd hobj.symm (EReal.coe_ne_bot _)
    · rw [h', EReal.top_add_coe] at hobj; exact absurd hobj (EReal.coe_ne_top _).symm
    · rw [hr] at hobj ⊢
      rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at hobj
      rw [EReal.coe_eq_coe_iff]
      linarith
  have he : (moreauEnvelopeEReal f lam x).toReal = c := by
    have h := hval x hxU
    rw [hPx, hc, EReal.coe_eq_coe_iff] at h
    simp only [hG, hPx, sub_self, smul_zero, norm_zero] at h
    linarith
  -- the graph of `T`
  have hgraph : ∀ y w, w ∈ proxLocalization f x ε y ↔ y + lam • w ∈ U ∧ G (y + lam • w) = w := by
    intro y w
    constructor
    · intro hw
      have hu : y + lam • w ∈ U := ⟨y, w, hw, rfl⟩
      exact ⟨hu, (hgr _ hu w).2 ⟨y, hw, rfl⟩⟩
    · rintro ⟨hu, hGw⟩
      obtain ⟨y', hy', hyy⟩ := (hgr _ hu w).1 hGw
      rw [add_left_inj] at hyy
      rw [hyy]; exact hy'
  have hPG : ∀ u, P u + lam • G u = u := fun u ↦ by
    simp only [hG, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]; abel
  have hGsub : ∀ u ∈ U, G u ∈ subdifferential f (P u) := by
    intro u hu
    have h := (hgraph (P u) (G u)).2 ⟨by rw [hPG]; exact hu, by rw [hPG]⟩
    exact h.1
  -- continuity of the envelope at `x̄`
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 hUo x hxU
  have hecont : ContinuousAt (fun z ↦ (moreauEnvelopeEReal f lam z).toReal) x :=
    (hdiff x hxU).2.2.continuousAt
  obtain ⟨r₁, hr₁, hr₁e⟩ := Metric.continuousAt_iff.1 hecont ε₂ hε₂
  set δ₀ := min r₀ (min r₁ (min (ε₂ / 2) (lam * ε₂ / 3))) with hδ₀_def
  have hδ₀ : 0 < δ₀ := by positivity
  have hδr₀ : δ₀ ≤ r₀ := min_le_left _ _
  have hδr₁ : δ₀ ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ₀ ≤ ε₂ / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδl : δ₀ ≤ lam * ε₂ / 3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hballU : ball x δ₀ ⊆ U := (ball_subset_ball hδr₀).trans hr₀U
  have hGx : G x = 0 := by simp [hG, hPx]
  have hineq : ∀ u ∈ ball x δ₀, ∀ x', f (P u) +
      ((⟪G u, x' - P u⟫_ℝ - μ / 2 * ‖x' - P u‖ ^ 2 : ℝ) : EReal) ≤ f x' := by
    intro u hu x'
    have huU := hballU hu
    rw [mem_ball, dist_eq_norm] at hu
    have hPu : ‖P u - x‖ < ε₂ := by
      have := (hPmono x hxU u huU).2
      rw [hPx] at this
      linarith
    have hGu : ‖G u - 0‖ < ε₂ := by
      have h1 := hGLip x hxU u huU
      rw [sub_zero]
      have h2 : ‖G u‖ ≤ 3 / lam * ‖u - x‖ := by
        simp only [hPx, sub_self, smul_zero, sub_zero] at h1
        exact h1
      calc ‖G u‖ ≤ 3 / lam * ‖u - x‖ := h2
        _ < 3 / lam * (lam * ε₂ / 3) := by
            apply mul_lt_mul_of_pos_left (lt_of_lt_of_le hu hδl) (by positivity)
        _ = ε₂ := by field_simp
    have hfu : f (P u) < f x + ε₂ := by
      rw [hval u huU, hc, ← EReal.coe_add, EReal.coe_lt_coe_iff]
      have h1 := hr₁e (show dist u x < r₁ by rw [dist_eq_norm]; linarith)
      rw [Real.dist_eq, he] at h1
      have h2 : 0 ≤ lam / 2 * ‖G u‖ ^ 2 := by positivity
      linarith [abs_lt.1 h1]
    exact hglob (P u) (G u) (hGsub u huU) hGu hPu hfu x'
  have hlow : ∀ x', ((c - μ / 2 * ‖x' - x‖ ^ 2 : ℝ) : EReal) ≤ f x' := by
    intro x'
    have h := hglob x 0 h0 (by simpa using hε₂) (by simpa using hε₂)
      (by rw [hc, ← EReal.coe_add]; exact EReal.coe_lt_coe_iff.2 (by linarith)) x'
    rw [hc, inner_zero_left, zero_sub, ← EReal.coe_add] at h
    convert h using 2
  exact ⟨⟨lam, μ, c, δ₀, P, hlam, hμ, hlammu, hδ₀, hc, hUo, hballU, hPx,
    fun u hu u' hu' ↦ (hPmono u hu u' hu').2, hGLip, fun u hu ↦ (hdiff u hu).2.2, he, hval,
    hgraph, hineq, hlow⟩⟩

end Core

/-! ### Estimates for second subderivatives -/

section Estimates

variable {f : E → EReal} {x : E}

omit [FiniteDimensional ℝ E] in
/-- A lower estimate of the quotients near `(0, w)` that converges bounds `d²f(x̄ | 0)(w)`. -/
theorem coe_le_secondSubderivative_of_eventually {w : E} {ψ : ℝ × E → ℝ} {L : ℝ}
    (hψ : ∀ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w, (ψ p : EReal) ≤ secondDifferenceQuotient f x 0 p.1 p.2)
    (hlim : Tendsto ψ (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 L)) :
    (L : EReal) ≤ secondSubderivative f x 0 w := by
  have h1 : Tendsto (fun p ↦ (ψ p : EReal)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (L : EReal)) :=
    (continuous_coe_real_ereal.tendsto L).comp hlim
  rw [← h1.liminf_eq]
  exact liminf_le_liminf hψ

omit [FiniteDimensional ℝ E] in
/-- `d²f(x̄ | 0)(w)` is at most the lower limit of the quotients along any approach to `(0, w)`. -/
theorem secondSubderivative_le_liminf {ι : Type*} {l : Filter ι} {w : E} {g : ι → ℝ × E}
    (hg : Tendsto g l (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w)) :
    secondSubderivative f x 0 w ≤
      liminf (fun i ↦ secondDifferenceQuotient f x 0 (g i).1 (g i).2) l :=
  liminf_le_liminf_of_le hg

end Estimates

/-! ### Rescaling -/

namespace ProxCore

variable {f : E → EReal} {x : E} {ε : ℝ} (K : ProxCore f x ε)

/-- `G = λ⁻¹(I - P) = ∇e_λ f` on `U`. -/
noncomputable def G (u : E) : E := K.lam⁻¹ • (u - K.P u)

/-- The envelope `e = e_λ f` as a real function. -/
noncomputable def e (u : E) : ℝ := (moreauEnvelopeEReal f K.lam u).toReal

/-- The rescaled proximal mapping `Pτ(u) = τ⁻¹(P(x̄ + τu) - x̄)`. -/
noncomputable def Ps (τ : ℝ) (u : E) : E := τ⁻¹ • (K.P (x + τ • u) - x)

/-- The rescaled gradient `Gτ(u) = τ⁻¹G(x̄ + τu)`, the difference quotient of `G` at `x̄`. -/
noncomputable def Gs (τ : ℝ) (u : E) : E := τ⁻¹ • K.G (x + τ • u)

/-- The halved second-order difference quotient `kτ(u) = τ⁻²(e(x̄ + τu) - e(x̄))` of `e`. -/
noncomputable def ks (τ : ℝ) (u : E) : ℝ := (τ ^ 2)⁻¹ * (K.e (x + τ • u) - K.c)

/-- The value `rτ(u) = 2kτ(u) - λ‖Gτ(u)‖²` of `Δ²_τ f(x̄ | 0)` at `Pτ(u)`. -/
noncomputable def rs (τ : ℝ) (u : E) : ℝ := 2 * K.ks τ u - K.lam * ‖K.Gs τ u‖ ^ 2

omit [FiniteDimensional ℝ E] in
theorem P_add_G (u : E) : K.P u + K.lam • K.G u = u := by
  simp only [G, smul_smul, mul_inv_cancel₀ K.hlam.ne', one_smul]; abel

omit [FiniteDimensional ℝ E] in
theorem G_x : K.G x = 0 := by simp [G, K.hPx]

omit [FiniteDimensional ℝ E] in
theorem e_x : K.e x = K.c := K.he

omit [FiniteDimensional ℝ E] in
theorem Ps_add_Gs {τ : ℝ} (hτ : τ ≠ 0) (u : E) : K.Ps τ u + K.lam • K.Gs τ u = u := by
  have h := K.P_add_G (x + τ • u)
  simp only [Ps, Gs]
  rw [smul_comm K.lam τ⁻¹, ← smul_add, sub_add_eq_add_sub, h, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ hτ, one_smul]

omit [FiniteDimensional ℝ E] in
theorem Ps_eq {τ : ℝ} (hτ : τ ≠ 0) (u : E) : K.Ps τ u = u - K.lam • K.Gs τ u := by
  exact eq_sub_of_add_eq (K.Ps_add_Gs hτ u)

omit [FiniteDimensional ℝ E] in
theorem add_smul_Ps {τ : ℝ} (hτ : τ ≠ 0) (u : E) : x + τ • K.Ps τ u = K.P (x + τ • u) := by
  simp only [Ps, smul_smul, mul_inv_cancel₀ hτ, one_smul]; abel

omit [FiniteDimensional ℝ E] in
theorem Gs_zero (τ : ℝ) : K.Gs τ 0 = 0 := by simp [Gs, K.G_x]

omit [FiniteDimensional ℝ E] in
theorem ks_zero (τ : ℝ) : K.ks τ 0 = 0 := by simp [ks, K.e_x]

omit [FiniteDimensional ℝ E] in
theorem Gs_lip {τ : ℝ} (hτ : 0 < τ) {u u' : E} (hu : x + τ • u ∈ proxRange f x ε K.lam)
    (hu' : x + τ • u' ∈ proxRange f x ε K.lam) :
    ‖K.Gs τ u - K.Gs τ u'‖ ≤ 3 / K.lam * ‖u - u'‖ := by
  have h := K.hGLip _ hu' _ hu
  have e1 : x + τ • u - (x + τ • u') = τ • (u - u') := by rw [smul_sub]; abel
  rw [e1, norm_smul, Real.norm_of_nonneg hτ.le] at h
  have e2 : K.Gs τ u - K.Gs τ u' = τ⁻¹ • (K.G (x + τ • u) - K.G (x + τ • u')) := by
    simp only [Gs, smul_sub]
  rw [e2, norm_smul, norm_inv, Real.norm_of_nonneg hτ.le]
  calc τ⁻¹ * ‖K.G (x + τ • u) - K.G (x + τ • u')‖ ≤ τ⁻¹ * (3 / K.lam * (τ * ‖u - u'‖)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 3 / K.lam * ‖u - u'‖ := by field_simp

omit [FiniteDimensional ℝ E] in
/-- Every bounded set of rescaled points eventually lies in `B(x̄, δ₀)`. -/
theorem eventually_mem_ball (R : ℝ) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ u : E, ‖u‖ ≤ R → x + τ • u ∈ ball x K.δ₀ := by
  have hpos : 0 < K.δ₀ / (|R| + 1) := div_pos K.hδ₀ (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hpos] with τ ⟨hτ0, hτ1⟩ u hu
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0.le]
  rw [lt_div_iff₀ (by positivity)] at hτ1
  have h1 : ‖u‖ ≤ |R| + 1 := by linarith [le_abs_self R]
  calc τ * ‖u‖ ≤ τ * (|R| + 1) := mul_le_mul_of_nonneg_left h1 hτ0.le
    _ < K.δ₀ := hτ1

omit [FiniteDimensional ℝ E] in
theorem eventually_mem_U (R : ℝ) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ u : E, ‖u‖ ≤ R → x + τ • u ∈ proxRange f x ε K.lam :=
  (K.eventually_mem_ball R).mono fun _ h u hu ↦ K.hball (h u hu)

omit [FiniteDimensional ℝ E] in
theorem norm_G_eq {τ : ℝ} (hτ : 0 < τ) (u : E) : ‖K.G (x + τ • u)‖ = τ * ‖K.Gs τ u‖ := by
  simp only [Gs, norm_smul, norm_inv, Real.norm_of_nonneg hτ.le]; field_simp

omit [FiniteDimensional ℝ E] in
theorem G_eq_smul_Gs {τ : ℝ} (hτ : 0 < τ) (u : E) :
    K.lam⁻¹ • (x + τ • u - K.P (x + τ • u)) = τ • K.Gs τ u := by
  change K.G (x + τ • u) = τ • (τ⁻¹ • K.G (x + τ • u))
  rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]

omit [FiniteDimensional ℝ E] in
theorem secondDifferenceQuotient_eq {τ : ℝ} (w' : E) :
    secondDifferenceQuotient f x 0 τ w' =
      ((2 / τ ^ 2 : ℝ) : EReal) * (f (x + τ • w') - (K.c : EReal)) := by
  simp [secondDifferenceQuotient, K.hfx]

omit [FiniteDimensional ℝ E] in
/-- The value of `Δ²_τ f(x̄ | 0)` at `Pτ(u)`. -/
theorem secondDifferenceQuotient_Ps {τ : ℝ} (hτ : 0 < τ) {u : E}
    (hu : x + τ • u ∈ proxRange f x ε K.lam) :
    secondDifferenceQuotient f x 0 τ (K.Ps τ u) = (K.rs τ u : EReal) := by
  have hv : f (x + τ • K.Ps τ u) =
      ((K.e (x + τ • u) - K.lam / 2 * ‖K.G (x + τ • u)‖ ^ 2 : ℝ) : EReal) := by
    rw [K.add_smul_Ps hτ.ne']; exact K.hval _ hu
  rw [secondDifferenceQuotient_of_coe K.hfx hv, EReal.coe_eq_coe_iff, K.norm_G_eq hτ]
  simp only [rs, ks, inner_zero_left, mul_zero, sub_zero]
  field_simp
  ring

omit [FiniteDimensional ℝ E] in
/-- The global prox-regularity inequality, rescaled. -/
theorem le_secondDifferenceQuotient {τ : ℝ} (hτ : 0 < τ) {u : E}
    (hu : x + τ • u ∈ ball x K.δ₀) (w' : E) :
    ((K.rs τ u + 2 * ⟪K.Gs τ u, w' - K.Ps τ u⟫_ℝ - K.mu * ‖w' - K.Ps τ u‖ ^ 2 : ℝ) : EReal) ≤
      secondDifferenceQuotient f x 0 τ w' := by
  set Ψ := K.rs τ u + 2 * ⟪K.Gs τ u, w' - K.Ps τ u⟫_ℝ - K.mu * ‖w' - K.Ps τ u‖ ^ 2 with hΨ
  have h := K.hineq _ hu (x + τ • w')
  have hv := K.hval _ (K.hball hu)
  rw [hv, ← EReal.coe_add] at h
  have hA : (moreauEnvelopeEReal f K.lam (x + τ • u)).toReal -
      K.lam / 2 * ‖K.lam⁻¹ • (x + τ • u - K.P (x + τ • u))‖ ^ 2 +
      (⟪K.lam⁻¹ • (x + τ • u - K.P (x + τ • u)), x + τ • w' - K.P (x + τ • u)⟫_ℝ -
        K.mu / 2 * ‖x + τ • w' - K.P (x + τ • u)‖ ^ 2) = K.c + τ ^ 2 / 2 * Ψ := by
    have e1 : x + τ • w' - K.P (x + τ • u) = τ • (w' - K.Ps τ u) := by
      rw [← K.add_smul_Ps hτ.ne', smul_sub]; abel
    rw [e1, K.G_eq_smul_Gs hτ, inner_smul_left, inner_smul_right, norm_smul, norm_smul,
      Real.norm_of_nonneg hτ.le]
    simp only [hΨ, rs, ks, e, RCLike.conj_to_real]
    field_simp
    ring
  rw [hA] at h
  rw [K.secondDifferenceQuotient_eq]
  rcases ereal_trichotomy (f (x + τ • w')) with h' | h' | ⟨r, hr⟩
  · rw [h'] at h; exact absurd (le_bot_iff.1 h) (EReal.coe_ne_bot _)
  · rw [h', EReal.top_sub_coe, EReal.coe_mul_top_of_pos (by positivity)]; exact le_top
  · rw [hr] at h ⊢
    rw [EReal.coe_le_coe_iff] at h
    rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity)]
    calc Ψ * τ ^ 2 = 2 * (τ ^ 2 / 2 * Ψ) := by ring
      _ ≤ 2 * (r - K.c) := by linarith

omit [FiniteDimensional ℝ E] in
/-- The global lower bound, rescaled. -/
theorem neg_le_secondDifferenceQuotient {τ : ℝ} (hτ : 0 < τ) (w' : E) :
    ((-(K.mu * ‖w'‖ ^ 2) : ℝ) : EReal) ≤ secondDifferenceQuotient f x 0 τ w' := by
  have h := K.hlow (x + τ • w')
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ.le] at h
  rw [K.secondDifferenceQuotient_eq]
  rcases ereal_trichotomy (f (x + τ • w')) with h' | h' | ⟨r, hr⟩
  · rw [h'] at h; exact absurd (le_bot_iff.1 h) (EReal.coe_ne_bot _)
  · rw [h', EReal.top_sub_coe, EReal.coe_mul_top_of_pos (by positivity)]; exact le_top
  · rw [hr] at h ⊢
    rw [EReal.coe_le_coe_iff] at h
    rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity)]
    calc -(K.mu * ‖w'‖ ^ 2) * τ ^ 2 = 2 * (-(K.mu / 2 * (τ * ‖w'‖) ^ 2)) := by ring
      _ ≤ 2 * (r - K.c) := by linarith

omit [FiniteDimensional ℝ E] in
/-- `kτ` is differentiable with gradient `Gτ`. -/
theorem ks_hasFDerivAt {τ : ℝ} (hτ : 0 < τ) {u : E} (hu : x + τ • u ∈ proxRange f x ε K.lam) :
    HasFDerivAt (K.ks τ) (innerSL ℝ (K.Gs τ u)) u := by
  have hd := K.hderiv _ hu
  have hpath : HasFDerivAt (fun v : E ↦ x + τ • v) (τ • ContinuousLinearMap.id ℝ E) u := by
    simpa using ((ContinuousLinearMap.id ℝ E).hasFDerivAt.const_smul τ).const_add x
  have hcomp := hd.comp u hpath
  have h2 := (hcomp.sub_const K.c).const_mul (τ ^ 2)⁻¹
  convert h2 using 1
  ext v
  simp only [Gs, G, innerSL_apply_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, smul_eq_mul]
  field_simp

omit [FiniteDimensional ℝ E] in
/-- The graphs of the difference quotients of `T` are parametrized by `Gτ`. -/
theorem svGraph_mappingDifferenceQuotient {τ : ℝ} (hτ : 0 < τ) :
    svGraph (mappingDifferenceQuotient (proxLocalization f x ε) x 0 τ) =
      lipschitzParamGraph (fun τ ↦ {u | x + τ • u ∈ proxRange f x ε K.lam}) K.Gs K.lam τ := by
  ext ⟨w, z⟩
  change z ∈ mappingDifferenceQuotient (proxLocalization f x ε) x 0 τ w ↔ _
  rw [mem_mappingDifferenceQuotient_iff hτ.ne', zero_add, K.hgraph]
  have e1 : x + τ • w + K.lam • τ • z = x + τ • (w + K.lam • z) := by
    rw [smul_add, smul_comm K.lam τ z]; abel
  simp only [lipschitzParamGraph, mem_setOf_eq, e1]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    simp only [Gs, G]
    rw [h2, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h3 : K.G (x + τ • (w + K.lam • z)) = τ • z := by
      have h4 := congrArg (τ • ·) h2
      simp only [Gs, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul] at h4
      exact h4
    exact h3

/-! ### Proto-differentiability of `T` and convergence of `Gτ` -/

omit [FiniteDimensional ℝ E] in
theorem eventually_closedBall_subset (R : ℝ) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), closedBall (0 : E) R ⊆ {u | x + τ • u ∈ proxRange f x ε K.lam} :=
  (K.eventually_mem_U R).mono fun _ h u hu ↦ h u (by rwa [mem_closedBall, dist_zero_right] at hu)

omit [FiniteDimensional ℝ E] in
theorem eventually_lip :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), ∀ u ∈ {u | x + τ • u ∈ proxRange f x ε K.lam},
      ∀ u' ∈ {u | x + τ • u ∈ proxRange f x ε K.lam},
        ‖K.Gs τ u - K.Gs τ u'‖ ≤ 3 / K.lam * ‖u - u'‖ :=
  Filter.mem_of_superset (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
    fun _ hτ _ hu _ hu' ↦ K.Gs_lip hτ hu hu'

omit [FiniteDimensional ℝ E] in
theorem svGraph_eventuallyEq :
    (fun τ ↦ svGraph (mappingDifferenceQuotient (proxLocalization f x ε) x 0 τ)) =ᶠ[𝓝[>] (0 : ℝ)]
      lipschitzParamGraph (fun τ ↦ {u | x + τ • u ∈ proxRange f x ε K.lam}) K.Gs K.lam :=
  Filter.mem_of_superset (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)
    fun _ hτ ↦ K.svGraph_mappingDifferenceQuotient hτ

/-- `T` is proto-differentiable at `x̄` for `0` exactly when the difference quotients `Gτ(u)` of
`G = ∇e_λ f` converge for every `u`. -/
theorem isProtoDifferentiableAt_iff :
    IsProtoDifferentiableAt (proxLocalization f x ε) x 0 ↔
      ∀ u, ∃ z, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 z) := by
  have hL0 : (0 : ℝ) ≤ 3 / K.lam := by have := K.hlam; positivity
  have heq := K.svGraph_eventuallyEq
  constructor
  · intro h u
    have hK : PKConvergesAlong (𝓝[>] (0 : ℝ))
        (lipschitzParamGraph (fun τ ↦ {u | x + τ • u ∈ proxRange f x ε K.lam}) K.Gs K.lam)
        (svGraph (graphicalDerivative (proxLocalization f x ε) x 0)) :=
      ⟨(innerSetLimitAlong_congr heq).symm.trans h.1, (outerSetLimitAlong_congr heq).symm.trans h.2⟩
    exact tendsto_of_pkConvergesAlong_lipschitzParamGraph hL0 K.eventually_closedBall_subset
      K.eventually_lip (Eventually.of_forall K.Gs_zero) hK u
  · intro h
    choose G₀ hG₀ using h
    have hK := pkConvergesAlong_lipschitzParamGraph_of_tendsto (lam := K.lam) hL0
      K.eventually_closedBall_subset K.eventually_lip hG₀
    have hD : svGraph (graphicalDerivative (proxLocalization f x ε) x 0) =
        {p : E × E | G₀ (p.1 + K.lam • p.2) = p.2} := by
      rw [svGraph_graphicalDerivative_eq_outerLimit, outerSetLimitAlong_congr heq, hK.2]
    rw [IsProtoDifferentiableAt, hD]
    exact ⟨(innerSetLimitAlong_congr heq).trans hK.1, (outerSetLimitAlong_congr heq).trans hK.2⟩

omit [FiniteDimensional ℝ E] in
/-- Under convergence of `Gτ` to `G₀`, the graphical derivative of `T` at `x̄` for `0` is
`{(w, z) ∣ G₀(w + λz) = z}`. -/
theorem svGraph_graphicalDerivative {G₀ : E → E}
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) :
    svGraph (graphicalDerivative (proxLocalization f x ε) x 0) =
      {p : E × E | G₀ (p.1 + K.lam • p.2) = p.2} := by
  have hL0 : (0 : ℝ) ≤ 3 / K.lam := by have := K.hlam; positivity
  have hK := pkConvergesAlong_lipschitzParamGraph_of_tendsto (lam := K.lam) hL0
    K.eventually_closedBall_subset K.eventually_lip hG₀
  rw [svGraph_graphicalDerivative_eq_outerLimit, outerSetLimitAlong_congr K.svGraph_eventuallyEq,
    hK.2]

/-! ### Lower and upper estimates for the second subderivative -/

omit [FiniteDimensional ℝ E] in
/-- The global lower bound `d²f(x̄ | 0)(w) ≥ -μ‖w‖²`. -/
theorem neg_le_secondSubderivative (w : E) :
    ((-(K.mu * ‖w‖ ^ 2) : ℝ) : EReal) ≤ secondSubderivative f x 0 w := by
  refine coe_le_secondSubderivative_of_eventually (ψ := fun p ↦ -(K.mu * ‖p.2‖ ^ 2)) ?_ ?_
  · filter_upwards [prod_mem_prod (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0) univ_mem] with p hp
    exact K.neg_le_secondDifferenceQuotient hp.1 p.2
  · exact ((continuous_const.mul (continuous_norm.pow 2)).neg.tendsto w).comp tendsto_snd

include K in
omit [FiniteDimensional ℝ E] in
theorem secondSubderivative_ne_bot (w : E) : secondSubderivative f x 0 w ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (K.neg_le_secondSubderivative w)

include K in
omit [FiniteDimensional ℝ E] in
/-- `d²f(x̄ | 0)(0) = 0`. -/
theorem secondSubderivative_zero : secondSubderivative f x 0 0 = 0 := by
  apply le_antisymm
  · have hg : Tendsto (fun τ : ℝ ↦ ((τ, 0) : ℝ × E)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 0) :=
      tendsto_id.prodMk tendsto_const_nhds
    refine (secondSubderivative_le_liminf hg).trans (le_of_eq ?_)
    have : (fun τ : ℝ ↦ secondDifferenceQuotient f x 0 (τ, (0 : E)).1 (τ, (0 : E)).2) =
        fun _ ↦ (0 : EReal) := by
      funext τ
      simp [secondDifferenceQuotient, K.hfx]
    rw [this, liminf_const]
  · simpa using K.neg_le_secondSubderivative 0

/-! ### Twice epi-differentiability forces convergence of `Gτ` -/

/-- The property of a limit `z` of `Gτ(u)` under twice epi-differentiability: with
`w = u - λz`, `d²f(x̄ | 0)(w) = a` is finite and `d²f(x̄ | 0) ≥ a + 2⟪z, · - w⟫ - μ‖· - w‖²`. -/
def LimitChar (u z : E) : Prop :=
  ∃ a : ℝ, secondSubderivative f x 0 (u - K.lam • z) = a ∧
    ∀ w', ((a + 2 * ⟪z, w' - (u - K.lam • z)⟫_ℝ - K.mu * ‖w' - (u - K.lam • z)‖ ^ 2 : ℝ) : EReal) ≤
      secondSubderivative f x 0 w'

omit [FiniteDimensional ℝ E] in
theorem limitChar_unique {u z₁ z₂ : E} (h₁ : K.LimitChar u z₁) (h₂ : K.LimitChar u z₂) :
    z₁ = z₂ := by
  obtain ⟨a₁, ha₁, hi₁⟩ := h₁
  obtain ⟨a₂, ha₂, hi₂⟩ := h₂
  have i1 := hi₁ (u - K.lam • z₂)
  have i2 := hi₂ (u - K.lam • z₁)
  rw [ha₂, EReal.coe_le_coe_iff] at i1
  rw [ha₁, EReal.coe_le_coe_iff] at i2
  have hw1 : u - K.lam • z₂ - (u - K.lam • z₁) = K.lam • (z₁ - z₂) := by rw [smul_sub]; abel
  have hw2 : u - K.lam • z₁ - (u - K.lam • z₂) = -(K.lam • (z₁ - z₂)) := by rw [smul_sub]; abel
  rw [hw1] at i1
  rw [hw2] at i2
  simp only [inner_neg_right, norm_neg, inner_smul_right, norm_smul, Real.norm_of_nonneg K.hlam.le]
    at i1 i2
  have hd : ⟪z₁, z₁ - z₂⟫_ℝ - ⟪z₂, z₁ - z₂⟫_ℝ = ‖z₁ - z₂‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have hd' : K.lam * ⟪z₁, z₁ - z₂⟫_ℝ - K.lam * ⟪z₂, z₁ - z₂⟫_ℝ = K.lam * ‖z₁ - z₂‖ ^ 2 := by
    rw [← mul_sub, hd]
  have hsum : 2 * K.lam * ‖z₁ - z₂‖ ^ 2 ≤ 2 * K.mu * (K.lam * ‖z₁ - z₂‖) ^ 2 := by linarith
  have hlm := K.hlammu
  have hlam := K.hlam
  have hn : ‖z₁ - z₂‖ ^ 2 ≤ 0 := by
    have h3 : 2 * K.lam * ‖z₁ - z₂‖ ^ 2 * (1 - K.lam * K.mu) ≤ 0 := by nlinarith
    have h4 : 0 < 2 * K.lam * (1 - K.lam * K.mu) := by nlinarith
    nlinarith
  have : ‖z₁ - z₂‖ = 0 := by nlinarith [norm_nonneg (z₁ - z₂)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

omit [FiniteDimensional ℝ E] in
/-- Limits of `Gτ(u)` along sequences have the property `LimitChar` when `f` is twice
epi-differentiable. -/
theorem limitChar_of_tendsto (hte : TwiceEpiDifferentiableAt f x 0) {u z : E} {τ : ℕ → ℝ}
    (hτ : Tendsto τ atTop (𝓝[>] 0)) (hz : Tendsto (fun n ↦ K.Gs (τ n) u) atTop (𝓝 z)) :
    K.LimitChar u z := by
  set w := u - K.lam • z with hw
  have hpos : ∀ᶠ n in atTop, 0 < τ n := hτ.eventually self_mem_nhdsWithin
  have hball : ∀ᶠ n in atTop, x + τ n • u ∈ ball x K.δ₀ :=
    (hτ.eventually (K.eventually_mem_ball ‖u‖)).mono fun n h ↦ h u le_rfl
  have hwn : Tendsto (fun n ↦ K.Ps (τ n) u) atTop (𝓝 w) := by
    have h1 : Tendsto (fun n ↦ u - K.lam • K.Gs (τ n) u) atTop (𝓝 w) :=
      tendsto_const_nhds.sub (hz.const_smul K.lam)
    refine h1.congr' ?_
    filter_upwards [hpos] with n hn
    rw [K.Ps_eq hn.ne']
  set r : ℕ → ℝ := fun n ↦ K.rs (τ n) u with hr
  set Lr := liminf (fun n ↦ (r n : EReal)) atTop with hLr
  -- the lower limit bounds `d²f(w)` from above
  have hle : secondSubderivative f x 0 w ≤ Lr := by
    have hg : Tendsto (fun n ↦ ((τ n, K.Ps (τ n) u) : ℝ × E)) atTop (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
      hτ.prodMk hwn
    refine (secondSubderivative_le_liminf hg).trans (le_of_eq (liminf_congr ?_))
    filter_upwards [hpos, hball] with n hn hnb
    exact K.secondDifferenceQuotient_Ps hn (K.hball hnb)
  -- the recovery sequences of twice epi-differentiability bound it from below
  have hup : ∀ w' (b : ℝ), secondSubderivative f x 0 w' = b →
      Lr ≤ ((b - 2 * ⟪z, w' - w⟫_ℝ + K.mu * ‖w' - w‖ ^ 2 : ℝ) : EReal) := by
    intro w' b hb
    have hmem : (w', b) ∈ epigraph (secondSubderivative f x 0) := by
      change secondSubderivative f x 0 w' ≤ (b : EReal); rw [hb]
    have hin := (twiceEpiDifferentiableAt_iff_subset.1 hte).2.2 hmem
    have hseq := innerSetLimitAlong_subset_innerSetLimit_comp
      (C := fun τ ↦ epigraph (secondDifferenceQuotient f x 0 τ)) hτ hin
    obtain ⟨y, hyC, hyl⟩ := mem_innerSetLimit_iff_exists_seq.1 hseq
    have hB : Tendsto (fun n ↦ (y n).2 - 2 * ⟪K.Gs (τ n) u, (y n).1 - K.Ps (τ n) u⟫_ℝ +
        K.mu * ‖(y n).1 - K.Ps (τ n) u‖ ^ 2) atTop
        (𝓝 (b - 2 * ⟪z, w' - w⟫_ℝ + K.mu * ‖w' - w‖ ^ 2)) := by
      have h1 : Tendsto (fun n ↦ (y n).1) atTop (𝓝 w') := (continuous_fst.tendsto _).comp hyl
      have h2 : Tendsto (fun n ↦ (y n).2) atTop (𝓝 b) := (continuous_snd.tendsto _).comp hyl
      exact (h2.sub (tendsto_const_nhds.mul (hz.inner (h1.sub hwn)))).add
        (tendsto_const_nhds.mul ((h1.sub hwn).norm.pow 2))
    have hB' := (continuous_coe_real_ereal.tendsto _).comp hB
    rw [← hB'.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [hyC, hpos, hball] with n hyn hn hnb
    have h1 := K.le_secondDifferenceQuotient hn hnb (y n).1
    have h2 : secondDifferenceQuotient f x 0 (τ n) (y n).1 ≤ ((y n).2 : EReal) := hyn
    have h3 := h1.trans h2
    rw [EReal.coe_le_coe_iff] at h3
    simp only [Function.comp_apply, hr, EReal.coe_le_coe_iff]
    linarith
  -- finiteness of `d²f(w)`
  have hfin_top : secondSubderivative f x 0 w ≠ ⊤ := by
    have h := hle.trans (hup 0 0 (by rw [K.secondSubderivative_zero]; rfl))
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) h
  set a := (secondSubderivative f x 0 w).toReal with ha
  have haeq : secondSubderivative f x 0 w = a :=
    (EReal.coe_toReal hfin_top (K.secondSubderivative_ne_bot w)).symm
  refine ⟨a, haeq, fun w' ↦ ?_⟩
  rcases ereal_trichotomy (secondSubderivative f x 0 w') with h' | h' | ⟨b, hb⟩
  · exact absurd h' (K.secondSubderivative_ne_bot w')
  · rw [h']; exact le_top
  · rw [hb, EReal.coe_le_coe_iff]
    have h := (haeq ▸ hle).trans (hup w' b hb)
    rw [EReal.coe_le_coe_iff] at h
    linarith

/-- **Theorem 13.40**, the direction from twice epi-differentiability: the quotients `Gτ(u)`
converge for every `u`. -/
theorem tendsto_Gs_of_twiceEpi (hte : TwiceEpiDifferentiableAt f x 0) (u : E) :
    ∃ z, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 z) := by
  have hbd : ∀ {τ : ℕ → ℝ}, Tendsto τ atTop (𝓝[>] 0) →
      ∀ᶠ n in atTop, K.Gs (τ n) u ∈ closedBall (0 : E) (3 / K.lam * ‖u‖) := by
    intro τ hτ
    filter_upwards [hτ.eventually self_mem_nhdsWithin, hτ.eventually (K.eventually_mem_U ‖u‖)]
      with n hn hnU
    have h := K.Gs_lip hn (hnU u le_rfl) (hnU 0 (by simp))
    rw [K.Gs_zero, sub_zero, sub_zero] at h
    rwa [mem_closedBall, dist_zero_right]
  -- a limit point along one sequence
  have hseq : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n ↦ mem_Ioi.2 (by positivity)⟩
  obtain ⟨z, -, φ, hφ, hφz⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall
    (hbd hseq).frequently
  have hz : K.LimitChar u z :=
    K.limitChar_of_tendsto hte (hseq.comp hφ.tendsto_atTop) hφz
  refine ⟨z, tendsto_of_subseq_tendsto fun ns hns ↦ ?_⟩
  obtain ⟨z', -, ψ, hψ, hψz⟩ := tendsto_subseq_of_frequently_bounded isBounded_closedBall
    (hbd hns).frequently
  have hz' : K.LimitChar u z' := K.limitChar_of_tendsto hte (hns.comp hψ.tendsto_atTop) hψz
  rw [K.limitChar_unique hz hz'] at *
  exact ⟨ψ, hψz⟩

/-! ### Convergence of `Gτ` gives twice epi-differentiability and the derivative formula -/

omit [FiniteDimensional ℝ E] in
theorem norm_Gs_le {τ : ℝ} (hτ : 0 < τ) {u : E} (hu : x + τ • u ∈ proxRange f x ε K.lam) :
    ‖K.Gs τ u‖ ≤ 3 / K.lam * ‖u‖ := by
  have h0 : x + τ • (0 : E) ∈ proxRange f x ε K.lam := by
    simpa using K.hball (mem_ball_self K.hδ₀)
  have h := K.Gs_lip hτ hu h0
  rwa [K.Gs_zero, sub_zero, sub_zero] at h

omit [FiniteDimensional ℝ E] in
theorem continuousOn_inner_Gs {τ : ℝ} (hτ : 0 < τ) {u : E}
    (hu : ∀ s ∈ Icc (0 : ℝ) 1, x + τ • (s • u) ∈ proxRange f x ε K.lam) :
    ContinuousOn (fun s : ℝ ↦ ⟪K.Gs τ (s • u), u⟫_ℝ) (Icc 0 1) := by
  have hlam := K.hlam
  refine (LipschitzOnWith.of_dist_le_mul
    (K := ⟨3 / K.lam * ‖u‖ ^ 2, by positivity⟩) fun a ha b hb ↦ ?_).continuousOn
  rw [Real.dist_eq, ← inner_sub_left, NNReal.coe_mk, Real.dist_eq]
  have h1 := K.Gs_lip hτ (hu a ha) (hu b hb)
  rw [← sub_smul, norm_smul, Real.norm_eq_abs] at h1
  calc |⟪K.Gs τ (a • u) - K.Gs τ (b • u), u⟫_ℝ| ≤ ‖K.Gs τ (a • u) - K.Gs τ (b • u)‖ * ‖u‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ 3 / K.lam * (|a - b| * ‖u‖) * ‖u‖ := by gcongr
    _ = 3 / K.lam * ‖u‖ ^ 2 * |a - b| := by ring

omit [FiniteDimensional ℝ E] in
/-- `kτ(u) = ∫₀¹ ⟪Gτ(su), u⟫ ds` when the segment `[x̄, x̄ + τu]` lies in `U`. -/
theorem ks_eq_integral {τ : ℝ} (hτ : 0 < τ) {u : E}
    (hu : ∀ s ∈ Icc (0 : ℝ) 1, x + τ • (s • u) ∈ proxRange f x ε K.lam) :
    K.ks τ u = ∫ s in (0 : ℝ)..1, ⟪K.Gs τ (s • u), u⟫_ℝ := by
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ K.ks τ (s • u)) ⟪K.Gs τ (s • u), u⟫_ℝ s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 := K.ks_hasFDerivAt hτ (hu s hs)
    have h2 : HasDerivAt (fun s : ℝ ↦ s • u) u s := by
      simpa using (hasDerivAt_id s).smul_const u
    have h3 := h1.comp_hasDerivAt s h2
    simpa using h3
  have hcont := K.continuousOn_inner_Gs hτ hu
  rw [← uIcc_of_le zero_le_one] at hcont
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp [K.ks_zero]

/-- The candidate value `η(u) = 2∫₀¹ ⟪G₀(su), u⟫ ds - λ‖G₀(u)‖²` of `d²f(x̄ | 0)` at `w₀(u)`. -/
noncomputable def eta (G₀ : E → E) (u : E) : ℝ :=
  2 * (∫ s in (0 : ℝ)..1, ⟪G₀ (s • u), u⟫_ℝ) - K.lam * ‖G₀ u‖ ^ 2

/-- The limit `w₀(u) = u - λG₀(u)` of `Pτ(u)`. -/
noncomputable def w0 (G₀ : E → E) (u : E) : E := u - K.lam • G₀ u

section Convergent

variable {G₀ : E → E}

omit [FiniteDimensional ℝ E] in
theorem tendsto_ks (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (u : E) :
    Tendsto (fun τ ↦ K.ks τ u) (𝓝[>] 0) (𝓝 (∫ s in (0 : ℝ)..1, ⟪G₀ (s • u), u⟫_ℝ)) := by
  have hlam := K.hlam
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ ∧
      ∀ s ∈ Icc (0 : ℝ) 1, x + τ • (s • u) ∈ proxRange f x ε K.lam := by
    filter_upwards [self_mem_nhdsWithin, K.eventually_mem_U ‖u‖] with τ hτ hU
    refine ⟨hτ, fun s hs ↦ hU _ ?_⟩
    rw [norm_smul, Real.norm_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg u) hs.2
  have hint : Tendsto (fun τ ↦ ∫ s in (0 : ℝ)..1, ⟪K.Gs τ (s • u), u⟫_ℝ) (𝓝[>] 0)
      (𝓝 (∫ s in (0 : ℝ)..1, ⟪G₀ (s • u), u⟫_ℝ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ 3 / K.lam * ‖u‖ ^ 2) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hev] with τ ⟨hτ, hU⟩
      rw [uIoc_of_le zero_le_one]
      exact ((K.continuousOn_inner_Gs hτ hU).mono Ioc_subset_Icc_self).aestronglyMeasurable
        measurableSet_Ioc
    · filter_upwards [hev] with τ ⟨hτ, hU⟩
      refine Eventually.of_forall fun s hs ↦ ?_
      rw [uIoc_of_le zero_le_one] at hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
      have hsu : ‖s • u‖ ≤ ‖u‖ := by
        rw [norm_smul, Real.norm_of_nonneg hs'.1]; exact mul_le_of_le_one_left (norm_nonneg u) hs'.2
      rw [Real.norm_eq_abs]
      calc |⟪K.Gs τ (s • u), u⟫_ℝ| ≤ ‖K.Gs τ (s • u)‖ * ‖u‖ := abs_real_inner_le_norm _ _
        _ ≤ 3 / K.lam * ‖s • u‖ * ‖u‖ := by gcongr; exact K.norm_Gs_le hτ (hU s hs')
        _ ≤ 3 / K.lam * ‖u‖ * ‖u‖ := by gcongr
        _ = 3 / K.lam * ‖u‖ ^ 2 := by ring
    · exact Eventually.of_forall fun s _ ↦ (hG₀ (s • u)).inner tendsto_const_nhds
  refine hint.congr' ?_
  filter_upwards [hev] with τ ⟨hτ, hU⟩
  exact (K.ks_eq_integral hτ hU).symm

omit [FiniteDimensional ℝ E] in
theorem tendsto_rs (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (u : E) :
    Tendsto (fun τ ↦ K.rs τ u) (𝓝[>] 0) (𝓝 (K.eta G₀ u)) :=
  ((K.tendsto_ks hG₀ u).const_mul 2).sub (((hG₀ u).norm.pow 2).const_mul K.lam)

omit [FiniteDimensional ℝ E] in
theorem tendsto_Ps (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (u : E) :
    Tendsto (fun τ ↦ K.Ps τ u) (𝓝[>] 0) (𝓝 (K.w0 G₀ u)) := by
  have h1 : Tendsto (fun τ ↦ u - K.lam • K.Gs τ u) (𝓝[>] 0) (𝓝 (K.w0 G₀ u)) :=
    tendsto_const_nhds.sub ((hG₀ u).const_smul K.lam)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  rw [K.Ps_eq (ne_of_gt hτ)]

omit [FiniteDimensional ℝ E] in
/-- Every `(w₀(u), G₀(u))` gives an exact quadratic minorant of `d²f(x̄ | 0)`. -/
theorem le_secondSubderivative_of_tendsto
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (u w' : E) :
    ((K.eta G₀ u + 2 * ⟪G₀ u, w' - K.w0 G₀ u⟫_ℝ - K.mu * ‖w' - K.w0 G₀ u‖ ^ 2 : ℝ) : EReal) ≤
      secondSubderivative f x 0 w' := by
  refine coe_le_secondSubderivative_of_eventually (ψ := fun p ↦ K.rs p.1 u +
    2 * ⟪K.Gs p.1 u, p.2 - K.Ps p.1 u⟫_ℝ - K.mu * ‖p.2 - K.Ps p.1 u‖ ^ 2) ?_ ?_
  · have hb := K.eventually_mem_ball ‖u‖
    filter_upwards [prod_mem_prod (inter_mem self_mem_nhdsWithin hb) univ_mem] with p hp
    exact K.le_secondDifferenceQuotient hp.1.1 (hp.1.2 u le_rfl) p.2
  · have h1 := (K.tendsto_rs hG₀ u).comp (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w'))
    have h2 := (hG₀ u).comp (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w'))
    have h3 := (K.tendsto_Ps hG₀ u).comp (tendsto_fst (f := 𝓝[>] (0 : ℝ)) (g := 𝓝 w'))
    have h4 : Tendsto (fun p : ℝ × E ↦ p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w') (𝓝 w') := tendsto_snd
    exact (h1.add (tendsto_const_nhds.mul (h2.inner (h4.sub h3)))).sub
      (tendsto_const_nhds.mul ((h4.sub h3).norm.pow 2))

omit [FiniteDimensional ℝ E] in
theorem secondSubderivative_w0 (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u)))
    (u : E) : secondSubderivative f x 0 (K.w0 G₀ u) = K.eta G₀ u := by
  apply le_antisymm
  · have hg : Tendsto (fun τ ↦ ((τ, K.Ps τ u) : ℝ × E)) (𝓝[>] (0 : ℝ))
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 (K.w0 G₀ u)) := tendsto_id.prodMk (K.tendsto_Ps hG₀ u)
    refine (secondSubderivative_le_liminf hg).trans (le_of_eq ?_)
    have h1 : Tendsto (fun τ ↦ (K.rs τ u : EReal)) (𝓝[>] 0) (𝓝 (K.eta G₀ u : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp (K.tendsto_rs hG₀ u)
    rw [← h1.liminf_eq]
    refine liminf_congr ?_
    filter_upwards [self_mem_nhdsWithin, K.eventually_mem_U ‖u‖] with τ hτ hU
    exact K.secondDifferenceQuotient_Ps hτ (hU u le_rfl)
  · simpa using K.le_secondSubderivative_of_tendsto hG₀ u (K.w0 G₀ u)

/-- The affine minorant `aff_u(w) = η(u)/2 + μ/2‖w₀(u)‖² + ⟪G₀(u) + μw₀(u), w - w₀(u)⟫` of
`½d²f(x̄ | 0) + μ/2‖·‖²`, exact at `w₀(u)`. -/
noncomputable def aff (G₀ : E → E) (u w : E) : ℝ :=
  K.eta G₀ u / 2 + K.mu / 2 * ‖K.w0 G₀ u‖ ^ 2 + ⟪G₀ u + K.mu • K.w0 G₀ u, w - K.w0 G₀ u⟫_ℝ

/-- The convex function `Φ̃ = sup_u aff_u`. -/
noncomputable def convexMinorant (G₀ : E → E) (w : E) : EReal := ⨆ u, (K.aff G₀ u w : EReal)

/-- The relation `{(w₀(u), G₀(u) + μw₀(u))}`, which will be `∂Φ̃`. -/
def slopeMap (G₀ : E → E) (w : E) : Set E :=
  {v | ∃ u, w = K.w0 G₀ u ∧ v = G₀ u + K.mu • K.w0 G₀ u}

omit [FiniteDimensional ℝ E] in
theorem aff_le (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (u w : E) :
    (K.aff G₀ u w : EReal) ≤ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w +
      ((K.mu / 2 * ‖w‖ ^ 2 : ℝ) : EReal) := by
  have h := K.le_secondSubderivative_of_tendsto hG₀ u w
  have h2 := mul_le_mul_of_nonneg_left h (show (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) by
    exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2))
  refine le_trans (le_of_eq ?_) (add_le_add h2 le_rfl)
  rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  have hn := norm_add_sq_real (w - K.w0 G₀ u) (K.w0 G₀ u)
  rw [sub_add_cancel, real_inner_comm (K.w0 G₀ u) (w - K.w0 G₀ u)] at hn
  simp only [aff, inner_add_left, real_inner_smul_left]
  rw [hn]
  ring

omit [FiniteDimensional ℝ E] in
theorem convexMinorant_le (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (w : E) :
    K.convexMinorant G₀ w ≤ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w +
      ((K.mu / 2 * ‖w‖ ^ 2 : ℝ) : EReal) :=
  iSup_le fun u ↦ K.aff_le hG₀ u w

omit [FiniteDimensional ℝ E] in
theorem convexMinorant_w0 (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (u : E) :
    K.convexMinorant G₀ (K.w0 G₀ u) =
      ((K.eta G₀ u / 2 + K.mu / 2 * ‖K.w0 G₀ u‖ ^ 2 : ℝ) : EReal) := by
  apply le_antisymm
  · refine (K.convexMinorant_le hG₀ _).trans (le_of_eq ?_)
    rw [K.secondSubderivative_w0 hG₀, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring
  · refine le_trans (le_of_eq ?_) (le_iSup (fun u' ↦ (K.aff G₀ u' (K.w0 G₀ u) : EReal)) u)
    simp [aff]

omit [FiniteDimensional ℝ E] in
theorem convex_epigraph_convexMinorant : Convex ℝ (epigraph (K.convexMinorant G₀)) := by
  intro p hp q hq a b ha hb hab
  change K.convexMinorant G₀ (a • p + b • q).1 ≤ (((a • p + b • q).2 : ℝ) : EReal)
  refine iSup_le fun u ↦ ?_
  have h1 : (K.aff G₀ u p.1 : EReal) ≤ (p.2 : EReal) :=
    (le_iSup (fun u ↦ (K.aff G₀ u p.1 : EReal)) u).trans hp
  have h2 : (K.aff G₀ u q.1 : EReal) ≤ (q.2 : EReal) :=
    (le_iSup (fun u ↦ (K.aff G₀ u q.1 : EReal)) u).trans hq
  rw [EReal.coe_le_coe_iff] at h1 h2 ⊢
  obtain rfl : b = 1 - a := by linarith
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have e : a • p.1 + (1 - a) • q.1 - K.w0 G₀ u =
      a • (p.1 - K.w0 G₀ u) + (1 - a) • (q.1 - K.w0 G₀ u) := by module
  simp only [aff] at h1 h2 ⊢
  rw [e, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

omit [FiniteDimensional ℝ E] in
theorem lowerSemicontinuous_convexMinorant : LowerSemicontinuous (K.convexMinorant G₀) :=
  lowerSemicontinuous_iSup fun _ ↦ (continuous_coe_real_ereal.comp
    (continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const)))
    ).lowerSemicontinuous

omit [FiniteDimensional ℝ E] in
theorem isProper_convexMinorant (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) :
    IsProper (K.convexMinorant G₀) :=
  ⟨⟨K.w0 G₀ 0, by rw [K.convexMinorant_w0 hG₀]; exact EReal.coe_lt_top _⟩,
    fun w ↦ lt_of_lt_of_le (EReal.bot_lt_coe (K.aff G₀ 0 w))
      (le_iSup (fun u ↦ (K.aff G₀ u w : EReal)) 0)⟩

theorem slopeMap_subset (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (w : E) :
    K.slopeMap G₀ w ⊆ subdifferential (K.convexMinorant G₀) w := by
  rintro v ⟨u, rfl, rfl⟩
  rw [mem_subdifferential_iff_of_convex K.convex_epigraph_convexMinorant
    (K.isProper_convexMinorant hG₀) (K.convexMinorant_w0 hG₀ u)]
  intro z
  exact le_iSup (fun u' ↦ (K.aff G₀ u' z : EReal)) u

/-- `slopeMap` is maximal monotone (Minty's criterion 12.12 with `λ' = λ/(1 - λμ)`). -/
theorem svMaximalMonotone_slopeMap
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) :
    SvMaximalMonotone (K.slopeMap G₀) := by
  have hmono : SvMonotone (K.slopeMap G₀) :=
    (svMonotone_subdifferential_of_convex (K.isProper_convexMinorant hG₀)
      K.convex_epigraph_convexMinorant).mono (K.slopeMap_subset hG₀)
  have hlm := K.hlammu
  have hlam := K.hlam
  set s := 1 - K.lam * K.mu with hs_def
  have hs : 0 < s := by linarith
  have hs0 : 1 - K.lam * K.mu ≠ 0 := ne_of_gt (by linarith)
  set lam' := K.lam / s with hlam'
  refine svMaximalMonotone_of_svDom_svResolvent hmono (lam := lam') (by positivity)
    (eq_univ_of_forall fun z ↦ ⟨K.w0 G₀ (s • z), mem_svResolvent.2
      ⟨G₀ (s • z) + K.mu • K.w0 G₀ (s • z), ⟨s • z, rfl, rfl⟩, ?_⟩⟩)
  have e1 : K.w0 G₀ (s • z) + lam' • (G₀ (s • z) + K.mu • K.w0 G₀ (s • z)) =
      ((1 + lam' * K.mu) * s) • z + (lam' - K.lam - lam' * K.mu * K.lam) • G₀ (s • z) := by
    simp only [w0]; module
  have c1 : (1 + lam' * K.mu) * s = 1 := by
    simp only [hlam', hs_def]; field_simp; ring
  have c2 : lam' - K.lam - lam' * K.mu * K.lam = 0 := by
    simp only [hlam', hs_def]; field_simp; ring
  rw [e1, c1, c2, one_smul, zero_smul, add_zero]

theorem subdifferential_convexMinorant
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) :
    subdifferential (K.convexMinorant G₀) = K.slopeMap G₀ :=
  (K.svMaximalMonotone_slopeMap hG₀).eq_of_subset
    (svMonotone_subdifferential_of_convex (K.isProper_convexMinorant hG₀)
      K.convex_epigraph_convexMinorant) (K.slopeMap_subset hG₀)

/-- Points `w₀(u)` approach every point of the domain of `Φ̃` with convergent values (8.10). -/
theorem exists_seq_w0 (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) {w : E}
    (hw : K.convexMinorant G₀ w < ⊤) :
    ∃ u : ℕ → E, Tendsto (fun n ↦ K.w0 G₀ (u n)) atTop (𝓝 w) ∧
      Tendsto (fun n ↦ K.convexMinorant G₀ (K.w0 G₀ (u n))) atTop
        (𝓝 (K.convexMinorant G₀ w)) := by
  have hp := K.isProper_convexMinorant hG₀
  have hne : K.convexMinorant G₀ w ≠ ⊥ := (hp.2 w).ne'
  have hl : IsLocallyLscAt (K.convexMinorant G₀) w :=
    isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ
      (K.lowerSemicontinuous_convexMinorant.lowerSemicontinuousOn univ) (mem_univ w) hne hw.ne
  obtain ⟨y, hy, hsub⟩ := exists_attentive_seq_regularSubdifferential_nonempty hl
    (EReal.coe_toReal hw.ne hne).symm
  have hu : ∀ n, ∃ u, y n = K.w0 G₀ u := by
    intro n
    obtain ⟨v, hv⟩ := (hsub n).2
    rw [K.subdifferential_convexMinorant hG₀] at hv
    obtain ⟨u, hu, -⟩ := hv
    exact ⟨u, hu⟩
  choose u hu using hu
  have hy' := tendsto_attentiveNhds_iff.1 hy
  refine ⟨u, ?_, ?_⟩
  · simpa only [← hu] using hy'.1
  · have h2 := hy'.2
    simp only [Function.comp_def, hu] at h2
    exact h2

/-- `½d²f(x̄ | 0) + μ/2‖·‖² = Φ̃`. -/
theorem half_secondSubderivative_add_eq
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) (w : E) :
    ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w + ((K.mu / 2 * ‖w‖ ^ 2 : ℝ) : EReal) =
      K.convexMinorant G₀ w := by
  refine le_antisymm ?_ (K.convexMinorant_le hG₀ w)
  rcases eq_or_lt_of_le (le_top : K.convexMinorant G₀ w ≤ ⊤) with htop | hlt
  · rw [htop]; exact le_top
  obtain ⟨u, hu1, hu2⟩ := K.exists_seq_w0 hG₀ hlt
  set c := (K.convexMinorant G₀ w).toReal with hc_def
  have hc : K.convexMinorant G₀ w = c :=
    (EReal.coe_toReal hlt.ne ((K.isProper_convexMinorant hG₀).2 w).ne').symm
  simp only [K.convexMinorant_w0 hG₀, hc] at hu2
  have hreal := EReal.tendsto_coe.1 hu2
  have heta : Tendsto (fun n ↦ K.eta G₀ (u n)) atTop (𝓝 (2 * (c - K.mu / 2 * ‖w‖ ^ 2))) := by
    have h1 := (hreal.sub ((hu1.norm.pow 2).const_mul (K.mu / 2))).const_mul 2
    refine h1.congr' (Eventually.of_forall fun n ↦ ?_)
    ring
  have hlsc :=
    lowerSemicontinuousAt_iff_le_liminf.1 (lowerSemicontinuous_secondSubderivative f x 0 w)
  have h2 : secondSubderivative f x 0 w ≤ ((2 * (c - K.mu / 2 * ‖w‖ ^ 2) : ℝ) : EReal) := by
    refine hlsc.trans ((liminf_le_liminf_of_le hu1).trans (le_of_eq ?_))
    have h3 : Tendsto (fun n ↦ secondSubderivative f x 0 (K.w0 G₀ (u n))) atTop
        (𝓝 ((2 * (c - K.mu / 2 * ‖w‖ ^ 2) : ℝ) : EReal)) := by
      simp only [K.secondSubderivative_w0 hG₀]
      exact (continuous_coe_real_ereal.tendsto _).comp heta
    exact h3.liminf_eq
  rw [hc]
  calc ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w + ((K.mu / 2 * ‖w‖ ^ 2 : ℝ) : EReal)
      ≤ ((1 / 2 : ℝ) : EReal) * ((2 * (c - K.mu / 2 * ‖w‖ ^ 2) : ℝ) : EReal) +
          ((K.mu / 2 * ‖w‖ ^ 2 : ℝ) : EReal) :=
        add_le_add (mul_le_mul_of_nonneg_left h2
          (by exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2))) le_rfl
    _ = (c : EReal) := by
        rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]; ring

omit [FiniteDimensional ℝ E] in
theorem mem_innerSetLimit_w0 (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u)))
    (u : E) (β : ℝ) (hβ : K.eta G₀ u ≤ β) :
    (K.w0 G₀ u, β) ∈ innerSetLimitAlong (𝓝[>] (0 : ℝ))
      (fun τ ↦ epigraph (secondDifferenceQuotient f x 0 τ)) := by
  intro V hV
  have hlim : Tendsto (fun τ ↦ ((K.Ps τ u, K.rs τ u + (β - K.eta G₀ u)) : E × ℝ)) (𝓝[>] 0)
      (𝓝 (K.w0 G₀ u, β)) := by
    have h := (K.tendsto_Ps hG₀ u).prodMk_nhds ((K.tendsto_rs hG₀ u).add_const (β - K.eta G₀ u))
    convert h using 3
    ring
  filter_upwards [hlim.eventually hV, self_mem_nhdsWithin, K.eventually_mem_U ‖u‖]
    with τ hτV hτ hU
  refine ⟨_, ?_, hτV⟩
  change secondDifferenceQuotient f x 0 τ (K.Ps τ u) ≤ ((K.rs τ u + (β - K.eta G₀ u) : ℝ) : EReal)
  rw [K.secondDifferenceQuotient_Ps hτ (hU u le_rfl), EReal.coe_le_coe_iff]
  linarith

/-- **Theorem 13.40**, the direction toward twice epi-differentiability. -/
theorem twiceEpi_of_tendsto (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) :
    TwiceEpiDifferentiableAt f x 0 := by
  rw [twiceEpiDifferentiableAt_iff_subset]
  refine ⟨by rw [K.hfx]; exact EReal.coe_ne_bot _, by rw [K.hfx]; exact EReal.coe_ne_top _, ?_⟩
  rintro ⟨w, α⟩ hwα
  change secondSubderivative f x 0 w ≤ (α : EReal) at hwα
  have hfin : secondSubderivative f x 0 w ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top α) hwα
  set a := (secondSubderivative f x 0 w).toReal with ha_def
  have ha : secondSubderivative f x 0 w = a :=
    (EReal.coe_toReal hfin (K.secondSubderivative_ne_bot w)).symm
  have haα : a ≤ α := by rw [ha] at hwα; exact EReal.coe_le_coe_iff.1 hwα
  have hΦ : K.convexMinorant G₀ w = ((a / 2 + K.mu / 2 * ‖w‖ ^ 2 : ℝ) : EReal) := by
    rw [← K.half_secondSubderivative_add_eq hG₀, ha, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_eq_coe_iff]
    ring
  obtain ⟨u, hu1, hu2⟩ := K.exists_seq_w0 hG₀ (by rw [hΦ]; exact EReal.coe_lt_top _)
  simp only [K.convexMinorant_w0 hG₀, hΦ] at hu2
  have hreal := EReal.tendsto_coe.1 hu2
  have heta : Tendsto (fun n ↦ K.eta G₀ (u n)) atTop (𝓝 a) := by
    have h1 := (hreal.sub ((hu1.norm.pow 2).const_mul (K.mu / 2))).const_mul 2
    have h2 : 2 * (a / 2 + K.mu / 2 * ‖w‖ ^ 2 - K.mu / 2 * ‖w‖ ^ 2) = a := by ring
    rw [h2] at h1
    refine h1.congr' (Eventually.of_forall fun n ↦ ?_)
    ring
  have hpts : Tendsto (fun n ↦ ((K.w0 G₀ (u n), α + K.eta G₀ (u n) - a) : E × ℝ)) atTop
      (𝓝 (w, α)) := by
    have h := hu1.prodMk_nhds ((heta.const_add α).sub_const a)
    convert h using 3
    ring
  exact (isClosed_innerSetLimitAlong _ _).mem_of_tendsto hpts
    (Eventually.of_forall fun n ↦ K.mem_innerSetLimit_w0 hG₀ (u n) _ (by linarith))

theorem hasGradientAt_neg_half_mul_norm_sq (μ : ℝ) (y : E) :
    HasGradientAt (fun y ↦ -(μ / 2 * ‖y‖ ^ 2)) (-(μ • y)) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (((hasStrictFDerivAt_norm_sq y).hasFDerivAt).const_mul (μ / 2)).neg
  convert h using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply]
  ring

/-- The subgradients of `h = ½d²f(x̄ | 0)` are described by `G₀`. -/
theorem mem_subdifferential_half_iff
    (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) {w z : E} :
    z ∈ subdifferential (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w) w ↔
      G₀ (w + K.lam • z) = z := by
  have hfun : (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w) =
      fun w ↦ K.convexMinorant G₀ w + ((-(K.mu / 2 * ‖w‖ ^ 2) : ℝ) : EReal) := by
    funext w
    rw [← K.half_secondSubderivative_add_eq hG₀ w, add_assoc, ← EReal.coe_add, add_neg_cancel,
      EReal.coe_zero, add_zero]
  have hiff2 : G₀ (w + K.lam • z) = z ↔ ∃ u, w = K.w0 G₀ u ∧ z = G₀ u := by
    constructor
    · intro h
      refine ⟨w + K.lam • z, ?_, h.symm⟩
      simp only [w0, h, add_sub_cancel_right]
    · rintro ⟨u, rfl, rfl⟩
      simp only [w0, sub_add_cancel]
  rw [hiff2]
  rcases eq_or_lt_of_le (le_top : K.convexMinorant G₀ w ≤ ⊤) with htop | hlt
  · constructor
    · intro hz
      exfalso
      obtain ⟨⟨c, hc⟩, -⟩ := mem_subdifferential_iff_exists_seq.1 hz
      have hw := congrFun hfun w
      simp only at hw
      rw [hw, htop, EReal.top_add_coe] at hc
      exact EReal.coe_ne_top c hc.symm
    · rintro ⟨u, rfl, -⟩
      rw [K.convexMinorant_w0 hG₀] at htop
      exact absurd htop (EReal.coe_ne_top _)
  · have hne := ((K.isProper_convexMinorant hG₀).2 w).ne'
    have hc : K.convexMinorant G₀ w = ((K.convexMinorant G₀ w).toReal : EReal) :=
      (EReal.coe_toReal hlt.ne hne).symm
    have hg : ∀ y ∈ ball w 1, HasGradientAt (fun y ↦ -(K.mu / 2 * ‖y‖ ^ 2)) (-(K.mu • y)) y :=
      fun y _ ↦ hasGradientAt_neg_half_mul_norm_sq K.mu y
    have hL : ∀ y ∈ ball w 1, ∀ y' ∈ ball w 1,
        ‖-(K.mu • y) - -(K.mu • y')‖ ≤ K.mu * ‖y - y'‖ := by
      intro y _ y' _
      rw [neg_sub_neg, ← smul_sub, norm_smul, Real.norm_of_nonneg K.hmu.le, norm_sub_rev]
    rw [hfun, subdifferential_add_lipschitz_gradient K.hmu.le hg hL (mem_ball_self one_pos) hc,
      K.subdifferential_convexMinorant hG₀]
    constructor
    · rintro ⟨v, ⟨u, rfl, rfl⟩, rfl⟩
      exact ⟨u, rfl, add_neg_cancel_right _ _⟩
    · rintro ⟨u, rfl, rfl⟩
      exact ⟨G₀ u + K.mu • K.w0 G₀ u, ⟨u, rfl, rfl⟩, add_neg_cancel_right _ _⟩

/-- **Theorem 13.40**, formula 13(31) in the normalized case: `DT(x̄ | 0) = ∂h`,
`h = ½d²f(x̄ | 0)`. -/
theorem graphicalDerivative_eq (hG₀ : ∀ u, Tendsto (fun τ ↦ K.Gs τ u) (𝓝[>] 0) (𝓝 (G₀ u))) :
    graphicalDerivative (proxLocalization f x ε) x 0 =
      subdifferential (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w) := by
  funext w
  ext z
  have h := congrArg (fun S : Set (E × E) ↦ (w, z) ∈ S) (K.svGraph_graphicalDerivative hG₀)
  simp only [eq_iff_iff] at h
  rw [K.mem_subdifferential_half_iff hG₀]
  exact h

end Convergent

include K in
omit [FiniteDimensional ℝ E] in
/-- `h = ½d²f(x̄ | 0)` is proper. -/
theorem isProper_half : IsProper (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w) := by
  refine ⟨⟨0, ?_⟩, fun w ↦ ?_⟩
  · change ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 0 < ⊤
    rw [K.secondSubderivative_zero, mul_zero]; exact EReal.zero_lt_top
  have h := K.neg_le_secondSubderivative w
  have h2 := mul_le_mul_of_nonneg_left h (show (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) by
    exact_mod_cast (by norm_num : (0 : ℝ) ≤ 1 / 2))
  rw [← EReal.coe_mul] at h2
  exact lt_of_lt_of_le (EReal.bot_lt_coe _) h2

include K in
/-- **Theorem 13.40**, normalized core: for the localization `T` of `∂f` from Proposition 13.37,
`T` is proto-differentiable at `x̄` for `0` if and only if `f` is twice epi-differentiable at `x̄`
for `0`, and then `DT(x̄ | 0) = ∂h` for `h = ½d²f(x̄ | 0)`. -/
theorem core_equivalence :
    (IsProtoDifferentiableAt (proxLocalization f x ε) x 0 ↔ TwiceEpiDifferentiableAt f x 0) ∧
    (IsProtoDifferentiableAt (proxLocalization f x ε) x 0 →
      graphicalDerivative (proxLocalization f x ε) x 0 =
        subdifferential (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x 0 w)) := by
  refine ⟨⟨fun h ↦ ?_, fun h ↦ K.isProtoDifferentiableAt_iff.2 (K.tendsto_Gs_of_twiceEpi h)⟩,
    fun h ↦ ?_⟩
  · choose G₀ hG₀ using K.isProtoDifferentiableAt_iff.1 h
    exact K.twiceEpi_of_tendsto hG₀
  · choose G₀ hG₀ using K.isProtoDifferentiableAt_iff.1 h
    exact K.graphicalDerivative_eq hG₀

end ProxCore

/-! ### Localization of proto-differentiability -/

section Localization

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Set limits only see the sets on bounded regions, eventually. -/
theorem setLimits_congr_of_eventually_inter_ball {ι X : Type*} [PseudoMetricSpace X]
    {l : Filter ι} {C C' : ι → Set X} (p₀ : X)
    (h : ∀ R > 0, ∀ᶠ i in l, C i ∩ ball p₀ R = C' i ∩ ball p₀ R) :
    innerSetLimitAlong l C = innerSetLimitAlong l C' ∧
      outerSetLimitAlong l C = outerSetLimitAlong l C' := by
  have key : ∀ {A B : ι → Set X}, (∀ R > 0, ∀ᶠ i in l, A i ∩ ball p₀ R = B i ∩ ball p₀ R) →
      innerSetLimitAlong l A ⊆ innerSetLimitAlong l B ∧
        outerSetLimitAlong l A ⊆ outerSetLimitAlong l B := by
    intro A B hAB
    have hV : ∀ q : X, ∀ V ∈ 𝓝 q, V ∩ ball p₀ (dist q p₀ + 1) ∈ 𝓝 q := fun q V hV ↦
      inter_mem hV (isOpen_ball.mem_nhds (by rw [mem_ball]; linarith))
    refine ⟨fun q hq V hVq ↦ ?_, fun q hq V hVq ↦ ?_⟩
    · filter_upwards [hq _ (hV q V hVq), hAB (dist q p₀ + 1) (by positivity)] with i hi hiAB
      obtain ⟨y, hyA, hyV, hyb⟩ := hi
      have : y ∈ B i ∩ ball p₀ (dist q p₀ + 1) := hiAB ▸ ⟨hyA, hyb⟩
      exact ⟨y, this.1, hyV⟩
    · refine ((hq _ (hV q V hVq)).and_eventually (hAB (dist q p₀ + 1) (by positivity))).mono ?_
      rintro i ⟨⟨y, hyA, hyV, hyb⟩, hiAB⟩
      have : y ∈ B i ∩ ball p₀ (dist q p₀ + 1) := hiAB ▸ ⟨hyA, hyb⟩
      exact ⟨y, this.1, hyV⟩
  have h' : ∀ R > 0, ∀ᶠ i in l, C' i ∩ ball p₀ R = C i ∩ ball p₀ R := fun R hR ↦
    (h R hR).mono fun _ hi ↦ hi.symm
  exact ⟨Subset.antisymm (key h).1 (key h').1, Subset.antisymm (key h).2 (key h').2⟩

omit [FiniteDimensional ℝ E] in
/-- A mapping whose graph near `(x̄, v̄)` is the translate by `(0, v̄)` of the graph of `T` near
`(x̄, 0)` has the same proto-differentiability and graphical derivative as `T`. -/
theorem isProtoDifferentiableAt_iff_of_eventually {S T : E → Set E} {x v : E}
    (h : ∀ᶠ p in 𝓝 (x, v), p.2 ∈ S p.1 ↔ p.2 - v ∈ T p.1) :
    (IsProtoDifferentiableAt S x v ↔ IsProtoDifferentiableAt T x 0) ∧
      graphicalDerivative S x v = graphicalDerivative T x 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 h
  have hR : ∀ R > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      svGraph (mappingDifferenceQuotient S x v τ) ∩ ball (0 : E × E) R =
        svGraph (mappingDifferenceQuotient T x 0 τ) ∩ ball (0 : E × E) R := by
    intro R hRpos
    filter_upwards [Ioo_mem_nhdsGT (show 0 < δ / R by positivity)] with τ ⟨hτ0, hτ1⟩
    ext ⟨w, z⟩
    simp only [mem_inter_iff, and_congr_left_iff]
    intro hwz
    rw [mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff] at hwz
    change z ∈ mappingDifferenceQuotient S x v τ w ↔ z ∈ mappingDifferenceQuotient T x 0 τ w
    rw [mem_mappingDifferenceQuotient_iff hτ0.ne', mem_mappingDifferenceQuotient_iff hτ0.ne']
    have hmem : (x + τ • w, v + τ • z) ∈ ball (x, v) δ := by
      rw [lt_div_iff₀ hRpos] at hτ1
      rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm, add_sub_cancel_left,
        add_sub_cancel_left, norm_smul, norm_smul, Real.norm_of_nonneg hτ0.le]
      constructor <;> nlinarith [norm_nonneg w, norm_nonneg z]
    have := hball hmem
    simp only [mem_setOf_eq, add_sub_cancel_left] at this
    rw [this, zero_add]
  obtain ⟨hin, hout⟩ := setLimits_congr_of_eventually_inter_ball (0 : E × E) hR
  have hD : svGraph (graphicalDerivative S x v) = svGraph (graphicalDerivative T x 0) := by
    rw [svGraph_graphicalDerivative_eq_outerLimit, svGraph_graphicalDerivative_eq_outerLimit, hout]
  refine ⟨?_, ?_⟩
  · rw [IsProtoDifferentiableAt, IsProtoDifferentiableAt, PKConvergesAlong, PKConvergesAlong, hin,
      hout, hD]
  · funext y
    ext z
    exact Set.ext_iff.1 hD (y, z)

end Localization

/-! ### The tilt by `v̄` -/

section Tilt

variable {f : E → EReal} {x v : E} {c : ℝ}

omit [FiniteDimensional ℝ E] in
theorem secondDifferenceQuotient_add_neg_inner (hx : f x = c) (τ : ℝ) (w : E) :
    secondDifferenceQuotient (fun y ↦ f y + ((-⟪v, y⟫_ℝ : ℝ) : EReal)) x 0 τ w =
      secondDifferenceQuotient f x v τ w := by
  simp only [secondDifferenceQuotient, inner_zero_left, mul_zero, EReal.coe_zero, sub_zero, hx]
  congr 1
  rcases ereal_trichotomy (f (x + τ • w)) with h' | h' | ⟨r, hr⟩
  · rw [h', EReal.bot_add, EReal.bot_sub, EReal.bot_sub, EReal.bot_sub]
  · rw [h', EReal.top_add_coe, ← EReal.coe_add, EReal.top_sub_coe, EReal.top_sub_coe,
      EReal.top_sub_coe]
  · rw [hr, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub,
      EReal.coe_eq_coe_iff, inner_add_right, real_inner_smul_right]
    ring

omit [FiniteDimensional ℝ E] in
theorem secondSubderivative_add_neg_inner (hx : f x = c) :
    secondSubderivative (fun y ↦ f y + ((-⟪v, y⟫_ℝ : ℝ) : EReal)) x 0 =
      secondSubderivative f x v := by
  funext w
  simp only [secondSubderivative, secondDifferenceQuotient_add_neg_inner hx]

omit [FiniteDimensional ℝ E] in
theorem twiceEpiDifferentiableAt_add_neg_inner_iff (hx : f x = c) :
    TwiceEpiDifferentiableAt (fun y ↦ f y + ((-⟪v, y⟫_ℝ : ℝ) : EReal)) x 0 ↔
      TwiceEpiDifferentiableAt f x v := by
  have hq : (fun τ ↦ epigraph (secondDifferenceQuotient
      (fun y ↦ f y + ((-⟪v, y⟫_ℝ : ℝ) : EReal)) x 0 τ)) =
      fun τ ↦ epigraph (secondDifferenceQuotient f x v τ) := by
    funext τ
    congr 1
    funext w
    exact secondDifferenceQuotient_add_neg_inner hx τ w
  rw [TwiceEpiDifferentiableAt, TwiceEpiDifferentiableAt, hq, secondSubderivative_add_neg_inner hx]
  simp only [hx, ← EReal.coe_add, ne_eq, EReal.coe_ne_bot, not_false_eq_true, EReal.coe_ne_top,
    true_and]

end Tilt

/-! ### Theorem 13.40 -/

/-- The reduction behind Theorem 13.40: for `f` prox-regular at `x̄` for `v̄`, the function
`f₁ = f - ⟪v̄, ·⟫ + δ_B` (`B` a small closed ball around `x̄`) is prox-regular at `x̄` for `0` and
prox-bounded, has `d²f₁(x̄ | 0) = d²f(x̄ | v̄)` and the same twice epi-differentiability, and
carries the data `ProxCore f₁ x̄ ε` of Proposition 13.37; the localization `T` of `∂f₁` agrees,
after translation by `v̄`, with `∂f` near `(x̄, v̄)` under subdifferential continuity, and with
every sufficiently close `f`-attentive localization of `∂f`. -/
theorem IsProxRegularAt.exists_proxCore {f : E → EReal} {x v : E} (hf : IsProxRegularAt f x v) :
    ∃ (f₁ : E → EReal) (ε : ℝ) (_ : ProxCore f₁ x ε),
      secondSubderivative f₁ x 0 = secondSubderivative f x v ∧
      (TwiceEpiDifferentiableAt f₁ x 0 ↔ TwiceEpiDifferentiableAt f x v) ∧
      (IsSubdifferentiallyContinuousAt f x v → ∀ᶠ p in 𝓝 (x, v),
        p.2 ∈ subdifferential f p.1 ↔ p.2 - v ∈ proxLocalization f₁ x ε p.1) ∧
      ∃ ε₀ > 0, ∀ ε', 0 < ε' → ε' ≤ ε₀ → ∀ᶠ p in 𝓝 (x, v),
        p.2 ∈ attentiveLocalization f x v ε' p.1 ↔ p.2 - v ∈ proxLocalization f₁ x ε p.1 := by
  classical
  have hf' := hf
  obtain ⟨hlsc, hv, ε₁, hε₁, ρ, hρ, hprox⟩ := hf'
  set c := (f x).toReal with hcdef
  have hc : f x = (c : EReal) := (EReal.coe_toReal hlsc.2.1 hlsc.1).symm
  -- the normalized, prox-bounded modification `f₁` (as in 13.46)
  set f₀ : E → EReal := fun y ↦ f y + ((-⟪v, y⟫_ℝ : ℝ) : EReal) with hf₀
  set f₁ : E → EReal := fun y ↦ if y ∈ closedBall x ε₁ then f₀ y else ⊤ with hf₁
  have hball₁ : ∀ y ∈ ball x ε₁, f₁ =ᶠ[𝓝 y] f₀ := by
    intro y hy
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    simp only [hf₁, if_pos (ball_subset_closedBall hz)]
  have hpr₁ : IsProxRegularAt f₁ x 0 := hf.sub_inner.congr_nhds (hball₁ x (mem_ball_self hε₁))
  have hpb₁ : IsProxBounded f₁ := by
    refine isProxBounded_of_bddBelow ⟨c - ⟪v, x⟫_ℝ - ρ / 2 * ε₁ ^ 2, fun y ↦ ?_⟩
    by_cases hy : y ∈ closedBall x ε₁
    · simp only [hf₁, if_pos hy, hf₀]
      have h1 := hprox x v hv (by simpa using hε₁) (by simpa using hε₁)
        (by rw [hc, ← EReal.coe_add]; exact EReal.coe_lt_coe_iff.2 (by linarith)) y hy
      rw [hc, ← EReal.coe_add] at h1
      rcases ereal_trichotomy (f y) with hy' | hy' | ⟨r, hr⟩
      · rw [hy'] at h1; exact absurd (le_bot_iff.1 h1) (EReal.coe_ne_bot _)
      · rw [hy', EReal.top_add_coe]; exact le_top
      · rw [hr] at h1 ⊢
        rw [← EReal.coe_add, EReal.coe_le_coe_iff]
        rw [EReal.coe_le_coe_iff] at h1
        have hn : ‖y - x‖ ≤ ε₁ := by rw [← dist_eq_norm]; exact hy
        have hsq : ‖y - x‖ ^ 2 ≤ ε₁ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
        have hin : ⟪v, y - x⟫_ℝ = ⟪v, y⟫_ℝ - ⟪v, x⟫_ℝ := inner_sub_right _ _ _
        nlinarith
    · simp only [hf₁, if_neg hy]; exact le_top
  -- second-order objects of `f₁` and `f`
  have hloc : f₁ =ᶠ[𝓝 x] f₀ := hball₁ x (mem_ball_self hε₁)
  have hd2 : secondSubderivative f₁ x 0 = secondSubderivative f x v := by
    funext w
    rw [secondSubderivative_congr_nhds hloc 0 w, secondSubderivative_add_neg_inner hc]
  have hte : TwiceEpiDifferentiableAt f₁ x 0 ↔ TwiceEpiDifferentiableAt f x v := by
    rw [← twiceEpiDifferentiableAt_add_neg_inner_iff hc]
    exact ⟨fun h ↦ h.congr_nhds hloc.symm, fun h ↦ h.congr_nhds hloc⟩
  -- the core
  obtain ⟨ε, hε, lam₀, hlam₀, H⟩ := hpr₁.exists_proxEnvelopeModel hpb₁
  obtain ⟨K⟩ := ProxCore.nonempty hpr₁ hpb₁ hlam₀ H
  -- facts about `f₁` near `x̄`
  have hf₁val : ∀ y ∈ ball x ε₁, f₁ y = f y + ((-⟪v, y⟫_ℝ : ℝ) : EReal) := fun y hy ↦
    (hball₁ y hy).self_of_nhds
  have hsub₁ : ∀ y ∈ ball x ε₁, ∀ w, w ∈ subdifferential f₁ y ↔ w + v ∈ subdifferential f y := by
    intro y hy w
    rw [subdifferential_eq_of_eventuallyEq (hball₁ y hy)]
    exact mem_subdifferential_sub_inner_iff
  have hf₁x : f₁ x = ((c - ⟪v, x⟫_ℝ : ℝ) : EReal) := by
    rw [hf₁val x (mem_ball_self hε₁), hc, ← EReal.coe_add, sub_eq_add_neg]
  have hnear : ∀ δ > 0, ∀ᶠ p in 𝓝 (x, v), ‖p.1 - x‖ < δ ∧ ‖p.2 - v‖ < δ := by
    intro δ hδ
    filter_upwards [ball_mem_nhds (x, v) hδ] with p hp
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hp
    exact hp
  have hvev : ∀ η > 0, ∀ᶠ p in 𝓝 (x, v), |⟪v, p.1 - x⟫_ℝ| < η := by
    intro η hη
    have h : Tendsto (fun p : E × E ↦ ⟪v, p.1 - x⟫_ℝ) (𝓝 (x, v)) (𝓝 ⟪v, x - x⟫_ℝ) :=
      (continuous_const.inner (continuous_fst.sub continuous_const)).tendsto _
    rw [sub_self, inner_zero_right] at h
    filter_upwards [h.eventually (Metric.ball_mem_nhds 0 hη)] with p hp
    rwa [Real.dist_0_eq_abs] at hp
  refine ⟨f₁, ε, K, hd2, hte, fun hsc ↦ ?_, ?_⟩
  · -- `∂f` under subdifferential continuity
    obtain ⟨δ, hδ, hδf⟩ := hsc.exists_lt hc (by positivity : (0 : ℝ) < ε / 2)
    filter_upwards [hnear (min δ (min ε ε₁)) (by positivity), hvev (ε / 2) (by positivity)]
      with p ⟨hp1, hp2⟩ hpv
    obtain ⟨y, w⟩ := p
    simp only at hp1 hp2 hpv ⊢
    have hyb : y ∈ ball x ε₁ := by
      rw [mem_ball, dist_eq_norm]; linarith [min_le_right δ (min ε ε₁), min_le_right ε ε₁]
    constructor
    · intro hw
      refine ⟨(hsub₁ y hyb _).2 (by rw [sub_add_cancel]; exact hw), by
        linarith [min_le_right δ (min ε ε₁), min_le_left ε ε₁], ?_, by
        linarith [min_le_right δ (min ε ε₁), min_le_left ε ε₁]⟩
      have hfy := hδf y w hw (by linarith [min_le_left δ (min ε ε₁)])
        (by linarith [min_le_left δ (min ε ε₁)])
      rw [hf₁val y hyb, hf₁x]
      rcases ereal_trichotomy (f y) with h' | h' | ⟨r, hr⟩
      · rw [h', EReal.bot_add]; exact EReal.bot_lt_coe _
      · rw [h'] at hfy; exact absurd hfy (not_lt.2 le_top)
      · rw [hr] at hfy ⊢
        rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        rw [EReal.coe_lt_coe_iff] at hfy
        rw [inner_sub_right] at hpv
        linarith [abs_lt.1 hpv]
    · rintro ⟨hw, -, -, -⟩
      have := (hsub₁ y hyb _).1 hw
      rwa [sub_add_cancel] at this
  · -- attentive localizations
    have hlam := K.hlam
    set U := proxRange f₁ x ε K.lam
    have hxU : x ∈ U := K.hball (mem_ball_self K.hδ₀)
    have hUo : IsOpen U := K.hUo
    set φ : E → ℝ := fun u ↦ K.e u - K.lam / 2 * ‖K.G u‖ ^ 2 with hφ
    have hφval : ∀ u ∈ U, f₁ (K.P u) = (φ u : EReal) := fun u hu ↦ K.hval u hu
    have hGcont : ContinuousAt K.G x := by
      rw [Metric.continuousAt_iff]
      intro η hη
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo x hxU
      refine ⟨min r (η * K.lam / 6), by positivity, fun u hu ↦ ?_⟩
      have huU : u ∈ U := hrU (lt_of_lt_of_le hu (min_le_left _ _))
      have h1 := K.hGLip x hxU u huU
      rw [dist_eq_norm]
      have h2 : ‖u - x‖ < η * K.lam / 6 := by
        rw [← dist_eq_norm]; exact lt_of_lt_of_le hu (min_le_right _ _)
      calc ‖K.G u - K.G x‖ ≤ 3 / K.lam * ‖u - x‖ := h1
        _ ≤ 3 / K.lam * (η * K.lam / 6) := by gcongr
        _ = η / 2 := by field_simp; ring
        _ < η := by linarith
    have hφcont : ContinuousAt φ x :=
      (K.hderiv x hxU).continuousAt.sub (continuousAt_const.mul (hGcont.norm.pow 2))
    have hφx : φ x = c - ⟪v, x⟫_ℝ := by
      have h := hφval x hxU
      rw [K.hPx, hf₁x, EReal.coe_eq_coe_iff] at h
      exact h.symm
    have hucont : Tendsto (fun p : E × E ↦ p.1 + K.lam • (p.2 - v)) (𝓝 (x, v)) (𝓝 x) := by
      have h : Tendsto (fun p : E × E ↦ p.1 + K.lam • (p.2 - v)) (𝓝 (x, v))
          (𝓝 (x + K.lam • (v - v))) :=
        (continuous_fst.add (continuous_const.smul (continuous_snd.sub continuous_const))).tendsto _
      simpa using h
    refine ⟨min (ε / (2 * (‖v‖ + 1))) (min ε₁ ε), by positivity, fun ε' hε' hε'0 ↦ ?_⟩
    have hε'1 : ε' ≤ ε / (2 * (‖v‖ + 1)) := le_trans hε'0 (min_le_left _ _)
    have hε'2 : ε' ≤ ε₁ := le_trans hε'0 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hε'3 : ε' ≤ ε := le_trans hε'0 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hφev : ∀ᶠ p in 𝓝 (x, v), |φ (p.1 + K.lam • (p.2 - v)) - φ x| < ε' / 2 :=
      (hucont.eventually (Metric.continuousAt_iff'.1 hφcont (ε' / 2) (by positivity))).mono
        fun p hp ↦ by rw [← Real.dist_eq]; exact hp
    filter_upwards [hnear ε' hε', hucont.eventually (hUo.mem_nhds hxU), hφev,
      hvev (ε' / 2) (by positivity)] with p ⟨hp1, hp2⟩ hpU hpφ hpv
    obtain ⟨y, w⟩ := p
    simp only at hp1 hp2 hpU hpφ hpv ⊢
    have hyb : y ∈ ball x ε₁ := by rw [mem_ball, dist_eq_norm]; linarith
    constructor
    · rintro ⟨hw, -, hlow, hup, -⟩
      refine ⟨(hsub₁ y hyb _).2 (by rw [sub_add_cancel]; exact hw), by linarith, ?_,
        by linarith⟩
      rw [hf₁val y hyb, hf₁x]
      rw [hc] at hup
      rcases ereal_trichotomy (f y) with h' | h' | ⟨r, hr⟩
      · rw [h', EReal.bot_add]; exact EReal.bot_lt_coe _
      · rw [h'] at hup; exact absurd hup (not_lt.2 le_top)
      · rw [hr] at hup ⊢
        rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at hup
        have h1 : |⟪v, y - x⟫_ℝ| ≤ ‖v‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
        have h2 : ‖v‖ * ‖y - x‖ ≤ ‖v‖ * ε' := mul_le_mul_of_nonneg_left hp1.le (norm_nonneg _)
        have h3 : ε' * (2 * (‖v‖ + 1)) ≤ ε := by
          rw [le_div_iff₀ (by positivity)] at hε'1; exact hε'1
        rw [inner_sub_right] at h1
        nlinarith [abs_le.1 h1, norm_nonneg v]
    · intro hTm
      have hw : w - v ∈ subdifferential f₁ y := hTm.1
      have hw' : w ∈ subdifferential f y := by
        have := (hsub₁ y hyb _).1 hw
        rwa [sub_add_cancel] at this
      obtain ⟨-, hGu⟩ := (K.hgraph y (w - v)).1 hTm
      set u := y + K.lam • (w - v) with hu
      have hPu : K.P u = y := by
        have h2 : u - K.P u = K.lam • (w - v) := by
          have h := congrArg (fun t ↦ K.lam • t) hGu
          simp only [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul] at h
          exact h
        have : K.P u = u - (u - K.P u) := by abel
        rw [this, h2, hu]; abel
      have hf₁y : f₁ y = (φ u : EReal) := by
        have h := hφval u hpU
        rwa [hPu] at h
      rw [hf₁val y hyb] at hf₁y
      have hfy : f y = ((φ u + ⟪v, y⟫_ℝ : ℝ) : EReal) := by
        rcases ereal_trichotomy (f y) with h' | h' | ⟨r, hr⟩
        · rw [h', EReal.bot_add] at hf₁y; exact absurd hf₁y.symm (EReal.coe_ne_bot _)
        · rw [h', EReal.top_add_coe] at hf₁y; exact absurd hf₁y.symm (EReal.coe_ne_top _)
        · rw [hr, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hf₁y
          rw [hr, EReal.coe_eq_coe_iff]
          linarith
      rw [inner_sub_right] at hpv
      rw [hφx] at hpφ
      refine ⟨hw', hp1, ?_, ?_, hp2⟩
      · rw [hc, hfy, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
        linarith [abs_lt.1 hpφ, abs_lt.1 hpv]
      · rw [hc, hfy, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        linarith [abs_lt.1 hpφ, abs_lt.1 hpv]


/-- **Theorem 13.40** (proto-differentiability of subgradient mappings).  Let `f` be prox-regular at
`x̄` for `v̄ ∈ ∂f(x̄)` and let `h = ½d²f(x̄ | v̄)`.
* If `f` is subdifferentially continuous at `x̄` for `v̄`, then `∂f` is proto-differentiable at `x̄`
  for `v̄` if and only if `f` is twice epi-differentiable at `x̄` for `v̄`, and then
  `D(∂f)(x̄ | v̄) = ∂h` (formula 13(31)).
* In general, the same holds with `∂f` replaced by any sufficiently close `f`-attentive localization
  of `∂f` around `(x̄, v̄)` (`attentiveLocalization f x̄ v̄ ε`, `0 < ε ≤ ε₀`).
* `h` is proper. -/
theorem proto_differentiability_of_subgradient_mappings {f : E → EReal} {x v : E}
    (hf : IsProxRegularAt f x v) :
    (IsSubdifferentiallyContinuousAt f x v →
      (IsProtoDifferentiableAt (subdifferential f) x v ↔ TwiceEpiDifferentiableAt f x v) ∧
      (TwiceEpiDifferentiableAt f x v →
        graphicalDerivative (subdifferential f) x v =
          subdifferential (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x v w))) ∧
    (∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ →
      (IsProtoDifferentiableAt (attentiveLocalization f x v ε) x v ↔
        TwiceEpiDifferentiableAt f x v) ∧
      (TwiceEpiDifferentiableAt f x v →
        graphicalDerivative (attentiveLocalization f x v ε) x v =
          subdifferential (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x v w))) ∧
    IsProper (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x v w) := by
  obtain ⟨f₁, ε, K, hd2, hte, hsc_agree, ε₀, hε₀, hatt⟩ := hf.exists_proxCore
  obtain ⟨hcore1, hcore2⟩ := K.core_equivalence
  have hprop := K.isProper_half
  rw [hd2] at hprop hcore2
  have htransfer : ∀ S : E → Set E,
      (∀ᶠ p in 𝓝 (x, v), p.2 ∈ S p.1 ↔ p.2 - v ∈ proxLocalization f₁ x ε p.1) →
      (IsProtoDifferentiableAt S x v ↔ TwiceEpiDifferentiableAt f x v) ∧
      (TwiceEpiDifferentiableAt f x v → graphicalDerivative S x v =
        subdifferential (fun w ↦ ((1 / 2 : ℝ) : EReal) * secondSubderivative f x v w)) := by
    intro S hS
    obtain ⟨h1, h2⟩ := isProtoDifferentiableAt_iff_of_eventually hS
    refine ⟨h1.trans (hcore1.trans hte), fun h ↦ ?_⟩
    rw [h2]
    exact hcore2 (hcore1.2 (hte.2 h))
  exact ⟨fun hsc ↦ htransfer _ (hsc_agree hsc),
    ⟨ε₀, hε₀, fun ε' h1 h2 ↦ htransfer _ (hatt ε' h1 h2)⟩, hprop⟩

end RW
