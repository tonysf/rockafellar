/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subgradients as normals to epigraphs

The vertical component of a normal separates ordinary subgradients (negative
height) from horizon subgradients (zero height).
-/

import RockafellarWets.Chapter8.SubgradientRelationships
import RockafellarWets.Chapter7.SubdifferentialRegularity
import RockafellarWets.Chapter7.AuxEpiComparison
import RockafellarWets.Chapter8.HorizonSubgradientSequences
import RockafellarWets.Chapter6.ChangeOfCoordinates

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → EReal} {x v : E} {c β : ℝ}

/-- Polarity of the subderivative epigraph and the regular epigraph normal
cone. The real test height includes points where the subderivative is infinite. -/
theorem mem_regularNormalCone_epigraph_iff (hx : f x = c) :
    WithLp.toLp 2 (v,β) ∈ regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      ∀ w (r : ℝ), subderivative f x w ≤ (r : EReal) → ⟪v,w⟫_ℝ + β*r ≤ 0 := by
  have hp : WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f := hx.le
  rw [mem_regularNormalCone_iff_inner_nonpos hp]
  have he (w : E) (r : ℝ) : WithLp.toLp 2 (w,r) ∈
      tangentCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      subderivative f x w ≤ (r : EReal) := by
    change _ ∈ tangentCone (l2ProdEquiv E ⁻¹' epigraph f) _ ↔ _
    rw [tangentCone_preimage_continuousLinearEquiv, mem_preimage, l2ProdEquiv_toLp,
      l2ProdEquiv_toLp, ← epigraph_subderivative_eq_tangentCone hx]
    rfl
  constructor
  · intro h w r hr
    have hinner := h _ ((he w r).mpr hr)
    simpa [WithLp.prod_inner_apply, real_inner_comm r β, mul_comm r β] using hinner
  · intro h z hz
    obtain ⟨⟨w,r⟩, rfl⟩ := (WithLp.toLp_surjective 2) z
    simpa [WithLp.prod_inner_apply, mul_comm r β] using h w r ((he w r).mp hz)

/-- **Theorem 8.9**, regular subgradients are the negative-unit-height slice
of the regular normal cone to the epigraph. -/
theorem mem_regularSubdifferential_iff_epigraph_normal (hx : f x = c) :
    v ∈ regularSubdifferential f x ↔
      WithLp.toLp 2 (v,(-1 : ℝ)) ∈ regularNormalCone (euclideanEpigraph f)
        (WithLp.toLp 2 (x,c)) := by
  rw [mem_regularSubdifferential_iff_inner_le_subderivative hx, mem_regularNormalCone_epigraph_iff hx]
  constructor
  · intro h w r hr
    have := EReal.coe_le_coe_iff.mp ((h w).trans hr)
    linarith
  · intro h w
    by_contra! hlt
    obtain ⟨r, hwr, hr⟩ := EReal.exists_between_coe_real hlt
    have := h w r hwr.le
    linarith [EReal.coe_lt_coe_iff.mp hr]

omit [FiniteDimensional ℝ E] in
/-- At a general epigraph point a regular normal also supports the entire
vertical fiber. This does not require convexity of the function. -/
theorem regularNormalCone_epigraph_vertical {v : E} {b r : ℝ}
    (hn : WithLp.toLp 2 (v,b) ∈ regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)))
    (hr : f x ≤ (r : EReal)) : b*(r-c) ≤ 0 := by
  let p := WithLp.toLp 2 (x,c)
  let q := WithLp.toLp 2 (x,r)
  let T := l2ProdEquiv E ⁻¹' (({x} : Set E) ×ˢ Ici (min c r))
  have hp : p ∈ T := ⟨rfl, show min c r ≤ c from min_le_left ..⟩
  have hq : q ∈ T := ⟨rfl, show min c r ≤ r from min_le_right ..⟩
  have hc : f x ≤ (c : EReal) := hn.1
  have hTe : T ⊆ euclideanEpigraph f := by
    intro z hz
    change (WithLp.ofLp z).1 = x ∧ min c r ≤ (WithLp.ofLp z).2 at hz
    change f (WithLp.ofLp z).1 ≤ ((WithLp.ofLp z).2 : EReal)
    rw [hz.1]
    exact (le_min hc hr).trans (by simpa [EReal.coe_strictMono.monotone.map_min] using EReal.coe_le_coe_iff.mpr hz.2)
  have htc := convex_preimage_continuousLinearEquiv (l2ProdEquiv E)
    ((convex_singleton x).prod (convex_Ici (min c r)))
  have hrad : q-p ∈ radialCone T p := ⟨1,one_pos, by simpa using hq⟩
  have ht := tangentCone_mono hTe p
    (derivableCone_subset_tangentCone hp (mem_derivableCone_of_convex htc hp hrad))
  have hinner := inner_nonpos_of_mem_regularNormalCone hn ht
  change ⟪v,x-x⟫_ℝ + (r-c)*b ≤ 0 at hinner
  simpa [mul_comm] using hinner

omit [FiniteDimensional ℝ E] in
theorem vertical_nonpos_of_mem_regularNormalCone_epigraph
    (hn : WithLp.toLp 2 (v,β) ∈ regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c))) :
    β ≤ 0 := by
  have h := regularNormalCone_epigraph_vertical hn (r := c+1)
    ((show f x ≤ (c : EReal) from hn.1).trans (EReal.coe_le_coe_iff.mpr (by linarith)))
  simpa using h

omit [FiniteDimensional ℝ E] in
theorem value_eq_of_mem_regularNormalCone_epigraph_of_neg
    (hn : WithLp.toLp 2 (v,β) ∈ regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)))
    (hb : β < 0) : f x = c := by
  by_contra ne
  obtain ⟨r, hr, hrc⟩ := EReal.exists_between_coe_real
    (lt_of_le_of_ne (show f x ≤ _ from hn.1) ne)
  have h := regularNormalCone_epigraph_vertical hn hr.le
  exact (not_lt_of_ge h) (mul_pos_of_neg_of_neg hb (sub_neg.mpr (EReal.coe_lt_coe_iff.mp hrc)))

omit [FiniteDimensional ℝ E] in
theorem vertical_nonpos_of_mem_normalCone_epigraph (hn : WithLp.toLp 2 (v,β) ∈
    normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c))) : β ≤ 0 := by
  obtain ⟨_, _, q, _, _, hq, hlim⟩ := hn
  have hpair := ((l2ProdEquiv E).continuous.tendsto _).comp hlim
  change Tendsto (fun n ↦ (q n).ofLp) atTop (𝓝 (v,β)) at hpair
  rw [nhds_prod_eq] at hpair
  exact le_of_tendsto hpair.snd (.of_forall fun n ↦ vertical_nonpos_of_mem_regularNormalCone_epigraph
    (v := (q n).ofLp.1) (hn := hq n))

/-- Normalizing a negative-height regular normal produces a regular
subgradient at a finite graph point. -/
theorem regularSubgradient_of_negative_height
    (hn : WithLp.toLp 2 (v,β) ∈ regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)))
    (hb : β < 0) : (-β)⁻¹ • v ∈ regularSubdifferential f x := by
  rw [mem_regularSubdifferential_iff_epigraph_normal
    (value_eq_of_mem_regularNormalCone_epigraph_of_neg hn hb)]
  have hs := (isCone_regularNormalCone hn.1).smul_mem hn (inv_nonneg.mpr (neg_pos.mpr hb).le)
  convert hs using 1
  apply WithLp.ofLp_injective
  ext <;> simp [smul_eq_mul, hb.ne]

/-- **Theorem 8.9**, limiting subgradients are precisely limiting normals
with vertical component −1. -/
theorem mem_subdifferential_iff_epigraph_normal (hx : f x = c) :
    v ∈ subdifferential f x ↔ WithLp.toLp 2 (v,(-1 : ℝ)) ∈
      normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
  constructor
  · intro hv
    obtain ⟨_, y, w, hy, hfy, hw, hwv⟩ := mem_subdifferential_iff_exists_seq.mp hv
    choose d hd using fun n ↦ (show ∃ a : ℝ, f (y n) = a from ⟨(hw n).choose, (hw n).choose_spec.1⟩)
    have hdto : Tendsto d atTop (𝓝 c) := by
      apply EReal.tendsto_coe.mp
      simpa only [Function.comp_def, hx, hd] using hfy
    exact ⟨hx.le, fun n ↦ WithLp.toLp 2 (y n,d n), fun n ↦ WithLp.toLp 2 (w n,(-1:ℝ)),
      fun n ↦ (hd n).le, ((l2ProdEquiv E).symm.continuous.tendsto _).comp (hy.prodMk_nhds hdto),
      fun n ↦ (mem_regularSubdifferential_iff_epigraph_normal (hd n)).mp (hw n),
      ((l2ProdEquiv E).symm.continuous.tendsto _).comp (hwv.prodMk_nhds tendsto_const_nhds)⟩
  · rintro ⟨_, p, nrm, _, hp, hn, hnlim⟩
    have hp' := ((l2ProdEquiv E).continuous.tendsto _).comp hp
    have hn' := ((l2ProdEquiv E).continuous.tendsto _).comp hnlim
    change Tendsto (fun n ↦ (p n).ofLp) atTop (𝓝 (x,c)) at hp'
    change Tendsto (fun n ↦ (nrm n).ofLp) atTop (𝓝 (v,(-1:ℝ))) at hn'
    rw [nhds_prod_eq] at hp' hn'
    let b := fun n ↦ (WithLp.ofLp (nrm n)).2
    have hb : Tendsto b atTop (𝓝 (-1 : ℝ)) := hn'.snd
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hb.eventually_lt_const (by norm_num : (-1:ℝ)<0))
    let φ := fun n : ℕ ↦ n+N
    have hφ : Tendsto φ atTop atTop := tendsto_add_atTop_nat N
    have hneg (n : ℕ) : b (φ n) < 0 := hN _ (Nat.le_add_left _ _)
    have hval (n : ℕ) := value_eq_of_mem_regularNormalCone_epigraph_of_neg
      (v := (WithLp.ofLp (nrm (φ n))).1) (c := (WithLp.ofLp (p (φ n))).2) (hn (φ n)) (hneg n)
    rw [mem_subdifferential_iff_exists_seq]
    refine ⟨⟨c,hx⟩, fun n ↦ (WithLp.ofLp (p (φ n))).1,
      fun n ↦ (-b (φ n))⁻¹ • (WithLp.ofLp (nrm (φ n))).1, hp'.fst.comp hφ, ?_,
      fun n ↦ regularSubgradient_of_negative_height (hn (φ n)) (hneg n), ?_⟩
    · simpa only [Function.comp_def, hval, hx] using
        (continuous_coe_real_ereal.tendsto c).comp (hp'.snd.comp hφ)
    · have hs := ((hb.comp hφ).neg.inv₀ (by norm_num : -(-1:ℝ) ≠ 0)).smul (hn'.fst.comp hφ)
      simpa [Function.comp_def] using hs

/-- **Theorem 8.9**, every horizon subgradient defines a horizontal limiting
normal to the epigraph. -/
theorem horizontal_normal_of_mem_horizonSubdifferential (hx : f x = c)
    (hv : v ∈ horizonSubdifferential f x) :
    WithLp.toLp 2 (v,(0 : ℝ)) ∈ normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
  rcases (mem_horizonSubdifferential_iff_zero_or_scaledSeq hx).mp hv with rfl |
    ⟨y,w,t,hy,hw,ht,ht0,hv⟩
  · exact (isCone_normalCone (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le)).1
  choose d hd using fun n ↦ (show ∃ a : ℝ, f (y n) = a from ⟨(hw n).choose, (hw n).choose_spec.1⟩)
  obtain ⟨hyx,hfy⟩ := tendsto_attentiveNhds_iff.mp hy
  have hdto : Tendsto d atTop (𝓝 c) := by
    apply EReal.tendsto_coe.mp
    simpa only [Function.comp_def, hd, hx] using hfy
  refine ⟨hx.le, fun n ↦ WithLp.toLp 2 (y n,d n), fun n ↦ t n • WithLp.toLp 2 (w n,(-1:ℝ)),
    fun n ↦ (hd n).le, ((l2ProdEquiv E).symm.continuous.tendsto _).comp (hyx.prodMk_nhds hdto),
    fun n ↦ (isCone_regularNormalCone (show WithLp.toLp 2 (y n,d n) ∈ euclideanEpigraph f
      from (hd n).le)).smul_mem ((mem_regularSubdifferential_iff_epigraph_normal (hd n)).mp
      (hw n)) (ht n).le, ?_⟩
  have hn : Tendsto (fun n ↦ t n * (-1)) atTop (𝓝 (0 : ℝ)) := by simpa using ht0.neg
  exact ((l2ProdEquiv E).symm.continuous.tendsto _).comp (hv.prodMk_nhds hn)

/-- The horizontal slice of the *regular* normal cone to the epigraph is
the polar of the effective domain of the subderivative at any finite point. -/
theorem horizontal_regularNormal_iff_polar_subderivative_domain {c : ℝ} (hx : f x = c) (v : E) :
    WithLp.toLp 2 (v,(0 : ℝ)) ∈ regularNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) ↔
      v ∈ polarCone (effectiveDomain (subderivative f x)) := by
  rw [mem_regularNormalCone_epigraph_iff hx]
  constructor
  · intro h w hw
    obtain ⟨r,hr,_⟩ := EReal.exists_between_coe_real (show subderivative f x w < ⊤ from hw)
    simpa using h w r hr.le
  · intro h w r hr
    simpa using h w (hr.trans_lt (EReal.coe_lt_top r))

end RW
