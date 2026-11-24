/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Lipschitzian geometry of subgradient mappings

Proposition 13.46.  As in the proof, we normalize to `v̄ = 0` and make the function prox-bounded
without changing it near `x̄`: `f₁ = f - ⟪v̄, ·⟫ + δ_B` for a small closed ball `B` around `x̄`.
Proposition 13.37 then presents the graph of an `f₁`-attentive localization `T` of `∂f₁` as the
graph of the Lipschitz mapping `∇e_λ f₁` in the coordinates `(y, w) ↦ (y + λw, w)`.  The
`f`-attentive localizations of `∂f` around `(x̄, v̄)` agree with the translate of `T` near
`(x̄, v̄)`, because along `gph T` the values `f₁(y) = e_λ f₁(u) - ‖u - y‖²/(2λ)`, `u = y + λw`,
depend continuously on `u`; under subdifferential continuity, `∂f` itself agrees with them.
-/

import RockafellarWets.Chapter13.ProxRegularEnvelopes
import RockafellarWets.Chapter13.ProxRegularPerturbations
import RockafellarWets.Chapter9.GraphicallyLipschitzianMappings
import RockafellarWets.Chapter10.SubgradientGerms
import RockafellarWets.Chapter12.Hypomonotonicity

open Filter Set Topology Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### Coordinates -/

/-- A mapping whose graph near `(x̄, v̄)` is `{(y, w) ∣ w - v̄ = G(y + λ(w - v̄))}`, with `G`
strictly continuous at `x̄`, is graphically Lipschitzian of dimension `n` around `(x̄, v̄)`. -/
theorem graphicallyLipschitzianAt_of_shifted_graph {S : E → Set E} {x v : E} (hv : v ∈ S x)
    {lam : ℝ} {G : E → E} (hG : StrictlyContinuousAt G x)
    (hgraph : ∀ᶠ z in 𝓝 (x, v), z ∈ svGraph S ↔ z.2 - v = G (z.1 + lam • (z.2 - v))) :
    GraphicallyLipschitzianAt S x v (Module.finrank ℝ E) := by
  let A := (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv
  let L₀ : (E × E) ≃ₗ[ℝ] (E × E) :=
    { toFun := fun p ↦ (p.1 + lam • p.2, p.2)
      invFun := fun p ↦ (p.1 - lam • p.2, p.2)
      map_add' := fun p q ↦ by
        ext <;> simp only [Prod.fst_add, Prod.snd_add, smul_add] <;> abel
      map_smul' := fun c p ↦ by
        ext <;> simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add, smul_comm c lam]
      left_inv := fun p ↦ by ext <;> simp
      right_inv := fun p ↦ by ext <;> simp }
  let L := L₀.toContinuousLinearEquiv.trans (A.prodCongr A)
  let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun a ↦ A (v + G (A.symm a - lam • v))
  apply graphicallyLipschitzianAt_of_linear_graph hv rfl L g
  · -- strict continuity of `g`
    obtain ⟨k, U, hU, hL⟩ := strictlyContinuousAt_iff.mp hG
    have hpt : (L (x, v)).1 = A (x + lam • v) := rfl
    rw [hpt]
    have hV : (fun a ↦ A.symm a - lam • v) ⁻¹' U ∈ 𝓝 (A (x + lam • v)) := by
      apply ((A.symm.continuous.sub continuous_const).continuousAt).preimage_mem_nhds
      simpa only [A.symm_apply_apply, add_sub_cancel_right] using hU
    refine strictlyContinuousAt_iff.mpr ⟨‖A.toContinuousLinearMap‖₊ * (k * ‖A.symm.toContinuousLinearMap‖₊),
      _, hV, ?_⟩
    intro a ha b hb
    have h1 := hL ha hb
    calc edist (g a) (g b) = edist (A (v + G (A.symm a - lam • v))) (A (v + G (A.symm b - lam • v))) :=
          rfl
      _ ≤ ‖A.toContinuousLinearMap‖₊ * edist (v + G (A.symm a - lam • v))
          (v + G (A.symm b - lam • v)) := A.toContinuousLinearMap.lipschitz _ _
      _ = ‖A.toContinuousLinearMap‖₊ * edist (G (A.symm a - lam • v)) (G (A.symm b - lam • v)) := by
          rw [edist_add_left]
      _ ≤ ‖A.toContinuousLinearMap‖₊ * (k * edist (A.symm a - lam • v) (A.symm b - lam • v)) :=
          by gcongr
      _ = ‖A.toContinuousLinearMap‖₊ * (k * edist (A.symm a) (A.symm b)) := by
          rw [edist_sub_right]
      _ ≤ ‖A.toContinuousLinearMap‖₊ * (k * (‖A.symm.toContinuousLinearMap‖₊ * edist a b)) :=
          by gcongr; exact A.symm.toContinuousLinearMap.lipschitz _ _
      _ = (‖A.toContinuousLinearMap‖₊ * (k * ‖A.symm.toContinuousLinearMap‖₊) : NNReal) *
          edist a b := by
          push_cast; ring
  · filter_upwards [hgraph] with z hz
    rw [hz]
    change _ ↔ A z.2 = A (v + G (A.symm (A (z.1 + lam • z.2)) - lam • v))
    rw [A.symm_apply_apply, A.injective.eq_iff,
      show z.1 + lam • z.2 - lam • v = z.1 + lam • (z.2 - v) by rw [smul_sub]; abel]
    constructor
    · intro h; rw [← h]; abel
    · intro h; exact (eq_sub_of_add_eq' h.symm).symm

/-! ### Locality of prox-regularity -/

omit [FiniteDimensional ℝ E] in
/-- Prox-regularity only depends on the function near `x̄`. -/
theorem IsProxRegularAt.congr_nhds [FiniteDimensional ℝ E] {f₁ f₂ : E → EReal} {x v : E}
    (h : f₁ =ᶠ[𝓝 x] f₂) (h₂ : IsProxRegularAt f₂ x v) : IsProxRegularAt f₁ x v := by
  obtain ⟨hl, hv, ε, hε, ρ, hρ, hprox⟩ := h₂
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (h : {y | f₁ y = f₂ y} ∈ 𝓝 x)
  have hx : f₁ x = f₂ x := h.self_of_nhds
  refine ⟨hl.congr_nhds h.symm, by rw [subdifferential_eq_of_eventuallyEq h]; exact hv,
    min ε (r / 2), lt_min hε (by positivity), ρ, hρ, fun y v' hv' hvv hy hfy x' hx' ↦ ?_⟩
  have hyr : y ∈ ball x r := by
    rw [mem_ball, dist_eq_norm]; linarith [min_le_right ε (r / 2)]
  have hloc : f₁ =ᶠ[𝓝 y] f₂ := by
    filter_upwards [isOpen_ball.mem_nhds hyr] with z hz using hball hz
  have hfy' : f₁ y = f₂ y := hloc.self_of_nhds
  have hx'r : x' ∈ ball x r := by
    rw [mem_ball]; rw [mem_closedBall] at hx'; linarith [min_le_right ε (r / 2)]
  have hfx' : f₁ x' = f₂ x' := hball hx'r
  rw [subdifferential_eq_of_eventuallyEq hloc] at hv'
  rw [hfy', hfx']
  refine hprox y v' hv' (lt_of_lt_of_le hvv (min_le_left _ _)) (lt_of_lt_of_le hy (min_le_left _ _))
    ?_ x' ?_
  · rw [← hfy', ← hx]
    exact lt_of_lt_of_le hfy (by
      have := EReal.coe_le_coe_iff.2 (min_le_left ε (r / 2))
      exact add_le_add le_rfl this)
  · rw [mem_closedBall] at hx' ⊢; linarith [min_le_left ε (r / 2)]

/-! ### Attentive localizations -/

/-- The `f`-attentive `ε`-localization of `∂f` around `(x̄, v̄)`: the pairs `(y, w) ∈ gph ∂f` with
`‖y - x̄‖ < ε`, `|f(y) - f(x̄)| < ε` and `‖w - v̄‖ < ε`. -/
def attentiveLocalization (f : E → EReal) (x v : E) (ε : ℝ) (y : E) : Set E :=
  {w | w ∈ subdifferential f y ∧ ‖y - x‖ < ε ∧ f x - ε < f y ∧ f y < f x + ε ∧ ‖w - v‖ < ε}

omit [FiniteDimensional ℝ E] in
/-- Subdifferential continuity, in neighborhood form. -/
theorem IsSubdifferentiallyContinuousAt.exists_lt {f : E → EReal} {x v : E}
    (h : IsSubdifferentiallyContinuousAt f x v) {c : ℝ} (hc : f x = c) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ y w, w ∈ subdifferential f y → ‖y - x‖ < δ → ‖w - v‖ < δ →
      f y < ((c + η : ℝ) : EReal) := by
  by_contra hcon
  push_neg at hcon
  choose ys ws hws hys hwv hfy using fun n : ℕ ↦ hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have hδ : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hyx : Tendsto ys atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (hys n).le) hδ
  have hwv' : Tendsto ws atTop (𝓝 v) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (hwv n).le) hδ
  have hlim := h.2 ys ws hyx hwv' hws
  rw [hc] at hlim
  have hev := hlim.eventually (gt_mem_nhds (EReal.coe_lt_coe_iff.2 (by linarith : c < c + η)))
  obtain ⟨n, hn⟩ := hev.exists
  exact absurd (hfy n) (not_le.2 hn)

omit [FiniteDimensional ℝ E] in
/-- Subgradients of `f - ⟪v, ·⟫` are those of `f` shifted by `-v`. -/
theorem mem_subdifferential_sub_inner_iff [FiniteDimensional ℝ E] {f : E → EReal} {y w v : E} :
    w ∈ subdifferential (fun z ↦ f z + ((-⟪v, z⟫_ℝ : ℝ) : EReal)) y ↔
      w + v ∈ subdifferential f y := by
  have hg : ∀ z ∈ ball y 1, HasGradientAt (fun z ↦ -⟪v, z⟫_ℝ) (-v) z := by
    intro z _
    rw [hasGradientAt_iff_hasFDerivAt]
    have := ((InnerProductSpace.toDual ℝ E v : E →L[ℝ] ℝ).hasFDerivAt (x := z)).neg
    convert this using 1
    ext u
    simp [InnerProductSpace.toDual_apply_apply]
  by_cases hfin : ∃ c : ℝ, f y = c
  · obtain ⟨c, hc⟩ := hfin
    rw [subdifferential_add_lipschitz_gradient (L := 0) le_rfl hg (fun _ _ _ _ ↦ by simp)
      (mem_ball_self one_pos) hc]
    constructor
    · rintro ⟨u, hu, rfl⟩
      simpa using hu
    · intro h
      exact ⟨w + v, h, by abel⟩
  · constructor
    · intro h
      exfalso
      obtain ⟨⟨c, hc⟩, -⟩ := mem_subdifferential_iff_exists_seq.1 h
      apply hfin
      refine ⟨(f y).toReal, (EReal.coe_toReal ?_ ?_).symm⟩
      · intro htop; rw [htop, EReal.top_add_coe] at hc; exact EReal.coe_ne_top c hc.symm
      · intro hbot; rw [hbot, EReal.bot_add] at hc; exact EReal.coe_ne_bot c hc.symm
    · intro h
      exact absurd (mem_subdifferential_iff_exists_seq.1 h).1 hfin

/-- **Proposition 13.46** (Lipschitzian geometry of subgradient mappings).  If `f` is prox-regular
at `x̄` for `v̄`, then every sufficiently close `f`-attentive localization of `∂f` around `(x̄, v̄)`
is graphically Lipschitzian of dimension `n` around `(x̄, v̄)`; if `f` is moreover
subdifferentially continuous at `x̄` for `v̄`, this holds for `∂f` itself. -/
theorem lipschitzian_geometry_of_subgradient_mappings {f : E → EReal} {x v : E}
    (hf : IsProxRegularAt f x v) :
    (∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ →
      GraphicallyLipschitzianAt (attentiveLocalization f x v ε) x v (Module.finrank ℝ E)) ∧
    (IsSubdifferentiallyContinuousAt f x v →
      GraphicallyLipschitzianAt (subdifferential f) x v (Module.finrank ℝ E)) := by
  classical
  have hf' := hf
  obtain ⟨hlsc, hv, ε₁, hε₁, ρ, hρ, hprox⟩ := hf'
  set c := (f x).toReal with hcdef
  have hc : f x = (c : EReal) := (EReal.coe_toReal hlsc.2.1 hlsc.1).symm
  -- the normalized, prox-bounded modification `f₁`
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
  -- Proposition 13.37 for `f₁`
  obtain ⟨ε, hε, lam₀, hlam₀, H⟩ := proximal_mappings_and_moreau_envelopes hpr₁ hpb₁
  set lam := lam₀ / 2 with hlam
  have hlam0 : 0 < lam := by positivity
  obtain ⟨P, hUo, hxU, hPx, hPsingle, hPmono, hdiff, hGLip, hgr⟩ := H lam hlam0 (by linarith)
  set U := proxRange f₁ x ε lam with hU
  set G : E → E := fun u ↦ lam⁻¹ • (u - P u) with hG
  have hGsc : StrictlyContinuousAt G x := by
    refine strictlyContinuousAt_iff.mpr ⟨⟨3 / lam, by positivity⟩, U, hUo.mem_nhds hxU, ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
    rw [dist_eq_norm, dist_eq_norm]
    have := hGLip b hb a ha
    simpa using this
  -- the graph of the localization `T` of `∂f₁`
  have hT : ∀ y w, w ∈ proxLocalization f₁ x ε y ↔ y + lam • w ∈ U ∧ G (y + lam • w) = w := by
    intro y w
    constructor
    · intro hw
      have hu : y + lam • w ∈ U := ⟨y, w, hw, rfl⟩
      exact ⟨hu, (hgr _ hu w).2 ⟨y, hw, rfl⟩⟩
    · rintro ⟨hu, hGw⟩
      obtain ⟨y', hy', hyy⟩ := (hgr _ hu w).1 hGw
      rw [add_left_inj] at hyy
      rw [hyy]; exact hy'
  -- values of `f₁` along `T`
  set φ : E → ℝ := fun u ↦ (moreauEnvelopeEReal f₁ lam u).toReal - 1 / (2 * lam) * ‖P u - u‖ ^ 2
    with hφ
  have hφval : ∀ u ∈ U, f₁ (P u) = (φ u : EReal) := by
    intro u hu
    have hmem : P u ∈ proximalMappingEReal f₁ lam u := by rw [hPsingle u hu]; exact mem_singleton _
    obtain ⟨hobj, -⟩ := mem_proximalMappingEReal_iff.1 hmem
    obtain ⟨he1, he2, -⟩ := hdiff u hu
    have he : moreauEnvelopeEReal f₁ lam u = ((moreauEnvelopeEReal f₁ lam u).toReal : EReal) :=
      (EReal.coe_toReal he2 he1).symm
    rw [proximalObjectiveEReal, he] at hobj
    rcases ereal_trichotomy (f₁ (P u)) with h' | h' | ⟨r, hr⟩
    · rw [h', EReal.bot_add] at hobj; exact absurd hobj.symm (EReal.coe_ne_bot _)
    · rw [h', EReal.top_add_coe] at hobj; exact absurd hobj (EReal.coe_ne_top _).symm
    · rw [hr] at hobj ⊢
      rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at hobj
      rw [EReal.coe_eq_coe_iff, hφ]
      dsimp only
      linarith
  have hφcont : ContinuousAt φ x := by
    obtain ⟨-, -, hd⟩ := hdiff x hxU
    have hP : ContinuousAt P x := by
      have : ∀ᶠ u in 𝓝 x, dist (P u) (P x) ≤ 2 * dist u x := by
        filter_upwards [hUo.mem_nhds hxU] with u hu
        rw [dist_eq_norm, dist_eq_norm]
        exact (hPmono x hxU u hu).2
      rw [Metric.continuousAt_iff]
      intro η hη
      obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 (this : {u | dist (P u) (P x) ≤ 2 * dist u x} ∈ 𝓝 x)
      refine ⟨min δ (η / 3), lt_min hδ (by positivity), fun u hu ↦ ?_⟩
      have h1 := hδU (lt_of_lt_of_le hu (min_le_left _ _))
      have h2 : dist u x < η / 3 := lt_of_lt_of_le hu (min_le_right _ _)
      calc dist (P u) (P x) ≤ 2 * dist u x := h1
        _ < η := by linarith
    exact hd.continuousAt.sub (continuousAt_const.mul ((hP.sub continuousAt_id).norm.pow 2))
  have hφx : φ x = c - ⟪v, x⟫_ℝ := by
    have h := hφval x hxU
    rw [hPx] at h
    simp only [hf₁, if_pos (mem_closedBall_self hε₁.le), hf₀, hc, ← EReal.coe_add,
      EReal.coe_eq_coe_iff] at h
    linarith
  -- values of `f` near `x̄`
  have hf₁val : ∀ y ∈ ball x ε₁, f₁ y = f y + ((-⟪v, y⟫_ℝ : ℝ) : EReal) := fun y hy ↦
    (hball₁ y hy).self_of_nhds
  have hsub₁ : ∀ y ∈ ball x ε₁, ∀ w, w ∈ subdifferential f₁ y ↔ w + v ∈ subdifferential f y := by
    intro y hy w
    rw [subdifferential_eq_of_eventuallyEq (hball₁ y hy)]
    exact mem_subdifferential_sub_inner_iff
  -- the map `z ↦ y + λ(w - v̄)` and its continuity
  have hucont : Tendsto (fun z : E × E ↦ z.1 + lam • (z.2 - v)) (𝓝 (x, v)) (𝓝 x) := by
    have h : Tendsto (fun z : E × E ↦ z.1 + lam • (z.2 - v)) (𝓝 (x, v))
        (𝓝 (x + lam • (v - v))) :=
      (continuous_fst.add (continuous_const.smul (continuous_snd.sub continuous_const))).tendsto _
    simpa using h
  have hUev : ∀ᶠ z in 𝓝 (x, v), z.1 + lam • (z.2 - v) ∈ U := hucont.eventually (hUo.mem_nhds hxU)
  -- a common description of the localizations near `(x̄, v̄)`
  have hTiff : ∀ᶠ z in 𝓝 (x, v), (z.2 - v ∈ proxLocalization f₁ x ε z.1 ↔
      z.2 - v = G (z.1 + lam • (z.2 - v))) := by
    filter_upwards [hUev] with z hz
    rw [hT]
    exact ⟨fun h ↦ h.2.symm, fun h ↦ ⟨hz, h.symm⟩⟩
  have hnear : ∀ δ > 0, ∀ᶠ z in 𝓝 (x, v), ‖z.1 - x‖ < δ ∧ ‖z.2 - v‖ < δ := by
    intro δ hδ
    have h1 : ∀ᶠ z in 𝓝 (x, v), z ∈ ball (x, v) δ := ball_mem_nhds _ hδ
    filter_upwards [h1] with z hz
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hz
    exact hz
  refine ⟨⟨min (ε / (2 * (‖v‖ + 1))) (min ε₁ ε), by positivity, fun ε' hε' hε'0 ↦ ?_⟩, fun hsc ↦ ?_⟩
  · -- attentive localizations
    have hε'1 : ε' ≤ ε / (2 * (‖v‖ + 1)) := le_trans hε'0 (min_le_left _ _)
    have hε'2 : ε' ≤ ε₁ := le_trans hε'0 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hε'3 : ε' ≤ ε := le_trans hε'0 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hmem : v ∈ attentiveLocalization f x v ε' x := ⟨hv, by simpa using hε', by
      rw [hc, ← EReal.coe_sub]; exact EReal.coe_lt_coe_iff.2 (by linarith), by
      rw [hc, ← EReal.coe_add]; exact EReal.coe_lt_coe_iff.2 (by linarith), by simpa using hε'⟩
    refine graphicallyLipschitzianAt_of_shifted_graph (lam := lam) hmem hGsc ?_
    -- continuity of `φ` and of `⟪v̄, y⟫` give the value condition along `T`
    have hφev : ∀ᶠ z in 𝓝 (x, v), |φ (z.1 + lam • (z.2 - v)) - φ x| < ε' / 2 :=
      (hucont.eventually (Metric.continuousAt_iff'.1 hφcont (ε' / 2) (by positivity))).mono
        fun z hz ↦ by rw [← Real.dist_eq]; exact hz
    have hvev : ∀ᶠ z in 𝓝 (x, v), |⟪v, z.1 - x⟫_ℝ| < ε' / 2 := by
      have h : Tendsto (fun z : E × E ↦ ⟪v, z.1 - x⟫_ℝ) (𝓝 (x, v)) (𝓝 ⟪v, x - x⟫_ℝ) :=
        (continuous_const.inner (continuous_fst.sub continuous_const)).tendsto _
      rw [sub_self, inner_zero_right] at h
      filter_upwards [h.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε' / 2))] with z hz
      rwa [Real.dist_0_eq_abs] at hz
    filter_upwards [hTiff, hnear ε' hε', hUev, hφev, hvev] with z hzT ⟨hz1, hz2⟩ hzU hzφ hzv
    rw [← hzT]
    obtain ⟨y, w⟩ := z
    simp only at hzT hz1 hz2 hzU hzφ hzv ⊢
    have hyb : y ∈ ball x ε₁ := by rw [mem_ball, dist_eq_norm]; linarith
    constructor
    · rintro ⟨hw, -, hlow, hup, -⟩
      refine ⟨(hsub₁ y hyb _).2 (by rw [sub_add_cancel]; exact hw), by linarith, ?_,
        by linarith⟩
      -- `f₁ y < f₁ x + ε`
      rw [hf₁val y hyb, hf₁val x (mem_ball_self hε₁), hc]
      rw [hc] at hup
      rcases ereal_trichotomy (f y) with h' | h' | ⟨r, hr⟩
      · rw [h', EReal.bot_add]; exact EReal.bot_lt_coe _
      · rw [h'] at hup; exact absurd hup (not_lt.2 le_top)
      · rw [hr] at hup ⊢
        rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
        rw [← EReal.coe_add, EReal.coe_lt_coe_iff] at hup
        apply EReal.coe_lt_coe_iff.2
        have h1 : |⟪v, y - x⟫_ℝ| ≤ ‖v‖ * ‖y - x‖ := abs_real_inner_le_norm _ _
        have h2 : ‖v‖ * ‖y - x‖ ≤ ‖v‖ * ε' := mul_le_mul_of_nonneg_left hz1.le (norm_nonneg _)
        have h3 : ε' * (2 * (‖v‖ + 1)) ≤ ε := by
          rw [le_div_iff₀ (by positivity)] at hε'1; exact hε'1
        rw [inner_sub_right] at h1
        nlinarith [abs_le.1 h1, norm_nonneg v]
    · intro hTm
      have hw : w - v ∈ subdifferential f₁ y := hTm.1
      have hw' : w ∈ subdifferential f y := by
        have := (hsub₁ y hyb _).1 hw
        rwa [sub_add_cancel] at this
      have hGu : G (y + lam • (w - v)) = w - v := ((hT y (w - v)).1 hTm).2
      set u := y + lam • (w - v) with hu
      have h2 : u - P u = lam • (w - v) := by
        have h := congrArg (fun t ↦ lam • t) hGu
        simp only [hG, smul_smul, mul_inv_cancel₀ hlam0.ne', one_smul] at h
        exact h
      have hPu : P u = y := by
        have : P u = u - (u - P u) := by abel
        rw [this, h2, hu]; abel
      have hf₁y : f₁ y = (φ u : EReal) := by
        have h := hφval u hzU
        rwa [hPu] at h
      rw [hf₁val y hyb] at hf₁y
      have hfy : f y = ((φ u + ⟪v, y⟫_ℝ : ℝ) : EReal) := by
        rcases ereal_trichotomy (f y) with h' | h' | ⟨r, hr⟩
        · rw [h', EReal.bot_add] at hf₁y; exact absurd hf₁y.symm (EReal.coe_ne_bot _)
        · rw [h', EReal.top_add_coe] at hf₁y; exact absurd hf₁y.symm (EReal.coe_ne_top _)
        · rw [hr, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hf₁y
          rw [hr, EReal.coe_eq_coe_iff]
          linarith
      rw [inner_sub_right] at hzv
      rw [hφx] at hzφ
      refine ⟨hw', hz1, ?_, ?_, hz2⟩
      · rw [hc, hfy, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
        linarith [abs_lt.1 hzφ, abs_lt.1 hzv]
      · rw [hc, hfy, ← EReal.coe_add, EReal.coe_lt_coe_iff]
        linarith [abs_lt.1 hzφ, abs_lt.1 hzv]
  · -- subdifferential continuity
    obtain ⟨δ, hδ, hδf⟩ := hsc.exists_lt hc (by positivity : (0 : ℝ) < ε / 2)
    refine graphicallyLipschitzianAt_of_shifted_graph (lam := lam) hv hGsc ?_
    have hvev : ∀ᶠ z in 𝓝 (x, v), |⟪v, z.1 - x⟫_ℝ| < ε / 2 := by
      have h : Tendsto (fun z : E × E ↦ ⟪v, z.1 - x⟫_ℝ) (𝓝 (x, v)) (𝓝 ⟪v, x - x⟫_ℝ) :=
        (continuous_const.inner (continuous_fst.sub continuous_const)).tendsto _
      rw [sub_self, inner_zero_right] at h
      filter_upwards [h.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε / 2))] with z hz
      rwa [Real.dist_0_eq_abs] at hz
    filter_upwards [hTiff, hnear (min δ (min ε ε₁)) (by positivity), hvev] with z hzT ⟨hz1, hz2⟩ hzv
    rw [← hzT]
    obtain ⟨y, w⟩ := z
    simp only at hzT hz1 hz2 hzv ⊢
    have hyb : y ∈ ball x ε₁ := by
      rw [mem_ball, dist_eq_norm]; linarith [min_le_right δ (min ε ε₁), min_le_right ε ε₁]
    change w ∈ subdifferential f y ↔ _
    constructor
    · intro hw
      refine ⟨(hsub₁ y hyb _).2 (by rw [sub_add_cancel]; exact hw), by
        linarith [min_le_right δ (min ε ε₁), min_le_left ε ε₁], ?_, by
        linarith [min_le_right δ (min ε ε₁), min_le_left ε ε₁]⟩
      have hfy := hδf y w hw (by linarith [min_le_left δ (min ε ε₁)])
        (by linarith [min_le_left δ (min ε ε₁)])
      rw [hf₁val y hyb, hf₁val x (mem_ball_self hε₁), hc]
      rcases ereal_trichotomy (f y) with h' | h' | ⟨r, hr⟩
      · rw [h', EReal.bot_add]; exact EReal.bot_lt_coe _
      · rw [h'] at hfy; exact absurd hfy (not_lt.2 le_top)
      · rw [hr] at hfy ⊢
        rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
        rw [EReal.coe_lt_coe_iff] at hfy
        apply EReal.coe_lt_coe_iff.2
        rw [inner_sub_right] at hzv
        linarith [abs_lt.1 hzv]
    · rintro ⟨hw, -, -, -⟩
      have := (hsub₁ y hyb _).1 hw
      rwa [sub_add_cancel] at this

end RW
