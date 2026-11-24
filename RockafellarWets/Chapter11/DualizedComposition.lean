/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dualized composition

Example 11.44.
-/
import RockafellarWets.Chapter11.PrimalDualSolutions
import RockafellarWets.Chapter11.HorizonConjugacy
import RockafellarWets.Chapter3.HomogeneousCompletion
import RockafellarWets.Chapter10.PLQCalculus
import RockafellarWets.Chapter11.ProductConjugacy

open Set Filter Topology Classical
open scoped InnerProductSpace
namespace RW
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `θ* ∘ g*`, with the convention `θ*(∞) = ∞` of **11.44**. -/
def conjugateComposition (θ : ℝ → EReal) (g : E → EReal) (y : E) : EReal :=
  if fenchelConjugate g y = ⊤ then ⊤ else fenchelConjugate θ (fenchelConjugate g y).toReal

section Perspective
variable {g : E → EReal}

omit [FiniteDimensional ℝ E] in
theorem closedPerspectiveFunction_of_pos {t : ℝ} (ht : 0 < t) (w : E) :
    closedPerspectiveFunction g (t, w) = (t : EReal) * g (t⁻¹ • w) := by
  simp [closedPerspectiveFunction, ht]

omit [FiniteDimensional ℝ E] in
theorem closedPerspectiveFunction_zero (w : E) :
    closedPerspectiveFunction g (0, w) = horizonFunction g w := by
  simp [closedPerspectiveFunction]

omit [FiniteDimensional ℝ E] in
theorem closedPerspectiveFunction_of_neg {t : ℝ} (ht : t < 0) (w : E) :
    closedPerspectiveFunction g (t, w) = ⊤ := by
  simp [closedPerspectiveFunction, not_lt.mpr ht.le, ht.ne]

/-- **11.5** in the form used by **11.44**: `g^∞ = σ_{dom g*}`. -/
theorem horizonFunction_eq_supportFunction_domain (hgp : IsProper g)
    (hgl : LowerSemicontinuous g) (hgc : Convex ℝ (epigraph g)) :
    horizonFunction g = supportFunction (effectiveDomain (fenchelConjugate g)) := by
  have hb := fenchelConjugate_fenchelConjugate_eq hgp hgl hgc
  have h := horizon_fenchelConjugate_eq_support_domain_of_proper
    (isProper_fenchelConjugate hgp hgl hgc) (by rw [hb]; exact hgp)
  rwa [hb] at h

omit [FiniteDimensional ℝ E] in
theorem le_supportFunction {D : Set E} {y : E} (hy : y ∈ D) (w : E) :
    (⟪y, w⟫_ℝ : EReal) ≤ supportFunction D w :=
  le_iSup (fun v : D ↦ (⟪(v : E), w⟫_ℝ : EReal)) ⟨y, hy⟩

omit [FiniteDimensional ℝ E] in
theorem supportFunction_zero_of_nonempty {D : Set E} (hD : D.Nonempty) :
    supportFunction D 0 = 0 := by
  haveI := hD.to_subtype
  simp [supportFunction]

/-- The scaled Fenchel inequality `t g(t⁻¹w) ≥ ⟨y,w⟩ - t g*(y)` for `t > 0`. -/
theorem coe_inner_sub_le_mul_of_pos (hgp : IsProper g) {t : ℝ} (ht : 0 < t) {y : E} {s : ℝ}
    (hs : fenchelConjugate g y = s) (w : E) :
    ((⟪y, w⟫_ℝ - t * s : ℝ) : EReal) ≤ (t : EReal) * g (t⁻¹ • w) := by
  have hY := fenchel_young hgp (t⁻¹ • w) y
  rw [hs] at hY
  induction hgv : g (t⁻¹ • w) using EReal.rec with
  | bot => exact absurd hgv (hgp.2 _).ne'
  | top => rw [EReal.coe_mul_top_of_pos ht]; exact le_top
  | coe a =>
    rw [hgv, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_smul_right] at hY
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
    have := mul_le_mul_of_nonneg_left hY ht.le
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at this
    linarith

theorem closedPerspectiveFunction_ne_bot (hgp : IsProper g) (hgl : LowerSemicontinuous g)
    (hgc : Convex ℝ (epigraph g)) (p : ℝ × E) : closedPerspectiveFunction g p ≠ ⊥ := by
  obtain ⟨t, w⟩ := p
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [closedPerspectiveFunction_of_neg ht]; exact top_ne_bot
  · rw [closedPerspectiveFunction_zero, horizonFunction_eq_supportFunction_domain hgp hgl hgc]
    obtain ⟨y, hy⟩ := (isProper_fenchelConjugate hgp hgl hgc).1
    exact ((EReal.bot_lt_coe _).trans_le
      (le_supportFunction (D := effectiveDomain (fenchelConjugate g)) hy w)).ne'
  · rw [closedPerspectiveFunction_of_pos ht]
    induction hgv : g (t⁻¹ • w) using EReal.rec with
    | bot => exact absurd hgv (hgp.2 _).ne'
    | top => rw [EReal.coe_mul_top_of_pos ht]; exact top_ne_bot
    | coe a => exact_mod_cast EReal.coe_ne_bot _

end Perspective

section ScalarConjugate
variable {θ : ℝ → EReal}

theorem inner_real_eq_mul (s t : ℝ) : ⟪s, t⟫_ℝ = s * t := by
  simp [mul_comm]

/-- If `θ(t)/t → ℓ` and `s < ℓ`, then `θ*(s) < ∞` for proper lsc convex `θ`
with `dom θ ⊆ [0,∞)`. -/
theorem fenchelConjugate_lt_top_of_lt_limit (hθp : IsProper θ) (hθl : LowerSemicontinuous θ)
    (hθc : Convex ℝ (epigraph θ)) (hdom : effectiveDomain θ ⊆ Ici 0) {ℓ : EReal}
    (hℓ : Tendsto (fun t : ℝ ↦ θ t * ((t⁻¹ : ℝ) : EReal)) atTop (𝓝 ℓ)) {s : ℝ}
    (hs : (s : EReal) < ℓ) : fenchelConjugate θ s < ⊤ := by
  obtain ⟨s', hs₁, hs₂⟩ := EReal.lt_iff_exists_real_btwn.mp hs
  have hev : ∀ᶠ t in atTop, (s' : EReal) < θ t * ((t⁻¹ : ℝ) : EReal) := hℓ.eventually (lt_mem_nhds hs₂)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  set T := max T₀ 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨⟨s₀, hs₀⟩, -⟩ := isProper_fenchelConjugate hθp hθl hθc
  obtain ⟨t₀, ht₀⟩ := hθp.1
  have hθt₀ : θ t₀ = ((θ t₀).toReal : EReal) := (EReal.coe_toReal ht₀.ne (hθp.2 t₀).ne').symm
  have hb₀ := bot_lt_fenchelConjugate_of_finite hθt₀ s₀
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, fenchelConjugate θ s₀ = c₀ :=
    ⟨_, (EReal.coe_toReal hs₀.ne hb₀.ne').symm⟩
  refine lt_of_le_of_lt ((fenchelConjugate_le_coe_iff θ s (max (|s - s₀| * T + c₀) 0)).mpr ?_)
    (EReal.coe_lt_top _)
  intro t
  rw [inner_real_eq_mul]
  by_cases htd : θ t < ⊤
  swap
  · rw [not_lt, top_le_iff] at htd
    rw [htd]
    exact le_top
  have ht0 : 0 ≤ t := hdom htd
  obtain ⟨a, ha⟩ : ∃ a : ℝ, θ t = a := ⟨_, (EReal.coe_toReal htd.ne (hθp.2 t).ne').symm⟩
  rw [ha, EReal.coe_le_coe_iff]
  have hmin := (fenchelConjugate_le_coe_iff θ s₀ c₀).mp hc₀.le t
  rw [ha, EReal.coe_le_coe_iff, inner_real_eq_mul] at hmin
  by_cases htT : t ≤ T
  · have h₁ : (s - s₀) * t ≤ |s - s₀| * T :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) ht0).trans
        (mul_le_mul_of_nonneg_left htT (abs_nonneg _))
    have : s * t - a ≤ |s - s₀| * T + c₀ := by linarith
    linarith [le_max_left (|s - s₀| * T + c₀) 0]
  · have htT₀ : T₀ ≤ t := (le_max_left _ _).trans (not_le.mp htT).le
    have htpos : 0 < t := hT.trans (not_le.mp htT)
    have hq := hT₀ t htT₀
    rw [ha, ← EReal.coe_mul, EReal.coe_lt_coe_iff] at hq
    have hst : s' * t < a := by
      have h := mul_lt_mul_of_pos_right hq htpos
      rwa [mul_assoc, inv_mul_cancel₀ htpos.ne', mul_one] at h
    have hss : s < s' := EReal.coe_lt_coe_iff.mp hs₁
    have : s * t - a ≤ 0 := by nlinarith [mul_lt_mul_of_pos_right hss htpos]
    linarith [le_max_right (|s - s₀| * T + c₀) 0]

end ScalarConjugate

/-- Affine precomposition preserves convex epigraphs, for any normed target. -/
theorem convex_epigraph_comp_add_const {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {h : G → EReal} (hh : Convex ℝ (epigraph h))
    (A : F →L[ℝ] G) (a : G) : Convex ℝ (epigraph (fun x ↦ h (A x + a))) := by
  intro p hp q hq s t hs ht hst
  have hh' := hh (show (A p.1 + a, p.2) ∈ epigraph h from hp)
    (show (A q.1 + a, q.2) ∈ epigraph h from hq) hs ht hst
  change h (A (s • p.1 + t • q.1) + a) ≤ ((s * p.2 + t * q.2 : ℝ) : EReal)
  change h (s • (A p.1 + a) + t • (A q.1 + a)) ≤ ((s * p.2 + t * q.2 : ℝ) : EReal) at hh'
  have he : s • (A p.1 + a) + t • (A q.1 + a) = A (s • p.1 + t • q.1) + a := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hst, one_smul, map_add, map_smul, map_smul]
  rwa [he] at hh'

variable {g : E → EReal} {θ : ℝ → EReal}

/-- The lower bound in **11.44**, valid without the limit condition. -/
theorem fenchelConjugate_conjugateComposition_le (hgp : IsProper g) (hgl : LowerSemicontinuous g)
    (hgc : Convex ℝ (epigraph g)) (hθp : IsProper θ) (z : E) :
    fenchelConjugate (conjugateComposition θ g) z ≤
      ⨅ t : Ici (0 : ℝ), θ t + closedPerspectiveFunction g ((t : ℝ), z) := by
  have hpc := isProper_fenchelConjugate hgp hgl hgc
  refine iSup_le fun y ↦ le_iInf fun t ↦ ?_
  obtain ⟨t, ht⟩ := t
  change (⟪z, y⟫_ℝ : EReal) - conjugateComposition θ g y ≤ θ t + closedPerspectiveFunction g (t, z)
  unfold conjugateComposition
  split_ifs with hgy
  · simp
  obtain ⟨s, hs⟩ : ∃ s : ℝ, fenchelConjugate g y = s :=
    ⟨_, (EReal.coe_toReal hgy (hpc.2 y).ne').symm⟩
  rw [hs, EReal.toReal_coe]
  by_cases hθt : θ t = ⊤
  · rw [hθt, EReal.top_add_of_ne_bot (closedPerspectiveFunction_ne_bot hgp hgl hgc _)]
    exact le_top
  obtain ⟨a, ha⟩ : ∃ a : ℝ, θ t = a := ⟨_, (EReal.coe_toReal hθt (hθp.2 t).ne').symm⟩
  have hconj : ((s * t - a : ℝ) : EReal) ≤ fenchelConjugate θ s := by
    have := le_fenchelConjugate θ t s
    rwa [ha, inner_real_eq_mul, ← EReal.coe_sub] at this
  have hpersp : ((⟪y, z⟫_ℝ - t * s : ℝ) : EReal) ≤ closedPerspectiveFunction g (t, z) := by
    rcases (show (0 : ℝ) ≤ t from ht).lt_or_eq with htp | rfl
    · rw [closedPerspectiveFunction_of_pos htp]
      exact coe_inner_sub_le_mul_of_pos hgp htp hs z
    · rw [closedPerspectiveFunction_zero, horizonFunction_eq_supportFunction_domain hgp hgl hgc]
      simpa using le_supportFunction (D := effectiveDomain (fenchelConjugate g))
        (show fenchelConjugate g y < ⊤ by rw [hs]; exact EReal.coe_lt_top s) z
  calc (⟪z, y⟫_ℝ : EReal) - fenchelConjugate θ s
      ≤ (⟪z, y⟫_ℝ : EReal) - ((s * t - a : ℝ) : EReal) := EReal.sub_le_sub le_rfl hconj
    _ = ((⟪y, z⟫_ℝ - t * s : ℝ) : EReal) + (a : EReal) := by
        rw [← EReal.coe_sub, ← EReal.coe_add, real_inner_comm]
        congr 1
        ring
    _ ≤ closedPerspectiveFunction g (t, z) + (a : EReal) := add_le_add hpersp le_rfl
    _ = θ t + closedPerspectiveFunction g (t, z) := by rw [ha, add_comm]

/-- The parameterization `f(λ,u) = θ(λ) + h(λ, z + u)` of **11.44**, where `h` is
the closed perspective of `g`. -/
def dualizedCompositionIntegrand (θ : ℝ → EReal) (g : E → EReal) (z : E) :
    WithLp 2 (ℝ × E) → EReal :=
  fun q ↦ θ q.fst + closedPerspectiveFunction g (q.fst, z + q.snd)

section Integrand
variable (hgp : IsProper g) (hgl : LowerSemicontinuous g) (hgc : Convex ℝ (epigraph g))
  (hθp : IsProper θ) (hθl : LowerSemicontinuous θ) (hθc : Convex ℝ (epigraph θ))
  (hdom : effectiveDomain θ ⊆ Ici 0) (z : E)
include hgp hgl hgc hθp

theorem dualizedCompositionIntegrand_ne_bot (q : WithLp 2 (ℝ × E)) :
    dualizedCompositionIntegrand θ g z q ≠ ⊥ := by
  simp only [dualizedCompositionIntegrand, ne_eq, EReal.add_eq_bot_iff, not_or]
  exact ⟨(hθp.2 _).ne', closedPerspectiveFunction_ne_bot hgp hgl hgc _⟩

omit hθp in
theorem horizonFunction_zero_of_proper : horizonFunction g 0 = 0 := by
  rw [horizonFunction_eq_supportFunction_domain hgp hgl hgc]
  exact supportFunction_zero_of_nonempty (isProper_fenchelConjugate hgp hgl hgc).1

include hdom in
theorem isProper_dualizedCompositionIntegrand : IsProper (dualizedCompositionIntegrand θ g z) := by
  refine ⟨?_, fun q ↦ bot_lt_iff_ne_bot.mpr (dualizedCompositionIntegrand_ne_bot hgp hgl hgc hθp z q)⟩
  obtain ⟨t₀, ht₀⟩ := hθp.1
  have ht₀0 : (0 : ℝ) ≤ t₀ := hdom ht₀
  rcases ht₀0.lt_or_eq with hpos | rfl
  · obtain ⟨x₀, hx₀⟩ := hgp.1
    refine ⟨WithLp.toLp 2 (t₀, t₀ • x₀ - z), ?_⟩
    change θ t₀ + closedPerspectiveFunction g (t₀, z + (t₀ • x₀ - z)) < ⊤
    rw [show z + (t₀ • x₀ - z) = t₀ • x₀ by abel, closedPerspectiveFunction_of_pos hpos,
      smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    refine EReal.add_lt_top ht₀.ne ?_
    induction hv : g x₀ using EReal.rec with
    | bot => exact absurd hv (hgp.2 _).ne'
    | top => exact absurd (hv ▸ hx₀) (lt_irrefl _)
    | coe a => exact_mod_cast EReal.coe_ne_top _
  · refine ⟨WithLp.toLp 2 (0, -z), ?_⟩
    change θ 0 + closedPerspectiveFunction g (0, z + -z) < ⊤
    rw [add_neg_cancel, closedPerspectiveFunction_zero, horizonFunction_zero_of_proper hgp hgl hgc,
      add_zero]
    exact ht₀

include hθl in
theorem lowerSemicontinuous_dualizedCompositionIntegrand :
    LowerSemicontinuous (dualizedCompositionIntegrand θ g z) := by
  have hfst : Continuous (fun q : WithLp 2 (ℝ × E) ↦ q.fst) := (WithLp.fstL 2 ℝ ℝ E).continuous
  have hsnd : Continuous (fun q : WithLp 2 (ℝ × E) ↦ q.snd) := (WithLp.sndL 2 ℝ ℝ E).continuous
  have h₂ : LowerSemicontinuous (fun q : WithLp 2 (ℝ × E) ↦
      closedPerspectiveFunction g (q.fst, z + q.snd)) :=
    (lowerSemicontinuous_closedPerspectiveFunction hgl hgp).comp
      (hfst.prodMk (continuous_const.add hsnd))
  exact (hθl.comp hfst).add' h₂ fun q ↦ EReal.continuousAt_add
    (.inr (closedPerspectiveFunction_ne_bot hgp hgl hgc _)) (.inl (hθp.2 _).ne')

include hθc in
theorem convex_epigraph_dualizedCompositionIntegrand :
    Convex ℝ (epigraph (dualizedCompositionIntegrand θ g z)) := by
  have h₁ : Convex ℝ (epigraph (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst)) := by
    have := convex_epigraph_compAffine hθc (WithLp.fstL 2 ℝ ℝ E) 0
    simpa using this
  have hh := convex_epigraph_of_sublinear (sublinear_closedPerspectiveFunction hgl hgp hgc)
  have h₂ : Convex ℝ (epigraph (fun q : WithLp 2 (ℝ × E) ↦
      closedPerspectiveFunction g (q.fst, z + q.snd))) := by
    have := convex_epigraph_comp_add_const hh
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).toContinuousLinearMap) ((0 : ℝ), z)
    convert this using 3 with q
    change closedPerspectiveFunction g (q.fst, z + q.snd) =
      closedPerspectiveFunction g ((q.fst, q.snd) + ((0 : ℝ), z))
    rw [Prod.mk_add_mk, add_zero, add_comm z]
  exact convex_epigraph_add_of_ne_bot h₁ h₂ (fun _ ↦ (hθp.2 _).ne')
    (fun _ ↦ closedPerspectiveFunction_ne_bot hgp hgl hgc _)

omit [FiniteDimensional ℝ E] hgp hgl hgc hθp in
theorem inner_toLp_real_prod (μ t : ℝ) (y u : E) :
    ⟪WithLp.toLp 2 (μ, y), WithLp.toLp 2 (t, u)⟫_ℝ = μ * t + ⟪y, u⟫_ℝ := by
  rw [WithLp.prod_inner_apply]
  exact congrArg (· + ⟪y, u⟫_ℝ) (inner_real_eq_mul μ t)

omit hθp in
/-- The scaled Fenchel bound for the closed perspective at any `t ≥ 0`. -/
theorem coe_inner_sub_le_closedPerspective {t : ℝ} (ht : 0 ≤ t) {y : E} {s : ℝ}
    (hs : fenchelConjugate g y = s) (w : E) :
    ((⟪y, w⟫_ℝ - t * s : ℝ) : EReal) ≤ closedPerspectiveFunction g (t, w) := by
  rcases ht.lt_or_eq with htp | rfl
  · rw [closedPerspectiveFunction_of_pos htp]
    exact coe_inner_sub_le_mul_of_pos hgp htp hs w
  · rw [closedPerspectiveFunction_zero, horizonFunction_eq_supportFunction_domain hgp hgl hgc]
    simpa using le_supportFunction (D := effectiveDomain (fenchelConjugate g))
      (show fenchelConjugate g y < ⊤ by rw [hs]; exact EReal.coe_lt_top s) w

include hdom in
/-- Upper conjugate estimate: `f*(μ,y) ≤ θ*(μ + g*(y)) - ⟨y,z⟩`. -/
theorem fenchelConjugate_dualizedCompositionIntegrand_le {y : E} {s : ℝ}
    (hs : fenchelConjugate g y = s) (μ : ℝ) :
    fenchelConjugate (dualizedCompositionIntegrand θ g z) (WithLp.toLp 2 (μ, y)) ≤
      fenchelConjugate θ (μ + s) - (⟪y, z⟫_ℝ : EReal) := by
  refine iSup_le fun q ↦ ?_
  obtain ⟨⟨t, u⟩, rfl⟩ := (WithLp.toLp_surjective 2) q
  change (⟪WithLp.toLp 2 (μ, y), WithLp.toLp 2 (t, u)⟫_ℝ : EReal) -
    (θ t + closedPerspectiveFunction g (t, z + u)) ≤ _
  rw [inner_toLp_real_prod]
  by_cases hθt : θ t = ⊤
  · rw [hθt, EReal.top_add_of_ne_bot (closedPerspectiveFunction_ne_bot hgp hgl hgc _),
      EReal.sub_top]
    exact bot_le
  obtain ⟨a, ha⟩ : ∃ a : ℝ, θ t = a := ⟨_, (EReal.coe_toReal hθt (hθp.2 t).ne').symm⟩
  have ht0 : 0 ≤ t := hdom (show θ t < ⊤ by rw [ha]; exact EReal.coe_lt_top a)
  have hpersp := coe_inner_sub_le_closedPerspective hgp hgl hgc ht0 hs (z + u)
  have hconj : (((μ + s) * t - a : ℝ) : EReal) ≤ fenchelConjugate θ (μ + s) := by
    have := le_fenchelConjugate θ t (μ + s)
    rwa [ha, inner_real_eq_mul, ← EReal.coe_sub] at this
  calc ((μ * t + ⟪y, u⟫_ℝ : ℝ) : EReal) - (θ t + closedPerspectiveFunction g (t, z + u))
      ≤ ((μ * t + ⟪y, u⟫_ℝ : ℝ) : EReal) - ((a : EReal) + ((⟪y, z + u⟫_ℝ - t * s : ℝ) : EReal)) := by
        rw [ha]
        exact EReal.sub_le_sub le_rfl (add_le_add le_rfl hpersp)
    _ = (((μ + s) * t - a : ℝ) : EReal) - (⟪y, z⟫_ℝ : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, inner_add_right]
        congr 1
        ring
    _ ≤ fenchelConjugate θ (μ + s) - (⟪y, z⟫_ℝ : EReal) := EReal.sub_le_sub hconj le_rfl

omit [FiniteDimensional ℝ E] hgl hgc hθp in
theorem le_fenchelConjugate_dualizedCompositionIntegrand {t : ℝ} (ht : 0 < t) {a : ℝ}
    (ha : θ t = a) (y x : E) :
    ((t * ⟪y, x⟫_ℝ - ⟪y, z⟫_ℝ - a : ℝ) : EReal) - (t : EReal) * g x ≤
      fenchelConjugate (dualizedCompositionIntegrand θ g z) (WithLp.toLp 2 (0, y)) := by
  refine le_trans (le_of_eq ?_) (le_fenchelConjugate _ (WithLp.toLp 2 (t, t • x - z)) _)
  change _ = (⟪WithLp.toLp 2 ((0 : ℝ), y), WithLp.toLp 2 (t, t • x - z)⟫_ℝ : EReal) -
    (θ t + closedPerspectiveFunction g (t, z + (t • x - z)))
  rw [inner_toLp_real_prod, show z + (t • x - z) = t • x by abel,
    closedPerspectiveFunction_of_pos ht, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, ha,
    inner_sub_right, inner_smul_right]
  induction hv : g x using EReal.rec with
  | bot => exact absurd hv (hgp.2 _).ne'
  | top => simp [EReal.coe_mul_top_of_pos ht]
  | coe γ =>
    norm_cast
    ring

omit [FiniteDimensional ℝ E] hgl hgc hθp in
theorem coe_lt_fenchelConjugate_dualizedCompositionIntegrand {t : ℝ} (ht : 0 < t) {a : ℝ}
    (ha : θ t = a) {y : E} {c : ℝ}
    (hc : (((c + a + ⟪y, z⟫_ℝ) / t : ℝ) : EReal) < fenchelConjugate g y) :
    (c : EReal) < fenchelConjugate (dualizedCompositionIntegrand θ g z) (WithLp.toLp 2 (0, y)) := by
  obtain ⟨x, hx⟩ := lt_iSup_iff.mp hc
  have hgx : g x ≠ ⊤ := by
    intro h
    rw [h, EReal.sub_top] at hx
    exact not_lt_bot hx
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, g x = γ := ⟨_, (EReal.coe_toReal hgx (hgp.2 x).ne').symm⟩
  rw [hγ, ← EReal.coe_sub, EReal.coe_lt_coe_iff, div_lt_iff₀ ht] at hx
  refine lt_of_lt_of_le ?_ (le_fenchelConjugate_dualizedCompositionIntegrand hgp z ht ha y x)
  rw [hγ, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
  have he : (⟪y, x⟫_ℝ - γ) * t = t * ⟪y, x⟫_ℝ - t * γ := by ring
  linarith

include hdom in
/-- Lower conjugate estimate: `θ*(g*(y)) - ⟨y,z⟩ ≤ f*(0,y)` when `g*(y)` is finite. -/
theorem fenchelConjugate_sub_le_fenchelConjugate_dualizedCompositionIntegrand {y : E} {s : ℝ}
    (hs : fenchelConjugate g y = s) :
    fenchelConjugate θ s - (⟪y, z⟫_ℝ : EReal) ≤
      fenchelConjugate (dualizedCompositionIntegrand θ g z) (WithLp.toLp 2 (0, y)) := by
  obtain ⟨⟨q₀, hq₀⟩, -⟩ := isProper_dualizedCompositionIntegrand hgp hgl hgc hθp hdom z
  have hFb : ⊥ < fenchelConjugate (dualizedCompositionIntegrand θ g z) (WithLp.toLp 2 (0, y)) :=
    bot_lt_fenchelConjugate_of_finite (EReal.coe_toReal hq₀.ne
      (dualizedCompositionIntegrand_ne_bot hgp hgl hgc hθp z q₀)).symm _
  rw [fenchelConjugate, sub_eq_add_neg, ereal_iSup_add]
  refine iSup_le fun t ↦ ?_
  by_cases hθt : θ t = ⊤
  · rw [hθt, EReal.sub_top, EReal.bot_add]
    exact bot_le
  obtain ⟨a, ha⟩ : ∃ a : ℝ, θ t = a := ⟨_, (EReal.coe_toReal hθt (hθp.2 t).ne').symm⟩
  have ht0 : 0 ≤ t := hdom (show θ t < ⊤ by rw [ha]; exact EReal.coe_lt_top a)
  rw [ha, inner_real_eq_mul, ← EReal.coe_sub, ← EReal.coe_neg, ← EReal.coe_add]
  rcases ht0.lt_or_eq with htp | rfl
  · refine le_of_forall_lt fun c hc ↦ ?_
    induction c using EReal.rec with
    | bot => exact hFb
    | top => exact absurd hc not_top_lt
    | coe c =>
      apply coe_lt_fenchelConjugate_dualizedCompositionIntegrand hgp z htp ha
      rw [hs, EReal.coe_lt_coe_iff, div_lt_iff₀ htp]
      rw [EReal.coe_lt_coe_iff] at hc
      linarith
  · refine le_trans (le_of_eq ?_) (le_fenchelConjugate _ (WithLp.toLp 2 ((0 : ℝ), -z)) _)
    change _ = (⟪WithLp.toLp 2 ((0 : ℝ), y), WithLp.toLp 2 ((0 : ℝ), -z)⟫_ℝ : EReal) -
      (θ 0 + closedPerspectiveFunction g (0, z + -z))
    rw [inner_toLp_real_prod, add_neg_cancel, closedPerspectiveFunction_zero,
      horizonFunction_zero_of_proper hgp hgl hgc, ha, add_zero, inner_neg_right]
    norm_cast
    ring

end Integrand

/-- **Example 11.44** (dualized composition): for proper lsc convex `g` and `θ`
with `dom θ ⊆ [0,∞)` and `lim_{λ→∞} θ(λ)/λ > -g(0)`,
`inf_{λ≥0} {θ(λ) + λ g(λ⁻¹z)} = (θ* ∘ g*)*(z)`, where `g^∞(z)` replaces
`λ g(λ⁻¹z)` at `λ = 0` and `θ*(∞) = ∞`. -/
theorem dualized_composition (hgp : IsProper g) (hgl : LowerSemicontinuous g)
    (hgc : Convex ℝ (epigraph g)) (hθp : IsProper θ) (hθl : LowerSemicontinuous θ)
    (hθc : Convex ℝ (epigraph θ)) (hdom : effectiveDomain θ ⊆ Ici 0) {ℓ : EReal}
    (hℓ : Tendsto (fun t : ℝ ↦ θ t * ((t⁻¹ : ℝ) : EReal)) atTop (𝓝 ℓ)) (hgℓ : -g 0 < ℓ)
    (z : E) :
    (⨅ t : Ici (0 : ℝ), θ t + closedPerspectiveFunction g ((t : ℝ), z)) =
      fenchelConjugate (conjugateComposition θ g) z := by
  refine le_antisymm ?_ (fenchelConjugate_conjugateComposition_le hgp hgl hgc hθp z)
  have hpc := isProper_fenchelConjugate hgp hgl hgc
  have hθcp := isProper_fenchelConjugate hθp hθl hθc
  by_cases hpos : ∃ t₁ : ℝ, 0 < t₁ ∧ θ t₁ < ⊤
  · obtain ⟨t₁, ht₁, ht₁'⟩ := hpos
    obtain ⟨a₁, ha₁⟩ : ∃ a : ℝ, θ t₁ = a := ⟨_, (EReal.coe_toReal ht₁'.ne (hθp.2 t₁).ne').symm⟩
    set F := dualizedCompositionIntegrand θ g z
    have hFp := isProper_dualizedCompositionIntegrand hgp hgl hgc hθp hdom z
    have hFl := lowerSemicontinuous_dualizedCompositionIntegrand hgp hgl hgc hθp hθl z
    have hFc := convex_epigraph_dualizedCompositionIntegrand hgp hgl hgc hθp hθc z
    have hprimal : (⨅ t : Ici (0 : ℝ), θ t + closedPerspectiveFunction g ((t : ℝ), z)) =
        ⨅ t, primalObjective F t := by
      apply le_antisymm
      · refine le_iInf fun t ↦ ?_
        by_cases ht : 0 ≤ t
        · refine (iInf_le _ ⟨t, ht⟩).trans (le_of_eq ?_)
          change _ = θ t + closedPerspectiveFunction g (t, z + 0)
          rw [add_zero]
        · have hθt : θ t = ⊤ := by
            by_contra hne
            exact ht (hdom (lt_top_iff_ne_top.mpr hne))
          change _ ≤ θ t + closedPerspectiveFunction g (t, z + 0)
          rw [hθt, EReal.top_add_of_ne_bot (closedPerspectiveFunction_ne_bot hgp hgl hgc _)]
          exact le_top
      · refine le_iInf fun t ↦ (iInf_le _ (t : ℝ)).trans (le_of_eq ?_)
        change θ t + closedPerspectiveFunction g (t, z + 0) = _
        rw [add_zero]
    have hV : (0 : ℝ) ∈ interior (effectiveDomain (dualParametricValue F)) := by
      rw [effectiveDomain_dualParametricValue]
      obtain ⟨a, ha₁, ha₂⟩ := EReal.lt_iff_exists_real_btwn.mp hgℓ
      obtain ⟨b, hb₁, hb₂⟩ := EReal.lt_iff_exists_real_btwn.mp ha₂
      have hab : a < b := EReal.coe_lt_coe_iff.mp hb₁
      have hinf : (⨅ y, fenchelConjugate g y) < (a : EReal) := by
        rw [iInf_eq_neg_fenchelConjugate_zero, fenchelConjugate_fenchelConjugate_eq hgp hgl hgc]
        exact ha₁
      obtain ⟨y, hy⟩ := iInf_lt_iff.mp hinf
      obtain ⟨s, hs⟩ : ∃ s : ℝ, fenchelConjugate g y = s :=
        ⟨_, (EReal.coe_toReal (hy.trans (EReal.coe_lt_top a)).ne (hpc.2 y).ne').symm⟩
      have hsa : s < a := by
        rw [hs] at hy
        exact EReal.coe_lt_coe_iff.mp hy
      refine mem_interior.mpr ⟨Ioo (-(b - a)) (b - a), fun μ hμ ↦ ?_, isOpen_Ioo, ?_⟩
      · refine ⟨WithLp.toLp 2 (μ, y), ?_, rfl⟩
        have hθs : fenchelConjugate θ (μ + s) < ⊤ :=
          fenchelConjugate_lt_top_of_lt_limit hθp hθl hθc hdom hℓ
            ((EReal.coe_lt_coe_iff.mpr (by linarith [hμ.2])).trans hb₂)
        obtain ⟨m, hm⟩ : ∃ m : ℝ, fenchelConjugate θ (μ + s) = m :=
          ⟨_, (EReal.coe_toReal hθs.ne (hθcp.2 _).ne').symm⟩
        refine lt_of_le_of_lt
          (fenchelConjugate_dualizedCompositionIntegrand_le hgp hgl hgc hθp hdom z hs μ) ?_
        rw [hm, ← EReal.coe_sub]
        exact EReal.coe_lt_top _
      · simp only [mem_Ioo, neg_lt_zero, sub_pos]
        exact ⟨hab, hab⟩
    rw [hprimal, primal_dual_strong_duality_of_dual_interior hFp hFl hFc hV]
    refine iSup_le fun y ↦ ?_
    by_cases hgy : fenchelConjugate g y = ⊤
    · have htop : fenchelConjugate F (WithLp.toLp 2 (0, y)) = ⊤ := by
        rw [EReal.eq_top_iff_forall_lt]
        intro c
        apply coe_lt_fenchelConjugate_dualizedCompositionIntegrand hgp z ht₁ ha₁
        rw [hgy]
        exact EReal.coe_lt_top _
      change -fenchelConjugate F (WithLp.toLp 2 (0, y)) ≤ _
      rw [htop, EReal.neg_top]
      exact bot_le
    · obtain ⟨s, hs⟩ : ∃ s : ℝ, fenchelConjugate g y = s :=
        ⟨_, (EReal.coe_toReal hgy (hpc.2 y).ne').symm⟩
      have hlow := fenchelConjugate_sub_le_fenchelConjugate_dualizedCompositionIntegrand
        hgp hgl hgc hθp hdom z hs
      have hk : conjugateComposition θ g y = fenchelConjugate θ s := by
        simp [conjugateComposition, hs]
      calc dualObjective F y = -fenchelConjugate F (WithLp.toLp 2 (0, y)) := rfl
        _ ≤ -(fenchelConjugate θ s - (⟪y, z⟫_ℝ : EReal)) := EReal.neg_le_neg_iff.mpr hlow
        _ = (⟪z, y⟫_ℝ : EReal) - conjugateComposition θ g y := by
            rw [EReal.neg_sub (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)), hk,
              sub_eq_add_neg, add_comm, real_inner_comm]
        _ ≤ fenchelConjugate (conjugateComposition θ g) z := le_fenchelConjugate _ y z
  · push_neg at hpos
    have hθtop : ∀ t, t ≠ 0 → θ t = ⊤ := by
      intro t ht
      rcases lt_or_gt_of_ne ht with htn | htp
      · by_contra hne
        exact absurd (hdom (lt_top_iff_ne_top.mpr hne)) (not_le.mpr htn)
      · exact top_le_iff.mp (hpos t htp)
    obtain ⟨c, hc⟩ : ∃ c : ℝ, θ 0 = c := by
      obtain ⟨t₀, ht₀⟩ := hθp.1
      have h0 : t₀ = 0 := by
        by_contra hne
        rw [hθtop t₀ hne] at ht₀
        exact lt_irrefl _ ht₀
      subst h0
      exact ⟨_, (EReal.coe_toReal ht₀.ne (hθp.2 0).ne').symm⟩
    have hθconj : ∀ s : ℝ, fenchelConjugate θ s = ((-c : ℝ) : EReal) := by
      intro s
      apply le_antisymm
      · refine iSup_le fun t ↦ ?_
        by_cases ht : t = 0
        · subst ht
          rw [hc, inner_real_eq_mul, mul_zero, ← EReal.coe_sub, zero_sub]
        · rw [hθtop t ht, EReal.sub_top]
          exact bot_le
      · refine le_trans (le_of_eq ?_) (le_fenchelConjugate θ 0 s)
        rw [hc, inner_real_eq_mul, mul_zero, ← EReal.coe_sub, zero_sub]
    calc (⨅ t : Ici (0 : ℝ), θ t + closedPerspectiveFunction g ((t : ℝ), z))
        ≤ θ 0 + closedPerspectiveFunction g (0, z) := iInf_le_of_le ⟨0, self_mem_Ici⟩ le_rfl
      _ = (c : EReal) + supportFunction (effectiveDomain (fenchelConjugate g)) z := by
          rw [hc, closedPerspectiveFunction_zero, horizonFunction_eq_supportFunction_domain hgp hgl hgc]
      _ ≤ fenchelConjugate (conjugateComposition θ g) z := by
          rw [supportFunction, ereal_add_iSup]
          refine iSup_le fun v ↦ ?_
          have hv : fenchelConjugate g v ≠ ⊤ := v.2.ne
          refine le_trans (le_of_eq ?_) (le_fenchelConjugate _ (v : E) z)
          rw [conjugateComposition, if_neg hv, hθconj, real_inner_comm z]
          norm_cast
          ring

end
end RW
