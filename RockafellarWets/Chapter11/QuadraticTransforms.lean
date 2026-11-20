/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The full and basic quadratic transforms

Examples 11.65 and 11.66 pair `ℝⁿ` with `ℝⁿ × ℝⁿˣⁿ_sym` and with `ℝⁿ × ℝ` under
couplings `⟨v,x⟩ - q(x)` with `q` quadratic.  Both are handled here through a
common coupling `Φ(x,y) = ⟨v(y),x⟩ - q(y,x)`.  Symmetric matrices are modelled
coordinate-free as the symmetric continuous linear operators.
-/
import RockafellarWets.Chapter11.GeneralizedConjugacy
import RockafellarWets.Chapter7.EpiLimitProperties
import RockafellarWets.Chapter7.EventualProxBoundedness

open Metric Set
open scoped InnerProductSpace

namespace RW

section PairingRegularity

variable {X Y : Type*}

/-- A conjugate under a coupling that is continuous in the second argument is
lower semicontinuous there. -/
theorem lowerSemicontinuous_pairingConjugate [TopologicalSpace Y] (Φ : X → Y → ℝ)
    (hΦ : ∀ x, Continuous (Φ x)) (f : X → EReal) :
    LowerSemicontinuous (pairingConjugate Φ f) := by
  change LowerSemicontinuous fun y ↦ ⨆ x, (Φ x y : EReal) - f x
  apply _root_.lowerSemicontinuous_iSup
  intro x
  cases h : f x with
  | bot => simpa using (lowerSemicontinuous_const : LowerSemicontinuous fun _ : Y ↦ (⊤ : EReal))
  | top => simpa using (lowerSemicontinuous_const : LowerSemicontinuous fun _ : Y ↦ (⊥ : EReal))
  | coe a =>
    have hc : Continuous fun y ↦ ((Φ x y - a : ℝ) : EReal) :=
      continuous_coe_real_ereal.comp ((hΦ x).sub continuous_const)
    simpa only [EReal.coe_sub] using hc.lowerSemicontinuous

/-- A conjugate under a coupling that is affine in the second argument has a
convex epigraph. -/
theorem convex_epigraph_pairingConjugate [AddCommGroup Y] [Module ℝ Y] (Φ : X → Y → ℝ)
    (hΦ : ∀ x (y₁ y₂ : Y) (a b : ℝ), a + b = 1 → Φ x (a • y₁ + b • y₂) = a * Φ x y₁ + b * Φ x y₂)
    (f : X → EReal) : Convex ℝ (epigraph (pairingConjugate Φ f)) := by
  intro p hp q hq a b ha hb hab
  change pairingConjugate Φ f p.1 ≤ (p.2 : EReal) at hp
  change pairingConjugate Φ f q.1 ≤ (q.2 : EReal) at hq
  change pairingConjugate Φ f (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  apply iSup_le
  intro x
  have hpx := (le_iSup (fun x ↦ (Φ x p.1 : EReal) - f x) x).trans hp
  have hqx := (le_iSup (fun x ↦ (Φ x q.1 : EReal) - f x) x).trans hq
  cases h : f x with
  | bot => rw [h] at hpx; simp at hpx
  | top => simp
  | coe c =>
    rw [h, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hpx hqx
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, hΦ x p.1 q.1 a b hab]
    have hp' := mul_le_mul_of_nonneg_left hpx ha
    have hq' := mul_le_mul_of_nonneg_left hqx hb
    have hc : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    linarith

end PairingRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section General

variable {Y : Type*} (v : Y → E) (q : Y → E → ℝ)

/-- The coupling `Φ(x,y) = ⟨v(y),x⟩ - q(y,x)`. -/
def quadraticCoupling (x : E) (y : Y) : ℝ := ⟪v y, x⟫_ℝ - q y x

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem coe_sub_le_coe_iff (r c : ℝ) (a : EReal) :
    (r : EReal) - a ≤ c ↔ ((r - c : ℝ) : EReal) ≤ a := by
  cases a with
  | bot =>
    rw [EReal.coe_sub_bot, top_le_iff, le_bot_iff]
    exact ⟨fun h ↦ absurd h (EReal.coe_ne_top _), fun h ↦ absurd h (EReal.coe_ne_bot _)⟩
  | top => simp
  | coe a =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro <;> linarith

/-- The conjugate is the Fenchel conjugate of the quadratically shifted function. -/
theorem pairingConjugate_quadraticCoupling (f : E → EReal) (y : Y) :
    pairingConjugate (quadraticCoupling v q) f y =
      fenchelConjugate (fun x ↦ f x + (q y x : EReal)) (v y) := by
  apply iSup_congr
  intro x
  change ((⟪v y, x⟫_ℝ - q y x : ℝ) : EReal) - f x = (⟪v y, x⟫_ℝ : EReal) - (f x + (q y x : EReal))
  cases f x with
  | bot => rw [EReal.coe_sub_bot, EReal.bot_add, EReal.coe_sub_bot]
  | top => simp
  | coe a =>
    rw [← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1
    ring

/-- The conjugate of the constant `∞` is the constant `-∞`. -/
theorem pairingConjugate_quadraticCoupling_of_top (f : E → EReal) (hf : ∀ x, f x = ⊤) :
    pairingConjugate (quadraticCoupling v q) f = fun _ ↦ ⊥ := by
  funext y
  apply le_antisymm _ bot_le
  apply iSup_le
  intro x
  rw [hf x]
  simp

omit [InnerProductSpace ℝ E] in
theorem isProxBounded_of_quadratic_minorant {f : E → EReal} {μ β : ℝ} (hμ : 0 < μ) (b : E)
    (h : ∀ w, ((β - 1 / (2 * μ) * ‖w - b‖ ^ 2 : ℝ) : EReal) ≤ f w) : IsProxBounded f :=
  ⟨μ, hμ, b, (EReal.bot_lt_coe β).trans_le ((le_moreauEnvelopeEReal_iff_quadratic_minorant μ β b).mpr h)⟩

omit [InnerProductSpace ℝ E] in
theorem exists_quadratic_minorant_of_isProxBounded {f : E → EReal} (h : IsProxBounded f) :
    ∃ μ > 0, ∃ b : E, ∃ β : ℝ, ∀ w, ((β - 1 / (2 * μ) * ‖w - b‖ ^ 2 : ℝ) : EReal) ≤ f w := by
  obtain ⟨μ, hμ, b, hb⟩ := h
  obtain ⟨β, _, hβ⟩ := EReal.exists_between_coe_real hb
  exact ⟨μ, hμ, b, β, (le_moreauEnvelopeEReal_iff_quadratic_minorant μ β b).mp hβ.le⟩

/-- A finite conjugate value forces prox-boundedness when the quadratic parts
grow at most quadratically. -/
theorem isProxBounded_of_pairingConjugate_lt_top
    (hgrowth : ∀ y, ∃ a : ℝ, ∀ x, q y x ≤ a * ‖x‖ ^ 2)
    {f : E → EReal} {y : Y} (hy : pairingConjugate (quadraticCoupling v q) f y < ⊤) :
    IsProxBounded f := by
  obtain ⟨c, hc, -⟩ := EReal.exists_between_coe_real hy
  obtain ⟨a, ha⟩ := hgrowth y
  have hA : 0 < max a 0 + 1 / 2 := by positivity
  refine isProxBounded_of_quadratic_minorant (μ := 1 / (2 * (max a 0 + 1 / 2)))
    (β := -c - ‖v y‖ ^ 2 / 2) (by positivity) 0 (fun w ↦ ?_)
  have hw : ((⟪v y, w⟫_ℝ - q y w : ℝ) : EReal) - f w ≤ c :=
    (le_iSup (fun x ↦ ((quadraticCoupling v q x y : ℝ) : EReal) - f x) w).trans hc.le
  rw [coe_sub_le_coe_iff] at hw
  refine le_trans (EReal.coe_le_coe_iff.mpr ?_) hw
  have h1 := ha w
  have h2 : -(‖v y‖ * ‖w‖) ≤ ⟪v y, w⟫_ℝ := neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have h3 : ‖v y‖ * ‖w‖ ≤ ‖v y‖ ^ 2 / 2 + ‖w‖ ^ 2 / 2 := by
    nlinarith [sq_nonneg (‖v y‖ - ‖w‖)]
  have h4 : a * ‖w‖ ^ 2 ≤ max a 0 * ‖w‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have h5 : 1 / (2 * (1 / (2 * (max a 0 + 1 / 2)))) = max a 0 + 1 / 2 := by
    field_simp
  rw [sub_zero, h5]
  nlinarith

/-- Without prox-boundedness the conjugate is identically `∞`. -/
theorem pairingConjugate_eq_top_of_not_isProxBounded
    (hgrowth : ∀ y, ∃ a : ℝ, ∀ x, q y x ≤ a * ‖x‖ ^ 2) {f : E → EReal}
    (hf : ¬ IsProxBounded f) :
    pairingConjugate (quadraticCoupling v q) f = fun _ ↦ ⊤ :=
  funext fun _ ↦ not_lt_top_iff.mp fun h ↦
    hf (isProxBounded_of_pairingConjugate_lt_top v q hgrowth h)

/-- Without prox-boundedness the biconjugate is identically `-∞`. -/
theorem pairingBiconjugate_eq_bot_of_not_isProxBounded
    (hgrowth : ∀ y, ∃ a : ℝ, ∀ x, q y x ≤ a * ‖x‖ ^ 2) {f : E → EReal}
    (hf : ¬ IsProxBounded f) :
    pairingConjugate (Function.swap (quadraticCoupling v q))
      (pairingConjugate (quadraticCoupling v q) f) = fun _ ↦ ⊥ := by
  rw [pairingConjugate_eq_top_of_not_isProxBounded v q hgrowth hf]
  funext x
  apply le_antisymm _ bot_le
  apply iSup_le
  intro y
  simp

/-- The biconjugate is a lower semicontinuous minorant, hence lies below the
lower closure. -/
theorem pairingBiconjugate_le_epiClosure (hcont : ∀ y, Continuous (q y)) (f : E → EReal) :
    pairingConjugate (Function.swap (quadraticCoupling v q))
      (pairingConjugate (quadraticCoupling v q) f) ≤ epiClosure f := by
  have hlsc := lowerSemicontinuous_pairingConjugate (Function.swap (quadraticCoupling v q))
    (fun y ↦ (continuous_const.inner continuous_id).sub (hcont y))
    (pairingConjugate (quadraticCoupling v q) f)
  have hle := pairingBiconjugate_le (quadraticCoupling v q) f
  rw [← epigraph_subset_epigraph_iff, epigraph_epiClosure]
  exact closure_minimal (epigraph_subset_epigraph_iff.mpr hle) (isClosed_epigraph_of_lsc_ereal _ hlsc)

omit [InnerProductSpace ℝ E] in
/-- A prox-bounded function lying above a level near a point has a quadratic
minorant at that level, centred at the point. -/
theorem exists_quadratic_minorant_near {f : E → EReal} {μ γ : ℝ} {b : E} (hμ : 0 < μ)
    (hmin : ∀ w, ((γ - 1 / (2 * μ) * ‖w - b‖ ^ 2 : ℝ) : EReal) ≤ f w) {x : E} {β δ : ℝ}
    (hδ : 0 < δ) (hnear : ∀ z, dist z x < δ → (β : EReal) ≤ f z) :
    ∃ r > 0, ∀ z, ((β - r / 2 * ‖z - x‖ ^ 2 : ℝ) : EReal) ≤ f z := by
  set M := max 0 (β - γ + ‖x - b‖ ^ 2 / μ) with hM_def
  have hM0 : 0 ≤ M := le_max_left _ _
  have hM : β - γ + ‖x - b‖ ^ 2 / μ ≤ M := le_max_right _ _
  refine ⟨2 / μ + 2 * M / δ ^ 2, by positivity, fun z ↦ ?_⟩
  by_cases hz : dist z x < δ
  · refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hnear z hz)
    have : 0 ≤ (2 / μ + 2 * M / δ ^ 2) / 2 * ‖z - x‖ ^ 2 := by positivity
    linarith
  · push_neg at hz
    rw [dist_eq_norm] at hz
    refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hmin z)
    have hzb : ‖z - b‖ ^ 2 ≤ 2 * ‖z - x‖ ^ 2 + 2 * ‖x - b‖ ^ 2 := by
      have h := norm_add_le (z - x) (x - b)
      rw [sub_add_sub_cancel] at h
      nlinarith [mul_le_mul h h (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)),
        sq_nonneg (‖z - x‖ - ‖x - b‖)]
    have hs2 : δ ^ 2 ≤ ‖z - x‖ ^ 2 := by nlinarith
    have hMs : M ≤ M / δ ^ 2 * ‖z - x‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    have h1 : 1 / (2 * μ) * ‖z - b‖ ^ 2 ≤ 1 / μ * ‖z - x‖ ^ 2 + ‖x - b‖ ^ 2 / μ := by
      have h := mul_le_mul_of_nonneg_left hzb (by positivity : (0:ℝ) ≤ 1 / (2 * μ))
      have he : 1 / (2 * μ) * (2 * ‖z - x‖ ^ 2 + 2 * ‖x - b‖ ^ 2) =
          1 / μ * ‖z - x‖ ^ 2 + ‖x - b‖ ^ 2 / μ := by
        field_simp
      linarith
    have he : (2 / μ + 2 * M / δ ^ 2) / 2 * ‖z - x‖ ^ 2 =
        1 / μ * ‖z - x‖ ^ 2 + M / δ ^ 2 * ‖z - x‖ ^ 2 := by
      field_simp
    rw [he]
    linarith

/-- For a prox-bounded function the lower closure lies below the biconjugate,
as soon as all the couplings `⟨w,x⟩ - (r/2)|x|²` with `r > 0` are available. -/
theorem epiClosure_le_pairingBiconjugate
    (hscal : ∀ r : ℝ, 0 < r → ∀ w : E, ∃ y, v y = w ∧ ∀ x, q y x = r / 2 * ‖x‖ ^ 2)
    {f : E → EReal} (hf : IsProxBounded f) :
    epiClosure f ≤ pairingConjugate (Function.swap (quadraticCoupling v q))
      (pairingConjugate (quadraticCoupling v q) f) := by
  intro x
  obtain ⟨μ, hμ, b, γ, hmin⟩ := exists_quadratic_minorant_of_isProxBounded hf
  by_contra hcon
  push_neg at hcon
  obtain ⟨β, hβ1, hβ2⟩ := EReal.exists_between_coe_real hcon
  have hnot : (x, β) ∉ closure (epigraph f) := by
    rw [← epigraph_epiClosure]
    exact fun h ↦ (not_le_of_gt hβ2) h
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl (x, β) hnot
  have hnear : ∀ z, dist z x < δ → (β : EReal) ≤ f z := by
    intro z hz
    have hz' : (z, β) ∈ ball (x, β) δ := by
      rw [mem_ball, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hz
    have hne : (z, β) ∉ epigraph f := fun h ↦ hball hz' (subset_closure h)
    exact (lt_of_not_ge hne).le
  obtain ⟨r, hr, hq⟩ := exists_quadratic_minorant_near hμ hmin hδ hnear
  obtain ⟨y, hvy, hqy⟩ := hscal r hr (r • x)
  have hconj : pairingConjugate (quadraticCoupling v q) f y ≤ ((r / 2 * ‖x‖ ^ 2 - β : ℝ) : EReal) := by
    apply iSup_le
    intro z
    rw [coe_sub_le_coe_iff]
    refine le_trans (le_of_eq ?_) (hq z)
    congr 1
    simp only [quadraticCoupling, hvy, hqy, real_inner_smul_left, norm_sub_sq_real, real_inner_comm x z]
    ring
  have hbi : (β : EReal) ≤ pairingConjugate (Function.swap (quadraticCoupling v q))
      (pairingConjugate (quadraticCoupling v q) f) x := by
    refine le_trans ?_ (le_iSup (fun y ↦ ((Function.swap (quadraticCoupling v q) y x : ℝ) : EReal) -
      pairingConjugate (quadraticCoupling v q) f y) y)
    calc (β : EReal) = ((quadraticCoupling v q x y : ℝ) : EReal) -
          ((r / 2 * ‖x‖ ^ 2 - β : ℝ) : EReal) := by
          rw [← EReal.coe_sub]
          congr 1
          simp only [quadraticCoupling, hvy, hqy, real_inner_smul_left, real_inner_self_eq_norm_sq]
          ring
      _ ≤ _ := EReal.sub_le_sub le_rfl hconj
  exact (not_le_of_gt hβ1) hbi

/-- The biconjugate of a prox-bounded function is its lower closure. -/
theorem pairingBiconjugate_eq_epiClosure (hcont : ∀ y, Continuous (q y))
    (hscal : ∀ r : ℝ, 0 < r → ∀ w : E, ∃ y, v y = w ∧ ∀ x, q y x = r / 2 * ‖x‖ ^ 2)
    {f : E → EReal} (hf : IsProxBounded f) :
    pairingConjugate (Function.swap (quadraticCoupling v q))
      (pairingConjugate (quadraticCoupling v q) f) = epiClosure f :=
  le_antisymm (pairingBiconjugate_le_epiClosure v q hcont f) (epiClosure_le_pairingBiconjugate v q hscal hf)

/-- Away from the two extreme cases the conjugate is proper. -/
theorem isProper_pairingConjugate_quadraticCoupling
    (hscal : ∀ r : ℝ, 0 < r → ∀ w : E, ∃ y, v y = w ∧ ∀ x, q y x = r / 2 * ‖x‖ ^ 2)
    {f : E → EReal} (hf : IsProxBounded f) (hdom : ∃ x, f x < ⊤) :
    IsProper (pairingConjugate (quadraticCoupling v q) f) := by
  obtain ⟨μ, hμ, b, γ, hmin⟩ := exists_quadratic_minorant_of_isProxBounded hf
  obtain ⟨x₀, hx₀⟩ := hdom
  refine ⟨?_, fun y ↦ ?_⟩
  · obtain ⟨y, hvy, hqy⟩ := hscal (1 / μ) (by positivity) ((1 / μ) • b)
    refine ⟨y, lt_of_le_of_lt (b := ((‖b‖ ^ 2 / (2 * μ) - γ : ℝ) : EReal)) ?_ (EReal.coe_lt_top _)⟩
    apply iSup_le
    intro z
    rw [coe_sub_le_coe_iff]
    refine le_trans (le_of_eq ?_) (hmin z)
    congr 1
    simp only [quadraticCoupling, hvy, hqy, real_inner_smul_left, norm_sub_sq_real, real_inner_comm b z]
    field_simp
    ring
  · have h := le_iSup (fun x ↦ ((quadraticCoupling v q x y : ℝ) : EReal) - f x) x₀
    refine lt_of_lt_of_le ?_ h
    cases hfx : f x₀ with
    | bot => simp
    | top => rw [hfx] at hx₀; exact absurd hx₀ (lt_irrefl _)
    | coe a => rw [← EReal.coe_sub]; exact EReal.bot_lt_coe _

omit [InnerProductSpace ℝ E] in
theorem bot_lt_of_isProxBounded {f : E → EReal} (hf : IsProxBounded f) (x : E) : ⊥ < f x := by
  obtain ⟨μ, -, b, γ, hmin⟩ := exists_quadratic_minorant_of_isProxBounded hf
  exact (EReal.bot_lt_coe _).trans_le (hmin x)

/-- The one-to-one correspondence between the proper, lower semicontinuous,
prox-bounded functions and the proper envelope functions on the parameter space,
given in both directions by the generalized conjugacy. -/
noncomputable def quadraticTransformEquiv (hcont : ∀ y, Continuous (q y))
    (hgrowth : ∀ y, ∃ a : ℝ, ∀ x, q y x ≤ a * ‖x‖ ^ 2)
    (hscal : ∀ r : ℝ, 0 < r → ∀ w : E, ∃ y, v y = w ∧ ∀ x, q y x = r / 2 * ‖x‖ ^ 2) :
    {f : E → EReal // IsProper f ∧ LowerSemicontinuous f ∧ IsProxBounded f} ≃
      {g : Y → EReal // IsProper g ∧ IsPairingEnvelope (Function.swap (quadraticCoupling v q)) g} where
  toFun f := ⟨pairingConjugate (quadraticCoupling v q) f.val,
    isProper_pairingConjugate_quadraticCoupling v q hscal f.property.2.2 f.property.1.1,
    isPairingEnvelope_conjugate _ _⟩
  invFun g := by
    refine ⟨pairingConjugate (Function.swap (quadraticCoupling v q)) g.val, ?_⟩
    have hg : pairingConjugate (quadraticCoupling v q)
        (pairingConjugate (Function.swap (quadraticCoupling v q)) g.val) = g.val :=
      (isPairingEnvelope_iff_biconjugate (Function.swap (quadraticCoupling v q)) g.val).mp g.property.2
    have hpb : IsProxBounded (pairingConjugate (Function.swap (quadraticCoupling v q)) g.val) := by
      by_contra hn
      obtain ⟨y, hy⟩ := g.property.1.1
      rw [← hg, pairingConjugate_eq_top_of_not_isProxBounded v q hgrowth hn] at hy
      exact lt_irrefl _ hy
    have henv := isPairingEnvelope_conjugate (Function.swap (quadraticCoupling v q)) g.val
    have hfix := (isPairingEnvelope_iff_biconjugate (quadraticCoupling v q) _).mp henv
    rw [pairingBiconjugate_eq_epiClosure v q hcont hscal hpb] at hfix
    refine ⟨⟨?_, bot_lt_of_isProxBounded hpb⟩, hfix ▸ lowerSemicontinuous_epiLowerLimit _, hpb⟩
    by_contra hn
    push_neg at hn
    have htop : ∀ x, pairingConjugate (Function.swap (quadraticCoupling v q)) g.val x = ⊤ :=
      fun x ↦ top_le_iff.mp (hn x)
    obtain ⟨y, -⟩ := g.property.1.1
    have hb := g.property.1.2 y
    rw [← hg, pairingConjugate_quadraticCoupling_of_top v q _ htop] at hb
    exact lt_irrefl _ hb
  left_inv f := by
    apply Subtype.ext
    change pairingConjugate (Function.swap (quadraticCoupling v q))
      (pairingConjugate (quadraticCoupling v q) f.val) = f.val
    rw [pairingBiconjugate_eq_epiClosure v q hcont hscal f.property.2.2,
      epiClosure_eq_of_lowerSemicontinuous f.property.2.1]
  right_inv g := Subtype.ext
    ((isPairingEnvelope_iff_biconjugate (Function.swap (quadraticCoupling v q)) g.val).mp g.property.2)

/-- Envelope functions on the parameter space are conjugates, hence lower
semicontinuous with convex epigraphs whenever the coupling is continuous and
affine in the parameter. -/
theorem isPairingEnvelope_quadraticCoupling_regular [TopologicalSpace Y] [AddCommGroup Y] [Module ℝ Y]
    (hc : ∀ x, Continuous (fun y ↦ quadraticCoupling v q x y))
    (ha : ∀ x (y₁ y₂ : Y) (a b : ℝ), a + b = 1 →
      quadraticCoupling v q x (a • y₁ + b • y₂) = a * quadraticCoupling v q x y₁ + b * quadraticCoupling v q x y₂)
    {g : Y → EReal} (hg : IsPairingEnvelope (Function.swap (quadraticCoupling v q)) g) :
    LowerSemicontinuous g ∧ Convex ℝ (epigraph g) := by
  have he := (isPairingEnvelope_iff_biconjugate (Function.swap (quadraticCoupling v q)) g).mp hg
  rw [← he]
  exact ⟨lowerSemicontinuous_pairingConjugate _ hc _, convex_epigraph_pairingConjugate _ ha _⟩

end General

section Basic

/-- The coupling `Φ(x,(v,r)) = ⟨v,x⟩ - r j(x)` with `j = ½|·|²` of Example 11.66. -/
noncomputable def basicQuadraticCoupling : E → E × ℝ → ℝ :=
  quadraticCoupling Prod.fst (fun y x ↦ y.2 * (1 / 2 * ‖x‖ ^ 2))

omit [InnerProductSpace ℝ E] in
private theorem basic_hcont : ∀ y : E × ℝ, Continuous (fun x : E ↦ y.2 * (1 / 2 * ‖x‖ ^ 2)) :=
  fun _ ↦ by fun_prop

omit [InnerProductSpace ℝ E] in
private theorem basic_hgrowth :
    ∀ y : E × ℝ, ∃ a : ℝ, ∀ x : E, y.2 * (1 / 2 * ‖x‖ ^ 2) ≤ a * ‖x‖ ^ 2 :=
  fun y ↦ ⟨y.2 / 2, fun x ↦ le_of_eq (by ring)⟩

omit [InnerProductSpace ℝ E] in
private theorem basic_hscal : ∀ r : ℝ, 0 < r → ∀ w : E, ∃ y : E × ℝ,
    y.1 = w ∧ ∀ x : E, y.2 * (1 / 2 * ‖x‖ ^ 2) = r / 2 * ‖x‖ ^ 2 :=
  fun r _ w ↦ ⟨(w, r), rfl, fun x ↦ by ring⟩

private theorem basic_continuous (x : E) :
    Continuous (fun y : E × ℝ ↦ basicQuadraticCoupling x y) := by
  unfold basicQuadraticCoupling quadraticCoupling
  fun_prop

private theorem basic_affine (x : E) (y₁ y₂ : E × ℝ) (a b : ℝ) (_ : a + b = 1) :
    basicQuadraticCoupling x (a • y₁ + b • y₂) =
      a * basicQuadraticCoupling x y₁ + b * basicQuadraticCoupling x y₂ := by
  simp only [basicQuadraticCoupling, quadraticCoupling, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, inner_add_left, real_inner_smul_left]
  ring

/-- **Example 11.66**, the basic quadratic transform. The conjugate is
`f^Φ(v,r) = (f + r j)*(v)`, the biconjugate is `cl f` for prox-bounded `f` and
`-∞` otherwise, `f^Φ ≡ -∞` when `f ≡ ∞`, `f^Φ ≡ ∞` when `f` is not
prox-bounded, and otherwise `f^Φ` is proper; it is always lower semicontinuous
and convex on `ℝⁿ × ℝ`. -/
theorem basicQuadraticTransform (f : E → EReal) :
    (∀ (v : E) (r : ℝ), pairingConjugate basicQuadraticCoupling f (v, r) =
        fenchelConjugate (fun x ↦ f x + ((r * (1 / 2 * ‖x‖ ^ 2) : ℝ) : EReal)) v) ∧
    (IsProxBounded f → pairingConjugate (Function.swap basicQuadraticCoupling)
        (pairingConjugate basicQuadraticCoupling f) = epiClosure f) ∧
    (¬ IsProxBounded f → pairingConjugate (Function.swap basicQuadraticCoupling)
        (pairingConjugate basicQuadraticCoupling f) = fun _ ↦ ⊥) ∧
    ((∀ x, f x = ⊤) → pairingConjugate basicQuadraticCoupling f = fun _ ↦ ⊥) ∧
    (¬ IsProxBounded f → pairingConjugate basicQuadraticCoupling f = fun _ ↦ ⊤) ∧
    (IsProxBounded f → (∃ x, f x < ⊤) → IsProper (pairingConjugate basicQuadraticCoupling f)) ∧
    LowerSemicontinuous (pairingConjugate basicQuadraticCoupling f) ∧
    Convex ℝ (epigraph (pairingConjugate basicQuadraticCoupling f)) :=
  ⟨fun v r ↦ pairingConjugate_quadraticCoupling Prod.fst _ f (v, r),
    pairingBiconjugate_eq_epiClosure Prod.fst _ basic_hcont basic_hscal,
    pairingBiconjugate_eq_bot_of_not_isProxBounded Prod.fst _ basic_hgrowth,
    pairingConjugate_quadraticCoupling_of_top Prod.fst _ f,
    pairingConjugate_eq_top_of_not_isProxBounded Prod.fst _ basic_hgrowth,
    isProper_pairingConjugate_quadraticCoupling Prod.fst _ basic_hscal,
    lowerSemicontinuous_pairingConjugate _ basic_continuous f,
    convex_epigraph_pairingConjugate _ basic_affine f⟩

/-- **Example 11.66**, the one-to-one correspondence between proper, lower
semicontinuous, prox-bounded functions on `ℝⁿ` and the proper envelope
functions on `ℝⁿ × ℝ`. -/
noncomputable def basicQuadraticTransformEquiv :
    {f : E → EReal // IsProper f ∧ LowerSemicontinuous f ∧ IsProxBounded f} ≃
      {g : E × ℝ → EReal // IsProper g ∧
        IsPairingEnvelope (Function.swap (basicQuadraticCoupling (E := E))) g} :=
  quadraticTransformEquiv Prod.fst _ basic_hcont basic_hgrowth basic_hscal

/-- **Example 11.66**, the functions on `ℝⁿ × ℝ` in the correspondence are
lower semicontinuous and convex. -/
theorem basicQuadraticTransformEquiv_regular
    (f : {f : E → EReal // IsProper f ∧ LowerSemicontinuous f ∧ IsProxBounded f}) :
    (basicQuadraticTransformEquiv f).val = pairingConjugate basicQuadraticCoupling f.val ∧
      IsProper (basicQuadraticTransformEquiv f).val ∧
      LowerSemicontinuous (basicQuadraticTransformEquiv f).val ∧
      Convex ℝ (epigraph (basicQuadraticTransformEquiv f).val) :=
  ⟨rfl, (basicQuadraticTransformEquiv f).property.1,
    isPairingEnvelope_quadraticCoupling_regular Prod.fst _ basic_continuous basic_affine
      (basicQuadraticTransformEquiv f).property.2⟩

end Basic

section Full

/-- The symmetric continuous linear operators, the coordinate-free form of the
space `ℝⁿˣⁿ_sym` of symmetric matrices. -/
noncomputable def symmetricOperators : Submodule ℝ (E →L[ℝ] E) where
  carrier := {A | (A : E →ₗ[ℝ] E).IsSymmetric}
  add_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq, ContinuousLinearMap.coe_add] at *
    exact hA.add hB
  zero_mem' := by
    intro x y
    simp
  smul_mem' c A hA := by
    intro x y
    change ⟪c • A x, y⟫_ℝ = ⟪x, c • A y⟫_ℝ
    rw [real_inner_smul_left, real_inner_smul_right]
    exact congrArg (c * ·) (hA x y)

/-- The coupling `Φ(x,(v,Q)) = ⟨v,x⟩ - j_Q(x)` with `j_Q(x) = ½⟨x,Qx⟩` of
Example 11.65. -/
noncomputable def fullQuadraticCoupling : E → E × symmetricOperators (E := E) → ℝ :=
  quadraticCoupling Prod.fst (fun y x ↦ 1 / 2 * ⟪x, (y.2 : E →L[ℝ] E) x⟫_ℝ)

private theorem full_hcont : ∀ y : E × symmetricOperators (E := E),
    Continuous (fun x : E ↦ 1 / 2 * ⟪x, (y.2 : E →L[ℝ] E) x⟫_ℝ) :=
  fun y ↦ continuous_const.mul (continuous_id.inner (y.2 : E →L[ℝ] E).continuous)

private theorem full_hgrowth : ∀ y : E × symmetricOperators (E := E),
    ∃ a : ℝ, ∀ x : E, 1 / 2 * ⟪x, (y.2 : E →L[ℝ] E) x⟫_ℝ ≤ a * ‖x‖ ^ 2 := by
  intro y
  refine ⟨‖(y.2 : E →L[ℝ] E)‖ / 2, fun x ↦ ?_⟩
  have h1 := real_inner_le_norm x ((y.2 : E →L[ℝ] E) x)
  have h2 := (y.2 : E →L[ℝ] E).le_opNorm x
  have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg x)
  nlinarith [norm_nonneg x]

private theorem full_hscal : ∀ r : ℝ, 0 < r → ∀ w : E, ∃ y : E × symmetricOperators (E := E),
    y.1 = w ∧ ∀ x : E, 1 / 2 * ⟪x, (y.2 : E →L[ℝ] E) x⟫_ℝ = r / 2 * ‖x‖ ^ 2 := by
  intro r _ w
  have hmem : r • (1 : E →L[ℝ] E) ∈ symmetricOperators (E := E) := by
    intro x y
    change ⟪r • x, y⟫_ℝ = ⟪x, r • y⟫_ℝ
    rw [real_inner_smul_left, real_inner_smul_right]
  refine ⟨(w, ⟨r • (1 : E →L[ℝ] E), hmem⟩), rfl, fun x ↦ ?_⟩
  change 1 / 2 * ⟪x, r • x⟫_ℝ = r / 2 * ‖x‖ ^ 2
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

private theorem full_continuous (x : E) :
    Continuous (fun y : E × symmetricOperators (E := E) ↦ fullQuadraticCoupling x y) := by
  unfold fullQuadraticCoupling quadraticCoupling
  have h : Continuous (fun y : E × symmetricOperators (E := E) ↦ (y.2 : E →L[ℝ] E) x) :=
    (continuous_subtype_val.comp continuous_snd).clm_apply continuous_const
  exact (continuous_fst.inner continuous_const).sub (continuous_const.mul (continuous_const.inner h))

private theorem full_affine (x : E) (y₁ y₂ : E × symmetricOperators (E := E)) (a b : ℝ)
    (_ : a + b = 1) :
    fullQuadraticCoupling x (a • y₁ + b • y₂) =
      a * fullQuadraticCoupling x y₁ + b * fullQuadraticCoupling x y₂ := by
  simp only [fullQuadraticCoupling, quadraticCoupling, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, Submodule.coe_add, Submodule.coe_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  ring

/-- **Example 11.65**, the full quadratic transform. The conjugate is
`f^Φ(v,Q) = (f + j_Q)*(v)`, the biconjugate is `cl f` for prox-bounded `f` and
`-∞` otherwise, `f^Φ ≡ -∞` when `f ≡ ∞`, `f^Φ ≡ ∞` when `f` is not
prox-bounded, and otherwise `f^Φ` is proper; it is always lower semicontinuous
and convex on `ℝⁿ × ℝⁿˣⁿ_sym`. -/
theorem fullQuadraticTransform (f : E → EReal) :
    (∀ (v : E) (Q : symmetricOperators (E := E)), pairingConjugate fullQuadraticCoupling f (v, Q) =
        fenchelConjugate (fun x ↦ f x + ((1 / 2 * ⟪x, (Q : E →L[ℝ] E) x⟫_ℝ : ℝ) : EReal)) v) ∧
    (IsProxBounded f → pairingConjugate (Function.swap fullQuadraticCoupling)
        (pairingConjugate fullQuadraticCoupling f) = epiClosure f) ∧
    (¬ IsProxBounded f → pairingConjugate (Function.swap fullQuadraticCoupling)
        (pairingConjugate fullQuadraticCoupling f) = fun _ ↦ ⊥) ∧
    ((∀ x, f x = ⊤) → pairingConjugate fullQuadraticCoupling f = fun _ ↦ ⊥) ∧
    (¬ IsProxBounded f → pairingConjugate fullQuadraticCoupling f = fun _ ↦ ⊤) ∧
    (IsProxBounded f → (∃ x, f x < ⊤) → IsProper (pairingConjugate fullQuadraticCoupling f)) ∧
    LowerSemicontinuous (pairingConjugate fullQuadraticCoupling f) ∧
    Convex ℝ (epigraph (pairingConjugate fullQuadraticCoupling f)) :=
  ⟨fun v Q ↦ pairingConjugate_quadraticCoupling Prod.fst _ f (v, Q),
    pairingBiconjugate_eq_epiClosure Prod.fst _ full_hcont full_hscal,
    pairingBiconjugate_eq_bot_of_not_isProxBounded Prod.fst _ full_hgrowth,
    pairingConjugate_quadraticCoupling_of_top Prod.fst _ f,
    pairingConjugate_eq_top_of_not_isProxBounded Prod.fst _ full_hgrowth,
    isProper_pairingConjugate_quadraticCoupling Prod.fst _ full_hscal,
    lowerSemicontinuous_pairingConjugate _ full_continuous f,
    convex_epigraph_pairingConjugate _ full_affine f⟩

/-- **Example 11.65**, the one-to-one correspondence between proper, lower
semicontinuous, prox-bounded functions on `ℝⁿ` and the proper envelope
functions on `ℝⁿ × ℝⁿˣⁿ_sym`. -/
noncomputable def fullQuadraticTransformEquiv :
    {f : E → EReal // IsProper f ∧ LowerSemicontinuous f ∧ IsProxBounded f} ≃
      {g : E × symmetricOperators (E := E) → EReal // IsProper g ∧
        IsPairingEnvelope (Function.swap (fullQuadraticCoupling (E := E))) g} :=
  quadraticTransformEquiv Prod.fst _ full_hcont full_hgrowth full_hscal

/-- **Example 11.65**, the functions on `ℝⁿ × ℝⁿˣⁿ_sym` in the correspondence
are lower semicontinuous and convex. -/
theorem fullQuadraticTransformEquiv_regular
    (f : {f : E → EReal // IsProper f ∧ LowerSemicontinuous f ∧ IsProxBounded f}) :
    (fullQuadraticTransformEquiv f).val = pairingConjugate fullQuadraticCoupling f.val ∧
      IsProper (fullQuadraticTransformEquiv f).val ∧
      LowerSemicontinuous (fullQuadraticTransformEquiv f).val ∧
      Convex ℝ (epigraph (fullQuadraticTransformEquiv f).val) :=
  ⟨rfl, (fullQuadraticTransformEquiv f).property.1,
    isPairingEnvelope_quadraticCoupling_regular Prod.fst _ full_continuous full_affine
      (fullQuadraticTransformEquiv f).property.2⟩

/-- **Example 11.66** as a restriction of 11.65: the basic coupling is the full
coupling at the scalar matrices `Q = rI`. -/
theorem basicQuadraticCoupling_eq_full (x v : E) (r : ℝ) (hr : r • (1 : E →L[ℝ] E) ∈ symmetricOperators (E := E)) :
    basicQuadraticCoupling x (v, r) = fullQuadraticCoupling x (v, ⟨r • (1 : E →L[ℝ] E), hr⟩) := by
  change ⟪v, x⟫_ℝ - r * (1 / 2 * ‖x‖ ^ 2) = ⟪v, x⟫_ℝ - 1 / 2 * ⟪x, r • x⟫_ℝ
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

end Full

end RW
