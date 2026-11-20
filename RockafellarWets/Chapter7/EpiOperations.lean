/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Transformations and sums of epi-convergent functions
-/

import RockafellarWets.Chapter7.EpiLimitCharacterization
import Mathlib.Topology.Order.MonotoneConvergence

open Filter Function Set Topology

namespace RW

section Transformations

variable {E : Type*} [PseudoMetricSpace E] {f : ℕ → E → EReal} {g : E → EReal}

/-- A continuously varying transformation, eventually monotone in height,
preserves epi-convergence. The transformation may also depend on position. -/
theorem EpiConverges.transform (h : EpiConverges f g)
    {T : ℕ → E → EReal → EReal} {S : E → EReal → EReal}
    (hm : ∀ᶠ n in atTop, ∀ x, Monotone (T n x))
    (hc : ∀ {x : E} {a : EReal} {y : ℕ → E} {b : ℕ → EReal},
      Tendsto y atTop (𝓝 x) → Tendsto b atTop (𝓝 a) →
      Tendsto (fun n ↦ T n (y n) (b n)) atTop (𝓝 (S x a))) :
    EpiConverges (fun n x ↦ T n x (f n x)) (fun x ↦ S x (g x)) := by
  apply epiConverges_iff_liminf_limsup.mpr
  intro x
  constructor
  · intro y hy
    let v (n : ℕ) := f n (y n)
    have hlow : g x ≤ liminf v atTop := (epiConverges_iff_liminf_limsup.mp h x).1 y hy
    have ht : Tendsto (fun n ↦ min (v n) (g x)) atTop (𝓝 (g x)) := by
      apply tendsto_of_le_liminf_of_limsup_le
      · rw [liminf_min, liminf_const]
        exact le_min hlow le_rfl
      · exact limsup_le_of_le (by isBoundedDefault) (.of_forall fun _ ↦ min_le_right _ _)
      all_goals isBoundedDefault
    rw [← (hc hy ht).liminf_eq]
    exact liminf_le_liminf (hm.mono fun n hn ↦ hn _ (min_le_left _ _))
  · obtain ⟨y, hy, hv⟩ := h.exists_tendsto_values x
    exact ⟨y, hy, (hc hy hv).limsup_eq.le⟩

/-- **Exercise 7.8(a).** Addition of a finite continuous function. -/
theorem EpiConverges.add_continuous (h : EpiConverges f g) {u : E → ℝ} (hu : Continuous u) :
    EpiConverges (fun n x ↦ f n x + (u x : EReal)) (fun x ↦ g x + (u x : EReal)) := by
  apply h.transform (T := fun _ x a ↦ a + (u x : EReal)) (S := fun x a ↦ a + (u x : EReal))
    (.of_forall fun _ _ _ _ hab ↦ add_le_add_left hab _)
  intro x a y b hy hb
  exact (EReal.continuousAt_add (p := (a, (u x : EReal)))
    (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))).tendsto.comp
    (hb.prodMk_nhds (continuous_coe_real_ereal.continuousAt.tendsto.comp ((hu.tendsto _).comp hy)))

/-- **Exercise 7.8(b).** Change of variables through a homeomorphism. -/
theorem EpiConverges.comp_homeomorph {F : Type*} [PseudoMetricSpace F]
    (h : EpiConverges f g) (e : F ≃ₜ E) :
    EpiConverges (fun n ↦ f n ∘ e) (g ∘ e) := by
  apply epiConverges_iff_liminf_limsup.mpr
  intro x
  obtain ⟨hlo, y, hy, hv⟩ := epiConverges_iff_liminf_limsup.mp h (e x)
  refine ⟨fun z hz ↦ hlo (e ∘ z) ((e.continuous.tendsto _).comp hz), e.symm ∘ y, ?_, ?_⟩
  · simpa using (e.symm.continuous.tendsto _).comp hy
  · simpa only [comp_apply, Homeomorph.apply_symm_apply] using hv

/-- **Exercise 7.8(c).** Composition with a continuous increasing function
on the extended real line. -/
theorem EpiConverges.comp_monotone (h : EpiConverges f g) {θ : EReal → EReal}
    (hm : Monotone θ) (hc : Continuous θ) :
    EpiConverges (fun n ↦ θ ∘ f n) (θ ∘ g) :=
  h.transform (T := fun _ _ ↦ θ) (.of_forall fun _ _ ↦ hm)
    (fun _ hb ↦ (hc.tendsto _).comp hb)

end Transformations

/-- The extension used in Exercise 7.8(c) takes the full infimum and supremum
as its endpoint values. -/
noncomputable def monotoneERealExtension (θ : ℝ → ℝ) : EReal → EReal :=
  EReal.rec (⨅ r : ℝ, (θ r : EReal)) (fun r ↦ (θ r : EReal)) (⨆ r : ℝ, (θ r : EReal))

theorem monotone_monotoneERealExtension {θ : ℝ → ℝ} (hm : Monotone θ) :
    Monotone (monotoneERealExtension θ) := by
  intro x y hxy
  cases x with
  | bot =>
    cases y with
    | bot => exact le_rfl
    | coe r => exact iInf_le _ r
    | top => exact (iInf_le _ (0 : ℝ)).trans (le_iSup (fun r : ℝ ↦ (θ r : EReal)) 0)
  | coe r =>
    cases y with
    | bot => exact ((EReal.bot_lt_coe r).not_ge hxy).elim
    | coe s => exact EReal.coe_le_coe_iff.mpr (hm (EReal.coe_le_coe_iff.mp hxy))
    | top => exact le_iSup (fun r : ℝ ↦ (θ r : EReal)) r
  | top =>
    have hy := top_unique hxy
    rw [hy]


theorem continuous_monotoneERealExtension {θ : ℝ → ℝ} (hm : Monotone θ) (hc : Continuous θ) :
    Continuous (monotoneERealExtension θ) := by
  have hmono : Monotone (fun r ↦ (θ r : EReal)) := fun _ _ h ↦ EReal.coe_le_coe_iff.mpr (hm h)
  apply continuous_iff_continuousAt.mpr
  intro x
  cases x with
  | bot =>
    rw [← continuousWithinAt_compl_self]
    change Tendsto _ (𝓝[≠] (⊥ : EReal)) _
    rw [EReal.nhdsWithin_bot, tendsto_map'_iff]
    exact tendsto_atBot_iInf hmono
  | coe r =>
    change Tendsto _ (𝓝 (r : EReal)) _
    rw [EReal.nhds_coe, tendsto_map'_iff]
    exact (continuous_coe_real_ereal.comp hc).tendsto _
  | top =>
    rw [← continuousWithinAt_compl_self]
    change Tendsto _ (𝓝[≠] (⊤ : EReal)) _
    rw [EReal.nhdsWithin_top, tendsto_map'_iff]
    exact tendsto_atTop_iSup hmono

/-- **Exercise 7.8(d).** Varying translations in the domain and affine
changes of scale in the values. Positivity is needed only at the limit. -/
theorem EpiConverges.affine_perturbation {E : Type*} [NormedAddCommGroup E]
    {f : ℕ → E → EReal} {g : E → EReal} (h : EpiConverges f g)
    {a : ℕ → E} {z : E} {c d : ℕ → ℝ} {s t : ℝ} (hs : 0 < s)
    (ha : Tendsto a atTop (𝓝 z)) (hc : Tendsto c atTop (𝓝 s)) (hd : Tendsto d atTop (𝓝 t)) :
    EpiConverges (fun n x ↦ (c n : EReal) * f n (x + a n) + (d n : EReal))
      (fun x ↦ (s : EReal) * g (x + z) + (t : EReal)) := by
  have hshift : EpiConverges (fun n x ↦ f n (x + a n)) (fun x ↦ g (x + z)) := by
    apply epiConverges_iff_liminf_limsup.mpr
    intro x
    obtain ⟨hlo, y, hy, hv⟩ := epiConverges_iff_liminf_limsup.mp h (x + z)
    exact ⟨fun w hw ↦ hlo _ (hw.add ha), fun n ↦ y n - a n,
      by simpa using hy.sub ha, by simpa only [sub_add_cancel] using hv⟩
  apply hshift.transform (T := fun n _ v ↦ (c n : EReal) * v + (d n : EReal))
    (S := fun _ v ↦ (s : EReal) * v + (t : EReal))
  · filter_upwards [hc.eventually_const_lt hs] with n hn x u v huv
    exact add_le_add_left (mul_le_mul_of_nonneg_left huv (by exact_mod_cast hn.le)) _
  · intro x u y v _ hv
    have hs' : (s : EReal) ≠ 0 := by exact_mod_cast hs.ne'
    have hmul := EReal.Tendsto.mul (continuous_coe_real_ereal.continuousAt.tendsto.comp hc) hv
      (.inl hs') (.inl hs') (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
    exact (EReal.continuousAt_add (p := ((s : EReal) * u, (t : EReal)))
      (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))).tendsto.comp
      (hmul.prodMk_nhds (continuous_coe_real_ereal.continuousAt.tendsto.comp hd))

section Addition

variable {E : Type*} [PseudoMetricSpace E]

/-- **Theorem 7.46.** Superadditivity of the lower epi-limit. -/
theorem add_epiLowerLimit_le (f h : ℕ → E → EReal) :
    epiLowerLimit f + epiLowerLimit h ≤ epiLowerLimit (fun n ↦ f n + h n) := by
  intro x
  obtain ⟨y, hy, heq⟩ := exists_tendsto_liminf_eq_epiLowerLimit (fun n ↦ f n + h n) x
  rw [← heq]
  exact (add_le_add (epiLowerLimit_le_liminf (f := f) hy)
    (epiLowerLimit_le_liminf (f := h) hy)).trans EReal.le_liminf_add

/-- Joint recovery sequences suffice for the sum when the limiting
functions are proper. -/
private theorem epiConverges_add_of_joint_recovery {f h : ℕ → E → EReal} {g k : E → EReal}
    (hf : EpiConverges f g) (hh : EpiConverges h k) (hg : IsProper g) (hk : IsProper k)
    (hr : ∀ x, ∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧ Tendsto (fun n ↦ f n (y n)) atTop (𝓝 (g x)) ∧
      Tendsto (fun n ↦ h n (y n)) atTop (𝓝 (k x))) :
    EpiConverges (fun n ↦ f n + h n) (g + k) := by
  apply epiConverges_iff_liminf_limsup.mpr
  intro x
  refine ⟨fun y hy ↦ (add_le_add ((epiConverges_iff_liminf_limsup.mp hf x).1 y hy)
    ((epiConverges_iff_liminf_limsup.mp hh x).1 y hy)).trans EReal.le_liminf_add, ?_⟩
  obtain ⟨y, hy, hf', hh'⟩ := hr x
  refine ⟨y, hy, ?_⟩
  exact ((EReal.continuousAt_add (p := (g x, k x)) (.inr (hk.2 x).ne') (.inl (hg.2 x).ne')).tendsto.comp
    (hf'.prodMk_nhds hh')).limsup_eq.le

/-- **Theorem 7.46(a).** Epi-convergence plus pointwise convergence for both
summands gives epi-convergence of their sum. -/
theorem epiConverges_add_of_pointwise {f h : ℕ → E → EReal} {g k : E → EReal}
    (hf : EpiConverges f g) (hh : EpiConverges h k) (hg : IsProper g) (hk : IsProper k)
    (hf' : ∀ x, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    (hh' : ∀ x, Tendsto (fun n ↦ h n x) atTop (𝓝 (k x))) :
    EpiConverges (fun n ↦ f n + h n) (g + k) :=
  epiConverges_add_of_joint_recovery hf hh hg hk fun x ↦
    ⟨fun _ ↦ x, tendsto_const_nhds, hf' x, hh' x⟩

/-- **Theorem 7.46(b).** Continuous convergence of the first summand supplies
a common recovery sequence. The symmetric case follows by commutativity. -/
theorem epiConverges_add_of_continuous_convergence {f h : ℕ → E → EReal} {g k : E → EReal}
    (hf : EpiConverges f g) (hh : EpiConverges h k) (hg : IsProper g) (hk : IsProper k)
    (hf' : ∀ x (y : ℕ → E), Tendsto y atTop (𝓝 x) →
      Tendsto (fun n ↦ f n (y n)) atTop (𝓝 (g x))) :
    EpiConverges (fun n ↦ f n + h n) (g + k) := by
  apply epiConverges_add_of_joint_recovery hf hh hg hk
  intro x
  obtain ⟨y, hy, hv⟩ := hh.exists_tendsto_values x
  exact ⟨y, hy, hf' x y hy, hv⟩

end Addition

end RW
