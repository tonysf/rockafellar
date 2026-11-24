/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Maximal monotonicity in one dimension

Exercise 12.9.

(a) A mapping `T : ℝ ⇉ ℝ` is monotone if and only if its graph is totally
ordered for the partial ordering of `ℝ²` induced by the cone `ℝ²₊`: any two
graph points `(x₀, v₀)` and `(x₁, v₁)` satisfy `x₀ ≤ x₁, v₀ ≤ v₁` or
`x₁ ≤ x₀, v₁ ≤ v₀`.  Maximal monotonicity is maximality of this chain.

(b) `T` is maximal monotone if and only if there is a nondecreasing
`φ : ℝ → ℝ̄`, neither identically `∞` nor identically `-∞`, with
`T(x) = {v ∈ ℝ | φ(x-) ≤ v ≤ φ(x+)}`, the one-sided limits being Mathlib's
`Function.leftLim` and `Function.rightLim` (`svMaximalMonotone_real_iff`).  The
variant `svMaximalMonotone_real_iff_tendsto` states the same with the one-sided
limits as `Tendsto` hypotheses.

For the necessity in (b) we follow the guide: with
`φ₊(x) = inf {v' | ∃ x' > x, v' ∈ T(x')}` and
`φ₋(x) = sup {v' | ∃ x' < x, v' ∈ T(x')}`, maximality gives
`T(x) = {v | φ₋(x) ≤ v ≤ φ₊(x)}`.  Then `φ = φ₊` works, with `φ(x+) = φ₊(x)` and
`φ(x-) = φ₋(x)`.  For the sufficiency, a pair comparable with the whole graph
but lying above `φ(x̂+)` forces `T` to be empty just right of `x̂`.  Then `φ = -∞`
up to the first point `s` where `φ` becomes finite, and the values of `T` at or
just beyond `s` contradict comparability.  The bound below `φ(x̂-)` is the
mirror argument.
-/

import RockafellarWets.Chapter12.MonotoneMappings
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Instances.EReal.Lemmas

open Set Filter Topology Function
open scoped InnerProductSpace

namespace RW

section OneDimension

/-- The inner product on `ℝ` is multiplication (a local copy of Chapter 10's
`real_inner_eq_mul'`, which is not imported here). -/
private theorem inner_real_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  simp [mul_comm]

/-- The monotonicity inequality on `ℝ`, by cases on the order of the points. -/
theorem inner_nonneg_real_iff {x v x' v' : ℝ} :
    0 ≤ ⟪v - v', x - x'⟫_ℝ ↔ (x' < x → v' ≤ v) ∧ (x < x' → v ≤ v') := by
  rw [inner_real_eq_mul]
  constructor
  · intro h
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · by_contra hv
      push_neg at hv
      nlinarith
    · by_contra hv
      push_neg at hv
      nlinarith
  · rintro ⟨h₁, h₂⟩
    rcases lt_trichotomy x' x with hx | rfl | hx
    · have := h₁ hx
      exact mul_nonneg (by linarith) (by linarith)
    · simp
    · have := h₂ hx
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- **Exercise 12.9(a).** A mapping `T : ℝ ⇉ ℝ` is monotone if and only if any
two of its graph points are ordered componentwise. -/
theorem svMonotone_real_iff {T : ℝ → Set ℝ} :
    SvMonotone T ↔ ∀ x₀ v₀, v₀ ∈ T x₀ → ∀ x₁ v₁, v₁ ∈ T x₁ →
      (x₀ ≤ x₁ ∧ v₀ ≤ v₁) ∨ (x₁ ≤ x₀ ∧ v₁ ≤ v₀) := by
  constructor
  · intro hT x₀ v₀ h₀ x₁ v₁ h₁
    have h := hT h₀ h₁
    rw [inner_real_eq_mul] at h
    rcases mul_nonneg_iff.1 h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · intro h x₀ v₀ h₀ x₁ v₁ h₁
    rw [inner_real_eq_mul]
    rcases h x₀ v₀ h₀ x₁ v₁ h₁ with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact mul_nonneg (by linarith) (by linarith)
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- **Exercise 12.9(a)**, in order-theoretic form: `T` is monotone exactly when
`gph T` is a chain for the componentwise order of `ℝ²`, the order induced by
`ℝ²₊`. -/
theorem svMonotone_real_iff_isChain {T : ℝ → Set ℝ} :
    SvMonotone T ↔ IsChain (· ≤ ·) (svGraph T) := by
  rw [svMonotone_real_iff]
  constructor
  · intro h p hp q hq _
    rcases h p.1 p.2 hp q.1 q.2 hq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl (Prod.le_def.2 ⟨h₁, h₂⟩)
    · exact Or.inr (Prod.le_def.2 ⟨h₁, h₂⟩)
  · intro h x₀ v₀ h₀ x₁ v₁ h₁
    by_cases hpq : (x₀, v₀) = (x₁, v₁)
    · rw [Prod.mk.injEq] at hpq
      exact Or.inl ⟨hpq.1.le, hpq.2.le⟩
    · rcases h (show (x₀, v₀) ∈ svGraph T from h₀) (show (x₁, v₁) ∈ svGraph T from h₁) hpq
        with hle | hle
      · exact Or.inl (Prod.mk_le_mk.1 hle)
      · exact Or.inr (Prod.mk_le_mk.1 hle)

/-- **Exercise 12.9**, from the guide: `T` is maximal monotone exactly when
`gph T` is a maximal chain for the componentwise order of `ℝ²`. -/
theorem svMaximalMonotone_real_iff_isMaxChain {T : ℝ → Set ℝ} :
    SvMaximalMonotone T ↔ IsMaxChain (· ≤ ·) (svGraph T) := by
  rw [svMaximalMonotone_iff_no_enlargement, svMonotone_real_iff_isChain]
  refine and_congr_right fun _ ↦ ⟨fun h t ht hsub ↦ ?_, fun h T' hT' hsub ↦ ?_⟩
  · have hgraph : svGraph (fun x ↦ {v | (x, v) ∈ t}) = t := by
      ext p
      rfl
    have hT' : SvMonotone (fun x ↦ {v | (x, v) ∈ t}) :=
      svMonotone_real_iff_isChain.2 (by rwa [hgraph])
    have := h _ hT' (by rwa [hgraph])
    rw [hgraph] at this
    exact this.symm
  · exact (h (svMonotone_real_iff_isChain.1 hT') hsub).symm

section Representation

variable {T : ℝ → Set ℝ} {φ : ℝ → EReal}

private theorem svMonotone_of_monotone_fun (hφ : Monotone φ)
    (hT : ∀ x, T x = {v : ℝ | leftLim φ x ≤ (v : EReal) ∧ (v : EReal) ≤ rightLim φ x}) :
    SvMonotone T := by
  refine svMonotone_real_iff.2 fun x₀ v₀ h₀ x₁ v₁ h₁ ↦ ?_
  rw [hT] at h₀ h₁
  rcases lt_trichotomy x₀ x₁ with hx | rfl | hx
  · exact Or.inl ⟨hx.le, EReal.coe_le_coe_iff.1
      (h₀.2.trans ((hφ.rightLim_le_leftLim hx).trans h₁.1))⟩
  · rcases le_total v₀ v₁ with hv | hv
    · exact Or.inl ⟨le_rfl, hv⟩
    · exact Or.inr ⟨le_rfl, hv⟩
  · exact Or.inr ⟨hx.le, EReal.coe_le_coe_iff.1
      (h₁.2.trans ((hφ.rightLim_le_leftLim hx).trans h₀.1))⟩

/-- A pair below every graph value to its right lies below `φ(x̂+)`. -/
private theorem le_rightLim_of_forall (hφ : Monotone φ) (hbot : ∃ x, φ x ≠ ⊥)
    (hT : ∀ x, T x = {v : ℝ | leftLim φ x ≤ (v : EReal) ∧ (v : EReal) ≤ rightLim φ x})
    {xh vh : ℝ} (h : ∀ x v, v ∈ T x → xh < x → vh ≤ v) : (vh : EReal) ≤ rightLim φ xh := by
  by_contra hlt
  push_neg at hlt
  have key : ∀ x, xh < x → ⊥ < rightLim φ x → rightLim φ x < vh → False := by
    intro x hx hb hlt'
    obtain ⟨r, hr⟩ : ∃ r : ℝ, rightLim φ x = r :=
      ⟨(rightLim φ x).toReal, (EReal.coe_toReal (ne_top_of_lt hlt') hb.ne').symm⟩
    have hrT : r ∈ T x := by
      rw [hT x]
      exact ⟨(hφ.leftLim_le_rightLim le_rfl).trans hr.le, hr.ge⟩
    have := h x r hrT hx
    rw [hr] at hlt'
    exact absurd (EReal.coe_lt_coe_iff.1 hlt') (not_lt.2 this)
  rw [hφ.rightLim_eq_sInf (NeBot.ne inferInstance)] at hlt
  obtain ⟨_, ⟨y, hy, rfl⟩, hyv⟩ := sInf_lt_iff.1 hlt
  have hy' : xh < y := hy
  have h₁ : ∀ x ∈ Ioo xh y, rightLim φ x = ⊥ := by
    intro x hx
    by_contra hne
    exact key x hx.1 (bot_lt_iff_ne_bot.2 hne) ((hφ.rightLim_le hx.2).trans_lt hyv)
  have h₂ : ∀ x < y, φ x = ⊥ := by
    intro x hx
    obtain ⟨m, hm₁, hm₂⟩ := exists_between (max_lt hx hy' : max x xh < y)
    have hm : m ∈ Ioo xh y := ⟨(le_max_right _ _).trans_lt hm₁, hm₂⟩
    have hφm : φ m ≤ ⊥ := (hφ.le_rightLim le_rfl).trans (h₁ m hm).le
    exact le_bot_iff.1 ((hφ ((le_max_left x xh).trans hm₁.le)).trans hφm)
  obtain ⟨z, hz⟩ := hbot
  set B := {x | φ x ≠ ⊥} with hBdef
  have hBne : B.Nonempty := ⟨z, hz⟩
  have hBlow : ∀ b ∈ B, y ≤ b := fun b hb ↦ not_lt.1 fun hby ↦ hb (h₂ b hby)
  have hBbdd : BddBelow B := ⟨y, hBlow⟩
  set s := sInf B with hsdef
  have hxs : xh < s := hy'.trans_le (le_csInf hBne hBlow)
  have h₄ : ∀ x < s, φ x = ⊥ := fun x hx ↦ not_not.1 (notMem_of_lt_csInf hx hBbdd)
  have h₅ : leftLim φ s = ⊥ := by
    rw [hφ.leftLim_eq_sSup (NeBot.ne inferInstance)]
    refine le_bot_iff.1 (sSup_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact (h₄ x hx).le
  have h₆ : rightLim φ s = ⊥ := by
    by_contra hne
    obtain ⟨r, -, hr₂⟩ := EReal.lt_iff_exists_real_btwn.1 (bot_lt_iff_ne_bot.2 hne)
    have hvT : min r (vh - 1) ∈ T s := by
      rw [hT s, h₅]
      exact ⟨bot_le, (EReal.coe_le_coe_iff.2 (min_le_left _ _)).trans hr₂.le⟩
    have h₁' := h s _ hvT hxs
    have h₂' : min r (vh - 1) ≤ vh - 1 := min_le_right _ _
    linarith
  have hlt₇ : sInf (φ '' Ioi s) < vh := by
    rw [← hφ.rightLim_eq_sInf (NeBot.ne inferInstance), h₆]
    exact EReal.bot_lt_coe vh
  obtain ⟨_, ⟨x, hx, rfl⟩, hxv⟩ := sInf_lt_iff.1 hlt₇
  have hx' : s < x := hx
  obtain ⟨b, hb, hbx⟩ := exists_lt_of_csInf_lt hBne hx'
  have hφx : ⊥ < φ x := by
    refine bot_lt_iff_ne_bot.2 fun h0 ↦ hb ?_
    have hle : φ b ≤ φ x := hφ hbx.le
    rw [h0] at hle
    exact le_bot_iff.1 hle
  obtain ⟨r, hr⟩ : ∃ r : ℝ, φ x = r :=
    ⟨(φ x).toReal, (EReal.coe_toReal (ne_top_of_lt hxv) hφx.ne').symm⟩
  have hrT : r ∈ T x := by
    rw [hT x]
    exact ⟨(hφ.leftLim_le le_rfl).trans hr.le, hr.ge.trans (hφ.le_rightLim le_rfl)⟩
  have := h x r hrT (hxs.trans hx')
  rw [hr] at hxv
  exact absurd (EReal.coe_lt_coe_iff.1 hxv) (not_lt.2 this)

/-- A pair above every graph value to its left lies above `φ(x̂-)`. -/
private theorem leftLim_le_of_forall (hφ : Monotone φ) (htop : ∃ x, φ x ≠ ⊤)
    (hT : ∀ x, T x = {v : ℝ | leftLim φ x ≤ (v : EReal) ∧ (v : EReal) ≤ rightLim φ x})
    {xh vh : ℝ} (h : ∀ x v, v ∈ T x → x < xh → v ≤ vh) : leftLim φ xh ≤ (vh : EReal) := by
  by_contra hlt
  push_neg at hlt
  have key : ∀ x, x < xh → leftLim φ x < ⊤ → (vh : EReal) < leftLim φ x → False := by
    intro x hx ht hlt'
    obtain ⟨r, hr⟩ : ∃ r : ℝ, leftLim φ x = r :=
      ⟨(leftLim φ x).toReal, (EReal.coe_toReal ht.ne (ne_bot_of_gt hlt')).symm⟩
    have hrT : r ∈ T x := by
      rw [hT x]
      exact ⟨hr.le, hr.ge.trans (hφ.leftLim_le_rightLim le_rfl)⟩
    have := h x r hrT hx
    rw [hr] at hlt'
    exact absurd (EReal.coe_lt_coe_iff.1 hlt') (not_lt.2 this)
  rw [hφ.leftLim_eq_sSup (NeBot.ne inferInstance)] at hlt
  obtain ⟨_, ⟨y, hy, rfl⟩, hyv⟩ := lt_sSup_iff.1 hlt
  have hy' : y < xh := hy
  have h₁ : ∀ x ∈ Ioo y xh, leftLim φ x = ⊤ := by
    intro x hx
    by_contra hne
    exact key x hx.2 (lt_top_iff_ne_top.2 hne) (hyv.trans_le (hφ.le_leftLim hx.1))
  have h₂ : ∀ x, y < x → φ x = ⊤ := by
    intro x hx
    obtain ⟨m, hm₁, hm₂⟩ := exists_between (lt_min hx hy' : y < min x xh)
    have hm : m ∈ Ioo y xh := ⟨hm₁, hm₂.trans_le (min_le_right _ _)⟩
    have hφm : ⊤ ≤ φ m := (h₁ m hm).ge.trans (hφ.leftLim_le le_rfl)
    exact top_le_iff.1 (hφm.trans (hφ (hm₂.le.trans (min_le_left x xh))))
  obtain ⟨z, hz⟩ := htop
  set B := {x | φ x ≠ ⊤} with hBdef
  have hBne : B.Nonempty := ⟨z, hz⟩
  have hBup : ∀ b ∈ B, b ≤ y := fun b hb ↦ not_lt.1 fun hyb ↦ hb (h₂ b hyb)
  have hBbdd : BddAbove B := ⟨y, hBup⟩
  set s := sSup B with hsdef
  have hsx : s < xh := (csSup_le hBne hBup).trans_lt hy'
  have h₄ : ∀ x, s < x → φ x = ⊤ := fun x hx ↦ not_not.1 (notMem_of_csSup_lt hx hBbdd)
  have h₅ : rightLim φ s = ⊤ := by
    rw [hφ.rightLim_eq_sInf (NeBot.ne inferInstance)]
    refine top_le_iff.1 (le_sInf ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact (h₄ x hx).ge
  have h₆ : leftLim φ s = ⊤ := by
    by_contra hne
    obtain ⟨r, hr₁, -⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_top_iff_ne_top.2 hne)
    have hvT : max r (vh + 1) ∈ T s := by
      rw [hT s, h₅]
      exact ⟨hr₁.le.trans (EReal.coe_le_coe_iff.2 (le_max_left _ _)), le_top⟩
    have h₁' := h s _ hvT hsx
    have h₂' : vh + 1 ≤ max r (vh + 1) := le_max_right _ _
    linarith
  have hlt₇ : (vh : EReal) < sSup (φ '' Iio s) := by
    rw [← hφ.leftLim_eq_sSup (NeBot.ne inferInstance), h₆]
    exact EReal.coe_lt_top vh
  obtain ⟨_, ⟨x, hx, rfl⟩, hxv⟩ := lt_sSup_iff.1 hlt₇
  have hx' : x < s := hx
  obtain ⟨b, hb, hxb⟩ := exists_lt_of_lt_csSup hBne hx'
  have hφx : φ x < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h0 ↦ hb ?_
    have hle : φ x ≤ φ b := hφ hxb.le
    rw [h0] at hle
    exact top_le_iff.1 hle
  obtain ⟨r, hr⟩ : ∃ r : ℝ, φ x = r :=
    ⟨(φ x).toReal, (EReal.coe_toReal hφx.ne (ne_bot_of_gt hxv)).symm⟩
  have hrT : r ∈ T x := by
    rw [hT x]
    exact ⟨(hφ.leftLim_le le_rfl).trans hr.le, hr.ge.trans (hφ.le_rightLim le_rfl)⟩
  have := h x r hrT (hx'.trans hsx)
  rw [hr] at hxv
  exact absurd (EReal.coe_lt_coe_iff.1 hxv) (not_lt.2 this)

/-- **Exercise 12.9(b)**, sufficiency. -/
theorem svMaximalMonotone_of_monotone_fun (hφ : Monotone φ) (htop : ∃ x, φ x ≠ ⊤)
    (hbot : ∃ x, φ x ≠ ⊥)
    (hT : ∀ x, T x = {v : ℝ | leftLim φ x ≤ (v : EReal) ∧ (v : EReal) ≤ rightLim φ x}) :
    SvMaximalMonotone T := by
  refine svMaximalMonotone_iff_forall_inner_nonneg.2
    ⟨svMonotone_of_monotone_fun hφ hT, fun xh vh h ↦ ?_⟩
  have h' : ∀ x v, v ∈ T x → (x < xh → v ≤ vh) ∧ (xh < x → vh ≤ v) :=
    fun x v hv ↦ inner_nonneg_real_iff.1 (h x v hv)
  rw [hT]
  exact ⟨leftLim_le_of_forall hφ htop hT fun x v hv hx ↦ (h' x v hv).1 hx,
    le_rightLim_of_forall hφ hbot hT fun x v hv hx ↦ (h' x v hv).2 hx⟩

/-- **Exercise 12.9(b)**, necessity, with `φ(x+) = φ₊(x)` and `φ(x-) = φ₋(x)`
for the functions of the guide. -/
theorem exists_monotone_fun_of_svMaximalMonotone (hT : SvMaximalMonotone T) :
    ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ x, φ x ≠ ⊤) ∧ (∃ x, φ x ≠ ⊥) ∧
      ∀ x, T x = {v : ℝ | leftLim φ x ≤ (v : EReal) ∧ (v : EReal) ≤ rightLim φ x} := by
  have hmono₁ : ∀ x₀ v₀ x₁ v₁, v₀ ∈ T x₀ → v₁ ∈ T x₁ → x₀ < x₁ → v₀ ≤ v₁ := by
    intro x₀ v₀ x₁ v₁ h₀ h₁ hx
    exact (inner_nonneg_real_iff.1 (hT.1 h₀ h₁)).1 hx
  let Sp : ℝ → Set EReal := fun x ↦ {e | ∃ x' v', v' ∈ T x' ∧ x < x' ∧ (v' : EReal) = e}
  let Sm : ℝ → Set EReal := fun x ↦ {e | ∃ x' v', v' ∈ T x' ∧ x' < x ∧ (v' : EReal) = e}
  let φp : ℝ → EReal := fun x ↦ sInf (Sp x)
  let φm : ℝ → EReal := fun x ↦ sSup (Sm x)
  have hchar : ∀ x v, v ∈ T x ↔ φm x ≤ (v : EReal) ∧ (v : EReal) ≤ φp x := by
    intro x v
    constructor
    · intro hv
      refine ⟨sSup_le ?_, le_sInf ?_⟩
      · rintro _ ⟨x', v', hv', hx', rfl⟩
        exact EReal.coe_le_coe_iff.2 (hmono₁ _ _ _ _ hv' hv hx')
      · rintro _ ⟨x', v', hv', hx', rfl⟩
        exact EReal.coe_le_coe_iff.2 (hmono₁ _ _ _ _ hv hv' hx')
    · rintro ⟨h₁, h₂⟩
      refine hT.mem_of_forall_inner_nonneg fun x' v' hv' ↦
        inner_nonneg_real_iff.2 ⟨fun hx' ↦ ?_, fun hx' ↦ ?_⟩
      · exact EReal.coe_le_coe_iff.1 ((le_sSup (s := Sm x) ⟨x', v', hv', hx', rfl⟩).trans h₁)
      · exact EReal.coe_le_coe_iff.1 (h₂.trans (sInf_le ⟨x', v', hv', hx', rfl⟩))
  have hSp : ∀ {x y : ℝ}, x ≤ y → Sp y ⊆ Sp x := by
    rintro x y hxy _ ⟨x', v', hv', hx', rfl⟩
    exact ⟨x', v', hv', hxy.trans_lt hx', rfl⟩
  have hSm : ∀ {x y : ℝ}, x ≤ y → Sm x ⊆ Sm y := by
    rintro x y hxy _ ⟨x', v', hv', hx', rfl⟩
    exact ⟨x', v', hv', hx'.trans_le hxy, rfl⟩
  have hφp : Monotone φp := fun x y hxy ↦ sInf_le_sInf (hSp hxy)
  have hφm : Monotone φm := fun x y hxy ↦ sSup_le_sSup (hSm hxy)
  have hkey : ∀ y x, y < x → φp y ≤ φm x := by
    intro y x hyx
    by_contra hlt
    push_neg at hlt
    obtain ⟨r, hr₁, hr₂⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    obtain ⟨m, hym, hmx⟩ := exists_between hyx
    have hrT : r ∈ T m := (hchar m r).2 ⟨(hφm hmx.le).trans hr₁.le, hr₂.le.trans (hφp hym.le)⟩
    exact absurd (le_sSup (s := Sm x) (a := (r : EReal)) ⟨m, r, hrT, hmx, rfl⟩) (not_le.2 hr₁)
  have hright : ∀ x, rightLim φp x = φp x := by
    intro x
    rw [hφp.rightLim_eq_sInf (NeBot.ne inferInstance)]
    apply le_antisymm
    · refine le_sInf ?_
      rintro _ ⟨x', v', hv', hx', rfl⟩
      obtain ⟨y, hxy, hyx'⟩ := exists_between hx'
      exact (sInf_le (mem_image_of_mem φp (show y ∈ Ioi x from hxy))).trans
        (sInf_le ⟨x', v', hv', hyx', rfl⟩)
    · refine le_sInf ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hφp (le_of_lt hy)
  have hleft : ∀ x, leftLim φp x = φm x := by
    intro x
    rw [hφp.leftLim_eq_sSup (NeBot.ne inferInstance)]
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hkey y x hy
    · refine sSup_le ?_
      rintro _ ⟨x', v', hv', hx', rfl⟩
      obtain ⟨y, hx'y, hyx⟩ := exists_between hx'
      refine le_trans ?_ (le_sSup (mem_image_of_mem φp (show y ∈ Iio x from hyx)))
      refine le_sInf ?_
      rintro _ ⟨x'', v'', hv'', hx'', rfl⟩
      exact EReal.coe_le_coe_iff.2 (hmono₁ _ _ _ _ hv' hv'' (hx'y.trans hx''))
  obtain ⟨x₀, v₀, hv₀⟩ : ∃ x v, v ∈ T x := by
    by_contra hne
    push_neg at hne
    obtain ⟨x', v', hv', -⟩ := hT.2 0 0 (hne 0 0)
    exact hne x' v' hv'
  refine ⟨φp, hφp, ⟨x₀ - 1, ?_⟩, ⟨x₀, ?_⟩, fun x ↦ ?_⟩
  · exact ne_top_of_le_ne_top (EReal.coe_ne_top v₀)
      (sInf_le ⟨x₀, v₀, hv₀, by linarith, rfl⟩)
  · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot v₀) ((hchar x₀ v₀).1 hv₀).2
  · ext v
    rw [mem_setOf_eq, hleft, hright, hchar]

/-- **Exercise 12.9(b) (maximal monotonicity in one dimension).** A mapping
`T : ℝ ⇉ ℝ` is maximal monotone if and only if there is a nondecreasing
`φ : ℝ → ℝ̄` with `φ ≢ ∞` and `φ ≢ -∞` such that
`T(x) = {v ∈ ℝ | φ(x-) ≤ v ≤ φ(x+)}`. -/
theorem svMaximalMonotone_real_iff :
    SvMaximalMonotone T ↔ ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ x, φ x ≠ ⊤) ∧ (∃ x, φ x ≠ ⊥) ∧
      ∀ x, T x = {v : ℝ | leftLim φ x ≤ (v : EReal) ∧ (v : EReal) ≤ rightLim φ x} :=
  ⟨exists_monotone_fun_of_svMaximalMonotone,
    fun ⟨_, hφ, htop, hbot, hT⟩ ↦ svMaximalMonotone_of_monotone_fun hφ htop hbot hT⟩

/-- **Exercise 12.9(b)** with `φ(x-) := lim_{x' ↗ x} φ(x')` and
`φ(x+) := lim_{x' ↘ x} φ(x')` written as limits.  For nondecreasing `φ` both limits
exist in `ℝ̄` (`Monotone.tendsto_leftLim`, `Monotone.tendsto_rightLim`) and are
unique, so the representation does not depend on the conventions of
`Function.leftLim` and `Function.rightLim`. -/
theorem svMaximalMonotone_real_iff_tendsto :
    SvMaximalMonotone T ↔ ∃ φ : ℝ → EReal, Monotone φ ∧ (∃ x, φ x ≠ ⊤) ∧ (∃ x, φ x ≠ ⊥) ∧
      ∀ x l r, Tendsto φ (𝓝[<] x) (𝓝 l) → Tendsto φ (𝓝[>] x) (𝓝 r) →
        T x = {v : ℝ | l ≤ (v : EReal) ∧ (v : EReal) ≤ r} := by
  rw [svMaximalMonotone_real_iff]
  refine exists_congr fun φ ↦ and_congr_right fun hφ ↦ and_congr_right fun _ ↦
    and_congr_right fun _ ↦ ⟨fun h x l r hl hr ↦ ?_, fun h x ↦ ?_⟩
  · rw [h x, leftLim_eq_of_tendsto (NeBot.ne inferInstance) hl,
      rightLim_eq_of_tendsto (NeBot.ne inferInstance) hr]
  · exact h x _ _ (hφ.tendsto_leftLim x) (hφ.tendsto_rightLim x)

end Representation

end OneDimension

end RW
