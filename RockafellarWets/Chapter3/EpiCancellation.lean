/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3: Exact cancellation in epi-addition

This file proves Theorem 3.34 for proper lower-semicontinuous convex
extended-real functions.  The proof uses tilted infima directly: coercivity
makes the common tilted infimum finite, so it can be cancelled in `EReal`.
-/

import RockafellarWets.Chapter3.ERealInfimum
import RockafellarWets.Chapter3.ExtendedCancellationCompletion
import RockafellarWets.Chapter3.EpiAddition

open EReal Set Topology

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The extended-real infimum of `f` after tilting by a continuous linear
functional.  Keeping the value in `EReal` is essential when the infimum is
unbounded below. -/
def tiltedInfimumEReal (f : E → EReal) (l : E →L[ℝ] ℝ) : EReal :=
  ⨅ x : E, f x + ((-l x : ℝ) : EReal)

/-- A proper coercive function has a finite tilted infimum for every
continuous linear functional. -/
theorem exists_tiltedInfimumEReal_eq_coe_of_isCoercive
    {g : E → EReal} (hproper : IsProper g) (hg : IsCoercive g)
    (l : E →L[ℝ] ℝ) :
    ∃ b : ℝ, tiltedInfimumEReal g l = (b : EReal) := by
  obtain ⟨β, hβ⟩ := hg (‖l‖ + 1) (by positivity)
  have hlower : (β : EReal) ≤ tiltedInfimumEReal g l := by
    rw [tiltedInfimumEReal]
    refine le_iInf fun x ↦ ?_
    have hlx : l x ≤ ‖l‖ * ‖x‖ := by
      exact (le_abs_self (l x)).trans
        (by simpa [Real.norm_eq_abs] using l.le_opNorm x)
    have hreal : β ≤ (‖l‖ + 1) * ‖x‖ + β - l x := by
      nlinarith [norm_nonneg x]
    have hcoe : (β : EReal) ≤
        (((‖l‖ + 1) * ‖x‖ + β : ℝ) : EReal) + ((-l x : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      apply EReal.coe_le_coe_iff.mpr
      linarith
    exact hcoe.trans (add_le_add (hβ x) le_rfl)
  rcases hproper.1 with ⟨x, hx⟩
  have hxbot : g x ≠ ⊥ := ne_of_gt (hproper.2 x)
  have hupper : tiltedInfimumEReal g l ≤
      (((g x).toReal - l x : ℝ) : EReal) := by
    rw [tiltedInfimumEReal]
    refine (iInf_le _ x).trans_eq ?_
    rw [← EReal.coe_toReal (ne_of_lt hx) hxbot, ← EReal.coe_add]
    congr 1
  refine ⟨(tiltedInfimumEReal g l).toReal, ?_⟩
  exact (EReal.coe_toReal
    (ne_of_lt (hupper.trans_lt (EReal.coe_lt_top _)))
    (ne_of_gt ((EReal.bot_lt_coe β).trans_le hlower))).symm

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Independent infima factor through `EReal` addition when the second
infimum is finite and neither family has pointwise value `⊥`. -/
theorem iInf_iInf_add_eq_add_iInf_of_eq_coe
    {F G : E → EReal}
    (hFbot : ∀ u, F u ≠ ⊥) (hGbot : ∀ w, G w ≠ ⊥)
    {b : ℝ} (hG : (⨅ w, G w) = (b : EReal)) :
    (⨅ u, ⨅ w, F u + G w) = (⨅ u, F u) + (⨅ w, G w) := by
  have hinner : ∀ u, (⨅ w, F u + G w) = F u + (b : EReal) := by
    intro u
    by_cases hutop : F u = ⊤
    · have htop : ∀ w, F u + G w = ⊤ := by
        intro w
        rw [hutop]
        exact EReal.top_add_of_ne_bot (hGbot w)
      simp_rw [htop]
      simp [hutop]
    · let a : ℝ := (F u).toReal
      have hFu : F u = (a : EReal) :=
        (EReal.coe_toReal hutop (hFbot u)).symm
      rw [hFu, ← coe_add_iInf, hG]
  simp_rw [hinner]
  rw [← iInf_add_coe, hG]

private theorem add_add_coe_eq_add_coe_add
    {a b : EReal} (habot : a ≠ ⊥) (hbbot : b ≠ ⊥) (s t : ℝ) :
    (a + b) + ((s + t : ℝ) : EReal) =
      (a + (s : EReal)) + (b + (t : EReal)) := by
  by_cases hatop : a = ⊤
  · have hbtbot : b + (t : EReal) ≠ ⊥ :=
      EReal.add_ne_bot_iff.mpr ⟨hbbot, EReal.coe_ne_bot _⟩
    rw [hatop, EReal.top_add_of_ne_bot hbbot, EReal.top_add_coe,
      EReal.top_add_coe, EReal.top_add_of_ne_bot hbtbot]
  · by_cases hbtop : b = ⊤
    · have hasbot : a + (s : EReal) ≠ ⊥ :=
        EReal.add_ne_bot_iff.mpr ⟨habot, EReal.coe_ne_bot _⟩
      rw [hbtop, EReal.add_top_of_ne_bot habot, EReal.top_add_coe,
        EReal.top_add_coe, EReal.add_top_of_ne_bot hasbot]
    · lift a to ℝ using ⟨hatop, habot⟩ with ar
      lift b to ℝ using ⟨hbtop, hbbot⟩ with br
      norm_cast
      ring

private theorem epi_tilt_reassociate
    {f g : E → EReal} (hproperf : IsProper f) (hproperg : IsProper g)
    (l : E →L[ℝ] ℝ) (u w : E) :
    (f u + g w) + ((-l (u + w) : ℝ) : EReal) =
      (f u + ((-l u : ℝ) : EReal)) +
        (g w + ((-l w : ℝ) : EReal)) := by
  have h := add_add_coe_eq_add_coe_add
    (ne_of_gt (hproperf.2 u)) (ne_of_gt (hproperg.2 w)) (-l u) (-l w)
  convert h using 1
  rw [map_add]
  rw [show -(l u + l w) = -l u + -l w by ring]

/-- Tilting turns an epi-sum into ordinary addition of tilted infima whenever
the common tilted infimum is finite. -/
theorem tiltedInfimumEReal_epiSum
    {f g : E → EReal} (hproperf : IsProper f) (hproperg : IsProper g)
    (l : E →L[ℝ] ℝ) {b : ℝ}
    (hb : tiltedInfimumEReal g l = (b : EReal)) :
    tiltedInfimumEReal (epiSum f g) l =
      tiltedInfimumEReal f l + tiltedInfimumEReal g l := by
  let F : E → EReal := fun u ↦ f u + ((-l u : ℝ) : EReal)
  let G : E → EReal := fun w ↦ g w + ((-l w : ℝ) : EReal)
  have hFbot : ∀ u, F u ≠ ⊥ := by
    intro u
    exact ne_of_gt (EReal.bot_lt_add_iff.mpr
      ⟨hproperf.2 u, EReal.bot_lt_coe _⟩)
  have hGbot : ∀ w, G w ≠ ⊥ := by
    intro w
    exact ne_of_gt (EReal.bot_lt_add_iff.mpr
      ⟨hproperg.2 w, EReal.bot_lt_coe _⟩)
  have hG : (⨅ w, G w) = (b : EReal) := by
    simpa [G, tiltedInfimumEReal] using hb
  have hfactor :
      (⨅ u, ⨅ w, F u + G w) =
        tiltedInfimumEReal f l + tiltedInfimumEReal g l := by
    simpa [F, G, tiltedInfimumEReal] using
      iInf_iInf_add_eq_add_iInf_of_eq_coe hFbot hGbot hG
  rw [← hfactor]
  apply le_antisymm
  · refine le_iInf fun u ↦ le_iInf fun w ↦ ?_
    rw [tiltedInfimumEReal]
    refine iInf_le_of_le (u + w) ?_
    change (⨅ z, f (u + w - z) + g z) + ((-l (u + w) : ℝ) : EReal) ≤
      F u + G w
    have hraw := add_le_add_right
      (iInf_le (fun z ↦ f (u + w - z) + g z) w)
      (((-l (u + w) : ℝ) : EReal))
    have hraw' : (⨅ z, f (u + w - z) + g z) +
        ((-l (u + w) : ℝ) : EReal) ≤
        (f (u + w - w) + g w) + ((-l (u + w) : ℝ) : EReal) := by
      simpa [add_comm] using hraw
    refine hraw'.trans ?_
    have huw : u + w - w = u := by abel
    rw [huw]
    exact (epi_tilt_reassociate hproperf hproperg l u w).le
  · rw [tiltedInfimumEReal]
    refine le_iInf fun x ↦ ?_
    rw [epiSum_apply, iInf_add_coe]
    refine le_iInf fun w ↦ ?_
    refine (iInf_le_of_le (x - w) (iInf_le _ w)).trans_eq ?_
    have hxw : x - w + w = x := sub_add_cancel x w
    change (f (x - w) + ((-l (x - w) : ℝ) : EReal)) +
      (g w + ((-l w : ℝ) : EReal)) =
        (f (x - w) + g w) + ((-l x : ℝ) : EReal)
    calc
      _ = (f (x - w) + g w) + ((-l ((x - w) + w) : ℝ) : EReal) :=
        (epi_tilt_reassociate hproperf hproperg l (x - w) w).symm
      _ = (f (x - w) + g w) + ((-l x : ℝ) : EReal) := by rw [hxw]

/-- Proper closed convex extended-real functions are determined by all of
their tilted infima. -/
theorem eq_of_forall_tiltedInfimumEReal_eq_of_convex_lsc
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁))
    (hlsc₁ : LowerSemicontinuous f₁) (hproper₁ : IsProper f₁)
    (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₂ : LowerSemicontinuous f₂) (hproper₂ : IsProper f₂)
    (hEq : ∀ l : E →L[ℝ] ℝ,
      tiltedInfimumEReal f₁ l = tiltedInfimumEReal f₂ l) :
    f₁ = f₂ := by
  funext x
  apply le_antisymm
  · by_contra hle
    have hxlt : f₂ x < f₁ x := lt_of_not_ge hle
    have h₂top : f₂ x ≠ ⊤ := ne_of_lt (hxlt.trans_le le_top)
    have h₂bot : f₂ x ≠ ⊥ := ne_of_gt (hproper₂.2 x)
    let r : ℝ := (f₂ x).toReal
    have h₂x : f₂ x = (r : EReal) :=
      (EReal.coe_toReal h₂top h₂bot).symm
    obtain ⟨l, b, hr, hminor⟩ :=
      exists_affine_minorant_gt_of_lt_of_convex_lsc_ereal
        hconv₁ hlsc₁ hproper₁ (x := x) (r := r) (by simpa [← h₂x])
    have hb₁ : (b : EReal) ≤ tiltedInfimumEReal f₁ l := by
      rw [tiltedInfimumEReal]
      refine le_iInf fun w ↦ ?_
      have hw := add_le_add (hminor w)
        (le_refl (((-l w : ℝ) : EReal)) )
      have heq : (((l w + b : ℝ) : EReal) + ((-l w : ℝ) : EReal)) =
          (b : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        ring
      rw [← heq]
      exact hw
    have hb₂ : (b : EReal) ≤ tiltedInfimumEReal f₂ l := by
      rw [← hEq l]
      exact hb₁
    have hbx : (b : EReal) ≤ f₂ x + ((-l x : ℝ) : EReal) :=
      hb₂.trans (iInf_le _ x)
    have hreal : b ≤ r - l x := by
      rw [h₂x, ← EReal.coe_add] at hbx
      exact EReal.coe_le_coe_iff.mp hbx
    linarith
  · by_contra hle
    have hxlt : f₁ x < f₂ x := lt_of_not_ge hle
    have h₁top : f₁ x ≠ ⊤ := ne_of_lt (hxlt.trans_le le_top)
    have h₁bot : f₁ x ≠ ⊥ := ne_of_gt (hproper₁.2 x)
    let r : ℝ := (f₁ x).toReal
    have h₁x : f₁ x = (r : EReal) :=
      (EReal.coe_toReal h₁top h₁bot).symm
    obtain ⟨l, b, hr, hminor⟩ :=
      exists_affine_minorant_gt_of_lt_of_convex_lsc_ereal
        hconv₂ hlsc₂ hproper₂ (x := x) (r := r) (by simpa [← h₁x])
    have hb₂ : (b : EReal) ≤ tiltedInfimumEReal f₂ l := by
      rw [tiltedInfimumEReal]
      refine le_iInf fun w ↦ ?_
      have hw := add_le_add (hminor w)
        (le_refl (((-l w : ℝ) : EReal)))
      have heq : (((l w + b : ℝ) : EReal) + ((-l w : ℝ) : EReal)) =
          (b : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        ring
      rw [← heq]
      exact hw
    have hb₁ : (b : EReal) ≤ tiltedInfimumEReal f₁ l := by
      rw [hEq l]
      exact hb₂
    have hbx : (b : EReal) ≤ f₁ x + ((-l x : ℝ) : EReal) :=
      hb₁.trans (iInf_le _ x)
    have hreal : b ≤ r - l x := by
      rw [h₁x, ← EReal.coe_add] at hbx
      exact EReal.coe_le_coe_iff.mp hbx
    linarith

/-- **Theorem 3.34 (exact form): cancellation in epi-addition.** If
`f₁ ⊞ g = f₂ ⊞ g` for proper lower-semicontinuous convex functions and the
common summand `g` is coercive, then `f₁ = f₂`. -/
theorem theorem334_eq_of_epiSum_eq
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {f₁ f₂ g : E → EReal}
    (hconv₁ : Convex ℝ (epigraph f₁))
    (hlsc₁ : LowerSemicontinuous f₁) (hproper₁ : IsProper f₁)
    (hconv₂ : Convex ℝ (epigraph f₂))
    (hlsc₂ : LowerSemicontinuous f₂) (hproper₂ : IsProper f₂)
    (_hconvg : Convex ℝ (epigraph g))
    (_hlscg : LowerSemicontinuous g) (hproperg : IsProper g)
    (hg : IsCoercive g)
    (hEq : epiSum f₁ g = epiSum f₂ g) :
    f₁ = f₂ := by
  apply eq_of_forall_tiltedInfimumEReal_eq_of_convex_lsc
    hconv₁ hlsc₁ hproper₁ hconv₂ hlsc₂ hproper₂
  intro l
  obtain ⟨b, hb⟩ := exists_tiltedInfimumEReal_eq_coe_of_isCoercive hproperg hg l
  have hsum : tiltedInfimumEReal f₁ l + (b : EReal) =
      tiltedInfimumEReal f₂ l + (b : EReal) := by
    calc
    tiltedInfimumEReal f₁ l + (b : EReal) =
        tiltedInfimumEReal f₁ l + tiltedInfimumEReal g l := by rw [hb]
    _ = tiltedInfimumEReal (epiSum f₁ g) l :=
      (tiltedInfimumEReal_epiSum hproper₁ hproperg l hb).symm
    _ = tiltedInfimumEReal (epiSum f₂ g) l := by rw [hEq]
    _ = tiltedInfimumEReal f₂ l + tiltedInfimumEReal g l :=
      tiltedInfimumEReal_epiSum hproper₂ hproperg l hb
    _ = tiltedInfimumEReal f₂ l + (b : EReal) := by rw [hb]
  apply le_antisymm
  · exact (EReal.addLECancellable_coe b).add_le_add_iff_right.mp hsum.le
  · exact (EReal.addLECancellable_coe b).add_le_add_iff_right.mp hsum.ge

end RW
