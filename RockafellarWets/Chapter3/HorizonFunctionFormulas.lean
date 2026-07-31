/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The sequential and ray formulas for horizon functions

This file supplies the two analytic formulas in Theorem 3.21.

* Formula 3(3) is represented by an exact sequential epigraph criterion:
  `λₙ ↓ 0`, `(xₙ,aₙ) → (w,a)`, and
  `(xₙ/λₙ,aₙ/λₙ) ∈ epi f`.  This is equivalent to
  `f∞(w) ≤ a`, and is the epigraphical form of the two-variable lower limit
  in the book.
* Formula 3(4) is proved exactly for real-valued proper closed convex
  functions.  The horizon value is the supremum of the ray difference
  quotients, and those quotients converge to that supremum as `τ → ∞`.

The real-valued restriction in the final limit statement avoids the project's
nonstandard absorbing-`⊥` subtraction.  The preceding ray-bound theorem is
stated for general `EReal`-valued proper closed convex functions and is the
subtraction-free form of the same formula.
-/

import RockafellarWets.Chapter3.EpiAddition
import RockafellarWets.Chapter2.Separation
import Mathlib.Topology.Order.MonotoneConvergence

open Set EReal Filter Topology

namespace RW

section SequentialFormula

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A positive-vanishing rescaling whose lifted points remain in `epi f` and
converge to `(w,a)`. This is the sequential epigraph form of formula 3(3). -/
def HasHorizonEpigraphSequence (f : E → EReal) (w : E) (a : ℝ) : Prop :=
  ∃ lam : ℕ → ℝ, ∃ x : ℕ → E, ∃ b : ℕ → ℝ,
    Tendsto lam atTop (𝓝[>] (0 : ℝ)) ∧
    Tendsto x atTop (𝓝 w) ∧
    Tendsto b atTop (𝓝 a) ∧
    ∀ n, (lam n)⁻¹ • (x n, b n) ∈ epigraph f

/-- Theorem 3.21, formula 3(3), exact sequential epigraph form. -/
theorem hasHorizonEpigraphSequence_iff_horizonFunction_le
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hne : (epigraph f).Nonempty)
    {w : E} {a : ℝ} :
    HasHorizonEpigraphSequence f w a ↔
      horizonFunction f w ≤ (a : EReal) := by
  rw [← mem_epigraph_iff,
    epigraph_horizonFunction_eq_horizonCone_epigraph hne]
  rw [horizonCone_eq_asymptoticCone hne]
  constructor
  · rintro ⟨lam, x, b, hlam, hx, hb, hmem⟩
    let c : ℕ → ℝ := fun n ↦ (lam n)⁻¹
    let u : ℕ → E × ℝ := fun n ↦ (x n, b n)
    have hc : Tendsto c atTop atTop := by
      exact hlam.inv_tendsto_nhdsGT_zero
    have hu : Tendsto u atTop (𝓝 (w, a)) :=
      hx.prodMk_nhds hb
    apply mem_asymptoticCone_of_seq_smul hc hu
    intro n
    simpa [c, u, Prod.smul_mk] using hmem n
  · intro h
    rcases exists_seq_pos_smul_of_mem_asymptoticCone
        (C := epigraph f) h with
      ⟨c, u, hc, hu, hcpos, hmem⟩
    refine ⟨fun n ↦ (c n)⁻¹, fun n ↦ (u n).1, fun n ↦ (u n).2,
      ?_, ?_, ?_, ?_⟩
    · exact tendsto_inv_atTop_nhdsGT_zero.comp hc
    · exact continuous_fst.continuousAt.tendsto.comp hu
    · exact continuous_snd.continuousAt.tendsto.comp hu
    · intro n
      simpa [Prod.smul_mk, smul_smul, inv_inv] using hmem n

/-- Equivalent expanding-scale version of formula 3(3). -/
theorem horizonFunction_le_iff_exists_expanding_epigraph_sequence
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hne : (epigraph f).Nonempty)
    {w : E} {a : ℝ} :
    horizonFunction f w ≤ (a : EReal) ↔
      ∃ c : ℕ → ℝ, ∃ u : ℕ → E × ℝ,
        Tendsto c atTop atTop ∧ Tendsto u atTop (𝓝 (w, a)) ∧
        (∀ n, 0 < c n) ∧ (∀ n, c n • u n ∈ epigraph f) := by
  rw [← mem_epigraph_iff,
    epigraph_horizonFunction_eq_horizonCone_epigraph hne]
  rw [horizonCone_eq_asymptoticCone hne]
  constructor
  · exact exists_seq_pos_smul_of_mem_asymptoticCone
  · rintro ⟨c, u, hc, hu, -, hmem⟩
    exact mem_asymptoticCone_of_seq_smul hc hu hmem

end SequentialFormula

section RayFormula

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem ereal_eq_of_forall_real_upper_bounds {p q : EReal}
    (h : ∀ a : ℝ, p ≤ (a : EReal) ↔ q ≤ (a : EReal)) :
    p = q := by
  apply le_antisymm
  · by_contra hpq
    have hqp : q < p := lt_of_not_ge hpq
    obtain ⟨a, hqa, hap⟩ := EReal.exists_between_coe_real hqp
    exact not_le_of_gt hap ((h a).2 hqa.le)
  · by_contra hqp
    have hpq : p < q := lt_of_not_ge hqp
    obtain ⟨a, hpa, haq⟩ := EReal.exists_between_coe_real hpq
    exact not_le_of_gt haq ((h a).1 hpa.le)

/-- The subtraction-free ray form of formula 3(4). A real number `a` bounds
`f∞(w)` exactly when the affine ray with slope `a` majorizes `f` from any
base point in the effective domain. -/
theorem horizonFunction_le_coe_iff_forall_ray_le
    {f : E → EReal} (hconv : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    {xbar w : E} (hxbar : xbar ∈ effectiveDomain f) {a : ℝ} :
    horizonFunction f w ≤ (a : EReal) ↔
      ∀ τ : ℝ, 0 < τ →
        f (xbar + τ • w) ≤ f xbar + ((τ * a : ℝ) : EReal) := by
  have hbarTop : f xbar ≠ ⊤ := ne_of_lt <| by
    simpa [mem_effectiveDomain_iff] using hxbar
  have hbarBot : f xbar ≠ ⊥ := ne_of_gt (hproper.2 xbar)
  let rbar : ℝ := (f xbar).toReal
  have hrbar : (rbar : EReal) = f xbar :=
    EReal.coe_toReal hbarTop hbarBot
  have hxepi : (xbar, rbar) ∈ epigraph f := by
    rw [mem_epigraph_iff, hrbar]
  constructor
  · intro ha τ hτ
    have hdir : (w, a) ∈ horizonCone (epigraph f) :=
      (mem_horizonCone_epigraph_iff_horizonFunction_le_of_isProper hproper).2 ha
    have hray :
        τ • (w, a) + (xbar, rbar) ∈ epigraph f :=
      smul_add_mem_of_mem_horizonCone
        (C := epigraph f) hconv
        (isClosed_epigraph_of_lsc_ereal f hlsc)
        hxepi hdir hτ.le
    rw [mem_epigraph_iff] at hray
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hrbar,
      add_comm] using hray
  · intro hray
    apply (mem_horizonCone_epigraph_iff_horizonFunction_le_of_isProper hproper).1
    apply mem_horizonCone_of_forall_smul_add_mem
      (C := epigraph f) (x := (xbar, rbar)) (w := (w, a))
    intro τ hτ
    rw [mem_epigraph_iff]
    rcases hτ.eq_or_lt with rfl | hτ
    · simp [hrbar] at hxepi ⊢
    · have h := hray τ hτ
      simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hrbar,
        add_comm] using h

/-- The real ray difference quotient appearing in formula 3(4). -/
noncomputable def rayDifferenceQuotient
    (f : E → ℝ) (xbar w : E) (τ : ℝ) : ℝ :=
  (f (xbar + τ • w) - f xbar) / τ

/-- Convexity makes the positive ray difference quotient monotone. -/
theorem monotoneOn_rayDifferenceQuotient
    {f : E → ℝ}
    (hconv : Convex ℝ (epigraph (fun x ↦ (f x : EReal))))
    (xbar w : E) :
    MonotoneOn (rayDifferenceQuotient f xbar w) (Set.Ioi 0) := by
  have hconvOn : ConvexOn ℝ Set.univ f := by
    rw [← convex_epigraph_iff_convexOn f Set.univ convex_univ]
    simpa [epigraph, EReal.coe_le_coe_iff] using hconv
  intro τ hτ σ hσ hτσ
  have hσpos : 0 < σ := hσ
  let r : ℝ := τ / σ
  have hr0 : 0 ≤ r := div_nonneg hτ.le hσpos.le
  have hr1 : r ≤ 1 := (div_le_one hσpos).2 hτσ
  have hcombo := hconvOn.2 (Set.mem_univ (xbar + σ • w))
    (Set.mem_univ xbar) hr0 (sub_nonneg.mpr hr1)
    (by ring)
  have hrEq : r * σ = τ := by
    dsimp [r]
    exact div_mul_cancel₀ τ hσpos.ne'
  have hpoint :
      r • (xbar + σ • w) + (1 - r) • xbar = xbar + τ • w := by
    calc
      r • (xbar + σ • w) + (1 - r) • xbar =
          (r + (1 - r)) • xbar + (r * σ) • w := by
            module
      _ = xbar + τ • w := by
            rw [hrEq]
            module
  rw [hpoint] at hcombo
  dsimp [rayDifferenceQuotient]
  have hineq :
      f (xbar + τ • w) ≤ r * f (xbar + σ • w) + (1 - r) * f xbar := by
    simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hcombo
  dsimp [r] at hineq ⊢
  rw [div_le_div_iff₀ hτ hσpos]
  field_simp [hσpos.ne'] at hineq ⊢
  nlinarith

/-- The EReal-valued ray quotient on the positive half-line. -/
noncomputable def rayDifferenceQuotientEReal (f : E → ℝ) (xbar w : E)
    (τ : {τ : ℝ // 0 < τ}) : EReal :=
  (rayDifferenceQuotient f xbar w τ : ℝ)

/-- Formula 3(4), supremum clause, for a real-valued proper closed convex
function. -/
theorem horizonFunction_eq_iSup_rayDifferenceQuotient
    {f : E → ℝ}
    (hconv : Convex ℝ (epigraph (fun x ↦ (f x : EReal))))
    (hlsc : LowerSemicontinuous (fun x ↦ (f x : EReal)))
    (xbar w : E) :
    horizonFunction (fun x ↦ (f x : EReal)) w =
      ⨆ τ : {τ : ℝ // 0 < τ}, rayDifferenceQuotientEReal f xbar w τ := by
  let fE : E → EReal := fun x ↦ (f x : EReal)
  have hproper : IsProper fE := by
    refine ⟨⟨xbar, EReal.coe_lt_top _⟩, fun x ↦ EReal.bot_lt_coe _⟩
  apply ereal_eq_of_forall_real_upper_bounds
  intro a
  rw [horizonFunction_le_coe_iff_forall_ray_le
    hconv hlsc hproper (xbar := xbar)
    (by simp [mem_effectiveDomain_iff])]
  constructor
  · intro h
    refine iSup_le fun τ ↦ ?_
    have hτ := h τ τ.property
    change ((rayDifferenceQuotient f xbar w τ : ℝ) : EReal) ≤ (a : EReal)
    have hτreal :
        f (xbar + (τ : ℝ) • w) ≤ f xbar + (τ : ℝ) * a := by
      exact_mod_cast hτ
    exact_mod_cast (show rayDifferenceQuotient f xbar w τ ≤ a by
      rw [rayDifferenceQuotient, div_le_iff₀ τ.property]
      linarith)
  · intro h τ hτ
    let t : {t : ℝ // 0 < t} := ⟨τ, hτ⟩
    have ht :
        rayDifferenceQuotientEReal f xbar w t ≤ (a : EReal) :=
      (le_iSup (fun s : {s : ℝ // 0 < s} ↦
        rayDifferenceQuotientEReal f xbar w s) t).trans h
    have htReal : rayDifferenceQuotient f xbar w τ ≤ a := by
      change
        ((rayDifferenceQuotient f xbar w τ : ℝ) : EReal) ≤
          (a : EReal) at ht
      exact_mod_cast ht
    have hreal :
        f (xbar + τ • w) ≤ f xbar + τ * a := by
      rw [rayDifferenceQuotient, div_le_iff₀ hτ] at htReal
      linarith
    exact_mod_cast hreal

/-- Formula 3(4), limit clause: the positive ray difference quotients tend to
their supremum, namely the horizon value. -/
theorem tendsto_rayDifferenceQuotientEReal_atTop
    {f : E → ℝ}
    (hconv : Convex ℝ (epigraph (fun x ↦ (f x : EReal))))
    (hlsc : LowerSemicontinuous (fun x ↦ (f x : EReal)))
    (xbar w : E) :
    Tendsto (rayDifferenceQuotientEReal f xbar w) atTop
      (𝓝 (horizonFunction (fun x ↦ (f x : EReal)) w)) := by
  rw [horizonFunction_eq_iSup_rayDifferenceQuotient hconv hlsc xbar w]
  apply tendsto_atTop_iSup
  intro τ σ hτσ
  have hmono :=
    monotoneOn_rayDifferenceQuotient hconv xbar w τ.property σ.property hτσ
  change
    ((rayDifferenceQuotient f xbar w τ : ℝ) : EReal) ≤
      ((rayDifferenceQuotient f xbar w σ : ℝ) : EReal)
  exact_mod_cast hmono

end RayFormula

end RW
