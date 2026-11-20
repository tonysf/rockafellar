/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: subsmoothness under epi-addition

**Theorem 10.56**, upper-`Cᵏ` clauses: for `f = g □ h` with `g` proper lsc, `h : ℝⁿ → ℝ`, and the
level sets `{w | g(w) + h(x - w) ≤ α}` locally bounded in `x`, if `h` is upper-`C¹` then `f` is
upper-`C¹`, and if `h` is upper-`C²` then `f` is upper-`C²` (`isUpperCOn_epiSum`, for every
`k ≥ 1`).  As in the book, around `x̄` with compact `V = IB(x̄, 1)` and
`T = {(z, w) | z ∈ V, w ∈ P(z)}` (compact by `epiAddition_minimizers_compact_graph`),
`f(x) = min_{(z, w) ∈ T} (f(z) - h(z - w) + h(x - w))` on `int V`, and 10.54 applied to `-h` on the
compact set `V - P(V)` turns this into a representation of `-f`
(`LowerRepresentation.minTranslates`).
-/

import RockafellarWets.Chapter10.EpiAdditionMinimizers
import RockafellarWets.Chapter10.SubsmoothRepresentations

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- If `-h = max_s L_s` on an open set `O'` and `f(x) = min_{t ∈ T} (a t + h(x - b t))` for
`x ∈ W` with `T` compact, `a`, `b` continuous and `x - b t ∈ O'`, then `-f` has the
representation `-f(x) = max_{(s, t)} (-a t + L_s(x - b t))` on `W`. -/
def LowerRepresentation.minTranslates {k : ℕ∞} {h f : E → ℝ} {O' W : Set E}
    (R : LowerRepresentation k (fun u ↦ -h u) O') (hO' : IsOpen O')
    (T : Type u) [TopologicalSpace T] [CompactSpace T] (a : T → ℝ) (b : T → E)
    (ha : Continuous a) (hb : Continuous b) (hmem : ∀ t, ∀ x ∈ W, x - b t ∈ O')
    (hle : ∀ t, ∀ x ∈ W, f x ≤ a t + h (x - b t))
    (heq : ∀ x ∈ W, ∃ t, f x = a t + h (x - b t)) :
    LowerRepresentation k (fun x ↦ -f x) W :=
  LowerRepresentation.mk (R.T × T) (fun p x ↦ -a p.2 + R.F p.1 (x - b p.2))
    (fun p ↦ contDiffOn_const.add ((R.contDiffOn p.1).comp
      (contDiffOn_id.sub contDiffOn_const) fun x hx ↦ hmem p.2 x hx))
    (fun j hj ↦ by
      have hΦ : ContinuousOn (fun p : (R.T × T) × E ↦ ((p.1.1, p.2 - b p.1.2) : R.T × E))
          (univ ×ˢ W) :=
        (continuous_fst.comp continuous_fst).prodMk
          (continuous_snd.sub (hb.comp (continuous_snd.comp continuous_fst))) |>.continuousOn
      have hmaps : MapsTo (fun p : (R.T × T) × E ↦ ((p.1.1, p.2 - b p.1.2) : R.T × E))
          (univ ×ˢ W) (univ ×ˢ O') := fun p hp ↦ ⟨trivial, hmem p.1.2 p.2 hp.2⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · have hv : ContinuousOn (fun p : (R.T × T) × E ↦ -a p.1.2 + R.F p.1.1 (p.2 - b p.1.2))
            (univ ×ˢ W) :=
          ((ha.comp (continuous_snd.comp continuous_fst)).neg.continuousOn).add
            (R.continuousOn_val.comp hΦ hmaps)
        refine ((continuousMultilinearCurryFin0 ℝ E ℝ).symm.continuous.comp_continuousOn
          hv).congr fun p _ ↦ ?_
        rw [iteratedFDeriv_zero_eq_comp]
        rfl
      · refine ((R.continuousOn_iteratedFDeriv j hj).comp hΦ hmaps).congr fun p hp ↦ ?_
        have hL : ContDiffAt ℝ j (fun x ↦ R.F p.1.1 (x - b p.1.2)) p.2 := by
          have h1 : ContDiffAt ℝ j (R.F p.1.1) (p.2 - b p.1.2) :=
            ((R.contDiffOn p.1.1).contDiffAt (hO'.mem_nhds (hmem p.1.2 p.2 hp.2))).of_le
              (by exact_mod_cast hj)
          exact h1.comp p.2 (contDiffAt_id.sub contDiffAt_const)
        show iteratedFDeriv ℝ j (fun x ↦ -a p.1.2 + R.F p.1.1 (x - b p.1.2)) p.2 =
          iteratedFDeriv ℝ j (R.F p.1.1) (p.2 - b p.1.2)
        rw [iteratedFDeriv_add_apply' contDiffAt_const hL, iteratedFDeriv_const_of_ne hj0.ne',
          Pi.zero_apply, zero_add, iteratedFDeriv_comp_sub])
    (fun p x hx ↦ by
      have h1 := R.le p.1 (x - b p.2) (hmem p.2 x hx)
      have h2 := hle p.2 x hx
      simp only at h1 ⊢
      linarith)
    (fun x hx ↦ by
      obtain ⟨t, ht⟩ := heq x hx
      obtain ⟨s, hs⟩ := R.exists_eq (x - b t) (hmem t x hx)
      refine ⟨(s, t), ?_⟩
      simp only at hs ⊢
      rw [hs, ht]
      ring)

/-- **Theorem 10.56**, upper-`Cᵏ` clauses for the parametric value
`f(x) = inf_w (g(w) + h(x - w))`: if `h` is upper-`Cᵏ` (`k ≥ 1`), so is `f`. -/
theorem isUpperCOn_epiAdditionValue {k : ℕ∞} (hk : 1 ≤ k) {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hhu : IsUpperCOn k h univ)
    (hb : EpiAdditionLocallyBounded g h) :
    IsUpperCOn k (fun x ↦ (parametricValue (epiAdditionIntegrand g h) x).toReal) univ := by
  have hhc : Continuous h := by
    have h1 : ContinuousOn (fun u ↦ -h u) univ := IsLowerCOn.continuousOn hhu hk
    simpa using (continuousOn_univ.1 h1).neg
  set P := parametricMinimizers (epiAdditionIntegrand g h) with hP
  set f : E → ℝ := fun x ↦ (parametricValue (epiAdditionIntegrand g h) x).toReal with hf
  have hfin : ∀ x, parametricValue (epiAdditionIntegrand g h) x = (f x : EReal) :=
    epiAddition_value_finite hp hl hhc hb
  have hfc : Continuous f := continuous_epiAdditionValue_toReal hp hl hhc hb
  obtain ⟨hne, -, -⟩ := epiAddition_minimizers_properties hp hl hhc hb
  have hmin : ∀ x z w, w ∈ P z → f x ≤ f z - h (z - w) + h (x - w) := by
    intro x z w hw
    have hw' := (mem_paramArgmin_iff _ z w).1 hw
    have h1 : g w + (h (z - w) : EReal) = (f z : EReal) := by
      have h0 := hw'.1
      change g w + (h (z - w) : EReal) = parametricValue (epiAdditionIntegrand g h) z at h0
      rw [h0, hfin z]
    have hgt : g w ≠ ⊤ := by
      intro ht
      rw [ht, EReal.top_add_coe] at h1
      exact EReal.coe_ne_top _ h1.symm
    have hga : g w = ((g w).toReal : EReal) := (EReal.coe_toReal hgt (hp.2 w).ne').symm
    rw [hga, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h1
    have h2 : parametricValue (epiAdditionIntegrand g h) x ≤ g w + (h (x - w) : EReal) :=
      iInf_le (fun w' : E ↦ epiAdditionIntegrand g h (WithLp.toLp 2 (w', x))) w
    rw [hfin x, hga, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    linarith
  intro x₀ _
  set V := closedBall x₀ 1 with hV
  have hVc : IsCompact V := isCompact_closedBall x₀ 1
  set T := {p : E × E | p.1 ∈ V ∧ p.2 ∈ P p.1} with hT
  have hTc : IsCompact T := epiAddition_minimizers_compact_graph hp hl hhc hb hVc
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hTc
  have hPV : IsCompact (svImage P V) := epiAddition_minimizers_compact_image hp hl hhc hb hVc
  set B := (fun q : E × E ↦ q.1 - q.2) '' (V ×ˢ svImage P V) with hB
  have hBc : IsCompact B := (hVc.prod hPV).image (continuous_fst.sub continuous_snd)
  obtain ⟨O', hO'o, hBO', -, ⟨R⟩⟩ :=
    IsLowerCOn.exists_common_representation hhu hk hBc (subset_univ B)
  have hmem : ∀ t : T, ∀ x ∈ ball x₀ 1, x - (t : E × E).2 ∈ O' := by
    intro t x hx
    apply hBO'
    exact ⟨(x, (t : E × E).2), ⟨ball_subset_closedBall hx,
      mem_svImage.2 ⟨(t : E × E).1, t.2.1, t.2.2⟩⟩, rfl⟩
  refine ⟨ball x₀ 1, isOpen_ball, mem_ball_self one_pos, subset_univ _, ⟨?_⟩⟩
  exact R.minTranslates hO'o T (fun t ↦ f (t : E × E).1 - h ((t : E × E).1 - (t : E × E).2))
    (fun t ↦ (t : E × E).2)
    ((hfc.comp (continuous_fst.comp continuous_subtype_val)).sub
      (hhc.comp ((continuous_fst.comp continuous_subtype_val).sub
        (continuous_snd.comp continuous_subtype_val))))
    (continuous_snd.comp continuous_subtype_val) hmem
    (fun t x _ ↦ hmin x _ _ t.2.2)
    (fun x hx ↦ by
      obtain ⟨w, hw⟩ := hne x
      exact ⟨⟨(x, w), ball_subset_closedBall hx, hw⟩, by ring⟩)

/-- **Theorem 10.56** (properties under epi-addition), upper-`Cᵏ` clauses: if `h` is upper-`C¹`
then `f = g □ h` is upper-`C¹`, and if `h` is upper-`C²` then `f` is upper-`C²` (any `k ≥ 1`). -/
theorem isUpperCOn_epiSum {k : ℕ∞} (hk : 1 ≤ k) {g : E → EReal} {h : E → ℝ} (hp : IsProper g)
    (hl : LowerSemicontinuous g) (hhu : IsUpperCOn k h univ)
    (hb : EpiAdditionLocallyBounded g h) :
    IsUpperCOn k (fun x ↦ (epiSum g (fun y ↦ (h y : EReal)) x).toReal) univ := by
  rw [← parametricValue_epiAdditionIntegrand]
  exact isUpperCOn_epiAdditionValue hk hp hl hhu hb

end RW
