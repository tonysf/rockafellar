/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Estimates on the Euclidean epigraph distances
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import RockafellarWets.Chapter3.HomogeneousCompletion
import RockafellarWets.Chapter4.ConeSetDistances
import RockafellarWets.Chapter7.EpiDistances

open Filter Metric Set Topology
open scoped NNReal

namespace RW

section UnclosedSets

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {C D : Set V}

private theorem rhoDistance_closure (r : ℝ≥0) :
    rhoDistance r (closure C) (closure D) = rhoDistance r C D := by
  have hd (A : Set V) : distanceProfile r (closure A) = distanceProfile r A :=
    ContinuousMap.ext fun _ ↦ infDist_closure
  simp [rhoDistance, hd]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- At a strictly smaller cutoff, truncating the closures cannot increase
the excess beyond the original excess at the larger cutoff. -/
private theorem rhoHatDistance_closure_le_of_lt (hC : C.Nonempty) (hD : D.Nonempty)
    {r s : ℝ≥0} (hrs : r < s) :
    rhoHatDistance r (closure C) (closure D) ≤ rhoHatDistance s C D := by
  let e := rhoHatDistance s C D
  have he : 0 ≤ e := rhoHatDistance_nonneg _ _ _
  have hi := (rhoHatDistance_le_iff s hC hD he).mp le_rfl
  have dir {A B : Set V} (hi : A ∩ closedBall 0 (s : ℝ) ⊆ cthickening e B) :
      closure A ∩ closedBall 0 (r : ℝ) ⊆ cthickening e (closure B) := by
    rw [cthickening_closure]
    intro x hx
    have hb : x ∈ ball 0 (s : ℝ) := lt_of_le_of_lt (show dist x 0 ≤ (r : ℝ) from hx.2) (show (r : ℝ) < (s : ℝ) from hrs)
    apply closure_minimal (t := cthickening e B) (s := ball 0 (s : ℝ) ∩ A)
      (fun _ h ↦ hi ⟨h.2, ball_subset_closedBall h.1⟩) isClosed_cthickening
    exact isOpen_ball.inter_closure ⟨hb, hx.1⟩
  exact (rhoHatDistance_le_iff r hC.closure hD.closure he).mpr ⟨dir hi.1, dir hi.2⟩

private theorem rhoDistance_zero_le_rhoHatDistance (hC : C.Nonempty) (hD : D.Nonempty)
    {s : ℝ≥0} (hs : max (infDist 0 C) (infDist 0 D) ≤ (s : ℝ)) :
    rhoDistance 0 C D ≤ rhoHatDistance s C D := by
  let e := rhoHatDistance s C D
  have he : 0 ≤ e := rhoHatDistance_nonneg _ _ _
  have hi := (rhoHatDistance_le_iff s hC hD he).mp le_rfl
  have dir {A B : Set V} (hA : A.Nonempty) (hB : B.Nonempty) (hb : infDist 0 B ≤ s)
      (hi : A ∩ closedBall 0 (s : ℝ) ⊆ cthickening e B) :
      infDist 0 B - infDist 0 A ≤ e := by
    by_contra! h
    obtain ⟨x, hxA, hx⟩ := (infDist_lt_iff hA).mp (show infDist 0 A < infDist 0 B - e by linarith)
    have hb' : x ∈ closedBall 0 (s : ℝ) := by
      rw [mem_closedBall, dist_comm]
      linarith
    have hh := mem_cthickening_iff.mp (hi ⟨hxA, hb'⟩)
    have hxB := (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hB) he).mp hh
    change infDist x B ≤ e at hxB
    have htriangle : infDist (0 : V) B ≤ infDist x B + dist 0 x := infDist_le_infDist_add_dist
    linarith
  apply (rhoDistance_le_iff he 0 C D).mpr
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  subst x
  rw [abs_le]
  constructor
  · linarith [dir hC hD ((le_max_right _ _).trans hs) hi.1]
  · exact dir hD hC ((le_max_left _ _).trans hs) hi.2

/-- A comparison at all smaller radii for the closed sets extends to the
original sets and the endpoint radius, by continuity of the first distance. -/
private theorem extend_rhoDistance_le (hC : C.Nonempty) (hD : D.Nonempty)
    {r s : ℝ≥0} {k : ℝ} (hk : 0 < k)
    (hs : k * (r : ℝ) + max (infDist 0 C) (infDist 0 D) ≤ s)
    (hcl : ∀ a b : ℝ≥0, k * (a : ℝ) + max (infDist 0 C) (infDist 0 D) ≤ b →
      rhoDistance a (closure C) (closure D) ≤ rhoHatDistance b (closure C) (closure D)) :
    rhoDistance r C D ≤ rhoHatDistance s C D := by
  by_cases hr : r = 0
  · subst r
    exact rhoDistance_zero_le_rhoHatDistance hC hD (by simpa using hs)
  · have hrpos : 0 < r := lt_of_le_of_ne (zero_le _) (Ne.symm hr)
    haveI : NeBot (𝓝[<] r) := nhdsLT_neBot_of_exists_lt ⟨0, hrpos⟩
    apply le_of_tendsto ((continuous_rhoDistance C D).continuousAt.continuousWithinAt
      (s := Iio r))
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : (a : ℝ) < r := ha
    let b : ℝ≥0 := ⟨k * (a : ℝ) + max (infDist 0 C) (infDist 0 D),
      add_nonneg (mul_nonneg hk.le a.2) (infDist_nonneg.trans (le_max_left _ _))⟩
    have hbs : b < s := by
      change k * (a : ℝ) + _ < (s : ℝ)
      linarith [mul_lt_mul_of_pos_left ha' hk]
    rw [← rhoDistance_closure]
    exact (hcl a b le_rfl).trans (rhoHatDistance_closure_le_of_lt hC hD hbs)

end UnclosedSets

section Estimates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f g : E → EReal}

/-- Distance from the origin of the product space to an epigraph. -/
noncomputable def epiOriginDistance (f : E → EReal) : ℝ := infDist 0 (euclideanEpigraph f)

/-- **Exercise 7.60(a)**, monotonicity of both distances. -/
theorem monotone_rhoEpiDistances (hf : (effectiveDomain f).Nonempty)
    (hg : (effectiveDomain g).Nonempty) :
    Monotone (fun r ↦ rhoEpiDistance r f g) ∧ Monotone (fun r ↦ rhoHatEpiDistance r f g) :=
  ⟨fun _ _ h ↦ rhoDistance_mono h _ _, fun _ _ h ↦
    rhoHatDistance_mono h (euclideanEpigraph_nonempty hf) (euclideanEpigraph_nonempty hg)⟩

/-- **Exercise 7.60(b)**. -/
theorem continuous_rhoEpiDistance (f g : E → EReal) : Continuous (fun r ↦ rhoEpiDistance r f g) :=
  continuous_rhoDistance _ _

/-- **Exercise 7.60(c)** for arbitrary extended-real functions with nonempty domains. -/
theorem rhoHatEpiDistance_le_rhoEpiDistance_le {r s : ℝ≥0}
    (hf : (effectiveDomain f).Nonempty) (hg : (effectiveDomain g).Nonempty)
    (hs : 2 * (r : ℝ) + max (epiOriginDistance f) (epiOriginDistance g) ≤ s) :
    rhoHatEpiDistance r f g ≤ rhoEpiDistance r f g ∧ rhoEpiDistance r f g ≤ rhoHatEpiDistance s f g := by
  have hC := euclideanEpigraph_nonempty hf
  have hD := euclideanEpigraph_nonempty hg
  refine ⟨rhoHatDistance_le_rhoDistance r hC hD, extend_rhoDistance_le hC hD (by norm_num) hs ?_⟩
  intro a b hb
  exact rhoDistance_le_rhoHatDistance_of_two_mul isClosed_closure isClosed_closure hC.closure hD.closure
    (by simpa only [infDist_closure] using hb)

/-- **Exercise 7.60(d)**. -/
theorem rhoEpiDistance_le_max_epiOriginDistance_add (r : ℝ≥0) (f g : E → EReal) :
    rhoEpiDistance r f g ≤ max (epiOriginDistance f) (epiOriginDistance g) + r :=
  rhoDistance_le_max_infDist_zero_add r _ _

/-- **Exercise 7.60(e)**. -/
theorem abs_rhoEpiDistance_sub_le (r s : ℝ≥0) (f g : E → EReal) :
    |rhoEpiDistance r f g - rhoEpiDistance s f g| ≤ 2 * |(r : ℝ) - s| :=
  abs_rhoDistance_sub_rhoDistance_le r s _ _

/-- **Exercise 7.60(f,g)**, the two integrated estimates. -/
theorem epiDistance_bounds (r : ℝ≥0) (f g : E → EReal) :
    (1 - Real.exp (-(r : ℝ))) * |epiOriginDistance f - epiOriginDistance g| +
        Real.exp (-(r : ℝ)) * rhoEpiDistance r f g ≤ epiDistance f g ∧
    epiDistance f g ≤ (1 - Real.exp (-(r : ℝ))) * rhoEpiDistance r f g +
      Real.exp (-(r : ℝ)) * (max (epiOriginDistance f) (epiOriginDistance g) + r + 1) := by
  unfold rhoEpiDistance
  rw [← rhoDistanceReal_coe r]
  exact ⟨integratedSetDistance_ge r.2 _ _, integratedSetDistance_le r.2 _ _⟩

/-- **Exercise 7.60(h)**. -/
theorem epiDistance_origin_bounds (f g : E → EReal) :
    |epiOriginDistance f - epiOriginDistance g| ≤ epiDistance f g ∧
      epiDistance f g ≤ max (epiOriginDistance f) (epiOriginDistance g) + 1 :=
  ⟨abs_infDist_zero_sub_le_integratedSetDistance _ _, integratedSetDistance_le_max_infDist_zero_add_one _ _⟩

end Estimates

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f g : E → EReal}

/-- The convex sharpening in **Exercise 7.60**. -/
theorem rhoEpiDistance_le_rhoHatEpiDistance_of_convex {r s : ℝ≥0}
    (hf : (effectiveDomain f).Nonempty) (hg : (effectiveDomain g).Nonempty)
    (hfc : Convex ℝ (epigraph f)) (hgc : Convex ℝ (epigraph g))
    (hs : (r : ℝ) + max (epiOriginDistance f) (epiOriginDistance g) ≤ s) :
    rhoEpiDistance r f g ≤ rhoHatEpiDistance s f g := by
  have hC := euclideanEpigraph_nonempty hf
  have hD := euclideanEpigraph_nonempty hg
  let T := (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toLinearMap
  have hCconv : Convex ℝ (euclideanEpigraph f) := hfc.linear_preimage T
  have hDconv : Convex ℝ (euclideanEpigraph g) := hgc.linear_preimage T
  apply extend_rhoDistance_le hC hD (k := 1) zero_lt_one (by simpa using hs)
  intro a b hb
  exact rhoDistance_le_rhoHatDistance_of_convex isClosed_closure isClosed_closure hC.closure hD.closure
    hCconv.closure hDconv.closure (by simpa only [one_mul, infDist_closure] using hb)

/-- Equality for convex epigraphs containing the origin in **Exercise 7.60**. -/
theorem rhoHatEpiDistance_eq_rhoEpiDistance_of_convex (r : ℝ≥0)
    (hfc : Convex ℝ (epigraph f)) (hgc : Convex ℝ (epigraph g)) (hf0 : f 0 ≤ 0) (hg0 : g 0 ≤ 0) :
    rhoHatEpiDistance r f g = rhoEpiDistance r f g := by
  have hf : (effectiveDomain f).Nonempty := ⟨0, hf0.trans_lt (by simp)⟩
  have hg : (effectiveDomain g).Nonempty := ⟨0, hg0.trans_lt (by simp)⟩
  refine le_antisymm (rhoHatDistance_le_rhoDistance r (euclideanEpigraph_nonempty hf)
    (euclideanEpigraph_nonempty hg)) (rhoEpiDistance_le_rhoHatEpiDistance_of_convex hf hg hfc hgc ?_)
  have hC : (0 : WithLp 2 (E × ℝ)) ∈ euclideanEpigraph f := by simpa [euclideanEpigraph, epigraph] using hf0
  have hD : (0 : WithLp 2 (E × ℝ)) ∈ euclideanEpigraph g := by simpa [euclideanEpigraph, epigraph] using hg0
  simp [epiOriginDistance, infDist_zero_of_mem hC, infDist_zero_of_mem hD]

/-- The homogeneous equalities and linear dependence on radius in **Exercise 7.60**.
The cones need not be closed or convex. -/
theorem rhoEpiDistances_of_positivelyHomogeneous (r : ℝ≥0)
    (hf : PositivelyHomogeneous f) (hg : PositivelyHomogeneous g) :
    rhoHatEpiDistance r f g = rhoEpiDistance r f g ∧
      rhoHatEpiDistance r f g = (r : ℝ) * rhoHatEpiDistance 1 f g ∧
      rhoEpiDistance r f g = (r : ℝ) * rhoEpiDistance 1 f g := by
  have hcone {u : E → EReal} (hu : PositivelyHomogeneous u) : IsCone (euclideanEpigraph u) := by
    have hc := isCone_epigraph_of_positivelyHomogeneous hu
    exact ⟨hc.1, fun _ hz _ hpos ↦ hc.2 hz hpos⟩
  have hC := hcone hf
  have hD := hcone hg
  have heq (s : ℝ≥0) : rhoHatEpiDistance s f g = rhoEpiDistance s f g := by
    refine le_antisymm (rhoHatDistance_le_rhoDistance s ⟨_,hC.1⟩ ⟨_,hD.1⟩) ?_
    apply extend_rhoDistance_le ⟨_, hC.1⟩ ⟨_, hD.1⟩ (k := 1) zero_lt_one
    · simp [infDist_zero_of_mem hC.1, infDist_zero_of_mem hD.1]
    · intro a b hab
      have hab' : a ≤ b := by
        simpa only [one_mul, infDist_zero_of_mem hC.1, infDist_zero_of_mem hD.1, max_self, add_zero] using hab
      rw [← rhoHatDistance_eq_rhoDistance_of_isCone a isClosed_closure isClosed_closure hC.closure hD.closure]
      exact rhoHatDistance_mono hab' ⟨_, hC.closure.1⟩ ⟨_, hD.closure.1⟩
  have hlin := rhoDistance_isCone_eq hC hD r
  exact ⟨heq r, by rw [heq r, heq 1]; exact hlin, hlin⟩

end Euclidean
end RW
