/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Lipschitz continuity of set-valued mappings

The finite-radius moduli are ordinary Lipschitz moduli of the distance profiles of
Chapter 4. This identifies the punctured two-point limsup with the infimum of local
Lipschitz constants, including at isolated points of the relative set.
-/

import RockafellarWets.Chapter4.LocalSetDistances
import RockafellarWets.Chapter4.HausdorffConvergence
import RockafellarWets.Chapter5.LocalBoundedness
import RockafellarWets.Chapter9.LipschitzModulus

open Filter Metric Set Topology
open scoped NNReal ENNReal Pointwise

namespace RW

variable {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- Nonempty closed fibers on the specified set. -/
def NonemptyClosedValuedOn (S : E → Set F) (X : Set E) : Prop :=
  ∀ x ∈ X, (S x).Nonempty ∧ IsClosed (S x)

/-- **Definition 9.26.** Global Hausdorff-Lipschitz continuity on a set with a given modulus. -/
def SvLipschitzOnWith (k : ℝ≥0) (S : E → Set F) (X : Set E) : Prop :=
  NonemptyClosedValuedOn S X ∧ ∀ a ∈ X, ∀ b ∈ X,
    hausdorffEDist (S a) (S b) ≤ ENNReal.ofReal (k*dist a b)

def SvLipschitzOn (S : E → Set F) (X : Set E) : Prop := ∃ k, SvLipschitzOnWith k S X

theorem SvLipschitzOnWith.mono {S : E → Set F} {X Y : Set E} {k : ℝ≥0}
    (h : SvLipschitzOnWith k S X) (hYX : Y ⊆ X) : SvLipschitzOnWith k S Y :=
  ⟨fun a ha ↦ h.1 a (hYX ha),fun a ha b hb ↦ h.2 a (hYX ha) b (hYX hb)⟩

/-- A closed nonempty fiber realizes each distance bound by a point. -/
theorem exists_mem_dist_le_iff_infEDist_le [ProperSpace F] {D : Set F} (hn : D.Nonempty) (hc : IsClosed D)
    (v : F) {r : ℝ} (hr : 0 ≤ r) : (∃ z ∈ D, dist v z ≤ r) ↔ infEDist v D ≤ ENNReal.ofReal r := by
  rw [ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hn) hr]
  change (∃ z ∈ D, dist v z ≤ r) ↔ infDist v D ≤ r
  refine ⟨fun ⟨z,hz,hd⟩ ↦ (infDist_le_dist_of_mem hz).trans hd, fun hd ↦ ?_⟩
  obtain ⟨z,hz,he⟩ := hc.exists_infDist_eq_dist hn v
  exact ⟨z,hz,he ▸ hd⟩

/-- The equivalent fiber-inclusion form of Definition 9.26. -/
theorem svLipschitzOnWith_iff_transport [ProperSpace F] {S : E → Set F} {X : Set E} {k : ℝ≥0}
    (hS : NonemptyClosedValuedOn S X) : SvLipschitzOnWith k S X ↔
      ∀ a ∈ X, ∀ b ∈ X, ∀ v ∈ S a, ∃ z ∈ S b, dist v z ≤ k*dist a b := by
  constructor
  · intro h a ha b hb v hv
    apply (exists_mem_dist_le_iff_infEDist_le (hS b hb).1 (hS b hb).2 _ (by positivity)).2
    exact (infEDist_le_hausdorffEDist_of_mem hv).trans (h.2 a ha b hb)
  · intro h
    refine ⟨hS,fun a ha b hb ↦ hausdorffEDist_le_of_infEDist (fun v hv ↦ ?_) (fun z hz ↦ ?_)⟩
    · exact (exists_mem_dist_le_iff_infEDist_le (hS b hb).1 (hS b hb).2 _ (by positivity)).1 (h a ha b hb v hv)
    · rw [dist_comm a b]
      exact (exists_mem_dist_le_iff_infEDist_le (hS a ha).1 (hS a ha).2 _ (by positivity)).1 (h b hb a ha z hz)

theorem svLipschitzOnWith_singleton_iff {g : E → F} {X : Set E} {k : ℝ≥0} :
    SvLipschitzOnWith k (fun a ↦ {g a}) X ↔ LipschitzOnWith k g X := by
  refine ⟨fun h ↦ LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_,fun h ↦ ?_⟩
  · have hh := h.2 a ha b hb
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg k.2 dist_nonneg)).1
    simpa only [hausdorffEDist_singleton,edist_dist] using hh
  · refine ⟨fun a _ ↦ ⟨singleton_nonempty _,isClosed_singleton⟩,fun a ha b hb ↦ ?_⟩
    simpa only [hausdorffEDist_singleton,edist_dist] using ENNReal.ofReal_le_ofReal (h.dist_le_mul a ha b hb)

end RW

namespace RW

variable {E F : Type*} [MetricSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The bounded-radius estimate 9(11), represented by distance profiles on the output ball. -/
def SvRhoLipschitzOnWith (k ρ : ℝ≥0) (S : E → Set F) (X : Set E) : Prop :=
  LipschitzOnWith k (fun a ↦ distanceProfile ρ (S a)) X

/-- **Definition 9.27.** The constant can depend on the radius of the output truncation. -/
def SvSubLipschitzOn (S : E → Set F) (X : Set E) : Prop :=
  NonemptyClosedValuedOn S X ∧ ∀ ρ : ℝ≥0, ∃ k : ℝ≥0, SvRhoLipschitzOnWith k ρ S X

/-- **Definition 9.28.** The relative finite-radius Lipschitz modulus. -/
noncomputable abbrev svLipschitzModulusWithin (S : E → Set F) (X : Set E) (ρ : ℝ≥0) (x : E) :=
  lipschitzModulusWithin (fun a ↦ distanceProfile ρ (S a)) X x

noncomputable abbrev svLipschitzModulus (S : E → Set F) (ρ : ℝ≥0) (x : E) :=
  svLipschitzModulusWithin S univ ρ x

/-- Definition 9.28 relative to the input set `X`. -/
def SvStrictlyContinuousWithinAt (S : E → Set F) (X : Set E) (x : E) : Prop :=
  x ∈ X ∧ (∀ᶠ a in 𝓝[X] x, (S a).Nonempty ∧ IsClosed (S a)) ∧ ∀ ρ : ℝ≥0, svLipschitzModulusWithin S X ρ x < ⊤

abbrev SvStrictlyContinuousAt (S : E → Set F) (x : E) := SvStrictlyContinuousWithinAt S univ x

def SvStrictlyContinuousOn (S : E → Set F) (X : Set E) : Prop := ∀ x ∈ X, SvStrictlyContinuousWithinAt S X x

/-- The displayed two-point limsup of Definition 9.28. -/
theorem svLipschitzModulusWithin_eq_limsup (S : E → Set F) (X : Set E) (ρ : ℝ≥0) (x : E) :
    svLipschitzModulusWithin S X ρ x = limsup (fun p : E × E ↦ ENNReal.ofReal (rhoDistance ρ (S p.1) (S p.2)) / edist p.1 p.2)
      ((𝓝[X] x ×ˢ 𝓝[X] x) ⊓ 𝓟 {p : E × E | p.1 ≠ p.2}) := by
  simpa only [rhoDistance, ← edist_dist] using lipschitzModulusWithin_eq_limsup (fun a ↦ distanceProfile ρ (S a)) X x

theorem svRhoLipschitzOnWith_iff_rhoDistance {S : E → Set F} {X : Set E} {k ρ : ℝ≥0} :
    SvRhoLipschitzOnWith k ρ S X ↔ ∀ a ∈ X, ∀ b ∈ X, rhoDistance ρ (S a) (S b) ≤ k*dist a b :=
  ⟨fun h a ha b hb ↦ h.dist_le_mul a ha b hb, LipschitzOnWith.of_dist_le_mul⟩

/-- Formula 9(8), in its uniform Lipschitz form for the distance functions. -/
theorem svRhoLipschitzOnWith_iff_distance_functions {S : E → Set F} {X : Set E} {k ρ : ℝ≥0} :
    SvRhoLipschitzOnWith k ρ S X ↔ ∀ v ∈ closedBall (0:F) (ρ:ℝ), LipschitzOnWith k (fun a ↦ infDist v (S a)) X := by
  rw [svRhoLipschitzOnWith_iff_rhoDistance]
  constructor
  · intro h v hv
    exact LipschitzOnWith.of_dist_le_mul (fun a ha b hb ↦ by simpa only [Real.dist_eq] using
      (abs_infDist_sub_infDist_le_rhoDistance ρ _ _ hv).trans (h a ha b hb))
  · intro h a ha b hb
    exact (rhoDistance_le_iff (mul_nonneg k.2 dist_nonneg) ..).2 fun v hv ↦ (h v hv).dist_le_mul a ha b hb

/-- Definition 9.27 implies the stated inclusion with precisely the same constant. -/
theorem SvRhoLipschitzOnWith.transport {S : E → Set F} {X : Set E} {k ρ : ℝ≥0} (h : SvRhoLipschitzOnWith k ρ S X)
    (hS : NonemptyClosedValuedOn S X) {a : E} (ha : a ∈ X) {b : E} (hb : b ∈ X)
    {v : F} (hv : v ∈ S a ∩ closedBall (0:F) (ρ:ℝ)) : ∃ z ∈ S b, dist v z ≤ k*dist a b := by
  apply (exists_mem_dist_le_iff_infEDist_le (hS b hb).1 (hS b hb).2 _ (by positivity)).2
  apply (rhoHatDistance_le_iff ρ (hS a ha).1 (hS b hb).1 (by positivity)).1
    ((rhoHatDistance_le_rhoDistance ρ (hS a ha).1 (hS b hb).1).trans (h.dist_le_mul a ha b hb)) |>.1
  exact hv

end RW
