/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A boundary of the global transport formulation

The paragraph after Definition 9.27 says that radius-dependent transport
constants can replace the distance-profile inequalities globally. Without
an additional bound on the fibers' distances from zero, this converse fails.
The following singleton-valued example is on an explicit subset of ℝ².
-/

import RockafellarWets.Chapter9.StrictSetValuedContinuity
import Mathlib.Topology.Instances.Int

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace RW

noncomputable section

/-- A sound global transport characterization for Definition 9.27 when the
fiber distances from zero have one common bound. -/
theorem svSubLipschitzOn_iff_transport_of_bounded_zero_distance
    {E F : Type*} [MetricSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {S : E → Set F} {X : Set E}
    (hS : NonemptyClosedValuedOn S X) {R : ℝ≥0}
    (hR : ∀ a ∈ X, infDist (0:F) (S a) ≤ (R:ℝ)) :
    SvSubLipschitzOn S X ↔ ∀ r : ℝ≥0, ∃ k : ℝ≥0, RhoTransport k r S X := by
  constructor
  · intro h r
    obtain ⟨k,hk⟩ := h.2 r
    exact ⟨k,fun a ha b hb v hv ↦ hk.transport hS ha hb hv⟩
  · intro h
    refine ⟨hS,fun r ↦ ?_⟩
    let s := 2*r+R
    obtain ⟨k,hk⟩ := h s
    refine ⟨k,svRhoLipschitzOnWith_iff_rhoDistance.mpr (fun a ha b hb ↦ ?_)⟩
    have hrad : 2*(r:ℝ)+max (infDist 0 (S a)) (infDist 0 (S b)) ≤ (s:ℝ) := by
      have hh := max_le (hR a ha) (hR b hb)
      simp only [s,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat]
      linarith
    exact (rhoDistance_le_rhoHatDistance_of_two_mul (hS a ha).2 (hS b hb).2
      (hS a ha).1 (hS b hb).1 hrad).trans ((rhoTransport_iff_rhoHatDistance hS).mp hk a ha b hb)

/-- Two points above each natural-number input, with a shrinking vertical gap. -/
def transportCounterPoint (n : ℕ) (b : Bool) : ℝ × ℝ :=
  ((n:ℝ),if b then ((n:ℝ)+1)⁻¹ else 0)

def transportCounterDomain : Set (ℝ × ℝ) :=
  Set.range (fun p : ℕ × Bool ↦ transportCounterPoint p.1 p.2)

/-- The two points over `n` have output values `n` and `2n`. -/
def transportCounterValue (p : ℝ × ℝ) : ℝ := if p.2 = 0 then p.1 else 2*p.1

def transportCounterMap (p : ℝ × ℝ) : Set ℝ := {transportCounterValue p}

private theorem counter_value (n : ℕ) (b : Bool) :
    transportCounterValue (transportCounterPoint n b) = if b then 2*(n:ℝ) else n := by
  cases b <;> simp [transportCounterValue,transportCounterPoint,ne_of_gt (show 0 < (n:ℝ)+1 by positivity)]

private theorem counter_value_bounds (n : ℕ) (b : Bool) :
    (n:ℝ) ≤ |transportCounterValue (transportCounterPoint n b)| ∧
      |transportCounterValue (transportCounterPoint n b)| ≤ 2*(n:ℝ) := by
  rw [counter_value]
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
  · rw [abs_of_nonneg (Nat.cast_nonneg n)]
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n]
  · rw [abs_of_nonneg (by positivity)]
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem counter_dist_index (n m : ℕ) (b c : Bool) :
    |(n:ℝ)-(m:ℝ)| ≤ dist (transportCounterPoint n b) (transportCounterPoint m c) := by
  exact le_max_left _ _

private theorem counter_dist_same (n : ℕ) (b c : Bool) (hbc : b ≠ c) :
    dist (transportCounterPoint n b) (transportCounterPoint n c) = ((n:ℝ)+1)⁻¹ := by
  cases b <;> cases c <;> simp_all [transportCounterPoint,Prod.dist_eq,Real.dist_eq,abs_of_nonneg] <;> positivity

private theorem counter_output_dist_same (n : ℕ) (b c : Bool) (hbc : b ≠ c) :
    dist (transportCounterValue (transportCounterPoint n b))
      (transportCounterValue (transportCounterPoint n c)) = (n:ℝ) := by
  rw [counter_value,counter_value]
  cases b <;> cases c <;> simp_all [Real.dist_eq,abs_of_nonneg,show (n:ℝ)-2*(n:ℝ) = -(n:ℝ) by ring,show 2*(n:ℝ)-(n:ℝ) = n by ring]

/-- Every bounded-output truncation has a global transport constant. -/
theorem transportCounterMap_has_all_transport :
    ∀ r : ℝ≥0, ∃ k : ℝ≥0, RhoTransport k r transportCounterMap transportCounterDomain := by
  intro r
  let k : ℝ≥0 := (r+1)^2+4*r+2
  refine ⟨k,?_⟩
  rintro p ⟨⟨n,b⟩,rfl⟩ q ⟨⟨m,c⟩,rfl⟩ v ⟨hv,hvr⟩
  have hv' : v = transportCounterValue (transportCounterPoint n b) := hv
  subst v
  refine ⟨transportCounterValue (transportCounterPoint m c),rfl,?_⟩
  have hn : (n:ℝ) ≤ (r:ℝ) := (counter_value_bounds n b).1.trans (by simpa using hvr)
  rcases eq_or_ne n m with rfl | hnm
  · rcases eq_or_ne b c with rfl | hbc
    · simp
    · rw [counter_dist_same n b c hbc,counter_output_dist_same n b c hbc]
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
      dsimp [k]
      have hn0 := Nat.cast_nonneg (α := ℝ) n
      nlinarith [r.2]
  · have hnm' : (n:ℤ) ≠ (m:ℤ) := by exact_mod_cast hnm
    have hd1 : 1 ≤ dist (transportCounterPoint n b) (transportCounterPoint m c) := by
      have hI := Int.pairwise_one_le_dist hnm'
      have hI' : 1 ≤ |(n:ℝ)-(m:ℝ)| := by simpa only [Int.dist_eq,Int.cast_natCast] using hI
      exact hI'.trans (counter_dist_index n m b c)
    have hm : (m:ℝ) ≤ n+dist (transportCounterPoint n b) (transportCounterPoint m c) := by
      have hh := neg_le_abs ((n:ℝ)-(m:ℝ))
      have hd := counter_dist_index n m b c
      linarith
    have hdout : dist (transportCounterValue (transportCounterPoint n b))
        (transportCounterValue (transportCounterPoint m c)) ≤ 2*(n:ℝ)+2*(m:ℝ) := by
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (add_le_add (counter_value_bounds n b).2 (counter_value_bounds m c).2)
    have hk : (4:ℝ)*r+2 ≤ (k:ℝ) := by
      dsimp [k]
      nlinarith [sq_nonneg ((r:ℝ)+1)]
    have hr0 : 0 ≤ (r:ℝ) := r.2
    calc
      _ ≤ 2*(n:ℝ)+2*(m:ℝ) := hdout
      _ ≤ (4*(r:ℝ)+2)*dist (transportCounterPoint n b) (transportCounterPoint m c) := by nlinarith
      _ ≤ (k:ℝ)*dist (transportCounterPoint n b) (transportCounterPoint m c) :=
        mul_le_mul_of_nonneg_right hk dist_nonneg

/-- The distance-profile formulation nevertheless fails, already at radius zero. -/
theorem transportCounterMap_not_subLipschitz :
    ¬ SvSubLipschitzOn transportCounterMap transportCounterDomain := by
  rintro ⟨_,h⟩
  obtain ⟨k,hk⟩ := h 0
  have H := (svRhoLipschitzOnWith_iff_distance_functions.mp hk) (0:ℝ) (by simp)
  obtain ⟨n,hn⟩ := exists_nat_gt (k:ℝ)
  have hp (b : Bool) : transportCounterPoint n b ∈ transportCounterDomain := ⟨(n,b),rfl⟩
  have hd := H.dist_le_mul (transportCounterPoint n false) (hp false) (transportCounterPoint n true) (hp true)
  have hv (b : Bool) : infDist (0:ℝ) (transportCounterMap (transportCounterPoint n b)) =
      transportCounterValue (transportCounterPoint n b) := by
    rw [transportCounterMap,infDist_singleton,dist_zero_left,Real.norm_eq_abs,counter_value]
    cases b <;> simp [abs_of_nonneg]
  rw [hv,hv,counter_output_dist_same n false true (by decide),counter_dist_same n false true (by decide)] at hd
  have hi : ((n:ℝ)+1)⁻¹ ≤ 1 := by
    have hh : (1:ℝ) ≤ (n:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    simpa only [one_div] using (div_le_one (a := (1:ℝ)) (b := (n:ℝ)+1) (by positivity)).mpr hh
  exact hn.not_ge (hd.trans (by simpa using mul_le_mul_of_nonneg_left hi k.2))

/-- A concrete failure of the global converse asserted after Definition9.27. -/
theorem subLipschitz_global_transport_converse_counterexample :
    NonemptyClosedValuedOn transportCounterMap transportCounterDomain ∧
      (∀ r : ℝ≥0, ∃ k : ℝ≥0, RhoTransport k r transportCounterMap transportCounterDomain) ∧
      ¬ SvSubLipschitzOn transportCounterMap transportCounterDomain :=
  ⟨fun p _ ↦ ⟨singleton_nonempty _,isClosed_singleton⟩,
    transportCounterMap_has_all_transport,transportCounterMap_not_subLipschitz⟩

end

end RW
