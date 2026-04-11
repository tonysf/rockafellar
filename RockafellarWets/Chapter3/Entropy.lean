/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Entropy Functions

This file starts Exercise 3.51 from Rockafellar & Wets by formalizing the
simplex entropy

`g(y) = ∑ i, y_i log y_i` on the simplex `{y | y_i ≥ 0, ∑ i y_i = 1}`,

extended by `∞` outside the simplex.
-/

import RockafellarWets.Chapter3.PositiveHulls
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Set EReal
open scoped BigOperators

namespace RW

section Entropy

variable {ι : Type*} [Fintype ι]

/-- The standard probability simplex in `ι → ℝ`. -/
def simplexSet : Set (ι → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}

/-- The real-valued entropy core `∑ i, y_i log y_i`. -/
noncomputable def entropyCore (y : ι → ℝ) : ℝ :=
  ∑ i, y i * Real.log (y i)

/-- The simplex entropy from Exercise 3.51, extended by `∞` outside the
simplex. -/
noncomputable def simplexEntropy (y : ι → ℝ) : EReal :=
  indicatorVA (simplexSet (ι := ι)) y + (entropyCore (ι := ι) y : ℝ)

theorem simplexSet_nonempty [Nonempty ι] : (simplexSet (ι := ι)).Nonempty := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  refine ⟨fun j => if j = i0 then 1 else 0, ?_⟩
  constructor
  · intro j
    by_cases hj : j = i0 <;> simp [hj]
  · simp [i0]

theorem simplexEntropy_apply_of_mem {y : ι → ℝ} (hy : y ∈ simplexSet (ι := ι)) :
    simplexEntropy (ι := ι) y = (entropyCore (ι := ι) y : EReal) := by
  rw [simplexEntropy, indicatorVA_apply_mem hy, zero_add]

theorem simplexEntropy_apply_of_not_mem {y : ι → ℝ} (hy : y ∉ simplexSet (ι := ι)) :
    simplexEntropy (ι := ι) y = ⊤ := by
  rw [simplexEntropy, indicatorVA_apply_not_mem hy, EReal.top_add_coe]

theorem isClosed_simplexSet : IsClosed (simplexSet (ι := ι)) := by
  classical
  have hnonneg : IsClosed {y : ι → ℝ | ∀ i, 0 ≤ y i} := by
    simpa [Set.setOf_forall] using
      isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have hsum : IsClosed {y : ι → ℝ | ∑ i, y i = 1} := by
    exact isClosed_eq
      (continuous_finset_sum _ fun i _ => continuous_apply i)
      continuous_const
  simpa [simplexSet, Set.setOf_and] using hnonneg.inter hsum

theorem convex_simplexSet : Convex ℝ (simplexSet (ι := ι)) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx_nonneg, hx_sum⟩
  rcases hy with ⟨hy_nonneg, hy_sum⟩
  constructor
  · intro i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      add_nonneg (mul_nonneg ha (hx_nonneg i)) (mul_nonneg hb (hy_nonneg i))
  · calc
      ∑ i, (a • x + b • y) i
          = a * ∑ i, x i + b * ∑ i, y i := by
              simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
                Finset.mul_sum]
      _ = 1 := by nlinarith [hx_sum, hy_sum, hab]

theorem continuous_entropyCore : Continuous (entropyCore (ι := ι)) := by
  classical
  unfold entropyCore
  refine continuous_finset_sum _ ?_
  intro i hi
  exact Real.Continuous.mul_log (continuous_apply i)

theorem convexOn_coord_entropyCore (i : ι) :
    ConvexOn ℝ (simplexSet (ι := ι)) (fun y : ι → ℝ => y i * Real.log (y i)) := by
  have hpre :
      ConvexOn ℝ
        ((LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) ⁻¹' Set.Ici (0 : ℝ))
        (fun y : ι → ℝ => y i * Real.log (y i)) := by
    simpa [Function.comp, LinearMap.proj_apply] using
      (Real.convexOn_mul_log.comp_linearMap
        (LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i))
  refine hpre.subset ?_ convex_simplexSet
  intro y hy
  exact hy.1 i

theorem convexOn_entropyCore :
    ConvexOn ℝ (simplexSet (ι := ι)) (entropyCore (ι := ι)) := by
  classical
  let s : Finset ι := Finset.univ
  have hsum :
      ConvexOn ℝ (simplexSet (ι := ι))
        (fun y : ι → ℝ => ∑ i ∈ s, y i * Real.log (y i)) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using convexOn_const (0 : ℝ) convex_simplexSet
    | @insert i s hi ih =>
        simpa [Finset.sum_insert, hi] using (convexOn_coord_entropyCore (ι := ι) i).add ih
  simpa [entropyCore, s] using hsum

theorem epigraph_simplexEntropy :
    epigraph (simplexEntropy (ι := ι)) =
      {p : (ι → ℝ) × ℝ | p.1 ∈ simplexSet (ι := ι) ∧ entropyCore (ι := ι) p.1 ≤ p.2} := by
  ext p
  constructor
  · intro hp
    rw [mem_epigraph_iff] at hp
    by_cases hy : p.1 ∈ simplexSet (ι := ι)
    · constructor
      · exact hy
      · rw [simplexEntropy_apply_of_mem (ι := ι) hy] at hp
        exact_mod_cast hp
    · exfalso
      rw [simplexEntropy_apply_of_not_mem (ι := ι) hy] at hp
      simpa using hp
  · rintro ⟨hy, hcore⟩
    rw [mem_epigraph_iff, simplexEntropy_apply_of_mem (ι := ι) hy]
    exact_mod_cast hcore

theorem convex_epigraph_simplexEntropy :
    Convex ℝ (epigraph (simplexEntropy (ι := ι))) := by
  simpa [epigraph_simplexEntropy] using
    (convexOn_entropyCore (ι := ι)).convex_epigraph

theorem lowerSemicontinuous_simplexEntropy :
    LowerSemicontinuous (simplexEntropy (ι := ι)) := by
  have hind : LowerSemicontinuous (indicatorVA (simplexSet (ι := ι))) :=
    lowerSemicontinuous_indicatorVA (C := simplexSet (ι := ι)) isClosed_simplexSet
  have hcore :
      Continuous (fun y : ι → ℝ => (entropyCore (ι := ι) y : EReal)) :=
    continuous_coe_real_ereal.comp continuous_entropyCore
  refine LowerSemicontinuous.add' hind hcore.lowerSemicontinuous ?_
  intro y
  exact EReal.continuousAt_add (.inr (by simp)) (.inr (by simp))

theorem simplexEntropy_isProper [Nonempty ι] :
    IsProper (simplexEntropy (ι := ι)) := by
  constructor
  · rcases simplexSet_nonempty (ι := ι) with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [simplexEntropy_apply_of_mem (ι := ι) hy]
    exact EReal.coe_lt_top (entropyCore (ι := ι) y)
  · intro y
    by_cases hy : y ∈ simplexSet (ι := ι)
    · rw [simplexEntropy_apply_of_mem (ι := ι) hy]
      simpa using (bot_lt_coe (entropyCore (ι := ι) y))
    · rw [simplexEntropy_apply_of_not_mem (ι := ι) hy]
      simp

/-- The nonnegative orthant in `ι → ℝ`. -/
def nonnegativeOrthant : Set (ι → ℝ) :=
  {y | ∀ i, 0 ≤ y i}

/-- The total mass `∑ i y_i`. -/
noncomputable def totalMass (y : ι → ℝ) : ℝ :=
  ∑ i, y i

theorem simplexSet_eq_nonnegativeOrthant_inter_mass :
    simplexSet (ι := ι) =
      {y : ι → ℝ | y ∈ nonnegativeOrthant (ι := ι) ∧ totalMass (ι := ι) y = 1} := by
  ext y
  simp [simplexSet, nonnegativeOrthant, totalMass]

theorem isClosed_nonnegativeOrthant : IsClosed (nonnegativeOrthant (ι := ι)) := by
  simpa [nonnegativeOrthant, Set.setOf_forall] using
    isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))

theorem convex_nonnegativeOrthant : Convex ℝ (nonnegativeOrthant (ι := ι)) := by
  intro x hx y hy a b ha hb hab i
  simpa [nonnegativeOrthant, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
    add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem continuous_totalMass : Continuous (totalMass (ι := ι)) := by
  unfold totalMass
  exact continuous_finset_sum _ fun i _ => continuous_apply i

theorem totalMass_nonneg {y : ι → ℝ} (hy : y ∈ nonnegativeOrthant (ι := ι)) :
    0 ≤ totalMass (ι := ι) y := by
  unfold totalMass
  exact Finset.sum_nonneg fun i _ => hy i

theorem totalMass_smul (c : ℝ) (y : ι → ℝ) :
    totalMass (ι := ι) (c • y) = c * totalMass (ι := ι) y := by
  simp [totalMass, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem eq_zero_of_mem_nonnegativeOrthant_of_totalMass_eq_zero {y : ι → ℝ}
    (hy : y ∈ nonnegativeOrthant (ι := ι))
    (hzero : totalMass (ι := ι) y = 0) :
    y = 0 := by
  classical
  funext i
  apply le_antisymm
  · have hle : y i ≤ totalMass (ι := ι) y := by
      unfold totalMass
      simpa using
        (Finset.single_le_sum (fun j _ => hy j) (by simp : i ∈ Finset.univ))
    simpa [hzero] using hle
  · exact hy i

theorem inv_smul_mem_simplexSet {y : ι → ℝ}
    (hy : y ∈ nonnegativeOrthant (ι := ι))
    (hypos : 0 < totalMass (ι := ι) y) :
    (totalMass (ι := ι) y)⁻¹ • y ∈ simplexSet (ι := ι) := by
  constructor
  · intro i
    have hinv : 0 ≤ (totalMass (ι := ι) y)⁻¹ := by positivity
    simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hinv (hy i)
  · calc
      ∑ i, (((totalMass (ι := ι) y)⁻¹ • y) i)
          = (totalMass (ι := ι) y)⁻¹ * totalMass (ι := ι) y := by
              simp [totalMass, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      _ = 1 := by field_simp [hypos.ne']

/-- The real-valued homogeneous entropy core
`∑ i y_i log y_i - (∑ i y_i) log (∑ i y_i)`. -/
noncomputable def homogeneousEntropyCore (y : ι → ℝ) : ℝ :=
  entropyCore (ι := ι) y - totalMass (ι := ι) y * Real.log (totalMass (ι := ι) y)

/-- Exercise 3.51's homogeneous entropy, extended by `∞` outside the
nonnegative orthant. -/
noncomputable def homogeneousEntropy (y : ι → ℝ) : EReal :=
  indicatorVA (nonnegativeOrthant (ι := ι)) y + (homogeneousEntropyCore (ι := ι) y : ℝ)

theorem homogeneousEntropy_apply_of_mem {y : ι → ℝ}
    (hy : y ∈ nonnegativeOrthant (ι := ι)) :
    homogeneousEntropy (ι := ι) y = (homogeneousEntropyCore (ι := ι) y : EReal) := by
  rw [homogeneousEntropy, indicatorVA_apply_mem hy, zero_add]

theorem homogeneousEntropy_apply_of_not_mem {y : ι → ℝ}
    (hy : y ∉ nonnegativeOrthant (ι := ι)) :
    homogeneousEntropy (ι := ι) y = ⊤ := by
  rw [homogeneousEntropy, indicatorVA_apply_not_mem hy, EReal.top_add_coe]

theorem homogeneousEntropyCore_eq_entropyCore_of_mem_simplex {y : ι → ℝ}
    (hy : y ∈ simplexSet (ι := ι)) :
    homogeneousEntropyCore (ι := ι) y = entropyCore (ι := ι) y := by
  rcases hy with ⟨_, hy_sum⟩
  simp [homogeneousEntropyCore, totalMass, hy_sum]

theorem homogeneousEntropy_eq_simplexEntropy_of_mem_simplex {y : ι → ℝ}
    (hy : y ∈ simplexSet (ι := ι)) :
    homogeneousEntropy (ι := ι) y = simplexEntropy (ι := ι) y := by
  rw [homogeneousEntropy_apply_of_mem (ι := ι) hy.1,
    simplexEntropy_apply_of_mem (ι := ι) hy,
    homogeneousEntropyCore_eq_entropyCore_of_mem_simplex (ι := ι) hy]

theorem continuous_homogeneousEntropyCore :
    Continuous (homogeneousEntropyCore (ι := ι)) := by
  unfold homogeneousEntropyCore
  exact continuous_entropyCore.sub
    (Real.Continuous.mul_log (continuous_totalMass (ι := ι)))

theorem lowerSemicontinuous_homogeneousEntropy :
    LowerSemicontinuous (homogeneousEntropy (ι := ι)) := by
  have hind : LowerSemicontinuous (indicatorVA (nonnegativeOrthant (ι := ι))) :=
    lowerSemicontinuous_indicatorVA (C := nonnegativeOrthant (ι := ι))
      isClosed_nonnegativeOrthant
  have hcore :
      Continuous (fun y : ι → ℝ => (homogeneousEntropyCore (ι := ι) y : EReal)) :=
    continuous_coe_real_ereal.comp continuous_homogeneousEntropyCore
  refine LowerSemicontinuous.add' hind hcore.lowerSemicontinuous ?_
  intro y
  exact EReal.continuousAt_add (.inr (by simp)) (.inr (by simp))

@[simp] theorem homogeneousEntropyCore_zero :
    homogeneousEntropyCore (ι := ι) (0 : ι → ℝ) = 0 := by
  simp [homogeneousEntropyCore, entropyCore, totalMass]

@[simp] theorem homogeneousEntropy_zero :
    homogeneousEntropy (ι := ι) (0 : ι → ℝ) = 0 := by
  rw [homogeneousEntropy_apply_of_mem (ι := ι) (y := 0)]
  · simp
  · intro i
    simp

theorem entropyCore_smul_of_mem_simplex {y : ι → ℝ} (hy : y ∈ simplexSet (ι := ι))
    {c : ℝ} (hc : 0 < c) :
    entropyCore (ι := ι) (c • y) =
      c * entropyCore (ι := ι) y + c * Real.log c := by
  rcases hy with ⟨_, hy_sum⟩
  calc
    entropyCore (ι := ι) (c • y)
        = ∑ i, (c * y i) * Real.log (c * y i) := by
            simp [entropyCore, Pi.smul_apply, smul_eq_mul]
    _ = ∑ i, (c * (y i * Real.log (y i)) + (c * Real.log c) * y i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hmul := Real.negMulLog_mul c (y i)
          unfold Real.negMulLog at hmul
          ring_nf at hmul ⊢
          linarith
    _ = ∑ i, c * (y i * Real.log (y i)) + ∑ i, (c * Real.log c) * y i := by
          rw [Finset.sum_add_distrib]
    _ = c * entropyCore (ι := ι) y + (c * Real.log c) * ∑ i, y i := by
          simp [entropyCore, Finset.mul_sum]
    _ = c * entropyCore (ι := ι) y + c * Real.log c := by
          simp [hy_sum]

theorem homogeneousEntropyCore_smul_of_mem_simplex {y : ι → ℝ}
    (hy : y ∈ simplexSet (ι := ι)) {c : ℝ} (hc : 0 < c) :
    homogeneousEntropyCore (ι := ι) (c • y) =
      c * entropyCore (ι := ι) y := by
  rcases hy with ⟨hy_nonneg, hy_sum⟩
  rw [homogeneousEntropyCore,
    entropyCore_smul_of_mem_simplex (ι := ι) ⟨hy_nonneg, hy_sum⟩ hc,
    totalMass_smul, totalMass, hy_sum]
  simp

theorem homogeneousEntropyCore_eq_totalMass_mul_entropyCore_normalized
    {y : ι → ℝ} (hy : y ∈ nonnegativeOrthant (ι := ι))
    (hypos : 0 < totalMass (ι := ι) y) :
    homogeneousEntropyCore (ι := ι) y =
      totalMass (ι := ι) y *
        entropyCore (ι := ι) ((totalMass (ι := ι) y)⁻¹ • y) := by
  let s : ℝ := totalMass (ι := ι) y
  have hs : 0 < s := hypos
  let z : ι → ℝ := s⁻¹ • y
  have hz : z ∈ simplexSet (ι := ι) := by
    simpa [s] using inv_smul_mem_simplexSet (ι := ι) hy hs
  have hy_eq : y = s • z := by
    ext i
    change y i = s * z i
    simp [z, s, Pi.smul_apply, smul_eq_mul, mul_assoc, hs.ne']
  calc
    homogeneousEntropyCore (ι := ι) y
        = homogeneousEntropyCore (ι := ι) (s • z) := by rw [hy_eq]
    _ = s * entropyCore (ι := ι) z :=
          homogeneousEntropyCore_smul_of_mem_simplex (ι := ι) hz hs
    _ = totalMass (ι := ι) y *
          entropyCore (ι := ι) ((totalMass (ι := ι) y)⁻¹ • y) := by
          simp [z, s]

theorem homogeneousEntropy_eq_totalMass_mul_entropyCore_normalized
    {y : ι → ℝ} (hy : y ∈ nonnegativeOrthant (ι := ι))
    (hypos : 0 < totalMass (ι := ι) y) :
    homogeneousEntropy (ι := ι) y =
      ((totalMass (ι := ι) y *
        entropyCore (ι := ι) ((totalMass (ι := ι) y)⁻¹ • y)) : EReal) := by
  rw [homogeneousEntropy_apply_of_mem (ι := ι) hy,
    homogeneousEntropyCore_eq_totalMass_mul_entropyCore_normalized (ι := ι) hy hypos,
    EReal.coe_mul]

theorem homogeneousEntropy_isProper [Nonempty ι] :
    IsProper (homogeneousEntropy (ι := ι)) := by
  constructor
  · rcases simplexSet_nonempty (ι := ι) with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [homogeneousEntropy_eq_simplexEntropy_of_mem_simplex (ι := ι) hy,
      simplexEntropy_apply_of_mem (ι := ι) hy]
    exact EReal.coe_lt_top (entropyCore (ι := ι) y)
  · intro y
    by_cases hy : y ∈ nonnegativeOrthant (ι := ι)
    · rw [homogeneousEntropy_apply_of_mem (ι := ι) hy]
      simpa using (bot_lt_coe (homogeneousEntropyCore (ι := ι) y))
    · rw [homogeneousEntropy_apply_of_not_mem (ι := ι) hy]
      simp

theorem mem_nonnegativeOrthant_of_mem_positiveHull_epigraph_simplexEntropy
    {y : ι → ℝ} {a : ℝ}
    (ha : (y, a) ∈ positiveHull (epigraph (simplexEntropy (ι := ι)))) :
    y ∈ nonnegativeOrthant (ι := ι) := by
  rcases ha with hzero | ⟨c, hc, p, hp, hpEq⟩
  · have hy0 : y = 0 := by
      simpa using congrArg Prod.fst hzero
    subst hy0
    intro i
    simp
  · rcases p with ⟨z, b⟩
    rw [epigraph_simplexEntropy] at hp
    rcases hp with ⟨hz, _⟩
    have hyEq : y = c • z := by
      simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.fst hpEq
    rw [hyEq]
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hc.le (hz.1 i)

theorem homogeneousEntropy_le_of_mem_positiveHull_epigraph_simplexEntropy
    {y : ι → ℝ} {a : ℝ}
    (ha : (y, a) ∈ positiveHull (epigraph (simplexEntropy (ι := ι)))) :
    homogeneousEntropy (ι := ι) y ≤ (a : EReal) := by
  rcases ha with hzero | ⟨c, hc, p, hp, hpEq⟩
  · have hy0 : y = 0 := by
      simpa using congrArg Prod.fst hzero
    have ha0 : a = 0 := by
      simpa using congrArg Prod.snd hzero
    subst hy0
    subst ha0
    simp
  · rcases p with ⟨z, b⟩
    rw [epigraph_simplexEntropy] at hp
    rcases hp with ⟨hz, hb⟩
    have hyEq : y = c • z := by
      simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.fst hpEq
    have haEq : a = c * b := by
      simpa [Prod.smul_mk, smul_eq_mul] using congrArg Prod.snd hpEq
    have hy : y ∈ nonnegativeOrthant (ι := ι) := by
      rw [hyEq]
      intro i
      simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hc.le (hz.1 i)
    have hreal : c * entropyCore (ι := ι) z ≤ a := by
      rw [haEq]
      exact mul_le_mul_of_nonneg_left hb hc.le
    have hEReal : ((c * entropyCore (ι := ι) z : ℝ) : EReal) ≤ (a : EReal) := by
      exact_mod_cast hreal
    calc
      homogeneousEntropy (ι := ι) y
          = (homogeneousEntropyCore (ι := ι) y : EReal) := by
              rw [homogeneousEntropy_apply_of_mem (ι := ι) hy]
      _ = ((c * entropyCore (ι := ι) z : ℝ) : EReal) := by
            rw [hyEq, homogeneousEntropyCore_smul_of_mem_simplex (ι := ι) hz hc]
      _ ≤ (a : EReal) := hEReal

theorem homogeneousEntropy_le_positiveHullFunction_simplexEntropy (y : ι → ℝ) :
    homogeneousEntropy (ι := ι) y ≤ positiveHullFunction (simplexEntropy (ι := ι)) y := by
  refine le_iInf ?_
  intro a
  exact homogeneousEntropy_le_of_mem_positiveHull_epigraph_simplexEntropy (ι := ι) a.property

theorem positiveHullFunction_simplexEntropy_le_homogeneousEntropy (y : ι → ℝ) :
    positiveHullFunction (simplexEntropy (ι := ι)) y ≤ homogeneousEntropy (ι := ι) y := by
  by_cases hy : y ∈ nonnegativeOrthant (ι := ι)
  · by_cases hy0 : totalMass (ι := ι) y = 0
    · have hyzero : y = 0 :=
        eq_zero_of_mem_nonnegativeOrthant_of_totalMass_eq_zero (ι := ι) hy hy0
      subst hyzero
      have hle :
          positiveHullFunction (simplexEntropy (ι := ι)) 0 ≤ (0 : EReal) := by
        simpa using
          (positiveHullFunction_le_of_mem_positiveHull_epigraph
            (f := simplexEntropy (ι := ι))
            (x := 0) (a := 0)
            (zero_mem_positiveHull (epigraph (simplexEntropy (ι := ι)))))
      simpa using hle
    · have hypos : 0 < totalMass (ι := ι) y := by
        exact lt_of_le_of_ne (totalMass_nonneg (ι := ι) hy) <| by
          intro h
          exact hy0 h.symm
      let s : ℝ := totalMass (ι := ι) y
      let z : ι → ℝ := s⁻¹ • y
      have hz : z ∈ simplexSet (ι := ι) := by
        simpa [s, z] using inv_smul_mem_simplexSet (ι := ι) hy hypos
      have hmem_epi : (z, entropyCore (ι := ι) z) ∈ epigraph (simplexEntropy (ι := ι)) := by
        rw [mem_epigraph_iff, simplexEntropy_apply_of_mem (ι := ι) hz]
      have hyEq : y = s • z := by
        ext i
        change y i = s * z i
        simp [z, s, Pi.smul_apply, smul_eq_mul, hypos.ne']
      have hmem_pos :
          (y, s * entropyCore (ι := ι) z) ∈ positiveHull (epigraph (simplexEntropy (ι := ι))) := by
        right
        refine ⟨s, hypos, (z, entropyCore (ι := ι) z), hmem_epi, ?_⟩
        change (y, s * entropyCore (ι := ι) z) = s • (z, entropyCore (ι := ι) z)
        exact Prod.ext hyEq (by simp [Prod.smul_mk, smul_eq_mul])
      calc
        positiveHullFunction (simplexEntropy (ι := ι)) y
            ≤ ((s * entropyCore (ι := ι) z : ℝ) : EReal) :=
              positiveHullFunction_le_of_mem_positiveHull_epigraph hmem_pos
        _ = homogeneousEntropy (ι := ι) y := by
              rw [homogeneousEntropy_eq_totalMass_mul_entropyCore_normalized (ι := ι) hy hypos]
              simp [s, z, EReal.coe_mul]
  · rw [homogeneousEntropy_apply_of_not_mem (ι := ι) hy]
    exact le_top

theorem homogeneousEntropy_eq_positiveHullFunction_simplexEntropy :
    homogeneousEntropy (ι := ι) = positiveHullFunction (simplexEntropy (ι := ι)) := by
  funext y
  exact le_antisymm
    (homogeneousEntropy_le_positiveHullFunction_simplexEntropy (ι := ι) y)
    (positiveHullFunction_simplexEntropy_le_homogeneousEntropy (ι := ι) y)

theorem positivelyHomogeneous_homogeneousEntropy :
    PositivelyHomogeneous (homogeneousEntropy (ι := ι)) := by
  simpa [homogeneousEntropy_eq_positiveHullFunction_simplexEntropy (ι := ι)] using
    positivelyHomogeneous_positiveHullFunction (f := simplexEntropy (ι := ι))

theorem convex_epigraph_homogeneousEntropy :
    Convex ℝ (epigraph (homogeneousEntropy (ι := ι))) := by
  simpa [homogeneousEntropy_eq_positiveHullFunction_simplexEntropy (ι := ι)] using
    convex_epigraph_positiveHullFunction (f := simplexEntropy (ι := ι))
      (convex_epigraph_simplexEntropy (ι := ι))

theorem homogeneousEntropy_ne_bot (y : ι → ℝ) :
    homogeneousEntropy (ι := ι) y ≠ ⊥ := by
  by_cases hy : y ∈ nonnegativeOrthant (ι := ι)
  · rw [homogeneousEntropy_apply_of_mem (ι := ι) hy]
    exact EReal.coe_ne_bot _
  · rw [homogeneousEntropy_apply_of_not_mem (ι := ι) hy]
    simp

/-- **Exercise 3.51**: the homogeneous entropy is sublinear. -/
theorem sublinear_homogeneousEntropy :
    Sublinear (homogeneousEntropy (ι := ι)) := by
  exact sublinear_of_positivelyHomogeneous_of_convex_epigraph_of_ne_bot
    (positivelyHomogeneous_homogeneousEntropy (ι := ι))
    (convex_epigraph_homogeneousEntropy (ι := ι))
    (homogeneousEntropy_ne_bot (ι := ι))

end Entropy

end RW
