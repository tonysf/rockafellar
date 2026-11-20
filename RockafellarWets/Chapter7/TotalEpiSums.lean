/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 7: Convergence of infimal convolutions
-/

import RockafellarWets.Chapter7.FiniteEpiSums
import RockafellarWets.Chapter7.TotalEpiProjection

open Filter Function Set Topology
open scoped Pointwise

namespace RW

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Proposition 7.56** in the geometric noncancellation form: no
nonzero selection of epigraph horizon vectors can sum to zero. -/
theorem epiConverges_finiteEpiSum_of_horizon_noCancel
    {f : ι → ℕ → E → EReal} {g : ι → E → EReal} (hc : ∀ i, TotalEpiConverges (f i) (g i))
    (hker : ∀ z : ι → E × ℝ, (∀ i, z i ∈ horizonCone (epigraph (g i))) →
      (∑ i, z i) = 0 → z = 0) :
    EpiConverges (fun n ↦ finiteEpiSum (fun i ↦ f i n)) (finiteEpiSum g) := by
  have hs := pkConverges_finiteSetSum_of_total_of_horizon_noCancel hc hker
  unfold EpiConverges
  rw [epigraph_finiteEpiSum_of_isClosed _ hs.isClosed, ← pkConverges_closure_iff]
  simp only [closure_epigraph_finiteEpiSum, pkConverges_closure_iff]
  exact hs

/-- **Proposition 7.56(b)** in epigraph form. -/
theorem totalEpiConverges_finiteEpiSum_of_horizon_noCancel
    {f : ι → ℕ → E → EReal} {g : ι → E → EReal} (hc : ∀ i, TotalEpiConverges (f i) (g i))
    (hprod : horizonCone (dependentSetProduct (fun i ↦ epigraph (g i))) =
      dependentSetProduct (fun i ↦ horizonCone (epigraph (g i))))
    (hker : ∀ z : ι → E × ℝ, (∀ i, z i ∈ horizonCone (epigraph (g i))) →
      (∑ i, z i) = 0 → z = 0) :
    TotalEpiConverges (fun n ↦ finiteEpiSum (fun i ↦ f i n)) (finiteEpiSum g) := by
  have hs := totalConverges_finiteSetSum hc hprod hker
  unfold TotalEpiConverges
  rw [epigraph_finiteEpiSum_of_isClosed _ hs.1]
  exact hs.of_termwise_closure_eq fun n ↦ closure_epigraph_finiteEpiSum _

omit [Nonempty ι] [FiniteDimensional ℝ E] in
/-- Scalar horizontal noncancellation together with exclusion of downward
vertical directions gives full epigraph noncancellation. -/
theorem epigraph_horizon_noCancel_of_finiteInfAddition
    {g : ι → E → EReal} (hzero : ∀ i, 0 ≤ horizonFunction (g i) 0)
    (hpos : ∀ x : ι → E, (∑ i, x i) = 0 →
      finiteInfAddition (fun i ↦ horizonFunction (g i) (x i)) ≤ 0 → x = 0) :
    ∀ z : ι → E × ℝ, (∀ i, z i ∈ horizonCone (epigraph (g i))) → (∑ i, z i) = 0 → z = 0 := by
  intro z hz he
  have hx : ∑ i, (z i).1 = 0 := by simpa only [Prod.fst_sum] using congrArg Prod.fst he
  have ha : ∑ i, (z i).2 = 0 := by simpa only [Prod.snd_sum] using congrArg Prod.snd he
  have hle (i : ι) : horizonFunction (g i) (z i).1 ≤ ((z i).2 : EReal) :=
    horizonFunction_le_of_mem_horizonCone_epigraph (hz i)
  have hx0 := hpos _ hx (by simpa only [ha, EReal.coe_zero] using finiteInfAddition_le_sum hle)
  have ha0 := (Fintype.sum_eq_zero_iff_of_nonneg (fun i ↦ show 0 ≤ (z i).2 from
    EReal.coe_nonneg.mp ((hzero i).trans (by simpa only [show (z i).1 = 0 from congrFun hx0 i] using hle i)))).mp ha
  funext i
  exact Prod.ext (congrFun hx0 i) (congrFun ha0 i)

/-- Scalar form of 7.56(b). The horizontal condition only needs to be
tested for tuples summing to zero. Nonnegative origin heights also exclude
vertical cancellation, which the horizontal condition alone cannot detect. -/
theorem totalEpiConverges_finiteEpiSum {f : ι → ℕ → E → EReal} {g : ι → E → EReal}
    (hc : ∀ i, TotalEpiConverges (f i) (g i))
    (hprod : horizonCone (dependentSetProduct (fun i ↦ epigraph (g i))) =
      dependentSetProduct (fun i ↦ horizonCone (epigraph (g i))))
    (hzero : ∀ i, 0 ≤ horizonFunction (g i) 0)
    (hpos : ∀ x : ι → E, (∑ i, x i) = 0 →
      finiteInfAddition (fun i ↦ horizonFunction (g i) (x i)) ≤ 0 → x = 0) :
    TotalEpiConverges (fun n ↦ finiteEpiSum (fun i ↦ f i n)) (finiteEpiSum g) :=
  totalEpiConverges_finiteEpiSum_of_horizon_noCancel hc hprod
    (epigraph_horizon_noCancel_of_finiteInfAddition hzero hpos)

omit [Nonempty ι] in
/-- The product-horizon identity in 7.56(b) holds for convex functions
with nonempty epigraphs, in particular for proper convex functions. -/
theorem horizonCone_product_epigraphs_of_convex {g : ι → E → EReal}
    (hconv : ∀ i, Convex ℝ (epigraph (g i))) (hne : ∀ i, (epigraph (g i)).Nonempty) :
    horizonCone (dependentSetProduct (fun i ↦ epigraph (g i))) =
      dependentSetProduct (fun i ↦ horizonCone (epigraph (g i))) :=
  horizonCone_pi_eq_pi_horizonCone_of_convex_nonempty _ hconv hne

/-- The scalar condition alone suffices for proper convex limits: their
horizon functions vanish at the origin and their product horizons factor. -/
theorem totalEpiConverges_finiteEpiSum_of_convex {f : ι → ℕ → E → EReal} {g : ι → E → EReal}
    (hc : ∀ i, TotalEpiConverges (f i) (g i)) (hg : ∀ i, IsProper (g i))
    (hconv : ∀ i, Convex ℝ (epigraph (g i)))
    (hpos : ∀ x : ι → E, (∑ i, x i) = 0 →
      finiteInfAddition (fun i ↦ horizonFunction (g i) (x i)) ≤ 0 → x = 0) :
    TotalEpiConverges (fun n ↦ finiteEpiSum (fun i ↦ f i n)) (finiteEpiSum g) :=
  totalEpiConverges_finiteEpiSum hc
    (horizonCone_product_epigraphs_of_convex hconv (fun i ↦ epigraph_nonempty_of_isProper (hg i)))
    (fun i ↦ (horizonFunction_zero_eq_zero_of_convex (hconv i)
      (hc i).epiConverges.lowerSemicontinuous (hg i)).ge) hpos

/-- **Proposition 7.56(a)** for binary infimal convolution, including the
vertical noncancellation condition at the origin. -/
theorem epiConverges_infAddEpiSum {f h : ℕ → E → EReal} {g k : E → EReal}
    (hf : TotalEpiConverges f g) (hh : TotalEpiConverges h k)
    (hg0 : 0 ≤ horizonFunction g 0) (hk0 : 0 ≤ horizonFunction k 0)
    (hpos : ∀ x : E, x ≠ 0 → 0 < infAddition (horizonFunction g x) (horizonFunction k (-x))) :
    EpiConverges (fun n ↦ infAddEpiSum (f n) (h n)) (infAddEpiSum g k) := by
  have hcomp (i : Fin 2) : TotalEpiConverges ((![f, h] : Fin 2 → ℕ → E → EReal) i)
      ((![g, k] : Fin 2 → E → EReal) i) := by
    fin_cases i
    · exact hf
    · exact hh
  have hzero (i : Fin 2) : 0 ≤ horizonFunction ((![g, k] : Fin 2 → E → EReal) i) 0 := by
    fin_cases i
    · exact hg0
    · exact hk0
  have hs := epiConverges_finiteEpiSum_of_horizon_noCancel hcomp
    (epigraph_horizon_noCancel_of_finiteInfAddition hzero (by
      intro x hx hval
      have hneg : x 1 = -(x 0) := neg_eq_of_add_eq_zero_right (by simpa [Fin.sum_univ_two] using hx) |>.symm
      have he : (fun i ↦ horizonFunction ((![g, k] : Fin 2 → E → EReal) i) (x i)) =
          ![horizonFunction g (x 0), horizonFunction k (x 1)] := by funext i; fin_cases i <;> rfl
      rw [he, finiteInfAddition_fin_two, hneg] at hval
      have hx0 : x 0 = 0 := by by_contra hn; exact (hpos _ hn).not_ge hval
      funext i
      fin_cases i
      · exact hx0
      · simpa [hx0] using hneg))
  have he (n : ℕ) : (fun i ↦ (![f, h] : Fin 2 → ℕ → E → EReal) i n) = ![f n, h n] := by
    funext i
    fin_cases i <;> rfl
  simpa only [he, finiteEpiSum_fin_two] using hs

end RW
