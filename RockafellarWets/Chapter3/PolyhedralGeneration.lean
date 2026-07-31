/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exercise 3.54: finite generation of polyhedral functions

This file turns the finite-generator description of a polyhedral epigraph into
the optimization formula of Exercise 3.54.  The ordinary generators are
convexly combined, the direction generators are conically combined, and the
value of the function is the infimum of the resulting height coordinate.
-/

import RockafellarWets.Chapter3.PolyhedralFunctions.Core
import RockafellarWets.Chapter3.PositiveHulls

open Set EReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cost of ordinary coefficients `w` and direction coefficients `c` is
the height coordinate of their combined epigraph generators. -/
noncomputable def polyhedralGeneratorCost
    (s : Finset (E × ℝ)) (w : (E × ℝ) → ℝ) (c : (E × ℝ) →₀ ℝ) : ℝ :=
  (∑ p ∈ s, w p * p.2) + c.sum fun p r => r * p.2

/-- Feasibility in the finite optimization problem of Exercise 3.54:
ordinary coefficients are nonnegative and sum to one, direction coefficients
are nonnegative and supported on the finite direction set, and their
first-coordinate combination is `x`. -/
def PolyhedralGeneratorFeasible
    (s t : Finset (E × ℝ)) (x : E)
    (w : (E × ℝ) → ℝ) (c : (E × ℝ) →₀ ℝ) : Prop :=
  (∀ p ∈ s, 0 ≤ w p) ∧
    ∑ p ∈ s, w p = 1 ∧
    ↑c.support ⊆ (↑t : Set (E × ℝ)) ∧
    (∀ p, 0 ≤ c p) ∧
    (∑ p ∈ s, w p • p.1) + c.sum (fun p r => r • p.1) = x

/-- The exact finite epigraph-generator property appearing in Exercise 3.54.
It records both directions of the representation, so it also characterizes
polyhedral epigraphs. -/
def HasFiniteEpigraphGeneratorFormula (f : E → EReal) : Prop :=
  ∃ s t : Finset (E × ℝ),
    ∀ {x : E} {a : ℝ},
      (x, a) ∈ epigraph f ↔
        ∃ w : (E × ℝ) → ℝ, ∃ c : (E × ℝ) →₀ ℝ,
          PolyhedralGeneratorFeasible s t x w c ∧
            polyhedralGeneratorCost s w c = a

private theorem generator_pair_eq_iff
    {s t : Finset (E × ℝ)} {x : E} {a : ℝ}
    {w : (E × ℝ) → ℝ} {c : (E × ℝ) →₀ ℝ}
    (hw0 : ∀ p ∈ s, 0 ≤ w p) (hw1 : ∑ p ∈ s, w p = 1)
    (hcsub : ↑c.support ⊆ (↑t : Set (E × ℝ))) (hc0 : ∀ p, 0 ≤ c p) :
    (∑ p ∈ s, w p • p) + c.sum (fun p r => r • p) = (x, a) ↔
      PolyhedralGeneratorFeasible s t x w c ∧
        polyhedralGeneratorCost s w c = a := by
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    refine ⟨⟨hw0, hw1, hcsub, hc0, ?_⟩, ?_⟩
    · simpa [Finsupp.sum, Prod.fst_add, Prod.fst_sum, Prod.smul_fst] using hfst
    · simpa [polyhedralGeneratorCost, Finsupp.sum, Prod.snd_add, Prod.snd_sum,
        Prod.smul_snd, smul_eq_mul] using hsnd
  · rintro ⟨hfeas, hcost⟩
    apply Prod.ext
    · simpa [Finsupp.sum, Prod.fst_add, Prod.fst_sum, Prod.smul_fst] using
        hfeas.2.2.2.2
    · simpa [polyhedralGeneratorCost, Finsupp.sum, Prod.snd_add, Prod.snd_sum,
        Prod.smul_snd, smul_eq_mul] using hcost

/-- Exercise 3.54, representation equivalence: a function has a polyhedral
epigraph exactly when it has a finite ordinary/direction generator formula. -/
theorem hasPolyhedralEpigraph_iff_hasFiniteEpigraphGeneratorFormula
    {f : E → EReal} :
    HasPolyhedralEpigraph f ↔ HasFiniteEpigraphGeneratorFormula f := by
  constructor
  · intro hf
    rcases hf.exists_epigraph_generator_formula with ⟨s, t, hst⟩
    refine ⟨s, t, ?_⟩
    intro x a
    rw [hst]
    constructor
    · rintro ⟨w, hw0, hw1, c, hcsub, hc0, hpair⟩
      exact ⟨w, c, (generator_pair_eq_iff hw0 hw1 hcsub hc0).1 hpair⟩
    · rintro ⟨w, c, hfeas, hcost⟩
      exact ⟨w, hfeas.1, hfeas.2.1, c, hfeas.2.2.1, hfeas.2.2.2.1,
        (generator_pair_eq_iff hfeas.1 hfeas.2.1
          hfeas.2.2.1 hfeas.2.2.2.1).2 ⟨hfeas, hcost⟩⟩
  · rintro ⟨s, t, hst⟩
    refine ⟨s, t, ?_⟩
    ext p
    rcases p with ⟨x, a⟩
    rw [mem_extendedConvexHull_finset_iff, hst]
    constructor
    · rintro ⟨w, c, hfeas, hcost⟩
      exact ⟨w, hfeas.1, hfeas.2.1, c, hfeas.2.2.1, hfeas.2.2.2.1,
        (generator_pair_eq_iff hfeas.1 hfeas.2.1
          hfeas.2.2.1 hfeas.2.2.2.1).2 ⟨hfeas, hcost⟩⟩
    · rintro ⟨w, hw0, hw1, c, hcsub, hc0, hpair⟩
      exact ⟨w, c, (generator_pair_eq_iff hw0 hw1 hcsub hc0).1 hpair⟩

/-- A fixed finite epigraph-generator formula evaluates `f x` as the infimum
of its coefficient cost.  The `EReal` statement is exact also at `⊤` (empty
feasible set) and `⊥` (costs unbounded below). -/
theorem value_eq_iInf_generatorCost_of_epigraph_generator_formula
    {f : E → EReal} {s t : Finset (E × ℝ)}
    (hst : ∀ {x : E} {a : ℝ},
      (x, a) ∈ epigraph f ↔
        ∃ w : (E × ℝ) → ℝ, ∃ c : (E × ℝ) →₀ ℝ,
          PolyhedralGeneratorFeasible s t x w c ∧
            polyhedralGeneratorCost s w c = a)
    (x : E) :
    f x =
      ⨅ q : {
        q : ((E × ℝ) → ℝ) × ((E × ℝ) →₀ ℝ) //
          PolyhedralGeneratorFeasible s t x q.1 q.2
      },
        (polyhedralGeneratorCost s q.1.1 q.1.2 : EReal) := by
  apply le_antisymm
  · refine le_iInf ?_
    intro q
    have hmem : (x, polyhedralGeneratorCost s q.1.1 q.1.2) ∈ epigraph f :=
      (hst (x := x) (a := polyhedralGeneratorCost s q.1.1 q.1.2)).2
        ⟨q.1.1, q.1.2, q.property, rfl⟩
    simpa [mem_epigraph_iff] using hmem
  · rw [← iInf_coe_real_ge_eq (f x)]
    refine le_iInf ?_
    intro a
    have hmem : (x, (a : ℝ)) ∈ epigraph f := by
      simpa [mem_epigraph_iff] using a.property
    rcases (hst (x := x) (a := (a : ℝ))).1 hmem with ⟨w, c, hfeas, hcost⟩
    exact le_trans
      (iInf_le
        (fun q : {
          q : ((E × ℝ) → ℝ) × ((E × ℝ) →₀ ℝ) //
            PolyhedralGeneratorFeasible s t x q.1 q.2
        } => (polyhedralGeneratorCost s q.1.1 q.1.2 : EReal))
        ⟨(w, c), hfeas⟩)
      (by simp [hcost])

/-- A finite generator property supplies finsets realizing the optimization
formula simultaneously at every `x`. -/
theorem HasFiniteEpigraphGeneratorFormula.exists_value_eq_iInf_generatorCost
    {f : E → EReal} (hf : HasFiniteEpigraphGeneratorFormula f) :
    ∃ s t : Finset (E × ℝ), ∀ x : E,
      f x =
        ⨅ q : {
          q : ((E × ℝ) → ℝ) × ((E × ℝ) →₀ ℝ) //
            PolyhedralGeneratorFeasible s t x q.1 q.2
        },
          (polyhedralGeneratorCost s q.1.1 q.1.2 : EReal) := by
  rcases hf with ⟨s, t, hst⟩
  exact ⟨s, t, value_eq_iInf_generatorCost_of_epigraph_generator_formula hst⟩

/-- Exercise 3.54, optimization formula: every polyhedral-epigraph function is
the infimum of a finite linear-cost coefficient problem. -/
theorem HasPolyhedralEpigraph.exists_value_eq_iInf_generatorCost
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) :
    ∃ s t : Finset (E × ℝ), ∀ x : E,
      f x =
        ⨅ q : {
          q : ((E × ℝ) → ℝ) × ((E × ℝ) →₀ ℝ) //
            PolyhedralGeneratorFeasible s t x q.1 q.2
        },
          (polyhedralGeneratorCost s q.1.1 q.1.2 : EReal) :=
  HasFiniteEpigraphGeneratorFormula.exists_value_eq_iInf_generatorCost
    (hasPolyhedralEpigraph_iff_hasFiniteEpigraphGeneratorFormula.mp hf)

/-- Exercise 3.54, attainment: whenever `f x` is finite, the finite
coefficient problem has a feasible solution whose cost is exactly `f x`. -/
theorem HasFiniteEpigraphGeneratorFormula.exists_generator_minimizer_of_finite
    {f : E → EReal} (hf : HasFiniteEpigraphGeneratorFormula f)
    {x : E} (htop : f x ≠ ⊤) (hbot : f x ≠ ⊥) :
    ∃ s t : Finset (E × ℝ),
      ∃ w : (E × ℝ) → ℝ, ∃ c : (E × ℝ) →₀ ℝ,
        PolyhedralGeneratorFeasible s t x w c ∧
          (polyhedralGeneratorCost s w c : EReal) = f x := by
  rcases hf with ⟨s, t, hst⟩
  have hmem : (x, (f x).toReal) ∈ epigraph f := by
    rw [mem_epigraph_iff, EReal.coe_toReal htop hbot]
  rcases (hst (x := x) (a := (f x).toReal)).1 hmem with
    ⟨w, c, hfeas, hcost⟩
  refine ⟨s, t, w, c, hfeas, ?_⟩
  rw [hcost, EReal.coe_toReal htop hbot]

/-- Exercise 3.54, attainment specialized to a function with polyhedral
epigraph. -/
theorem HasPolyhedralEpigraph.exists_generator_minimizer_of_finite
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    {x : E} (htop : f x ≠ ⊤) (hbot : f x ≠ ⊥) :
    ∃ s t : Finset (E × ℝ),
      ∃ w : (E × ℝ) → ℝ, ∃ c : (E × ℝ) →₀ ℝ,
        PolyhedralGeneratorFeasible s t x w c ∧
          (polyhedralGeneratorCost s w c : EReal) = f x :=
  HasFiniteEpigraphGeneratorFormula.exists_generator_minimizer_of_finite
    (hasPolyhedralEpigraph_iff_hasFiniteEpigraphGeneratorFormula.mp hf) htop hbot

/-- Exercise 3.54 in one statement: one pair of finite ordinary and direction
generator sets yields the optimization formula at every point, and the same
coefficient problem attains every finite value. -/
theorem HasPolyhedralEpigraph.exists_generator_optimization_formula
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) :
    ∃ s t : Finset (E × ℝ),
      (∀ x : E,
        f x =
          ⨅ q : {
            q : ((E × ℝ) → ℝ) × ((E × ℝ) →₀ ℝ) //
              PolyhedralGeneratorFeasible s t x q.1 q.2
          },
            (polyhedralGeneratorCost s q.1.1 q.1.2 : EReal)) ∧
      ∀ x : E, f x ≠ ⊤ → f x ≠ ⊥ →
        ∃ w : (E × ℝ) → ℝ, ∃ c : (E × ℝ) →₀ ℝ,
          PolyhedralGeneratorFeasible s t x w c ∧
            (polyhedralGeneratorCost s w c : EReal) = f x := by
  rcases (hasPolyhedralEpigraph_iff_hasFiniteEpigraphGeneratorFormula.mp hf) with
    ⟨s, t, hst⟩
  refine ⟨s, t, value_eq_iInf_generatorCost_of_epigraph_generator_formula hst, ?_⟩
  intro x htop hbot
  have hmem : (x, (f x).toReal) ∈ epigraph f := by
    rw [mem_epigraph_iff, EReal.coe_toReal htop hbot]
  rcases (hst (x := x) (a := (f x).toReal)).1 hmem with
    ⟨w, c, hfeas, hcost⟩
  exact ⟨w, c, hfeas, by rw [hcost, EReal.coe_toReal htop hbot]⟩

end RW
