/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Euclidean cones representing epigraphs in conjugacy
-/
import RockafellarWets.Chapter11.HorizonConjugacy
import RockafellarWets.Chapter11.ConjugateInvariance
import RockafellarWets.Chapter3.PositiveHulls
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Set Filter Topology
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev ConjugacySpace (E : Type*) [NormedAddCommGroup E] := WithLp 2 (E × WithLp 2 (ℝ × ℝ))

def conjugacyPoint (x : E) (a b : ℝ) : ConjugacySpace E := WithLp.toLp 2 (x,WithLp.toLp 2 (a,b))

@[simp] theorem conjugacyPoint_fst (x : E) (a b : ℝ) : (conjugacyPoint x a b).fst = x := rfl
@[simp] theorem conjugacyPoint_snd_fst (x : E) (a b : ℝ) : (conjugacyPoint x a b).snd.fst = a := rfl
@[simp] theorem conjugacyPoint_snd_snd (x : E) (a b : ℝ) : (conjugacyPoint x a b).snd.snd = b := rfl
@[simp] theorem conjugacyPoint_eta (p : ConjugacySpace E) : conjugacyPoint p.fst p.snd.fst p.snd.snd = p := rfl

@[simp] theorem inner_conjugacyPoint (p : ConjugacySpace E) (x : E) (a b : ℝ) :
    ⟪p,conjugacyPoint x a b⟫_ℝ = ⟪p.fst,x⟫_ℝ+p.snd.fst*a+p.snd.snd*b := by
  simp [conjugacyPoint,WithLp.prod_inner_apply,real_inner_comm,add_assoc,mul_comm]

/-- The cone `K_f` in Exercise 11.7, with coordinates `(x,α,-λ)`. -/
def conjugacyPrimalCone (f : E → EReal) : Set (ConjugacySpace E) :=
  {p | ((p.fst,p.snd.fst),p.snd.snd) ∈ raySpaceCone (epigraph f) (horizonCone (epigraph f))}

/-- The cone `K_g`, with coordinates `(v,-μ,β)`. -/
def conjugacyDualCone (g : E → EReal) : Set (ConjugacySpace E) :=
  {p | ((p.fst,p.snd.snd),p.snd.fst) ∈ raySpaceCone (epigraph g) (horizonCone (epigraph g))}

@[simp] theorem mem_conjugacyPrimalCone_neg_one (f : E → EReal) (x : E) (a : ℝ) :
    conjugacyPoint x a (-1) ∈ conjugacyPrimalCone f ↔ f x ≤ (a:EReal) :=
  mem_raySpaceCone_neg_one_iff

@[simp] theorem mem_conjugacyDualCone_neg_one (f : E → EReal) (x : E) (a : ℝ) :
    conjugacyPoint x (-1) a ∈ conjugacyDualCone f ↔ f x ≤ (a:EReal) :=
  mem_raySpaceCone_neg_one_iff

variable [FiniteDimensional ℝ E]

/-- Testing against the unit-height slice suffices, including the horizon
part of the cone. -/
theorem mem_polar_conjugacyPrimalCone_iff (f : E → EReal) (q : ConjugacySpace E) :
    q ∈ polarCone (conjugacyPrimalCone f) ↔
      ∀ (x : E) (a : ℝ), f x ≤ (a:EReal) → ⟪q.fst,x⟫_ℝ+q.snd.fst*a-q.snd.snd ≤ 0 := by
  constructor
  · intro h x a ha
    have hh := h (conjugacyPoint x a (-1)) ((mem_conjugacyPrimalCone_neg_one f x a).mpr ha)
    simpa only [inner_conjugacyPoint,mul_neg_one,← sub_eq_add_neg] using hh
  · intro h p hp
    let D : Set ((E × ℝ) × ℝ) :=
      {r | ⟪q.fst,r.1.1⟫_ℝ+q.snd.fst*r.1.2+q.snd.snd*r.2 ≤ 0}
    have hclosed : IsClosed D := isClosed_le (by fun_prop) continuous_const
    have hbase : raySpaceCone (epigraph f) ({0} : Set (E × ℝ)) ⊆ D := by
      rintro r (⟨u,hu,t,ht,rfl⟩ | ⟨hu,hr⟩)
      · have hh := mul_nonpos_of_nonneg_of_nonpos ht.le (h u.1 u.2 hu)
        change ⟪q.fst,t • u.1⟫_ℝ+q.snd.fst*(t*u.2)+q.snd.snd*(-t) ≤ 0
        rw [real_inner_smul_right]
        nlinarith
      · have hu' : r.1 = 0 := hu
        have hr' : r.2 = 0 := hr
        simp [D,hu',hr']
    have hr : ((p.fst,p.snd.fst),p.snd.snd) ∈ closure (raySpaceCone (epigraph f) ({0} : Set (E × ℝ))) := by
      rcases hp with hp | hp
      · exact subset_closure (Or.inl hp)
      · have hh := mem_closure_raySpaceCone_of_mem_horizonCone
          (C := epigraph f) (K := ({0} : Set (E × ℝ)))
          (by refine ⟨by simp,?_⟩; intro x hx t ht; simp_all) hp.1
        have hp0 : p.snd.snd = 0 := hp.2
        simpa only [hp0] using hh
    have hh := closure_minimal hbase hclosed hr
    change ⟪q.fst,p.fst⟫_ℝ+q.snd.fst*p.snd.fst+q.snd.snd*p.snd.snd ≤ 0 at hh
    conv_lhs => rw [← conjugacyPoint_eta p,inner_conjugacyPoint]
    exact hh

/-- The conjugate is recovered from the `-1` slice of the polar cone. -/
theorem mem_polar_conjugacyPrimalCone_dual_slice (f : E → EReal) (v : E) (b : ℝ) :
    conjugacyPoint v (-1) b ∈ polarCone (conjugacyPrimalCone f) ↔ fenchelConjugate f v ≤ (b:EReal) := by
  rw [mem_polar_conjugacyPrimalCone_iff,fenchelConjugate_le_coe_iff_epigraph]
  constructor
  · intro h p hp
    have hh := h p.1 p.2 hp
    change ⟪v,p.1⟫_ℝ-p.2 ≤ b
    simpa using hh
  · intro h x a ha
    have hh := h (show (x,a) ∈ epigraph f from ha)
    change ⟪v,x⟫_ℝ+(-1)*a-b ≤ 0
    change ⟪v,x⟫_ℝ-a ≤ b at hh
    linarith

end
end RW
