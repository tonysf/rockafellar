/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3D: Horizon Functions Under Pointwise Max/Min

This file formalizes Proposition 3.30 from Rockafellar-Wets:
- horizon functions under pointwise suprema
- horizon functions under finite pointwise infima
-/

import RockafellarWets.Chapter3.HorizonFunctions

open Set EReal Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The epigraph of a pointwise supremum is the intersection of the epigraphs. -/
theorem epigraph_iSup {ι : Type*} (f : ι → E → EReal) :
    epigraph (fun x => ⨆ i, f i x) = ⋂ i, epigraph (f i) := by
  ext p
  rcases p with ⟨x, a⟩
  simp [mem_epigraph_iff, iSup_le_iff]

/-- The epigraph of a binary pointwise supremum is the intersection of the two
epigraphs. -/
theorem epigraph_sup {f g : E → EReal} :
    epigraph (fun x => f x ⊔ g x) = epigraph f ∩ epigraph g := by
  ext p
  rcases p with ⟨x, a⟩
  simp [mem_epigraph_iff, sup_le_iff]

/-- For a finite nonempty family, the epigraph of the pointwise infimum is the
union of the epigraphs. -/
theorem epigraph_iInf_of_finite {ι : Type*} [Finite ι] [Nonempty ι]
    (f : ι → E → EReal) :
    epigraph (fun x => ⨅ i, f i x) = ⋃ i, epigraph (f i) := by
  ext p
  rcases p with ⟨x, a⟩
  rw [mem_epigraph_iff]
  simp only [mem_iUnion, mem_epigraph_iff]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finite.exists_min (fun i => f i x)
    refine ⟨i, ?_⟩
    have hEq : (⨅ j, f j x) = f i x := le_antisymm (iInf_le _ i) (le_iInf hi)
    simpa [hEq] using h
  · rintro ⟨i, hi⟩
    exact (iInf_le (fun j => f j x) i).trans hi

/-- The epigraph of a binary pointwise infimum is the union of the two
epigraphs. -/
theorem epigraph_inf {f g : E → EReal} :
    epigraph (fun x => f x ⊓ g x) = epigraph f ∪ epigraph g := by
  ext p
  rcases p with ⟨x, a⟩
  simp [mem_epigraph_iff]

/-- Equality of real epigraphs determines an `EReal`-valued function. -/
theorem eq_of_epigraph_eq {f g : E → EReal} (hfg : epigraph f = epigraph g) :
    f = g := by
  funext x
  apply le_antisymm
  · by_contra h
    have hlt : g x < f x := lt_of_not_ge h
    obtain ⟨a, hga, haf⟩ := EReal.exists_between_coe_real hlt
    have hxg : (x, a) ∈ epigraph g := by
      rw [mem_epigraph_iff]
      exact hga.le
    have hxf : (x, a) ∈ epigraph f := by simpa [hfg] using hxg
    rw [mem_epigraph_iff] at hxf
    exact not_le_of_gt haf hxf
  · by_contra h
    have hlt : f x < g x := lt_of_not_ge h
    obtain ⟨a, hfa, hag⟩ := EReal.exists_between_coe_real hlt
    have hxf : (x, a) ∈ epigraph f := by
      rw [mem_epigraph_iff]
      exact hfa.le
    have hxg : (x, a) ∈ epigraph g := by simpa [hfg] using hxf
    rw [mem_epigraph_iff] at hxg
    exact not_le_of_gt hag hxg

/-- Enlarging the epigraph can only decrease the horizon function. -/
theorem horizonFunction_mono_of_epigraph_mono {f g : E → EReal} {w : E}
    (hfg : epigraph f ⊆ epigraph g) :
    horizonFunction g w ≤ horizonFunction f w := by
  refine le_iInf ?_
  intro a
  exact horizonFunction_le_of_mem_horizonCone_epigraph <| horizonCone_mono hfg a.property

/-- **Proposition 3.30** (first inequality): the horizon function of a pointwise
supremum dominates the pointwise supremum of the horizon functions. -/
theorem iSup_horizonFunction_le_horizonFunction_iSup {ι : Type*}
    (f : ι → E → EReal) (w : E) :
    (⨆ i, horizonFunction (f i) w) ≤ horizonFunction (fun x => ⨆ i, f i x) w := by
  refine iSup_le ?_
  intro i
  exact horizonFunction_mono_of_epigraph_mono <| by
    rw [epigraph_iSup]
    exact Set.iInter_subset _ i

/-- The horizon function of a binary pointwise supremum dominates the pointwise
supremum of the two horizon functions. -/
theorem sup_horizonFunction_le_horizonFunction_sup
    (f g : E → EReal) (w : E) :
    horizonFunction f w ⊔ horizonFunction g w ≤
      horizonFunction (fun x => f x ⊔ g x) w := by
  have hsup :
      (⨆ b : Bool, horizonFunction (fun x => cond b (f x) (g x)) w) ≤
        horizonFunction (fun x => ⨆ b : Bool, cond b (f x) (g x)) w :=
    iSup_horizonFunction_le_horizonFunction_iSup
      (f := fun b x => cond b (f x) (g x)) w
  simpa [sup_eq_iSup] using hsup

/-- **Proposition 3.30** (second inequality): the horizon function of a pointwise
infimum is bounded above by the pointwise infimum of the horizon functions. -/
theorem horizonFunction_iInf_le_iInf {ι : Type*}
    (f : ι → E → EReal) (w : E) :
    horizonFunction (fun x => ⨅ i, f i x) w ≤ ⨅ i, horizonFunction (f i) w := by
  refine le_iInf ?_
  intro i
  exact horizonFunction_mono_of_epigraph_mono <| by
    intro p hp
    rcases p with ⟨x, a⟩
    rw [mem_epigraph_iff] at hp ⊢
    exact (iInf_le (fun j => f j x) i).trans hp

/-- The horizon function of a binary pointwise infimum is bounded above by the
pointwise infimum of the two horizon functions. -/
theorem horizonFunction_inf_le_inf_horizonFunction
    (f g : E → EReal) (w : E) :
    horizonFunction (fun x => f x ⊓ g x) w ≤
      horizonFunction f w ⊓ horizonFunction g w := by
  have hinf :
      horizonFunction (fun x => ⨅ b : Bool, cond b (f x) (g x)) w ≤
        ⨅ b : Bool, horizonFunction (fun x => cond b (f x) (g x)) w :=
    horizonFunction_iInf_le_iInf (f := fun b x => cond b (f x) (g x)) w
  simpa [inf_eq_iInf] using hinf

/-- **Proposition 3.30** (equality case for suprema): if the pointwise supremum
has a nonempty epigraph and the functions are proper, lsc, and convex, then the
horizon function commutes with the supremum. -/
theorem horizonFunction_iSup_eq_iSup {ι : Type*} {f : ι → E → EReal}
    (hconv : ∀ i, Convex ℝ (epigraph (f i))) (hlsc : ∀ i, LowerSemicontinuous (f i))
    (hproper : ∀ i, IsProper (f i))
    (hsup : (epigraph (fun x => ⨆ i, f i x)).Nonempty) :
    horizonFunction (fun x => ⨆ i, f i x) = fun w => ⨆ i, horizonFunction (f i) w := by
  apply eq_of_epigraph_eq
  calc
    epigraph (horizonFunction (fun x => ⨆ i, f i x))
        = horizonCone (epigraph (fun x => ⨆ i, f i x)) := by
          exact epigraph_horizonFunction_eq_horizonCone_epigraph hsup
    _ = horizonCone (⋂ i, epigraph (f i)) := by
          rw [epigraph_iSup]
    _ = ⋂ i, horizonCone (epigraph (f i)) := by
          refine horizonCone_iInter_eq_iInter_horizonCone hconv ?_ ?_
          · intro i
            exact isClosed_epigraph_of_lsc_ereal (f i) (hlsc i)
          · simpa [epigraph_iSup] using hsup
    _ = ⋂ i, epigraph (horizonFunction (f i)) := by
          ext p
          simp [epigraph_horizonFunction_eq_horizonCone_epigraph
            (epigraph_nonempty_of_isProper (hproper _))]
    _ = epigraph (fun w => ⨆ i, horizonFunction (f i) w) := by
          rw [epigraph_iSup]

/-- If the pointwise supremum of two functions has nonempty epigraph and each
function is proper, lsc, and convex, then the horizon function commutes with
the binary pointwise supremum. -/
theorem horizonFunction_sup_eq_sup {f g : E → EReal}
    (hf_conv : Convex ℝ (epigraph f)) (hg_conv : Convex ℝ (epigraph g))
    (hf_lsc : LowerSemicontinuous f) (hg_lsc : LowerSemicontinuous g)
    (hf_proper : IsProper f) (hg_proper : IsProper g)
    (hsup : (epigraph (fun x => f x ⊔ g x)).Nonempty) :
    horizonFunction (fun x => f x ⊔ g x) =
      fun w => horizonFunction f w ⊔ horizonFunction g w := by
  have hsup' :
      horizonFunction (fun x => ⨆ b : Bool, cond b (f x) (g x)) =
        fun w => ⨆ b : Bool, horizonFunction (fun x => cond b (f x) (g x)) w :=
    horizonFunction_iSup_eq_iSup
      (f := fun b x => cond b (f x) (g x))
      (by
        intro b
        cases b
        · simpa using hg_conv
        · simpa using hf_conv)
      (by
        intro b
        cases b
        · simpa using hg_lsc
        · simpa using hf_lsc)
      (by
        intro b
        cases b
        · simpa using hg_proper
        · simpa using hf_proper)
      (by simpa [sup_eq_iSup] using hsup)
  funext w
  calc
    horizonFunction (fun x => f x ⊔ g x) w
        = horizonFunction (fun x => ⨆ b : Bool, cond b (f x) (g x)) w := by
            simp [sup_eq_iSup]
    _ = ⨆ b : Bool, horizonFunction (fun x => cond b (f x) (g x)) w := congrFun hsup' w
    _ = ⨆ b : Bool, cond b (horizonFunction f w) (horizonFunction g w) := by
          congr with b
          cases b <;> rfl
    _ = horizonFunction f w ⊔ horizonFunction g w := by
          simp [sup_eq_iSup]

/-- **Proposition 3.30** (equality case for finite infima): for a finite nonempty
family, the horizon function commutes with the pointwise infimum. -/
theorem horizonFunction_iInf_eq_iInf_of_finite {ι : Type*} [Finite ι] [Nonempty ι]
    (f : ι → E → EReal) :
    horizonFunction (fun x => ⨅ i, f i x) = fun w => ⨅ i, horizonFunction (f i) w := by
  funext w
  apply le_antisymm
  · exact horizonFunction_iInf_le_iInf f w
  · refine le_iInf ?_
    intro a
    have ha :
        (w, (a : ℝ)) ∈ ⋃ i, horizonCone (epigraph (f i)) := by
      have hmem : (w, (a : ℝ)) ∈ horizonCone (epigraph (fun x => ⨅ i, f i x)) := a.property
      simpa [epigraph_iInf_of_finite, horizonCone_iUnion_eq_iUnion_horizonCone] using hmem
    rcases Set.mem_iUnion.1 ha with ⟨i, hi⟩
    exact (iInf_le (fun j => horizonFunction (f j) w) i).trans <|
      horizonFunction_le_of_mem_horizonCone_epigraph hi

/-- For a binary pointwise infimum, the horizon function commutes with the
infimum. -/
theorem horizonFunction_inf_eq_inf {f g : E → EReal} :
    horizonFunction (fun x => f x ⊓ g x) =
      fun w => horizonFunction f w ⊓ horizonFunction g w := by
  have hinf :
      horizonFunction (fun x => ⨅ b : Bool, cond b (f x) (g x)) =
        fun w => ⨅ b : Bool, horizonFunction (fun x => cond b (f x) (g x)) w :=
    horizonFunction_iInf_eq_iInf_of_finite (f := fun b x => cond b (f x) (g x))
  funext w
  calc
    horizonFunction (fun x => f x ⊓ g x) w
        = horizonFunction (fun x => ⨅ b : Bool, cond b (f x) (g x)) w := by
            simp [inf_eq_iInf]
    _ = ⨅ b : Bool, horizonFunction (fun x => cond b (f x) (g x)) w := congrFun hinf w
    _ = ⨅ b : Bool, cond b (horizonFunction f w) (horizonFunction g w) := by
          congr with b
          cases b <;> rfl
    _ = horizonFunction f w ⊓ horizonFunction g w := by
          simp [inf_eq_iInf]

end RW
