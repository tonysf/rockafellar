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

/-- The effective domain of a finite nonempty pointwise supremum is the
intersection of the effective domains. -/
theorem effectiveDomain_iSup_of_finite {ι : Type*} [Finite ι] [Nonempty ι]
    (f : ι → E → EReal) :
    effectiveDomain (fun x => ⨆ i, f i x) = ⋂ i, effectiveDomain (f i) := by
  ext x
  simp only [mem_effectiveDomain_iff, mem_iInter]
  constructor
  · intro h i
    exact lt_of_le_of_lt (le_iSup (fun j => f j x) i) h
  · intro h
    obtain ⟨i, hi⟩ := Finite.exists_max (fun i => f i x)
    have hle : f i x ≤ (⨆ j, f j x) := le_iSup (fun j : ι => f j x) i
    have hEq : (⨆ j, f j x) = f i x := le_antisymm (iSup_le hi) hle
    simpa [hEq] using h i

/-- If a finite nonempty family of proper functions has a common
effective-domain point, then its pointwise supremum is proper. -/
theorem isProper_iSup_of_finite_of_isProper_of_nonempty_iInter_effectiveDomain
    {ι : Type*} [Finite ι] [Nonempty ι] {f : ι → E → EReal}
    (hf : ∀ i, IsProper (f i))
    (hdom : (⋂ i, effectiveDomain (f i)).Nonempty) :
    IsProper (fun x => ⨆ i, f i x) := by
  refine ⟨?_, ?_⟩
  · change (effectiveDomain (fun x => ⨆ i, f i x)).Nonempty
    rw [effectiveDomain_iSup_of_finite]
    exact hdom
  · intro x
    let i₀ : ι := Classical.choice ‹Nonempty ι›
    exact lt_of_lt_of_le ((hf i₀).2 x) (le_iSup (fun i => f i x) i₀)

/-- Lower semicontinuity is preserved by arbitrary pointwise suprema. -/
theorem lowerSemicontinuous_iSup {ι : Type*} {f : ι → E → EReal}
    (hf : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (fun x => ⨆ i, f i x) := by
  rw [lsc_iff_epigraph_closed_ereal]
  rw [epigraph_iSup]
  exact isClosed_iInter fun i => isClosed_epigraph_of_lsc_ereal (f i) (hf i)

/-- Convexity of epigraphs is preserved by arbitrary pointwise suprema. -/
theorem convex_epigraph_iSup {ι : Type*} {f : ι → E → EReal}
    (hf : ∀ i, Convex ℝ (epigraph (f i))) :
    Convex ℝ (epigraph (fun x => ⨆ i, f i x)) := by
  rw [epigraph_iSup]
  exact convex_iInter fun i => hf i

/-- The epigraph of a binary pointwise supremum is the intersection of the two
epigraphs. -/
theorem epigraph_sup {f g : E → EReal} :
    epigraph (fun x => f x ⊔ g x) = epigraph f ∩ epigraph g := by
  ext p
  rcases p with ⟨x, a⟩
  simp [mem_epigraph_iff, sup_le_iff]

/-- Lower semicontinuity is preserved by binary pointwise suprema. -/
theorem lowerSemicontinuous_sup {f g : E → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (fun x => f x ⊔ g x) := by
  simpa [sup_eq_iSup] using
    lowerSemicontinuous_iSup (f := fun b : Bool => fun x => cond b (f x) (g x)) (by
      intro b
      cases b
      · simpa using hg
      · simpa using hf)

/-- Convexity of epigraphs is preserved by binary pointwise suprema. -/
theorem convex_epigraph_sup {f g : E → EReal}
    (hf : Convex ℝ (epigraph f)) (hg : Convex ℝ (epigraph g)) :
    Convex ℝ (epigraph (fun x => f x ⊔ g x)) := by
  simpa [sup_eq_iSup] using
    convex_epigraph_iSup (f := fun b : Bool => fun x => cond b (f x) (g x)) (by
      intro b
      cases b
      · simpa using hg
      · simpa using hf)

/-- The effective domain of a binary pointwise supremum is the intersection of
the effective domains. -/
theorem effectiveDomain_sup {f g : E → EReal} :
    effectiveDomain (fun x => f x ⊔ g x) = effectiveDomain f ∩ effectiveDomain g := by
  ext x
  simp [mem_effectiveDomain_iff, sup_lt_iff]

/-- If two proper functions have a common effective-domain point, then their
binary pointwise supremum is proper. -/
theorem isProper_sup_of_isProper_of_nonempty_effectiveDomain_inter
    {f g : E → EReal} (hf : IsProper f) (_hg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x => f x ⊔ g x) := by
  refine ⟨?_ , ?_⟩
  · simpa [effectiveDomain_sup] using hdom
  · intro x
    exact lt_of_lt_of_le (hf.2 x) le_sup_left

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

/-- Lower semicontinuity is preserved by finite nonempty pointwise infima. -/
theorem lowerSemicontinuous_iInf_of_finite {ι : Type*} [Finite ι] [Nonempty ι]
    {f : ι → E → EReal} (hf : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (fun x => ⨅ i, f i x) := by
  rw [lsc_iff_epigraph_closed_ereal]
  rw [epigraph_iInf_of_finite]
  exact isClosed_iUnion_of_finite fun i =>
    isClosed_epigraph_of_lsc_ereal (f i) (hf i)

/-- The effective domain of a finite nonempty pointwise infimum is the union of
the effective domains. -/
theorem effectiveDomain_iInf_of_finite {ι : Type*} [Finite ι] [Nonempty ι]
    (f : ι → E → EReal) :
    effectiveDomain (fun x => ⨅ i, f i x) = ⋃ i, effectiveDomain (f i) := by
  ext x
  simp only [mem_effectiveDomain_iff, mem_iUnion]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finite.exists_min (fun i => f i x)
    refine ⟨i, ?_⟩
    have hEq : (⨅ j, f j x) = f i x := le_antisymm (iInf_le _ i) (le_iInf hi)
    simpa [← hEq] using h
  · rintro ⟨i, hi⟩
    exact (iInf_le (fun j => f j x) i).trans_lt hi

/-- A finite nonempty pointwise infimum of proper functions is proper. -/
theorem isProper_iInf_of_finite {ι : Type*} [Finite ι] [Nonempty ι]
    {f : ι → E → EReal} (hf : ∀ i, IsProper (f i)) :
    IsProper (fun x => ⨅ i, f i x) := by
  refine ⟨?_, ?_⟩
  · rcases (Classical.choice ‹Nonempty ι›) with i
    rcases (hf i).1 with ⟨x, hx⟩
    exact ⟨x, (iInf_le (fun j => f j x) i).trans_lt hx⟩
  · intro x
    obtain ⟨i, hi⟩ := Finite.exists_min (fun i => f i x)
    have hEq : (⨅ j, f j x) = f i x := le_antisymm (iInf_le _ i) (le_iInf hi)
    simpa [hEq] using (hf i).2 x

/-- The epigraph of a binary pointwise infimum is the union of the two
epigraphs. -/
theorem epigraph_inf {f g : E → EReal} :
    epigraph (fun x => f x ⊓ g x) = epigraph f ∪ epigraph g := by
  ext p
  rcases p with ⟨x, a⟩
  simp [mem_epigraph_iff]

/-- Lower semicontinuity is preserved by binary pointwise infima. -/
theorem lowerSemicontinuous_inf {f g : E → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (fun x => f x ⊓ g x) := by
  simpa [inf_eq_iInf] using
    lowerSemicontinuous_iInf_of_finite (f := fun b : Bool => fun x => cond b (f x) (g x)) (by
      intro b
      cases b
      · simpa using hg
      · simpa using hf)

/-- The effective domain of a binary pointwise infimum is the union of the two
effective domains. -/
theorem effectiveDomain_inf {f g : E → EReal} :
    effectiveDomain (fun x => f x ⊓ g x) = effectiveDomain f ∪ effectiveDomain g := by
  ext x
  simp [mem_effectiveDomain_iff, inf_lt_iff]

/-- The binary pointwise infimum of proper functions is proper. -/
theorem isProper_inf_of_isProper {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) :
    IsProper (fun x => f x ⊓ g x) := by
  have hproper :
      IsProper (fun x => ⨅ b : Bool, cond b (f x) (g x)) :=
    isProper_iInf_of_finite (f := fun b : Bool => fun x => cond b (f x) (g x)) (by
      intro b
      cases b
      · simpa using hg
      · simpa using hf)
  simpa [inf_eq_iInf] using hproper

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
