/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Level Boundedness as Local Boundedness

Example 5.17 is the dictionary entry translating the level boundedness of
Chapter 1 into the local boundedness of Definition 5.14.  Clause (a) reads a
function's level sets as a mapping `α → lev≤α f` and identifies its local
boundedness with level boundedness of `f`; clause (b) does the same for a
parameterized function `f(x,u)`, where the mapping is `u → lev≤α f(·,u)` and
the function-side property is level boundedness in `x` locally uniformly in
`u`, Definition 1.16.

Clause (a) needs none of the covering machinery of 5.15.  Level sets are
nested in `α`, so the image of a neighborhood of `α` under the level-set
mapping already collapses into a single level set at a slightly larger level;
monotonicity does the work that a finite subcover would otherwise do.

Definition 1.16 enters as `IsLevelBoundedInXLocallyUniformly` from
Chapter 3, where it was introduced for parametric minimization.  It packages
the sublevel set inside the product space `IRⁿ × IRᵐ`, cut down by a closed
ball of parameters, whereas 5.17(b) wants the slice in `IRⁿ` alone.  The two
agree because a subset of a product with bounded second projection is bounded
exactly when its first projection is, which is isolated below as
`isBounded_inter_levelSet_iff`.
-/

import RockafellarWets.Chapter3.Parametric
import RockafellarWets.Chapter5.LocalBoundedness
import RockafellarWets.Chapter5.ProfileMappings

open Bornology Filter Metric Set Topology

namespace RW

section LevelSetMapping

variable {E : Type*} [PseudoMetricSpace E]

omit [PseudoMetricSpace E] in
/-- The image of a set of levels under the level-set mapping of `f` collapses
into a single level set whenever that set of levels is bounded above. -/
theorem svImage_levelSet_subset {f : E → EReal} {V : Set ℝ} {β : ℝ}
    (hβ : ∀ α ∈ V, α ≤ β) :
    svImage (fun α : ℝ ↦ levelSet f (α : EReal)) V ⊆ levelSet f (β : EReal) := by
  intro x hx
  obtain ⟨α, hαV, hxα⟩ := mem_svImage.1 hx
  exact levelSet_monotone f (by exact_mod_cast hβ α hαV) hxα

/-- **Example 5.17(a)**: the level-set mapping `α → lev≤α f` is locally
bounded exactly when `f` is level-bounded.

Necessity is the observation that local boundedness at `α` already forces the
single value `lev≤α f` to be bounded.  Sufficiency uses the nesting of level
sets: the unit ball around `α` has image inside `lev≤(α+1) f`. -/
theorem svLocallyBounded_levelSet_iff (f : E → EReal) :
    SvLocallyBounded (fun α : ℝ ↦ levelSet f (α : EReal)) ↔ IsLevelBounded f := by
  constructor
  · intro h α
    exact (h α).isBounded_apply
  · intro h α
    refine ⟨ball α 1, ball_mem_nhds α one_pos, IsBounded.subset (h (α + 1)) ?_⟩
    refine svImage_levelSet_subset fun β hβ ↦ ?_
    have : |β - α| < 1 := by simpa [Real.dist_eq] using mem_ball.1 hβ
    cases abs_lt.1 this with
    | intro _ hub => linarith

/-- **Example 5.17(a)**, phrased through the epigraphical profile mapping of
5.5: the level-set mapping is `Ef⁻¹`. -/
theorem svLocallyBounded_svInv_epiProfile_iff (f : E → EReal) :
    SvLocallyBounded (svInv (epiProfile f)) ↔ IsLevelBounded f :=
  svLocallyBounded_levelSet_iff f

end LevelSetMapping

section ParameterizedLevelSets

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The parameterized level-set mapping `u → {x | f(x,u) ≤ α}` of 5.17(b). -/
def paramLevelSet (f : E × F → EReal) (α : ℝ) : F → Set E :=
  fun u ↦ {x | f (x, u) ≤ (α : EReal)}

omit [NormedAddCommGroup E] [NormedAddCommGroup F] in
@[simp]
theorem mem_paramLevelSet {f : E × F → EReal} {α : ℝ} {u : F} {x : E} :
    x ∈ paramLevelSet f α u ↔ f (x, u) ≤ (α : EReal) := Iff.rfl

omit [NormedAddCommGroup E] [NormedAddCommGroup F] in
/-- The image of a parameter set under the parameterized level-set mapping is
the first projection of the corresponding sublevel slice. -/
theorem svImage_paramLevelSet (f : E × F → EReal) (α : ℝ) (V : Set F) :
    svImage (paramLevelSet f α) V = Prod.fst '' ((univ ×ˢ V) ∩ levelSet f (α : EReal)) := by
  ext x
  simp only [mem_svImage, mem_image, mem_inter_iff, mem_prod, mem_univ, true_and,
    mem_paramLevelSet, levelSet, mem_setOf_eq, Prod.exists]
  constructor
  · rintro ⟨u, huV, hxu⟩
    exact ⟨x, u, ⟨huV, hxu⟩, rfl⟩
  · rintro ⟨y, u, ⟨huV, hyu⟩, rfl⟩
    exact ⟨u, huV, hyu⟩

/-- A sublevel slice over a bounded set of parameters is bounded exactly when
the corresponding image in the decision space is.

This is what reconciles Definition 1.16, which measures boundedness in the
product space, with 5.17(b), which measures it in `IRⁿ`. -/
theorem isBounded_inter_levelSet_iff {f : E × F → EReal} {α : ℝ} {V : Set F}
    (hV : IsBounded V) :
    IsBounded ((univ ×ˢ V) ∩ levelSet f (α : EReal)) ↔
      IsBounded (svImage (paramLevelSet f α) V) := by
  rw [svImage_paramLevelSet]
  refine ⟨IsBounded.image_fst, fun h ↦ IsBounded.subset (h.prod hV) ?_⟩
  rintro ⟨x, u⟩ ⟨⟨-, huV⟩, hxu⟩
  exact ⟨mem_image_of_mem _ ⟨⟨mem_univ x, huV⟩, hxu⟩, huV⟩

/-- **Example 5.17(b)**: `f(x,u)` is level-bounded in `x` locally uniformly in
`u` exactly when, for every level `α`, the mapping `u → {x | f(x,u) ≤ α}` is
locally bounded. -/
theorem isLevelBoundedInXLocallyUniformly_iff_svLocallyBounded (f : E × F → EReal) :
    IsLevelBoundedInXLocallyUniformly f ↔ ∀ α : ℝ, SvLocallyBounded (paramLevelSet f α) := by
  constructor
  · intro h α u
    obtain ⟨eps, heps, hbdd⟩ := h u α
    exact ⟨closedBall u eps, closedBall_mem_nhds u heps,
      (isBounded_inter_levelSet_iff isBounded_closedBall).1 hbdd⟩
  · intro h u α
    obtain ⟨V, hV, hbdd⟩ := h α u
    obtain ⟨eps, heps, hepsV⟩ := Metric.mem_nhds_iff.1 hV
    refine ⟨eps / 2, by positivity, (isBounded_inter_levelSet_iff isBounded_closedBall).2 ?_⟩
    refine hbdd.subset (svImage_mono ?_)
    exact fun z hz ↦
      hepsV (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith)))

/-- **Example 5.17(b)**, final clause: the joint mapping
`(u, α) → {x | f(x,u) ≤ α}` is locally bounded as well.

At `(ū, ᾱ)` one level suffices for a whole neighborhood: every level within
distance `1` of `ᾱ` has its slice inside the slice at level `ᾱ + 1`. -/
theorem svLocallyBounded_paramLevelSet_prod {f : E × F → EReal}
    (h : IsLevelBoundedInXLocallyUniformly f) :
    SvLocallyBounded (fun p : F × ℝ ↦ paramLevelSet f p.2 p.1) := by
  rintro ⟨u, α⟩
  obtain ⟨eps, heps, hbdd⟩ := h u (α + 1)
  refine ⟨closedBall u eps ×ˢ ball α 1,
    prod_mem_nhds (closedBall_mem_nhds u heps) (ball_mem_nhds α one_pos),
    IsBounded.subset ((isBounded_inter_levelSet_iff isBounded_closedBall).1 hbdd) ?_⟩
  intro x hx
  obtain ⟨⟨v, β⟩, ⟨hvu, hβα⟩, hxv⟩ := mem_svImage.1 hx
  refine mem_svImage.2 ⟨v, hvu, ?_⟩
  have hβ : β ≤ α + 1 := by
    have : |β - α| < 1 := by simpa [Real.dist_eq] using mem_ball.1 hβα
    cases abs_lt.1 this with
    | intro _ hub => linarith
  exact le_trans (mem_paramLevelSet.1 hxv) (by exact_mod_cast hβ)

end ParameterizedLevelSets

end RW
