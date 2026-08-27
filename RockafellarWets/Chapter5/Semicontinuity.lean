/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Set-Valued Mappings and Semicontinuity

This file sets up the conventions of Chapter 5 -- domain, range, graph, and
inverse of a set-valued mapping -- then formalizes formula 5(1) and
Definition 5.4.

Formula 5(1) takes the limit along the *full* neighborhood filter of `x̄`, not
the punctured one: the book is explicit that the constant sequence `xν ≡ x̄`
is among those considered.  That choice is what makes `lim sup ⊂ S(x̄)`
equivalent to `lim sup = S(x̄)`, and what forces `S(x̄)` to be closed whenever
`S` is outer semicontinuous at `x̄`.
-/

import RockafellarWets.Chapter5.SetLimitsAlong

open Filter Set Topology

namespace RW

section Mappings

variable {E F : Type*}

/-- The domain of a set-valued mapping: the points with nonempty image. -/
def svDom (S : E → Set F) : Set E := {x | (S x).Nonempty}

/-- The range of a set-valued mapping. -/
def svRange (S : E → Set F) : Set F := {u | ∃ x, u ∈ S x}

/-- The graph of a set-valued mapping. -/
def svGraph (S : E → Set F) : Set (E × F) := {p | p.2 ∈ S p.1}

/-- The inverse of a set-valued mapping.  Unlike the single-valued case this
is always defined, with no injectivity or surjectivity hypothesis. -/
def svInv (S : E → Set F) : F → Set E := fun u ↦ {x | u ∈ S x}

@[simp]
theorem mem_svDom {S : E → Set F} {x : E} :
    x ∈ svDom S ↔ (S x).Nonempty := Iff.rfl

@[simp]
theorem mem_svRange {S : E → Set F} {u : F} :
    u ∈ svRange S ↔ ∃ x, u ∈ S x := Iff.rfl

@[simp]
theorem mem_svGraph {S : E → Set F} {p : E × F} :
    p ∈ svGraph S ↔ p.2 ∈ S p.1 := Iff.rfl

@[simp]
theorem mem_svInv {S : E → Set F} {u : F} {x : E} :
    x ∈ svInv S u ↔ u ∈ S x := Iff.rfl

@[simp]
theorem svInv_svInv (S : E → Set F) : svInv (svInv S) = S := rfl

theorem svDom_svInv (S : E → Set F) : svDom (svInv S) = svRange S := rfl

theorem svRange_svInv (S : E → Set F) : svRange (svInv S) = svDom S := rfl

/-- The graph of the inverse is the graph of `S` with coordinates swapped. -/
theorem svGraph_svInv (S : E → Set F) :
    svGraph (svInv S) = Prod.swap ⁻¹' svGraph S := rfl

end Mappings

section Limits

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- Formula 5(1): the outer limit of `S(x)` as `x → x̄`, taken along the full
neighborhood filter so that the constant sequence at `x̄` is included. -/
def svOuterLimit (S : E → Set F) (x : E) : Set F :=
  outerSetLimitAlong (nhds x) S

/-- Formula 5(1): the inner limit of `S(x)` as `x → x̄`. -/
def svInnerLimit (S : E → Set F) (x : E) : Set F :=
  innerSetLimitAlong (nhds x) S

/-- Formula 5(1) relative to a set `X`, as in the paragraph following
Definition 5.4. -/
def svOuterLimitWithin (S : E → Set F) (X : Set E) (x : E) : Set F :=
  outerSetLimitAlong (nhdsWithin x X) S

/-- Formula 5(1) relative to a set `X`. -/
def svInnerLimitWithin (S : E → Set F) (X : Set E) (x : E) : Set F :=
  innerSetLimitAlong (nhdsWithin x X) S

theorem svOuterLimitWithin_univ (S : E → Set F) (x : E) :
    svOuterLimitWithin S univ x = svOuterLimit S x := by
  rw [svOuterLimitWithin, svOuterLimit, nhdsWithin_univ]

theorem svInnerLimitWithin_univ (S : E → Set F) (x : E) :
    svInnerLimitWithin S univ x = svInnerLimit S x := by
  rw [svInnerLimitWithin, svInnerLimit, nhdsWithin_univ]

/-- The image at the base point always lies in the outer limit: the constant
sequence `xν ≡ x̄` is admissible in 5(1). -/
theorem subset_svOuterLimit (S : E → Set F) (x : E) : S x ⊆ svOuterLimit S x := by
  intro u hu V hV
  rw [Filter.frequently_iff]
  intro U hU
  exact ⟨x, mem_of_mem_nhds hU, ⟨u, hu, mem_of_mem_nhds hV⟩⟩

/-- The relative form: at a point of `X` the constant sequence `xν ≡ x̄` is
still admissible, since `x̄ ∈ X`. -/
theorem subset_svOuterLimitWithin (S : E → Set F) {X : Set E} {x : E}
    (hx : x ∈ X) : S x ⊆ svOuterLimitWithin S X x := by
  intro u hu V hV
  rw [Filter.frequently_iff]
  intro U hU
  exact ⟨x, mem_of_mem_nhdsWithin hx hU, ⟨u, hu, mem_of_mem_nhds hV⟩⟩

/-- The inner limit is contained in the outer limit. -/
theorem svInnerLimit_subset_svOuterLimit (S : E → Set F) (x : E) :
    svInnerLimit S x ⊆ svOuterLimit S x :=
  innerSetLimitAlong_subset_outerSetLimitAlong S

/-- Both limits at a point are closed sets. -/
theorem isClosed_svOuterLimit (S : E → Set F) (x : E) :
    IsClosed (svOuterLimit S x) :=
  isClosed_outerSetLimitAlong _ S

theorem isClosed_svInnerLimit (S : E → Set F) (x : E) :
    IsClosed (svInnerLimit S x) :=
  isClosed_innerSetLimitAlong _ S

end Limits

section Definition54

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Definition 5.4**: `S` is outer semicontinuous at `x`. -/
def SvOscAt (S : E → Set F) (x : E) : Prop := svOuterLimit S x ⊆ S x

/-- **Definition 5.4**: `S` is inner semicontinuous at `x`. -/
def SvIscAt (S : E → Set F) (x : E) : Prop := S x ⊆ svInnerLimit S x

/-- **Definition 5.4**: `S` is continuous at `x` when it is both outer and
inner semicontinuous there. -/
def SvContinuousAt (S : E → Set F) (x : E) : Prop := SvOscAt S x ∧ SvIscAt S x

/-- **Definition 5.4** relative to a set `X`. -/
def SvOscWithinAt (S : E → Set F) (X : Set E) (x : E) : Prop :=
  svOuterLimitWithin S X x ⊆ S x

/-- **Definition 5.4** relative to a set `X`. -/
def SvIscWithinAt (S : E → Set F) (X : Set E) (x : E) : Prop :=
  S x ⊆ svInnerLimitWithin S X x

/-- **Definition 5.4**, set-wide form: `S` is outer semicontinuous relative
to `X` when it is so at every point of `X`. -/
def SvOscOn (S : E → Set F) (X : Set E) : Prop := ∀ x ∈ X, SvOscWithinAt S X x

/-- **Definition 5.4**, set-wide form of inner semicontinuity. -/
def SvIscOn (S : E → Set F) (X : Set E) : Prop := ∀ x ∈ X, SvIscWithinAt S X x

/-- **Definition 5.4**: `S` is outer semicontinuous everywhere. -/
def SvOsc (S : E → Set F) : Prop := ∀ x, SvOscAt S x

/-- **Definition 5.4**: `S` is inner semicontinuous everywhere. -/
def SvIsc (S : E → Set F) : Prop := ∀ x, SvIscAt S x

/-- **Definition 5.4**: the equivalent equality form of outer
semicontinuity. -/
theorem svOscAt_iff_svOuterLimit_eq {S : E → Set F} {x : E} :
    SvOscAt S x ↔ svOuterLimit S x = S x :=
  ⟨fun h ↦ Subset.antisymm h (subset_svOuterLimit S x), fun h ↦ h.subset⟩

/-- Outer semicontinuity at `x` forces `S x` to be closed, as the book notes
immediately after Definition 5.4. -/
theorem SvOscAt.isClosed {S : E → Set F} {x : E} (h : SvOscAt S x) :
    IsClosed (S x) := by
  rw [← svOscAt_iff_svOuterLimit_eq.1 h]
  exact isClosed_svOuterLimit S x

/-- **Definition 5.4** relative to `X`: the equality form of outer
semicontinuity. -/
theorem svOscWithinAt_iff_svOuterLimitWithin_eq {S : E → Set F} {X : Set E}
    {x : E} (hx : x ∈ X) :
    SvOscWithinAt S X x ↔ svOuterLimitWithin S X x = S x :=
  ⟨fun h ↦ Subset.antisymm h (subset_svOuterLimitWithin S hx), fun h ↦ h.subset⟩

/-- The book records that `S(x̄)` is closed under outer semicontinuity
"whether in the main sense or merely relative to some subset `X`". -/
theorem SvOscWithinAt.isClosed {S : E → Set F} {X : Set E} {x : E}
    (hx : x ∈ X) (h : SvOscWithinAt S X x) : IsClosed (S x) := by
  rw [← (svOscWithinAt_iff_svOuterLimitWithin_eq hx).1 h]
  exact isClosed_outerSetLimitAlong _ S

/-- An outer semicontinuous mapping relative to `X` is closed-valued on
`X`. -/
theorem SvOscOn.isClosed_apply {S : E → Set F} {X : Set E} (h : SvOscOn S X)
    {x : E} (hx : x ∈ X) : IsClosed (S x) :=
  (h x hx).isClosed hx

/-- For a closed-valued mapping, inner semicontinuity has the equivalent
equality form. -/
theorem svIscAt_iff_svInnerLimit_eq {S : E → Set F} {x : E}
    (hclosed : SvOscAt S x) :
    SvIscAt S x ↔ svInnerLimit S x = S x := by
  constructor
  · intro h
    refine Subset.antisymm ?_ h
    exact (svInnerLimit_subset_svOuterLimit S x).trans hclosed
  · intro h
    exact h.symm.subset

/-- Continuity at `x` says exactly that both limits agree with `S x`. -/
theorem svContinuousAt_iff {S : E → Set F} {x : E} :
    SvContinuousAt S x ↔
      svOuterLimit S x = S x ∧ svInnerLimit S x = S x := by
  constructor
  · rintro ⟨hosc, hisc⟩
    exact ⟨svOscAt_iff_svOuterLimit_eq.1 hosc,
      (svIscAt_iff_svInnerLimit_eq hosc).1 hisc⟩
  · rintro ⟨houter, hinner⟩
    exact ⟨svOscAt_iff_svOuterLimit_eq.2 houter, hinner.symm.subset⟩

/-- The remark following Definition 5.4: inner semicontinuity at a point of
the domain forces a whole neighborhood to lie in the domain. -/
theorem SvIscAt.eventually_mem_svDom {S : E → Set F} {x : E}
    (h : SvIscAt S x) (hx : x ∈ svDom S) :
    ∀ᶠ y in nhds x, y ∈ svDom S := by
  obtain ⟨u, hu⟩ := hx
  simpa [svDom] using h hu univ univ_mem

/-- Consequently an inner semicontinuous mapping has its base point in the
interior of the domain, as the book records for `X = IRⁿ`. -/
theorem SvIscAt.mem_interior_svDom {S : E → Set F} {x : E}
    (h : SvIscAt S x) (hx : x ∈ svDom S) :
    x ∈ interior (svDom S) :=
  mem_interior_iff_mem_nhds.2 (h.eventually_mem_svDom hx)

/-- The relative form of the same remark: `X ∩ V ⊂ dom S` for some
neighborhood `V` of the base point. -/
theorem SvIscWithinAt.eventually_mem_svDom {S : E → Set F} {X : Set E} {x : E}
    (h : SvIscWithinAt S X x) (hx : x ∈ svDom S) :
    ∀ᶠ y in nhdsWithin x X, y ∈ svDom S := by
  obtain ⟨u, hu⟩ := hx
  simpa [svDom] using h hu univ univ_mem

/-- The absolute notions are the case `X = univ` of the relative ones. -/
theorem svOscWithinAt_univ {S : E → Set F} {x : E} :
    SvOscWithinAt S univ x ↔ SvOscAt S x := by
  rw [SvOscWithinAt, SvOscAt, svOuterLimitWithin_univ]

theorem svIscWithinAt_univ {S : E → Set F} {x : E} :
    SvIscWithinAt S univ x ↔ SvIscAt S x := by
  rw [SvIscWithinAt, SvIscAt, svInnerLimitWithin_univ]

theorem svOscOn_univ {S : E → Set F} : SvOscOn S univ ↔ SvOsc S := by
  constructor
  · intro h x; exact svOscWithinAt_univ.1 (h x (mem_univ x))
  · intro h x _; exact svOscWithinAt_univ.2 (h x)

theorem svIscOn_univ {S : E → Set F} : SvIscOn S univ ↔ SvIsc S := by
  constructor
  · intro h x; exact svIscWithinAt_univ.1 (h x (mem_univ x))
  · intro h x _; exact svIscWithinAt_univ.2 (h x)

end Definition54

end RW
