/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Graphical Convergence Relative to a Set

The paragraph after 5.33 defines graphical convergence of `Sν` to `S`
*relative to a set* `X`: formula 5(7) is required at every `x̄ ∈ X`, but with
the approaching sequences `xν → x̄` constrained to `X`.  The book then records
that for closed `X` this is the same as graphical convergence of the
restrictions `Sν|X` to `S|X`, the restriction being the mapping that agrees
with `S` on `X` and is empty-valued everywhere else.

Constraining the sequences shrinks *both* limits, so relative graphical
convergence neither implies nor is implied by the absolute notion; only the
two inclusions taken together say anything, and that is why the definition
below is stated as a pair rather than as an equality of limits.

The identification with the restrictions splits at `X`, and the two halves
use `X` differently.

* At a point of `X` the restricted mappings see only arguments of `X`, so a
  sequence witnessing a limit for `Sν|X` already lies in `X` where it
  matters -- eventually for the inner limit, only frequently for the outer
  one.  The remaining indices are repaired at no cost by `x̄` itself, which
  belongs to `X`: `Function.extend` off the subsequence for the outer limit,
  a finite modification for the inner one.  Closedness plays no part here.

* Off `X` the restricted mappings are empty-valued, so the inner inclusion is
  vacuous and everything rests on the graphical outer limit vanishing.  That
  is exactly where `X` has to be closed: a point of that outer limit at `x̄`
  is approached from arguments of `X`, putting `x̄` in `cl X`.

Closedness is not a technicality.  `restrict_not_graphicalConverges_of_not_isClosed`
exhibits a constant sequence of mappings that converges graphically relative
to `X = (0, ∞)` and yet whose restrictions do not converge graphically, their
graphs picking up a point over `0 ∈ cl X \ X`.
-/

import RockafellarWets.Chapter5.GraphicalLimitFormulas
import RockafellarWets.Chapter5.LocallyBoundedContinuity

open Filter Metric Set Topology

namespace RW

section Definitions

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- The graphical outer limit at `x` **relative to** `X`: the union of the
Chapter 4 outer limits of `Sν(xν)` over the sequences `xν → x` lying in `X`. -/
def graphicalOuterLimitWithin (Sseq : ℕ → E → Set F) (X : Set E) (x : E) : Set F :=
  ⋃ y ∈ svApproachSeqs X x, outerSetLimit fun n ↦ Sseq n (y n)

/-- The graphical inner limit at `x` **relative to** `X`. -/
def graphicalInnerLimitWithin (Sseq : ℕ → E → Set F) (X : Set E) (x : E) : Set F :=
  ⋃ y ∈ svApproachSeqs X x, innerSetLimit fun n ↦ Sseq n (y n)

/-- The paragraph after 5.33: `Sν → S` graphically at `x̄` relative to `X`,
i.e. formula 5(7) at `x̄` with `xν` constrained to `X`. -/
def GraphicalConvergesWithinAt (Sseq : ℕ → E → Set F) (S : E → Set F)
    (X : Set E) (x : E) : Prop :=
  graphicalOuterLimitWithin Sseq X x ⊆ S x ∧
    S x ⊆ graphicalInnerLimitWithin Sseq X x

/-- The paragraph after 5.33: `Sν → S` graphically relative to `X`. -/
def GraphicalConvergesOn (Sseq : ℕ → E → Set F) (S : E → Set F) (X : Set E) :
    Prop :=
  ∀ x ∈ X, GraphicalConvergesWithinAt Sseq S X x

variable {Sseq : ℕ → E → Set F} {X Y : Set E} {x : E} {u : F}

theorem mem_graphicalOuterLimitWithin_iff :
    u ∈ graphicalOuterLimitWithin Sseq X x ↔
      ∃ y ∈ svApproachSeqs X x, u ∈ outerSetLimit fun n ↦ Sseq n (y n) := by
  simp only [graphicalOuterLimitWithin, mem_iUnion₂, exists_prop]

theorem mem_graphicalInnerLimitWithin_iff :
    u ∈ graphicalInnerLimitWithin Sseq X x ↔
      ∃ y ∈ svApproachSeqs X x, u ∈ innerSetLimit fun n ↦ Sseq n (y n) := by
  simp only [graphicalInnerLimitWithin, mem_iUnion₂, exists_prop]

/-- Relative inner limits sit inside relative outer limits, as in 5.32. -/
theorem graphicalInnerLimitWithin_subset_graphicalOuterLimitWithin
    (Sseq : ℕ → E → Set F) (X : Set E) (x : E) :
    graphicalInnerLimitWithin Sseq X x ⊆ graphicalOuterLimitWithin Sseq X x :=
  iUnion₂_mono fun _ _ ↦ innerSetLimit_subset_outerSetLimit _

/-- Both relative limits are monotone in the constraining set: a larger `X`
admits more approaching sequences. -/
theorem graphicalOuterLimitWithin_mono (Sseq : ℕ → E → Set F) (hXY : X ⊆ Y)
    (x : E) :
    graphicalOuterLimitWithin Sseq X x ⊆ graphicalOuterLimitWithin Sseq Y x :=
  iUnion₂_subset fun y hy ↦
    subset_iUnion₂ (s := fun y (_ : y ∈ svApproachSeqs Y x) ↦
      outerSetLimit fun n ↦ Sseq n (y n)) y ⟨fun n ↦ hXY (hy.1 n), hy.2⟩

theorem graphicalInnerLimitWithin_mono (Sseq : ℕ → E → Set F) (hXY : X ⊆ Y)
    (x : E) :
    graphicalInnerLimitWithin Sseq X x ⊆ graphicalInnerLimitWithin Sseq Y x :=
  iUnion₂_subset fun y hy ↦
    subset_iUnion₂ (s := fun y (_ : y ∈ svApproachSeqs Y x) ↦
      innerSetLimit fun n ↦ Sseq n (y n)) y ⟨fun n ↦ hXY (hy.1 n), hy.2⟩

end Definitions

section Absolute

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {x : E}

/-- Relative to the whole space the relative outer limit is the graphical
outer limit of 5.32. -/
theorem graphicalOuterLimitWithin_univ (Sseq : ℕ → E → Set F) (x : E) :
    graphicalOuterLimitWithin Sseq univ x = graphicalOuterLimit Sseq x := by
  rw [graphicalOuterLimitWithin, svApproachSeqs_univ, graphicalOuterLimit_eq_iUnion]

theorem graphicalInnerLimitWithin_univ (Sseq : ℕ → E → Set F) (x : E) :
    graphicalInnerLimitWithin Sseq univ x = graphicalInnerLimit Sseq x := by
  rw [graphicalInnerLimitWithin, svApproachSeqs_univ, graphicalInnerLimit_eq_iUnion]

/-- Relative graphical convergence at `x̄` relative to the whole space is the
graphical convergence at `x̄` of 5(7). -/
theorem graphicalConvergesWithinAt_univ_iff :
    GraphicalConvergesWithinAt Sseq S univ x ↔ GraphicalConvergesAt Sseq S x := by
  rw [GraphicalConvergesWithinAt, GraphicalConvergesAt,
    graphicalOuterLimitWithin_univ, graphicalInnerLimitWithin_univ]

/-- Relative graphical convergence relative to the whole space is graphical
convergence. -/
theorem graphicalConvergesOn_univ_iff :
    GraphicalConvergesOn Sseq S univ ↔ GraphicalConverges Sseq S := by
  rw [GraphicalConvergesOn, graphicalConverges_iff_forall_graphicalConvergesAt]
  exact ⟨fun h x ↦ graphicalConvergesWithinAt_univ_iff.1 (h x (mem_univ x)),
    fun h x _ ↦ graphicalConvergesWithinAt_univ_iff.2 (h x)⟩

end Absolute

section Restriction

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E} {x : E}

/-- At a point of `X` the graphical outer limit of the restrictions is the
relative graphical outer limit.

A witnessing subsequence for the restrictions lies in `X` automatically, and
`Function.extend` parks the unused indices at `x̄ ∈ X`. -/
theorem graphicalOuterLimit_svRestrict (Sseq : ℕ → E → Set F) (hx : x ∈ X) :
    graphicalOuterLimit (fun n ↦ svRestrict (Sseq n) X) x =
      graphicalOuterLimitWithin Sseq X x := by
  refine Subset.antisymm (fun u hu ↦ ?_) (iUnion₂_subset fun y hy u hu ↦ ?_)
  · obtain ⟨φ, y, v, hφ, hv, hy, hvu⟩ := mem_graphicalOuterLimit_iff.1 hu
    refine mem_graphicalOuterLimitWithin_iff.2
      ⟨Function.extend φ y (fun _ ↦ x), ⟨fun j ↦ ?_, tendsto_extend_of_strictMono hφ hy⟩,
        fun W hW ↦ ?_⟩
    · by_cases hj : ∃ n, φ n = j
      · obtain ⟨n, rfl⟩ := hj
        rw [hφ.injective.extend_apply]
        exact (hv n).2
      · rw [Function.extend_apply' _ _ _ hj]
        exact hx
    · have hev : ∀ᶠ n in atTop,
          (Sseq (φ n) (Function.extend φ y (fun _ ↦ x) (φ n)) ∩ W).Nonempty := by
        filter_upwards [hvu.eventually_mem hW] with n hn
        rw [hφ.injective.extend_apply]
        exact ⟨v n, (hv n).1, hn⟩
      exact Frequently.filter_mono
        ((frequently_map (m := φ)).2 hev.frequently) hφ.tendsto_atTop
  · have hval : (fun n ↦ svRestrict (Sseq n) X (y n)) = fun n ↦ Sseq n (y n) :=
      funext fun n ↦ svRestrict_apply (hy.1 n)
    rw [graphicalOuterLimit_eq_iUnion]
    exact mem_iUnion₂.2 ⟨y, hy.2, by rw [hval]; exact hu⟩

/-- At a point of `X` the graphical inner limit of the restrictions is the
relative graphical inner limit.

Here the witnessing sequence lies in `X` only eventually, and the finitely
many stray terms are replaced by `x̄ ∈ X`; neither the limit of the sequence
nor the inner limit of the values feels a finite modification. -/
theorem graphicalInnerLimit_svRestrict (Sseq : ℕ → E → Set F) (hx : x ∈ X) :
    graphicalInnerLimit (fun n ↦ svRestrict (Sseq n) X) x =
      graphicalInnerLimitWithin Sseq X x := by
  classical
  refine Subset.antisymm (fun u hu ↦ ?_) (iUnion₂_subset fun y hy u hu ↦ ?_)
  · obtain ⟨y, v, hv, hy, hvu⟩ := mem_graphicalInnerLimit_iff.1 hu
    obtain ⟨N, hN⟩ := eventually_atTop.1 hv
    have hz : (fun n ↦ if N ≤ n then y n else x) =ᶠ[atTop] y := by
      filter_upwards [eventually_ge_atTop N] with n hn
      simp only [if_pos hn]
    refine mem_graphicalInnerLimitWithin_iff.2
      ⟨fun n ↦ if N ≤ n then y n else x, ⟨fun n ↦ ?_, hy.congr' hz.symm⟩, ?_⟩
    · by_cases hn : N ≤ n
      · simpa only [if_pos hn] using (hN n hn).2
      · simpa only [if_neg hn] using hx
    · refine mem_innerSetLimit_iff_exists_seq.2 ⟨v, ?_, hvu⟩
      filter_upwards [eventually_ge_atTop N] with n hn
      simpa only [if_pos hn] using (hN n hn).1
  · have hval : (fun n ↦ svRestrict (Sseq n) X (y n)) = fun n ↦ Sseq n (y n) :=
      funext fun n ↦ svRestrict_apply (hy.1 n)
    rw [graphicalInnerLimit_eq_iUnion]
    exact mem_iUnion₂.2 ⟨y, hy.2, by rw [hval]; exact hu⟩

/-- Off a **closed** `X` the restrictions have empty graphical outer limit:
their values are approached only from arguments of `X`, so a point of that
limit would put `x̄` in `cl X = X`. -/
theorem graphicalOuterLimit_svRestrict_eq_empty (Sseq : ℕ → E → Set F)
    (hX : IsClosed X) (hx : x ∉ X) :
    graphicalOuterLimit (fun n ↦ svRestrict (Sseq n) X) x = ∅ := by
  refine eq_empty_of_forall_notMem fun u hu ↦ ?_
  obtain ⟨φ, y, v, hφ, hv, hy, hvu⟩ := mem_graphicalOuterLimit_iff.1 hu
  exact hx (hX.mem_of_tendsto hy (Eventually.of_forall fun n ↦ (hv n).2))

/-- **The paragraph after 5.33**: for closed `X`, graphical convergence
relative to `X` is graphical convergence of the restrictions. -/
theorem graphicalConvergesOn_iff_graphicalConverges_svRestrict (hX : IsClosed X) :
    GraphicalConvergesOn Sseq S X ↔
      GraphicalConverges (fun n ↦ svRestrict (Sseq n) X) (svRestrict S X) := by
  rw [graphicalConverges_iff]
  constructor
  · intro h
    refine ⟨fun z ↦ ?_, fun z ↦ ?_⟩
    · by_cases hz : z ∈ X
      · rw [graphicalOuterLimit_svRestrict _ hz, svRestrict_apply hz]
        exact (h z hz).1
      · rw [graphicalOuterLimit_svRestrict_eq_empty _ hX hz]
        exact empty_subset _
    · by_cases hz : z ∈ X
      · rw [graphicalInnerLimit_svRestrict _ hz, svRestrict_apply hz]
        exact (h z hz).2
      · rw [svRestrict_eq_empty hz]
        exact empty_subset _
  · rintro ⟨hout, hin⟩ z hz
    have h₁ := hout z
    have h₂ := hin z
    rw [graphicalOuterLimit_svRestrict _ hz, svRestrict_apply hz] at h₁
    rw [graphicalInnerLimit_svRestrict _ hz, svRestrict_apply hz] at h₂
    exact ⟨h₁, h₂⟩

/-- The relative counterpart of the displayed formula of 5.32 for the outer
limit: membership is witnessed by a subsequence of values taken at arguments
of `X` approaching `x̄`. -/
theorem mem_graphicalOuterLimitWithin_iff_exists_subsequence {u : F} (hx : x ∈ X) :
    u ∈ graphicalOuterLimitWithin Sseq X x ↔
      ∃ (φ : ℕ → ℕ) (y : ℕ → E) (v : ℕ → F), StrictMono φ ∧ (∀ n, y n ∈ X) ∧
        (∀ n, v n ∈ Sseq (φ n) (y n)) ∧
        Tendsto y atTop (nhds x) ∧ Tendsto v atTop (nhds u) := by
  rw [← graphicalOuterLimit_svRestrict Sseq hx, mem_graphicalOuterLimit_iff]
  constructor
  · rintro ⟨φ, y, v, hφ, hv, hy, hvu⟩
    exact ⟨φ, y, v, hφ, fun n ↦ (hv n).2, fun n ↦ (hv n).1, hy, hvu⟩
  · rintro ⟨φ, y, v, hφ, hyX, hv, hy, hvu⟩
    exact ⟨φ, y, v, hφ, fun n ↦ ⟨hv n, hyX n⟩, hy, hvu⟩

/-- The relative counterpart for the inner limit: no subsequence is needed,
but the selection -- membership in `X` included -- is only eventual. -/
theorem mem_graphicalInnerLimitWithin_iff_exists_seq {u : F} (hx : x ∈ X) :
    u ∈ graphicalInnerLimitWithin Sseq X x ↔
      ∃ (y : ℕ → E) (v : ℕ → F),
        (∀ᶠ n in atTop, y n ∈ X ∧ v n ∈ Sseq n (y n)) ∧
        Tendsto y atTop (nhds x) ∧ Tendsto v atTop (nhds u) := by
  rw [← graphicalInnerLimit_svRestrict Sseq hx, mem_graphicalInnerLimit_iff]
  constructor
  · rintro ⟨y, v, hv, hy, hvu⟩
    exact ⟨y, v, hv.mono fun n hn ↦ ⟨hn.2, hn.1⟩, hy, hvu⟩
  · rintro ⟨y, v, hv, hy, hvu⟩
    exact ⟨y, v, hv.mono fun n hn ↦ ⟨hn.2, hn.1⟩, hy, hvu⟩

/-- The constant sequence at `x̄ ∈ X` is admissible, so the pointwise limits
at `x̄` sit inside the relative graphical ones -- formula 5(11), relative
version. -/
theorem pointwiseOuterLimit_subset_graphicalOuterLimitWithin
    (Sseq : ℕ → E → Set F) (hx : x ∈ X) :
    pointwiseOuterLimit Sseq x ⊆ graphicalOuterLimitWithin Sseq X x :=
  subset_iUnion₂_of_subset (fun _ ↦ x) ⟨fun _ ↦ hx, tendsto_const_nhds⟩ Subset.rfl

theorem pointwiseInnerLimit_subset_graphicalInnerLimitWithin
    (Sseq : ℕ → E → Set F) (hx : x ∈ X) :
    pointwiseInnerLimit Sseq x ⊆ graphicalInnerLimitWithin Sseq X x :=
  subset_iUnion₂_of_subset (fun _ ↦ x) ⟨fun _ ↦ hx, tendsto_const_nhds⟩ Subset.rfl

/-- A relative graphical limit is closed-valued on a closed `X`, by the
remark after 5.32 applied to the restrictions. -/
theorem GraphicalConvergesOn.isClosed_apply (hX : IsClosed X)
    (h : GraphicalConvergesOn Sseq S X) (hx : x ∈ X) : IsClosed (S x) := by
  have := (((graphicalConvergesOn_iff_graphicalConverges_svRestrict hX).1 h).svOsc x).isClosed
  rwa [svRestrict_apply hx] at this

end Restriction

section ClosednessNeeded

open scoped Topology

/-- Closedness of `X` is not a technicality in the identification above.

Take `X = (0, ∞) ⊂ IR`, and let every `Sν` be the constant mapping with value
`{0}`.  The sequence converges graphically to that mapping relative to `X` --
a constant sequence converges to itself and the value `{0}` is closed -- yet
the restrictions do not converge graphically to the restriction: their common
graph is `(0, ∞) × {0}`, whose outer limit reaches the point `(0, 0)` lying
over `0 ∈ cl X \ X`, where the restriction is empty-valued. -/
theorem restrict_not_graphicalConverges_of_not_isClosed :
    GraphicalConvergesOn (fun (_ : ℕ) (_ : ℝ) ↦ ({0} : Set ℝ))
        (fun _ ↦ ({0} : Set ℝ)) (Ioi 0) ∧
      ¬ GraphicalConverges
        (fun (_ : ℕ) ↦ svRestrict (fun (_ : ℝ) ↦ ({0} : Set ℝ)) (Ioi 0))
        (svRestrict (fun _ ↦ ({0} : Set ℝ)) (Ioi 0)) := by
  constructor
  · intro x hx
    constructor
    · refine iUnion₂_subset fun y _ ↦ ?_
      simpa only [outerSetLimit_const, isClosed_singleton.closure_eq] using Subset.rfl
    · refine subset_iUnion₂_of_subset (fun _ ↦ x)
        ⟨fun _ ↦ hx, tendsto_const_nhds⟩ ?_
      simpa only [innerSetLimit_const, isClosed_singleton.closure_eq] using Subset.rfl
  · rw [graphicalConverges_iff]
    rintro ⟨hout, -⟩
    have hmem : (0 : ℝ) ∈
        graphicalOuterLimit
          (fun (_ : ℕ) ↦ svRestrict (fun (_ : ℝ) ↦ ({0} : Set ℝ)) (Ioi 0)) 0 := by
      refine mem_graphicalOuterLimit_iff.2
        ⟨id, fun n ↦ ((n : ℝ) + 1)⁻¹, fun _ ↦ 0, strictMono_id,
          fun n ↦ ⟨rfl, mem_Ioi.2 (by positivity)⟩, ?_, tendsto_const_nhds⟩
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := hout 0 hmem
    rw [svRestrict_eq_empty (by simp)] at this
    exact this
end ClosednessNeeded

end RW
