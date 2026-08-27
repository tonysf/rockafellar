/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Inner Semicontinuity from Convexity

Inner semicontinuity is harder to verify than outer semicontinuity and is not
constructive in the way the osc hull is.  Theorem 5.9 supplies the criteria
that convexity makes available, together with formula 5(4) relating
graph-convexity to the inclusion `S((1-τ)x₀ + τx₁) ⊃ (1-τ)S(x₀) + τS(x₁)`.

All three clauses run through the sequential bridge of
`SequentialLimits.lean`, because the Chapter 4 convexity results they invoke
-- 4.15 for (a), 4.32(c) for (b), 4.30's inner-limit half for (c) -- are all
stated for sequences of sets.  With the bridge in place each clause becomes a
short reduction:

* (a) is 4.15 in one direction and the closedness of inner limits, plus
  `cl(int C) = cl C` for convex `C` with nonempty interior, in the other;
* (b) intersects the fibre `{x} × IRᵐ` with `gph S` inside `IRⁿ × IRᵐ` and
  applies 4.32(c), the non-separation hypothesis being exactly
  `x̄ ∈ int(dom S)`;
* (c) is the inner-limit half of 4.30 composed with monotonicity of the
  convex hull.
-/

import RockafellarWets.Chapter4.ConvexHullConvergence
import RockafellarWets.Chapter4.ConvexInternalApproximation
import RockafellarWets.Chapter4.ConvexSystemConvergence
import RockafellarWets.Chapter5.SemicontinuityCriteria

open Filter Metric Set Topology

open scoped Pointwise

namespace RW

section Definitions

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
variable [Module ℝ F]

/-- A set-valued mapping is convex-valued when each image set is convex. -/
def SvConvexValued (S : E → Set F) : Prop := ∀ x, Convex ℝ (S x)

/-- A set-valued mapping is graph-convex when its graph is convex. -/
def SvGraphConvex (S : E → Set F) : Prop := Convex ℝ (svGraph S)

/-- Graph-convexity implies convex-valuedness. -/
theorem SvGraphConvex.svConvexValued {S : E → Set F} (h : SvGraphConvex S) :
    SvConvexValued S := by
  intro x u hu v hv a b ha hb hab
  have := h (x := (x, u)) hu (y := (x, v)) hv ha hb hab
  simpa [svGraph, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab] using this

/-- **Formula 5(4).**  Graph-convexity is the inclusion
`S((1-τ)x₀ + τx₁) ⊃ (1-τ)S(x₀) + τS(x₁)` for `τ ∈ (0,1)`. -/
theorem svGraphConvex_iff (S : E → Set F) :
    SvGraphConvex S ↔ ∀ (x₀ x₁ : E) (τ : ℝ), 0 < τ → τ < 1 →
      (1 - τ) • S x₀ + τ • S x₁ ⊆ S ((1 - τ) • x₀ + τ • x₁) := by
  constructor
  · rintro h x₀ x₁ τ hτ0 hτ1 - ⟨-, ⟨u₀, hu₀, rfl⟩, -, ⟨u₁, hu₁, rfl⟩, rfl⟩
    exact h (x := (x₀, u₀)) hu₀ (y := (x₁, u₁)) hu₁ (by linarith) hτ0.le
      (by ring)
  · intro h
    rintro ⟨x₀, u₀⟩ hu₀ ⟨x₁, u₁⟩ hu₁ a b ha hb hab
    rcases ha.lt_or_eq with ha' | ha'
    · rcases hb.lt_or_eq with hb' | hb'
      · have hb1 : b < 1 := by linarith
        have ha1 : a = 1 - b := by linarith
        subst ha1
        exact h x₀ x₁ b hb' hb1
          ⟨(1 - b) • u₀, ⟨u₀, hu₀, rfl⟩, b • u₁, ⟨u₁, hu₁, rfl⟩, rfl⟩
      · simp only [← hb', zero_smul, add_zero] at hab ⊢
        simpa [hab] using hu₀
    · simp only [← ha', zero_smul, zero_add] at hab ⊢
      simpa [hab] using hu₁

end Definitions

section ProductLimits

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- A product of inner-limit points lies in the inner limit of the products.
This is the binary case of 4.29's inner half, in the form 5.9(b) needs. -/
theorem prod_innerSetLimit_subset (A : ℕ → Set E) (B : ℕ → Set F) :
    innerSetLimit A ×ˢ innerSetLimit B ⊆ innerSetLimit fun n ↦ A n ×ˢ B n := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩ W hW
  obtain ⟨U, hU, N, hN, hUN⟩ := mem_nhds_prod_iff.1 hW
  filter_upwards [ha U hU, hb N hN] with n hnA hnB
  obtain ⟨p, hpA, hpU⟩ := hnA
  obtain ⟨q, hqB, hqN⟩ := hnB
  exact ⟨(p, q), ⟨hpA, hqB⟩, hUN ⟨hpU, hqN⟩⟩

/-- The second component of a point in the inner limit of products lies in
the inner limit of the second factors. -/
theorem snd_mem_innerSetLimit_of_mem_prod {A : ℕ → Set E} {B : ℕ → Set F}
    {a : E} {b : F} (h : (a, b) ∈ innerSetLimit fun n ↦ A n ×ˢ B n) :
    b ∈ innerSetLimit B := by
  intro N hN
  filter_upwards [h ((univ : Set E) ×ˢ N) (prod_mem_nhds univ_mem hN)] with n hn
  obtain ⟨p, hp₁, hp₂⟩ := hn
  exact ⟨p.2, hp₁.2, hp₂.2⟩

end ProductLimits

section ConvexCriteria

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Theorem 5.9(a).**  For a convex-valued mapping whose image at `x` has
nonempty interior, inner semicontinuity relative to `X` at `x` is the
condition that each interior image point `u` has a neighborhood of `(x, u)`
whose trace on `X × IRᵐ` lies in `gph S`.

The forward direction shrinks a compact ball around `u` and uses 4.15 to keep
it inside `int S(x')` for all nearby `x' ∈ X`.  The converse notes that the
condition puts every interior image point in the inner limit, which is
closed, so it contains `cl(int S(x)) = cl S(x) ⊇ S(x)`. -/
theorem svIscWithinAt_iff_of_convexValued {S : E → Set F} {X : Set E} {x : E}
    (hx : x ∈ X) (hconv : SvConvexValued S) (hne : (interior (S x)).Nonempty) :
    SvIscWithinAt S X x ↔
      ∀ u ∈ interior (S x), ∃ W ∈ nhds (x, u),
        W ∩ (X ×ˢ (univ : Set F)) ⊆ svGraph S := by
  constructor
  · intro h u hu
    obtain ⟨r, hr, hB⟩ : ∃ r > 0, closedBall u r ⊆ interior (S x) := by
      obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.1 isOpen_interior u hu
      refine ⟨s / 2, by linarith, fun z hz ↦ hball (mem_ball.2 ?_)⟩
      exact lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith)
    have hseq : ∀ y : ℕ → E, Tendsto y atTop (nhdsWithin x X) →
        ∀ᶠ n in atTop, closedBall u r ⊆ interior (S (y n)) := by
      intro y hy
      obtain ⟨z, hzX, hzto, hzeq⟩ := exists_seq_mem_of_tendsto_nhdsWithin hx hy
      have hSx := (svIscWithinAt_iff_forall_seq hx).1 h z hzX hzto
      have hstep := eventually_compact_subset_interior_innerSetLimit
        (fun n ↦ S (z n)) (fun n ↦ hconv (z n)) (isCompact_closedBall u r)
        (hB.trans (interior_mono hSx))
      filter_upwards [hstep, hzeq] with n hn heq
      rwa [heq] at hn
    have hev : ∀ᶠ x' in nhdsWithin x X, closedBall u r ⊆ S x' := by
      have hall : ∀ᶠ x' in nhdsWithin x X,
          closedBall u r ⊆ interior (S x') :=
        Filter.eventually_iff_seq_eventually.2 hseq
      filter_upwards [hall] with x' hx'
      exact hx'.trans interior_subset
    obtain ⟨V, hV, hVsub⟩ := eventually_nhdsWithin_iff_exists_nhds.1 hev
    refine ⟨V ×ˢ closedBall u r,
      prod_mem_nhds hV (closedBall_mem_nhds u hr), ?_⟩
    rintro ⟨x', u'⟩ ⟨⟨hx'V, hu'B⟩, hx'X, -⟩
    exact hVsub x' ⟨hx'X, hx'V⟩ hu'B
  · intro h
    have hsub : interior (S x) ⊆ svInnerLimitWithin S X x := by
      intro u hu
      obtain ⟨W, hW, hWsub⟩ := h u hu
      obtain ⟨V, hV, U, hU, hVU⟩ := mem_nhds_prod_iff.1 hW
      intro N hN
      have hmemX : ∀ᶠ x' in nhdsWithin x X, x' ∈ X :=
        Filter.eventually_mem_set.2 self_mem_nhdsWithin
      have hmemV : ∀ᶠ x' in nhdsWithin x X, x' ∈ V :=
        Filter.eventually_mem_set.2 (nhdsWithin_le_nhds hV)
      filter_upwards [hmemX, hmemV] with x' hx'X hx'V
      have hgr : (x', u) ∈ svGraph S :=
        hWsub ⟨hVU ⟨hx'V, mem_of_mem_nhds hU⟩, hx'X, mem_univ _⟩
      exact ⟨u, mem_svGraph.1 hgr, mem_of_mem_nhds hN⟩
    calc S x ⊆ closure (S x) := subset_closure
      _ = closure (interior (S x)) :=
          ((hconv x).closure_interior_eq_closure_of_nonempty_interior hne).symm
      _ ⊆ svInnerLimitWithin S X x :=
          closure_minimal hsub (isClosed_innerSetLimitAlong _ S)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Theorem 5.9(a)**, the book's principal form, taken relative to
`dom S`. -/
theorem svIscWithinAt_svDom_iff_of_convexValued {S : E → Set F} {x : E}
    (hconv : SvConvexValued S) (hne : (interior (S x)).Nonempty) :
    SvIscWithinAt S (svDom S) x ↔
      ∀ u ∈ interior (S x), ∃ W ∈ nhds (x, u),
        W ∩ (svDom S ×ˢ (univ : Set F)) ⊆ svGraph S :=
  svIscWithinAt_iff_of_convexValued (hne.mono interior_subset) hconv hne

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **Theorem 5.9(a)**, the "in particular" clause: inner semicontinuity at
`x` says that `gph S` has `(x, u)` in its interior for every interior image
point `u`. -/
theorem svIscAt_iff_of_convexValued {S : E → Set F} {x : E}
    (hconv : SvConvexValued S) (hne : (interior (S x)).Nonempty) :
    SvIscAt S x ↔ ∀ u ∈ interior (S x), (x, u) ∈ interior (svGraph S) := by
  rw [← svIscWithinAt_univ,
    svIscWithinAt_iff_of_convexValued (mem_univ x) hconv hne]
  refine forall_congr' fun u ↦ forall_congr' fun _ ↦ ?_
  constructor
  · rintro ⟨W, hW, hWsub⟩
    exact mem_interior_iff_mem_nhds.2
      (Filter.mem_of_superset hW fun p hp ↦ hWsub ⟨hp, mem_univ _, mem_univ _⟩)
  · intro hmem
    exact ⟨interior (svGraph S), isOpen_interior.mem_nhds hmem,
      fun _ hp ↦ interior_subset hp.1⟩

/-- **Theorem 5.9(b).**  A graph-convex mapping is inner semicontinuous at
every interior point of its domain.

Writing `S(x) = L⁻¹(x) ∩ gph S` for the projection `L : (x, u) ↦ x` turns the
claim into an inner-limit statement about intersections of convex sets, which
is 4.32(c).  The non-separation hypothesis it needs is exactly interiority of
`x` in `dom S`. -/
theorem SvGraphConvex.svIscAt {S : E → Set F} (h : SvGraphConvex S) {x : E}
    (hx : x ∈ interior (svDom S)) : SvIscAt S x := by
  rw [svIscAt_iff_forall_seq]
  intro y hy v hv
  set C₁ : ℕ → Set (E × F) := fun n ↦ ({y n} : Set E) ×ˢ (univ : Set F)
    with hC₁def
  set C₂ : ℕ → Set (E × F) := fun _ ↦ svGraph S with hC₂def
  have hC₁conv : ∀ n, Convex ℝ (C₁ n) := fun _ ↦
    (convex_singleton _).prod convex_univ
  have hC₂conv : ∀ n, Convex ℝ (C₂ n) := fun _ ↦ h
  -- Lower bounds on the two inner limits.
  have hfibre : ({x} : Set E) ×ˢ (univ : Set F) ⊆ innerSetLimit C₁ := by
    have hsing : innerSetLimit (fun n ↦ ({y n} : Set E)) = {x} :=
      (pkConverges_singleton_iff.2 hy).inner_eq
    have huniv : innerSetLimit (fun _ : ℕ ↦ (univ : Set F)) = univ := by
      rw [innerSetLimit_const (univ : Set F), closure_univ]
    have hstep := prod_innerSetLimit_subset (fun n ↦ ({y n} : Set E))
      (fun _ : ℕ ↦ (univ : Set F))
    rw [hsing, huniv] at hstep
    exact hstep
  have hgraph : svGraph S ⊆ innerSetLimit C₂ := by
    have hconst : innerSetLimit C₂ = closure (svGraph S) :=
      innerSetLimit_const (svGraph S)
    rw [hconst]
    exact subset_closure
  -- The non-separation hypothesis.
  have hnosep : CannotBeSeparated (innerSetLimit C₁) (innerSetLimit C₂) := by
    have hOopen : IsOpen ((fun d : E ↦ x - d) ⁻¹' interior (svDom S)) :=
      isOpen_interior.preimage (continuous_const.sub continuous_id)
    have hOzero : (0 : E) ∈ (fun d : E ↦ x - d) ⁻¹' interior (svDom S) := by
      simpa using hx
    have hincl :
        ((fun d : E ↦ x - d) ⁻¹' interior (svDom S)) ×ˢ (univ : Set F) ⊆
          innerSetLimit C₁ - innerSetLimit C₂ := by
      rintro ⟨p, q⟩ ⟨hp, -⟩
      obtain ⟨b, hb⟩ := interior_subset hp
      refine Set.mem_sub.2 ⟨(x, q + b), hfibre ⟨rfl, mem_univ _⟩, (x - p, b),
        hgraph hb, ?_⟩
      simp
    refine mem_interior_iff_mem_nhds.2
      (Filter.mem_of_superset ((hOopen.prod isOpen_univ).mem_nhds ?_) hincl)
    exact ⟨hOzero, mem_univ _⟩
  -- 4.32(c), then project onto the second factor.
  have key := inter_innerSetLimit_subset_of_cannotBeSeparated hC₁conv hC₂conv
    hnosep
  have hmem : (x, v) ∈ innerSetLimit fun n ↦ C₁ n ∩ C₂ n :=
    key ⟨hfibre ⟨rfl, mem_univ _⟩, hgraph hv⟩
  have hcap : (fun n ↦ C₁ n ∩ C₂ n) =
      fun n ↦ ({y n} : Set E) ×ˢ S (y n) := by
    funext n
    ext ⟨a, b⟩
    constructor
    · rintro ⟨⟨ha, -⟩, hb⟩
      rw [mem_singleton_iff] at ha
      subst ha
      exact ⟨rfl, hb⟩
    · rintro ⟨ha, hb⟩
      rw [mem_singleton_iff] at ha
      subst ha
      exact ⟨⟨rfl, mem_univ _⟩, hb⟩
  rw [hcap] at hmem
  exact snd_mem_innerSetLimit_of_mem_prod hmem

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Theorem 5.9(c).**  Inner semicontinuity is inherited by the convex-hull
mapping `x ↦ con S(x)`. -/
theorem SvIscAt.convexHull {S : E → Set F} {x : E} (h : SvIscAt S x) :
    SvIscAt (fun z ↦ convexHull ℝ (S z)) x := by
  rw [svIscAt_iff_forall_seq] at h ⊢
  intro y hy
  exact (convexHull_mono (h y hy)).trans
    (convexHull_innerSetLimit_subset fun n ↦ S (y n))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The relative form of 5.9(c). -/
theorem SvIscWithinAt.convexHull {S : E → Set F} {X : Set E} {x : E}
    (hx : x ∈ X) (h : SvIscWithinAt S X x) :
    SvIscWithinAt (fun z ↦ convexHull ℝ (S z)) X x := by
  rw [svIscWithinAt_iff_forall_seq hx] at h ⊢
  intro y hyX hy
  exact (convexHull_mono (h y hyX hy)).trans
    (convexHull_innerSetLimit_subset fun n ↦ S (y n))

end ConvexCriteria

end RW
