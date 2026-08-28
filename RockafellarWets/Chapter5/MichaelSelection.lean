/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Michael's Selection Theorem

Theorem 5.58 says that an inner semicontinuous closed-convex-valued mapping
has a continuous selection, and in fact a countable family of them whose
values are dense in every image.  This file builds the selection; the
countable family is `MichaelRepresentation.lean`.

The book's proof has five parts.  Parts 1 and 4 -- a partition of unity
subordinate to a locally finite refinement, first on a compact set and then on
a σ-compact one -- are already in Mathlib, in a form that is both shorter and
more general than the book's:
`exists_continuous_forall_mem_convex_of_local_const` produces a continuous
`g` with `g(y) ∈ t(y)` for any convex-valued `t` admitting a locally constant
witness, over any normal paracompact domain.  Stone's theorem makes every
pseudometric space paracompact, so **σ-compactness of `dom S` is never
needed**; it is what the book assumes in order to run the construction by
hand.

What remains is the book's Parts 2 and 3, here in the order

* `exists_continuous_approx_selection` -- for each `η > 0` a continuous
  `η`-approximate selection, obtained from the Mathlib lemma with
  `t(y) = S(y) + ηB`, whose locally constant witness at `ȳ` is *any* point of
  `S(ȳ)`.  This costs no compactness at all, where the book has it only on a
  compact `X`, and it uses neither closed-valuedness nor completeness;
* `SvIsc.inter_ball` -- the refinement `S(y) ∩ B(f(y), ρ)` by a moving *open*
  ball is again isc.  The book cites 4.32 and 5.24 for this; the direct
  argument below is shorter and needs neither.  The ball must be open: the
  slack `ρ - d(w, f(ȳ))` at an interior point is what absorbs the motion of
  the centre, which is also why the iteration is phrased with open balls
  rather than the book's `sν(x) + 2⁻ᵛIB`;
* `exists_continuous_selection` -- the iteration.  Approximating to within
  `2⁻ᵛ`, refining by the ball of that radius about the approximation, and
  approximating the refinement to within `2⁻⁽ᵛ⁺¹⁾` makes the successive
  approximations `3·2⁻⁽ᵛ⁺¹⁾`-close, uniformly in `y`, which is exactly the
  geometric Cauchy bound of `cauchySeq_of_le_geometric_two`.  The limit is
  continuous because the bound is uniform, and it lands *in* `S(y)` rather
  than in its closure because the values are closed -- the one and only use
  of closed-valuedness in the whole construction.

Finite-dimensionality is not needed either: a Banach target suffices for the
selection.  The results are stated over a normal paracompact domain and a
Banach target, and then transported to the book's `X ⊂ IRⁿ` through the
Section J convention that the relative topology on `X` is the subspace
topology on `↥X`, for which `svIsc_subtype_iff` is the dictionary.
-/

import RockafellarWets.Chapter5.ContinuousSelections
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Analysis.Normed.Module.Convex

open Filter Metric Set Topology

open scoped Pointwise

namespace RW

section ApproximateSelections

variable {Y : Type*} [TopologicalSpace Y] [NormalSpace Y] [ParacompactSpace Y]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Theorem 5.58, Part 2**: an isc mapping with nonempty convex values has,
for every `η > 0`, a continuous `η`-approximate selection -- a continuous `g`
with `S(y) ∩ B(g(y), η) ≠ ∅` at every `y`.

The mapping `t(y) := S(y) + ηB` is convex-valued, and at `ȳ` *any* point
`c ∈ S(ȳ)` is a locally constant witness for it: inner semicontinuity applied
to the neighborhood `B(c, η)` of `c` says that `S(y)` meets `B(c, η)` for all
nearby `y`, which is exactly `c ∈ t(y)`.  Mathlib's partition-of-unity lemma
then supplies the continuous `g`.

The book obtains this only on a compact `X`, by way of its own Part 1.  Here
there is no compactness, no closed-valuedness and no completeness; the domain
need only be normal and paracompact. -/
theorem exists_continuous_approx_selection {S : Y → Set F}
    (hne : ∀ y, (S y).Nonempty) (hconv : ∀ y, Convex ℝ (S y))
    (hisc : SvIsc S) {η : ℝ} (hη : 0 < η) :
    ∃ g : C(Y, F), ∀ y, (S y ∩ ball (g y) η).Nonempty := by
  set t : Y → Set F := fun y ↦ S y + ball (0 : F) η with ht_def
  have ht : ∀ y, Convex ℝ (t y) := fun y ↦ (hconv y).add (convex_ball _ _)
  have H : ∀ y : Y, ∃ c : F, ∀ᶠ z in nhds y, c ∈ t z := by
    intro y
    obtain ⟨c, hc⟩ := hne y
    refine ⟨c, ?_⟩
    filter_upwards [hisc y hc (ball c η) (ball_mem_nhds c hη)] with z hz
    obtain ⟨w, hwS, hwball⟩ := hz
    exact ⟨w, hwS, c - w, by
      simpa [mem_ball, dist_eq_norm, norm_sub_rev] using mem_ball.1 hwball, by abel_nf⟩
  obtain ⟨g, hg⟩ := exists_continuous_forall_mem_convex_of_local_const ht H
  refine ⟨g, fun y ↦ ?_⟩
  obtain ⟨w, hwS, v, hvball, hwv⟩ := hg y
  exact ⟨w, hwS, by
    rw [mem_ball, dist_eq_norm, ← hwv]
    simpa [norm_sub_rev] using mem_ball.1 hvball⟩

end ApproximateSelections

section MovingBall

variable {Y : Type*} [TopologicalSpace Y]
variable {F : Type*} [PseudoMetricSpace F]

/-- The refinement of an isc mapping by a moving *open* ball is again isc.

At `ȳ` a point `w ∈ S(ȳ) ∩ B(f(ȳ), ρ)` has slack `δ := ρ - d(w, f(ȳ)) > 0`.
Continuity of `f` moves the centre by less than `δ/2`, and inner
semicontinuity of `S` applied to `W ∩ B(w, δ/2)` produces, for nearby `y`, a
point `v ∈ S(y) ∩ W` within `δ/2` of `w`; then

    d(v, f(y)) ≤ d(v, w) + d(w, f(ȳ)) + d(f(ȳ), f(y)) < δ/2 + (ρ - δ) + δ/2 = ρ.

The book cites 4.32 and 5.24 for this step.  Openness of the ball is
essential -- with a closed ball the slack can be `0` and nothing is left to
absorb the motion of the centre. -/
theorem SvIsc.inter_ball {S : Y → Set F} (hisc : SvIsc S) {f : Y → F}
    (hf : Continuous f) {ρ : ℝ} : SvIsc (fun y ↦ S y ∩ ball (f y) ρ) := by
  intro y w hw W hW
  obtain ⟨hwS, hwB⟩ := hw
  have hδpos : 0 < ρ - dist w (f y) := sub_pos.2 (mem_ball.1 hwB)
  have h1 : ∀ᶠ z in nhds y, dist (f z) (f y) < (ρ - dist w (f y)) / 2 :=
    Metric.tendsto_nhds.1 hf.continuousAt _ (by linarith)
  have h2 := hisc y hwS (W ∩ ball w ((ρ - dist w (f y)) / 2))
    (Filter.inter_mem hW (ball_mem_nhds w (by linarith)))
  filter_upwards [h1, h2] with z hz1 hz2
  obtain ⟨v, hvS, hvW, hvb⟩ := hz2
  refine ⟨v, ⟨hvS, ?_⟩, hvW⟩
  have e1 : dist v w < (ρ - dist w (f y)) / 2 := mem_ball.1 hvb
  have e3 : dist (f y) (f z) < (ρ - dist w (f y)) / 2 := by rwa [dist_comm] at hz1
  have e4 : dist v (f z) ≤ dist v w + dist w (f y) + dist (f y) (f z) :=
    dist_triangle4 _ _ _ _
  exact mem_ball.2 (by linarith)

end MovingBall

section ExactSelection

variable {Y : Type*} [TopologicalSpace Y] [NormalSpace Y] [ParacompactSpace Y]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Theorem 5.58, Part 3** -- Michael's selection theorem.  An isc mapping
with nonempty closed convex values over a normal paracompact domain has a
continuous selection.

The approximations of Part 2 are iterated: `s₀` is `1`-approximate, and given
a `2⁻ᵛ`-approximate `sν` the refinement `S(y) ∩ B(sν(y), 2⁻ᵛ)` is nonempty-,
convex- and (by `SvIsc.inter_ball`) inner-semicontinuous-valued, so Part 2
applied to *it* with `η = 2⁻⁽ᵛ⁺¹⁾` yields a `2⁻⁽ᵛ⁺¹⁾`-approximate `sν₊₁`
which is also within `2⁻⁽ᵛ⁺¹⁾ + 2⁻ᵛ = 3·2⁻⁽ᵛ⁺¹⁾` of `sν`, uniformly in `y`.
That bound is the hypothesis of `cauchySeq_of_le_geometric_two`, so each
`sν(y)` converges; the limit is uniform, hence continuous, and lies within
`3·2⁻ᵛ + 2⁻ᵛ` of `S(y)` for every `ν`.

Closed-valuedness enters exactly once, at that last step. -/
theorem exists_continuous_selection {S : Y → Set F}
    (hne : ∀ y, (S y).Nonempty) (hclosed : ∀ y, IsClosed (S y))
    (hconv : ∀ y, Convex ℝ (S y)) (hisc : SvIsc S) :
    ∃ s : C(Y, F), ∀ y, s y ∈ S y := by
  classical
  have hrpos : ∀ n : ℕ, (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := fun n ↦ by positivity
  obtain ⟨f₀, hf₀⟩ := exists_continuous_approx_selection hne hconv hisc one_pos
  have step : ∀ (n : ℕ) (f : C(Y, F)),
      (∀ y, (S y ∩ ball (f y) ((2 : ℝ) ^ n)⁻¹).Nonempty) →
      ∃ f' : C(Y, F), (∀ y, (S y ∩ ball (f' y) ((2 : ℝ) ^ (n + 1))⁻¹).Nonempty) ∧
        ∀ y, dist (f' y) (f y) ≤ 3 / 2 / 2 ^ n := by
    intro n f hf
    obtain ⟨f', hf'⟩ := exists_continuous_approx_selection
      (S := fun y ↦ S y ∩ ball (f y) ((2 : ℝ) ^ n)⁻¹)
      hf (fun y ↦ (hconv y).inter (convex_ball _ _))
      (hisc.inter_ball f.continuous) (hrpos (n + 1))
    refine ⟨f', fun y ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨v, hv1, hv2⟩ := hf' y
      exact ⟨v, hv1.1, hv2⟩
    · obtain ⟨v, hv1, hv2⟩ := hf' y
      have h1 : dist v (f' y) < ((2 : ℝ) ^ (n + 1))⁻¹ := mem_ball.1 hv2
      have h2 : dist v (f y) < ((2 : ℝ) ^ n)⁻¹ := mem_ball.1 hv1.2
      have h3 : dist (f' y) (f y) ≤ dist (f' y) v + dist v (f y) := dist_triangle _ _ _
      have h4 : ((2 : ℝ) ^ (n + 1))⁻¹ = ((2 : ℝ) ^ n)⁻¹ / 2 := by
        rw [pow_succ]; field_simp
      have h5 : dist (f' y) v = dist v (f' y) := dist_comm _ _
      have h6 : (3 : ℝ) / 2 / 2 ^ n = ((2 : ℝ) ^ n)⁻¹ / 2 + ((2 : ℝ) ^ n)⁻¹ := by
        field_simp; ring
      rw [h6]
      linarith
  choose! nxt hnxt1 hnxt2 using step
  set g : ℕ → C(Y, F) := fun n ↦ Nat.rec f₀ (fun k fk ↦ nxt k fk) n with hgdef
  have hgP : ∀ n y, (S y ∩ ball (g n y) ((2 : ℝ) ^ n)⁻¹).Nonempty := by
    intro n
    induction n with
    | zero => simpa using hf₀
    | succ k ih => exact hnxt1 k (g k) ih
  have hgd : ∀ n y, dist (g n y) (g (n + 1) y) ≤ 3 / 2 / 2 ^ n := fun n y ↦ by
    rw [dist_comm]; exact hnxt2 n (g n) (hgP n) y
  have hcauchy : ∀ y, CauchySeq fun n ↦ g n y :=
    fun y ↦ cauchySeq_of_le_geometric_two (fun n ↦ hgd n y)
  choose s hs using fun y ↦ cauchySeq_tendsto_of_complete (hcauchy y)
  have hbound : ∀ n y, dist (g n y) (s y) ≤ 3 / 2 ^ n :=
    fun n y ↦ dist_le_of_le_geometric_two_of_tendsto (fun m ↦ hgd m y) (hs y) n
  -- The bound does not depend on `y`, so the convergence is uniform.
  have hunif : TendstoUniformly (fun n y ↦ g n y) s atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < ε / 3) one_half_lt_one
    filter_upwards [eventually_ge_atTop N] with n hn y
    have h1 : (3 : ℝ) / 2 ^ n ≤ 3 / 2 ^ N := by
      gcongr
      norm_num
    have h2 : ((1 : ℝ) / 2) ^ N = ((2 : ℝ) ^ N)⁻¹ := by
      rw [div_pow, one_pow, one_div]
    have h3 : (3 : ℝ) / 2 ^ N < ε := by
      rw [h2] at hN
      rw [div_eq_mul_inv]
      linarith
    calc dist (s y) (g n y) = dist (g n y) (s y) := dist_comm _ _
      _ ≤ 3 / 2 ^ n := hbound n y
      _ < ε := lt_of_le_of_lt h1 h3
  -- Closed-valuedness is used here, and nowhere else in the construction.
  have hmem : ∀ y, s y ∈ S y := by
    intro y
    rw [← (hclosed y).closure_eq]
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < ε / 4) one_half_lt_one
    obtain ⟨v, hvS, hvb⟩ := hgP N y
    refine ⟨v, hvS, ?_⟩
    have h1 : dist (s y) (g N y) ≤ 3 / 2 ^ N := by rw [dist_comm]; exact hbound N y
    have h2 : dist (g N y) v < ((2 : ℝ) ^ N)⁻¹ := by rw [dist_comm]; exact mem_ball.1 hvb
    have h3 : dist (s y) v ≤ dist (s y) (g N y) + dist (g N y) v := dist_triangle _ _ _
    have h4 : ((1 : ℝ) / 2) ^ N = ((2 : ℝ) ^ N)⁻¹ := by rw [div_pow, one_pow, one_div]
    have h5 : (3 : ℝ) / 2 ^ N = 3 * ((2 : ℝ) ^ N)⁻¹ := by rw [div_eq_mul_inv]
    rw [h4] at hN
    linarith
  exact ⟨⟨s, hunif.continuous (.of_forall fun n ↦ (g n).continuous)⟩, hmem⟩

end ExactSelection

section RelativeForm

variable {E : Type*} [PseudoMetricSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- A continuous map on the subspace `↥X` is the restriction of a function on
the whole space that is continuous relative to `X`.  This is what carries the
constructions above, which live on `↥X`, back to the book's phrasing in terms
of `ContinuousOn`. -/
theorem exists_continuousOn_restrict_eq {X : Set E} (σ : C(X, F)) :
    ∃ s : E → F, ContinuousOn s X ∧ ∀ y : X, s ↑y = σ y := by
  classical
  refine ⟨fun z ↦ if h : z ∈ X then σ ⟨z, h⟩ else 0, ?_, fun y ↦ dif_pos y.2⟩
  have hres : X.restrict (fun z ↦ if h : z ∈ X then σ ⟨z, h⟩ else 0) = σ :=
    funext fun y ↦ dif_pos y.2
  rw [continuousOn_iff_continuous_restrict, hres]
  exact σ.continuous

/-- **Theorem 5.58**, first assertion, in the book's relative phrasing: a
mapping isc relative to `X` with nonempty closed convex values on `X` has a
selection continuous relative to `X`.

Neither σ-compactness of `X` nor finite-dimensionality appears: the subspace
`↥X` of a pseudometric space is normal and paracompact by Stone's theorem,
and a Banach target suffices. -/
theorem exists_continuousOn_selection_of_svIscOn {S : E → Set F} {X : Set E}
    (hne : ∀ x ∈ X, (S x).Nonempty) (hclosed : ∀ x ∈ X, IsClosed (S x))
    (hconv : ∀ x ∈ X, Convex ℝ (S x)) (hisc : SvIscOn S X) :
    ∃ s : E → F, ContinuousOn s X ∧ ∀ x ∈ X, s x ∈ S x := by
  obtain ⟨σ, hσ⟩ := exists_continuous_selection (S := fun y : X ↦ S ↑y)
    (fun y ↦ hne y y.2) (fun y ↦ hclosed y y.2) (fun y ↦ hconv y y.2)
    (svIsc_subtype_iff.2 hisc)
  obtain ⟨s, hscont, hseq⟩ := exists_continuousOn_restrict_eq σ
  exact ⟨s, hscont, fun x hx ↦ hseq ⟨x, hx⟩ ▸ hσ ⟨x, hx⟩⟩

/-- **Theorem 5.58**, first assertion, as printed, with `X = dom S`:
nonemptiness of the values is then automatic. -/
theorem exists_continuousOn_svDom_selection {S : E → Set F}
    (hclosed : ∀ x ∈ svDom S, IsClosed (S x))
    (hconv : ∀ x ∈ svDom S, Convex ℝ (S x)) (hisc : SvIscOn S (svDom S)) :
    ∃ s : E → F, ContinuousOn s (svDom S) ∧ ∀ x ∈ svDom S, s x ∈ S x :=
  exists_continuousOn_selection_of_svIscOn (fun _ hx ↦ hx) hclosed hconv hisc

end RelativeForm

end RW
