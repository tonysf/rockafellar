/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Michael Representations and Extensions of Selections

Theorem 5.58 asks for more than the single selection built in
`MichaelSelection.lean`.  It asks for a *Michael representation*: a countable
family `{sᵢ}` of selections, each continuous relative to `dom S`, with

    S(x) = cl {sᵢ(x) | i ∈ I}   for every x ∈ dom S.

Corollary 5.59 asks instead for a selection prescribed in advance on a closed
subset of the domain.  Both are Michael's theorem applied to a modified
mapping, and the modifications are what this file supplies.

Three of them are stated on their own, since each is used twice:

* `SvIsc.closure_inter_isOpen` -- trimming `S` by a fixed *open* set and
  closing up preserves inner semicontinuity.  The book cites 4.32(c); the
  direct argument is four lines and purely topological, needing no metric: a
  point of `cl(S(ȳ) ∩ O)` is approximated by a point `w' ∈ S(ȳ) ∩ O`, and
  `U ∩ O` is then a neighborhood of `w'` that inner semicontinuity of `S`
  carries into the nearby values.
* `svIsc_piecewise_singleton` -- pasting a continuous single-valued selection
  over a *closed* set `C` preserves inner semicontinuity.  At a point of `C`
  two eventualities combine: continuity of `σ` handles the nearby points of
  `C`, and inner semicontinuity of `S` at `σ(ȳ) ∈ S(ȳ)` handles the points
  outside it.  At a point off `C` the value is `S` throughout a whole
  neighborhood, which is where closedness of `C` is used.
* `exists_isClosed_seq_of_isOpen` -- an open set in a pseudometric space is
  the union of the closed inner shells `{y | 1/k ≤ d(y, Oᶜ)}`.  The book
  exhausts `S⁻¹(int IB(u, ρ))` by unions of rational balls shrunk by
  `1/(2k)²`, which is machinery it needs only because it is working with
  σ-compactness in `IRⁿ`.  The shells are written with `Metric.infEDist` so
  that `O = Y`, with empty complement and distance `∞`, needs no separate
  case -- the same reason `DistanceCriteria.lean` uses the extended distance.

The book's Part 5 is then `exists_selections_hitting_closure`, stated for one
open convex set `B` at a time: the trimmed mapping `cl(S(y) ∩ B)` is
nonempty-, closed- and convex-valued and isc on the open set `S⁻¹(B)`, so
Michael's theorem gives it a selection `σ` there; pasting `σ` over each shell
of `S⁻¹(B)` and applying Michael's theorem again turns `σ` into a countable
family of selections of `S` itself, one of which agrees with `σ` at any
prescribed point of `S⁻¹(B)`.  Running this along the countable family of
balls of `GenericContinuity.lean` -- centres in a countable dense set, radii
`1/(n+1)` -- gives the representation, since the values at `ȳ` of the
selections coming from a ball `B(d, r)` with `ū ∈ B(d, r)` and `r < ε` lie in
`IB(d, r)`, hence within `2ε` of `ū`.

Separability of the target is needed only here, for the countable family of
balls; the single selection of 5.58 does not use it.  As there, neither
σ-compactness of `dom S` nor finite-dimensionality appears.

**Corollary 5.59 is stated with closed-valuedness added.**  As printed it
assumes only convex-valuedness, but the mapping `S̄` its proof feeds to 5.58
takes the values of `S` off the prescribed set, and 5.58 needs those values
closed -- that is the one place in the whole construction where closedness is
used, and it is what puts the limit of the approximations *in* `S(y)` rather
than in its closure.
-/

import RockafellarWets.Chapter5.MichaelSelection
import RockafellarWets.Chapter5.GenericContinuity

open Filter Metric Set Topology

open scoped Set.Notation

namespace RW

section Composition

variable {Y Z F : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace F]

/-- Inner semicontinuity is preserved by precomposition with a continuous
single-valued map: the eventuality along `𝓝 (f z)` pulls back along `f`. -/
theorem SvIscAt.comp {S : Y → Set F} {f : Z → Y} {z : Z} (hS : SvIscAt S (f z))
    (hf : ContinuousAt f z) : SvIscAt (fun w ↦ S (f w)) z :=
  fun _ hu W hW ↦ hf.eventually (hS hu W hW)

/-- The everywhere form of `SvIscAt.comp`.  With `f = Subtype.val` it says
that an isc mapping stays isc when restricted to a subspace, which is how the
selection theorem is applied inside the open sets `S⁻¹(B)`. -/
theorem SvIsc.comp {S : Y → Set F} (hS : SvIsc S) {f : Z → Y} (hf : Continuous f) :
    SvIsc (fun w ↦ S (f w)) :=
  fun z ↦ (hS (f z)).comp hf.continuousAt

/-- Trimming an isc mapping by a fixed open set and taking closures leaves it
isc.  This is the step the book takes from 4.32(c).

Given `w ∈ cl(S(ȳ) ∩ O)` and a neighborhood `W ∋ w`, shrink `W` to an open
`U`; density supplies `w' ∈ S(ȳ) ∩ O ∩ U`, and `U ∩ O` is an open
neighborhood of `w'`, so inner semicontinuity of `S` puts a point
`v ∈ S(y) ∩ U ∩ O` in every nearby value.  That `v` lies in `S(y) ∩ O`, hence
in its closure, and in `U ⊂ W`.

At points where `S(ȳ) ∩ O` is empty the statement is vacuous, so no
hypothesis relating `O` to the domain is needed. -/
theorem SvIsc.closure_inter_isOpen {S : Y → Set F} (hisc : SvIsc S) {O : Set F}
    (hO : IsOpen O) : SvIsc (fun y ↦ closure (S y ∩ O)) := by
  intro y w hw W hW
  obtain ⟨U, hUW, hUopen, hwU⟩ := mem_nhds_iff.1 hW
  obtain ⟨w', hw'U, hw'S, hw'O⟩ := _root_.mem_closure_iff.1 hw U hUopen hwU
  filter_upwards [hisc y hw'S (U ∩ O)
    (Filter.inter_mem (hUopen.mem_nhds hw'U) (hO.mem_nhds hw'O))] with z hz
  obtain ⟨v, hvS, hvU, hvO⟩ := hz
  exact ⟨v, subset_closure ⟨hvS, hvO⟩, hUW hvU⟩

end Composition

section Gluing

variable {Y F : Type*} [TopologicalSpace Y] [TopologicalSpace F]

open Classical in
/-- Pasting a continuous selection over a closed set preserves inner
semicontinuity: if `σ` is continuous relative to a closed `C` with
`σ(y) ∈ S(y)` there, then the mapping equal to `{σ(y)}` on `C` and to `S(y)`
off it is isc wherever `S` is.

At `ȳ ∈ C` the only value to test is `σ(ȳ)`, and two eventualities cover the
nearby points: continuity of `σ` relative to `C` handles those in `C`, and
inner semicontinuity of `S` at `σ(ȳ) ∈ S(ȳ)` handles the rest.  At `ȳ ∉ C`
closedness of `C` gives a whole neighborhood missing `C`, on which the
mapping is `S` itself.

This is the modification behind both the Michael representation and 5.59; in
the first the pasted selection is the one built on `S⁻¹(B)`, in the second it
is the selection prescribed by hypothesis. -/
theorem svIsc_piecewise_singleton {S : Y → Set F} (hisc : SvIsc S) {C : Set Y}
    (hC : IsClosed C) {σ : Y → F} (hσ : ContinuousOn σ C)
    (hmem : ∀ y ∈ C, σ y ∈ S y) :
    SvIsc (fun y ↦ if y ∈ C then ({σ y} : Set F) else S y) := by
  intro y u hu W hW
  dsimp only at hu ⊢
  by_cases hyC : y ∈ C
  · rw [if_pos hyC, mem_singleton_iff] at hu
    subst hu
    have h1 : ∀ᶠ z in nhds y, z ∈ C → σ z ∈ W :=
      eventually_nhdsWithin_iff.1 (hσ y hyC hW)
    filter_upwards [h1, hisc y (hmem y hyC) W hW] with z hz1 hz2
    by_cases hzC : z ∈ C
    · exact ⟨σ z, by rw [if_pos hzC]; exact rfl, hz1 hzC⟩
    · rw [if_neg hzC]; exact hz2
  · rw [if_neg hyC] at hu
    filter_upwards [hC.isOpen_compl.mem_nhds hyC, hisc y hu W hW] with z hz1 hz2
    rw [if_neg hz1]; exact hz2

end Gluing

section Exhaustion

variable {Y : Type*} [PseudoMetricSpace Y]

/-- An open set in a pseudometric space is the union of the closed inner
shells `{y | 1/k ≤ d(y, Oᶜ)}`.

The extended distance is used so that `O = Y` -- empty complement, distance
`∞` -- is covered by the shell `k = 0` rather than needing a case of its own,
and a shell misses `Oᶜ` because the extended distance from a point of a set
to that set is `0` while `(k : ℝ≥0∞)⁻¹` is never `0`. -/
theorem exists_isClosed_seq_of_isOpen {O : Set Y} (hO : IsOpen O) :
    ∃ C : ℕ → Set Y, (∀ k, IsClosed (C k)) ∧ (∀ k, C k ⊆ O) ∧
      ∀ y ∈ O, ∃ k, y ∈ C k := by
  refine ⟨fun k ↦ {y : Y | (k : ENNReal)⁻¹ ≤ infEDist y Oᶜ}, fun k ↦ ?_,
    fun k y hy ↦ ?_, fun y hy ↦ ?_⟩
  · exact isClosed_le continuous_const continuous_infEDist
  · simp only [mem_setOf_eq] at hy
    by_contra hyO
    rw [infEDist_zero_of_mem (Set.mem_compl hyO), nonpos_iff_eq_zero,
      ENNReal.inv_eq_zero] at hy
    exact ENNReal.natCast_ne_top k hy
  · have hpos : infEDist y Oᶜ ≠ 0 := fun h ↦
      (hO.isClosed_compl.closure_eq ▸ mem_closure_iff_infEDist_zero.2 h) hy
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hpos
    exact ⟨k, hk.le⟩

end Exhaustion

section HittingSelections

variable {Y : Type*} [PseudoMetricSpace Y]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Theorem 5.58, Part 5**, at a single open convex set `B`: there is a
countable family of selections of `S`, one of which passes through
`cl(S(y) ∩ B)` at any prescribed `y` whose value meets `B`.

The trimmed mapping `y ↦ cl(S(y) ∩ B)` is nonempty-, closed- and
convex-valued on the open set `S⁻¹(B)` and isc there by
`SvIsc.closure_inter_isOpen` and `SvIsc.comp`, so Michael's theorem gives it
a continuous selection `σ` on `S⁻¹(B)`.  That `σ` is not yet a selection of
`S` on all of `Y`; pasting it over the `k`-th closed shell of `S⁻¹(B)` and
applying Michael's theorem to the pasted mapping produces one that is, and
that still agrees with `σ` on the shell.  Every point of `S⁻¹(B)` lies in
some shell, so some member of the family passes through `cl(S(y) ∩ B)`. -/
theorem exists_selections_hitting_closure {S : Y → Set F}
    (hne : ∀ y, (S y).Nonempty) (hclosed : ∀ y, IsClosed (S y))
    (hconv : ∀ y, Convex ℝ (S y)) (hisc : SvIsc S)
    {B : Set F} (hBopen : IsOpen B) (hBconv : Convex ℝ B) :
    ∃ f : ℕ → C(Y, F), (∀ k y, f k y ∈ S y) ∧
      ∀ y, (S y ∩ B).Nonempty → ∃ k, f k y ∈ closure (S y ∩ B) := by
  classical
  have hOopen : IsOpen (svPreimage S B) := svIsc_iff_isOpen_svPreimage.1 hisc B hBopen
  obtain ⟨σ, hσ⟩ : ∃ σ : C(svPreimage S B, F), ∀ y : svPreimage S B,
      σ y ∈ closure (S ↑y ∩ B) :=
    exists_continuous_selection (fun y ↦ (mem_svPreimage.1 y.2).mono subset_closure)
      (fun _ ↦ isClosed_closure) (fun y ↦ ((hconv _).inter hBconv).closure)
      ((hisc.closure_inter_isOpen hBopen).comp continuous_subtype_val)
  obtain ⟨τ, hτcont, hτeq⟩ := exists_continuousOn_restrict_eq σ
  have hτcl : ∀ y (h : y ∈ svPreimage S B), τ y ∈ closure (S y ∩ B) :=
    fun y h ↦ hτeq ⟨y, h⟩ ▸ hσ ⟨y, h⟩
  have hτS : ∀ y ∈ svPreimage S B, τ y ∈ S y := fun y h ↦ by
    rw [← (hclosed y).closure_eq]
    exact closure_mono inter_subset_left (hτcl y h)
  obtain ⟨C, hCclosed, hCsub, hCmem⟩ := exists_isClosed_seq_of_isOpen hOopen
  have hglue : ∀ k, ∃ s : C(Y, F),
      ∀ y, s y ∈ if y ∈ C k then ({τ y} : Set F) else S y := by
    intro k
    refine exists_continuous_selection ?_ ?_ ?_
      (svIsc_piecewise_singleton hisc (hCclosed k)
        (fun y hy ↦ (hτcont.continuousAt (hOopen.mem_nhds (hCsub k hy))).continuousWithinAt)
        (fun y hy ↦ hτS y (hCsub k hy)))
    · intro y
      by_cases h : y ∈ C k
      · rw [if_pos h]; exact singleton_nonempty _
      · rw [if_neg h]; exact hne y
    · intro y
      by_cases h : y ∈ C k
      · rw [if_pos h]; exact isClosed_singleton
      · rw [if_neg h]; exact hclosed y
    · intro y
      by_cases h : y ∈ C k
      · rw [if_pos h]; exact convex_singleton _
      · rw [if_neg h]; exact hconv y
  choose f hf using hglue
  refine ⟨f, fun k y ↦ ?_, fun y hy ↦ ?_⟩
  · have h := hf k y
    by_cases hyC : y ∈ C k
    · rw [if_pos hyC, mem_singleton_iff] at h
      rw [h]
      exact hτS y (hCsub k hyC)
    · rwa [if_neg hyC] at h
  · obtain ⟨k, hk⟩ := hCmem y hy
    have h := hf k y
    rw [if_pos hk, mem_singleton_iff] at h
    exact ⟨k, h ▸ hτcl y (hCsub k hk)⟩

end HittingSelections

section Representation

variable {Y : Type*} [PseudoMetricSpace Y]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [TopologicalSpace.SeparableSpace F]

/-- **Theorem 5.58**, the Michael representation, on a pseudometric domain: an
isc mapping with nonempty closed convex values admits a countable family of
continuous selections whose values at each point are dense in that point's
image.

The family is `exists_selections_hitting_closure` run along the countable
ball family of 5.55: centres in a countable dense subset of the target, radii
`1/(n+1)`.  Given `ū ∈ S(ȳ)` and `ε > 0`, `exists_ball_closedBall_subset`
supplies a ball with `ū ∈ B(d, r)` and `IB(d, r) ⊂ B(ū, ε)`; the value of
`S` at `ȳ` meets `B(d, r)`, so some selection of that ball's family has
`s(ȳ) ∈ cl(S(ȳ) ∩ B(d, r)) ⊂ IB(d, r) ⊂ B(ū, ε)`.

Separability of the target is used only for this countable ball family. -/
theorem exists_countable_dense_selections {S : Y → Set F}
    (hne : ∀ y, (S y).Nonempty) (hclosed : ∀ y, IsClosed (S y))
    (hconv : ∀ y, Convex ℝ (S y)) (hisc : SvIsc S) :
    ∃ 𝒮 : Set C(Y, F), 𝒮.Countable ∧ (∀ s ∈ 𝒮, ∀ y, s y ∈ S y) ∧
      ∀ y, closure ((fun s : C(Y, F) ↦ s y) '' 𝒮) = S y := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense F
  have hDc : Countable D := hDcount.to_subtype
  choose f hfS hfhit using fun q : D × ℕ ↦
    exists_selections_hitting_closure (B := ball (q.1 : F) ((q.2 : ℝ) + 1)⁻¹)
      hne hclosed hconv hisc isOpen_ball (convex_ball _ _)
  refine ⟨range fun p : (D × ℕ) × ℕ ↦ f p.1 p.2, countable_range _, ?_, fun y ↦ ?_⟩
  · rintro s ⟨p, rfl⟩ y
    exact hfS p.1 p.2 y
  refine Subset.antisymm ((hclosed y).closure_subset_iff.2 ?_) fun u hu ↦ ?_
  · rintro u ⟨s, ⟨p, rfl⟩, rfl⟩
    exact hfS p.1 p.2 y
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  obtain ⟨d, hdD, n, hud, hballsub⟩ :=
    exists_ball_closedBall_subset hDdense (ball_mem_nhds u hε)
  obtain ⟨k, hk⟩ := hfhit (⟨d, hdD⟩, n) y ⟨u, hu, hud⟩
  refine ⟨f (⟨d, hdD⟩, n) k y,
    mem_image_of_mem _ (mem_range_self (((⟨d, hdD⟩ : D), n), k)), ?_⟩
  have h2 : closure (S y ∩ ball (d : F) ((n : ℝ) + 1)⁻¹)
      ⊆ closedBall d ((n : ℝ) + 1)⁻¹ :=
    (closure_mono inter_subset_right).trans closure_ball_subset_closedBall
  exact mem_ball'.1 (hballsub (h2 hk))

end Representation

section RelativeForm

variable {E : Type*} [PseudoMetricSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section Michael

variable [TopologicalSpace.SeparableSpace F]

/-- **Theorem 5.58** in the book's relative phrasing: a mapping isc relative
to `X` with nonempty closed convex values on `X` admits a countable family of
selections continuous relative to `X` whose values are dense in every image.

This is `exists_countable_dense_selections` on the subspace `↥X`, transported
by `svIsc_subtype_iff` and `exists_continuousOn_restrict_eq`. -/
theorem exists_countable_michael_representation {S : E → Set F} {X : Set E}
    (hne : ∀ x ∈ X, (S x).Nonempty) (hclosed : ∀ x ∈ X, IsClosed (S x))
    (hconv : ∀ x ∈ X, Convex ℝ (S x)) (hisc : SvIscOn S X) :
    ∃ 𝒮 : Set (E → F), 𝒮.Countable ∧
      (∀ s ∈ 𝒮, ContinuousOn s X ∧ ∀ x ∈ X, s x ∈ S x) ∧
      ∀ x ∈ X, closure ((fun s : E → F ↦ s x) '' 𝒮) = S x := by
  classical
  obtain ⟨𝒮, hcount, hmem, hdense⟩ := exists_countable_dense_selections
    (S := fun y : X ↦ S ↑y) (fun y ↦ hne y y.2) (fun y ↦ hclosed y y.2)
    (fun y ↦ hconv y y.2) (svIsc_subtype_iff.2 hisc)
  choose ext hextcont hexteq using fun σ : C(X, F) ↦ exists_continuousOn_restrict_eq σ
  refine ⟨ext '' 𝒮, hcount.image _, ?_, fun x hx ↦ ?_⟩
  · rintro s ⟨σ, hσ, rfl⟩
    exact ⟨hextcont σ, fun x hx ↦ hexteq σ ⟨x, hx⟩ ▸ hmem σ hσ ⟨x, hx⟩⟩
  have himg : (fun s : E → F ↦ s x) '' (ext '' 𝒮)
      = (fun σ : C(X, F) ↦ σ ⟨x, hx⟩) '' 𝒮 := by
    rw [← image_comp]
    exact image_congr fun σ _ ↦ hexteq σ ⟨x, hx⟩
  rw [himg]
  exact hdense ⟨x, hx⟩

/-- **Theorem 5.58** as printed, with `X = dom S`: nonemptiness of the values
is then automatic. -/
theorem exists_countable_michael_representation_svDom {S : E → Set F}
    (hclosed : ∀ x ∈ svDom S, IsClosed (S x))
    (hconv : ∀ x ∈ svDom S, Convex ℝ (S x)) (hisc : SvIscOn S (svDom S)) :
    ∃ 𝒮 : Set (E → F), 𝒮.Countable ∧
      (∀ s ∈ 𝒮, ContinuousOn s (svDom S) ∧ ∀ x ∈ svDom S, s x ∈ S x) ∧
      ∀ x ∈ svDom S, closure ((fun s : E → F ↦ s x) '' 𝒮) = S x :=
  exists_countable_michael_representation (fun _ hx ↦ hx) hclosed hconv hisc

end Michael

/-- **Corollary 5.59**, relative to a general set `X`: a selection continuous
relative to a closed `X₀ ⊂ X` extends to a selection continuous relative to
the whole of `X`.

The mapping `S̄(x) = {s̄(x)}` on `X₀` and `S(x)` elsewhere is isc relative to
`X` by `svIsc_piecewise_singleton` and has nonempty closed convex values, so
5.58 supplies a continuous selection of it -- which is a selection of `S`
agreeing with `s̄` on `X₀`.  No countable family is involved, so separability
of the target is not needed.

**Closed-valuedness is an added hypothesis.**  The printed statement assumes
only convex-valuedness; but `S̄` takes the values of `S` off `X₀`, and the
theorem it is fed to needs those closed.  Michael's theorem uses closedness
exactly once, to put the limit of its approximations in `S(x)` rather than in
`cl S(x)`, and nothing about `S̄` recovers it. -/
theorem exists_continuousOn_selection_extension {S : E → Set F} {X X₀ : Set E}
    (hne : ∀ x ∈ X, (S x).Nonempty) (hclosed : ∀ x ∈ X, IsClosed (S x))
    (hconv : ∀ x ∈ X, Convex ℝ (S x)) (hisc : SvIscOn S X)
    (hX₀ : IsClosed X₀) (hX₀sub : X₀ ⊆ X) {s₀ : E → F} (hs₀ : ContinuousOn s₀ X₀)
    (hs₀mem : ∀ x ∈ X₀, s₀ x ∈ S x) :
    ∃ s : E → F, ContinuousOn s X ∧ (∀ x ∈ X, s x ∈ S x) ∧ ∀ x ∈ X₀, s x = s₀ x := by
  classical
  have hCclosed : IsClosed (X ↓∩ X₀) := hX₀.preimage continuous_subtype_val
  have hσcont : ContinuousOn (fun y : X ↦ s₀ ↑y) (X ↓∩ X₀) := fun y hy ↦
    (hs₀ ↑y hy).comp continuous_subtype_val.continuousWithinAt fun _ hz ↦ hz
  obtain ⟨σ, hσ⟩ := exists_continuous_selection
    (S := fun y : X ↦ if y ∈ X ↓∩ X₀ then ({s₀ ↑y} : Set F) else S ↑y)
    (fun y ↦ by
      dsimp only
      by_cases h : y ∈ X ↓∩ X₀
      · rw [if_pos h]; exact singleton_nonempty _
      · rw [if_neg h]; exact hne _ y.2)
    (fun y ↦ by
      dsimp only
      by_cases h : y ∈ X ↓∩ X₀
      · rw [if_pos h]; exact isClosed_singleton
      · rw [if_neg h]; exact hclosed _ y.2)
    (fun y ↦ by
      dsimp only
      by_cases h : y ∈ X ↓∩ X₀
      · rw [if_pos h]; exact convex_singleton _
      · rw [if_neg h]; exact hconv _ y.2)
    (svIsc_piecewise_singleton (svIsc_subtype_iff.2 hisc) hCclosed hσcont
      fun y hy ↦ hs₀mem ↑y hy)
  have hσmem : ∀ y : X, σ y ∈ S ↑y := by
    intro y
    have h := hσ y
    by_cases hy : y ∈ X ↓∩ X₀
    · rw [if_pos hy, mem_singleton_iff] at h
      rw [h]
      exact hs₀mem ↑y hy
    · rwa [if_neg hy] at h
  obtain ⟨s, hscont, hseq⟩ := exists_continuousOn_restrict_eq σ
  refine ⟨s, hscont, fun x hx ↦ hseq ⟨x, hx⟩ ▸ hσmem ⟨x, hx⟩, fun x hx ↦ ?_⟩
  have h := hσ ⟨x, hX₀sub hx⟩
  rw [if_pos (show (⟨x, hX₀sub hx⟩ : X) ∈ X ↓∩ X₀ from hx), mem_singleton_iff] at h
  rw [hseq ⟨x, hX₀sub hx⟩, h]

/-- **Corollary 5.59** as printed, with `X = dom S`. -/
theorem exists_continuousOn_selection_extension_svDom {S : E → Set F} {X₀ : Set E}
    (hclosed : ∀ x ∈ svDom S, IsClosed (S x))
    (hconv : ∀ x ∈ svDom S, Convex ℝ (S x)) (hisc : SvIscOn S (svDom S))
    (hX₀ : IsClosed X₀) (hX₀sub : X₀ ⊆ svDom S) {s₀ : E → F}
    (hs₀ : ContinuousOn s₀ X₀) (hs₀mem : ∀ x ∈ X₀, s₀ x ∈ S x) :
    ∃ s : E → F, ContinuousOn s (svDom S) ∧ (∀ x ∈ svDom S, s x ∈ S x) ∧
      ∀ x ∈ X₀, s x = s₀ x :=
  exists_continuousOn_selection_extension (fun _ hx ↦ hx) hclosed hconv hisc hX₀
    hX₀sub hs₀ hs₀mem

end RelativeForm

end RW
