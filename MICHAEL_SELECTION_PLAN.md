# Plan: Theorem 5.58 and Corollary 5.59 (Michael selections)

This is the plan for the last two unproved results of Chapter 5 Section J.
Everything asserted below as "verified" was compiled against this repository's
toolchain before the plan was written; the probe files are reproduced inline so
they can be pasted straight into a scratch file.

Delete this file once 5.58 and 5.59 are in the ledger.

## The headline finding

**Mathlib already has the analytic core of Michael's theorem.** It is not
called that, which is why a name-based search reports it missing:

```
Mathlib/Analysis/Convex/PartitionOfUnity.lean
  exists_continuous_forall_mem_convex_of_local_const
    (ht : ∀ x, Convex ℝ (t x)) (H : ∀ x : X, ∃ c : E, ∀ᶠ y in 𝓝 x, c ∈ t y) :
    ∃ g : C(X, E), ∀ x, g x ∈ t x
```

for `X` a normal paracompact space and `E` a topological real vector space.
That single lemma discharges **Parts 1 and 4** of the book's proof — the whole
partition-of-unity construction, the local finiteness, and the passage from
compact to σ-compact — and it does so in more generality than the book states.

Consequently this is not the from-scratch build the project memory assumed. The
remaining work is the book's Parts 2, 3 and 5, plus 5.59.

## Typeclass setting

```lean
variable {E : Type*} [PseudoMetricSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
```

with `[SeparableSpace F]` added only for the Michael representation (Part D),
never for the plain selection.

Verified: for `X : Set E` with `E` a pseudometric space, `↥X` gets
`NormalSpace` and `ParacompactSpace` automatically, and so does `↥O` for
`O : Set ↥X` — which Part D needs, since it recurses one subtype deeper.

```lean
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.ContinuousMap.Bounded.Basic

example {E : Type*} [PseudoMetricSpace E] (X : Set E) : NormalSpace X := by infer_instance
example {E : Type*} [PseudoMetricSpace E] (X : Set E) : ParacompactSpace X := by infer_instance
example {E : Type*} [PseudoMetricSpace E] (X : Set E) (O : Set X) :
    ParacompactSpace O := by infer_instance
```

**Gotcha, already paid for once.** `ParacompactSpace ↥X` does *not* resolve
from `Mathlib.Analysis.Convex.PartitionOfUnity` alone. The instance lives in
`Mathlib/Topology/EMetricSpace/Paracompact.lean`, which that file does not
import. Import it explicitly. Likewise `convex_ball` needs
`Mathlib.Analysis.Normed.Module.Convex`, and pointwise `+` on sets needs
`open scoped Pointwise`.

## Work in the subtype throughout

Section J's recorded convention (see the `CHAPTER5_COVERAGE.md` preamble) is
that relative topology on `X` is the subspace topology on `↥X`. Follow it here:
the construction is much cleaner as a statement about `S' : ↥X → Set F`,
`S' y = S ↑y`, with `SvIsc S'` absolute, than as `SvIscOn S X` with
`ContinuousOn`/`WithinAt` bookkeeping at every step.

**First deliverable — the bridge lemma**, next to the ones added for 5.55 in
`Chapter5/SemicontinuityCriteria.lean`:

```lean
theorem svIscAt_subtype_iff {S : E → Set F} {X : Set E} {x : E} (hx : x ∈ X) :
    SvIscAt (fun y : X ↦ S ↑y) ⟨x, hx⟩ ↔ SvIscWithinAt S X x
```

and the `SvOsc` counterpart if a proof wants it. Both come straight out of
`preimage_val_mem_nhds_iff`, which is already in that file. Convert once at the
top of 5.58 and once at the bottom, and convert the finished selection back to
the project's `ContinuousOn s X` form with `continuousOn_iff_continuous_restrict`
so that 5.58 reads like 5.57.

## Part A — approximate selections (book Part 2). VERIFIED, compiles today

For each `η > 0` an isc convex-valued mapping has a continuous `η`-approximate
selection, **with no compactness anywhere** — the book gets this only on a
compact `X`.

Take `t y := S y + B(0, η)`, convex as a sum of convex sets. For the local
constant at `x` take any `c ∈ S x`: inner semicontinuity applied to `B(c, η)`
says `S y` meets `B(c, η)` eventually, which is exactly `c ∈ t y`. Feed that to
`exists_continuous_forall_mem_convex_of_local_const`.

This compiles as written (one `abel_nf` hint to tidy):

```lean
theorem exists_continuous_approx_selection {S : E → Set F} {X : Set E}
    (hne : ∀ x ∈ X, (S x).Nonempty) (hconv : ∀ x ∈ X, Convex ℝ (S x))
    (hisc : SvIscOn S X) {η : ℝ} (hη : 0 < η) :
    ∃ g : C(X, F), ∀ x : X, (S x ∩ ball (g x) η).Nonempty := by
  set t : X → Set F := fun y ↦ S y + ball (0 : F) η with ht_def
  have ht : ∀ y : X, Convex ℝ (t y) := fun y ↦ (hconv y y.2).add (convex_ball _ _)
  have H : ∀ x : X, ∃ c : F, ∀ᶠ y in nhds x, c ∈ t y := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := hne x hx
    have hev : ∀ᶠ z in nhdsWithin x X, (S z ∩ ball c η).Nonempty :=
      hisc x hx hc (ball c η) (ball_mem_nhds c hη)
    have hev' := (preimage_val_mem_nhds_iff
      (A := {z | (S z ∩ ball c η).Nonempty}) hx).2 hev
    refine ⟨c, ?_⟩
    filter_upwards [hev'] with y hy
    obtain ⟨w, hwS, hwball⟩ := hy
    exact ⟨w, hwS, c - w, by
      simpa [mem_ball, dist_eq_norm, norm_sub_rev] using mem_ball.1 hwball, by abel⟩
  obtain ⟨g, hg⟩ := exists_continuous_forall_mem_convex_of_local_const ht H
  refine ⟨g, fun x ↦ ?_⟩
  obtain ⟨w, hwS, v, hvball, hwv⟩ := hg x
  exact ⟨w, hwS, by
    rw [mem_ball, dist_eq_norm, ← hwv]
    simpa [norm_sub_rev] using mem_ball.1 hvball⟩
```

Note it uses neither closed-valuedness nor completeness. Restate it on `↥X`
once the bridge lemma exists.

## Part B — the moving-ball refinement is isc

The one genuinely new semicontinuity lemma. The book cites 4.32 and 5.24 for
it; a direct argument is shorter and needs neither.

```lean
theorem svIsc_inter_ball {S : Y → Set F} (hisc : SvIsc S)
    {f : Y → F} (hf : Continuous f) {r : ℝ} :
    SvIsc (fun y ↦ S y ∩ ball (f y) r)
```

At `ȳ`, let `w ∈ S ȳ ∩ B(f ȳ, r)` and let `W` be a neighborhood of `w`. Put
`δ := r - d(w, f ȳ) > 0` — this is why the **open** ball must be used, and why
the iteration below must be phrased with open balls rather than the book's
`sν(x) + 2^{-ν}IB`. Continuity of `f` makes `d(f y, f ȳ) < δ/2` eventually;
inner semicontinuity of `S` applied to the neighborhood `W ∩ B(w, δ/2)` of `w`
makes `S y` meet it eventually. Any `v` in that intersection has

    d(v, f y) ≤ d(v, w) + d(w, f ȳ) + d(f ȳ, f y) < δ/2 + (r - δ) + δ/2 = r,

so `v ∈ S y ∩ B(f y, r) ∩ W`.

Convexity and nonemptiness of the refined values are `Convex.inter` with
`convex_ball` (verified) and the conclusion of the previous Part A step.

## Part C — exact selection by iteration (book Part 3)

Set `rν := 2^{-ν}`. Part A with `η = 1` gives `s₀`. Given `sν` continuous with
`(S y ∩ B(sν y, rν)).Nonempty` for all `y`, let

    Tν y := S y ∩ B(sν y, rν)

— nonempty, convex, and isc by Part B — and apply Part A to `Tν` with
`η = r_{ν+1}` to get `s_{ν+1}`. Then `(S y ∩ B(s_{ν+1} y, r_{ν+1})).Nonempty`
because `Tν y ⊆ S y`, and picking `v ∈ Tν y ∩ B(s_{ν+1} y, r_{ν+1})` gives

    d(s_{ν+1} y, sν y) ≤ d(s_{ν+1} y, v) + d(v, sν y) < r_{ν+1} + rν = 3·r_{ν+1}

uniformly in `y`. That is a uniform geometric Cauchy bound.

Two routes to the limit; **prefer the first**:

1. `sν - s₀` is bounded and continuous, so it is an element of `↥X →ᵇ F`, a
   complete space (`BoundedContinuousFunction.instCompleteSpace`, verified).
   The bound above is exactly the hypothesis of `cauchySeq_of_le_geometric_two`
   (`dist (f n) (f (n+1)) ≤ C / 2 / 2 ^ n`, verified present). Take the limit
   `g` there and set `s := s₀ + g`.
2. `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto` followed by
   `TendstoUniformlyOn.continuousOn` (both verified present), taking the
   pointwise limit first.

Finally `d(s y, sν y) ≤ 3·rν` by telescoping and `d(sν y, S y) < rν`, so
`infDist (s y) (S y) = 0`; **closed-valuedness is used exactly here** to
conclude `s y ∈ S y`. It is used nowhere else in Parts A–C.

## Part D — the Michael representation (book Part 5)

Needs `[SeparableSpace F]`. Work on `Y := ↥(dom S)`.

* Index by the ball family of 5.55: reuse `exists_ball_closedBall_subset` from
  `Chapter5/GenericContinuity.lean` verbatim — centres in a countable dense set,
  radii `1/(n+1)`. It already delivers exactly "for every `ū` and every
  neighbourhood, a ball with `ū` in the open ball and the closed ball inside".
* For an index `q` with centre `d` and radius `r`, put
  `O_q := {y : Y | (S y ∩ B(d, r)).Nonempty}`. It is **open** by
  `SvIscOn.isOpen_svPreimage` — which was added to
  `Chapter5/SemicontinuityCriteria.lean` for 5.55 and is already in the subtype
  form this needs.
* `S_q : ↥O_q → Set F := fun y ↦ closure (S y ∩ B(d, r))` is nonempty-,
  closed- and convex-valued (`(hconv.inter (convex_ball _ _)).closure`,
  verified) and isc relative to `O_q`. The book cites 4.32(c); prove it
  directly instead: a point of `closure (S ȳ ∩ B)` is approximated by some
  `w' ∈ S ȳ ∩ B`, and isc of `S` carries a neighbourhood of `w'` contained in
  `B` into the nearby values. Parts A–C then give a continuous selection
  `σ_q : ↥O_q → F`.
* Exhaust `O_q` from inside by relatively closed sets. The book uses rational
  balls and σ-compactness; in a metric space simply take

      C_{q,k} := {y : Y | 1/k ≤ infEDist y (Y \ O_q)}

  closed in `Y`, with `⋃ₖ C_{q,k} = O_q`. Use `infEDist`, not `infDist`, so
  that the case `O_q = Y` (empty complement, distance `∞`) behaves; this is the
  same reason `DistanceCriteria.lean` uses `infEDist`.
* Glue: `S_{q,k} y := if y ∈ C_{q,k} then {σ_q y} else S y`, which is
  nonempty-, closed- and convex-valued and isc relative to `Y`. Parts A–C give
  a continuous selection `s_{q,k}` of `S_{q,k}`, hence of `S`.
* Density: given `ȳ`, `ū ∈ S ȳ` and `ε > 0`, the ball lemma supplies `q` with
  `ū ∈ B(d, r)` and `r < ε`; then `ȳ ∈ O_q`, and `ȳ ∈ C_{q,k}` for large `k`,
  and `s_{q,k} ȳ = σ_q ȳ ∈ closure (S ȳ ∩ B(d,r)) ⊆ IB(d, r)`, so
  `d(ū, s_{q,k} ȳ) ≤ 2r < 2ε`.

**Factor the gluing lemma out**, because 5.59 is the same construction:

```lean
theorem svIsc_piecewise_singleton {S : Y → Set F} (hisc : SvIsc S)
    (hval : ∀ y, IsClosed (S y)) {C : Set Y} (hC : IsClosed C)
    {σ : Y → F} (hσ : ContinuousOn σ C) (hmem : ∀ y ∈ C, σ y ∈ S y) :
    SvIsc (fun y ↦ if y ∈ C then {σ y} else S y)
```

At `y ∈ C` combine two eventualities — continuity of `σ` handles the nearby
points of `C`, and inner semicontinuity of `S` at `σ y ∈ S y` handles the
points outside it. At `y ∉ C` closedness of `C` gives a neighbourhood missing
`C` entirely, and the value is `S` throughout it. The `if` needs
`Classical.propDecidable`; use `open Classical in` on the definition, not
`open scoped Classical` (the `linter.style.openClassical` check fires on the
latter, as `Chapter1/Defs.lean` still shows).

## Part E — Corollary 5.59

`S̄ y := if y ∈ X₀ then {s̄ y} else S y` for closed `X₀ ⊆ dom S`, then 5.58.
The gluing lemma above is the entire content; `dom S̄ = dom S`, and closedness
of `X₀` is what makes `S̄` isc at points outside `X₀`.

## Hypothesis findings to record in the ledger

Check each and write it into the 5.58/5.59 rows.

1. **σ-compactness of `dom S` is not needed.** The book assumes it to run its
   own partition-of-unity construction; Stone's theorem, an instance in
   Mathlib, makes every metric subspace paracompact, which is strictly more
   than the book extracts by hand. Record as a dropped hypothesis, in the
   project's usual style ("where a proof turns out not to need an assumption
   the book prints, the assumption is dropped and the ledger row says so").
2. **Finite-dimensionality is not needed.** `F` a Banach space suffices for the
   selection; separability is needed only for the countable representation.
   This is a generalization boundary, not an adaptation.
3. **5.59 as printed asks only for convex-valuedness**, while the 5.58 it
   invokes asks for closed-convex-valuedness, and `S̄` inherits closedness from
   `S`. Verify, and if it stands, record it the way the omitted
   closed-valuedness of 5.43(b) and 5.46 is recorded.

## Order of work

1. Bridge lemma `svIscAt_subtype_iff` into `SemicontinuityCriteria.lean`.
2. New module `Chapter5/MichaelSelection.lean`: Part A (paste the verified
   proof), Part B, Part C.
3. Commit — "a continuous selection exists" is a real milestone and 5.58's
   first sentence.
4. Part D, then Part E.
5. Ledger and `README.md`; `python3 scripts/check_ledgers.py`; full `lake build`
   at 600 s.

Part A is done. Part C is the fiddliest. Part D is the longest.
