# Copy/paste prompt: P19 approximation of normals

You are the P19 worker for Chapter 6 batch 2 in the `lean_rockafellar`
repository. Formalize every clause of Rockafellar--Wets Exercise 6.18,
including the stronger assertion that the approximating normals in both
parts can be chosen proximal. Prove a reusable API, leave no placeholders,
and commit only your assigned file.

## Starting state and branch

Use an isolated checkout and create `chapter6-p19-normal-approximation` from
exactly:

```text
9fa1c19eab36f7fc79845f679d35b87344366e0b
```

```text
git switch -c chapter6-p19-normal-approximation 9fa1c19
git rev-parse HEAD
git status --short
```

Do not reset or overwrite an existing branch. Stop before editing if the full
hash differs or the starting worktree is dirty.

## Exclusive ownership

Create and edit only:

```text
RockafellarWets/Chapter6/NormalApproximation.lean
```

Do not edit existing source, umbrella imports, `README.md`,
`CHAPTER6_COVERAGE.md`, any ledger or lake file, anything under
`parallel_tasks/`, or another worker-owned file. Do not import another Batch 2
worker's unmerged module. Put every declaration in `namespace RW`.

## Book scope and required results

Exercise 6.18 is on book page 214 (PDF page 222). Work in a finite-dimensional
real inner-product space, as the book does. Part (a) says that for closed `C`,
`xbar ∈ C`, `vbar ∈ normalCone C xbar`, and `ε > 0`, there are `x ∈ C` and a
proximal normal `v` at `x`, both within `ε` of `xbar` and `vbar`. State the
open-ball version and, if convenient, a sequence/density version such as

```lean
theorem exists_proximalNormal_close_of_mem_normalCone
    [FiniteDimensional ℝ E] {C : Set E} (hC : IsClosed C)
    {xbar vbar : E} (hxbar : xbar ∈ C) (hvbar : vbar ∈ normalCone C xbar)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ C ∩ Metric.ball xbar ε,
      (proximalNormalCone C x ∩ Metric.ball vbar ε).Nonempty
```

You may use a cleaner logically equivalent conjunction. Also record explicitly
that the selected proximal normal lies in
`normalCone C x`, using `proximalNormalCone_subset_regularNormalCone` and
`regularNormalCone_subset_normalCone`; do not weaken the result to an
approximation by regular normals.

Part (b) concerns a sequence `Cseq : ℕ → Set E` of nonempty closed sets with
only the printed outer-limit hypothesis

```lean
outerSetLimit Cseq = C
```

not full PK convergence. For every `xbar ∈ C` and
`vbar ∈ normalCone C xbar`, produce a strict extraction `φ : ℕ → ℕ` and
sequences `xs vs : ℕ → E` satisfying

```lean
StrictMono φ
∀ n, xs n ∈ Cseq (φ n)
∀ n, vs n ∈ proximalNormalCone (Cseq (φ n)) (xs n)
Tendsto xs atTop (nhds xbar)
Tendsto vs atTop (nhds vbar)
```

Require `IsClosed C`, `∀ n, IsClosed (Cseq n)`, and
`∀ n, (Cseq n).Nonempty`, exactly as needed by the printed exercise and
projection existence. Then package the stated graphical consequence, and
prefer the stronger proximal form:

```lean
normalCone C xbar ⊆
  graphicalOuterLimit (fun n ↦ proximalNormalCone (Cseq n)) xbar

normalCone C xbar ⊆
  graphicalOuterLimit (fun n ↦ normalCone (Cseq n)) xbar
```

The first inclusion should imply the second. Do not replace `outerSetLimit
Cseq = C` by `PKConverges Cseq C`; that would lose the point of 6.18(b).

## Intended proof route and existing APIs

Start from:

- `RockafellarWets/Chapter6/ProximalNormals.lean`:
  `proximalNormalCone`, its quadratic/projection characterizations,
  `proximalNormalCone_subset_regularNormalCone`, and
  `projMapping_add_smul_eq_singleton_of_lt`;
- `RockafellarWets/Chapter6/NormalCones.lean`: the sequential definition and
  constructors for `normalCone`;
- `RockafellarWets/Chapter5/ProjectionGraphicalConvergence.lean`:
  `projMapping_nonempty`, `outerSetLimit_svGraph_projMapping_subset`,
  `svGraph_projMapping_subset_innerSetLimit`, and the full projection
  convergence theorem;
- `RockafellarWets/Chapter4/SetConvergenceCompactness.lean`:
  `exists_pkConvergent_subsequence_with_nonempty_limit`;
- `RockafellarWets/Chapter4/SetLimitCharacterizations.lean` and
  `RockafellarWets/Chapter5/GraphicalLimits.lean` for the subsequence
  characterizations.

For (a), first handle a unit regular normal. Project
`xbar + δ • vbar` onto `C`. The nearest-point inequality and the regular-normal
little-o inequality show that the normalized projection displacement tends to
`vbar`; then use the defining projection step to make it proximal. Treat zero
and arbitrary norm carefully, and lift from regular normals to limiting
normals using their defining sequences. A sequence lemma followed by an
`eventually` choice is often cleaner than doing all estimates directly inside
an arbitrary ball.

For (b), do not assume the full sequence converges. First prove the proximal
case: retain `xbar` while extracting a PK-convergent subsequence, call its
limit `D`, observe `D ⊆ C` from the outer-limit hypothesis, and hence preserve
the relevant projection onto `D`. Projection graphical convergence then
gives proximal normals to the extracted `Cseq`. Extend from proximal to all
normal vectors with (a), a diagonal argument, or equivalently by using the
closedness of the outer graph limit. Make every composition of strict
extractions explicit and verify its indices.

## Exclusions and quality bar

Do not formalize 6.19, alter the definitions of projections or normal cones,
or add a global compactness framework. Do not claim graphical convergence of
normal cones: the book only proves an outer inclusion and gives an example
where it is strict. Keep all finite-dimensional assumptions visible.

No `sorry`, `admit`, new `axiom`, linter suppression, or theorem that merely
restates an unproved premise is allowed.

## Verification and commit

Run:

```text
lake env lean RockafellarWets/Chapter6/NormalApproximation.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/NormalApproximation.lean
git diff --check
git status --short
```

The search must be empty and status must name only the assigned file. Commit:

```text
git add RockafellarWets/Chapter6/NormalApproximation.lean
git commit -m "Formalize approximation of normal vectors"
```

Report the commit hash, public theorem inventory with exact hypotheses, how
the outer-limit-only hypothesis was preserved, and every verification result.
