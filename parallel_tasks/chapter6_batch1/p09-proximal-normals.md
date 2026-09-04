# P09 — Proximal normals and convex projections (6.16–6.17)

You are implementing an isolated Chapter 6 work package in the
`lean_rockafellar` repository. Work only on the branch and file assigned
below. The result must be production Lean code, not a sketch.

## Git contract

- Start from the exact base commit
  `b2eb4ea92faefd721b93eba48422a6c204d61fc9` (`b2eb4ea`).
- Create and work on the branch `chapter6-p09-proximal-normals`.
- Before editing, verify that `git rev-parse HEAD` is `b2eb4ea` (the full hash
  may be shown by Git).
- Your required final commit message is:
  `Chapter 6: formalize proximal normals`

## Exclusive file ownership

You may create or edit exactly one repository file:

`RockafellarWets/Chapter6/ProximalNormals.lean`

Do not edit any other file. In particular, do not edit `README.md`, any
`CHAPTER*_COVERAGE.md` ledger, `RockafellarWets.lean`,
`RockafellarWets/Chapter6.lean`, any batch index or shared contract under
`parallel_tasks/`, or a Lean file assigned to another prompt. Do not add an
umbrella import. Integration will be done separately.

Place every new declaration in `namespace RW`.

## Objective

Formalize Example 6.16 and Proposition 6.17 using the repository's
set-valued nearest-point map `projMapping`. Define proximal normal vectors,
prove that projection displacements are regular normals, prove the
smaller-step uniqueness property, and identify proximal and limiting normals
for convex sets. Derive the pointwise/mapping form of
`P_C = (I + N_C)⁻¹`.

Work over a real inner-product space. The inner-product norm supplies the
strict convexity needed by the existing segment-uniqueness lemma.

## Required mathematical deliverables

1. Define the proximal normal cone by the printed projection criterion:

   ```lean
   def proximalNormalCone (C : Set E) (x : E) : Set E :=
     {v | ∃ τ : ℝ, 0 < τ ∧ x ∈ projMapping C (x + τ • v)}
   ```

   Add a simp/membership theorem and prove that it is a cone at feasible
   points (`IsCone (proximalNormalCone C x)`). Respect the repository's
   convention that cones are empty off `C` (prove this or make it follow from
   the definition).

2. Prove the quadratic-support characterization, with constants normalized
   in either direction:

   ```lean
   v ∈ proximalNormalCone C x ↔
     x ∈ C ∧ ∃ ε > 0, ∀ y ∈ C,
       ⟪v, y - x⟫_ℝ ≤ ε * ‖y - x‖ ^ 2
   ```

   This is the expansion of the nearest-point inequality. Use
   `norm_sub_sq_real`, `real_inner_self_eq_norm_sq`, and positivity of the
   projection step.

3. Formalize Example 6.16:

   ```lean
   theorem sub_mem_regularNormalCone_of_mem_projMapping
       (hx : xbar ∈ projMapping C x) :
       x - xbar ∈ regularNormalCone C xbar

   theorem proximalNormalCone_subset_regularNormalCone :
       proximalNormalCone C x ⊆ regularNormalCone C x
   ```

   Also expose nonnegative scaling of a projection displacement as a regular
   normal.

   This worker owns the generic public projection-to-regular-normal API,
   including the displayed `sub_mem_regularNormalCone_of_mem_projMapping`
   theorem. P10 may use the same calculation only privately or inline.

4. Prove the intermediate-point uniqueness statement. If
   `x ∈ projMapping C (x + τ • v)`, `0 < τ'`, and `τ' < τ`, then

   ```lean
   projMapping C (x + τ' • v) = {x}.
   ```

   Reparameterize the point as lying strictly inside the segment from the
   original center to its nearest point and apply the existing
   `projMapping_segment` theorem.

5. Formalize Proposition 6.17 for a convex set:

   ```lean
   theorem proximalNormalCone_eq_normalCone_of_convex
       (hC : Convex ℝ C) (hx : x ∈ C) :
       proximalNormalCone C x = normalCone C x

   theorem mem_normalCone_iff_mem_projMapping_add_of_convex
       (hC : Convex ℝ C) (hx : x ∈ C) :
       v ∈ normalCone C x ↔ x ∈ projMapping C (x + v)
   ```

   The proof should use `normalCone_eq_of_convex`; the global supporting
   inequality expands directly into the squared-distance comparison.

6. Give mapping-level forms of the resolvent identities. A suitable exact
   formulation is:

   ```lean
   projMapping C =
     svInv (fun x => (fun v => x + v) '' normalCone C x)
   ```

   for convex `C`, together with the pointwise inverse-minus-identity form

   ```lean
   normalCone C x =
     (fun z => z - x) '' svInv (projMapping C) x.
   ```

   Extensionally equivalent formulations using `svAdd` and the singleton
   identity mapping are acceptable. State any necessary feasibility or
   convexity hypotheses explicitly and do not assume closedness unless a
   proof step actually uses projection attainment; all displayed statements
   concern already-given projection members.

## Existing files and APIs to use

- `RockafellarWets/Chapter5/ProjectionMappings.lean`:
  `projMapping`, `mem_projMapping`, and `projMapping_nonempty` if needed.
- `RockafellarWets/Chapter5/ProjectionGraphicalConvergence.lean`:
  `mem_projMapping_self`, `mem_projMapping_iff_dist`, and especially
  `projMapping_segment`.
- `RockafellarWets/Chapter5/Semicontinuity.lean`:
  `svInv`, `mem_svInv`; `RockafellarWets/Chapter5/PerturbedMappings.lean`
  provides `svAdd` if you choose that formulation.
- `RockafellarWets/Chapter6/NormalCones.lean`:
  `regularNormalCone`, `normalCone`, `isCone_regularNormalCone`, and
  `regularNormalCone_subset_normalCone`.
- `RockafellarWets/Chapter6/ConvexSets.lean`:
  `normalCone_eq_of_convex` and
  `normalCone_eq_regularNormalCone_of_convex`.
- Mathlib inner-product identities:
  `norm_sub_sq_real`, `real_inner_self_eq_norm_sq`, inner-product
  add/sub/smul lemmas, and `sq_le_sq₀`/nonnegativity tools as useful.

Prove the projection-to-normal result directly from squared norms; do not
depend on the parallel implementation of Theorem 6.12.

## Exclusions

- Do not work on the function proximal mappings `proximalMapping`,
  `proxMappingEReal`, Moreau envelopes, or Chapter 3 cancellation results.
- Do not formalize the nonconvex counterexample after 6.17.
- Do not edit or import a file created by another batch branch.
- Do not require global nonemptiness of `projMapping C`; the main results
  begin with an explicit projection member.
- Do not use `sorry`, `admit`, `axiom`, or an unsound placeholder.

## Verification and completion

From the repository root, run:

```text
lake env lean RockafellarWets/Chapter6/ProximalNormals.lean
rg -n '\bsorry\b|\badmit\b|\baxiom\b' RockafellarWets/Chapter6/ProximalNormals.lean
git diff --check
git status --short
```

Resolve every error and warning that indicates a real defect. The `rg`
command must produce no matches, and `git status --short` must name only the
assigned file. Then stage only the assigned file and create the required
commit:

```text
git add RockafellarWets/Chapter6/ProximalNormals.lean
git commit -m "Chapter 6: formalize proximal normals"
```

Report the commit hash, the exact verification command, and a short list of
the public declarations added.
