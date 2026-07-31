# RockafellarWets

Lean 4 formalization of parts of Rockafellar and Wets, *Variational Analysis*.

## Scope

This repository is building a reusable Lean development of the convex-analytic and
variational-analysis results in the book, not just a list of isolated theorem
statements. The formalization is organized chapter-by-chapter and aims to capture
both the main results and the supporting infrastructure around them: extended-real
valued functions, epigraphs, semicontinuity, convexity, cones, horizon
constructions, coercivity, and related operations.

Where the book's notation does not line up exactly with current Mathlib APIs, the
formalization follows the Lean/Mathlib version that gives the mathematically
correct statement in context.

## Current Status

- `lake build` passes.
- `RockafellarWets/` is currently `sorry`-free.
- The project currently covers:
  - Chapter 1, *Max and Min*: project definitions, semicontinuity, and Moreau
    envelope material.
  - Chapter 2, *Convexity*: convex sets and functions, level sets, operations
    preserving convexity, convex hulls, separation, and relative interior.
  - Chapter 3, *Cones and Cosmic Closure*, through Proposition 3.55:
    cosmic compactification, horizon cones and functions, cone and set
    calculus, coercivity, parametric minimization, epi-addition, cancellation,
    orderings, positive hulls, and the polyhedral cone/set/function layer.
- Current frontier:
  - the Chapter 3 ledger classifies all 55 numbered results: 36 exact and 19
    explicitly documented Lean/Mathlib adaptations;
  - the polyhedral layer now contains both finite-halfspace and
    finite-generator representations, their Minkowski–Weyl equivalence, and
    the closure operations needed for Proposition 3.55;
  - Chapters 4 and beyond have not started.

The frontier is not a claim of contiguous completion. See the
[Chapter 3 coverage ledger](CHAPTER3_COVERAGE.md) for a conservative,
result-by-result account of exact, adapted, partial, and missing coverage.

## Roadmap

From here, we plan to continue chapter-by-chapter in book order. The goal is a
comprehensive sweep of the remainder of the book: main results, examples, and
exercises will all be formalized, with dependency-critical exercises prioritized
first whenever they unlock later sections.

1. Chapter 4, *Set Convergence*: formalize inner and outer limits,
   Painleve-Kuratowski convergence, Pompeiu-Hausdorff distance, and the
   compactness and horizon-limit layer.
2. Chapter 5, *Set-Valued Mappings*: cover domains, ranges, inverses,
   semicontinuity, local boundedness, graphical convergence, and selection
   material.
3. Chapter 6, *Variational Geometry*: develop tangent cones, normal cones,
   Clarke regularity, multipliers, proximal normals, and tangent-normal
   relations.
4. Chapter 7, *Epigraphical Limits*: formalize pointwise convergence,
   epi-convergence, minimization stability, epi-continuity, and epi-distance
   results.
5. Chapter 8, *Subderivatives and Subgradients*: cover subderivatives,
   subgradients, convexity and optimality criteria, duality, calmness, and
   graphical differentiation.
6. Chapter 9, *Lipschitzian Properties*: formalize Lipschitz moduli,
   subdifferential criteria, the Aubin property, metric regularity, and
   derivative-based characterizations.
7. Chapter 10, *Subdifferential Calculus*: develop normals to level sets, chain
   rules, parametric optimality, PLQ and amenable objects, and coderivative
   calculus.
8. Chapter 11, *Dualization*: cover Legendre-Fenchel duality, conjugacy, polar
   sets and gauges, dual operations, dual optimization, and Lagrangian
   constructions.
9. Chapter 12, *Monotone Mappings*: formalize monotonicity and maximality,
    Minty parameterization, links with convex functions, graphical convergence,
    and variational inequalities.
10. Chapter 13, *Second-Order Theory*: develop second-order differentiability,
    second subderivatives, calculus rules, second-order optimality, and
    prox-regularity.
11. Chapter 14, *Measurability*: cover measurable mappings and selections,
    normal integrands, operations on integrands, and integral functionals.

Priorities may occasionally shift to match Mathlib support and dependency order,
but the intended reading and formalization order remains the book order.

## Repository Layout

- `RockafellarWets.lean`: top-level import for the current formalization.
- `RockafellarWets/Chapter1`, `RockafellarWets/Chapter2`,
  `RockafellarWets/Chapter3`: chapter-level Lean sources.
- `CHAPTER3_COVERAGE.md`: result-by-result Chapter 3 coverage ledger.
- `rockafellar_wets.pdf`: local reference copy of the text used during the
  formalization.
- `LICENSE`: Apache License 2.0, matching the source-file headers.

## Building

```bash
lake build
```

The required Lean toolchain is pinned in `lean-toolchain`.

## License

This project is licensed under the [Apache License 2.0](LICENSE).
