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
- `scripts/check_ledgers.py` passes: the coverage ledgers agree with their
  own result rows, and every ledger link and module import resolves.
- The project currently covers:
  - Chapter 1, *Max and Min*: project definitions, semicontinuity, and Moreau
    envelope material.
  - Chapter 2, *Convexity*: convex sets and functions, level sets, operations
    preserving convexity, convex hulls, separation, and relative interior.
  - Chapter 3, *Cones and Cosmic Closure*, through Proposition 3.55:
    cosmic compactification, horizon cones and functions, cone and set
    calculus, coercivity, parametric minimization, epi-addition, cancellation,
    orderings, positive hulls, and the polyhedral cone/set/function layer.
  - Chapter 4, *Set Convergence*, through Exercise 4.48: inner, outer,
    horizon, cosmic, and total limits; convergence under operations;
    quantitative set distances; hyperspace metrics; compactness; and
    separability.
  - Chapter 5, *Set-Valued Mappings*, through Theorem 5.19: domains, ranges,
    graphs, and inverses; set limits along an arbitrary index filter; outer
    and inner semicontinuity, with their neighborhood, sequential, graph, and
    open-preimage characterizations; profile, feasible-set, and convex
    constraint examples; continuity of distances; uniformity of approximation;
    local boundedness, level boundedness, and the horizon mapping.
- Current frontier:
  - the Chapter 3 ledger classifies all 55 numbered results: 52 exact and three
    explicitly justified adaptations forced by the project's infinity
    conventions;
  - the Chapter 4 ledger classifies all 48 numbered results: 47 exact and one
    documented adaptation for the false openness/local-compactness clause in
    4.47 under the literal closed-ball cosmic embedding;
  - the Chapter 5 ledger classifies all 59 numbered results: 16 exact so far,
    consecutive from 5.4 through 5.19, covering formula 5(1), Definition 5.4,
    the characterizations of semicontinuity, and the local-boundedness
    section.

See the [Chapter 3](CHAPTER3_COVERAGE.md), [Chapter 4](CHAPTER4_COVERAGE.md),
and [Chapter 5](CHAPTER5_COVERAGE.md) coverage ledgers for conservative,
result-by-result accounts of exact, adapted, and missing coverage.

## Roadmap

From here, we plan to continue chapter-by-chapter in book order. The goal is a
comprehensive sweep of the remainder of the book: main results, examples, and
exercises will all be formalized, with dependency-critical exercises prioritized
first whenever they unlock later sections.

1. Chapter 5, *Set-Valued Mappings*: cover domains, ranges, inverses,
   semicontinuity, local boundedness, graphical convergence, and selection
   material.
2. Chapter 6, *Variational Geometry*: develop tangent cones, normal cones,
   Clarke regularity, multipliers, proximal normals, and tangent-normal
   relations.
3. Chapter 7, *Epigraphical Limits*: formalize pointwise convergence,
   epi-convergence, minimization stability, epi-continuity, and epi-distance
   results.
4. Chapter 8, *Subderivatives and Subgradients*: cover subderivatives,
   subgradients, convexity and optimality criteria, duality, calmness, and
   graphical differentiation.
5. Chapter 9, *Lipschitzian Properties*: formalize Lipschitz moduli,
   subdifferential criteria, the Aubin property, metric regularity, and
   derivative-based characterizations.
6. Chapter 10, *Subdifferential Calculus*: develop normals to level sets, chain
   rules, parametric optimality, PLQ and amenable objects, and coderivative
   calculus.
7. Chapter 11, *Dualization*: cover Legendre-Fenchel duality, conjugacy, polar
   sets and gauges, dual operations, dual optimization, and Lagrangian
   constructions.
8. Chapter 12, *Monotone Mappings*: formalize monotonicity and maximality,
   Minty parameterization, links with convex functions, graphical convergence,
   and variational inequalities.
9. Chapter 13, *Second-Order Theory*: develop second-order differentiability,
   second subderivatives, calculus rules, second-order optimality, and
   prox-regularity.
10. Chapter 14, *Measurability*: cover measurable mappings and selections,
    normal integrands, operations on integrands, and integral functionals.

Priorities may occasionally shift to match Mathlib support and dependency order,
but the intended reading and formalization order remains the book order.

## Repository Layout

- `RockafellarWets.lean`: top-level import for the current formalization.
- `RockafellarWets/Chapter1`, `RockafellarWets/Chapter2`,
  `RockafellarWets/Chapter3`, `RockafellarWets/Chapter4`: chapter-level Lean
  sources.
- `CHAPTER3_COVERAGE.md`, `CHAPTER4_COVERAGE.md`, `CHAPTER5_COVERAGE.md`:
  result-by-result coverage ledgers.
- `scripts/`: repository checks run in CI alongside `lake build`.
- `rockafellar_wets.pdf`: local reference copy of the text used during the
  formalization.
- `LICENSE`: Apache License 2.0, matching the source-file headers.

## Building

```bash
lake build
```

The required Lean toolchain is pinned in `lean-toolchain`.

The coverage ledgers are machine-checked against their own rows, and every
`import RockafellarWets.*` is checked to resolve, by:

```bash
python3 scripts/check_ledgers.py
```

## License

This project is licensed under the [Apache License 2.0](LICENSE).
