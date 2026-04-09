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
  - Large parts of Chapter 3, *Cones and Cosmic Closure*: horizon cones,
    horizon functions, linear images, set operations, cone calculus, pointed
    cones, positive homogeneity, positive hulls and gauge functions,
    coercivity, pointwise operations, parametric minimization, epi-addition,
    and cone-induced orderings.
- Current frontier:
  - the development has reached the gauge-function material in Section G of
    Chapter 3;
  - Chapter 3 is still in progress;
  - Chapters 4 and beyond have not yet been started in this repository.

## Repository Layout

- `RockafellarWets.lean`: top-level import for the current formalization.
- `RockafellarWets/Chapter1`, `RockafellarWets/Chapter2`,
  `RockafellarWets/Chapter3`: chapter-level Lean sources.
- `rockafellar_wets.pdf`: local reference copy of the text used during the
  formalization.

## Building

```bash
lake build
```

The required Lean toolchain is pinned in `lean-toolchain`.
