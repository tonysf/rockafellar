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
  - Chapter 5, *Set-Valued Mappings*, every numbered result: the
    introductory examples of constraint systems, generalized equations and
    implicit mappings, and algorithmic mappings and fixed points; domains,
    ranges, graphs, and inverses; set limits along an arbitrary index
    filter; outer and inner semicontinuity, with their neighborhood,
    sequential, graph, and open-preimage characterizations; profile,
    feasible-set, and convex constraint examples; continuity of distances;
    uniformity of approximation; local boundedness, level boundedness, the
    horizon mapping, the continuity criteria for single-valued and locally
    bounded mappings, optimal-set mappings, projections and proximal
    mappings, perturbed mappings, the closedness and horizon criteria for
    images, the total-continuity section, including horizon and cosmic set
    limits along an arbitrary index filter, the convergence of images of
    converging sets, and the pointwise and graphical limits of mappings with
    their limit formulas, graphical convergence relative to a set,
    uniformity criteria, projection example and compactness theorem, the
    approximation of generalized equations, the equicontinuity properties
    that reconcile graphical with pointwise convergence, continuous and
    uniform convergence of mappings with their distance function
    descriptions, the theorems relating the two to each other and to
    graphical convergence, the set-valued Arzelà--Ascoli theorem, the
    set-valued Dini theorem for monotone sequences, the generic continuity
    of semicontinuous mappings and of extended-real-valued functions, the
    continuous selections given by projections, and Michael's selection
    theorem with the countable Michael representations of 5.58 and the
    extension of prescribed selections of 5.59.
  - Chapter 6, *Variational Geometry*, every numbered result of Sections A
    through I: tangent, derivable, regular-tangent, regular-normal, limiting-normal,
    proximal-normal, and polar cones; tangent-normal polarity and the
    characterizations and consequences of Clarke regularity; boundary-point
    characterizations by nonzero normals; the full change of coordinates and the
    smooth-manifold cones; convex-set, finite-box, and finite Euclidean-product
    formulas; first-order optimality, variational inequalities, and
    complementarity; the everywhere-smooth gradient witness for regular
    normals; convex projections, proximal approximation of normals, and
    supporting-halfspace envelopes; pointedness and polarity, with Farkas'
    lemma for polyhedral cones; regular-tangent changes of coordinates;
    convexified cones and their finite-sum descriptions; active-constraint
    formulas and locally exact tangent approximations for polyhedral sets;
    normals to tangent cones, tangent-distance estimates, and separation of convex cones;
    local and global recession cones with their tangent and normal
    characterizations, interior tangents, and internal approximation in
    tangent limits; normal and tangent cones to sets with constraint
    structure, with Fritz John and Lagrange multipliers; the tangent-form,
    relative-interior, and convexified constraint qualifications and the
    Mangasarian--Fromovitz condition; tangents and normals to intersections,
    image sets, and sums of sets; and
    corrected generic continuity of normal-cone mappings.
  - Chapter 7, *Epigraphical Limits*, including epi-limit formulas, continuous
    and uniform convergence, convex functions, semiderivatives, minimization
    stability, and distance estimates. The Chapter 7 ledger records the scope of
    all 69 numbered results, including the hypotheses needed for each adaptation. The general
    Euclidean change-of-variables proof in 7.8 uses a pinned Lean proof of
    Brouwer’s fixed-point theorem.
  - Chapter 8, *Subderivatives and Subgradients*, including regular and limiting
    subgradients, epigraph normals, support functions, and graphical derivatives.
    All 54 numbered results have formalized counterparts, with four corrected
    statements and their scope documented in the Chapter 8 ledger.
  - Chapter 9, *Lipschitzian Properties*, all 69 numbered results: sharp
    Lipschitz moduli, subgradient criteria, set-valued Lipschitz properties,
    metric regularity, inverse and implicit mappings, Rademacher's theorem,
    Clarke derivatives, mollifier recovery, penalties, and extremal principles.
    The ledger records 58 exact results and 11 documented adaptations.
  - Chapter 10, *Subdifferential Calculus*, covers all 59 numbered results. Its generalized Fermat
    rules, proximal stationarity, level-set geometry, chain and coordinate
    rules, parametric minimization, epi-addition, amenability, subsmoothness,
    coderivatives, variational principles, and Lagrange multipliers are covered in
    48 exact results and 11 adaptations. Counterexamples and corrected hypotheses
    are recorded in the [Chapter 10 ledger](CHAPTER10_COVERAGE.md).
  - Chapter 11, *Dualization*, begins with the Legendre–Fenchel conjugate and its order-reversing property.
- Current frontier:
  - the Chapter 3 ledger classifies all 55 numbered results: 52 exact and three
    explicitly justified adaptations forced by the project's infinity
    conventions;
  - the Chapter 4 ledger classifies all 48 numbered results: 47 exact and one
    documented adaptation for the false openness/local-compactness clause in
    4.47 under the literal closed-ball cosmic embedding;
  - the Chapter 5 ledger classifies all 59 numbered results: 51 exact and
    eight documented adaptations, with no clause outstanding, covering 5.1
    through 5.59 -- formula 5(1), Definition 5.4, the characterizations of
    semicontinuity, the whole local-boundedness section, optimal-set
    mappings, both halves of 5.23, the closedness and horizon criteria for
    images, cosmic and total continuity -- where the inner condition printed
    in 5.27 is shown to be false and corrected against 4.20 -- the images of
    converging sets, and the graphical convergence section through 5.48 --
    where the closed-valuedness hypothesis printed in 5.34(a) is shown to be
    insufficient, and the closed-valuedness *omitted* from the last sentence
    of 5.43(b) and from both clauses of 5.46 is shown to be necessary -- and
    the whole of the metric-description section, where the uniform clause of
    5.49 is shown to be false as printed and is corrected by the bound its
    own proof assumes, and where the graph-distance space of 5.50 is
    identified isometrically with the Chapter 4 hyperspace -- and the whole
    operations section, where the first concluding statement of 5.53 is
    shown to be false as printed and is corrected by the total graph
    convergence its own proof uses -- and the generic continuity theorems
    5.55 and 5.56, whose relative topology on `X` is taken to be the
    subspace topology on `↥X`, where the book's nowhere dense and meager in
    `X` are Mathlib's own predicates, and the continuous selections of 5.57
    with the pointwise selection remark that precedes them -- and Michael's
    selection theorem, whose partition-of-unity core turns out to be in
    Mathlib already under another name, so that the σ-compactness of `dom S`
    printed in 5.58 is dropped, Stone's theorem supplying more than the
    book's construction extracts by hand, while the closed-valuedness
    *omitted* from 5.59 is added, the mapping its proof builds inheriting
    its values from `S`.  The three introductory examples are stated last
    rather than first, since the mappings they name are built from machinery
    the later sections supply, and the proximal half of 5.23 is 5.22 applied
    to the proximal integrand, for which the extended-real proximal mapping
    missing from Chapter 1 is supplied here.  Chapter 5 is complete;
  - the Chapter 6 ledger classifies all 49 numbered results: 45 exact and four
    adapted, with no missing or partial result.  Exact coverage comprises
    6.1--6.33, 6.35--6.43, and 6.45--6.47; 6.34, 6.44, 6.48, and 6.49 are
    adapted.  The third batch completes Sections D through I: Theorem 6.14
    and its tangent counterpart 6.31 are proved from a compact quadratic
    penalty with normalized Fritz John multipliers, so that the printed
    representation follows once the constraint qualification excludes a zero
    objective multiplier, and Corollary 6.15 gives Lagrange multipliers with
    the four printed sign cases for arbitrary finite families of closed
    intervals; Proposition 6.35 characterizes local recession through nearby
    tangents and normals by a squared-distance argument along rays; Theorem
    6.36 and Corollary 6.37 give the five equivalent interior-tangent
    conditions, the pointedness criterion, the closure formula, and the
    uniform internal approximation of compact direction sets; Exercise 6.39
    relates the tangent-surjectivity, relative-interior, and convexified
    constraint qualifications, with the relative interior read as Mathlib's
    intrinsic interior, and Example 6.40 instantiates all of them as the
    Mangasarian--Fromovitz condition on a mixed inequality/equality box;
    Theorems 6.42 and 6.43 give intersections and images, including the
    closed-cone union under a locally bounded inverse and the convex linear
    equalities without closedness; and Exercise 6.44 is derived from 6.43 by
    coordinate summation.  Exercise 6.44 is adapted: its printed first
    inclusion, the sum of the factor tangent cones inside the tangent cone of
    the sum, fails for closed factors, and a formalized plane counterexample
    with two compact factors shows why; the inclusion is proved under
    geometric derivability of the factors, and every other clause as printed.
    The second
    parallel batch completes the limiting-normal change of coordinates, so
    that all three formulas of 6.7 are proved, and derives the smooth-manifold
    cones of 6.8 from it, with geometric derivability supplied by the implicit
    function theorem; packages the arbitrary finite box of 6.10 and the
    nonnegative-orthant complementarity of 6.13 on `EuclideanSpace`; assembles
    the everywhere-`C¹` unique-maximum witness of 6.11; proves the proximal
    approximation of normals 6.18 under only the printed outer-limit
    hypothesis; adds local and global recession cones for 6.33--6.34;
    completes the arbitrary finite product formulas of 6.41, including the
    regular-tangent equality and the tangent equality under Clarke
    regularity; and proves Farkas' lemma 6.45 with the polar exchange of
    finitely generated and H-polyhedral cones.  Exercise 6.34 is adapted
    rather than overstated: its clause (c) needs `C` nonempty under the book's
    own rule `∅^∞ = {0}`, and is proved for the ray-defined global recession
    cone, since the literal intersection of local recession cones is the whole
    space for an open convex set.  Exercise 6.19 characterizes boundary points
    by nonzero limiting normals and interior points by the zero normal cone,
    and includes the normal-cone inclusion under closure.  Proposition 6.27
    proves that normals to the tangent cone are normals to the original set,
    together with unit-normal distance witnesses and attained extremum bounds.
    Theorem 6.28 and
    Corollaries 6.29--6.30 supply both tangent-normal polarities, all seven
    equivalent regularity criteria, and convexity and geometric derivability
    at Clarke regular points.  The finite-product proof now uses this general
    polarity module.  Exercise 6.32 gives the regular-tangent change of
    coordinates for arbitrary target sets, and 6.38 supplies the convexified
    cones, their polar identities, and the sharp finite-sum bound by the
    ambient dimension.  Theorem 6.46 and Exercise 6.47 give the active-constraint
    tangent and normal formulas and the exact local agreement of a polyhedron
    with its translated tangent cone.  Exercise 6.48 supplies the weak, proper,
    and almost-strict cone-separation criteria.  Its literal almost-strict
    hyperplane equivalence requires a nontrivial ambient space; the two zero
    cones in dimension zero give a formal counterexample to the unrestricted
    statement, while the algebraic equivalences hold in every finite dimension.
    Proposition 6.49 is adapted rather than
    overstated: the arbitrary-set frontier claim fails for `C = ℚ ⊂ ℝ`, while
    the formalized theorem holds on `C ∩ frontier C` for arbitrary `C` and
    recovers the full meagerness and density conclusion on `frontier C` when
    `C` is closed.

See the [Chapter 3](CHAPTER3_COVERAGE.md), [Chapter 4](CHAPTER4_COVERAGE.md),
[Chapter 5](CHAPTER5_COVERAGE.md), [Chapter 6](CHAPTER6_COVERAGE.md),
[Chapter 7](CHAPTER7_COVERAGE.md), [Chapter 8](CHAPTER8_COVERAGE.md),
[Chapter 9](CHAPTER9_COVERAGE.md), [Chapter 10](CHAPTER10_COVERAGE.md), and
[Chapter 11](CHAPTER11_COVERAGE.md)
coverage ledgers for conservative, result-by-result accounts of exact,
adapted, and missing coverage.

## Roadmap

From here, we plan to continue chapter-by-chapter in book order. The goal is a
comprehensive sweep of the remainder of the book: main results, examples, and
exercises will all be formalized, with dependency-critical exercises prioritized
first whenever they unlock later sections.

1. Chapter 6, *Variational Geometry*: tangent cones, normal cones, Clarke
   regularity, multipliers, proximal normals, and tangent-normal relations.
   Every numbered result is now covered; the remaining work is the four
   adapted statements, should sharper formulations become available.
2. Chapter 7, *Epigraphical Limits*: every numbered result has a proof or
   a documented correction with its verified scope in the ledger.
3. Chapter 8, *Subderivatives and Subgradients*: every numbered result has a
   proof or a documented correction, including all proximal recovery and
   Clarke subgradient clauses.
4. Chapter 9, *Lipschitzian Properties*: every numbered result has a proof
   or a documented correction, including mollifier recovery and extremal
   principles.
5. Chapter 10, *Subdifferential Calculus*, covers every numbered entry,
   including the eigenvalue example and the two marginal subsmoothness theorems.
6. Chapter 11, *Dualization*: cover Legendre-Fenchel duality, conjugacy, polar
   sets and gauges, dual operations, dual optimization, and Lagrangian
   constructions.
7. Chapter 12, *Monotone Mappings*: formalize monotonicity and maximality,
   Minty parameterization, links with convex functions, graphical convergence,
   and variational inequalities.
8. Chapter 13, *Second-Order Theory*: develop second-order differentiability,
   second subderivatives, calculus rules, second-order optimality, and
   prox-regularity.
9. Chapter 14, *Measurability*: cover measurable mappings and selections,
   normal integrands, operations on integrands, and integral functionals.

Priorities may occasionally shift to match Mathlib support and dependency order,
but the intended reading and formalization order remains the book order.

## Repository Layout

- `RockafellarWets.lean`: top-level import for the current formalization.
- `RockafellarWets/Chapter1` through `RockafellarWets/Chapter11`:
  chapter-level Lean sources.
- `CHAPTER3_COVERAGE.md`, `CHAPTER4_COVERAGE.md`, `CHAPTER5_COVERAGE.md`,
  `CHAPTER6_COVERAGE.md`, `CHAPTER7_COVERAGE.md`, `CHAPTER8_COVERAGE.md`,
  `CHAPTER9_COVERAGE.md`, `CHAPTER10_COVERAGE.md`, and `CHAPTER11_COVERAGE.md`: result-by-result coverage ledgers.
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

After building, the complete kernel-dependency audit for Chapters 6–11 runs with the following command.

```bash
lake env lean scripts/audit_variational.lean
```

This includes private helpers and generated declarations and permits only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## License

This project is licensed under the [Apache License 2.0](LICENSE).
