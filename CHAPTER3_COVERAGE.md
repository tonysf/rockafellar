# Chapter 3 Coverage

This ledger tracks Results 3.1–3.55 in Chapter 3, *Cones and Cosmic
Closure*, of Rockafellar and Wets, *Variational Analysis*. It records the
declarations imported by `RockafellarWets/Chapter3.lean`.

Each row distinguishes a literal formalization from a deliberate model or
`EReal`-convention adaptation. In particular, an **Adapted** row must identify
the changed statement and may cite a formal counterexample showing why the
literal statement is unavailable under the project definitions.

## Status key

- **Exact**: every substantive clause has a matching Lean declaration.
- **Adapted**: the mathematical role is covered, with the precise encoding,
  ambient-type restriction, or extended-real convention stated in the row.
- **Partial**: a substantive implication or clause is still absent.
- **Missing**: no substantive formalization is present.

| Status | Count |
| --- | ---: |
| Exact | 52 |
| Adapted | 3 |
| **Total** | **55** |

## Results 3.1–3.16

| Result | Status | Coverage and principal evidence |
| --- | --- | --- |
| 3.1 | **Exact** | [`CosmicSpace.lean`](RockafellarWets/Chapter3/CosmicSpace.lean) defines the closed-ball compactification, ordinary and direction embeddings, and both convergence clauses. |
| 3.2 | **Exact** | [`CosmicSpace.lean`](RockafellarWets/Chapter3/CosmicSpace.lean) proves compactness, classified convergent subsequences, and the bounded-sequence characterization. |
| 3.3 | **Exact** | [`Defs.lean`](RockafellarWets/Chapter3/Defs.lean) defines `horizonCone`, including the empty-set convention, closure invariance, and closedness. |
| 3.4 | **Exact** | [`CosmicSetClosure.lean`](RockafellarWets/Chapter3/CosmicSetClosure.lean) transports the closure formula and closedness criterion to actual subsets of the closed-ball `CosmicSpace`; the ray-space results remain the proof backend. |
| 3.5 | **Exact** | [`HorizonCones.lean`](RockafellarWets/Chapter3/HorizonCones.lean): `isBounded_iff_horizonCone_eq_singleton_zero`. |
| 3.6 | **Exact** | [`HorizonCones.lean`](RockafellarWets/Chapter3/HorizonCones.lean) proves convexity and both directions of the closed-convex ray characterization. |
| 3.7 | **Exact** | [`FiniteConeSetOperations.lean`](RockafellarWets/Chapter3/FiniteConeSetOperations.lean) packages the three-way equivalence with arbitrary finite nonnegative combinations. |
| 3.8 | **Exact** | [`Cones.lean`](RockafellarWets/Chapter3/Cones.lean) supplies lineality/difference subspaces, maximality/minimality, and the negation criterion. |
| 3.9 | **Exact** | [`HorizonCones.lean`](RockafellarWets/Chapter3/HorizonCones.lean) covers arbitrary intersections/unions, closed-convex intersection equality, and finite-union equality. |
| 3.10 | **Exact** | [`LinearImages.lean`](RockafellarWets/Chapter3/LinearImages.lean) proves the general inclusion and the closed-image/equality theorem under horizon-kernel nondegeneracy. |
| 3.11 | **Exact** | [`DependentProducts.lean`](RockafellarWets/Chapter3/DependentProducts.lean) proves every finite-product clause for dependent factors `∀ i, Set (E i)`, including convex and bounded-off-factor equalities; the homogeneous API is recovered by specialization. |
| 3.12 | **Exact** | [`FiniteConeSetOperations.lean`](RockafellarWets/Chapter3/FiniteConeSetOperations.lean) gives finite-family closedness, inclusion, convex equality, and bounded-off-one equality for set sums. |
| 3.13 | **Exact** | [`PointedCones.lean`](RockafellarWets/Chapter3/PointedCones.lean) defines `IsPointed`. |
| 3.14 | **Exact** | [`PointedCones.lean`](RockafellarWets/Chapter3/PointedCones.lean): `isPointed_iff_inter_neg_eq_singleton_zero`. |
| 3.15 | **Exact** | [`FiniteConeSetOperations.lean`](RockafellarWets/Chapter3/FiniteConeSetOperations.lean) proves the linearly-independent representation, the sharp dimension bound, and the exact padded `finrank`-term form; [`PointedCones.lean`](RockafellarWets/Chapter3/PointedCones.lean) supplies closedness and pointedness. |
| 3.16 | **Exact** | [`NonlinearImages.lean`](RockafellarWets/Chapter3/NonlinearImages.lean) proves closedness of a continuous image under the book's no-bounded-horizon-escape condition and its standard sufficient cases. |

## Results 3.17–3.40

| Result | Status | Coverage and principal evidence |
| --- | --- | --- |
| 3.17 | **Exact** | [`HorizonFunctions.lean`](RockafellarWets/Chapter3/HorizonFunctions.lean) defines `horizonFunction` and proves the epigraph identity, including the identically-`⊤` case. |
| 3.18 | **Exact** | [`PositiveHomogeneity.lean`](RockafellarWets/Chapter3/PositiveHomogeneity.lean) defines positive homogeneity and sublinearity. |
| 3.19 | **Exact** | [`PositiveHomogeneity.lean`](RockafellarWets/Chapter3/PositiveHomogeneity.lean) gives the cone/convex-cone epigraph equivalences; [`HomogeneousCompletion.lean`](RockafellarWets/Chapter3/HomogeneousCompletion.lean) proves `(cl f)∞ = f∞` and `f∞ = cl f` for positively homogeneous `f`. |
| 3.20 | **Exact** | [`PositiveHomogeneity.lean`](RockafellarWets/Chapter3/PositiveHomogeneity.lean) constructs the linearity subspace and proves the global-linearity equivalence. |
| 3.21 | **Exact** | [`HorizonFunctionFormulas.lean`](RockafellarWets/Chapter3/HorizonFunctionFormulas.lean) proves formula 3(3), defines the extended-real ray difference quotient, and proves the exact monotone supremum and `atTop` limit formula 3(4); the earlier real-valued wrappers remain available. |
| 3.22 | **Exact** | [`HorizonFunctions.lean`](RockafellarWets/Chapter3/HorizonFunctions.lean) proves both the bounded-half-line and bounded-above cosmic-sequence hypotheses. |
| 3.23 | **Exact** | [`HorizonFunctions.lean`](RockafellarWets/Chapter3/HorizonFunctions.lean) proves the inclusion, convex/lsc equality, and bounded-level consequence. |
| 3.24 | **Exact** | [`ConstraintHorizons.lean`](RockafellarWets/Chapter3/ConstraintHorizons.lean) proves the constraint-system inclusion and closed-convex equality, including real-valued wrappers. |
| 3.25 | **Exact** | [`RadialCoercivity.lean`](RockafellarWets/Chapter3/RadialCoercivity.lean) defines the literal extended-real `radialSlopeLiminf`, bounded-below-on-bounded-sets condition, and all three radial coercivity predicates. |
| 3.26 | **Exact** | [`RadialCoercivity.lean`](RockafellarWets/Chapter3/RadialCoercivity.lean) proves formula 3(7), all three horizon characterizations, and equivalence with the existing affine-minorant API under the book's proper/lsc finite-dimensional hypotheses. |
| 3.27 | **Exact** | [`RadialCoercivity.lean`](RockafellarWets/Chapter3/RadialCoercivity.lean) gives the literal radial implication, convex equivalence, and exclusion of counter-coercivity. |
| 3.28 | **Exact** | [`RadialCoercivity.lean`](RockafellarWets/Chapter3/RadialCoercivity.lean) proves infinite prox-threshold directly from literal non-counter-coercivity under the proper/lsc hypotheses. |
| 3.29 | **Exact** | [`HorizonAddition.lean`](RockafellarWets/Chapter3/HorizonAddition.lean) proves the nonconvex inequality, convex equality, and both coercivity consequences. |
| 3.30 | **Exact** | [`Pointwise.lean`](RockafellarWets/Chapter3/Pointwise.lean) proves the supremum and infimum inequalities and their equality cases. |
| 3.31 | **Exact** | [`Parametric.lean`](RockafellarWets/Chapter3/Parametric.lean) proves condition 3(8), convex necessity, formula 3(9), regularity, and finite attainment; [`RadialCoercivity.lean`](RockafellarWets/Chapter3/RadialCoercivity.lean) supplies both inheritance clauses in the literal radial terminology. |
| 3.32 | **Exact** | [`Parametric.lean`](RockafellarWets/Chapter3/Parametric.lean) uses the book-correct `argmin`: identically-`⊤` slices have no minimizers while `⊥`-valued minimizers are retained, and proves all boundedness and value-function clauses. |
| 3.33 | **Exact** | [`EpiAdditionBookCompletion.lean`](RockafellarWets/Chapter3/EpiAdditionBookCompletion.lean) derives both non-counter-coercivity facts from the book's paired horizon-positivity condition and proves the nonconvex properness, lsc, attainment, and horizon inequality without the earlier extra hypotheses; [`EpiAddition.lean`](RockafellarWets/Chapter3/EpiAddition.lean) supplies the convex equalities. |
| 3.34 | **Exact** | [`EpiCancellation.lean`](RockafellarWets/Chapter3/EpiCancellation.lean) proves cancellation for proper lsc convex extended-real functions under coercivity of the common epi-summand. The proof factors finite tilted infima and cancels the common factor, with no coercivity or full-domain assumption on the left operands. |
| 3.35 | **Exact** | [`SetCancellation.lean`](RockafellarWets/Chapter3/SetCancellation.lean) proves bounded-summand cancellation for nonempty closed convex sets (in fact without using convexity of the common bounded set). |
| 3.36 | **Exact** | [`ExtendedCancellationCompletion.lean`](RockafellarWets/Chapter3/ExtendedCancellationCompletion.lean) defines the genuine extended-real Moreau envelope and proves single-positive-parameter injectivity for proper lsc convex functions, with no coercivity or full-domain assumptions. |
| 3.37 | **Exact** | [`ExtendedProximalCancellationCompletion.lean`](RockafellarWets/Chapter3/ExtendedProximalCancellationCompletion.lean) proves extended-real proximal attainment and constructs a global factor-two Lipschitz selection. [`ExtendedProximalCancellationExact.lean`](RockafellarWets/Chapter3/ExtendedProximalCancellationExact.lean) proves that equality of one positive-parameter proximal mapping is equivalent to the functions differing by a finite constant, for proper lsc convex extended-real functions without coercivity or full-domain assumptions. |
| 3.38 | **Exact** | [`Orderings.lean`](RockafellarWets/Chapter3/Orderings.lean) proves construction, converse representation, closure under limits, and pointedness/antisymmetry. |
| 3.39 | **Exact** | [`MatrixOrderings.lean`](RockafellarWets/Chapter3/MatrixOrderings.lean) specializes all six clauses to the positive-semidefinite matrix order. |
| 3.40 | **Adapted** | [`HomogeneousOperations.lean`](RockafellarWets/Chapter3/HomogeneousOperations.lean) and [`HomogeneousCompletion.lean`](RockafellarWets/Chapter3/HomogeneousCompletion.lean) cover the basic operations. [`HomogeneousSublinearCompletion.lean`](RockafellarWets/Chapter3/HomogeneousSublinearCompletion.lean) gives the exact bottom-regular criterion for sublinearity of epi-addition and a formal counterexample to the unconditional rule under absorbing-`⊥` addition. Indexed unions/infima retain the necessary nonempty-index qualification. |

## Results 3.41–3.55

| Result | Status | Coverage and principal evidence |
| --- | --- | --- |
| 3.41 | **Exact** | [`CosmicConvexity.lean`](RockafellarWets/Chapter3/CosmicConvexity.lean) defines `IsCosmicallyConvex` directly on subsets of the closed-ball `CosmicSpace`. |
| 3.42 | **Exact** | [`CosmicConvexity.lean`](RockafellarWets/Chapter3/CosmicConvexity.lean) proves the exact equivalence with convexity of the associated `cosmicRayCone`. |
| 3.43 | **Exact** | [`CosmicConvexity.lean`](RockafellarWets/Chapter3/CosmicConvexity.lean) proves the extended line-segment principle on closed-ball cosmic sets. |
| 3.44 | **Exact** | [`CosmicConvexity.lean`](RockafellarWets/Chapter3/CosmicConvexity.lean) defines the bespoke `cosmicConvexHull`, proves its universal property, and gives the book's ordinary/direction formula. |
| 3.45 | **Exact** | [`CosmicClosure.lean`](RockafellarWets/Chapter3/CosmicClosure.lean) proves closedness, the horizon formula, and the minimal closed-convex superset property. |
| 3.46 | **Exact** | [`CosmicClosure.lean`](RockafellarWets/Chapter3/CosmicClosure.lean) proves both closure and horizon formulas. |
| 3.47 | **Exact** | [`ConvexHullFunctions.lean`](RockafellarWets/Chapter3/ConvexHullFunctions.lean) proves properness, lsc, coercivity, domain equality, and attainment; [`ConvexHullFunctionSharp.lean`](RockafellarWets/Chapter3/ConvexHullFunctionSharp.lean) proves the sharp `finrank E + 1` representation. |
| 3.48 | **Adapted** | [`PositiveHulls.lean`](RockafellarWets/Chapter3/PositiveHulls.lean) proves both closure formulas and [`HomogeneousCompletion.lean`](RockafellarWets/Chapter3/HomogeneousCompletion.lean) proves the coercive sufficient case. [`PositiveHullExactCompletion.lean`](RockafellarWets/Chapter3/PositiveHullExactCompletion.lean) formally refutes the literal nonconvex full-domain sufficient condition with a continuous finite-valued function on `ℝ²`; the valid full-domain wrapper therefore retains convexity/properness. |
| 3.49 | **Adapted** | [`PositiveHullExactCompletion.lean`](RockafellarWets/Chapter3/PositiveHullExactCompletion.lean) formalizes the mixed-`⊥`/`⊤` counterexample to unconditional sublinearity and proves the exact no-`⊥` correction. [`LowerClosureProperness.lean`](RockafellarWets/Chapter3/LowerClosureProperness.lean) proves the lower closure of every proper convex function is proper, so clause (c) now has no extra hypothesis. The sole adaptation is forced by the project's absorbing-`⊥` convention. |
| 3.50 | **Exact** | [`PositiveHulls.lean`](RockafellarWets/Chapter3/PositiveHulls.lean) proves the gauge formula, lsc, sublinearity, all set identities, and the norm equivalence. |
| 3.51 | **Exact** | [`Entropy.lean`](RockafellarWets/Chapter3/Entropy.lean) proves the simplex and homogeneous entropy properties and positive-hull identity. |
| 3.52 | **Exact** | [`MinkowskiWeyl.lean`](RockafellarWets/Chapter3/MinkowskiWeyl.lean) defines finite homogeneous halfspace representations and proves `isHPolyhedralCone_iff_isFinitelyGeneratedCone`. |
| 3.53 | **Exact** | [`MinkowskiWeyl.lean`](RockafellarWets/Chapter3/MinkowskiWeyl.lean) proves `isHPolyhedral_iff_isPolyhedral`, connecting the halfspace and ordinary-plus-direction generator representations. |
| 3.54 | **Exact** | [`PolyhedralGeneration.lean`](RockafellarWets/Chapter3/PolyhedralGeneration.lean) gives the explicit coefficient infimum, the epigraph equivalence, finite attainment, and the proper one-finite-value clause. |
| 3.55 | **Exact** | [`MinkowskiWeyl.lean`](RockafellarWets/Chapter3/MinkowskiWeyl.lean) and [`PolyhedralOperations/MinkowskiWeylClosures.lean`](RockafellarWets/Chapter3/PolyhedralOperations/MinkowskiWeylClosures.lean) prove every set and function closure operation without the former map/ray hypotheses. The structural `HasClosedPolyhedralEpigraph` layer covers all degenerate cases, while `IsConvexPiecewiseLinear` wrappers state the proper nondegenerate specialization. |

## Regression coverage

[`MinkowskiWeylExamples.lean`](RockafellarWets/Chapter3/MinkowskiWeylExamples.lean)
checks empty, zero, full, simplicial, and non-pointed cones, together with
noninjective, nonsurjective, and zero-map preimages.
[`PolyhedralOperationExamples.lean`](RockafellarWets/Chapter3/PolyhedralOperationExamples.lean)
checks proper max/addition/value-function cases and the all-`⊤` and all-`⊥`
boundary cases.
[`PositiveHullExactCompletion.lean`](RockafellarWets/Chapter3/PositiveHullExactCompletion.lean)
and
[`HomogeneousSublinearCompletion.lean`](RockafellarWets/Chapter3/HomogeneousSublinearCompletion.lean)
contain regression counterexamples for the two absorbing-infinity adaptations.
