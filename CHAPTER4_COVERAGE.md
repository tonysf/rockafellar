# Chapter 4 Coverage Ledger

This ledger tracks Chapter 4 of Rockafellar--Wets result by result. `Exact`
means that every substantive mathematical clause is available under the
project's stated finite-dimensional real-space assumptions. `Partial` records
a sound API for only part of the printed result. `Missing` means that no
result-specific API has yet been integrated.

The first completed batch contains 16 exact results, three partial results,
and 29 results not yet integrated. Empty-set behavior is built into the
definitions through extended distance; no nonemptiness convention is hidden
in the count.

| Status | Count |
| --- | ---: |
| Exact | 16 |
| Partial | 3 |
| Missing | 29 |
| **Total** | **48** |

| Result | Status | Lean coverage / remaining work |
|---|---|---|
| 4.1 Inner and outer limits | Exact | `outerSetLimit`, `innerSetLimit`, and `PKConverges` use frequent/eventual neighborhood hits along `atTop`. |
| 4.2 Characterizations of set limits | **Exact** | [`SetLimitCharacterizations.lean`](RockafellarWets/Chapter4/SetLimitCharacterizations.lean) gives the tail-union, all-subsequence, open- and closed-thickening formulas; [`SetLimitDistances.lean`](RockafellarWets/Chapter4/SetLimitDistances.lean) gives the exact extended-distance liminf/limsup forms. |
| 4.3 Monotone and sandwiched sequences | **Exact** | [`SetLimitCharacterizations.lean`](RockafellarWets/Chapter4/SetLimitCharacterizations.lean) proves the increasing, decreasing, and sandwich clauses. |
| 4.4 Closedness of limits | **Exact** | [`SetLimits.lean`](RockafellarWets/Chapter4/SetLimits.lean) proves closedness, termwise-closure invariance, and the constant-set specialization. |
| 4.5 Hit-and-miss criteria | **Partial** | [`HitAndMiss.lean`](RockafellarWets/Chapter4/HitAndMiss.lean) proves the open-set, compact-set, open-ball, and closed-ball equivalences. The rational-coordinate countable-ball reduction in 4.5(c) is not yet exposed. |
| 4.6 Index criterion for convergence | **Exact** | [`HitAndMiss.lean`](RockafellarWets/Chapter4/HitAndMiss.lean) proves convergence to the outer limit from the frequent-hit/eventual-hit condition. |
| 4.7 Pointwise convergence of distance functions | **Exact** | [`SetLimitDistances.lean`](RockafellarWets/Chapter4/SetLimitDistances.lean) and [`DistanceConvergence.lean`](RockafellarWets/Chapter4/DistanceConvergence.lean) prove both one-sided inequalities and the pointwise convergence equivalence. |
| 4.8 Equality in distance limits | **Exact** | [`DistanceConvergence.lean`](RockafellarWets/Chapter4/DistanceConvergence.lean) proves the outer-limit equality and sharp inner-limit inequality. |
| 4.9 Set convergence through projections | **Exact** | [`ProjectionConvergence.lean`](RockafellarWets/Chapter4/ProjectionConvergence.lean) proves the general set-valued projection criterion and the single-valued convex specialization. |
| 4.10 Uniformity of approximation | **Partial** | [`UniformApproximation.lean`](RockafellarWets/Chapter4/UniformApproximation.lean) proves both bounded-ball equivalences and the combined convergence criterion. Arbitrary-center, sufficiently-large-radius, and rational-parameter wrappers remain to be exposed. |
| 4.11 Escape to the horizon | **Partial** | [`DistanceConvergence.lean`](RockafellarWets/Chapter4/DistanceConvergence.lean) and [`EscapeToHorizon.lean`](RockafellarWets/Chapter4/EscapeToHorizon.lean) prove the distance, bounded-ball, and both excess-set equivalences. Explicit sufficiently-large-radius and rational-parameter wrappers remain. |
| 4.12 Limits of connected sets | **Exact** | [`ConnectedLimits.lean`](RockafellarWets/Chapter4/ConnectedLimits.lean) proves the bounded connected-set conclusion and a closed-ball strengthening. |
| 4.13 Pompeiu--Hausdorff distance | **Exact** | [`HausdorffConvergence.lean`](RockafellarWets/Chapter4/HausdorffConvergence.lean) gives the extended distance and defining formula; [`ConvexTruncations.lean`](RockafellarWets/Chapter4/ConvexTruncations.lean) proves the unrestricted implication and common-bounded equivalence. |
| 4.14 Limits of cones | **Exact** | [`ConeLimits.lean`](RockafellarWets/Chapter4/ConeLimits.lean) proves the inner, outer, convergent-limit, and nontriviality clauses. |
| 4.15 Limits of convex sets | **Exact** | [`ConvexLimits.lean`](RockafellarWets/Chapter4/ConvexLimits.lean) proves convexity; [`ConvexInternalApproximation.lean`](RockafellarWets/Chapter4/ConvexInternalApproximation.lean) proves eventual interior containment of compact subsets. |
| 4.16 Convergence through convex truncations | **Exact** | [`ConvexTruncations.lean`](RockafellarWets/Chapter4/ConvexTruncations.lean) proves the sufficiently-large-radius Hausdorff truncation equivalence. |
| 4.17 Limits of star-shaped sets | **Exact** | [`StarShapedLimits.lean`](RockafellarWets/Chapter4/StarShapedLimits.lean) defines the nonvacuous book notion and proves bounded-limit preservation. |
| 4.18 Extraction of convergent subsequences | **Exact** | [`SetConvergenceCompactness.lean`](RockafellarWets/Chapter4/SetConvergenceCompactness.lean) proves the escaping/nonempty-convergent-subsequence dichotomy. |
| 4.19 Cluster description of limits | **Exact** | [`ClusterLimits.lean`](RockafellarWets/Chapter4/ClusterLimits.lean) identifies the inner limit with the intersection and the outer limit with the union of all subsequential set limits. |
| 4.20 Cosmic limits through horizon limits | Missing | Blocked on the exact closed-ball cosmic bridge. |
| 4.21 Properties of horizon limits | Missing | Blocked on 4.20. |
| 4.22 Eventually bounded sequences | Missing | Blocked on 4.20. |
| 4.23 Total set convergence | Missing | Blocked on 4.20. |
| 4.24 Horizon criterion for total convergence | Missing | Blocked on 4.20. |
| 4.25 Automatic cases of total convergence | Missing | Blocked on 4.20. |
| 4.26 Convergence of images | Missing | |
| 4.27 Total convergence of linear images | Missing | |
| 4.28 Projections of convex sets | Missing | |
| 4.29 Products and sums | Missing | |
| 4.30 Convergence of convex hulls | Missing | |
| 4.31 Convergence of unions | Missing | |
| 4.32 Solutions to convex systems | Missing | |
| 4.33 Convergence of convex intersections | Missing | |
| 4.34 Distance function relations | Missing | |
| 4.35 Uniform convergence of distance functions | Missing | |
| 4.36 Quantification of set convergence | Missing | |
| 4.37 Distance estimates | Missing | |
| 4.38 Pompeiu--Hausdorff distance as a limit | Missing | |
| 4.39 Distance between convex truncations | Missing | |
| 4.40 Properties of Pompeiu--Hausdorff distance | Missing | |
| 4.41 Integrated set-distance estimates | Missing | |
| 4.42 Metric description of set convergence | Missing | |
| 4.43 Local compactness of the set hyperspace | Missing | |
| 4.44 Distances between cones | Missing | |
| 4.45 Separability and finite-set approximation | Missing | |
| 4.46 Metric description of cosmic set convergence | Missing | |
| 4.47 Metric description of total set convergence | Missing | |
| 4.48 Cosmic metric properties | Missing | |

## Verification cases

The Chapter 4 regression suite will cover constant, increasing, decreasing,
sandwiched, and alternating sequences; alternating `∅`/`univ`; convergent
singletons; and pointwise closure replacement. The basic constant, empty,
full, monotone, sandwich, and closure-replacement laws are already theorem
checked in the foundational modules.
