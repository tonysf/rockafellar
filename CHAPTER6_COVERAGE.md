# Chapter 6 Coverage Ledger

This ledger tracks Chapter 6 of Rockafellar--Wets, *Variational Geometry*,
result by result.  `Exact` means that every substantive mathematical clause is
available under the project's stated finite-dimensional real-space
assumptions.  `Adapted` records a mathematically necessary change to a printed
statement, together with a formal explanation or counterexample.  `Partial`
records a sound API for only part of the printed result, with the remaining
clauses named.  `Missing` means that no result-specific API has yet been
integrated.

Formalization has started at Section A, the tangent cones of 6.1 and 6.2.

The chapter's limits are Painleve--Kuratowski limits indexed by a *scaling
parameter* rather than by an argument, so nothing new is needed to state them:
the filter-native set limits of
[`SetLimitsAlong.lean`](RockafellarWets/Chapter5/SetLimitsAlong.lean), written
for formula 5(1) along an arbitrary index filter, are used here along
`𝓝[>] 0` on `ℝ`.  That is why 6.2 costs only the two identifications and
inherits closedness of both cones from Chapter 5.

| Status | Count |
| --- | ---: |
| Exact | 2 |
| Missing | 47 |
| **Total** | **49** |

| Result | Status | Lean coverage / remaining work |
|---|---|---|
| 6.1 Tangent vectors and geometric derivability | **Exact** | [`TangentCones.lean`](RockafellarWets/Chapter6/TangentCones.lean) defines the tangent cone by formula 6(2), the derivable tangent vectors by the path condition, and geometric derivability as the inclusion of the first in the second.  The path `ξ : [0, ε] → C` is carried as a total function `ℝ → E` constrained on `[0, ε]`, and its right derivative at `0` as a limit along `𝓝[>] 0`, which is what the book's `ξ'₊(0)` means; **no continuity of `ξ` away from `0` is asked, exactly as printed**, and that is what makes the hard half of 6.2 provable at all.  The convergence `xν →_C x̄` printed alongside `[xν - x̄]/τν → w` in 6(2) is redundant -- the differences are `τν` times a convergent sequence -- so `mem_tangentCone_of_forall` is supplied as a constructor that does not ask for it, and the definition keeps the printed form. |
| 6.2 Tangent cone properties | **Exact** | [`TangentCones.lean`](RockafellarWets/Chapter6/TangentCones.lean) proves every clause.  Formula 6(3) is the identification of Definition 6.1 with `outerSetLimitAlong (𝓝[>] 0)` of the magnified difference sets `τ ↦ τ⁻¹(C - x̄)`, and the derivable vectors with `innerSetLimitAlong` of the same family; closedness of both cones is then `isClosed_outerSetLimitAlong` and `isClosed_innerSetLimitAlong` from [`SetLimitsAlong.lean`](RockafellarWets/Chapter5/SetLimitsAlong.lean), and the concluding clause -- geometric derivability is convergence of `[C - x̄]/τ` as `τ ↓ 0` -- is equality of the two limits.  **The Chapter 5 set limits transfer with no change**: they were written along an arbitrary index filter for formula 5(1), and here the index is the scaling parameter rather than the argument.  Both cones are shown to be cones in the Chapter 3 sense, the zero vector coming from the constant sequence at `x̄` and the rescaling of `w` by `c > 0` from rescaling `τν` by `1/c`, respectively from reparameterizing the path by `t ↦ ct`.  The one substantive direction is that an inner-limit vector is *derivable*, where a path has to be produced: it is chosen one point per `τ`, within `τ` of the best point of `τ⁻¹(C - x̄)` available, so the error is at most `d(w, τ⁻¹(C - x̄)) + τ` and both terms vanish -- the slack device of the pointwise selection remark before 5.57.  **`x̄ ∈ C` is needed only for the derivable half**, since `ξ(0) = x̄` forces it while the inner limit puts `x̄` only in `cl C`; formula 6(3) itself is proved at every `x̄`.  The unnumbered Figure 6-4 example of a set whose tangent cone is a half-plane while its derivable cone is `{0}` is not formalized. |
| 6.3 Normal vectors | Missing | |
| 6.4 Clarke regularity of sets | Missing | |
| 6.5 Normal cone properties | Missing | |
| 6.6 Limits of normal vectors | Missing | |
| 6.7 Change of coordinates | Missing | |
| 6.8 Tangents and normals to smooth manifolds | Missing | |
| 6.9 Tangents and normals to convex sets | Missing | |
| 6.10 Tangents and normals to boxes | Missing | |
| 6.11 Gradient characterization of regular normals | Missing | |
| 6.12 Basic first-order conditions for optimality | Missing | |
| 6.13 Variational inequalities and complementarity | Missing | |
| 6.14 Normal cones to sets with constraint structure | Missing | |
| 6.15 Lagrange multipliers | Missing | |
| 6.16 Proximal normals | Missing | |
| 6.17 Proximality of normals to convex sets | Missing | |
| 6.18 Approximation of normals | Missing | |
| 6.19 Characterization of boundary points | Missing | |
| 6.20 Envelope representation of convex sets | Missing | |
| 6.21 Polarity correspondence | Missing | |
| 6.22 Pointedness and polarity | Missing | |
| 6.23 Orthogonal subspaces | Missing | |
| 6.24 Polarity of normals and tangents to convex sets | Missing | |
| 6.25 Regular tangent vectors | Missing | |
| 6.26 Regular tangent cone properties | Missing | |
| 6.27 Normals to tangent cones | Missing | |
| 6.28 Tangent-normal polarity | Missing | |
| 6.29 Characterizations of Clarke regularity | Missing | |
| 6.30 Consequences of Clarke regularity | Missing | |
| 6.31 Tangent cones to sets with constraint structure | Missing | |
| 6.32 Regular tangents under a change of coordinates | Missing | |
| 6.33 Recession vectors | Missing | |
| 6.34 Recession cones and convexity | Missing | |
| 6.35 Recession vectors from tangents and normals | Missing | |
| 6.36 Interior tangents and recession | Missing | |
| 6.37 Internal approximation in tangent limits | Missing | |
| 6.38 Convexified normal and tangent cones | Missing | |
| 6.39 Constraint qualification in tangent cone form | Missing | |
| 6.40 Mangasarian-Fromovitz constraint qualification | Missing | |
| 6.41 Tangents and normals to product sets | Missing | |
| 6.42 Tangents and normals to intersections | Missing | |
| 6.43 Tangents and normals to image sets | Missing | |
| 6.44 Tangents and normals under set addition | Missing | |
| 6.45 Polars of polyhedral cones; Farkas | Missing | |
| 6.46 Tangents and normals to polyhedral sets | Missing | |
| 6.47 Exactness of tangent approximations | Missing | |
| 6.48 Separation of convex cones | Missing | |
| 6.49 Generic continuity of normal-cone mappings | Missing | |
