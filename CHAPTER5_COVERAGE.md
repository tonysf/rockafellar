# Chapter 5 Coverage Ledger

This ledger tracks Chapter 5 of Rockafellar--Wets, *Set-Valued Mappings*,
result by result. `Exact` means that every substantive mathematical clause is
available under the project's stated finite-dimensional real-space
assumptions. `Adapted` records a mathematically necessary change to a printed
statement, together with a formal explanation or counterexample. `Partial`
records a sound API for only part of the printed result, with the remaining
clauses named. `Missing` means that no result-specific API has yet been
integrated.

Formalization is under way: the conventions for domains, ranges, graphs, and
inverses, formula 5(1), Definition 5.4, and the neighborhood, sequential,
graph, and preimage characterizations of semicontinuity.

The sequential criteria rest on
[`SequentialLimits.lean`](RockafellarWets/Chapter5/SequentialLimits.lean),
which transports the Chapter 4 limits along `atTop` to the limits of formula
5(1) along the neighborhood filter and back.  It is written as reusable
machinery rather than inline to 5.6, since later results in the chapter are
also stated with sequences.

| Status | Count |
| --- | ---: |
| Exact | 8 |
| Missing | 51 |
| **Total** | **59** |

| Result | Status | Lean coverage / remaining work |
|---|---|---|
| 5.1 Constraint systems | Missing | |
| 5.2 Generalized equations and implicit mappings | Missing | |
| 5.3 Algorithmic mappings and fixed points | Missing | |
| 5.4 Continuity and semicontinuity | **Exact** | [`SetLimitsAlong.lean`](RockafellarWets/Chapter5/SetLimitsAlong.lean) restates the Definition 4.1 limits along an arbitrary index filter; [`Semicontinuity.lean`](RockafellarWets/Chapter5/Semicontinuity.lean) defines formula 5(1) along the full neighborhood filter, defines osc, isc, and continuity both absolutely and relative to a set, and proves the equalities the book records immediately afterwards: `lim sup = S(x̄)` under osc, closedness of `S(x̄)` under osc both absolutely and relative to a set `X`, the closed-valued equality form of isc, and that isc at a point of the domain puts a whole neighborhood inside the domain. |
| 5.5 Profile mappings | **Exact** | [`ProfileMappings.lean`](RockafellarWets/Chapter5/ProfileMappings.lean) defines `epiProfile` and `hypoProfile` over the Chapter 1 extended-real conventions and proves `gph Ef = epi f`, `dom Ef = dom f`, `Ef⁻¹(α) = lev≤α f`, that `Ef` is osc at `x̄` iff `f` is lsc at `x̄`, isc iff `f` is usc, continuous iff `f` is continuous, and that the level-set mapping `α ↦ lev≤α f` is osc everywhere iff `f` is lsc everywhere. The hypographical analogues `gph Hf = hypo f`, `dom Hf`, `Hf⁻¹(α) = lev≥α f`, osc iff usc, and isc iff lsc are proved as well. |
| 5.6 Criteria for semicontinuity at a point | **Exact** | [`SemicontinuityCriteria.lean`](RockafellarWets/Chapter5/SemicontinuityCriteria.lean) proves the neighborhood criteria (a) and (b) in the book's `X ∩ V ∩ S⁻¹(W)` form, and the sequential criteria (c) and (d) quantified over all `xν ∈ X` with `xν → x̄` and `S(xν) → D`, relative to `X` and in the absolute case. The sequential clauses go through the diagonal extraction of [`SequentialLimits.lean`](RockafellarWets/Chapter5/SequentialLimits.lean) followed by the subsequence compactness of 4.18. |
| 5.7 Characterizations of semicontinuity | **Exact** | [`SemicontinuityCriteria.lean`](RockafellarWets/Chapter5/SemicontinuityCriteria.lean) proves (a) in full -- osc everywhere is closedness of `gph S`, and `S` is osc exactly when `S⁻¹` is; (b) for closed-valued `S`, as `IsClosed (X ↓∩ S⁻¹(B))` for every compact `B` and equivalently as the closure condition `X ∩ cl(X ∩ S⁻¹(B)) ⊂ S⁻¹(B)`, with the absolute case `X = IRⁿ` separately; and (c) in both the absolute form (`S⁻¹(O)` open for open `O`) and the relative form. The forward half of (b) needs no structure on the target; the converse uses compactness of closed balls and is stated for a proper metric target. |
| 5.8 Feasible-set mappings | **Exact** | [`FeasibleSets.lean`](RockafellarWets/Chapter5/FeasibleSets.lean) defines the parameterized constraint mapping `T`, empty off the parameter set `W`, and proves that `gph T` is closed and hence `T` is osc when `X` and `W` are closed and the constraint functions are continuous on `X × W`; that `T` is osc at every interior point of `W` when `W` is not closed, via the locality of osc and a closed neighborhood inside `W`; and that `dom T` is the set of `w ∈ W` whose constraint system is consistent. |
| 5.9 Inner semicontinuity from convexity | **Exact** | [`ConvexSemicontinuity.lean`](RockafellarWets/Chapter5/ConvexSemicontinuity.lean) defines convex-valuedness and graph-convexity, proves formula 5(4), and proves all three clauses: (a) in the general relative form with the specializations to `dom S` and to the absolute "in particular" statement `(x̄, u) ∈ int(gph S)`, via 4.15 in one direction and closedness of inner limits with `cl(int C) = cl C` in the other; (b) via 4.32(c) applied to the fibre `{x̄} × IRᵐ` intersected with `gph S`, the non-separation hypothesis being interiority of `x̄` in `dom S`; (c) via the inner-limit half of 4.30, both absolutely and relative to a set. |
| 5.10 Parameterized convex constraints | **Exact** | [`ConvexConstraints.lean`](RockafellarWets/Chapter5/ConvexConstraints.lean) proves the printed conclusion: a Slater point at `w₀` yields an explicit open neighborhood of `w₀` on which `T` is continuous. The supporting assertions of the Detail are proved too -- closed graph and hence osc everywhere (needing continuity only, no convexity), convexity of each `T(w)`, openness of the strictly feasible set, and the interior identity `int T(w) = {x | fᵢ(x,w) < 0}` that the book takes from 2.34. Since 2.34 is not available in this project's Chapter 2, inner semicontinuity is obtained instead from density of the strictly feasible set in `T(w)`, proved directly from the Slater segment; the interior identity is then derived from the same computation rather than assumed. |
| 5.11 Continuity of distances | **Exact** | [`DistanceCriteria.lean`](RockafellarWets/Chapter5/DistanceCriteria.lean) proves (a), (b), and (c) relative to a set `X` and in the absolute case, with distances taken as `Metric.infEDist` so that `d(u, ∅) = ∞` as the book requires. Clause (b) needs neither closed-valuedness nor properness; only (a) uses closedness of `S(x̄)` and compactness of closed balls, the latter through the new filter-native compact extraction `outerSetLimitAlong_inter_nonempty_of_frequently` in [`SetLimitsAlong.lean`](RockafellarWets/Chapter5/SetLimitsAlong.lean), which replaces the subsequence step that 4.7 supplies only for sequences. The printed clause (b) reads `u → d(u, S(x))`; this is a misprint for `x → d(u, S(x))`, as clauses (a) and (c) make clear, and the corrected reading is what is proved. |
| 5.12 Uniformity of approximation in semicontinuity | Missing | |
| 5.13 Uniform continuity | Missing | |
| 5.14 Local boundedness | Missing | |
| 5.15 Boundedness of images | Missing | |
| 5.16 Local boundedness of inverses | Missing | |
| 5.17 Level boundedness as local boundedness | Missing | |
| 5.18 Horizon criterion for local boundedness | Missing | |
| 5.19 Outer semicontinuity under local boundedness | Missing | |
| 5.20 Continuity of single-valued mappings | Missing | |
| 5.21 Continuity of locally bounded mappings | Missing | |
| 5.22 Optimal-set mappings | Missing | |
| 5.23 Proximal mappings and projections | Missing | |
| 5.24 Continuity of perturbed mappings | Missing | |
| 5.25 Closedness of images | Missing | |
| 5.26 Horizon criterion for a closed image | Missing | |
| 5.27 Cosmic semicontinuity | Missing | |
| 5.28 Total continuity | Missing | |
| 5.29 Criteria for total continuity | Missing | |
| 5.30 Images of converging sets | Missing | |
| 5.31 Pointwise limits of mappings | Missing | |
| 5.32 Graphical limits of mappings | Missing | |
| 5.33 Graphical limit formulas at a point | Missing | |
| 5.34 Uniformity in graphical convergence | Missing | |
| 5.35 Graphical convergence of projection mappings | Missing | |
| 5.36 Extraction of graphically convergent subsequences | Missing | |
| 5.37 Approximation of generalized equations | Missing | |
| 5.38 Equicontinuity properties | Missing | |
| 5.39 Equicontinuity of single-valued mappings | Missing | |
| 5.40 Graphical versus pointwise convergence | Missing | |
| 5.41 Continuous and uniform limits of mappings | Missing | |
| 5.42 Distance function descriptions of convergence | Missing | |
| 5.43 Continuous versus uniform convergence | Missing | |
| 5.44 Graphical versus continuous convergence | Missing | |
| 5.45 Graphical convergence of single-valued mappings | Missing | |
| 5.46 Graphical convergence from uniform convergence | Missing | |
| 5.47 Arzelà-Ascoli, set-valued version | Missing | |
| 5.48 Uniform convergence of monotone sequences | Missing | |
| 5.49 Metric version of continuous and uniform convergence | Missing | |
| 5.50 Quantification of graphical convergence | Missing | |
| 5.51 Addition of set-valued mappings | Missing | |
| 5.52 Composition of set-valued mappings | Missing | |
| 5.53 Images of converging mappings | Missing | |
| 5.54 Convergence of positive hulls | Missing | |
| 5.55 Generic continuity from semicontinuity | Missing | |
| 5.56 Generic continuity of extended-real-valued functions | Missing | |
| 5.57 Projections as continuous selections | Missing | |
| 5.58 Michael representations of isc mappings | Missing | |
| 5.59 Extensions of continuous selections | Missing | |
