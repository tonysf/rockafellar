# Chapter 6 Coverage Ledger

This ledger tracks Chapter 6 of Rockafellar--Wets, *Variational Geometry*,
result by result.  `Exact` means that every substantive mathematical clause is
available under the project's stated finite-dimensional real-space
assumptions.  `Adapted` records a mathematically necessary change to a printed
statement, together with a formal explanation or counterexample.  `Partial`
records a sound API for only part of the printed result, with the remaining
clauses named.  `Missing` means that no result-specific API has yet been
integrated.

Formalization covers Sections A and B, results 6.1 through 6.6, together with
6.9 and the tangent cone clause of 6.7 from Section C.  6.9 is taken ahead of
6.7 deliberately: it is self-contained, resting only on Sections A and B,
whereas 6.7 is a surjective inverse-function-theorem argument.  Of 6.7 itself
only the tangent cone formula is proved; the two normal cone formulas are
blocked twice over, once because Mathlib's plain product `F × ker ∇F(x̄)`
carries the sup norm and so has no adjoint, and once because the alternative
route from the tangent formula is the polarity `(A⁻¹K)° = A*(K°)` that the
book itself does not establish until 6.21 and 6.45.

The chapter's limits are Painleve--Kuratowski limits indexed by a *scaling
parameter* rather than by an argument, so nothing new is needed to state them:
the filter-native set limits of
[`SetLimitsAlong.lean`](RockafellarWets/Chapter5/SetLimitsAlong.lean), written
for formula 5(1) along an arbitrary index filter, are used here along
`𝓝[>] 0` on `ℝ`.  That is why 6.2 costs only the two identifications and
inherits closedness of both cones from Chapter 5.  Section B is the same story
one level up: the general normal cone of 6.3 *is* the relative outer limit
`svOuterLimitWithin (regularNormalCone C) C x̄` of formula 5(1) applied to the
regular normal cone mapping, so 6.5's closedness is
`isClosed_outerSetLimitAlong` and 6.6 is the statement that a relative outer
limit absorbs a second application of itself.

**Ambient setting.**  Section A is stated over
`[NormedAddCommGroup E] [NormedSpace ℝ E]`, since tangency is a statement
about difference quotients and needs no pairing.  Section B needs one, and
takes `[InnerProductSpace ℝ E]`, the setting already used in Chapters 1--3;
a dual-space pairing was rejected because it would fork every normal-cone
statement between `E` and `E →L[ℝ] ℝ` for no gain in a book written in
`IRⁿ`, where the two are identified throughout.  Section A is left exactly as
it was: an inner product space is a normed space, so the tangent cones apply
unchanged.  `[FiniteDimensional ℝ E]` is *not* a standing assumption of the
Section B module; it is asked for by name in the one place the book's proofs
use it, the implication `⇐` of 6(6), where unit-length difference quotients
are made to converge along a subsequence.

**The convention 6(8).**  Formula 6(8) sets `N_C(x̄) = N̂_C(x̄) = ∅` for
`x̄ ∉ C`.  This is carried definitionally, by the conjunct `x̄ ∈ C` in both
definitions, rather than by a case split at each use.  Without it the `ε`
inequality of 6(5) would hold *vacuously* at every `x̄ ∉ cl C`, since
`𝓝[C] x̄` is then the trivial filter, and `N̂_C(x̄)` would come out as the
whole space.  The convention earns its place immediately: it is what makes
`dom N_C = dom N̂_C = C` true, what lets the relative outer limit of 6(7) be
replaced by the full one, and what makes the closed-set graph formula
`gph N_C = cl(gph N̂_C)` come out.

| Status | Count |
| --- | ---: |
| Exact | 7 |
| Partial | 1 |
| Missing | 41 |
| **Total** | **49** |

| Result | Status | Lean coverage / remaining work |
|---|---|---|
| 6.1 Tangent vectors and geometric derivability | **Exact** | [`TangentCones.lean`](RockafellarWets/Chapter6/TangentCones.lean) defines the tangent cone by formula 6(2), the derivable tangent vectors by the path condition, and geometric derivability as the inclusion of the first in the second.  The path `ξ : [0, ε] → C` is carried as a total function `ℝ → E` constrained on `[0, ε]`, and its right derivative at `0` as a limit along `𝓝[>] 0`, which is what the book's `ξ'₊(0)` means; **no continuity of `ξ` away from `0` is asked, exactly as printed**, and that is what makes the hard half of 6.2 provable at all.  The convergence `xν →_C x̄` printed alongside `[xν - x̄]/τν → w` in 6(2) is redundant -- the differences are `τν` times a convergent sequence -- so `mem_tangentCone_of_forall` is supplied as a constructor that does not ask for it, and the definition keeps the printed form. |
| 6.2 Tangent cone properties | **Exact** | [`TangentCones.lean`](RockafellarWets/Chapter6/TangentCones.lean) proves every clause.  Formula 6(3) is the identification of Definition 6.1 with `outerSetLimitAlong (𝓝[>] 0)` of the magnified difference sets `τ ↦ τ⁻¹(C - x̄)`, and the derivable vectors with `innerSetLimitAlong` of the same family; closedness of both cones is then `isClosed_outerSetLimitAlong` and `isClosed_innerSetLimitAlong` from [`SetLimitsAlong.lean`](RockafellarWets/Chapter5/SetLimitsAlong.lean), and the concluding clause -- geometric derivability is convergence of `[C - x̄]/τ` as `τ ↓ 0` -- is equality of the two limits.  **The Chapter 5 set limits transfer with no change**: they were written along an arbitrary index filter for formula 5(1), and here the index is the scaling parameter rather than the argument.  Both cones are shown to be cones in the Chapter 3 sense, the zero vector coming from the constant sequence at `x̄` and the rescaling of `w` by `c > 0` from rescaling `τν` by `1/c`, respectively from reparameterizing the path by `t ↦ ct`.  The one substantive direction is that an inner-limit vector is *derivable*, where a path has to be produced: it is chosen one point per `τ`, within `τ` of the best point of `τ⁻¹(C - x̄)` available, so the error is at most `d(w, τ⁻¹(C - x̄)) + τ` and both terms vanish -- the slack device of the pointwise selection remark before 5.57.  **`x̄ ∈ C` is needed only for the derivable half**, since `ξ(0) = x̄` forces it while the inner limit puts `x̄` only in `cl C`; formula 6(3) itself is proved at every `x̄`.  The unnumbered Figure 6-4 example of a set whose tangent cone is a half-plane while its derivable cone is `{0}` is not formalized. |
| 6.3 Normal vectors | **Exact** | [`NormalCones.lean`](RockafellarWets/Chapter6/NormalCones.lean) defines `regularNormalCone` by formula 6(4) and `normalCone` by the sequential clause of 6.3, then proves the identification `normalCone C x̄ = svOuterLimitWithin (regularNormalCone C) C x̄` that formula 6(7) records.  **6(4) is formalized as 6(5)**, in the filter form `∀ ε > 0, ∀ᶠ y in 𝓝[C] x̄, ⟨v, y - x̄⟩ ≤ ε‖y - x̄‖`, with `mem_regularNormalCone_iff` giving the `ε`-`δ` reading: the book's `o(|x - x̄|)` is not a function but a property, and the text states outright that 6(4) *means* 6(5), the two being equivalent because `max{0, ⟨v, x - x̄⟩}` is the `o` term.  The base point `x̄` may be taken in the closure of `C` without harm; excluding `x = x̄` from 6(5), as the book does, changes nothing, both sides of the inequality vanishing there.  The convergence `xν →_C x̄` printed in the sequential clause asks `xν ∈ C` separately, but that is already carried by `vν ∈ N̂_C(xν)` under the convention 6(8), so `mem_normalCone_of_forall` is supplied as a constructor that does not ask for it, as `mem_tangentCone_of_forall` is in 6.1.  The identification is proved directly in both directions rather than through the Chapter 5 sequential bridge, one point `(xν, vν)` chosen per `ν` within `1/(ν+1)` of `x̄` and of `v`; the bridge would have produced a subsequence to discard afterwards. |
| 6.4 Clarke regularity of sets | **Exact** | [`NormalCones.lean`](RockafellarWets/Chapter6/NormalCones.lean) defines `IsClarkeRegularAt` as printed, the conjunction of local closedness at `x̄` with `N_C(x̄) = N̂_C(x̄)`, and `isClarkeRegularAt_iff` records that only the inclusion `N_C(x̄) ⊆ N̂_C(x̄)` is at issue, the reverse being 6(7).  Local closedness at a point is the book's notion from the paragraph opening Chapter 1I* -- `C ∩ V` closed for some closed neighborhood `V` of `x̄`, which need not meet `C` -- and had no definition in the repository, so `IsLocallyClosedAt` is introduced here.  It is deliberately *not* Mathlib's `IsLocallyClosed`, which asks a set to be the intersection of an open set with a closed one and is a different notion; `IsClosed.isLocallyClosedAt` records the book's remark that a closed set is locally closed everywhere. |
| 6.5 Normal cone properties | **Exact** | [`NormalCones.lean`](RockafellarWets/Chapter6/NormalCones.lean) proves every clause: both sets are cones, `N_C(x̄)` is closed, `N̂_C(x̄)` is closed and convex, formula 6(6) characterizes `N̂_C(x̄)` against the tangent cone, and formula 6(7) is the identification proved at 6.3, with `N̂_C(x̄) ⊆ N_C(x̄)` from the constant sequence.  Closedness of `N_C(x̄)` is `isClosed_outerSetLimitAlong` through 6(7), exactly as the book has it.  **Convexity and closedness of `N̂_C(x̄)` are proved directly from 6(5), not through 6(6) as the book routes them**: a convex combination of two vectors satisfying the `ε` inequality satisfies it with the same `ε`, and a vector within `ε/2` of one satisfying the `ε/2` inequality satisfies the `ε` one by Cauchy--Schwarz.  The point of the detour is that both statements are then dimension-free, whereas the book's route through 6(6) would import compactness of the unit ball into two facts that do not need it.  6(6) itself splits accordingly: `⇒` holds in any inner product space, while `⇐` is stated with `[FiniteDimensional ℝ E]`.  That is not a hypothesis added to the printed statement -- it is the book's ambient `IRⁿ`, and it is used for precisely the step the printed proof takes, normalizing `[xν - x̄]/|xν - x̄|` to unit length and passing to a convergent subsequence.  `regularNormalCone_eq_iInter` records 6(6) in the form the book's convexity argument uses, as an intersection of closed half-spaces.  The figures 6-5 and 6-6, and the accompanying remark that the inward corner point is derivable without being regular, are not formalized. |
| 6.6 Limits of normal vectors | **Exact** | [`NormalCones.lean`](RockafellarWets/Chapter6/NormalCones.lean) proves both readings: `mem_normalCone_of_tendsto` is the printed sequential statement and `svOscWithinAt_normalCone` is the `In other words` clause, outer semicontinuity of `N_C` at `x̄` relative to `C` in the sense of Definition 5.4, with `svOscOn_normalCone` for the whole of `C`.  **The proof is not the book's.**  The book argues that `gph N_C` is the closure of `gph N̂_C` in `C × IRⁿ` and hence closed there; formalized through 6(7), the statement is instead that a relative outer limit absorbs a second application of itself, `svOuterLimitWithin_svOuterLimitWithin_subset`, which is a fact about formula 5(1) in any topological space and needs no product topology, no metric and no sequences.  The book's closure form is then proved separately, as `svGraph_normalCone`, for a closed `C`, together with the other two claims of the paragraph after 6.6: `dom N_C = dom N̂_C = C`, and `N_C(x̄) = lim sup_{x → x̄} N̂_C(x)` along the *full* neighborhood filter.  The last of these is split, since `normalCone_eq_svOuterLimit_of_mem` shows it needs no closedness at points of `C` -- emptiness of `N̂_C` off `C` already forces the relative and full outer limits to agree -- and closedness of `C` is used only to make both sides empty off `C`.  `x̄ ∈ C` is a hypothesis throughout: it is what writing `N_C(x̄)` presupposes in Definition 6.3, and what the book's own `closed relative to C × IRⁿ` says. |
| 6.7 Change of coordinates | **Partial** | [`ChangeOfCoordinates.lean`](RockafellarWets/Chapter6/ChangeOfCoordinates.lean) proves the **tangent cone formula** `T_C(x̄) = {w | ∇F(x̄)w ∈ T_D(ū)}`, by the book's guide with the basis replaced by a projection: where the guide picks `a₁, …, a_{n-m}` spanning `ker ∇F(x̄)` and appends the linear forms `⟨aᵢ, ·⟩` to make the Jacobian square, `tangentCone_preimage_of_surjective` appends the orthogonal projection `P` onto that kernel, so that `Φ = (G, P)` has the bijective derivative `∇F(x̄) × P` and `C = Φ⁻¹(D × ker ∇F(x̄))` holds globally, not merely near `x̄`.  The change of coordinates itself is `tangentCone_preimage`, proved from the inverse function theorem in the form Mathlib supplies it: the inclusion `⊆` pushes tangent vectors forward through `Φ`, and `⊇` pushes them forward through the local inverse, whose image lands in `Φ⁻¹(S)` only near the point, which is where `tangentCone_inter_nhds` -- the locality of the tangent cone -- is used.  The supporting lemmas are stated for their own sake and reused later: monotonicity, locality, the push-forward `∇H(x̄)(T_A(x̄)) ⊆ T_{H(A)}(H(x̄))` through any differentiable `H`, and `T_{S × IRᵏ} = T_S × IRᵏ`, which needs the free coordinate to move along the *same* scalings.  Everything is proved for real Hilbert spaces, finite-dimensionality never being used.  **The two normal cone formulas are outstanding**: `N_C(x̄) = ∇F(x̄)*(N_D(ū))` and `N̂_C(x̄) = ∇F(x̄)*(N̂_D(ū))`.  Transporting regular normals through the same augmentation needs an adjoint on the augmented target, and Mathlib's plain product `F × ker ∇F(x̄)` carries the sup norm, so it is not an inner product space -- that structure lives on `WithLp 2 (F × ker ∇F(x̄))`.  Deducing them instead from the tangent formula is the polarity `(A⁻¹K)° = A*(K°)`, which needs a separation theorem and closedness of `A*(K°)`, and which the book itself defers to 6.21 and 6.45; the general normal cone additionally needs a uniform-injectivity argument at the neighboring points where `∇F` is evaluated. |
| 6.8 Tangents and normals to smooth manifolds | Missing | The book derives this from 6.7 with `D = {0}`, so it waits on 6.7. |
| 6.9 Tangents and normals to convex sets | **Exact** | [`ConvexSets.lean`](RockafellarWets/Chapter6/ConvexSets.lean) proves every clause.  The set `K` of the printed proof is named `radialCone C x̄`, the directions `w` with `x̄ + λw ∈ C` for some `λ > 0`; it is shown convex for convex `C` and open for open `C`.  Geometric derivability, `T_C(x̄) = cl K` and the same formula for the derivable cone all come from the sandwich `K ⊆ D_C(x̄) ⊆ T_C(x̄) ⊆ cl K`, whose left-hand inclusion is the straight path `t ↦ x̄ + tw` -- admissible because Definition 6.1 asks no continuity of the path away from `0`, and in `C` by convexity -- and whose right-hand inclusion holds for every set, each difference quotient of 6(2) being itself a radial direction.  **The normal cone formula is proved without 6(6)**, and so without finite-dimensionality: `⟨v, x - x̄⟩ ≤ 0` for all `x ∈ C` gives 6(4) with any `ε` at all, while conversely `x - x̄` is a radial direction and hence a tangent vector, so the `⇒` half of 6(6), which is dimension-free, applies.  `N_C(x̄) = N̂_C(x̄)` is then the book's limit argument, `⟨vν, x - xν⟩ ≤ 0` passing to the limit; local closedness plays no part in it and enters only through Definition 6.4, exactly as the concluding sentence of 6.9 says.  The interior formula is the one clause needing `[FiniteDimensional ℝ E]`: when `int C ≠ ∅` it is `cl K = cl K₀` -- from `C ⊆ cl(int C)`, which is 2.33 -- followed by `int(cl K₀) = int K₀ = K₀` for the convex *open* set `K₀`, and when `int C = ∅` it is the statement that `cl K` then has empty interior, which is false in infinite dimensions and here comes from `span(C - x̄)` being closed and from a convex set with `aff C = IRⁿ` having interior points.  Figure 6-8 and the supporting-halfspace remark are not formalized. |
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
