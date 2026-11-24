/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Monotone Mappings

Set-valued mappings `T : ℝⁿ ⇉ ℝⁿ` are functions `T : E → Set E` on a real inner
product space `E`, with the graph, inverse, domain and range of Chapter 5.
The foundational module `MonotoneMappings` provides the core declarations of
Definitions 12.1 and 12.5:

* `RW.SvMonotone`, `RW.SvStrictlyMonotone` (Definition 12.1);
* `RW.SvMaximalMonotone`, `RW.SvMaximalMonotoneLocallyAt` (Definition 12.5),
  with `RW.svMaximalMonotone_iff_no_enlargement` identifying the pointwise
  criterion with the absence of monotone graph enlargements.

The ledger `CHAPTER12_COVERAGE.md` records the status of every numbered result.
-/

import RockafellarWets.Chapter12.AffineMonotonicity
import RockafellarWets.Chapter12.ContinuousMaximality
import RockafellarWets.Chapter12.ConvexConcaveMonotonicity
import RockafellarWets.Chapter12.ConvexSubgradientConvergence
import RockafellarWets.Chapter12.ConvexSubgradientMappings
import RockafellarWets.Chapter12.CyclicalMonotonicity
import RockafellarWets.Chapter12.DifferentiableMonotonicity
import RockafellarWets.Chapter12.DisplacementMappings
import RockafellarWets.Chapter12.DoubleEnvelopes
import RockafellarWets.Chapter12.EpsilonSubgradients
import RockafellarWets.Chapter12.GenericSingleValuedness
import RockafellarWets.Chapter12.Hypomonotonicity
import RockafellarWets.Chapter12.MaximalExtensions
import RockafellarWets.Chapter12.MaximalMonotoneComposition
import RockafellarWets.Chapter12.MaximalMonotoneGraphs
import RockafellarWets.Chapter12.MaximalMonotoneStructure
import RockafellarWets.Chapter12.MintyParameterization
import RockafellarWets.Chapter12.MonotoneContinuity
import RockafellarWets.Chapter12.MonotoneDomains
import RockafellarWets.Chapter12.MonotoneGraphicalConvergence
import RockafellarWets.Chapter12.MonotoneMappings
import RockafellarWets.Chapter12.MonotoneNonexpansiveCorrespondence
import RockafellarWets.Chapter12.MonotoneOperations
import RockafellarWets.Chapter12.MonotoneProtoDerivatives
import RockafellarWets.Chapter12.MonotoneRangesGrowth
import RockafellarWets.Chapter12.MonotoneSemidifferentiability
import RockafellarWets.Chapter12.MonotoneSolutionSets
import RockafellarWets.Chapter12.MonotoneVariationalInequalities
import RockafellarWets.Chapter12.MoreauYosida
import RockafellarWets.Chapter12.NonexpansiveMappings
import RockafellarWets.Chapter12.OneDimensionalCyclicalMonotonicity
import RockafellarWets.Chapter12.OneDimensionalMonotonicity
import RockafellarWets.Chapter12.PiecewiseLinearQuadraticSubgradients
import RockafellarWets.Chapter12.PiecewisePolyhedralMonotonicity
import RockafellarWets.Chapter12.ProjectionMonotonicity
import RockafellarWets.Chapter12.ProximalMappingMonotonicity
import RockafellarWets.Chapter12.ResolventMaximality
import RockafellarWets.Chapter12.Resolvents
import RockafellarWets.Chapter12.SaddlePointInequalities
import RockafellarWets.Chapter12.StrongConvexity
import RockafellarWets.Chapter12.StrongConvexityDuality
import RockafellarWets.Chapter12.StrongConvexityMonotonicity
import RockafellarWets.Chapter12.StrongMonotonicity
import RockafellarWets.Chapter12.SubspaceConeProjections
import RockafellarWets.Chapter12.YosidaRegularization
