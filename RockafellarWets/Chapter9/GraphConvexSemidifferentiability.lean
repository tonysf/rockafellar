/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semidifferentiability of graph-convex mappings
-/

import RockafellarWets.Chapter9.GraphConvexStrictContinuity
import RockafellarWets.Chapter9.SemidifferentiabilityFromAubin

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {x : E} {u : F}

/-- **Example 9.52.** A closed, convex graph gives a semiderivative at every
interior-domain input and every associated output. -/
theorem SvGraphConvex.hasMappingSemiderivative (hc : SvGraphConvex S) (ho : SvOsc S)
    (hx : x ∈ interior (svDom S)) (hu : u ∈ S x) :
    HasMappingSemiderivative S x u (graphicalDerivative S x u) :=
  (hc.svStrictlyContinuousAt (fun a ↦ (ho a).isClosed) hx).hasMappingSemiderivative_of_regular hu
    (isGraphicallyRegularAt_of_graphConvex_of_osc hc ho hu)

end RW
