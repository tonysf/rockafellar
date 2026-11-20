/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Convex qualifications for partial differentiation and parametric stationarity
-/

import RockafellarWets.Chapter10.PartialSubgradients
import RockafellarWets.Chapter10.ConvexChainQualification

open Set
open scoped InnerProductSpace

namespace RW

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ P]
  {f : WithLp 2 (E × P) → EReal} {x : E} {p : P} {c : ℝ}

/-- **Corollary 10.11**, the convex nonseparation alternative for the
affine slice with the parameter fixed. -/
theorem convex_partialQualification_iff_not_separated
    (hc : Convex ℝ (epigraph f)) (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hx : f (WithLp.toLp 2 (x,p)) = c) :
    (∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) ↔
      ¬ HasSeparatingLinearizationNormal (effectiveDomain f) (WithLp.toLp 2 (x,p))
        (partialEmbeddingDerivative (E := E) (P := P)) := by
  rw [← convex_chainQualification_iff_not_separated hc hp hl hx]
  constructor
  · intro h q hq he
    rw [partialEmbeddingDerivative_adjoint] at he
    have hy := h q.snd (by simpa only [← he] using hq)
    apply WithLp.ofLp_injective
    exact Prod.ext he hy
  · intro h y hy
    have he := h (WithLp.toLp 2 ((0:E),y)) hy (by simp)
    exact congrArg WithLp.snd he

/-- **Example 10.12**, the convex qualification excludes precisely the
supporting half-spaces whose nonzero normals lie in the parameter space. -/
theorem convex_partialQualification_iff_no_vertical_support
    (hc : Convex ℝ (epigraph f)) (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hx : f (WithLp.toLp 2 (x,p)) = c) :
    (∀ y, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,p)) → y = 0) ↔
      ¬ ∃ y : P, y ≠ 0 ∧ ∀ q ∈ effectiveDomain f, ⟪y,q.snd-p⟫_ℝ ≤ 0 := by
  have hh := horizonSubdifferential_eq_normalCone_domain_of_locallyLsc hc hp
    (locallyLscAt_of_lowerSemicontinuous_finite hl hx) hx
  have hxD : WithLp.toLp 2 (x,p) ∈ effectiveDomain f := hx.trans_lt (EReal.coe_lt_top _)
  rw [hh,normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph hc) hxD]
  have he (y : P) (q : WithLp 2 (E × P)) :
      ⟪WithLp.toLp 2 ((0:E),y),q-WithLp.toLp 2 (x,p)⟫_ℝ = ⟪y,q.snd-p⟫_ℝ := by
    change ⟪(0:E),q.fst-x⟫_ℝ+⟪y,q.snd-p⟫_ℝ = _
    simp
  simp only [mem_setOf_eq,he]
  constructor
  · intro h ⟨y,hy,hs⟩
    exact hy (h y hs)
  · intro h y hy
    by_contra he
    exact h ⟨y,he,hy⟩

end RW
