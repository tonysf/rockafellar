/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lipschitzian meaning of the parameter constraint qualification

Proposition 10.16: the horizontal horizon qualification is exactly the
Aubin property of the mapping from a parameter to its slice epigraph.
-/

import RockafellarWets.Chapter10.ParametricEpigraphProjection
import RockafellarWets.Chapter9.ImplicitGraphPermutations
import RockafellarWets.Chapter8.SubderivativeRegularityCriterion

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {E P : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The epigraph of the decision-variable slice at a parameter. -/
def parametricEpigraphMapping (f : WithLp 2 (E × P) → EReal) (u : P) : Set (WithLp 2 (E × ℝ)) :=
  {q | f (WithLp.toLp 2 (q.fst,u)) ≤ (q.snd : EReal)}

/-- The orthogonal coordinate permutation `(u,x,a) ↦ (x,u,a)`. -/
def parametricEpigraphPermutation :
    WithLp 2 (P × WithLp 2 (E × ℝ)) ≃ₗᵢ[ℝ] WithLp 2 (WithLp 2 (E × P) × ℝ) :=
  (LinearIsometryEquiv.withLpProdAssoc 2 ℝ P E ℝ).symm.trans
    (LinearIsometryEquiv.withLpProdCongr 2
      (LinearIsometryEquiv.withLpProdComm 2 ℝ P E) (LinearIsometryEquiv.refl ℝ ℝ))

@[simp] theorem parametricEpigraphPermutation_apply (q : WithLp 2 (P × WithLp 2 (E × ℝ))) :
    parametricEpigraphPermutation q = WithLp.toLp 2 (WithLp.toLp 2 (q.snd.fst,q.fst),q.snd.snd) := rfl

theorem euclideanSvGraph_parametricEpigraphMapping (f : WithLp 2 (E × P) → EReal) :
    euclideanSvGraph (parametricEpigraphMapping f) =
      parametricEpigraphPermutation ⁻¹' euclideanEpigraph f := rfl

theorem isClosed_svGraph_parametricEpigraphMapping {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) : IsClosed (svGraph (parametricEpigraphMapping f)) := by
  have he : svGraph (parametricEpigraphMapping f) =
      (fun q : P × WithLp 2 (E × ℝ) ↦ (WithLp.toLp 2 (q.2.fst,q.1),q.2.snd)) ⁻¹' epigraph f := rfl
  rw [he]
  apply (isClosed_epigraph_of_lsc_ereal f hl).preimage
  fun_prop

/-- The zero-input coderivative is exactly the horizontal horizon slice. -/
theorem coderivative_parametricEpigraphMapping_zero {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) {x : E} {u : P} {a : ℝ}
    (hx : f (WithLp.toLp 2 (x,u)) = a) :
    coderivative (parametricEpigraphMapping f) u (WithLp.toLp 2 (x,a)) 0 =
      {y | WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,u))} := by
  have hlocal := isLocallyLscAt_of_isLocallyClosedAt_epigraph hx
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal f hl) _)
  ext y
  change WithLp.toLp 2 (y,-(0 : WithLp 2 (E × ℝ))) ∈
    normalCone (euclideanSvGraph (parametricEpigraphMapping f))
      (WithLp.toLp 2 (u,WithLp.toLp 2 (x,a))) ↔ _
  rw [neg_zero,euclideanSvGraph_parametricEpigraphMapping,normalCone_preimage_linearIsometryEquiv]
  change WithLp.toLp 2 (WithLp.toLp 2 ((0:E),y),(0:ℝ)) ∈
    normalCone (euclideanEpigraph f) (WithLp.toLp 2 (WithLp.toLp 2 (x,u),a)) ↔ _
  exact (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hlocal hx).symm

/-- **Proposition 10.16**, the exact equivalence between horizon
qualification and Aubin stability of the slice epigraph. -/
theorem hasAubinProperty_parametricEpigraphMapping_iff {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) {x : E} {u : P} {a : ℝ}
    (hx : f (WithLp.toLp 2 (x,u)) = a) :
    HasAubinPropertyAt (parametricEpigraphMapping f) u (WithLp.toLp 2 (x,a)) ↔
      ∀ y : P, WithLp.toLp 2 ((0:E),y) ∈ horizonSubdifferential f (WithLp.toLp 2 (x,u)) → y = 0 := by
  have hm : WithLp.toLp 2 (x,a) ∈ parametricEpigraphMapping f u := hx.le
  rw [hasAubinPropertyAt_iff_coderivative_zero hm
    (RW.IsClosed.isLocallyClosedAt (isClosed_svGraph_parametricEpigraphMapping hl) _),
    coderivative_parametricEpigraphMapping_zero hl hx]
  constructor
  · intro he y hy
    exact mem_singleton_iff.mp (he ▸ hy)
  · intro hQ
    apply Subset.antisymm (fun y hy ↦ mem_singleton_iff.mpr (hQ y hy))
    apply singleton_subset_iff.mpr
    exact (subdifferential_properties hx).2.2.2.2.1.1

end

end RW
