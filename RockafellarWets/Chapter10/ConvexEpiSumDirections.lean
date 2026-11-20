/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The convex lower-closure directional formula for finite epi-addition
-/

import RockafellarWets.Chapter10.ConvexFiniteEpiAddition
import RockafellarWets.Chapter10.FiniteEpigraphSums

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 10.18**, the exact convex directional formula. Finite
inf-addition includes the mixed-infinity convention from Chapter 7. -/
theorem subderivative_finiteEpiSum_eq_epiClosure {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hc : ∀ i, Convex ℝ (epigraph (f i))) (hb : HasBoundedEpiSumDecompositions f)
    {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) {a : PiLp 2 (fun _ : ι ↦ E)}
    (ha : a ∈ epiSumDecompositions f x) :
    subderivative (finiteEpiSumValue f) x = epiClosure (finiteEpiSum (fun i ↦ subderivative (f i) (a i))) := by
  classical
  obtain ⟨c,hcval⟩ := separablePi_finite_components (ha.2.1.trans hx)
  have hsum : ∑ i, c i = r := EReal.coe_eq_coe_iff.mp
    ((separablePi_eq_coe hcval).symm.trans (ha.2.1.trans hx))
  let C := l2PiSet (fun i ↦ euclideanEpigraph (f i))
  let z : PiLp 2 (fun _ : ι ↦ WithLp 2 (E × ℝ)) := WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (a i,c i))
  let A := l2CoordinateSum (ι := ι) (E := WithLp 2 (E × ℝ))
  have hz : z ∈ C := fun i ↦ (hcval i).le
  have hconv (i : ι) : Convex ℝ (euclideanEpigraph (f i)) :=
    convex_preimage_continuousLinearEquiv (l2ProdEquiv E) (hc i)
  have hC : Convex ℝ C := by
    intro p hp' q hq' t s ht hs hts i
    exact hconv i (hp' i) (hq' i) ht hs hts
  have hAz : A z = WithLp.toLp 2 (x,r) := by
    apply (l2ProdEquiv E).injective
    change (l2ProdEquiv E) (l2CoordinateSum z) = (x,r)
    rw [l2CoordinateSum_apply,map_sum]
    change (∑ i, (a i,c i)) = (x,r)
    exact Prod.ext (by simpa only [Prod.fst_sum] using ha.1)
      (by simpa only [Prod.snd_sum] using hsum)
  have hreg (i : ι) : IsClarkeRegularAt (euclideanEpigraph (f i)) (z i) :=
    isClarkeRegularAt_of_convex (hconv i) (hz i)
      (RW.IsClosed.isLocallyClosedAt (isClosed_euclideanEpigraph (hf i)) (z i))
  have ht := tangentCone_linear_image_of_convex A hC hz
  have hepi : A '' C = euclideanEpigraph (finiteEpiSumValue f) :=
    (euclideanEpigraph_finiteEpiSumValue hp hf hb).symm
  rw [hepi,hAz,← euclideanEpigraph_subderivative hx,
    tangentCone_l2PiSet_of_isClarkeRegularAt hz hreg] at ht
  have he (i : ι) : tangentCone (euclideanEpigraph (f i)) (z i) =
      euclideanEpigraph (subderivative (f i) (a i)) := (euclideanEpigraph_subderivative (hcval i)).symm
  simp only [he] at ht
  have hclosed := closure_euclideanEpigraph_finiteEpiSum (fun i ↦ subderivative (f i) (a i))
  change closure (euclideanEpigraph (finiteEpiSum (fun i ↦ subderivative (f i) (a i)))) =
    closure (A '' l2PiSet (fun i ↦ euclideanEpigraph (subderivative (f i) (a i)))) at hclosed
  rw [← hclosed] at ht
  apply eq_of_epigraph_eq
  apply (l2ProdEquiv E).surjective.preimage_injective
  change euclideanEpigraph (subderivative (finiteEpiSumValue f) x) =
    (l2ProdEquiv E) ⁻¹' epigraph (epiClosure _)
  have hcl (S : Set (E × ℝ)) : (l2ProdEquiv E) ⁻¹' closure S = closure ((l2ProdEquiv E) ⁻¹' S) :=
    (l2ProdEquiv E).toHomeomorph.preimage_closure S
  rw [epigraph_epiClosure,hcl]
  exact ht

end

end RW
