/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Amenability of convex constraint systems
-/
import RockafellarWets.Chapter10.AmenablePreimages
import RockafellarWets.Chapter6.ProductCones

open Set
open scoped InnerProductSpace

noncomputable section
namespace RW
universe u
variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem convex_l2ProdSet {X : Set E} {D : Set F} (hX : Convex ℝ X) (hD : Convex ℝ D) :
    Convex ℝ (l2ProdSet X D) :=
  (hX.prod hD).linear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearEquiv.toLinearMap

private theorem polyhedral_l2ProdSet {X : Set E} {D : Set F}
    (hX : IsPolyhedral X) (hD : IsPolyhedral D) : IsPolyhedral (l2ProdSet X D) :=
  (hX.prod hD).continuousLinear_preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap

private theorem graphEmbedding_adjoint {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (v : WithLp 2 (E × F)) :
    (fderiv ℝ (fun y ↦ WithLp.toLp 2 (y,f y)) x).adjoint v = v.fst+(fderiv ℝ f x).adjoint v.snd := by
  have hd := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.hasFDerivAt.comp x
    ((hasFDerivAt_id x).prodMk hf.hasFDerivAt)
  change HasFDerivAt (fun y ↦ WithLp.toLp 2 (y,f y)) _ x at hd
  rw [hd.fderiv]
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left,inner_add_left,ContinuousLinearMap.adjoint_inner_left]
  change ⟪v,WithLp.toLp 2 (w,fderiv ℝ f x w)⟫_ℝ = _
  simp [WithLp.prod_inner_apply]

/-- **Example 10.24(d)**: the original normal constraint qualification is
exactly what is needed for the product representation of a constraint system. -/
def convexConstraintsAmenableModel {X : Set E} {D : Set F} {f : E → F} {x : E}
    {r : ℕ} {full : Bool} (hr : 1 ≤ r) (hX : IsClosed X) (hD : IsClosed D)
    (hXc : Convex ℝ X) (hDc : Convex ℝ D) (hf : ContDiff ℝ r f)
    (hx : x ∈ X ∩ f ⁻¹' D)
    (hQ : ∀v ∈ normalCone D (f x), -(fderiv ℝ f x).adjoint v ∈ normalCone X x → v = 0)
    (hp : full = true → IsPolyhedral X ∧ IsPolyhedral D) :
    AmenableSetModel (X ∩ f ⁻¹' D) x r full where
  Target := WithLp 2 (E × F)
  constraint := l2ProdSet X D
  inner := fun y ↦ WithLp.toLp 2 (y,f y)
  neighborhood := univ
  isOpen := isOpen_univ
  mem := mem_univ x
  base := hx
  closed := isClosed_l2ProdSet hX hD
  convex := convex_l2ProdSet hXc hDc
  smooth := ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.contDiff.comp (contDiff_id.prodMk hf)).contDiffOn
  eqOn := fun _ _ ↦ Iff.rfl
  qualification := by
    intro v hv hz
    rw [normalCone_l2ProdSet] at hv
    rw [graphEmbedding_adjoint (hf.differentiable (by exact_mod_cast (show r ≠ 0 by omega)) x)] at hz
    have hfst : v.fst = -(fderiv ℝ f x).adjoint v.snd := eq_neg_of_add_eq_zero_left hz
    have hsnd := hQ v.snd hv.2 (hfst ▸ hv.1)
    apply WithLp.ofLp_injective
    exact Prod.ext (by simpa [hsnd] using hfst) hsnd
  polyhedral := fun h ↦ polyhedral_l2ProdSet (hp h).1 (hp h).2

/-- C¹ convex constraint systems are amenable under the normal CQ. -/
theorem setAmenableAt_convex_constraints {X : Set E} {D : Set F} {f : E → F} {x : E}
    (hX : IsClosed X) (hD : IsClosed D) (hXc : Convex ℝ X) (hDc : Convex ℝ D)
    (hf : ContDiff ℝ 1 f) (hx : x ∈ X ∩ f ⁻¹' D)
    (hQ : ∀v ∈ normalCone D (f x), -(fderiv ℝ f x).adjoint v ∈ normalCone X x → v = 0) :
    SetAmenableAt (X ∩ f ⁻¹' D) x :=
  ⟨convexConstraintsAmenableModel le_rfl hX hD hXc hDc hf hx hQ (by simp)⟩

/-- C² convex constraint systems are strongly amenable under the normal CQ. -/
theorem setStronglyAmenableAt_convex_constraints {X : Set E} {D : Set F} {f : E → F} {x : E}
    (hX : IsClosed X) (hD : IsClosed D) (hXc : Convex ℝ X) (hDc : Convex ℝ D)
    (hf : ContDiff ℝ 2 f) (hx : x ∈ X ∩ f ⁻¹' D)
    (hQ : ∀v ∈ normalCone D (f x), -(fderiv ℝ f x).adjoint v ∈ normalCone X x → v = 0) :
    SetStronglyAmenableAt (X ∩ f ⁻¹' D) x :=
  ⟨convexConstraintsAmenableModel (by norm_num) hX hD hXc hDc hf hx hQ (by simp)⟩

/-- C² polyhedral constraint systems are fully amenable under the normal CQ. -/
theorem setFullyAmenableAt_polyhedral_constraints {X : Set E} {D : Set F} {f : E → F} {x : E}
    (hX : IsPolyhedral X) (hD : IsPolyhedral D) (hf : ContDiff ℝ 2 f) (hx : x ∈ X ∩ f ⁻¹' D)
    (hQ : ∀v ∈ normalCone D (f x), -(fderiv ℝ f x).adjoint v ∈ normalCone X x → v = 0) :
    SetFullyAmenableAt (X ∩ f ⁻¹' D) x :=
  ⟨convexConstraintsAmenableModel (by norm_num) hX.isClosed hD.isClosed hX.convex hD.convex hf hx hQ
    (fun _ ↦ ⟨hX,hD⟩)⟩

end RW
end
