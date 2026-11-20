/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epigraph projection for parametric minimization

The compactness infrastructure for Theorem 10.13. Euclidean products carry
their Hilbert norm, while the earlier value-function machinery uses ordinary
products; the coordinate maps below connect the two representations.
-/

import RockafellarWets.Chapter3.Parametric
import RockafellarWets.Chapter5.OptimalSetMappings
import RockafellarWets.Chapter6.ImageSetCones
import RockafellarWets.Chapter8.HorizontalEpigraphNormals
import RockafellarWets.Chapter7.LocalMinimization

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {E P : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The value function of a Euclidean parametric integrand. -/
def parametricValue (f : WithLp 2 (E × P) → EReal) : P → EReal :=
  valueFunction (fun q : E × P ↦ f (WithLp.toLp 2 q))

/-- The minimizing decisions at a fixed parameter. -/
def parametricMinimizers (f : WithLp 2 (E × P) → EReal) : P → Set E :=
  paramArgmin (fun q : E × P ↦ f (WithLp.toLp 2 q))

/-- Level boundedness in the decision variable, locally uniformly in the
parameter, for an integrand represented on a Euclidean product. -/
def IsParametricallyLevelBounded (f : WithLp 2 (E × P) → EReal) : Prop :=
  IsLevelBoundedInXLocallyUniformly (fun q : E × P ↦ f (WithLp.toLp 2 q))

@[simp] theorem mem_parametricMinimizers {f : WithLp 2 (E × P) → EReal} {x : E} {u : P} :
    x ∈ parametricMinimizers f u ↔
      f (WithLp.toLp 2 (x,u)) = parametricValue f u ∧ parametricValue f u < ⊤ :=
  mem_paramArgmin_iff _ _ _

/-- Coordinates on the epigraph of a function on a Euclidean product. -/
def parametricEpigraphCoordinates :
    WithLp 2 (WithLp 2 (E × P) × ℝ) ≃L[ℝ] ((E × P) × ℝ) :=
  (l2ProdEquiv (WithLp 2 (E × P))).trans
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E P).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))

@[simp] theorem parametricEpigraphCoordinates_apply (q : WithLp 2 (WithLp 2 (E × P) × ℝ)) :
    parametricEpigraphCoordinates q = (WithLp.ofLp (WithLp.ofLp q).1,(WithLp.ofLp q).2) := rfl

/-- The epigraph projection `(x,u,a) ↦ (u,a)`. -/
def parametricEpigraphProjection :
    WithLp 2 (WithLp 2 (E × P) × ℝ) →L[ℝ] WithLp 2 (P × ℝ) :=
  (l2ProdEquiv P).symm.toContinuousLinearMap.comp
    ((valueProjection (E := E) (F := P)).toContinuousLinearMap.comp
      parametricEpigraphCoordinates.toContinuousLinearMap)

@[simp] theorem parametricEpigraphProjection_apply (q : WithLp 2 (WithLp 2 (E × P) × ℝ)) :
    parametricEpigraphProjection q =
      WithLp.toLp 2 ((WithLp.ofLp (WithLp.ofLp q).1).2,(WithLp.ofLp q).2) := rfl

/-- The projection adjoint inserts a zero decision component. -/
theorem parametricEpigraphProjection_adjoint (v : P) (b : ℝ) :
    (parametricEpigraphProjection (E := E) (P := P)).adjoint (WithLp.toLp 2 (v,b)) =
      WithLp.toLp 2 (WithLp.toLp 2 ((0:E),v),b) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [WithLp.prod_inner_apply]

theorem isProper_parametricValue {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) (hb : IsParametricallyLevelBounded f) :
    IsProper (parametricValue f) := by
  apply isProper_valueFunction_of_lsc_localUniform
    (hl.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.continuous) _ hb
  exact ⟨by obtain ⟨q,hq⟩ := hp.1; exact ⟨WithLp.ofLp q,hq⟩,fun q ↦ hp.2 _⟩

theorem parametricMinimizers_nonempty {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) (hb : IsParametricallyLevelBounded f)
    {u : P} (hu : parametricValue f u < ⊤) : (parametricMinimizers f u).Nonempty := by
  apply paramArgmin_nonempty
    (hl.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.continuous) _ hb hu
  exact ⟨by obtain ⟨q,hq⟩ := hp.1; exact ⟨WithLp.ofLp q,hq⟩,fun q ↦ hp.2 _⟩

/-- The projected epigraph is exact, including attainment of each finite
boundary height. -/
theorem euclideanEpigraph_parametricValue {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hb : IsParametricallyLevelBounded f) :
    euclideanEpigraph (parametricValue f) =
      parametricEpigraphProjection '' euclideanEpigraph f := by
  have he := epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    (hl.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.continuous) hb
  change epigraph (parametricValue f) =
    valueProjection '' epigraph (fun q : E × P ↦ f (WithLp.toLp 2 q)) at he
  ext q
  constructor
  · intro hq
    have hq' : WithLp.ofLp q ∈ epigraph (parametricValue f) := hq
    rw [he] at hq'
    obtain ⟨⟨⟨x,u⟩,a⟩,hx,heq⟩ := hq'
    refine ⟨WithLp.toLp 2 (WithLp.toLp 2 (x,u),a),hx,?_⟩
    exact congrArg (WithLp.toLp 2) heq
  · rintro ⟨q,hq,rfl⟩
    change (⨅ x, f (WithLp.toLp 2 (x,(WithLp.ofLp (WithLp.ofLp q).1).2))) ≤ _
    exact (iInf_le _ (WithLp.ofLp (WithLp.ofLp q).1).1).trans hq

/-- A bounded parameter-height neighborhood has bounded lifts in the
epigraph, by local uniform level boundedness. -/
theorem parametricEpigraphProjection_locally_bounded_inverse
    {f : WithLp 2 (E × P) → EReal} (hb : IsParametricallyLevelBounded f) (u : P) (a : ℝ) :
    ∃ U ∈ 𝓝 (WithLp.toLp 2 (u,a)), Bornology.IsBounded
      (euclideanEpigraph f ∩ parametricEpigraphProjection ⁻¹' U) := by
  obtain ⟨r,hr,hbnd⟩ := hb u (a+1)
  let U := (l2ProdEquiv P) ⁻¹' (closedBall u r ×ˢ Icc (a-1) (a+1))
  have hU : U ∈ 𝓝 (WithLp.toLp 2 (u,a)) :=
    (l2ProdEquiv P).continuous.continuousAt.preimage_mem_nhds
      (prod_mem_nhds (closedBall_mem_nhds u hr) (Icc_mem_nhds (by linarith) (by linarith)))
  refine ⟨U,hU,?_⟩
  have hprod := hbnd.prod (isBounded_Icc (a := a-1) (b := a+1))
  have hi := (parametricEpigraphCoordinates (E := E) (P := P)).symm.toContinuousLinearMap.lipschitz.isBounded_image hprod
  apply hi.subset
  intro q ⟨hq,hqu⟩
  refine ⟨parametricEpigraphCoordinates q,?_,
    (parametricEpigraphCoordinates (E := E) (P := P)).symm_apply_apply q⟩
  change (WithLp.ofLp (WithLp.ofLp q).1,(WithLp.ofLp q).2) ∈ _
  change (WithLp.ofLp (WithLp.ofLp q).1).2 ∈ closedBall u r ∧
    (WithLp.ofLp q).2 ∈ Icc (a-1) (a+1) at hqu
  refine ⟨⟨⟨mem_univ _,hqu.1⟩,?_⟩,hqu.2⟩
  exact hq.trans (EReal.coe_le_coe_iff.mpr hqu.2.2)

/-- Lower semicontinuity of the marginal under the compactness hypothesis. -/
theorem lowerSemicontinuous_parametricValue {f : WithLp 2 (E × P) → EReal}
    (hl : LowerSemicontinuous f) (hp : IsProper f) (hb : IsParametricallyLevelBounded f) :
    LowerSemicontinuous (parametricValue f) := by
  apply lowerSemicontinuous_valueFunction_of_localUniform
    (hl.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.continuous) _ hb
  exact ⟨by obtain ⟨q,hq⟩ := hp.1; exact ⟨WithLp.ofLp q,hq⟩,fun q ↦ hp.2 _⟩

/-- At the optimal height the projection fiber is exactly the minimizer set. -/
theorem parametricEpigraphProjection_fiber {f : WithLp 2 (E × P) → EReal} {u : P} {a : ℝ}
    (hu : parametricValue f u = a) :
    euclideanEpigraph f ∩ parametricEpigraphProjection ⁻¹' {WithLp.toLp 2 (u,a)} =
      (fun x ↦ WithLp.toLp 2 (WithLp.toLp 2 (x,u),a)) '' parametricMinimizers f u := by
  ext q
  obtain ⟨⟨z,b⟩,rfl⟩ := WithLp.toLp_surjective 2 q
  obtain ⟨⟨x,v⟩,rfl⟩ := WithLp.toLp_surjective 2 z
  constructor
  · rintro ⟨hf,he⟩
    have he' : (v,b) = (u,a) := WithLp.toLp_injective 2 he
    cases he'
    refine ⟨x,mem_parametricMinimizers.mpr ⟨?_,hu.trans_lt (EReal.coe_lt_top a)⟩,rfl⟩
    exact le_antisymm (hf.trans_eq hu.symm) (iInf_le _ x)
  · rintro ⟨y,hy,he⟩
    rw [← he]
    exact ⟨(mem_parametricMinimizers.mp hy).1.trans hu |>.le,rfl⟩

end

end RW
