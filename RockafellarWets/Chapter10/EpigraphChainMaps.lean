/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epigraph lifts for the basic chain rule
-/

import RockafellarWets.Chapter8.SubdifferentialRegularityCriterion
import RockafellarWets.Chapter6.ConstraintTangents
import RockafellarWets.Chapter6.LimitingNormalChangeOfCoordinates

open Filter Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Lift a mapping by leaving the epigraph height unchanged. -/
def epigraphChainMap (G : E → F) (p : WithLp 2 (E × ℝ)) : WithLp 2 (F × ℝ) :=
  WithLp.toLp 2 (G p.fst,p.snd)

/-- The block derivative of the epigraph lift. -/
noncomputable def epigraphChainDerivative (A : E →L[ℝ] F) :
    WithLp 2 (E × ℝ) →L[ℝ] WithLp 2 (F × ℝ) :=
  (l2ProdEquiv F).symm.toContinuousLinearMap.comp
    ((A.comp (WithLp.fstL 2 ℝ E ℝ)).prod (WithLp.sndL 2 ℝ E ℝ))

@[simp] theorem epigraphChainDerivative_apply (A : E →L[ℝ] F) (p : WithLp 2 (E × ℝ)) :
    epigraphChainDerivative A p = WithLp.toLp 2 (A p.fst,p.snd) := rfl

theorem hasFDerivAt_epigraphChainMap {G : E → F} {A : E →L[ℝ] F} {x : E}
    (h : HasFDerivAt G A x) (c : ℝ) :
    HasFDerivAt (epigraphChainMap G) (epigraphChainDerivative A) (WithLp.toLp 2 (x,c)) := by
  exact (l2ProdEquiv F).symm.toContinuousLinearMap.hasFDerivAt.comp _
    ((h.comp _ (WithLp.fstL 2 ℝ E ℝ).hasFDerivAt).prodMk (WithLp.sndL 2 ℝ E ℝ).hasFDerivAt)

theorem contDiff_epigraphChainMap {G : E → F} (h : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (epigraphChainMap G) :=
  (l2ProdEquiv F).symm.contDiff.comp
    ((h.comp (WithLp.fstL 2 ℝ E ℝ).contDiff).prodMk (WithLp.sndL 2 ℝ E ℝ).contDiff)

@[simp] theorem euclideanEpigraph_comp (G : E → F) (g : F → EReal) :
    euclideanEpigraph (g ∘ G) = epigraphChainMap G ⁻¹' euclideanEpigraph g := rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

@[simp] theorem epigraphChainDerivative_adjoint (A : E →L[ℝ] F) (p : WithLp 2 (F × ℝ)) :
    (epigraphChainDerivative A).adjoint p = WithLp.toLp 2 (A.adjoint p.fst,p.snd) := by
  apply ext_inner_right ℝ
  intro q
  rw [ContinuousLinearMap.adjoint_inner_left,epigraphChainDerivative_apply,
    WithLp.prod_inner_apply,WithLp.prod_inner_apply,ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem epigraphChainDerivative_surjective {A : E →L[ℝ] F} (h : Function.Surjective A) :
    Function.Surjective (epigraphChainDerivative A) := by
  intro q
  obtain ⟨w,hw⟩ := h q.fst
  exact ⟨WithLp.toLp 2 (w,q.snd),by simp only [epigraphChainDerivative_apply,WithLp.toLp_fst,WithLp.toLp_snd,hw]; rfl⟩

theorem locallyLscAt_of_lowerSemicontinuous_finite {g : F → EReal} {z : F} {c : ℝ}
    (hl : LowerSemicontinuous g) (hz : g z = c) : IsLocallyLscAt g z :=
  isLocallyLscAt_of_isLocallyClosedAt_epigraph hz
    (RW.IsClosed.isLocallyClosedAt (isClosed_epigraph_of_lsc_ereal g hl) (z,c))

/-- The chain-rule horizon qualification is precisely the normal
qualification for the epigraph inverse image. -/
theorem epigraphChain_constraintQualification {G : E → F} {g : F → EReal} {x : E} {c : ℝ}
    (hG : ContDiff ℝ 1 G) (hl : LowerSemicontinuous g) (hx : g (G x) = c)
    (hQ : ∀ y ∈ horizonSubdifferential g (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0) :
    NormalConstraintQualification univ (euclideanEpigraph g)
      (fderiv ℝ (epigraphChainMap G) (WithLp.toLp 2 (x,c)))
      (WithLp.toLp 2 (x,c)) (WithLp.toLp 2 (G x,c)) := by
  have hd : HasFDerivAt G (fderiv ℝ G x) x := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hde : HasFDerivAt (epigraphChainMap G) (epigraphChainDerivative (fderiv ℝ G x))
      (WithLp.toLp 2 (x,c)) := hasFDerivAt_epigraphChainMap hd c
  rw [hde.fderiv]
  intro q hq hzero
  rw [normalCone_univ,mem_singleton_iff,neg_eq_zero,epigraphChainDerivative_adjoint] at hzero
  have hfst : (fderiv ℝ G x).adjoint q.fst = 0 := congrArg WithLp.fst hzero
  have hsnd : q.snd = 0 := congrArg WithLp.snd hzero
  have hhor : q.fst ∈ horizonSubdifferential g (G x) := by
    apply (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc
      (locallyLscAt_of_lowerSemicontinuous_finite hl hx) hx).mpr
    simpa only [← hsnd] using hq
  have hq0 := hQ q.fst hhor hfst
  apply WithLp.ofLp_injective
  exact Prod.ext hq0 hsnd

end RW
