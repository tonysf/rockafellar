/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Smooth perturbations preserve amenability
-/
import RockafellarWets.Chapter10.AmenableFunctionCalculus
import RockafellarWets.Chapter10.AmenableExamples
import RockafellarWets.Chapter6.ProductCones

open Set
open scoped InnerProductSpace

noncomputable section
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem plq_continuousLinear (l : E →L[ℝ] ℝ) :
    IsPiecewiseLinearQuadratic (fun y ↦ (l y:EReal)) := by
  let q : QuadraticPiece E := ⟨0,by simp,l.adjoint 1,0⟩
  simpa [q,QuadraticPiece.eval,ContinuousLinearMap.adjoint_inner_left] using
    isPiecewiseLinearQuadratic_piece (E := E) IsPolyhedral.univ q

private theorem convex_epigraph_continuousLinear (l : E →L[ℝ] ℝ) :
    Convex ℝ (epigraph (fun y ↦ (l y:EReal))) := by
  have hh := (convex_epigraph_iff_convexOn l univ convex_univ).mpr (l.toLinearMap.convexOn convex_univ)
  simpa [epigraph] using hh

private theorem lifted_domain {g : E → EReal} (hp : IsProper g) :
    effectiveDomain (fun z : WithLp 2 (E × ℝ) ↦ g z.fst+(z.snd:EReal)) =
      l2ProdSet (effectiveDomain g) univ := by
  ext z
  change g z.fst+(z.snd:EReal) < ⊤ ↔ g z.fst < ⊤ ∧ True
  rw [and_true]
  constructor
  · intro hz
    by_contra hn
    have he : g z.fst = ⊤ := top_unique (not_lt.mp hn)
    rw [he,EReal.top_add_coe] at hz
    exact lt_irrefl _ hz
  · intro hz
    exact EReal.add_lt_top (ne_of_lt hz) (EReal.coe_ne_top _)

private theorem closure_l2ProdSet_univ (D : Set E) :
    closure (l2ProdSet D (univ : Set ℝ)) = l2ProdSet (closure D) univ := by
  change closure ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).toHomeomorph ⁻¹' (D ×ˢ univ)) = _
  rw [← Homeomorph.preimage_closure,closure_prod_eq,closure_univ]
  rfl

/-- Adding a smooth finite function to an amenable model preserves its
smoothness order and its piecewise-linear-quadratic outer function. -/
def AmenableFunctionModel.add_smooth {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) {q : E → ℝ} (hq : ContDiff ℝ r q) :
    AmenableFunctionModel (fun y ↦ f y+(q y:EReal)) x r full where
  Target := WithLp 2 (M.Target × ℝ)
  outer := fun z ↦ M.outer z.fst+(z.snd:EReal)
  inner := fun y ↦ WithLp.toLp 2 (M.inner y,q y)
  neighborhood := M.neighborhood
  isOpen := M.isOpen
  mem := M.mem
  finite := ⟨(EReal.bot_lt_add_iff.mpr ⟨bot_lt_iff_ne_bot.mpr M.finite.1,EReal.bot_lt_coe _⟩).ne',
    EReal.add_ne_top M.finite.2 (EReal.coe_ne_top _)⟩
  proper := by
    obtain ⟨y,hy⟩ := M.proper.1
    refine ⟨⟨WithLp.toLp 2 (y,0),?_⟩,fun z ↦ ?_⟩
    · simpa using hy
    · exact EReal.bot_lt_add_iff.mpr ⟨M.proper.2 _,EReal.bot_lt_coe _⟩
  lsc := by
    apply LowerSemicontinuous.add' (M.lsc.comp (WithLp.fstL 2 ℝ M.Target ℝ).continuous)
      (continuous_coe_real_ereal.comp (WithLp.sndL 2 ℝ M.Target ℝ).continuous).lowerSemicontinuous
    intro z
    exact EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))
  convex := by
    have hc : Convex ℝ (epigraph (fun z : WithLp 2 (M.Target × ℝ) ↦ M.outer z.fst)) := by
      simpa using convex_epigraph_compAffine M.convex (WithLp.fstL 2 ℝ M.Target ℝ) 0
    exact convex_epigraph_add_of_ne_bot hc (convex_epigraph_continuousLinear (WithLp.sndL 2 ℝ M.Target ℝ))
      (fun z ↦ (M.proper.2 z.fst).ne') (fun z ↦ EReal.coe_ne_bot z.snd)
  smooth := (WithLp.prodContinuousLinearEquiv 2 ℝ M.Target ℝ).symm.contDiff.contDiffOn.comp
    (M.smooth.prodMk hq.contDiffOn) (fun _ _ ↦ mem_univ _)
  eqOn := by intro y hy; change f y+(q y:EReal) = M.outer (M.inner y)+(q y:EReal); rw [M.eqOn y hy]
  qualification := by
    intro v hv hz
    rw [lifted_domain M.proper,closure_l2ProdSet_univ,normalCone_l2ProdSet,normalCone_univ] at hv
    have hsnd : v.snd = 0 := hv.2
    have hmd := ((M.smooth x M.mem).contDiffAt (M.isOpen.mem_nhds M.mem)).differentiableAt
      (by exact_mod_cast (show r ≠ 0 by omega))
    have hqd := hq.differentiable (by exact_mod_cast (show r ≠ 0 by omega)) x
    have hd := (WithLp.prodContinuousLinearEquiv 2 ℝ M.Target ℝ).symm.toContinuousLinearMap.hasFDerivAt.comp x
      (hmd.hasFDerivAt.prodMk hqd.hasFDerivAt)
    change HasFDerivAt (fun y ↦ WithLp.toLp 2 (M.inner y,q y)) _ x at hd
    have ha : (fderiv ℝ (fun y ↦ WithLp.toLp 2 (M.inner y,q y)) x).adjoint v =
        (fderiv ℝ M.inner x).adjoint v.fst := by
      rw [hd.fderiv]
      apply ext_inner_right ℝ
      intro w
      rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
      change ⟪v,WithLp.toLp 2 (fderiv ℝ M.inner x w,fderiv ℝ q x w)⟫_ℝ = _
      simp [WithLp.prod_inner_apply,hsnd]
    rw [ha] at hz
    have hfst := M.qualification v.fst hv.1 hz
    apply WithLp.ofLp_injective
    exact Prod.ext hfst hsnd
  plq := by
    intro hf
    have hp : IsPiecewiseLinearQuadratic (fun z : WithLp 2 (M.Target × ℝ) ↦ M.outer z.fst) := by
      simpa using (M.plq hf).compAffine (WithLp.fstL 2 ℝ M.Target ℝ) 0
    exact hp.add (plq_continuousLinear (WithLp.sndL 2 ℝ M.Target ℝ))

/-- Smooth C¹ perturbations preserve amenability. -/
theorem AmenableAt.add_smooth {f : E → EReal} {q : E → ℝ} {x : E}
    (h : AmenableAt f x) (hq : ContDiff ℝ 1 q) : AmenableAt (fun y ↦ f y+(q y:EReal)) x := by
  obtain ⟨M⟩ := h
  exact ⟨M.add_smooth le_rfl hq⟩

theorem StronglyAmenableAt.add_smooth {f : E → EReal} {q : E → ℝ} {x : E}
    (h : StronglyAmenableAt f x) (hq : ContDiff ℝ 2 q) : StronglyAmenableAt (fun y ↦ f y+(q y:EReal)) x := by
  obtain ⟨M⟩ := h
  exact ⟨M.add_smooth (by norm_num) hq⟩

theorem FullyAmenableAt.add_smooth {f : E → EReal} {q : E → ℝ} {x : E}
    (h : FullyAmenableAt f x) (hq : ContDiff ℝ 2 q) : FullyAmenableAt (fun y ↦ f y+(q y:EReal)) x := by
  obtain ⟨M⟩ := h
  exact ⟨M.add_smooth (by norm_num) hq⟩

/-- **Example 10.24(g)**, all three smoothness and polyhedral variants. -/
theorem convex_add_smooth_amenable {f : E → EReal} {q : E → ℝ} {x : E}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hx : x ∈ effectiveDomain f) (hq : ContDiff ℝ 1 q) :
    AmenableAt (fun y ↦ f y+(q y:EReal)) x :=
  (stronglyAmenableAt_of_convex hp hl hc hx).amenableAt.add_smooth hq

theorem convex_add_smooth_stronglyAmenable {f : E → EReal} {q : E → ℝ} {x : E}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hx : x ∈ effectiveDomain f) (hq : ContDiff ℝ 2 q) :
    StronglyAmenableAt (fun y ↦ f y+(q y:EReal)) x :=
  (stronglyAmenableAt_of_convex hp hl hc hx).add_smooth hq

theorem convex_plq_add_smooth_fullyAmenable {f : E → EReal} {q : E → ℝ} {x : E}
    (hp : IsProper f) (hf : IsPiecewiseLinearQuadratic f) (hc : Convex ℝ (epigraph f))
    (hx : x ∈ effectiveDomain f) (hq : ContDiff ℝ 2 q) :
    FullyAmenableAt (fun y ↦ f y+(q y:EReal)) x :=
  (fullyAmenableAt_of_convex_plq hf hc hx).add_smooth hq

end RW
end
