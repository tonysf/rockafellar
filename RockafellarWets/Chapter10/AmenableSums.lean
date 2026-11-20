/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Product models for qualified amenable sums
-/
import RockafellarWets.Chapter10.AmenableComposition
import RockafellarWets.Chapter10.AmenableExamples
import RockafellarWets.Chapter10.SeparableSubderivatives

open Set
open scoped InnerProductSpace

noncomputable section
namespace RW
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The domain of a proper separable sum is the product of its domains. -/
theorem effectiveDomain_separableSum {f : E → EReal} {g : F → EReal}
    (hf : IsProper f) (hg : IsProper g) :
    effectiveDomain (separableSum f g) = l2ProdSet (effectiveDomain f) (effectiveDomain g) := by
  ext z
  change f z.fst+g z.snd < ⊤ ↔ f z.fst < ⊤ ∧ g z.snd < ⊤
  constructor
  · intro h
    constructor
    · by_contra hn
      have he : f z.fst = ⊤ := top_unique (not_lt.mp hn)
      rw [he,EReal.top_add_of_ne_bot (hg.2 _).ne'] at h
      exact lt_irrefl _ h
    · by_contra hn
      have he : g z.snd = ⊤ := top_unique (not_lt.mp hn)
      rw [he,EReal.add_top_of_ne_bot (hf.2 _).ne'] at h
      exact lt_irrefl _ h
  · rintro ⟨h,k⟩
    exact EReal.add_lt_top h.ne k.ne

theorem closure_l2ProdSet (C : Set E) (D : Set F) :
    closure (l2ProdSet C D) = l2ProdSet (closure C) (closure D) := by
  change closure ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).toHomeomorph ⁻¹' (C ×ˢ D)) = _
  rw [← Homeomorph.preimage_closure,closure_prod_eq]
  rfl

/-- A pair of local amenable representations gives an amenable sum model
under the zero-sum horizon qualification. -/
def AmenableFunctionModel.add {f g : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (N : AmenableFunctionModel g x r full) (hr : 1 ≤ r)
    (hQ : ∀v ∈ horizonSubdifferential f x, ∀w ∈ horizonSubdifferential g x,
      v+w = 0 → v = 0 ∧ w = 0) : AmenableFunctionModel (fun y ↦ f y+g y) x r full where
  Target := WithLp 2 (M.Target × N.Target)
  outer := separableSum M.outer N.outer
  inner := fun y ↦ WithLp.toLp 2 (M.inner y,N.inner y)
  neighborhood := M.neighborhood ∩ N.neighborhood
  isOpen := M.isOpen.inter N.isOpen
  mem := ⟨M.mem,N.mem⟩
  finite := ⟨(EReal.bot_lt_add_iff.mpr ⟨bot_lt_iff_ne_bot.mpr M.finite.1,bot_lt_iff_ne_bot.mpr N.finite.1⟩).ne',
    EReal.add_ne_top M.finite.2 N.finite.2⟩
  proper := by
    obtain ⟨u,hu⟩ := M.proper.1
    obtain ⟨v,hv⟩ := N.proper.1
    exact ⟨⟨WithLp.toLp 2 (u,v),EReal.add_lt_top hu.ne hv.ne⟩,
      fun z ↦ EReal.bot_lt_add_iff.mpr ⟨M.proper.2 _,N.proper.2 _⟩⟩
  lsc := lowerSemicontinuous_separableSum M.lsc N.lsc M.proper N.proper
  convex := by
    have hcM : Convex ℝ (epigraph (fun z : WithLp 2 (M.Target × N.Target) ↦ M.outer z.fst)) := by
      simpa using convex_epigraph_compAffine M.convex (WithLp.fstL 2 ℝ M.Target N.Target) 0
    have hcN : Convex ℝ (epigraph (fun z : WithLp 2 (M.Target × N.Target) ↦ N.outer z.snd)) := by
      simpa using convex_epigraph_compAffine N.convex (WithLp.sndL 2 ℝ M.Target N.Target) 0
    exact convex_epigraph_add_of_ne_bot hcM hcN (fun z ↦ (M.proper.2 z.fst).ne') (fun z ↦ (N.proper.2 z.snd).ne')
  smooth := (WithLp.prodContinuousLinearEquiv 2 ℝ M.Target N.Target).symm.contDiff.contDiffOn.comp
    ((M.smooth.mono inter_subset_left).prodMk (N.smooth.mono inter_subset_right)) (fun _ _ ↦ mem_univ _)
  eqOn := by
    intro y hy
    change f y+g y = M.outer (M.inner y)+N.outer (N.inner y)
    rw [M.eqOn y hy.1,N.eqOn y hy.2]
  qualification := by
    intro v hv hz
    rw [effectiveDomain_separableSum M.proper N.proper,closure_l2ProdSet,normalCone_l2ProdSet] at hv
    have hmd := ((M.smooth x M.mem).contDiffAt (M.isOpen.mem_nhds M.mem)).differentiableAt
      (by exact_mod_cast (show r ≠ 0 by omega))
    have hnd := ((N.smooth x N.mem).contDiffAt (N.isOpen.mem_nhds N.mem)).differentiableAt
      (by exact_mod_cast (show r ≠ 0 by omega))
    have hd := (WithLp.prodContinuousLinearEquiv 2 ℝ M.Target N.Target).symm.toContinuousLinearMap.hasFDerivAt.comp x
      (hmd.hasFDerivAt.prodMk hnd.hasFDerivAt)
    change HasFDerivAt (fun y ↦ WithLp.toLp 2 (M.inner y,N.inner y)) _ x at hd
    have ha : (fderiv ℝ (fun y ↦ WithLp.toLp 2 (M.inner y,N.inner y)) x).adjoint v =
        (fderiv ℝ M.inner x).adjoint v.fst+(fderiv ℝ N.inner x).adjoint v.snd := by
      rw [hd.fderiv]
      apply ext_inner_right ℝ
      intro w
      rw [ContinuousLinearMap.adjoint_inner_left,inner_add_left,
        ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
      change ⟪v,WithLp.toLp 2 (fderiv ℝ M.inner x w,fderiv ℝ N.inner x w)⟫_ℝ = _
      simp [WithLp.prod_inner_apply]
    rw [ha] at hz
    have hfm : M.outer (M.inner x) = ((f x).toReal:EReal) := by
      rw [← M.eqOn x M.mem]; exact (EReal.coe_toReal M.finite.2 M.finite.1).symm
    have hgn : N.outer (N.inner x) = ((g x).toReal:EReal) := by
      rw [← N.eqOn x N.mem]; exact (EReal.coe_toReal N.finite.2 N.finite.1).symm
    have hmf : (fderiv ℝ M.inner x).adjoint v.fst ∈ horizonSubdifferential f x := by
      rw [(M.derivatives hr).2.1]
      exact ⟨v.fst,by rw [horizonSubdifferential_eq_normalCone_closure_domain M.proper M.lsc M.convex hfm]; exact hv.1,rfl⟩
    have hng : (fderiv ℝ N.inner x).adjoint v.snd ∈ horizonSubdifferential g x := by
      rw [(N.derivatives hr).2.1]
      exact ⟨v.snd,by rw [horizonSubdifferential_eq_normalCone_closure_domain N.proper N.lsc N.convex hgn]; exact hv.2,rfl⟩
    obtain ⟨h0,h1⟩ := hQ _ hmf _ hng hz
    apply WithLp.ofLp_injective
    exact Prod.ext (M.qualification _ hv.1 h0) (N.qualification _ hv.2 h1)
  plq := by
    intro hf
    have hpM : IsPiecewiseLinearQuadratic (fun z : WithLp 2 (M.Target × N.Target) ↦ M.outer z.fst) := by
      simpa using (M.plq hf).compAffine (WithLp.fstL 2 ℝ M.Target N.Target) 0
    have hpN : IsPiecewiseLinearQuadratic (fun z : WithLp 2 (M.Target × N.Target) ↦ N.outer z.snd) := by
      simpa using (N.plq hf).compAffine (WithLp.sndL 2 ℝ M.Target N.Target) 0
    exact hpM.add hpN

end RW
end
