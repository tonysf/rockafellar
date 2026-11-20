/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Composite Lagrange multipliers
-/

import RockafellarWets.Chapter10.ConstrainedSubgradients
import RockafellarWets.Chapter10.FermatRule

open Filter Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {X : Set E} {k : E → ℝ} {G : E → F} {θ : F → EReal} {x : E} {c : ℝ}

/-- The extended-real constrained objective of Example 10.8. -/
noncomputable def compositeObjective (X : Set E) (k : E → ℝ) (G : E → F) (θ : F → EReal) (z : E) : EReal :=
  indicatorVA X z+θ (G z)+(k z:EReal)

/-- The composite constraint qualification stated in terms of domain normals. -/
def CompositeConstraintQualification (X : Set E) (G : E → F) (θ : F → EReal) (x : E) : Prop :=
  ∀ y ∈ normalCone (effectiveDomain θ) (G x), -(fderiv ℝ G x).adjoint y ∈ normalCone X x → y = 0

theorem horizonSubdifferential_eq_normalCone_domain_of_lsc
    (hθ : Convex ℝ (epigraph θ)) (hp : IsProper θ) (hl : LowerSemicontinuous θ)
    {z : F} (hc : θ z = c) : horizonSubdifferential θ z = normalCone (effectiveDomain θ) z := by
  ext y
  rw [mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc
    (locallyLscAt_of_lowerSemicontinuous_finite hl hc) hc,horizontal_normal_iff_normalCone_domain hθ hp hc]

private theorem composite_chain_data
    (hG : ContDiff ℝ 1 G) (hθ : Convex ℝ (epigraph θ)) (hp : IsProper θ)
    (hl : LowerSemicontinuous θ) (hx : x ∈ X) (hc : θ (G x) = c)
    (hQ : CompositeConstraintQualification X G θ x) :
    IsProper (θ ∘ G) ∧ IsSubdifferentiallyRegularAt (θ ∘ G) x ∧
    subdifferential (θ ∘ G) x = (fderiv ℝ G x).adjoint '' subdifferential θ (G x) ∧
    horizonSubdifferential (θ ∘ G) x = (fderiv ℝ G x).adjoint '' normalCone (effectiveDomain θ) (G x) ∧
    (∀ y ∈ horizonSubdifferential (θ ∘ G) x, -y ∈ normalCone X x → y = 0) := by
  have hhr := horizonSubdifferential_eq_normalCone_domain_of_lsc hθ hp hl hc
  have hq : ∀ y ∈ horizonSubdifferential θ (G x), (fderiv ℝ G x).adjoint y = 0 → y = 0 := by
    intro y hy he
    apply hQ y (hhr ▸ hy)
    rw [he,neg_zero]
    exact (isCone_normalCone hx).1
  have hrθ := (isSubdifferentiallyRegularAt_of_convex hθ
    (locallyLscAt_of_lowerSemicontinuous_finite hl hc)).1
  have heh := horizonSubdifferential_comp_eq_of_regular hG hl hrθ hq
  rw [hhr] at heh
  refine ⟨⟨⟨x,hc.trans_lt (EReal.coe_lt_top _)⟩,fun z ↦ hp.2 (G z)⟩,
    hrθ.comp_of_horizon_qualification hG hl hq,subdifferential_comp_eq_of_regular hG hl hrθ hq,heh,?_⟩
  intro y hy hn
  obtain ⟨v,hv,rfl⟩ := heh ▸ hy
  rw [hQ v hv hn,map_zero]

theorem compositeObjective_eq_coe (hx : x ∈ X) (hc : θ (G x) = c) :
    compositeObjective X k G θ x = ((c+k x:ℝ):EReal) := by
  simp only [compositeObjective,indicatorVA_apply_mem hx,zero_add,hc,EReal.coe_add]

/-- **Example 10.8**, the limiting multiplier inclusion. -/
theorem subdifferential_compositeObjective_subset
    (hX : IsClosed X) (hk : ContDiff ℝ 1 k) (hG : ContDiff ℝ 1 G)
    (hθ : Convex ℝ (epigraph θ)) (hp : IsProper θ) (hl : LowerSemicontinuous θ)
    (hx : x ∈ X) (hc : θ (G x) = c) (hQ : CompositeConstraintQualification X G θ x) :
    subdifferential (compositeObjective X k G θ) x ⊆
      {v | ∃ y ∈ subdifferential θ (G x), v-gradient k x-(fderiv ℝ G x).adjoint y ∈ normalCone X x} := by
  obtain ⟨hpG,_,hs,_,hq⟩ := composite_chain_data hG hθ hp hl hx hc hQ
  have hv : (indicatorVA X+θ ∘ G) x = c := by simp [indicatorVA_apply_mem hx,Function.comp_def,hc]
  rw [show subdifferential (compositeObjective X k G θ) x = _ from
    (subdifferentials_add_smooth hv hk.contDiffAt).2.1]
  rintro v ⟨z,hz,rfl⟩
  obtain ⟨a,ha,b,hb,rfl⟩ := subdifferential_indicator_add_subset hX (hl.comp hG.continuous) hpG hx hc hq hz
  obtain ⟨y,hy,rfl⟩ := hs ▸ hb
  exact ⟨y,hy,by simpa only [add_sub_cancel_right] using ha⟩

/-- **Example 10.8**, the horizon multiplier inclusion. -/
theorem horizonSubdifferential_compositeObjective_subset
    (hX : IsClosed X) (hk : ContDiff ℝ 1 k) (hG : ContDiff ℝ 1 G)
    (hθ : Convex ℝ (epigraph θ)) (hp : IsProper θ) (hl : LowerSemicontinuous θ)
    (hx : x ∈ X) (hc : θ (G x) = c) (hQ : CompositeConstraintQualification X G θ x) :
    horizonSubdifferential (compositeObjective X k G θ) x ⊆
      {v | ∃ y ∈ normalCone (effectiveDomain θ) (G x), v-(fderiv ℝ G x).adjoint y ∈ normalCone X x} := by
  obtain ⟨hpG,_,_,hs,hq⟩ := composite_chain_data hG hθ hp hl hx hc hQ
  have hv : (indicatorVA X+θ ∘ G) x = c := by simp [indicatorVA_apply_mem hx,Function.comp_def,hc]
  rw [show horizonSubdifferential (compositeObjective X k G θ) x = _ from
    (subdifferentials_add_smooth hv hk.contDiffAt).2.2]
  intro v hv
  obtain ⟨a,ha,b,hb,rfl⟩ := horizonSubdifferential_indicator_add_subset hX (hl.comp hG.continuous) hpG hx hc hq hv
  obtain ⟨y,hy,rfl⟩ := hs ▸ hb
  exact ⟨y,hy,by simpa only [add_sub_cancel_right] using ha⟩

/-- **Example 10.8**, regularity for a regular constraint set. -/
theorem isSubdifferentiallyRegularAt_compositeObjective
    (hX : IsClosed X) (hk : ContDiff ℝ 1 k) (hG : ContDiff ℝ 1 G)
    (hθ : Convex ℝ (epigraph θ)) (hp : IsProper θ) (hl : LowerSemicontinuous θ)
    (hx : x ∈ X) (hc : θ (G x) = c) (hQ : CompositeConstraintQualification X G θ x)
    (hR : IsClarkeRegularAt X x) : IsSubdifferentiallyRegularAt (compositeObjective X k G θ) x := by
  obtain ⟨hpG,hr,_,_,hq⟩ := composite_chain_data hG hθ hp hl hx hc hQ
  exact (isSubdifferentiallyRegularAt_add_smooth_iff (g := indicatorVA X+θ ∘ G)
    (U := univ) univ_mem hk.contDiffOn).mpr (hr.indicator_add hX (hl.comp hG.continuous) hpG hx hR hq)

/-- **Example 10.8**, both exact multiplier formulas for a regular constraint set. -/
theorem subdifferentials_compositeObjective_eq
    (hX : IsClosed X) (hk : ContDiff ℝ 1 k) (hG : ContDiff ℝ 1 G)
    (hθ : Convex ℝ (epigraph θ)) (hp : IsProper θ) (hl : LowerSemicontinuous θ)
    (hx : x ∈ X) (hc : θ (G x) = c) (hQ : CompositeConstraintQualification X G θ x)
    (hR : IsClarkeRegularAt X x) :
    subdifferential (compositeObjective X k G θ) x =
      {v | ∃ y ∈ subdifferential θ (G x), v-gradient k x-(fderiv ℝ G x).adjoint y ∈ normalCone X x} ∧
    horizonSubdifferential (compositeObjective X k G θ) x =
      {v | ∃ y ∈ normalCone (effectiveDomain θ) (G x), v-(fderiv ℝ G x).adjoint y ∈ normalCone X x} := by
  obtain ⟨hpG,hr,hs,hh,hq⟩ := composite_chain_data hG hθ hp hl hx hc hQ
  have hv : (indicatorVA X+θ ∘ G) x = c := by simp [indicatorVA_apply_mem hx,Function.comp_def,hc]
  constructor
  · apply Subset.antisymm (subdifferential_compositeObjective_subset hX hk hG hθ hp hl hx hc hQ)
    rintro v ⟨y,hy,hn⟩
    rw [show subdifferential (compositeObjective X k G θ) x = _ from
      (subdifferentials_add_smooth hv hk.contDiffAt).2.1,
      subdifferential_indicator_add_eq hr hX (hl.comp hG.continuous) hpG hx hR hq,hs]
    exact ⟨v-gradient k x,⟨_,hn,_,⟨y,hy,rfl⟩,sub_add_cancel _ _⟩,sub_add_cancel _ _⟩
  · apply Subset.antisymm (horizonSubdifferential_compositeObjective_subset hX hk hG hθ hp hl hx hc hQ)
    rintro v ⟨y,hy,hn⟩
    rw [show horizonSubdifferential (compositeObjective X k G θ) x = _ from
      (subdifferentials_add_smooth hv hk.contDiffAt).2.2,
      horizonSubdifferential_indicator_add_eq hr hX (hl.comp hG.continuous) hpG hx hR hq,hh]
    exact ⟨_,hn,_,⟨y,hy,rfl⟩,sub_add_cancel _ _⟩

/-- **Example 10.8**, necessary Lagrange multiplier stationarity. -/
theorem exists_composite_multiplier_of_localMin
    (hX : IsClosed X) (hk : ContDiff ℝ 1 k) (hG : ContDiff ℝ 1 G)
    (hθ : Convex ℝ (epigraph θ)) (hp : IsProper θ) (hl : LowerSemicontinuous θ)
    (hx : x ∈ X) (hc : θ (G x) = c) (hQ : CompositeConstraintQualification X G θ x)
    (hm : IsLocalMin (compositeObjective X k G θ) x) :
    ∃ y ∈ subdifferential θ (G x), -(gradient k x+(fderiv ℝ G x).adjoint y) ∈ normalCone X x := by
  obtain ⟨y,hy,hn⟩ := subdifferential_compositeObjective_subset hX hk hG hθ hp hl hx hc hQ
    (RW.IsLocalMin.zero_mem_subdifferential hm (compositeObjective_eq_coe hx hc))
  exact ⟨y,hy,by convert hn using 1 <;> abel⟩

/-- The unconditional regular multiplier inclusion used in the convex
sufficiency argument. Here the multiplier is a subgradient of the cost,
not merely a normal to its domain. -/
theorem regularSubdifferential_compositeObjective_superset
    (hk : ContDiff ℝ 1 k) (hG : ContDiff ℝ 1 G)
    (hθ : Convex ℝ (epigraph θ)) (hp : IsProper θ)
    (hx : x ∈ X) (hc : θ (G x) = c) (hR : IsClarkeRegularAt X x) :
    {v | ∃ y ∈ subdifferential θ (G x), v-gradient k x-(fderiv ℝ G x).adjoint y ∈ normalCone X x} ⊆
      regularSubdifferential (compositeObjective X k G θ) x := by
  rintro v ⟨y,hy,hn⟩
  have hy' : (fderiv ℝ G x).adjoint y ∈ regularSubdifferential (θ ∘ G) x := by
    apply adjoint_regularSubdifferential_subset_comp (hG.differentiable one_ne_zero x).hasFDerivAt hc
    exact ⟨y,(subdifferential_eq_regularSubdifferential_of_convex hθ hp hc) ▸ hy,rfl⟩
  have hn' : v-gradient k x-(fderiv ℝ G x).adjoint y ∈ regularSubdifferential (indicatorVA X) x := by
    rw [regularSubdifferential_indicatorVA,← hR.2]
    exact hn
  have hv : (indicatorVA X+θ ∘ G) x = c := by simp [indicatorVA_apply_mem hx,Function.comp_def,hc]
  rw [show regularSubdifferential (compositeObjective X k G θ) x = _ from
    (subdifferentials_add_smooth hv hk.contDiffAt).1]
  refine ⟨v-gradient k x,?_,sub_add_cancel _ _⟩
  exact regularSubdifferential_add_superset (indicatorVA_apply_mem hx) hc
    ⟨_,hn',_,hy',sub_add_cancel _ _⟩

/-- **Example 10.8**, convex sufficiency of the multiplier condition,
without the constraint qualification. -/
theorem mem_argmin_compositeObjective_of_multiplier
    (hk : ContDiff ℝ 1 k) (hG : ContDiff ℝ 1 G)
    (hθ : Convex ℝ (epigraph θ)) (hp : IsProper θ)
    (hx : x ∈ X) (hc : θ (G x) = c) (hX : Convex ℝ X) (hclosed : IsClosed X)
    (hconv : Convex ℝ (epigraph (compositeObjective X k G θ)))
    (hstat : ∃ y ∈ subdifferential θ (G x), -(gradient k x+(fderiv ℝ G x).adjoint y) ∈ normalCone X x) :
    x ∈ argmin (compositeObjective X k G θ) := by
  have hval := compositeObjective_eq_coe (k := k) hx hc
  have hpo : IsProper (compositeObjective X k G θ) :=
    ⟨⟨x,hval.trans_lt (EReal.coe_lt_top _)⟩,fun z ↦ EReal.bot_lt_add_iff.mpr
      ⟨EReal.bot_lt_add_iff.mpr ⟨((indicatorVA_isProper_iff X).mpr ⟨x,hx⟩).2 z,hp.2 (G z)⟩,EReal.bot_lt_coe _⟩⟩
  apply (mem_argmin_iff_zero_mem_subdifferential_of_convex hconv hpo hval).mpr
  apply regularSubdifferential_subset_subdifferential _ _
  apply regularSubdifferential_compositeObjective_superset hk hG hθ hp hx hc (isClarkeRegularAt_of_convex hX hx (RW.IsClosed.isLocallyClosedAt hclosed x))
  obtain ⟨y,hy,hn⟩ := hstat
  exact ⟨y,hy,by simpa only [zero_sub,sub_eq_add_neg,neg_add,zero_add] using hn⟩

end RW
