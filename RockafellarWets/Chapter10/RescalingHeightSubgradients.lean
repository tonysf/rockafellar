/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subgradients of the height formulation of nonlinear rescaling
-/

import RockafellarWets.Chapter10.RescalingEpigraphNormals
import RockafellarWets.Chapter10.CoordinateSubderivatives

open Set
open scoped Pointwise InnerProductSpace

namespace RW
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

abbrev rescalingHeightConstraint (f : E → EReal) : Set (WithLp 2 (ℝ × E)) :=
  (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ E) ⁻¹' euclideanEpigraph f

theorem rescalingHeightIntegrand_eq_indicator_add (f : E → EReal) (θ : ℝ → EReal) :
    rescalingHeightIntegrand f θ = indicatorVA (rescalingHeightConstraint f) +
      (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst) := by
  funext q
  change indicatorVA (euclideanEpigraph f) _ + _ = indicatorVA _ q + _
  congr 1

theorem isProper_heightFunction {θ : ℝ → EReal} (hp : IsProper θ) :
    IsProper (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst) := by
  obtain ⟨a,ha⟩ := hp.1
  exact ⟨⟨WithLp.toLp 2 (a,(0:E)),ha⟩,fun q ↦ hp.2 q.fst⟩

theorem rescaling_height_qualification {f : E → EReal} {θ : ℝ → EReal} {x : E} {c d : ℝ}
    (hθ : LowerSemicontinuous θ) (hx : f x = c) (hc : θ c = d)
    (hQ : 0 ∉ subdifferential f x ∨ horizonSubdifferential θ c = {0}) :
    ∀ y ∈ horizonSubdifferential (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst) (WithLp.toLp 2 (c,x)),
      -y ∈ normalCone (rescalingHeightConstraint f) (WithLp.toLp 2 (c,x)) → y = 0 := by
  intro y hy hn
  rw [horizonSubdifferential_heightFunction hθ hc x] at hy
  obtain ⟨t,ht,rfl⟩ := hy
  have hn' : WithLp.toLp 2 ((0:E),-t) ∈ normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
    simpa only [WithLp.neg_fst,WithLp.neg_snd,WithLp.toLp_fst,WithLp.toLp_snd,neg_zero]
      using (mem_normalCone_swapped_epigraph _ _).mp hn
  have ht0 : t = 0 := by
    rcases hQ with hQ | hQ
    · have hnonneg : 0 ≤ t := neg_nonpos.mp (vertical_nonpos_of_mem_normalCone_epigraph hn')
      by_contra hne
      obtain ⟨w,hw,he⟩ := (epigraph_normal_negative_slice hx (lt_of_le_of_ne hnonneg (Ne.symm hne))).mp hn'
      have hw0 : w = 0 := (smul_eq_zero.mp he.symm).resolve_left hne
      exact hQ (hw0 ▸ hw)
    · exact mem_singleton_iff.mp (hQ ▸ ht)
  simp [ht0]

theorem horizontal_normal_add_height_iff {f : E → EReal} {x v : E} {c : ℝ}
    (hf : LowerSemicontinuous f) (hx : f x = c) (Λ : Set ℝ) :
    WithLp.toLp 2 ((0:ℝ),v) ∈ normalCone (rescalingHeightConstraint f) (WithLp.toLp 2 (c,x)) +
      (fun t : ℝ ↦ WithLp.toLp 2 (t,(0:E))) '' Λ ↔ v ∈ rescalingSubgradientSet Λ f x := by
  rw [mem_rescalingSubgradientSet_iff_epigraph_normal hx hf]
  constructor
  · rintro ⟨a,ha,b,⟨t,ht,rfl⟩,he⟩
    have he1 := congrArg (fun q : WithLp 2 (ℝ × E) ↦ q.fst) he
    have he2 := congrArg (fun q : WithLp 2 (ℝ × E) ↦ q.snd) he
    have ha1 : a.fst = -t := by simpa only [WithLp.add_fst,WithLp.toLp_fst,add_eq_zero_iff_eq_neg] using he1
    have ha2 : a.snd = v := by simpa only [WithLp.add_snd,WithLp.toLp_snd,add_zero] using he2
    refine ⟨t,ht,?_⟩
    simpa only [ha1,ha2,WithLp.toLp_fst,WithLp.toLp_snd] using (mem_normalCone_swapped_epigraph _ _).mp ha
  · rintro ⟨t,ht,hn⟩
    refine ⟨WithLp.toLp 2 (-t,v), (mem_normalCone_swapped_epigraph _ _).mpr hn,
      WithLp.toLp 2 (t,(0:E)),⟨t,ht,rfl⟩,?_⟩
    apply WithLp.ofLp_injective
    ext <;> simp

/-- The qualification in 10.19(b) gives both horizontal multiplier inclusions. -/
theorem rescalingHeightIntegrand_subgradients {f : E → EReal} {θ : ℝ → EReal} {x : E} {c d : ℝ}
    (hf : LowerSemicontinuous f) (hpθ : IsProper θ) (hθ : LowerSemicontinuous θ)
    (hx : f x = c) (hc : θ c = d)
    (hQ : 0 ∉ subdifferential f x ∨ horizonSubdifferential θ c = {0}) :
    {v | WithLp.toLp 2 ((0:ℝ),v) ∈ subdifferential (rescalingHeightIntegrand f θ) (WithLp.toLp 2 (c,x))}
      ⊆ rescalingSubgradientSet (subdifferential θ c) f x ∧
    {v | WithLp.toLp 2 ((0:ℝ),v) ∈ horizonSubdifferential (rescalingHeightIntegrand f θ) (WithLp.toLp 2 (c,x))}
      ⊆ rescalingSubgradientSet (horizonSubdifferential θ c) f x := by
  have hC : IsClosed (rescalingHeightConstraint f) := (isClosed_euclideanEpigraph hf).preimage
    (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ E).continuous
  have hg : LowerSemicontinuous (fun q : WithLp 2 (ℝ × E) ↦ θ q.fst) := hθ.comp (WithLp.fstL 2 ℝ ℝ E).continuous
  have hmem : WithLp.toLp 2 (c,x) ∈ rescalingHeightConstraint f := hx.le
  have hqual := rescaling_height_qualification hθ hx hc hQ
  have hsub := subdifferential_indicator_add_subset hC hg (isProper_heightFunction hpθ) hmem hc hqual
  have hhor := horizonSubdifferential_indicator_add_subset hC hg (isProper_heightFunction hpθ) hmem hc hqual
  rw [← rescalingHeightIntegrand_eq_indicator_add,subdifferential_heightFunction hc x] at hsub
  rw [← rescalingHeightIntegrand_eq_indicator_add,horizonSubdifferential_heightFunction hθ hc x] at hhor
  exact ⟨fun _ hv ↦ (horizontal_normal_add_height_iff hf hx _).mp (hsub hv),
    fun _ hv ↦ (horizontal_normal_add_height_iff hf hx _).mp (hhor hv)⟩

end
end RW
