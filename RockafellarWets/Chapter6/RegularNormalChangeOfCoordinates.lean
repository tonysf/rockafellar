/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Regular-normal change of coordinates

This file proves the regular-normal clause of Exercise 6.7. The proof uses
the `L²` product `WithLp 2 (F × ker G')` for the augmented codomain, so the
augmented derivative is a map of Hilbert spaces and has an adjoint.
-/

import RockafellarWets.Chapter6.ChangeOfCoordinates
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section RegularNormalLocality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A P03-local version of regular-normal locality. The eventual inequality
in Definition 6.3 is unchanged after intersecting with a neighborhood of the
base point. -/
private theorem regularNormalCone_inter_nhds_p03
    {C U : Set E} {x : E} (hU : U ∈ 𝓝 x) :
    regularNormalCone (C ∩ U) x = regularNormalCone C x := by
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hnhds : 𝓝[C ∩ U] x = 𝓝[C] x :=
    nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds hU)
  ext v
  rw [mem_regularNormalCone, mem_regularNormalCone]
  constructor
  · rintro ⟨⟨hxC, -⟩, hv⟩
    exact ⟨hxC, by simpa only [hnhds] using hv⟩
  · rintro ⟨hxC, hv⟩
    exact ⟨⟨hxC, hxU⟩, by simpa only [hnhds] using hv⟩

end RegularNormalLocality

section RegularNormalPullback

variable {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The adjoint derivative pulls regular normals back through a differentiable
map. This one-way chain rule only needs ordinary Fréchet differentiability. -/
theorem adjoint_image_regularNormalCone_subset_preimage
    {H : E → K} {H' : E →L[ℝ] K} {a : E}
    (hH : HasFDerivAt H H' a) (S : Set K) :
    ContinuousLinearMap.adjoint H' '' regularNormalCone S (H a) ⊆
      regularNormalCone (H ⁻¹' S) a := by
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨hv.1, ?_⟩
  intro ε hε
  have hnormalCoeff : 0 < ε / (2 * (‖H'‖ + 1)) := by positivity
  have herrorCoeff : 0 < ε / (2 * (‖v‖ + 1)) := by positivity
  have hmap : Tendsto H (𝓝[H ⁻¹' S] a) (𝓝[S] H a) :=
    hH.continuousAt.continuousWithinAt.tendsto_nhdsWithin fun _ hy ↦ hy
  have hnormal : ∀ᶠ y in 𝓝[H ⁻¹' S] a,
      ⟪v, H y - H a⟫_ℝ ≤ ε / (2 * (‖H'‖ + 1)) * ‖H y - H a‖ :=
    hmap (hv.2 _ hnormalCoeff)
  have herrorOne : ∀ᶠ y in 𝓝[H ⁻¹' S] a,
      ‖H y - H a - H' (y - a)‖ ≤ 1 * ‖y - a‖ :=
    nhdsWithin_le_nhds (hH.isLittleO.def (by positivity : (0 : ℝ) < 1))
  have herrorSmall : ∀ᶠ y in 𝓝[H ⁻¹' S] a,
      ‖H y - H a - H' (y - a)‖ ≤
        ε / (2 * (‖v‖ + 1)) * ‖y - a‖ :=
    nhdsWithin_le_nhds (hH.isLittleO.def herrorCoeff)
  filter_upwards [hnormal, herrorOne, herrorSmall] with y hy hOne hSmall
  have hHbound : ‖H y - H a‖ ≤ (‖H'‖ + 1) * ‖y - a‖ := by
    calc
      ‖H y - H a‖ =
          ‖H' (y - a) + (H y - H a - H' (y - a))‖ := by congr 1; abel
      _ ≤ ‖H' (y - a)‖ + ‖H y - H a - H' (y - a)‖ := norm_add_le _ _
      _ ≤ ‖H'‖ * ‖y - a‖ + 1 * ‖y - a‖ :=
        add_le_add (H'.le_opNorm _) hOne
      _ = (‖H'‖ + 1) * ‖y - a‖ := by ring
  have hnormalBound :
      ε / (2 * (‖H'‖ + 1)) * ‖H y - H a‖ ≤ ε / 2 * ‖y - a‖ := by
    calc
      ε / (2 * (‖H'‖ + 1)) * ‖H y - H a‖ ≤
          ε / (2 * (‖H'‖ + 1)) * ((‖H'‖ + 1) * ‖y - a‖) :=
        mul_le_mul_of_nonneg_left hHbound hnormalCoeff.le
      _ = ε / 2 * ‖y - a‖ := by field_simp
  have herrorInner :
      -⟪v, H y - H a - H' (y - a)⟫_ℝ ≤
        ‖v‖ * ‖H y - H a - H' (y - a)‖ :=
    (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have hcoef : ‖v‖ * (ε / (2 * (‖v‖ + 1))) ≤ ε / 2 := by
    calc
      ‖v‖ * (ε / (2 * (‖v‖ + 1))) =
          (‖v‖ * ε) / (2 * (‖v‖ + 1)) := by ring
      _ ≤ ε / 2 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (‖v‖ + 1))]
        nlinarith [norm_nonneg v]
  have herrorBound :
      ‖v‖ * ‖H y - H a - H' (y - a)‖ ≤ ε / 2 * ‖y - a‖ := by
    calc
      ‖v‖ * ‖H y - H a - H' (y - a)‖ ≤
          ‖v‖ * (ε / (2 * (‖v‖ + 1)) * ‖y - a‖) :=
        mul_le_mul_of_nonneg_left hSmall (norm_nonneg v)
      _ = (‖v‖ * (ε / (2 * (‖v‖ + 1)))) * ‖y - a‖ := by ring
      _ ≤ ε / 2 * ‖y - a‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hsplit : ⟪v, H' (y - a)⟫_ℝ =
      ⟪v, H y - H a⟫_ℝ - ⟪v, H y - H a - H' (y - a)⟫_ℝ := by
    calc
      ⟪v, H' (y - a)⟫_ℝ =
          ⟪v, (H y - H a) - (H y - H a - H' (y - a))⟫_ℝ := by
        congr 1
        abel
      _ = ⟪v, H y - H a⟫_ℝ - ⟪v, H y - H a - H' (y - a)⟫_ℝ :=
        inner_sub_right _ _ _
  rw [hsplit]
  nlinarith

end RegularNormalPullback

section RegularNormalLocalDiffeomorphism

/-- Regular normal cones transform by the adjoint derivative under a local
change of coordinates. -/
theorem regularNormalCone_preimage
    {E K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    {Phi : E → K} {Phi' : E ≃L[ℝ] K} {x : E}
    (hPhi : HasStrictFDerivAt Phi (Phi' : E →L[ℝ] K) x) (S : Set K) :
    regularNormalCone (Phi ⁻¹' S) x =
      ContinuousLinearMap.adjoint (Phi' : E →L[ℝ] K) ''
        regularNormalCone S (Phi x) := by
  refine Set.Subset.antisymm ?_
    (adjoint_image_regularNormalCone_subset_preimage hPhi.hasFDerivAt S)
  intro v hv
  obtain ⟨V, hV, hVinv⟩ :=
    Filter.eventually_iff_exists_mem.1 hPhi.eventually_right_inverse
  let L : K → E := hPhi.localInverse Phi Phi' x
  have hLderiv : HasFDerivAt L (Phi'.symm : K →L[ℝ] E) (Phi x) :=
    hPhi.to_localInverse.hasFDerivAt
  have hLbase : L (Phi x) = x := hPhi.localInverse_apply_image
  have hadjmem :
      ContinuousLinearMap.adjoint (Phi'.symm : K →L[ℝ] E) v ∈
        regularNormalCone (L ⁻¹' (Phi ⁻¹' S)) (Phi x) := by
    have hvL : v ∈ regularNormalCone (Phi ⁻¹' S) (L (Phi x)) := by
      simpa only [hLbase] using hv
    exact adjoint_image_regularNormalCone_subset_preimage
      hLderiv (Phi ⁻¹' S) ⟨v, hvL, rfl⟩
  have hset : (L ⁻¹' (Phi ⁻¹' S)) ∩ V = S ∩ V := by
    ext y
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hyS, hyV⟩
      exact ⟨by simpa [L, hVinv y hyV] using hyS, hyV⟩
    · rintro ⟨hyS, hyV⟩
      exact ⟨by simpa [L, hVinv y hyV] using hyS, hyV⟩
  have hadjmemS :
      ContinuousLinearMap.adjoint (Phi'.symm : K →L[ℝ] E) v ∈
        regularNormalCone S (Phi x) := by
    rw [← regularNormalCone_inter_nhds_p03 hV, ← hset,
      regularNormalCone_inter_nhds_p03 hV]
    exact hadjmem
  refine ⟨ContinuousLinearMap.adjoint (Phi'.symm : K →L[ℝ] E) v,
    hadjmemS, ?_⟩
  apply ext_inner_right ℝ
  intro w
  calc
    ⟪ContinuousLinearMap.adjoint (Phi' : E →L[ℝ] K)
          (ContinuousLinearMap.adjoint (Phi'.symm : K →L[ℝ] E) v), w⟫_ℝ =
        ⟪ContinuousLinearMap.adjoint (Phi'.symm : K →L[ℝ] E) v,
          (Phi' : E →L[ℝ] K) w⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪v, (Phi'.symm : K →L[ℝ] E) ((Phi' : E →L[ℝ] K) w)⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪v, w⟫_ℝ := by simp

end RegularNormalLocalDiffeomorphism

section L2Cylinder

/-- The cylinder over `D` in the Hilbert `L²` product. -/
def l2Cylinder {F N : Type*} (D : Set F) : Set (WithLp 2 (F × N)) :=
  {z | z.fst ∈ D}

variable {F N : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N]

/-- Regular normals to an `L²` cylinder are precisely the regular normals
to its base, with zero component in the free coordinate. -/
theorem regularNormalCone_l2Cylinder (D : Set F) (u : F) (b : N) :
    regularNormalCone (l2Cylinder D) (WithLp.toLp 2 (u, b)) =
      WithLp.toLp 2 '' (regularNormalCone D u ×ˢ ({0} : Set N)) := by
  ext q
  constructor
  · intro hq
    rw [mem_regularNormalCone_iff] at hq
    have huD : u ∈ D := by
      simpa [l2Cylinder] using hq.1
    have hfst : q.fst ∈ regularNormalCone D u := by
      rw [mem_regularNormalCone_iff]
      refine ⟨huD, ?_⟩
      intro ε hε
      obtain ⟨δ, hδ, hqδ⟩ := hq.2 ε hε
      refine ⟨δ, hδ, ?_⟩
      intro y hyD hyδ
      have hmem : WithLp.toLp 2 (y, b) ∈ l2Cylinder D := by
        exact hyD
      have hnorm :
          ‖WithLp.toLp 2 (y, b) - WithLp.toLp 2 (u, b)‖ = ‖y - u‖ := by
        rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_fst]
      have h := hqδ (WithLp.toLp 2 (y, b)) hmem (by simpa [hnorm] using hyδ)
      simpa [WithLp.prod_inner_apply, hnorm] using h
    have htangent : ∀ w : N,
        WithLp.toLp 2 (0, w) ∈
          tangentCone (l2Cylinder D) (WithLp.toLp 2 (u, b)) := by
      intro w
      let τs : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
      refine mem_tangentCone_of_forall
        (xs := fun n ↦ WithLp.toLp 2 (u, b + τs n • w))
        (τs := τs) ?_ ?_ ?_ ?_
      · intro n
        exact huD
      · intro n
        dsimp [τs]
        positivity
      · dsimp [τs]
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      · apply tendsto_const_nhds.congr'
        filter_upwards [] with n
        dsimp [τs]
        rw [← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, add_sub_cancel_left,
          ← WithLp.toLp_smul]
        simp only [Prod.smul_mk, smul_zero, one_div, inv_inv]
        rw [← mul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    have hsnd : q.snd = 0 := by
      apply ext_inner_right ℝ
      intro w
      have hp := inner_nonpos_of_mem_regularNormalCone
        (C := l2Cylinder D) (x := WithLp.toLp 2 (u, b))
        (v := q) (by rwa [mem_regularNormalCone_iff]) (htangent w)
      have hn := inner_nonpos_of_mem_regularNormalCone
        (C := l2Cylinder D) (x := WithLp.toLp 2 (u, b))
        (v := q) (by rwa [mem_regularNormalCone_iff]) (htangent (-w))
      simp only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
        inner_zero_right, zero_add, inner_neg_right] at hp hn
      simp only [inner_zero_left]
      linarith
    refine ⟨(q.fst, 0), ⟨hfst, rfl⟩, ?_⟩
    have hpair : (q.fst, (0 : N)) = WithLp.ofLp q := by
      apply Prod.ext
      · rfl
      · exact hsnd.symm
    calc
      WithLp.toLp 2 (q.fst, 0) = WithLp.toLp 2 (WithLp.ofLp q) :=
        congrArg (WithLp.toLp 2) hpair
      _ = q := WithLp.toLp_ofLp 2 q
  · rintro ⟨⟨v, n⟩, ⟨hv, hn⟩, rfl⟩
    simp only [Set.mem_singleton_iff] at hn
    subst n
    rw [mem_regularNormalCone_iff] at hv ⊢
    refine ⟨?_, ?_⟩
    · exact hv.1
    · intro ε hε
      obtain ⟨δ, hδ, hvδ⟩ := hv.2 ε hε
      refine ⟨δ, hδ, ?_⟩
      intro z hz hzδ
      have hfstnorm : ‖z.fst - u‖ ≤ ‖z - WithLp.toLp 2 (u, b)‖ := by
        simpa using WithLp.norm_fst_le (p := 2) (F) (z - WithLp.toLp 2 (u, b))
      have hfstlt : ‖z.fst - u‖ < δ := lt_of_le_of_lt hfstnorm hzδ
      have hvineq := hvδ z.fst hz hfstlt
      rw [WithLp.prod_inner_apply]
      simp only [inner_zero_left, add_zero]
      exact hvineq.trans (mul_le_mul_of_nonneg_left hfstnorm hε.le)

end L2Cylinder

section L2AugmentedAdjoint

variable {E F N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N] [CompleteSpace N]

/-- The adjoint of an `L²`-augmented equivalence, evaluated on a vector in
the first coordinate, is the adjoint of that first coordinate map. -/
theorem adjoint_l2Augmentation_toLp_fst
    (G' : E →L[ℝ] F) (P : E →L[ℝ] N)
    (Psi : E ≃L[ℝ] WithLp 2 (F × N))
    (hPsiApply : ∀ z, Psi z = WithLp.toLp 2 (G' z, P z)) (v : F) :
    ContinuousLinearMap.adjoint (Psi : E →L[ℝ] WithLp 2 (F × N))
        (WithLp.toLp 2 (v, 0)) =
      ContinuousLinearMap.adjoint G' v := by
  apply ext_inner_right ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  change ⟪WithLp.toLp 2 (v, 0), Psi z⟫_ℝ = ⟪v, G' z⟫_ℝ
  rw [hPsiApply]
  simp [WithLp.prod_inner_apply]

end L2AugmentedAdjoint

section RegularNormalChangeOfCoordinates

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Exercise 6.7**, the regular-normal clause: if `G'` is surjective, the
regular normals to `G ⁻¹' D` are exactly the adjoint images of the regular
normals to `D`.

The proof augments `G` by the orthogonal projection onto `ker G'`. Its target
is the Hilbert product `WithLp 2 (F × ker G')`, rather than the sup-normed
ordinary product, so the augmented derivative has an adjoint. -/
theorem regularNormalCone_preimage_of_surjective
    {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x)
    (hsurj : Function.Surjective G')
    (D : Set F) :
    regularNormalCone (G ⁻¹' D) x =
      ContinuousLinearMap.adjoint G' '' regularNormalCone D (G x) := by
  have hkerclosed :
      IsClosed ((LinearMap.ker (G' : E →ₗ[ℝ] F) : Submodule ℝ E) : Set E) :=
    ContinuousLinearMap.isClosed_ker G'
  haveI : CompleteSpace ((LinearMap.ker (G' : E →ₗ[ℝ] F) : Submodule ℝ E)) :=
    hkerclosed.completeSpace_coe
  set N : Submodule ℝ E := LinearMap.ker (G' : E →ₗ[ℝ] F) with hN
  set P : E →L[ℝ] N := N.orthogonalProjection with hP
  have hPself : ∀ (z : E) (hz : z ∈ N), (P z : E) = z := by
    intro z hz
    have hself := Submodule.orthogonalProjection_mem_subspace_eq_self (K := N) ⟨z, hz⟩
    rw [hP, hself]
  have hPker : ∀ z : E, (P z : E) ∈ N := fun z ↦ (P z).2
  set Q : E →L[ℝ] F × N := G'.prod P with hQ
  have hkerQ : LinearMap.ker (Q : E →ₗ[ℝ] F × N) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hw1 : G' w = 0 := congrArg Prod.fst hw
    have hw2 : P w = 0 := congrArg Prod.snd hw
    have hwN : w ∈ N := hw1
    have : (P w : E) = w := hPself w hwN
    rw [hw2] at this
    simpa using this.symm
  have hrangeQ : LinearMap.range (Q : E →ₗ[ℝ] F × N) = ⊤ := by
    rw [Submodule.eq_top_iff']
    rintro ⟨u, n⟩
    obtain ⟨w₀, hw₀⟩ := hsurj u
    refine ⟨w₀ - (P w₀ : E) + (n : E), ?_⟩
    have h1 : G' (w₀ - (P w₀ : E) + (n : E)) = u := by
      have hA : G' (P w₀ : E) = 0 := hPker w₀
      have hB : G' (n : E) = 0 := n.2
      rw [map_add, map_sub, hA, hB, hw₀, sub_zero, add_zero]
    have h2 : P (w₀ - (P w₀ : E) + (n : E)) = n := by
      have hA : P (P w₀ : E) = P w₀ := by
        have := hPself (P w₀ : E) (hPker w₀)
        exact Subtype.ext this
      have hB : P (n : E) = n := Subtype.ext (hPself (n : E) n.2)
      rw [map_add, map_sub, hA, hB, sub_self, zero_add]
    exact Prod.ext h1 h2
  set Psi0 : E ≃L[ℝ] F × N :=
    ContinuousLinearEquiv.ofBijective Q hkerQ hrangeQ with hPsi0
  have hcoe0 : (Psi0 : E →L[ℝ] F × N) = Q :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  set Psi : E ≃L[ℝ] WithLp 2 (F × N) :=
    Psi0.trans (WithLp.prodContinuousLinearEquiv 2 ℝ F N).symm with hPsi
  have hPsiApply : ∀ z : E, Psi z = WithLp.toLp 2 (G' z, P z) := by
    intro z
    rw [hPsi]
    simp only [ContinuousLinearEquiv.trans_apply,
      WithLp.prodContinuousLinearEquiv_symm_apply]
    have hPsi0Apply : Psi0 z = Q z := by
      change (Psi0 : E →L[ℝ] F × N) z = Q z
      rw [hcoe0]
    rw [hPsi0Apply, hQ]
    rfl
  let Phi : E → WithLp 2 (F × N) := fun z ↦ WithLp.toLp 2 (G z, P z)
  have hPhi : HasStrictFDerivAt Phi
      (Psi : E →L[ℝ] WithLp 2 (F × N)) x := by
    have hcomp :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ F N).symm.hasStrictFDerivAt.comp x
        (hG.prodMk P.hasStrictFDerivAt)
    rw [hPsi]
    simpa only [Phi, WithLp.prodContinuousLinearEquiv_symm_apply] using hcomp
  have hpre : Phi ⁻¹' l2Cylinder D = G ⁻¹' D := by
    ext z
    simp [Phi, l2Cylinder]
  have hadj : ∀ v : F,
      ContinuousLinearMap.adjoint (Psi : E →L[ℝ] WithLp 2 (F × N))
          (WithLp.toLp 2 (v, 0)) =
        ContinuousLinearMap.adjoint G' v := by
    intro v
    exact adjoint_l2Augmentation_toLp_fst G' P Psi hPsiApply v
  have hchange := regularNormalCone_preimage hPhi (l2Cylinder D)
  rw [hpre, regularNormalCone_l2Cylinder] at hchange
  rw [hchange]
  refine Set.Subset.antisymm ?_ ?_
  · rintro q ⟨z, ⟨⟨v, n⟩, ⟨hv, hn⟩, rfl⟩, rfl⟩
    simp only [Set.mem_singleton_iff] at hn
    subst n
    exact ⟨v, hv, (hadj v).symm⟩
  · rintro q ⟨v, hv, rfl⟩
    refine ⟨WithLp.toLp 2 (v, 0), ?_, hadj v⟩
    exact ⟨(v, 0), ⟨hv, rfl⟩, rfl⟩

end RegularNormalChangeOfCoordinates

end RW
