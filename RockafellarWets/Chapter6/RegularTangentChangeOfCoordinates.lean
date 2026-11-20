/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Regular tangents under a change of coordinates

Exercise 6.32, for arbitrary target sets. The proof uses the moving-base
sequential definition of regular tangency, strict differentiability, and the
inverse function theorem. No local closedness of the target set is needed.
-/

import RockafellarWets.Chapter6.RegularTangents

open Asymptotics Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section StrictDerivativeTransport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Strict differentiability transports scaled differences whose two base
points both approach the point of differentiation. -/
theorem HasStrictFDerivAt.tendsto_scaled_sub
    {H : E → F} {H' : E →L[ℝ] F} {x w : E}
    (hH : HasStrictFDerivAt H H' x)
    {ι : Type*} {l : Filter ι} {xs ys : ι → E} {c : ι → ℝ}
    (hxs : Tendsto xs l (nhds x)) (hys : Tendsto ys l (nhds x))
    (hq : Tendsto (fun n ↦ c n • (xs n - ys n)) l (nhds w)) :
    Tendsto (fun n ↦ c n • (H (xs n) - H (ys n))) l (nhds (H' w)) := by
  have herr := calc
    (fun n ↦ c n • (H (xs n) - H (ys n)) - H' (c n • (xs n - ys n)))
        =o[ℝ; l] (fun n ↦ c n • (xs n - ys n)) := by
      simpa [smul_sub] using
        (hH.isLittleOTVS.comp_tendsto (hxs.prodMk_nhds hys)).smul_left c
    _ =O[ℝ; l] (1 : ι → ℝ) := hq.isBigOTVS_one _
  rw [isLittleOTVS_one] at herr
  simpa using herr.add ((H'.continuous.tendsto w).comp hq)

/-- The selected points in the sequential definition may lie in the set only
eventually: a finite initial segment can be replaced by the feasible base point. -/
private theorem mem_regularTangentCone_of_eventual_sequences
    {C : Set E} {x w : E} (hx : x ∈ C)
    (h : ∀ (τs : ℕ → ℝ) (xbars : ℕ → E),
      (∀ n, 0 < τs n) → Tendsto τs atTop (nhds 0) →
      (∀ n, xbars n ∈ C) → Tendsto xbars atTop (nhds x) →
      ∃ xs : ℕ → E, (∀ᶠ n in atTop, xs n ∈ C) ∧
        Tendsto xs atTop (nhds x) ∧
        Tendsto (fun n ↦ (τs n)⁻¹ • (xs n - xbars n)) atTop (nhds w)) :
    w ∈ regularTangentCone C x := by
  rw [mem_regularTangentCone_iff_forall_sequences hx]
  intro τs xbars hτpos hτ0 hxbarC hxbarto
  obtain ⟨xs, hxsC, hxsto, hq⟩ := h τs xbars hτpos hτ0 hxbarC hxbarto
  obtain ⟨xs', hxs'C, hxs'to, hxseq⟩ :=
    exists_seq_mem_of_tendsto_nhdsWithin hx (tendsto_nhdsWithin_iff.2 ⟨hxsto, hxsC⟩)
  refine ⟨xs', hxs'C, hxs'to, hq.congr' ?_⟩
  filter_upwards [hxseq] with n hn
  rw [hn]

end StrictDerivativeTransport

section LocalDiffeomorphism

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Regular tangent cones transform by the derivative under a local change of
coordinates. This formula holds for every set at a feasible base point. -/
theorem regularTangentCone_preimage
    {Φ : E → F} {Φ' : E ≃L[ℝ] F} {x : E}
    (hΦ : HasStrictFDerivAt Φ (Φ' : E →L[ℝ] F) x)
    (S : Set F) (hx : Φ x ∈ S) :
    regularTangentCone (Φ ⁻¹' S) x =
      (Φ' : E →L[ℝ] F) ⁻¹' regularTangentCone S (Φ x) := by
  have hxpre : x ∈ Φ ⁻¹' S := hx
  let I : F → E := hΦ.localInverse Φ Φ' x
  have hIto : Tendsto I (nhds (Φ x)) (nhds x) := hΦ.localInverse_tendsto
  have hright : ∀ᶠ y in nhds (Φ x), Φ (I y) = y := hΦ.eventually_right_inverse
  have hleft : ∀ᶠ z in nhds x, I (Φ z) = z := hΦ.eventually_left_inverse
  have hI : HasStrictFDerivAt I (Φ'.symm : F →L[ℝ] E) (Φ x) := hΦ.to_localInverse
  refine Subset.antisymm ?_ ?_
  · intro w hw
    rw [mem_preimage, mem_regularTangentCone_iff_forall_sequences hx]
    intro τs ybars hτpos hτ0 hybarS hybarto
    have hliftto : Tendsto (fun n ↦ I (ybars n)) atTop (nhds x) := hIto.comp hybarto
    have hliftS : ∀ᶠ n in atTop, I (ybars n) ∈ Φ ⁻¹' S := by
      filter_upwards [hybarto.eventually hright] with n hn
      change Φ (I (ybars n)) ∈ S
      rw [hn]
      exact hybarS n
    obtain ⟨xbars, hxbarS, hxbarto, hxbars⟩ :=
      exists_seq_mem_of_tendsto_nhdsWithin hxpre
        (tendsto_nhdsWithin_iff.2 ⟨hliftto, hliftS⟩)
    obtain ⟨xs, hxsS, hxsto, hq⟩ :=
      (mem_regularTangentCone_iff_forall_sequences hxpre).1 hw
        τs xbars hτpos hτ0 hxbarS hxbarto
    refine ⟨fun n ↦ Φ (xs n), hxsS, hΦ.continuousAt.tendsto.comp hxsto, ?_⟩
    apply (RW.HasStrictFDerivAt.tendsto_scaled_sub hΦ hxsto hxbarto hq).congr'
    filter_upwards [hxbars, hybarto.eventually hright] with n hn hrightn
    rw [hn, hrightn]
  · intro w hw
    apply mem_regularTangentCone_of_eventual_sequences hxpre
    intro τs xbars hτpos hτ0 hxbarS hxbarto
    have hΦxbarto : Tendsto (fun n ↦ Φ (xbars n)) atTop (nhds (Φ x)) :=
      hΦ.continuousAt.tendsto.comp hxbarto
    obtain ⟨ys, hysS, hysto, hq⟩ :=
      (mem_regularTangentCone_iff_forall_sequences hx).1 hw
        τs (fun n ↦ Φ (xbars n)) hτpos hτ0 hxbarS hΦxbarto
    refine ⟨fun n ↦ I (ys n), ?_, hIto.comp hysto, ?_⟩
    · filter_upwards [hysto.eventually hright] with n hn
      change Φ (I (ys n)) ∈ S
      rw [hn]
      exact hysS n
    · have hlim := RW.HasStrictFDerivAt.tendsto_scaled_sub hI hysto hΦxbarto hq
      simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at hlim
      apply hlim.congr'
      filter_upwards [hxbarto.eventually hleft] with n hn
      rw [hn]

end LocalDiffeomorphism

section Product

variable {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- A free product coordinate contributes every regular tangent direction,
with the same moving bases and scales as the constrained coordinate. -/
theorem regularTangentCone_prod_univ {S : Set F} {u : F} (hu : u ∈ S) (b : N) :
    regularTangentCone (S ×ˢ (univ : Set N)) (u, b) =
      regularTangentCone S u ×ˢ (univ : Set N) := by
  have hub : (u, b) ∈ S ×ˢ (univ : Set N) := ⟨hu, mem_univ b⟩
  refine Subset.antisymm ?_ ?_
  · rintro ⟨w₁, w₂⟩ hw
    refine ⟨?_, mem_univ _⟩
    rw [mem_regularTangentCone_iff_forall_sequences hu]
    intro τs ubars hτpos hτ0 hubarS hubarto
    obtain ⟨ps, hpsS, hpsto, hq⟩ :=
      (mem_regularTangentCone_iff_forall_sequences hub).1 hw
        τs (fun n ↦ (ubars n, b)) hτpos hτ0
        (fun n ↦ ⟨hubarS n, mem_univ b⟩) (hubarto.prodMk_nhds tendsto_const_nhds)
    exact ⟨fun n ↦ (ps n).1, fun n ↦ (hpsS n).1, hpsto.fst_nhds, hq.fst_nhds⟩
  · rintro ⟨w₁, w₂⟩ ⟨hw₁, -⟩
    rw [mem_regularTangentCone_iff_forall_sequences hub]
    intro τs pbars hτpos hτ0 hpbarS hpbarto
    obtain ⟨xs, hxsS, hxsto, hq⟩ :=
      (mem_regularTangentCone_iff_forall_sequences hu).1 hw₁
        τs (fun n ↦ (pbars n).1) hτpos hτ0 (fun n ↦ (hpbarS n).1) hpbarto.fst_nhds
    refine ⟨fun n ↦ (xs n, (pbars n).2 + τs n • w₂),
      fun n ↦ ⟨hxsS n, mem_univ _⟩, ?_, ?_⟩
    · convert hxsto.prodMk_nhds (hpbarto.snd_nhds.add (hτ0.smul tendsto_const_nhds)) using 1
      simp
    · have hsnd : ∀ n,
          (τs n)⁻¹ • (((pbars n).2 + τs n • w₂) - (pbars n).2) = w₂ := by
        intro n
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (hτpos n).ne', one_smul]
      exact hq.prodMk_nhds (tendsto_const_nhds.congr fun n ↦ (hsnd n).symm)

end Product

section Submersion

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Exercise 6.32**: for a map with a surjective strict derivative, regular
tangents to a preimage are exactly the inverse images of regular tangents.

The augmented map pairs `G` with the orthogonal projection onto `ker G'`, so
its derivative is invertible. The free kernel coordinate is removed by the
product formula. This works for arbitrary `D`, without local closedness or
finite-dimensionality. A `C¹` map has a strict derivative, so the printed smooth full-rank
hypothesis is a special case. -/
theorem regularTangentCone_preimage_of_surjective {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x) (hsurj : Function.Surjective G')
    (D : Set F) (hx : G x ∈ D) :
    regularTangentCone (G ⁻¹' D) x = G' ⁻¹' regularTangentCone D (G x) := by
  have hkerclosed : IsClosed ((LinearMap.ker (G' : E →ₗ[ℝ] F) : Submodule ℝ E) : Set E) :=
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
      have hA : G' ((P w₀ : E)) = 0 := hPker w₀
      have hB : G' ((n : E)) = 0 := n.2
      rw [map_add, map_sub, hA, hB, hw₀, sub_zero, add_zero]
    have h2 : P (w₀ - (P w₀ : E) + (n : E)) = n := by
      have hA : P ((P w₀ : E)) = P w₀ := by
        have := hPself ((P w₀ : E)) (hPker w₀)
        exact Subtype.ext this
      have hB : P ((n : E)) = n := Subtype.ext (hPself (n : E) n.2)
      rw [map_add, map_sub, hA, hB, sub_self, zero_add]
    exact Prod.ext h1 h2
  set Ψ : E ≃L[ℝ] F × N := ContinuousLinearEquiv.ofBijective Q hkerQ hrangeQ with hΨ
  have hcoe : (Ψ : E →L[ℝ] F × N) = Q := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hΦ : HasStrictFDerivAt (fun z ↦ (G z, P z)) (Ψ : E →L[ℝ] F × N) x := by
    rw [hcoe, hQ]
    exact hG.prodMk P.hasStrictFDerivAt
  have hpre : (fun z ↦ (G z, P z)) ⁻¹' (D ×ˢ (univ : Set N)) = G ⁻¹' D := by
    ext z
    simp
  have hkey := regularTangentCone_preimage hΦ (D ×ˢ (univ : Set N))
    (show (G x, P x) ∈ D ×ˢ (univ : Set N) from ⟨hx, mem_univ _⟩)
  rw [hpre, regularTangentCone_prod_univ hx, hcoe] at hkey
  rw [hkey]
  ext w
  simp [hQ]

/-- The smooth full-rank form of Exercise 6.32, stated with the canonical
Fréchet derivative. Only `C¹` regularity at the base point is required. -/
theorem regularTangentCone_preimage_of_contDiffAt
    {G : E → F} {x : E} (hG : ContDiffAt ℝ 1 G x)
    (hsurj : Function.Surjective (fderiv ℝ G x))
    (D : Set F) (hx : G x ∈ D) :
    regularTangentCone (G ⁻¹' D) x = (fderiv ℝ G x) ⁻¹' regularTangentCone D (G x) :=
  regularTangentCone_preimage_of_surjective (hG.hasStrictFDerivAt one_ne_zero) hsurj D hx

end Submersion

end RW
