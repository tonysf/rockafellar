/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local sections of submersions

A map between real Hilbert spaces whose strict derivative is surjective has a
continuous local right inverse.  The proof augments the map by the orthogonal
projection onto the kernel of its derivative, applies the inverse function
theorem to the resulting square map, and then restricts the local inverse to
the affine slice through the base point.
-/

import RockafellarWets.Chapter6.ChangeOfCoordinates

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section LocalSubmersion

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A map with a surjective strict derivative has a local right inverse through
the base point.  Its strict derivative is a continuous linear right inverse of
the derivative of the original map. -/
theorem HasStrictFDerivAt.exists_local_rightInverse_of_surjective
    {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x) (hsurj : Function.Surjective G') :
    ∃ (R : F →L[ℝ] E) (s : F → E),
      G'.comp R = ContinuousLinearMap.id ℝ F ∧
      HasStrictFDerivAt s R (G x) ∧
      s (G x) = x ∧
      ∀ᶠ y in nhds (G x), G (s y) = y := by
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
    have hwG : G' w = 0 := congrArg Prod.fst hw
    have hwP : P w = 0 := congrArg Prod.snd hw
    have hwN : w ∈ N := hwG
    have hwself : (P w : E) = w := hPself w hwN
    rw [hwP] at hwself
    simpa using hwself.symm
  have hrangeQ : LinearMap.range (Q : E →ₗ[ℝ] F × N) = ⊤ := by
    rw [Submodule.eq_top_iff']
    rintro ⟨u, n⟩
    obtain ⟨w₀, hw₀⟩ := hsurj u
    refine ⟨w₀ - (P w₀ : E) + (n : E), ?_⟩
    have hGpart : G' (w₀ - (P w₀ : E) + (n : E)) = u := by
      have hPw₀ : G' (P w₀ : E) = 0 := hPker w₀
      have hn : G' (n : E) = 0 := n.2
      rw [map_add, map_sub, hPw₀, hn, hw₀, sub_zero, add_zero]
    have hPpart : P (w₀ - (P w₀ : E) + (n : E)) = n := by
      have hPPw₀ : P (P w₀ : E) = P w₀ := by
        exact Subtype.ext (hPself (P w₀ : E) (hPker w₀))
      have hPn : P (n : E) = n := Subtype.ext (hPself (n : E) n.2)
      rw [map_add, map_sub, hPPw₀, hPn, sub_self, zero_add]
    exact Prod.ext hGpart hPpart
  set Ψ : E ≃L[ℝ] F × N := ContinuousLinearEquiv.ofBijective Q hkerQ hrangeQ with hΨ
  have hcoe : (Ψ : E →L[ℝ] F × N) = Q :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  let Φ : E → F × N := fun z ↦ (G z, P z)
  have hΦ : HasStrictFDerivAt Φ (Ψ : E →L[ℝ] F × N) x := by
    rw [hcoe, hQ]
    exact hG.prodMk P.hasStrictFDerivAt
  set I : F →L[ℝ] F × N :=
    (ContinuousLinearMap.id ℝ F).prod (0 : F →L[ℝ] N) with hI
  let ι : F → F × N := fun y ↦ (y, P x)
  have hι : HasStrictFDerivAt ι I (G x) := by
    rw [hI]
    exact (hasStrictFDerivAt_id (G x)).prodMk (hasStrictFDerivAt_const (P x) (G x))
  let R : F →L[ℝ] E := (Ψ.symm : F × N →L[ℝ] E).comp I
  let s : F → E := fun y ↦ hΦ.localInverse Φ Ψ x (ι y)
  have hR : G'.comp R = ContinuousLinearMap.id ℝ F := by
    apply ContinuousLinearMap.ext
    intro y
    have hinv : Q (Ψ.symm (I y)) = I y := by
      rw [← hcoe]
      exact Ψ.apply_symm_apply (I y)
    have hfst := congrArg Prod.fst hinv
    rw [hQ] at hfst
    simpa [R, hI] using hfst
  have hs : HasStrictFDerivAt s R (G x) := by
    simpa [s, R, ι, Φ] using hΦ.to_localInverse.comp (G x) hι
  have hsx : s (G x) = x := by
    simp [s, ι, Φ]
  have hright : ∀ᶠ y in nhds (G x), G (s y) = y := by
    have hlocal :
        ∀ᶠ y in nhds (G x),
          Φ (hΦ.localInverse Φ Ψ x (ι y)) = ι y := by
      exact hι.continuousAt.eventually <| by
        simpa [ι, Φ] using hΦ.eventually_right_inverse
    filter_upwards [hlocal] with y hy
    simpa [s, ι, Φ] using congrArg Prod.fst hy
  exact ⟨R, s, hR, hs, hsx, hright⟩

/-- Neighborhood form of the local submersion theorem.  The section maps a
neighborhood of `G x` into a neighborhood of `x`, and is an exact right
inverse there. -/
theorem HasStrictFDerivAt.exists_local_rightInverse_neighborhoods_of_surjective
    {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x) (hsurj : Function.Surjective G') :
    ∃ (R : F →L[ℝ] E) (s : F → E),
      G'.comp R = ContinuousLinearMap.id ℝ F ∧
      HasStrictFDerivAt s R (G x) ∧
      s (G x) = x ∧
      ∃ U ∈ nhds x, ∃ V ∈ nhds (G x),
        Set.MapsTo s V U ∧ Set.EqOn (G ∘ s) id V := by
  obtain ⟨R, s, hR, hs, hsx, hright⟩ :=
    RW.HasStrictFDerivAt.exists_local_rightInverse_of_surjective hG hsurj
  refine ⟨R, s, hR, hs, hsx, ?_⟩
  let U : Set E := Metric.ball x 1
  have hU : U ∈ nhds x := Metric.ball_mem_nhds x zero_lt_one
  have hsto : Tendsto s (nhds (G x)) (nhds x) := by
    simpa [hsx] using hs.continuousAt.tendsto
  have hsU : s ⁻¹' U ∈ nhds (G x) := hsto.eventually hU
  let V : Set F := s ⁻¹' U ∩ {y | G (s y) = y}
  have hV : V ∈ nhds (G x) := by
    exact inter_mem hsU hright
  refine ⟨U, hU, V, hV, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    simpa only [Function.comp_apply, id_eq] using hy.2

omit [CompleteSpace E] [CompleteSpace F] in
/-- A convergent family in the target can be lifted through a local section:
the lifts converge to the base point and have the prescribed image
eventually. -/
theorem HasStrictFDerivAt.lift_through_local_rightInverse
    {G : E → F} {x : E} {R : F →L[ℝ] E} {s : F → E}
    (hs : HasStrictFDerivAt s R (G x)) (hsx : s (G x) = x)
    (hright : ∀ᶠ y in nhds (G x), G (s y) = y)
    {I : Type*} {l : Filter I} {ys : I → F}
    (hys : Tendsto ys l (nhds (G x))) :
    Tendsto (s ∘ ys) l (nhds x) ∧
      ∀ᶠ i in l, G (s (ys i)) = ys i := by
  have hsto : Tendsto s (nhds (G x)) (nhds x) := by
    simpa [hsx] using hs.continuousAt.tendsto
  constructor
  · exact hsto.comp hys
  · exact hys.eventually hright

/-- Target values tending to `G x` have lifts supplied by the local
submersion section. -/
theorem HasStrictFDerivAt.exists_local_lift_of_surjective
    {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x) (hsurj : Function.Surjective G')
    {I : Type*} {l : Filter I} {ys : I → F}
    (hys : Tendsto ys l (nhds (G x))) :
    ∃ (R : F →L[ℝ] E) (s : F → E),
      G'.comp R = ContinuousLinearMap.id ℝ F ∧
      HasStrictFDerivAt s R (G x) ∧
      s (G x) = x ∧
      Tendsto (s ∘ ys) l (nhds x) ∧
      ∀ᶠ i in l, G (s (ys i)) = ys i := by
  obtain ⟨R, s, hR, hs, hsx, hright⟩ :=
    RW.HasStrictFDerivAt.exists_local_rightInverse_of_surjective hG hsurj
  obtain ⟨htendsto, himage⟩ :=
    RW.HasStrictFDerivAt.lift_through_local_rightInverse hs hsx hright hys
  exact ⟨R, s, hR, hs, hsx, htendsto, himage⟩

/-- **Uniform local solvability.**  A map with a surjective strict derivative
solves `G y = u` from any nearby starting point `q`, with an error controlled
linearly by the residual `u - G q` and a constant independent of `q`.

This is stronger than the section through the base point, which only solves
from `x` itself, and it is what a *moving* base point needs.  The solving map
is `σ(u, q) = Ψ(u, P q)`, where `Φ = (G, P)` is the augmented map of the
submersion theorem and `Ψ` its local inverse: the second coordinate keeps the
starting point's kernel component, so `σ(G q, q) = q`, and the estimate is the
local Lipschitz bound of `Ψ` read against the sup norm of the product. -/
theorem HasStrictFDerivAt.exists_uniform_local_solve_of_surjective
    {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x) (hsurj : Function.Surjective G') :
    ∃ (κ : ℝ) (σ : F × E → E), 0 < κ ∧
      ∀ᶠ r in nhds ((G x, x) : F × E),
        G (σ r) = r.1 ∧ ‖σ r - r.2‖ ≤ κ * ‖r.1 - G r.2‖ := by
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
    intro v hv
    have hv1 : G' v = 0 := congrArg Prod.fst hv
    have hv2 : P v = 0 := congrArg Prod.snd hv
    have hvN : v ∈ N := hv1
    have hself : (P v : E) = v := hPself v hvN
    rw [hv2] at hself
    simpa using hself.symm
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
      have hA : P ((P w₀ : E)) = P w₀ := Subtype.ext (hPself ((P w₀ : E)) (hPker w₀))
      have hB : P ((n : E)) = n := Subtype.ext (hPself (n : E) n.2)
      rw [map_add, map_sub, hA, hB, sub_self, zero_add]
    exact Prod.ext h1 h2
  set Ψ : E ≃L[ℝ] F × N := ContinuousLinearEquiv.ofBijective Q hkerQ hrangeQ with hΨ
  have hcoe : (Ψ : E →L[ℝ] F × N) = Q := ContinuousLinearEquiv.coe_ofBijective _ _ _
  set Φ : E → F × N := fun z ↦ (G z, P z) with hΦdef
  have hΦ : HasStrictFDerivAt Φ (Ψ : E →L[ℝ] F × N) x := by
    rw [hcoe, hQ]
    exact hG.prodMk P.hasStrictFDerivAt
  set L : F × N → E := hΦ.localInverse Φ Ψ x with hL
  have hLderiv : HasStrictFDerivAt L (Ψ.symm : F × N →L[ℝ] E) (Φ x) :=
    hΦ.to_localInverse
  -- a local Lipschitz bound for the local inverse
  have hlip : ∀ᶠ p in nhds ((Φ x, Φ x) : (F × N) × (F × N)),
      ‖L p.1 - L p.2 - (Ψ.symm : F × N →L[ℝ] E) (p.1 - p.2)‖ ≤ 1 * ‖p.1 - p.2‖ :=
    hLderiv.isLittleO.def one_pos
  rw [nhds_prod_eq] at hlip
  obtain ⟨W₁, hW₁, W₂, hW₂, hWsub⟩ := Filter.mem_prod_iff.1 hlip
  set W : Set (F × N) := W₁ ∩ W₂ with hWdef
  have hW : W ∈ nhds (Φ x) := Filter.inter_mem hW₁ hW₂
  have hWlip : ∀ p ∈ W, ∀ p' ∈ W,
      ‖L p - L p'‖ ≤ (‖(Ψ.symm : F × N →L[ℝ] E)‖ + 1) * ‖p - p'‖ := by
    intro p hp p' hp'
    have hmem : (p, p') ∈ W₁ ×ˢ W₂ := ⟨hp.1, hp'.2⟩
    have hbound := hWsub hmem
    have hop : ‖(Ψ.symm : F × N →L[ℝ] E) (p - p')‖
        ≤ ‖(Ψ.symm : F × N →L[ℝ] E)‖ * ‖p - p'‖ :=
      (Ψ.symm : F × N →L[ℝ] E).le_opNorm _
    have htri : ‖L p - L p'‖
        ≤ ‖(Ψ.symm : F × N →L[ℝ] E) (p - p')‖
          + ‖L p - L p' - (Ψ.symm : F × N →L[ℝ] E) (p - p')‖ := by
      have h := norm_add_le ((Ψ.symm : F × N →L[ℝ] E) (p - p'))
        (L p - L p' - (Ψ.symm : F × N →L[ℝ] E) (p - p'))
      have heq : (Ψ.symm : F × N →L[ℝ] E) (p - p')
          + (L p - L p' - (Ψ.symm : F × N →L[ℝ] E) (p - p')) = L p - L p' := by abel
      rwa [heq] at h
    simp only [Set.mem_setOf_eq] at hbound
    linarith
  refine ⟨‖(Ψ.symm : F × N →L[ℝ] E)‖ + 1, fun r ↦ L (r.1, P r.2), by positivity, ?_⟩
  -- the two neighborhoods that make the construction work
  have hcontΦ : ContinuousAt Φ x := hΦ.continuousAt
  have hAmem : (fun r : F × E ↦ ((r.1, P r.2) : F × N)) ⁻¹' W ∈ nhds ((G x, x) : F × E) := by
    have hcont : Continuous fun r : F × E ↦ ((r.1, P r.2) : F × N) :=
      continuous_fst.prodMk (P.continuous.comp continuous_snd)
    exact hcont.continuousAt.preimage_mem_nhds hW
  have hBmem : (fun r : F × E ↦ r.2) ⁻¹' {z | L (Φ z) = z} ∈ nhds ((G x, x) : F × E) :=
    continuousAt_snd.preimage_mem_nhds hΦ.eventually_left_inverse
  have hCmem : (fun r : F × E ↦ (Φ r.2)) ⁻¹' W ∈ nhds ((G x, x) : F × E) := by
    have hcont : ContinuousAt (fun r : F × E ↦ Φ r.2) ((G x, x) : F × E) := by
      have h : ContinuousAt (Φ ∘ (Prod.snd : F × E → E)) ((G x, x) : F × E) :=
        hcontΦ.comp continuousAt_snd
      exact h
    exact hcont.preimage_mem_nhds hW
  have hDmem : (fun r : F × E ↦ ((r.1, P r.2) : F × N)) ⁻¹' {p | Φ (L p) = p}
      ∈ nhds ((G x, x) : F × E) := by
    have hcont : Continuous fun r : F × E ↦ ((r.1, P r.2) : F × N) :=
      continuous_fst.prodMk (P.continuous.comp continuous_snd)
    exact hcont.continuousAt.preimage_mem_nhds hΦ.eventually_right_inverse
  filter_upwards [hAmem, hBmem, hCmem, hDmem] with r hA hB hC hD
  have hΦr : Φ r.2 = (G r.2, P r.2) := rfl
  constructor
  · have h := hD
    simp only [mem_preimage, mem_setOf_eq] at h
    exact congrArg Prod.fst h
  · have hq : L (Φ r.2) = r.2 := hB
    have hkey : ‖L (r.1, P r.2) - L (Φ r.2)‖
        ≤ (‖(Ψ.symm : F × N →L[ℝ] E)‖ + 1) * ‖((r.1, P r.2) : F × N) - Φ r.2‖ :=
      hWlip _ hA _ hC
    rw [hq] at hkey
    have hsub : ((r.1, P r.2) : F × N) - Φ r.2 = (r.1 - G r.2, 0) := by
      rw [hΦr]
      simp
    rw [hsub] at hkey
    simpa using hkey


end LocalSubmersion

end RW
