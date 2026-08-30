/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Change of Coordinates

Exercise 6.7 prints three formulas for `C = F⁻¹(D)` at a point where
`∇F(x̄)` has full rank.  This file proves the first of them, the tangent cone
formula, and the reusable transport lemmas it rests on: monotonicity and
locality of the tangent cone, the push-forward of tangent vectors through a
differentiable map, the tangent cone to `S × IRᵏ`, and the change of
coordinates itself, `T_{Φ⁻¹(S)}(x̄) = ∇Φ(x̄)⁻¹(T_S(Φ(x̄)))` for `Φ` with an
invertible strict derivative.

The two normal cone formulas of 6.7 are **not** proved here.  Their natural
route is the same augmentation, but through adjoints, and the augmented
target `F × ker ∇F(x̄)` carries the *sup* norm in Mathlib, so it is not an
inner product space and has no adjoint; the inner product structure lives on
`WithLp 2 (F × ker ∇F(x̄))` instead.  The other route, deducing the normal
formulas from the tangent formula, is the polarity `(A⁻¹K)° = A*(K°)`, which
the book itself does not establish until 6.21 and 6.45.

The augmentation is the book's guide with the basis replaced by a projection:
where the guide picks `a₁, …, a_{n-m}` spanning `ker ∇F(x̄)` and appends the
linear forms `⟨aᵢ, ·⟩`, this file appends the orthogonal projection `P` onto
that kernel.  The pair `Φ = (G, P)` then has derivative `∇F(x̄) × P`, which is
bijective for the reason the guide's `∇F₀(x̄)` has rank `n`, and
`C = Φ⁻¹(D × ker ∇F(x̄))` holds globally rather than only near `x̄`.
-/

import RockafellarWets.Chapter6.NormalCones

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

section TangentTransport

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The tangent cone is monotone in the set. -/
theorem tangentCone_mono {C D : Set E} (h : C ⊆ D) (x : E) :
    tangentCone C x ⊆ tangentCone D x := by
  rintro w ⟨xs, τs, hxC, hxto, hτpos, hτ0, hq⟩
  exact ⟨xs, τs, fun n ↦ h (hxC n), hxto, hτpos, hτ0, hq⟩

/-- The tangent cone is a local notion: intersecting with a neighborhood of the
base point changes nothing.  The sequences of 6(2) are eventually inside the
neighborhood, and dropping a finite head of a sequence is harmless. -/
theorem tangentCone_inter_nhds {C U : Set E} {x : E} (hU : U ∈ nhds x) :
    tangentCone (C ∩ U) x = tangentCone C x := by
  refine Subset.antisymm (tangentCone_mono inter_subset_left x) ?_
  rintro w ⟨xs, τs, hxC, hxto, hτpos, hτ0, hq⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hxto hU)
  exact ⟨fun n ↦ xs (n + N), fun n ↦ τs (n + N),
    fun n ↦ ⟨hxC _, hN _ (Nat.le_add_left N n)⟩,
    hxto.comp (tendsto_add_atTop_nat N), fun n ↦ hτpos _,
    hτ0.comp (tendsto_add_atTop_nat N), hq.comp (tendsto_add_atTop_nat N)⟩

/-- Tangent vectors push forward under a differentiable map: the derivative
carries the tangent cone of a set into the tangent cone of its image. -/
theorem image_tangentCone_subset {H : E → G} {H' : E →L[ℝ] G} {a : E}
    (hH : HasFDerivAt H H' a) (A : Set E) :
    H' '' tangentCone A a ⊆ tangentCone (H '' A) (H a) := by
  rintro _ ⟨w, ⟨xs, τs, hxA, hxto, hτpos, hτ0, hq⟩, rfl⟩
  refine mem_tangentCone_of_forall (fun n ↦ ⟨xs n, hxA n, rfl⟩) hτpos hτ0 ?_
  have hdecomp : ∀ n, (τs n)⁻¹ • (H (xs n) - H a)
      = H' ((τs n)⁻¹ • (xs n - a))
        + (τs n)⁻¹ • (H (xs n) - H a - H' (xs n - a)) := by
    intro n
    rw [map_smul]
    module
  have hlin : Tendsto (fun n ↦ H' ((τs n)⁻¹ • (xs n - a))) atTop (nhds (H' w)) :=
    (H'.continuous.tendsto w).comp hq
  have herr : Tendsto
      (fun n ↦ (τs n)⁻¹ • (H (xs n) - H a - H' (xs n - a))) atTop (nhds 0) := by
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro η hη
    have hpos : (0 : ℝ) < ‖w‖ + 1 := by positivity
    have hε : (0 : ℝ) < η / (2 * (‖w‖ + 1)) := by positivity
    have hbound : ∀ᶠ n in atTop, ‖(τs n)⁻¹ • (xs n - a)‖ < ‖w‖ + 1 :=
      hq.norm.eventually_lt_const (lt_add_one ‖w‖)
    filter_upwards [hxto (hH.isLittleO.def hε), hbound] with n hn hb
    have hτ : (0 : ℝ) < τs n := hτpos n
    have hnorm : ‖(τs n)⁻¹ • (H (xs n) - H a - H' (xs n - a))‖
        = (τs n)⁻¹ * ‖H (xs n) - H a - H' (xs n - a)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hτ)]
    have hq' : ‖(τs n)⁻¹ • (xs n - a)‖ = (τs n)⁻¹ * ‖xs n - a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hτ)]
    rw [hnorm]
    have hstep : (τs n)⁻¹ * ‖H (xs n) - H a - H' (xs n - a)‖
        ≤ (τs n)⁻¹ * (η / (2 * (‖w‖ + 1)) * ‖xs n - a‖) :=
      mul_le_mul_of_nonneg_left hn (inv_pos.2 hτ).le
    have hstep2 : (τs n)⁻¹ * (η / (2 * (‖w‖ + 1)) * ‖xs n - a‖)
        = η / (2 * (‖w‖ + 1)) * ((τs n)⁻¹ * ‖xs n - a‖) := by ring
    rw [← hq'] at hstep2
    have hlt : η / (2 * (‖w‖ + 1)) * ‖(τs n)⁻¹ • (xs n - a)‖
        < η / (2 * (‖w‖ + 1)) * (‖w‖ + 1) := by
      exact mul_lt_mul_of_pos_left hb hε
    have hval : η / (2 * (‖w‖ + 1)) * (‖w‖ + 1) = η / 2 := by
      field_simp
    linarith
  have hsum := hlin.add herr
  rw [add_zero] at hsum
  exact hsum.congr fun n ↦ (hdecomp n).symm

end TangentTransport

section TangentProd

variable {G N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- The tangent cone to `S × IRᵏ` is the tangent cone to `S` times `IRᵏ`.  The
free coordinate contributes every direction, along the *same* scalings. -/
theorem tangentCone_prod_univ (S : Set G) (u : G) (b : N) :
    tangentCone (S ×ˢ (univ : Set N)) (u, b)
      = tangentCone S u ×ˢ (univ : Set N) := by
  refine Subset.antisymm ?_ ?_
  · rintro ⟨w₁, w₂⟩ ⟨ps, τs, hpS, hpto, hτpos, hτ0, hq⟩
    refine ⟨?_, mem_univ _⟩
    refine mem_tangentCone_of_forall (xs := fun n ↦ (ps n).1) (fun n ↦ (hpS n).1)
      hτpos hτ0 ?_
    exact (continuous_fst.tendsto _).comp hq
  · rintro ⟨w₁, w₂⟩ ⟨hw₁, -⟩
    obtain ⟨xs, τs, hxS, hxto, hτpos, hτ0, hq⟩ := hw₁
    refine mem_tangentCone_of_forall (xs := fun n ↦ (xs n, b + τs n • w₂))
      (fun n ↦ ⟨hxS n, mem_univ _⟩) hτpos hτ0 ?_
    have hsnd : ∀ n, (τs n)⁻¹ • ((b + τs n • w₂) - b) = w₂ := by
      intro n
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (hτpos n).ne', one_smul]
    have hpair : Tendsto (fun n ↦ ((τs n)⁻¹ • (xs n - u), (τs n)⁻¹ • ((b + τs n • w₂) - b)))
        atTop (nhds (w₁, w₂)) := by
      refine hq.prodMk_nhds ?_
      exact tendsto_const_nhds.congr fun n ↦ (hsnd n).symm
    exact hpair

end TangentProd

section LocalDiffeo

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Tangent cones transform by the derivative under a change of coordinates.
The inclusion `⊆` is the push-forward of tangent vectors through `Φ`; the
inclusion `⊇` is the same push-forward through the local inverse supplied by
the inverse function theorem, whose image lands in `Φ⁻¹(S)` only near `x̄`,
which is where the locality of the tangent cone is used. -/
theorem tangentCone_preimage {Φ : E → G} {Φ' : E ≃L[ℝ] G} {x : E}
    (hΦ : HasStrictFDerivAt Φ (Φ' : E →L[ℝ] G) x) (S : Set G) :
    tangentCone (Φ ⁻¹' S) x = (Φ' : E →L[ℝ] G) ⁻¹' tangentCone S (Φ x) := by
  refine Subset.antisymm (fun w hw ↦ ?_) (fun w hw ↦ ?_)
  · exact tangentCone_mono (image_preimage_subset Φ S) (Φ x)
      (image_tangentCone_subset hΦ.hasFDerivAt (Φ ⁻¹' S) ⟨w, hw, rfl⟩)
  · obtain ⟨V, hV, hVinv⟩ :=
      Filter.eventually_iff_exists_mem.1 hΦ.eventually_right_inverse
    have hwSV : (Φ' : E →L[ℝ] G) w ∈ tangentCone (S ∩ V) (Φ x) := by
      rw [tangentCone_inter_nhds hV]
      exact hw
    have h2 : (Φ'.symm : G →L[ℝ] E) ((Φ' : E →L[ℝ] G) w)
        ∈ tangentCone (hΦ.localInverse Φ Φ' x '' (S ∩ V)) (hΦ.localInverse Φ Φ' x (Φ x)) :=
      image_tangentCone_subset hΦ.to_localInverse.hasFDerivAt (S ∩ V) ⟨_, hwSV, rfl⟩
    rw [hΦ.localInverse_apply_image] at h2
    have h3 : hΦ.localInverse Φ Φ' x '' (S ∩ V) ⊆ Φ ⁻¹' S := by
      rintro _ ⟨y, ⟨hyS, hyV⟩, rfl⟩
      refine mem_preimage.2 ?_
      rw [hVinv y hyV]
      exact hyS
    have h4 := tangentCone_mono h3 x h2
    simpa using h4

end LocalDiffeo

section ChangeOfCoordinates

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Exercise 6.7**, the tangent cone clause: for `C = F⁻¹(D)` with
`∇F(x̄)` of full rank, `T_C(x̄) = {w | ∇F(x̄)w ∈ T_D(ū)}`.

The proof is the book's guide.  The Jacobian is made square by pairing `G`
with the orthogonal projection onto `ker ∇F(x̄)`, which the book realizes by
choosing a basis of that kernel; the augmented map `Φ = (G, P)` then has an
invertible strict derivative, `C = Φ⁻¹(D × ker ∇F(x̄))` on the nose, and the
change of coordinates is `tangentCone_preimage`. -/
theorem tangentCone_preimage_of_surjective {G : E → F} {G' : E →L[ℝ] F} {x : E}
    (hG : HasStrictFDerivAt G G' x) (hsurj : Function.Surjective G') (D : Set F) :
    tangentCone (G ⁻¹' D) x = G' ⁻¹' tangentCone D (G x) := by
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
  have hkey := tangentCone_preimage hΦ (D ×ˢ (univ : Set N))
  rw [hpre, tangentCone_prod_univ, hcoe] at hkey
  rw [hkey]
  ext w
  simp [hQ]

end ChangeOfCoordinates

end RW
