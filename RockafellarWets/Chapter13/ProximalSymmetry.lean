/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 13: Symmetry in derivatives of proximal mappings and projections

Corollaries 13.53 and 13.54.  By Proposition 13.37, around a point `x̃` with `0 ∈ ∂f(x̃)` at which a
prox-bounded `f` is prox-regular, `P_λ f = I - λ∇e_λ f` on an open set `O`, with `P_λ f` Lipschitz and
`e_λ f` of class `C¹⁺`.  The Hessians of `e_λ f` are symmetric where they exist (symmetry of second
derivatives), hence so are the Jacobians of `P_λ f` and their limits; Theorem 9.62 applied to
`F = P_λ f` together with this symmetry gives all the formulas (`symmetric_reachableJacobians_formulas`,
the part of Theorem 13.52 that comes from 9.62, for any strictly continuous `F` with symmetric
reachable Jacobians).  For `f = δ_C`, `P_λ δ_C = P_C` for every `λ > 0`.
-/

import RockafellarWets.Chapter13.GeneralizedHessians
import RockafellarWets.Chapter13.ProxRegularProjections

open Filter Set Topology Metric MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The difference quotient `[⟪z, F(x + τw)⟫ - ⟪z, F(x)⟫]/τ`. -/
noncomputable def innerDifferenceQuotient (F : E → E) (z w x : E) (τ : ℝ) : ℝ :=
  (⟪z, F (x + τ • w)⟫_ℝ - ⟪z, F x⟫_ℝ) / τ

/-- The Jacobians of `P = I - λG` are symmetric at points where `P` is differentiable, when `G` is
the gradient of a function differentiable on an open set `U`. -/
theorem fderiv_inner_comm_of_gradient {e : E → ℝ} {P : E → E} {U : Set E} {lam : ℝ} (hU : IsOpen U)
    (hlam : lam ≠ 0)
    (he : ∀ v ∈ U, HasFDerivAt e (innerSL ℝ (lam⁻¹ • (v - P v))) v) {u : E} (hu : u ∈ U)
    (hP : DifferentiableAt ℝ P u) (a b : E) :
    ⟪fderiv ℝ P u a, b⟫_ℝ = ⟪a, fderiv ℝ P u b⟫_ℝ := by
  set G : E → E := fun v ↦ lam⁻¹ • (v - P v) with hG
  have hgrad : ∀ v ∈ U, gradient e v = G v := by
    intro v hv
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    convert he v hv using 1
  have hGd : DifferentiableAt ℝ G u := (differentiableAt_id.sub hP).const_smul lam⁻¹
  have hev : gradient e =ᶠ[𝓝 u] G := Filter.mem_of_superset (hU.mem_nhds hu) fun v hv ↦ hgrad v hv
  have hgd : DifferentiableAt ℝ (gradient e) u := hev.differentiableAt_iff.2 hGd
  have hed : ∀ᶠ y in 𝓝 u, DifferentiableAt ℝ e y :=
    Filter.mem_of_superset (hU.mem_nhds hu) fun v hv ↦ (he v hv).differentiableAt
  have hsym := hessian_inner_comm hed hgd
  rw [hev.fderiv_eq] at hsym
  have hPeq : P = fun v ↦ v - lam • G v := by
    funext v; simp only [G, smul_smul, mul_inv_cancel₀ hlam, one_smul]; abel
  have hfd : fderiv ℝ P u = ContinuousLinearMap.id ℝ E - lam • fderiv ℝ G u := by
    rw [hPeq]
    exact ((hasFDerivAt_id u).sub (hGd.hasFDerivAt.const_smul lam)).fderiv
  rw [hfd]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hsym a b]

variable [MeasurableSpace E] [BorelSpace E]

/-- The part of Theorem 13.52 that comes from 9.62, for any `F` strictly continuous on an open set
`O` whose reachable Jacobians at `x̄` are symmetric: the set `∇̄F(x̄)` is nonempty and compact, the
convex hulls of strict derivatives, coderivatives and `{Aw ∣ A ∈ ∇̄F(x̄)}` coincide, and for all
`z, w` the maxima `max ⟪z, Aw⟫`, `max ⟪z, D_*F(x̄)(w)⟫`, `max ⟪w, D_*F(x̄)(z)⟫` and the upper limits
of `[⟪z, F(x + τw)⟫ - ⟪z, F(x)⟫]/τ` and `[⟪w, F(x + τz)⟫ - ⟪w, F(x)⟫]/τ` agree. -/
theorem symmetric_reachableJacobians_formulas {F : E → E} {O D : Set E} (hO : IsOpen O)
    (hg : ∀ y ∈ O, StrictlyContinuousAt F y) (hD : D ⊆ {y ∈ O | DifferentiableAt ℝ F y})
    (hnull : volume ({y ∈ O | DifferentiableAt ℝ F y} \ D) = 0) {x : E} (hx : x ∈ O)
    (hsym : ∀ A ∈ reachableJacobians F D x, ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ) :
    (reachableJacobians F D x).Nonempty ∧ IsCompact (reachableJacobians F D x) ∧
    (∀ w, convexHull ℝ (strictGraphicalDerivative (svSingleton F) x (F x) w) =
        convexHull ℝ (coderivative (svSingleton F) x (F x) w) ∧
      convexHull ℝ (coderivative (svSingleton F) x (F x) w) =
        convexHull ℝ ((fun A : E →L[ℝ] E ↦ A w) '' reachableJacobians F D x)) ∧
    ∀ z w, ∃ A ∈ reachableJacobians F D x,
      (∀ B ∈ reachableJacobians F D x, ⟪z, B w⟫_ℝ ≤ ⟪z, A w⟫_ℝ) ∧
      (∃ ζ ∈ strictGraphicalDerivative (svSingleton F) x (F x) w,
        (∀ ζ' ∈ strictGraphicalDerivative (svSingleton F) x (F x) w, ⟪z, ζ'⟫_ℝ ≤ ⟪z, ζ⟫_ℝ) ∧
          ⟪z, ζ⟫_ℝ = ⟪z, A w⟫_ℝ) ∧
      (∃ ζ ∈ strictGraphicalDerivative (svSingleton F) x (F x) z,
        (∀ ζ' ∈ strictGraphicalDerivative (svSingleton F) x (F x) z, ⟪w, ζ'⟫_ℝ ≤ ⟪w, ζ⟫_ℝ) ∧
          ⟪w, ζ⟫_ℝ = ⟪z, A w⟫_ℝ) ∧
      limsup (fun q : E × ℝ ↦ ((innerDifferenceQuotient F z w q.1 q.2 : ℝ) : EReal))
        (𝓝 x ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
      limsup (fun q : E × ℝ ↦ ((innerDifferenceQuotient F w z q.1 q.2 : ℝ) : EReal))
        (𝓝 x ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) := by
  have hDdiff : ∀ y ∈ D, DifferentiableAt ℝ F y := fun y hy ↦ (hD hy).2
  have hxD := subset_closure_differentiability_set_of_null_complement volume hO hg hnull hx
  obtain ⟨hne, hcpt⟩ := reachableJacobians_nonempty_compact (hg x hx) hxD
  have hclarke : ∀ y w, limsup (fun q : E × ℝ ↦
      ((innerDifferenceQuotient F y w q.1 q.2 : ℝ) : EReal)) (𝓝 x ×ˢ 𝓝[>] 0) =
      supportFunction (strictGraphicalDerivative (svSingleton F) x (F x) w) y := by
    intro y w
    have hsc : ERealStrictlyContinuousAt (fun a ↦ ((⟪y, F a⟫_ℝ : ℝ) : EReal)) x :=
      ⟨by simp, by simpa only [EReal.toReal_coe] using (hg x hx).inner_const y⟩
    rw [← (hg x hx).regularSubderivative_scalar_eq_support_strictGraphicalDerivative w y,
      hsc.regularSubderivative_eq_limsup_differenceQuotient]
    apply limsup_congr
    filter_upwards [tendsto_snd.eventually self_mem_nhdsWithin] with q hq
    rw [innerDifferenceQuotient, differenceQuotient, ← EReal.coe_sub, ← EReal.coe_mul,
      div_eq_inv_mul]
  refine ⟨hne, hcpt, fun w ↦ ?_, fun z w ↦ ?_⟩
  · have h1 :=
      (convexHull_strictGraphicalDerivative_eq_reachableJacobians hO hg hDdiff hnull hx w).1
    have h2 := (convexHull_coderivative_eq_reachableJacobians hO hg hDdiff hnull hx w).1
    have himg : (fun A : E →L[ℝ] E ↦ A.adjoint w) '' reachableJacobians F D x =
        (fun A : E →L[ℝ] E ↦ A w) '' reachableJacobians F D x := by
      apply image_congr
      intro A hA
      apply ext_inner_right ℝ
      intro u
      rw [ContinuousLinearMap.adjoint_inner_left, hsym A hA w u]
    rw [himg] at h2
    exact ⟨h1.trans h2.symm, h2⟩
  · obtain ⟨ζ, hζ, v, -, A, hA, hζv, hζA, hζmax, -, hAmax⟩ :=
      strictGraphicalDerivative_coderivative_reachableJacobian_maxima hO hg hDdiff hnull hx w z
    obtain ⟨ζ', hζ', v', -, A', hA', -, hζA', hζ'max, -, hA'max⟩ :=
      strictGraphicalDerivative_coderivative_reachableJacobian_maxima hO hg hDdiff hnull hx z w
    have hAA' : ⟪w, A' z⟫_ℝ = ⟪z, A w⟫_ℝ := by
      apply le_antisymm
      · have h1 := hAmax A' hA'
        have h2 := hsym A' hA' w z
        have h3 : ⟪A' w, z⟫_ℝ = ⟪z, A' w⟫_ℝ := real_inner_comm _ _
        linarith
      · have h1 := hA'max A hA
        have h2 := hsym A hA w z
        have h3 : ⟪A w, z⟫_ℝ = ⟪z, A w⟫_ℝ := real_inner_comm _ _
        linarith
    refine ⟨A, hA, hAmax, ⟨ζ, hζ, hζmax, hζA⟩, ⟨ζ', hζ', hζ'max, hζA'.trans hAA'⟩, ?_, ?_⟩
    · rw [hclarke]
      apply le_antisymm
      · refine (supportFunction_le_iff _ _ _).2 fun a ha ↦ EReal.coe_le_coe_iff.2 ?_
        have h1 := hζmax a ha
        have h2 : ⟪a, z⟫_ℝ = ⟪z, a⟫_ℝ := real_inner_comm _ _
        linarith
      · have h : ⟪ζ, z⟫_ℝ = ⟪z, A w⟫_ℝ := by rw [real_inner_comm]; exact hζA
        rw [← h]
        exact inner_le_supportFunction hζ z
    · rw [hclarke]
      apply le_antisymm
      · refine (supportFunction_le_iff _ _ _).2 fun a ha ↦ EReal.coe_le_coe_iff.2 ?_
        have h1 := hζ'max a ha
        have h2 : ⟪a, w⟫_ℝ = ⟪w, a⟫_ℝ := real_inner_comm _ _
        linarith
      · have h : ⟪ζ', w⟫_ℝ = ⟪z, A w⟫_ℝ := by rw [real_inner_comm]; linarith
        rw [← h]
        exact inner_le_supportFunction hζ' w

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Reachable Jacobians are symmetric when the Jacobians are symmetric at the points of `D`. -/
theorem reachableJacobians_inner_comm {F : E → E} {D : Set E} {x : E}
    (hsymD : ∀ y ∈ D, ∀ a b, ⟪fderiv ℝ F y a, b⟫_ℝ = ⟪a, fderiv ℝ F y b⟫_ℝ)
    {A : E →L[ℝ] E} (hA : A ∈ reachableJacobians F D x) (u v : E) :
    ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ := by
  obtain ⟨y, hyD, -, hlim⟩ := mem_clusterValuesWithin_iff.1 hA
  have hu : Tendsto (fun n ↦ fderiv ℝ F (y n) u) atTop (𝓝 (A u)) :=
    ((ContinuousLinearMap.apply ℝ E u).continuous.tendsto A).comp hlim
  have hv : Tendsto (fun n ↦ fderiv ℝ F (y n) v) atTop (𝓝 (A v)) :=
    ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto A).comp hlim
  exact tendsto_nhds_unique (hu.inner tendsto_const_nhds)
    ((tendsto_const_nhds.inner hv).congr fun n ↦ (hsymD (y n) (hyD n) u v).symm)

/-- **Corollary 13.53** (symmetry in derivatives of proximal mappings).  Let `f` be prox-bounded and
prox-regular at `x̃` for `0 ∈ ∂f(x̃)`.  For every sufficiently small `λ > 0` there is an open set
`O ∋ x̃` on which `P_λ f = {P}` with `P` strictly continuous, such that at every `x̄ ∈ O` and for
every approach set `D` of points of differentiability of `P` in `O` with negligible complement, the
reachable Jacobians `∇̄(P_λ f)(x̄)` form a nonempty compact set of symmetric maps, the convex hulls
of `D_*(P_λ f)(x̄)(w)`, `D*(P_λ f)(x̄)(w)` and `{Aw ∣ A ∈ ∇̄(P_λ f)(x̄)}` coincide, and for all
`z, w`, `max_A ⟪z, Aw⟫ = max ⟪z, D_*(P_λ f)(x̄)(w)⟫ = max ⟪w, D_*(P_λ f)(x̄)(z)⟫` equals the upper
limits of `[⟪z, P_λ f(x + τw)⟫ - ⟪z, P_λ f(x)⟫]/τ` and `[⟪w, P_λ f(x + τz)⟫ - ⟪w, P_λ f(x)⟫]/τ`. -/
theorem symmetry_in_derivatives_of_proximal_mappings {f : E → EReal} {x : E}
    (hpb : IsProxBounded f) (hpr : IsProxRegularAt f x 0) :
    ∃ lam₀ > 0, ∀ lam, 0 < lam → lam < lam₀ → ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ ∃ P : E → E,
      (∀ u ∈ O, proximalMappingEReal f lam u = {P u}) ∧ (∀ u ∈ O, StrictlyContinuousAt P u) ∧
      ∀ D : Set E, D ⊆ {y ∈ O | DifferentiableAt ℝ P y} →
        volume ({y ∈ O | DifferentiableAt ℝ P y} \ D) = 0 → ∀ y ∈ O,
        (reachableJacobians P D y).Nonempty ∧ IsCompact (reachableJacobians P D y) ∧
        (∀ A ∈ reachableJacobians P D y, ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ) ∧
        (∀ w, convexHull ℝ (strictGraphicalDerivative (svSingleton P) y (P y) w) =
            convexHull ℝ (coderivative (svSingleton P) y (P y) w) ∧
          convexHull ℝ (coderivative (svSingleton P) y (P y) w) =
            convexHull ℝ ((fun A : E →L[ℝ] E ↦ A w) '' reachableJacobians P D y)) ∧
        ∀ z w, ∃ A ∈ reachableJacobians P D y,
          (∀ B ∈ reachableJacobians P D y, ⟪z, B w⟫_ℝ ≤ ⟪z, A w⟫_ℝ) ∧
          (∃ ζ ∈ strictGraphicalDerivative (svSingleton P) y (P y) w,
            (∀ ζ' ∈ strictGraphicalDerivative (svSingleton P) y (P y) w, ⟪z, ζ'⟫_ℝ ≤ ⟪z, ζ⟫_ℝ) ∧
              ⟪z, ζ⟫_ℝ = ⟪z, A w⟫_ℝ) ∧
          (∃ ζ ∈ strictGraphicalDerivative (svSingleton P) y (P y) z,
            (∀ ζ' ∈ strictGraphicalDerivative (svSingleton P) y (P y) z, ⟪w, ζ'⟫_ℝ ≤ ⟪w, ζ⟫_ℝ) ∧
              ⟪w, ζ⟫_ℝ = ⟪z, A w⟫_ℝ) ∧
          limsup (fun q : E × ℝ ↦ ((innerDifferenceQuotient P z w q.1 q.2 : ℝ) : EReal))
            (𝓝 y ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
          limsup (fun q : E × ℝ ↦ ((innerDifferenceQuotient P w z q.1 q.2 : ℝ) : EReal))
            (𝓝 y ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) := by
  obtain ⟨ε, hε, lam₀, hlam₀, H⟩ := proximal_mappings_and_moreau_envelopes hpr hpb
  refine ⟨lam₀, hlam₀, fun lam hlam hlt ↦ ?_⟩
  obtain ⟨P, hUo, hxU, -, hPsingle, hPmono, hdiff, -, -⟩ := H lam hlam hlt
  set O := proxRange f x ε lam
  have hsc : ∀ u ∈ O, StrictlyContinuousAt P u := by
    intro u hu
    refine strictlyContinuousAt_iff.2 ⟨2, O, hUo.mem_nhds hu, ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact_mod_cast (hPmono b hb a ha).2
  refine ⟨O, hUo, hxU, P, hPsingle, hsc, fun D hD hnull y hy ↦ ?_⟩
  have hsymD : ∀ u ∈ D, ∀ a b, ⟪fderiv ℝ P u a, b⟫_ℝ = ⟪a, fderiv ℝ P u b⟫_ℝ :=
    fun u hu a b ↦ fderiv_inner_comm_of_gradient hUo hlam.ne' (fun v hv ↦ (hdiff v hv).2.2)
      (hD hu).1 (hD hu).2 a b
  have hsym : ∀ A ∈ reachableJacobians P D y, ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ :=
    fun A hA u v ↦ reachableJacobians_inner_comm hsymD hA u v
  obtain ⟨h1, h2, h3, h4⟩ := symmetric_reachableJacobians_formulas hUo hsc hD hnull hy hsym
  exact ⟨h1, h2, hsym, h3, h4⟩

/-- **Corollary 13.54** (symmetry in derivatives of projections).  If `C` is prox-regular at
`x̃ ∈ C` for `0`, there is an open set `O ∋ x̃` on which `P_C = {P}` with `P` strictly continuous,
and at every `x̄ ∈ O` the conclusions of Corollary 13.53 hold for `P_C`. -/
theorem symmetry_in_derivatives_of_projections {C : Set E} {x : E} (hx : x ∈ C)
    (hC : IsProxRegularSetAt C x 0) :
    ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ ∃ P : E → E,
      (∀ u ∈ O, projMapping C u = {P u}) ∧ (∀ u ∈ O, StrictlyContinuousAt P u) ∧
      ∀ D : Set E, D ⊆ {y ∈ O | DifferentiableAt ℝ P y} →
        volume ({y ∈ O | DifferentiableAt ℝ P y} \ D) = 0 → ∀ y ∈ O,
        (reachableJacobians P D y).Nonempty ∧ IsCompact (reachableJacobians P D y) ∧
        (∀ A ∈ reachableJacobians P D y, ∀ u v, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ) ∧
        (∀ w, convexHull ℝ (strictGraphicalDerivative (svSingleton P) y (P y) w) =
            convexHull ℝ (coderivative (svSingleton P) y (P y) w) ∧
          convexHull ℝ (coderivative (svSingleton P) y (P y) w) =
            convexHull ℝ ((fun A : E →L[ℝ] E ↦ A w) '' reachableJacobians P D y)) ∧
        ∀ z w, ∃ A ∈ reachableJacobians P D y,
          (∀ B ∈ reachableJacobians P D y, ⟪z, B w⟫_ℝ ≤ ⟪z, A w⟫_ℝ) ∧
          (∃ ζ ∈ strictGraphicalDerivative (svSingleton P) y (P y) w,
            (∀ ζ' ∈ strictGraphicalDerivative (svSingleton P) y (P y) w, ⟪z, ζ'⟫_ℝ ≤ ⟪z, ζ⟫_ℝ) ∧
              ⟪z, ζ⟫_ℝ = ⟪z, A w⟫_ℝ) ∧
          (∃ ζ ∈ strictGraphicalDerivative (svSingleton P) y (P y) z,
            (∀ ζ' ∈ strictGraphicalDerivative (svSingleton P) y (P y) z, ⟪w, ζ'⟫_ℝ ≤ ⟪w, ζ⟫_ℝ) ∧
              ⟪w, ζ⟫_ℝ = ⟪z, A w⟫_ℝ) ∧
          limsup (fun q : E × ℝ ↦ ((innerDifferenceQuotient P z w q.1 q.2 : ℝ) : EReal))
            (𝓝 y ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) ∧
          limsup (fun q : E × ℝ ↦ ((innerDifferenceQuotient P w z q.1 q.2 : ℝ) : EReal))
            (𝓝 y ×ˢ 𝓝[>] 0) = ((⟪z, A w⟫_ℝ : ℝ) : EReal) := by
  have hpr : IsProxRegularAt (indicatorVA C) x 0 := (isProxRegularAt_indicatorVA_iff hx).2 hC
  obtain ⟨lam₀, hlam₀, H⟩ :=
    symmetry_in_derivatives_of_proximal_mappings (isProxBounded_indicatorVA C) hpr
  obtain ⟨O, hO, hxO, P, hP, hrest⟩ := H (lam₀ / 2) (by positivity) (by linarith)
  refine ⟨O, hO, hxO, P, fun u hu ↦ ?_, hrest⟩
  rw [← proximalMappingEReal_indicatorVA C (show (0 : ℝ) < lam₀ / 2 by positivity)]
  exact hP u hu

end RW
