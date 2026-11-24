/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Proto-derivatives of monotone mappings

Exercise 12.64.

The difference quotients `Δ_τT(x̄|v̄)(w) = τ⁻¹(T(x̄ + τw) - v̄)` of a maximal
monotone mapping are maximal monotone, and those of a cyclically monotone mapping
are cyclically monotone, since the inner products and cyclic sums only scale by
`τ⁻²`.  Proto-differentiability is graphical convergence of the quotients to
`DT(x̄|v̄)` along every sequence `τν ↘ 0`, so 12.32 makes `DT(x̄|v̄)` maximal
monotone, its graph containing the origin.  For the cyclic clause the guide
suggests 12.25 and 12.35; instead, cyclical monotonicity passes to graphical
inner limits directly (the cyclic sums are finite), and a cyclically monotone
mapping that is maximal monotone is maximal cyclically monotone.

For the resolvent `R_λ = (I + λT)⁻¹` the linear change of coordinates
`(z, y) ↦ (y, λ⁻¹(z - y))` of `IRⁿ × IRⁿ` takes `gph R_λ` onto `gph T` and
`(z̄_λ, x̄)` to `(x̄, v̄)`, for `z̄_λ = x̄ + λv̄`.  Tangent cones and geometric
derivability are invariant under linear isomorphisms, which gives
`DR_λ(z̄_λ) = (I + λDT(x̄|v̄))⁻¹` and the equivalence of the proto-differentiability
of `T` and `R_λ` (8.41).  As `R_λ` is single-valued and nonexpansive, it has the
Aubin property, so proto-differentiability of `R_λ` is its semidifferentiability
(9.50), which for a calm single-valued mapping is single-valuedness of the
graphical derivative (9.25(a)).  Differentiability of `R_λ` is linearity of
`DR_λ(z̄_λ)` (9.25(b)); when `gph DT(x̄|v̄)` is a linear subspace, the
nonexpansive bound `|DR_λ(z̄_λ)(z)| ≤ |z|` forces `DR_λ(z̄_λ)` to be single-valued,
and the subspace is the image of the graph of `∇R_λ(z̄_λ)`, so it has dimension `n`.
-/

import RockafellarWets.Chapter12.MonotoneGraphicalConvergence
import RockafellarWets.Chapter12.CyclicalMonotonicity
import RockafellarWets.Chapter9.SemidifferentiabilityFromAubin
import RockafellarWets.Chapter9.SingleValuedDifferentiability
import RockafellarWets.Chapter9.SingleValuedGraphicalDerivatives

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

section DifferenceQuotients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The difference quotients of a monotone mapping are monotone. -/
theorem SvMonotone.differenceQuotient {T : E → Set E} (hT : SvMonotone T) (x u : E)
    {τ : ℝ} (hτ : τ ≠ 0) : SvMonotone (mappingDifferenceQuotient T x u τ) := by
  rintro w₀ _ ⟨v₀, hv₀, rfl⟩ w₁ _ ⟨v₁, hv₁, rfl⟩
  have h := hT hv₀ hv₁
  have e : ⟪τ⁻¹ • (v₁ - u) - τ⁻¹ • (v₀ - u), w₁ - w₀⟫_ℝ =
      (τ⁻¹ * τ⁻¹) * ⟪v₁ - v₀, (x + τ • w₁) - (x + τ • w₀)⟫_ℝ := by
    rw [← smul_sub, sub_sub_sub_cancel_right, add_sub_add_left_eq_sub, ← smul_sub,
      real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [e]
  exact mul_nonneg (mul_self_nonneg _) h

/-- The difference quotients of a maximal monotone mapping are maximal monotone. -/
theorem SvMaximalMonotone.differenceQuotient {T : E → Set E} (hT : SvMaximalMonotone T)
    (x u : E) {τ : ℝ} (hτ : τ ≠ 0) : SvMaximalMonotone (mappingDifferenceQuotient T x u τ) := by
  refine ⟨hT.1.differenceQuotient x u hτ, fun w z hz ↦ ?_⟩
  have hz' : u + τ • z ∉ T (x + τ • w) := fun h ↦
    hz ((mem_mappingDifferenceQuotient_iff hτ).2 h)
  obtain ⟨x', v', hv', hlt⟩ := hT.2 _ _ hz'
  refine ⟨τ⁻¹ • (x' - x), τ⁻¹ • (v' - u), ?_, ?_⟩
  · rw [mem_mappingDifferenceQuotient_iff hτ, smul_inv_smul₀ hτ, smul_inv_smul₀ hτ,
      add_sub_cancel, add_sub_cancel]
    exact hv'
  · have e : ⟪z - τ⁻¹ • (v' - u), w - τ⁻¹ • (x' - x)⟫_ℝ =
        (τ⁻¹ * τ⁻¹) * ⟪u + τ • z - v', x + τ • w - x'⟫_ℝ := by
      have e1 : z - τ⁻¹ • (v' - u) = τ⁻¹ • (u + τ • z - v') := by
        rw [smul_sub τ⁻¹ (u + τ • z) v', smul_add, smul_smul, inv_mul_cancel₀ hτ, one_smul,
          smul_sub]
        abel
      have e2 : w - τ⁻¹ • (x' - x) = τ⁻¹ • (x + τ • w - x') := by
        rw [smul_sub τ⁻¹ (x + τ • w) x', smul_add, smul_smul, inv_mul_cancel₀ hτ, one_smul,
          smul_sub]
        abel
      rw [e1, e2, real_inner_smul_left, real_inner_smul_right, mul_assoc]
    rw [e]
    exact mul_neg_of_pos_of_neg (mul_self_pos.2 (inv_ne_zero hτ)) hlt

/-- The difference quotients of a cyclically monotone mapping are cyclically
monotone: the cyclic sums scale by `τ⁻²`, the base value `u` dropping out
because `Σᵢ (x_{i+1} - xᵢ) = 0` around a cycle. -/
theorem SvCyclicallyMonotone.differenceQuotient {T : E → Set E}
    (hT : SvCyclicallyMonotone T) (x u : E) {τ : ℝ} (hτ : τ ≠ 0) :
    SvCyclicallyMonotone (mappingDifferenceQuotient T x u τ) := by
  intro m hm w z hz
  choose v hv hvz using hz
  have h := hT m hm (fun i ↦ x + τ • w i) v hv
  have hsum : ∑ i, ⟪u, w (finRotate (m + 1) i) - w i⟫_ℝ = 0 := by
    rw [← inner_sum, Finset.sum_sub_distrib, Equiv.sum_comp (finRotate (m + 1)) w, sub_self,
      inner_zero_right]
  have key : cyclicSum w z = τ⁻¹ * τ⁻¹ * cyclicSum (fun i ↦ x + τ • w i) v -
      τ⁻¹ * ∑ i, ⟪u, w (finRotate (m + 1) i) - w i⟫_ℝ := by
    simp only [cyclicSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hvz i, add_sub_add_left_eq_sub, ← smul_sub, real_inner_smul_left,
      real_inner_smul_right, inner_sub_left]
    field_simp
  rw [key, hsum, mul_zero, sub_zero]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) h

/-- **Theorem 12.32**, first assertion, for cyclical monotonicity: the
graphical inner limit of cyclically monotone mappings is cyclically monotone. -/
theorem svCyclicallyMonotone_graphicalInnerLimit {T : ℕ → E → Set E}
    (hT : ∀ n, SvCyclicallyMonotone (T n)) : SvCyclicallyMonotone (graphicalInnerLimit T) := by
  intro m hm x v hv
  choose y w hw hy hwv using fun i ↦ mem_graphicalInnerLimit_iff.1 (hv i)
  have hev : ∀ᶠ n in atTop, ∀ i, w i n ∈ T n (y i n) := eventually_all.2 hw
  have hlim : Tendsto (fun n ↦ cyclicSum (fun i ↦ y i n) (fun i ↦ w i n)) atTop
      (𝓝 (cyclicSum x v)) := by
    unfold cyclicSum
    exact tendsto_finset_sum _ fun i _ ↦ (hwv i).inner ((hy _).sub (hy i))
  refine le_of_tendsto hlim ?_
  filter_upwards [hev] with n hn
  exact hT n m hm _ _ hn

end DifferenceQuotients

section GraphicalDerivatives

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The scales `1/(n + 1)` decrease to zero. -/
theorem tendsto_one_div_add_one_nhdsGT :
    Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n ↦ show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity⟩

/-- The graph of a graphical derivative contains the origin. -/
theorem zero_mem_graphicalDerivative {S : E → Set F} {x : E} {u : F} (hu : u ∈ S x) :
    (0 : F) ∈ graphicalDerivative S x u 0 :=
  (svPositivelyHomogeneous_graphicalDerivative hu).1

/-- Proto-differentiability gives graphical convergence of the difference
quotients along every sequence of positive scales tending to zero. -/
theorem IsProtoDifferentiableAt.graphicalConverges {S : E → Set F} {x : E} {u : F}
    (h : IsProtoDifferentiableAt S x u) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[>] 0)) :
    GraphicalConverges (fun n ↦ mappingDifferenceQuotient S x u (τ n))
      (graphicalDerivative S x u) :=
  pkConvergesAlong_iff_forall_seq.mp h τ hτ

/-- Proto-differentiability is geometric derivability of the graph in the
product space `E × F`. -/
theorem isProtoDifferentiableAt_iff_isGeometricallyDerivable_svGraph {S : E → Set F} {x : E}
    {u : F} (hx : u ∈ S x) :
    IsProtoDifferentiableAt S x u ↔ IsGeometricallyDerivable (svGraph S) (x, u) := by
  rw [isProtoDifferentiableAt_iff_geometricallyDerivable hx]
  exact isGeometricallyDerivable_preimage_continuousLinearEquiv
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F) (svGraph S) (WithLp.toLp 2 (x, u))

end GraphicalDerivatives

section Resolvents

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear change of coordinates `(z, y) ↦ (y, λ⁻¹(z - y))` of `E × E`,
with inverse `(x, v) ↦ (x + λv, x)`.  It takes the graph of the resolvent
`(I + λT)⁻¹` onto the graph of `T`. -/
noncomputable def resolventGraphEquiv (lam : ℝ) (hlam : lam ≠ 0) : (E × E) ≃L[ℝ] (E × E) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.snd ℝ E E).prod
      (lam⁻¹ • (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)))
    ((ContinuousLinearMap.fst ℝ E E + lam • ContinuousLinearMap.snd ℝ E E).prod
      (ContinuousLinearMap.fst ℝ E E))
    (fun p ↦ by
      ext <;> simp [smul_smul, mul_inv_cancel₀ hlam])
    (fun p ↦ by
      ext <;> simp [smul_smul, inv_mul_cancel₀ hlam])

@[simp]
theorem resolventGraphEquiv_apply (lam : ℝ) (hlam : lam ≠ 0) (p : E × E) :
    resolventGraphEquiv lam hlam p = (p.2, lam⁻¹ • (p.1 - p.2)) := rfl

/-- `y ∈ (I + λS)⁻¹(y + λu)` exactly when `u ∈ S(y)`. -/
theorem mem_svResolvent_add_smul_iff {S : E → Set E} {lam : ℝ} (hlam : lam ≠ 0) {y u : E} :
    y ∈ svResolvent S lam (y + lam • u) ↔ u ∈ S y := by
  rw [mem_svResolvent]
  constructor
  · rintro ⟨u', hu', h⟩
    rw [add_right_inj, (smul_right_injective E hlam).eq_iff] at h
    exact h ▸ hu'
  · exact fun h ↦ ⟨u, h, rfl⟩

/-- The graph of the resolvent `(I + λT)⁻¹` is the preimage of the graph of `T`
under `(z, y) ↦ (y, λ⁻¹(z - y))`. -/
theorem svGraph_svResolvent_eq_preimage (T : E → Set E) {lam : ℝ} (hlam : lam ≠ 0) :
    svGraph (svResolvent T lam) = resolventGraphEquiv lam hlam ⁻¹' svGraph T := by
  ext ⟨z, y⟩
  change y ∈ svResolvent T lam z ↔ lam⁻¹ • (z - y) ∈ T y
  conv_lhs => rw [show z = y + lam • (lam⁻¹ • (z - y)) by
    rw [smul_inv_smul₀ hlam, add_sub_cancel]]
  exact mem_svResolvent_add_smul_iff hlam

theorem resolventGraphEquiv_add_smul (lam : ℝ) (hlam : lam ≠ 0) (x v : E) :
    resolventGraphEquiv lam hlam (x + lam • v, x) = (x, v) := by
  rw [resolventGraphEquiv_apply, add_sub_cancel_left, inv_smul_smul₀ hlam]

/-- **Exercise 12.64**, the derivative of the resolvent: for every mapping `T`,
`DR_λ(z̄_λ | x̄) = (I + λDT(x̄|v̄))⁻¹` at `z̄_λ = x̄ + λv̄`, where `R_λ = (I + λT)⁻¹`.
The graphs correspond under the linear change of coordinates
`(z, y) ↦ (y, λ⁻¹(z - y))`. -/
theorem graphicalDerivative_svResolvent (T : E → Set E) {lam : ℝ} (hlam : lam ≠ 0) (x v : E) :
    graphicalDerivative (svResolvent T lam) (x + lam • v) x =
      svResolvent (graphicalDerivative T x v) lam := by
  apply svGraph_injective
  rw [svGraph_graphicalDerivative, svGraph_svResolvent_eq_preimage _ hlam,
    tangentCone_preimage_continuousLinearEquiv, svGraph_svResolvent_eq_preimage _ hlam,
    svGraph_graphicalDerivative, resolventGraphEquiv_add_smul]

/-- **Exercise 12.64**: `T` is proto-differentiable at `x̄` for `v̄` exactly when
`R_λ = (I + λT)⁻¹` is proto-differentiable at `z̄_λ = x̄ + λv̄` for `x̄`. -/
theorem isProtoDifferentiableAt_svResolvent_iff (T : E → Set E) {lam : ℝ} (hlam : lam ≠ 0)
    {x v : E} (hv : v ∈ T x) :
    IsProtoDifferentiableAt (svResolvent T lam) (x + lam • v) x ↔
      IsProtoDifferentiableAt T x v := by
  have hx : x ∈ svResolvent T lam (x + lam • v) := (mem_svResolvent_add_smul_iff hlam).2 hv
  rw [isProtoDifferentiableAt_iff_isGeometricallyDerivable_svGraph hx,
    isProtoDifferentiableAt_iff_isGeometricallyDerivable_svGraph hv,
    svGraph_svResolvent_eq_preimage _ hlam, isGeometricallyDerivable_preimage_continuousLinearEquiv,
    resolventGraphEquiv_add_smul]

end Resolvents

section SingleValued

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A semiderivative of a single-valued mapping has at most one value in each
direction: the difference quotients are singletons, and a point of their inner
limit is a limit of the quotient vectors. -/
theorem HasMappingSemiderivative.subsingleton_svSingleton {f : E → F} {x : E} {H : E → Set F}
    (h : HasMappingSemiderivative (svSingleton f) x (f x) H) (w : E) : (H w).Subsingleton := by
  have key : ∀ c ∈ H w, Tendsto (fun p : ℝ × E ↦ p.1⁻¹ • (f (x + p.1 • p.2) - f x))
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w) (𝓝 c) := by
    intro c hc
    rw [← (h w).1] at hc
    refine tendsto_def.2 fun V hV ↦ ?_
    filter_upwards [hc V hV] with p hp
    obtain ⟨_, ⟨y, hy, rfl⟩, hyV⟩ := hp
    rw [show y = f (x + p.1 • p.2) from hy] at hyV
    exact hyV
  intro a ha b hb
  exact tendsto_nhds_unique (key a ha) (key b hb)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- For a calm single-valued mapping, semidifferentiability is single-valuedness
of the graphical derivative (Exercise 9.25(a)). -/
theorem exists_hasMappingSemiderivative_svSingleton_iff {f : E → F} {z : E} (hf : CalmAt f z) :
    (∃ H, HasMappingSemiderivative (svSingleton f) z (f z) H) ↔
      ∃ A : E → F, graphicalDerivative (svSingleton f) z (f z) = svSingleton A := by
  constructor
  · rintro ⟨H, hH⟩
    have hD := hH.protoDerivative.2
    refine ⟨fun w ↦ (hf.graphicalDerivative_nonempty w).some, funext fun w ↦ ?_⟩
    have hsub : (graphicalDerivative (svSingleton f) z (f z) w).Subsingleton := by
      rw [hD]
      exact hH.subsingleton_svSingleton w
    exact hsub.eq_singleton_of_mem (hf.graphicalDerivative_nonempty w).some_mem
  · rintro ⟨A, hA⟩
    exact ⟨_, hasMappingSemiderivative_singleton_iff_calm_graphical.2 ⟨hf, hA⟩⟩

end SingleValued

section MaximalMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 12.64**: if a maximal monotone `T` is proto-differentiable at `x̄`
for `v̄ ∈ T(x̄)`, the graphical derivative `DT(x̄|v̄)` is maximal monotone.  The
difference quotients are maximal monotone and converge graphically to
`DT(x̄|v̄)`, whose graph contains the origin (12.32). -/
theorem svMaximalMonotone_graphicalDerivative {T : E → Set E} (hT : SvMaximalMonotone T)
    {x v : E} (hv : v ∈ T x) (hp : IsProtoDifferentiableAt T x v) :
    SvMaximalMonotone (graphicalDerivative T x v) :=
  (hp.graphicalConverges tendsto_one_div_add_one_nhdsGT).svMaximalMonotone
    (fun n ↦ hT.differenceQuotient x v (by positivity)) ⟨0, 0, zero_mem_graphicalDerivative hv⟩

/-- **Exercise 12.64**, maximal cyclical monotonicity: the difference quotients
are cyclically monotone, hence so is their graphical limit `DT(x̄|v̄)`, which is
maximal monotone by the first assertion and so maximal cyclically monotone. -/
theorem svMaximalCyclicallyMonotone_graphicalDerivative {T : E → Set E}
    (hT : SvMaximalCyclicallyMonotone T) {x v : E} (hv : v ∈ T x)
    (hp : IsProtoDifferentiableAt T x v) :
    SvMaximalCyclicallyMonotone (graphicalDerivative T x v) := by
  have hmax := svMaximalMonotone_graphicalDerivative hT.svMaximalMonotone hv hp
  have hg := hp.graphicalConverges tendsto_one_div_add_one_nhdsGT
  exact ⟨(svCyclicallyMonotone_graphicalInnerLimit fun n ↦
      hT.1.differenceQuotient x v (by positivity)).mono (graphicalConverges_iff.1 hg).2,
    fun T' hT' hsub ↦ hmax.eq_of_subset hT'.svMonotone hsub⟩

theorem SvMaximalMonotone.svResolvent_eq_svSingleton {T : E → Set E} (hT : SvMaximalMonotone T)
    {lam : ℝ} (hlam : 0 < lam) : svResolvent T lam = svSingleton (resolventMap T lam) :=
  hT.svResolvent_eq_fun hlam

theorem SvMaximalMonotone.calmAtWith_resolventMap {T : E → Set E} (hT : SvMaximalMonotone T)
    {lam : ℝ} (hlam : 0 < lam) (z : E) : CalmAtWith 1 (resolventMap T lam) z :=
  Eventually.of_forall fun y ↦ (hT.lipschitzWith_resolventMap hlam).dist_le_mul y z

theorem SvMaximalMonotone.strictlyContinuousAt_resolventMap {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) (z : E) :
    StrictlyContinuousAt (resolventMap T lam) z :=
  strictlyContinuousAt_iff.2
    ⟨1, univ, univ_mem, (hT.lipschitzWith_resolventMap hlam).lipschitzOnWith⟩

/-- The resolvent of a maximal monotone mapping has the Aubin property, being
single-valued and nonexpansive. -/
theorem SvMaximalMonotone.hasAubinPropertyAt_svResolvent {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) (z : E) :
    HasAubinPropertyAt (svResolvent T lam) z (resolventMap T lam z) := by
  rw [hT.svResolvent_eq_svSingleton hlam]
  exact (hT.strictlyContinuousAt_resolventMap hlam z).hasAubinProperty_singleton

/-- **Exercise 12.64**: proto-differentiability of `T` at `x̄` for `v̄` is
semidifferentiability of the resolvent `R_λ = (I + λT)⁻¹` at `z̄_λ = x̄ + λv̄`
(9.50(b), the resolvent being Lipschitz). -/
theorem SvMaximalMonotone.isProtoDifferentiableAt_iff_semidifferentiable_svResolvent
    {T : E → Set E} (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) {x v : E}
    (hv : v ∈ T x) :
    IsProtoDifferentiableAt T x v ↔
      ∃ H, HasMappingSemiderivative (svResolvent T lam) (x + lam • v) x H := by
  rw [← isProtoDifferentiableAt_svResolvent_iff T hlam.ne' hv]
  constructor
  · intro hp
    have ha := hT.hasAubinPropertyAt_svResolvent hlam (x + lam • v)
    rw [hT.resolventMap_add_smul hlam hv] at ha
    exact ⟨_, ha.hasMappingSemiderivative hp⟩
  · rintro ⟨H, hH⟩
    exact hH.protoDerivative.1

/-- **Exercise 12.64**: semidifferentiability of `R_λ` at `z̄_λ` is
single-valuedness of `DR_λ(z̄_λ)` (9.25(a)). -/
theorem SvMaximalMonotone.semidifferentiable_svResolvent_iff {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) {x v : E} (hv : v ∈ T x) :
    (∃ H, HasMappingSemiderivative (svResolvent T lam) (x + lam • v) x H) ↔
      ∃ A : E → E, graphicalDerivative (svResolvent T lam) (x + lam • v) x = svSingleton A := by
  have key := exists_hasMappingSemiderivative_svSingleton_iff
    (hT.calmAtWith_resolventMap hlam (x + lam • v) |> fun h ↦ (⟨1, h⟩ : CalmAt _ _))
  rw [hT.resolventMap_add_smul hlam hv] at key
  rw [hT.svResolvent_eq_svSingleton hlam]
  exact key

/-- The derivative of the resolvent determines a linear map when the graph of
`DT(x̄|v̄)` is a linear subspace: then `DR_λ(z̄_λ)` is single-valued, being
nonempty and bounded by the nonexpansive estimate, and linear. -/
theorem SvMaximalMonotone.exists_linear_graphicalDerivative_svResolvent {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) {x v : E} (hv : v ∈ T x)
    (M : Submodule ℝ (E × E)) (hM : (M : Set (E × E)) = svGraph (graphicalDerivative T x v)) :
    ∃ L : E →L[ℝ] E,
      graphicalDerivative (svResolvent T lam) (x + lam • v) x = svSingleton L := by
  set S := graphicalDerivative T x v with hSdef
  have hR : resolventMap T lam (x + lam • v) = x := hT.resolventMap_add_smul hlam hv
  have hDR : graphicalDerivative (svResolvent T lam) (x + lam • v) x = svResolvent S lam :=
    graphicalDerivative_svResolvent T hlam.ne' x v
  have hcalm := hT.calmAtWith_resolventMap hlam (x + lam • v)
  have hD' : graphicalDerivative (svSingleton (resolventMap T lam)) (x + lam • v)
      (resolventMap T lam (x + lam • v)) = svResolvent S lam := by
    rw [hR, ← hT.svResolvent_eq_svSingleton hlam, hDR]
  have hne : ∀ w, (svResolvent S lam w).Nonempty := fun w ↦ by
    rw [← hD']
    exact CalmAt.graphicalDerivative_nonempty ⟨1, hcalm⟩ w
  have hbd : ∀ w y, y ∈ svResolvent S lam w → ‖y‖ ≤ ‖w‖ := fun w y hy ↦ by
    rw [← hD'] at hy
    simpa using hcalm.graphicalDerivative_norm_le hy
  have hmemM : ∀ y u, (y, u) ∈ M ↔ u ∈ S y := fun y u ↦ by
    rw [← SetLike.mem_coe, hM]
    rfl
  -- membership in the resolvent of `S` through `M`
  have hres : ∀ w y, y ∈ svResolvent S lam w ↔ (y, lam⁻¹ • (w - y)) ∈ M := fun w y ↦ by
    rw [hmemM]
    conv_lhs => rw [show w = y + lam • (lam⁻¹ • (w - y)) by
      rw [smul_inv_smul₀ hlam.ne', add_sub_cancel]]
    exact mem_svResolvent_add_smul_iff hlam.ne'
  -- single-valuedness
  have huniq : ∀ w y₁ y₂, y₁ ∈ svResolvent S lam w → y₂ ∈ svResolvent S lam w → y₁ = y₂ := by
    intro w y₁ y₂ h₁ h₂
    have hsub := M.sub_mem ((hres w y₁).1 h₁) ((hres w y₂).1 h₂)
    have h0 : y₁ - y₂ ∈ svResolvent S lam 0 := by
      rw [hres]
      convert hsub using 2
      simp only [Prod.snd_sub]
      rw [← smul_sub]
      congr 1
      abel
    have := hbd 0 _ h0
    rw [norm_zero, norm_le_zero_iff, sub_eq_zero] at this
    exact this
  choose A hA using hne
  have hAeq : ∀ w y, y ∈ svResolvent S lam w → y = A w := fun w y hy ↦ huniq w y (A w) hy (hA w)
  have hAM : ∀ w, (A w, lam⁻¹ • (w - A w)) ∈ M := fun w ↦ (hres w (A w)).1 (hA w)
  let Al : E →ₗ[ℝ] E :=
    { toFun := A
      map_add' := fun w₁ w₂ ↦ by
        refine (hAeq (w₁ + w₂) (A w₁ + A w₂) ((hres _ _).2 ?_)).symm
        convert M.add_mem (hAM w₁) (hAM w₂) using 1
        ext
        · rfl
        · simp only [Prod.snd_add, ← smul_add]
          congr 1
          abel
      map_smul' := fun c w ↦ by
        refine (hAeq (c • w) (c • A w) ((hres _ _).2 ?_)).symm
        convert M.smul_mem c (hAM w) using 1
        ext
        · rfl
        · simp only [Prod.smul_snd, smul_comm c lam⁻¹, smul_sub] }
  refine ⟨LinearMap.toContinuousLinearMap Al, ?_⟩
  rw [hDR]
  funext w
  exact (Set.eq_singleton_iff_unique_mem.2 ⟨hA w, fun y hy ↦ hAeq w y hy⟩)


/-- **Exercise 12.64**: `R_λ` is differentiable at `z̄_λ = x̄ + λv̄` exactly when
`DT(x̄|v̄)` is a generalized linear mapping, its graph being a linear subspace
of `E × E` (9.25(b)). -/
theorem SvMaximalMonotone.differentiableAt_resolventMap_iff {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) {x v : E} (hv : v ∈ T x) :
    DifferentiableAt ℝ (resolventMap T lam) (x + lam • v) ↔
      ∃ M : Submodule ℝ (E × E), (M : Set (E × E)) = svGraph (graphicalDerivative T x v) := by
  have hR : resolventMap T lam (x + lam • v) = x := hT.resolventMap_add_smul hlam hv
  have hcalm : CalmAt (resolventMap T lam) (x + lam • v) :=
    ⟨1, hT.calmAtWith_resolventMap hlam _⟩
  constructor
  · intro hd
    have h := (hasFDerivAt_iff_calm_graphical.1 hd.hasFDerivAt).2
    rw [hR, ← hT.svResolvent_eq_svSingleton hlam, graphicalDerivative_svResolvent T hlam.ne' x v]
      at h
    set L := fderiv ℝ (resolventMap T lam) (x + lam • v)
    refine ⟨LinearMap.ker (LinearMap.fst ℝ E E -
      (L : E →ₗ[ℝ] E) ∘ₗ (LinearMap.fst ℝ E E + lam • LinearMap.snd ℝ E E)), ?_⟩
    ext ⟨w, u⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.fst_apply,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.snd_apply,
      ContinuousLinearMap.coe_coe, sub_eq_zero]
    change w = L (w + lam • u) ↔ u ∈ graphicalDerivative T x v w
    rw [← mem_svResolvent_add_smul_iff hlam.ne', h]
    exact Iff.rfl
  · rintro ⟨M, hM⟩
    obtain ⟨L, hL⟩ := hT.exists_linear_graphicalDerivative_svResolvent hlam hv M hM
    have h2 : graphicalDerivative (svSingleton (resolventMap T lam)) (x + lam • v)
        (resolventMap T lam (x + lam • v)) = svSingleton L := by
      rw [hR, ← hT.svResolvent_eq_svSingleton hlam, hL]
    exact (hasFDerivAt_iff_calm_graphical.2 ⟨hcalm, h2⟩).differentiableAt

/-- **Exercise 12.64**: a linear subspace that is the graph of `DT(x̄|v̄)` is
necessarily `n`-dimensional, being the image of the graph of the linear map
`∇R_λ(z̄_λ)` under the change of coordinates `(z, y) ↦ (y, λ⁻¹(z - y))`. -/
theorem SvMaximalMonotone.finrank_eq_of_svGraph_graphicalDerivative {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) {x v : E} (hv : v ∈ T x)
    (M : Submodule ℝ (E × E)) (hM : (M : Set (E × E)) = svGraph (graphicalDerivative T x v)) :
    Module.finrank ℝ M = Module.finrank ℝ E := by
  obtain ⟨L, hL⟩ := hT.exists_linear_graphicalDerivative_svResolvent hlam hv M hM
  rw [graphicalDerivative_svResolvent T hlam.ne' x v] at hL
  let ψ : E →ₗ[ℝ] E × E :=
    (L : E →ₗ[ℝ] E).prod (lam⁻¹ • (LinearMap.id - (L : E →ₗ[ℝ] E)))
  have hψ : ∀ w, ψ w = (L w, lam⁻¹ • (w - L w)) := fun w ↦ rfl
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).2 fun w hw ↦ ?_
    rw [hψ, Prod.mk_eq_zero, smul_eq_zero, sub_eq_zero] at hw
    rcases hw with ⟨h1, h2 | h2⟩
    · exact absurd h2 (inv_ne_zero hlam.ne')
    · rw [h2, h1]
  have hMψ : M = LinearMap.range ψ := by
    apply SetLike.coe_injective
    ext ⟨y, u⟩
    rw [hM, SetLike.mem_coe, LinearMap.mem_range]
    change u ∈ graphicalDerivative T x v y ↔ _
    rw [← mem_svResolvent_add_smul_iff hlam.ne', hL]
    change y = L (y + lam • u) ↔ _
    constructor
    · intro h
      refine ⟨y + lam • u, ?_⟩
      rw [hψ, ← h, add_sub_cancel_left, inv_smul_smul₀ hlam.ne']
    · rintro ⟨w, hw⟩
      rw [hψ, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      rw [smul_inv_smul₀ hlam.ne', add_sub_cancel]
  rw [hMψ, LinearMap.finrank_range_of_inj hinj]

/-- **Exercise 12.64 (proto-derivatives of monotone mappings)**, collected.  For
maximal monotone `T`, `v̄ ∈ T(x̄)` and `λ > 0`, with `R_λ = (I + λT)⁻¹` and
`z̄_λ = x̄ + λv̄`: if `T` is proto-differentiable at `x̄` for `v̄`, then `DT(x̄|v̄)`
is maximal monotone, and maximal cyclically monotone when `T` is; always
`DR_λ(z̄_λ) = (I + λDT(x̄|v̄))⁻¹`; proto-differentiability of `T` at `x̄` for `v̄`
is semidifferentiability of `R_λ` at `z̄_λ`, and also single-valuedness of
`DR_λ(z̄_λ)`; `R_λ` is differentiable at `z̄_λ` exactly when the graph of
`DT(x̄|v̄)` is a linear subspace, which is then `n`-dimensional. -/
theorem proto_derivatives_of_monotone_mappings {T : E → Set E} (hT : SvMaximalMonotone T)
    {x v : E} (hv : v ∈ T x) :
    (IsProtoDifferentiableAt T x v → SvMaximalMonotone (graphicalDerivative T x v)) ∧
    (SvMaximalCyclicallyMonotone T → IsProtoDifferentiableAt T x v →
      SvMaximalCyclicallyMonotone (graphicalDerivative T x v)) ∧
    ∀ lam : ℝ, 0 < lam →
      svResolvent T lam = svSingleton (resolventMap T lam) ∧
      graphicalDerivative (svResolvent T lam) (x + lam • v) x =
        svResolvent (graphicalDerivative T x v) lam ∧
      (IsProtoDifferentiableAt T x v ↔
        ∃ H, HasMappingSemiderivative (svResolvent T lam) (x + lam • v) x H) ∧
      (IsProtoDifferentiableAt T x v ↔
        ∃ A : E → E, graphicalDerivative (svResolvent T lam) (x + lam • v) x = svSingleton A) ∧
      (DifferentiableAt ℝ (resolventMap T lam) (x + lam • v) ↔
        ∃ M : Submodule ℝ (E × E), (M : Set (E × E)) = svGraph (graphicalDerivative T x v)) ∧
      ∀ M : Submodule ℝ (E × E), (M : Set (E × E)) = svGraph (graphicalDerivative T x v) →
        Module.finrank ℝ M = Module.finrank ℝ E :=
  ⟨svMaximalMonotone_graphicalDerivative hT hv,
    fun hc ↦ svMaximalCyclicallyMonotone_graphicalDerivative hc hv,
    fun _ hlam ↦ ⟨hT.svResolvent_eq_svSingleton hlam,
      graphicalDerivative_svResolvent T hlam.ne' x v,
      hT.isProtoDifferentiableAt_iff_semidifferentiable_svResolvent hlam hv,
      (hT.isProtoDifferentiableAt_iff_semidifferentiable_svResolvent hlam hv).trans
        (hT.semidifferentiable_svResolvent_iff hlam hv),
      hT.differentiableAt_resolventMap_iff hlam hv,
      fun M hM ↦ hT.finrank_eq_of_svGraph_graphicalDerivative hlam hv M hM⟩⟩

end MaximalMonotone



end RW
