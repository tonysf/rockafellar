/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: monotonicity of piecewise polyhedral mappings

This file formalizes Proposition 12.29, together with the parts of Definition
2.47 and Exercise 2.48 that it uses.

* A mapping `S` is piecewise polyhedral (9.57) when `gph S` is a finite union of
  polyhedral sets (`SvPiecewisePolyhedral`).
* A mapping `G : D → F` is piecewise linear on `D` (2.47(a)) when `D` is a finite
  union of polyhedral sets on each of which `G` is affine (`IsPiecewiseLinearOn`).
* Exercise 2.48: `G` is piecewise linear on `D` exactly when its graph over `D`
  is piecewise polyhedral.  For the converse, a convex piece of a graph is the
  graph of an affine map: the projection to the first factor is injective on
  the span of differences of the piece (a barycentric perturbation argument),
  and a left inverse of it gives the linear part
  (`exists_affine_of_convex_subset_graph`).

For 12.29, `gph (I + λT)⁻¹` is the image of `gph T` under the invertible linear
map `(x, v) ↦ (x + λv, x)`, and for maximal monotone `T` the resolvent is
single-valued everywhere (12.12), so 2.48 converts piecewise polyhedrality of
its graph into piecewise linearity of `resolventMap T λ` on the whole space.
-/

import RockafellarWets.Chapter12.ResolventMaximality
import RockafellarWets.Chapter9.PiecewisePolyhedralCalmness

open Set
open scoped InnerProductSpace Pointwise

namespace RW

section Definitions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Example 9.57**: a mapping is piecewise polyhedral when its graph is the
union of finitely many polyhedral sets. -/
def SvPiecewisePolyhedral (S : E → Set F) : Prop :=
  IsPiecewisePolyhedral (svGraph S)

/-- **Definition 2.47(a) (piecewise linearity).**  `G` is piecewise linear on
`D` if `D` is the union of finitely many polyhedral sets, relative to each of
which `G(x) = Ax + a` for a linear map `A` and a vector `a`. -/
def IsPiecewiseLinearOn (G : E → F) (D : Set E) : Prop :=
  ∃ m : ℕ, ∃ C : Fin m → Set E, ∃ A : Fin m → E →L[ℝ] F, ∃ a : Fin m → F,
    (∀ i, IsPolyhedral (C i)) ∧ D = ⋃ i, C i ∧ ∀ i, ∀ x ∈ C i, G x = A i x + a i

/-- Linear images of piecewise polyhedral sets are piecewise polyhedral. -/
theorem IsPiecewisePolyhedral.linear_image {A : Set E} (hA : IsPiecewisePolyhedral A)
    (L : E →ₗ[ℝ] F) : IsPiecewisePolyhedral (L '' A) := by
  obtain ⟨m, C, hC, rfl⟩ := hA
  exact ⟨m, fun i ↦ L '' C i, fun i ↦ (hC i).linear_image L, image_iUnion⟩

end Definitions

section Graphs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
/-- A convex set contained in the graph of a function is the graph of the
restriction of an affine map. -/
theorem exists_affine_of_convex_subset_graph {G : Set (E × F)} (hG : Convex ℝ G)
    (hfun : ∀ p ∈ G, ∀ q ∈ G, p.1 = q.1 → p.2 = q.2) :
    ∃ A : E →L[ℝ] F, ∃ a : F, ∀ p ∈ G, p.2 = A p.1 + a := by
  rcases G.eq_empty_or_nonempty with rfl | ⟨g₀, hg₀⟩
  · exact ⟨0, 0, fun p hp ↦ absurd hp (notMem_empty p)⟩
  set L : Submodule ℝ (E × F) := Submodule.span ℝ ((fun p ↦ p - g₀) '' G) with hLdef
  have key : ∀ d ∈ L, d.1 = 0 → d.2 = 0 := by
    intro d hd hd1
    obtain ⟨n, c, s, hsum⟩ := Submodule.mem_span_set'.1 hd
    choose p hp hps using fun i ↦ (s i).2
    set ε : ℝ := 1 / ((n + 1) * (∑ i, |c i| + 1)) with hεdef
    have hM : 0 ≤ ∑ i, |c i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
    have hε : 0 < ε := by positivity
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hεc : ∀ i, ε * |c i| ≤ 1 / (n + 1) := by
      intro i
      have hci : |c i| ≤ ∑ j, |c j| :=
        Finset.single_le_sum (f := fun j ↦ |c j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
      rw [hεdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hn]
      nlinarith
    have hεsum : ε * |∑ i, c i| ≤ 1 / (n + 1) := by
      have hs : |∑ i, c i| ≤ ∑ i, |c i| := Finset.abs_sum_le_sum_abs _ _
      rw [hεdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hn]
      nlinarith
    set P : Fin (n + 1) → E × F := Fin.cons g₀ p
    set w : Fin (n + 1) → ℝ := Fin.cons (1 / (n + 1) - ε * ∑ i, c i)
      (fun i ↦ 1 / (n + 1) + ε * c i)
    set w' : Fin (n + 1) → ℝ := fun _ ↦ 1 / (n + 1)
    have hPG : ∀ j ∈ Finset.univ, P j ∈ G := by
      intro j _
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · exact hg₀
      · exact hp i
    have hw₀ : ∀ j ∈ Finset.univ, 0 ≤ w j := by
      intro j _
      refine Fin.cases ?_ (fun i ↦ ?_) j
      · simp only [w, Fin.cons_zero]
        have := le_abs_self (∑ i, c i)
        nlinarith
      · simp only [w, Fin.cons_succ]
        have := neg_abs_le (c i)
        nlinarith [hεc i]
    have hw₁ : ∑ j, w j = 1 := by
      simp only [w, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      field_simp
      ring
    have hw'₀ : ∀ j ∈ Finset.univ, 0 ≤ w' j := fun j _ ↦ by positivity
    have hw'₁ : ∑ j, w' j = 1 := by
      simp only [w', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      push_cast
      ring
    have hm₁ := hG.sum_mem hw₀ hw₁ hPG
    have hm₂ := hG.sum_mem hw'₀ hw'₁ hPG
    have hps' : ∀ i, p i - g₀ = (s i : E × F) := hps
    have hd' : d = ∑ i, c i • (p i - g₀) := by
      rw [← hsum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [← hps' i]
    have hdiff : ∑ j, w j • P j = ∑ j, w' j • P j + ε • d := by
      rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
      simp only [← sub_smul]
      rw [Fin.sum_univ_succ]
      simp only [P, w, w', Fin.cons_zero, Fin.cons_succ, add_sub_cancel_left, sub_sub_cancel_left]
      rw [hd', Finset.smul_sum]
      simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, neg_smul, Finset.mul_sum,
        Finset.sum_smul]
      abel
    have h1 : (∑ j, w j • P j).1 = (∑ j, w' j • P j).1 := by
      rw [hdiff, Prod.fst_add, Prod.smul_fst, hd1, smul_zero, add_zero]
    have h2 := hfun _ hm₁ _ hm₂ h1
    rw [hdiff, Prod.snd_add, Prod.smul_snd, add_eq_left] at h2
    exact (smul_eq_zero.1 h2).resolve_left hε.ne'
  set π : L →ₗ[ℝ] E := (LinearMap.fst ℝ E F).comp L.subtype with hπ
  have hker : LinearMap.ker π = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun d hd ↦ ?_
    have h1 : (d : E × F).1 = 0 := hd
    have h2 := key d d.2 h1
    exact Subtype.ext (Prod.ext h1 h2)
  obtain ⟨ψ, hψ⟩ := π.exists_leftInverse_of_injective hker
  set A : E →ₗ[ℝ] F := (LinearMap.snd ℝ E F).comp (L.subtype.comp ψ) with hA
  refine ⟨LinearMap.toContinuousLinearMap A, g₀.2 - A g₀.1, fun q hq ↦ ?_⟩
  have hdL : q - g₀ ∈ L := Submodule.subset_span ⟨q, hq, rfl⟩
  have hψd : ψ (q - g₀).1 = ⟨q - g₀, hdL⟩ := by
    have := congrArg (fun h ↦ h ⟨q - g₀, hdL⟩) hψ
    simpa [π] using this
  have hAd : A (q - g₀).1 = (q - g₀).2 := by
    simp only [hA, LinearMap.comp_apply, hψd, Submodule.subtype_apply, LinearMap.snd_apply]
  have h1 : A q.1 - A g₀.1 = q.2 - g₀.2 := by
    rw [← map_sub, ← Prod.fst_sub, hAd, Prod.snd_sub]
  have h2 : A q.1 = q.2 - g₀.2 + A g₀.1 := by
    rw [← h1]
    abel
  change q.2 = A q.1 + (g₀.2 - A g₀.1)
  rw [h2]
  abel

omit [FiniteDimensional ℝ F] in
/-- **Exercise 2.48 (graphs of piecewise linear mappings).**  `G` is piecewise
linear relative to `D` exactly when its graph over `D` is a finite union of
polyhedral sets. -/
theorem isPiecewiseLinearOn_iff_isPiecewisePolyhedral_graph (G : E → F) (D : Set E) :
    IsPiecewiseLinearOn G D ↔ IsPiecewisePolyhedral {p : E × F | p.1 ∈ D ∧ p.2 = G p.1} := by
  constructor
  · rintro ⟨m, C, A, a, hC, rfl, hG⟩
    refine ⟨m, fun i ↦ (LinearMap.prod LinearMap.id (A i : E →ₗ[ℝ] F)) '' C i +
      {((0 : E), a i)}, fun i ↦ ((hC i).linear_image _).add (IsPolyhedral.singleton _), ?_⟩
    ext ⟨x, u⟩
    simp only [mem_setOf_eq, mem_iUnion, mem_add, mem_image, mem_singleton_iff,
      LinearMap.prod_apply, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨i, _, ⟨x, hi, rfl⟩, _, rfl, by rw [hG i x hi]; simp⟩
    · rintro ⟨i, _, ⟨y, hy, rfl⟩, _, rfl, he⟩
      simp only [Pi.prod, Prod.mk_add_mk, add_zero, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨⟨i, hy⟩, (hG i y hy).symm⟩
  · rintro ⟨m, K, hK, hgraph⟩
    have hsub : ∀ j, K j ⊆ {p : E × F | p.1 ∈ D ∧ p.2 = G p.1} := fun j ↦
      hgraph ▸ subset_iUnion K j
    have hfun : ∀ j, ∀ p ∈ K j, ∀ q ∈ K j, p.1 = q.1 → p.2 = q.2 := by
      intro j p hp q hq hpq
      rw [(hsub j hp).2, (hsub j hq).2, hpq]
    choose A a hAa using fun j ↦ exists_affine_of_convex_subset_graph (hK j).convex (hfun j)
    refine ⟨m, fun j ↦ (LinearMap.fst ℝ E F) '' K j, A, a,
      fun j ↦ (hK j).linear_image _, ?_, ?_⟩
    · ext x
      simp only [mem_iUnion, mem_image, LinearMap.fst_apply]
      constructor
      · intro hx
        have : (x, G x) ∈ ⋃ j, K j := hgraph ▸ ⟨hx, rfl⟩
        obtain ⟨j, hj⟩ := mem_iUnion.1 this
        exact ⟨j, _, hj, rfl⟩
      · rintro ⟨j, p, hp, rfl⟩
        exact (hsub j hp).1
    · rintro j x ⟨p, hp, rfl⟩
      simp only [LinearMap.fst_apply]
      rw [← (hsub j hp).2]
      exact hAa j p hp

end Graphs

section Resolvents

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear map `(x, v) ↦ (x + λv, x)` carrying `gph T` onto `gph (I + λT)⁻¹`. -/
def resolventGraphMap (lam : ℝ) : E × E →ₗ[ℝ] E × E :=
  LinearMap.prod (LinearMap.fst ℝ E E + lam • LinearMap.snd ℝ E E) (LinearMap.fst ℝ E E)

/-- The inverse linear map `(z, x) ↦ (x, λ⁻¹(z - x))`. -/
noncomputable def resolventGraphMapInv (lam : ℝ) : E × E →ₗ[ℝ] E × E :=
  LinearMap.prod (LinearMap.snd ℝ E E) (lam⁻¹ • (LinearMap.fst ℝ E E - LinearMap.snd ℝ E E))

theorem svGraph_svResolvent_eq_image (T : E → Set E) (lam : ℝ) :
    svGraph (svResolvent T lam) = resolventGraphMap lam '' svGraph T := by
  ext ⟨z, x⟩
  simp only [mem_svGraph, mem_svResolvent, mem_image, Prod.exists, resolventGraphMap,
    LinearMap.prod_apply, Pi.prod, LinearMap.add_apply, LinearMap.fst_apply,
    LinearMap.smul_apply, LinearMap.snd_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨x, v, hv, rfl, rfl⟩
  · rintro ⟨x', v, hv, rfl, rfl⟩
    exact ⟨v, hv, rfl⟩

theorem svGraph_eq_image_svResolvent (T : E → Set E) {lam : ℝ} (hlam : lam ≠ 0) :
    svGraph T = resolventGraphMapInv lam '' svGraph (svResolvent T lam) := by
  ext ⟨x, v⟩
  simp only [mem_svGraph, mem_svResolvent, mem_image, Prod.exists, resolventGraphMapInv,
    LinearMap.prod_apply, Pi.prod, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Prod.mk.injEq]
  constructor
  · intro hv
    refine ⟨x + lam • v, x, ⟨v, hv, rfl⟩, rfl, ?_⟩
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  · rintro ⟨z, x', ⟨v', hv', rfl⟩, rfl, rfl⟩
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    exact hv'

/-- For `λ ≠ 0`, `T` is piecewise polyhedral exactly when `(I + λT)⁻¹` is. -/
theorem svPiecewisePolyhedral_iff_svResolvent (T : E → Set E) {lam : ℝ} (hlam : lam ≠ 0) :
    SvPiecewisePolyhedral T ↔ SvPiecewisePolyhedral (svResolvent T lam) := by
  constructor
  · intro h
    unfold SvPiecewisePolyhedral at h ⊢
    rw [svGraph_svResolvent_eq_image]
    exact h.linear_image _
  · intro h
    unfold SvPiecewisePolyhedral at h ⊢
    rw [svGraph_eq_image_svResolvent T hlam]
    exact h.linear_image _

variable [FiniteDimensional ℝ E]

/-- For maximal monotone `T` and `λ > 0`, the graph of `(I + λT)⁻¹` is the graph
of `resolventMap T λ` over the whole space (12.12). -/
theorem svGraph_svResolvent_eq_graph {T : E → Set E} (hT : SvMaximalMonotone T) {lam : ℝ}
    (hlam : 0 < lam) :
    svGraph (svResolvent T lam) = {p : E × E | p.1 ∈ univ ∧ p.2 = resolventMap T lam p.1} := by
  ext ⟨z, x⟩
  rw [mem_svGraph, hT.svResolvent_eq_singleton_resolventMap hlam]
  simp

/-- For maximal monotone `T` and `λ > 0`, `T` is piecewise polyhedral exactly
when `(I + λT)⁻¹` is piecewise linear. -/
theorem svPiecewisePolyhedral_iff_isPiecewiseLinearOn_resolventMap {T : E → Set E}
    (hT : SvMaximalMonotone T) {lam : ℝ} (hlam : 0 < lam) :
    SvPiecewisePolyhedral T ↔ IsPiecewiseLinearOn (resolventMap T lam) univ := by
  rw [svPiecewisePolyhedral_iff_svResolvent T hlam.ne', SvPiecewisePolyhedral,
    svGraph_svResolvent_eq_graph hT hlam, isPiecewiseLinearOn_iff_isPiecewisePolyhedral_graph]

/-- **Proposition 12.29 (monotonicity of piecewise polyhedral mappings).**  For
maximal monotone `T`, `T` is piecewise polyhedral if and only if, for some
`λ > 0`, the resolvent `(I + λT)⁻¹ = resolventMap T λ` (single-valued by 12.12)
is piecewise linear, in which case this holds for every `λ > 0`. -/
theorem monotonicity_of_piecewise_polyhedral_mappings {T : E → Set E}
    (hT : SvMaximalMonotone T) :
    (∀ lam : ℝ, 0 < lam → svResolvent T lam = fun z ↦ {resolventMap T lam z}) ∧
      (SvPiecewisePolyhedral T ↔
        ∃ lam : ℝ, 0 < lam ∧ IsPiecewiseLinearOn (resolventMap T lam) univ) ∧
      (SvPiecewisePolyhedral T → ∀ lam : ℝ, 0 < lam →
        IsPiecewiseLinearOn (resolventMap T lam) univ) :=
  ⟨fun _ hlam ↦ hT.svResolvent_eq_fun hlam,
    ⟨fun h ↦ ⟨1, one_pos, (svPiecewisePolyhedral_iff_isPiecewiseLinearOn_resolventMap hT
      one_pos).1 h⟩, fun ⟨_, hlam, h⟩ ↦
        (svPiecewisePolyhedral_iff_isPiecewiseLinearOn_resolventMap hT hlam).2 h⟩,
    fun h _ hlam ↦ (svPiecewisePolyhedral_iff_isPiecewiseLinearOn_resolventMap hT hlam).1 h⟩

end Resolvents

end RW
