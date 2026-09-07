/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Interior Tangents and Recession

Theorem 6.36 and Corollary 6.37.  A direction interior to the regular tangent
cone recedes locally, uniformly over a whole neighborhood of directions, and
such directions exist exactly when the normal cone is pointed.

Two of the printed conditions are interiors of convex cones, so 6.22 supplies
their strict pairing form directly; the loop is closed by 6.35, which turns the
nonstrict pairing at nearby points into local recession.  The passage from a
single interior direction to a *neighborhood* of directions is the only place
where the book's appeal to simplex neighborhoods (2.28(e)) is needed, and
Mathlib's `Convex.exists_subset_interior_convexHull_finset_of_isCompact`
supplies it: a compact convex set inside an open set can be squeezed between a
polytope and that set.
-/

import RockafellarWets.Chapter6.RecessionCharacterization
import Mathlib.Analysis.Normed.Affine.Convex

open Filter Metric Set Topology
open scoped InnerProductSpace

noncomputable section

namespace RW

section UniformHull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set E} {x : E}

/-- The uniform clause of 6.34(a) for the convex hull of a finite set of local
recession vectors, in the form the interior statements need. -/
theorem exists_uniform_localRecession_convexHull {u : Finset E}
    (hu : ∀ v ∈ u, v ∈ localRecessionCone C x) :
    ∃ V ∈ nhds x, ∃ ε > 0, ∀ y ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε,
      ∀ v ∈ convexHull ℝ (u : Set E), y + τ • v ∈ C := by
  classical
  obtain ⟨V, hV, ε, hε, hprop⟩ :=
    exists_uniform_localRecession (C := C) (x := x) (ι := {v // v ∈ u})
      (fun k ↦ (k : E)) (fun k ↦ hu k.1 k.2)
  refine ⟨V, hV, ε, hε, fun y hy τ hτ v hv ↦ ?_⟩
  rw [Finset.convexHull_eq] at hv
  obtain ⟨a, ha0, hasum, hacenter⟩ := hv
  have hsum1 : ∑ k : {v // v ∈ u}, a (k : E) = 1 := by
    rw [← hasum, ← Finset.attach_eq_univ]
    exact Finset.sum_attach u a
  have hrepr : ∑ k : {v // v ∈ u}, a (k : E) • (k : E) = v := by
    rw [← hacenter, Finset.centerMass, hasum, inv_one, one_smul,
      ← Finset.attach_eq_univ]
    exact Finset.sum_attach u fun z ↦ a z • z
  have hcomb := hprop y hy τ hτ (fun k : {v // v ∈ u} ↦ a (k : E))
    (fun k ↦ ha0 k.1 k.2) hsum1
  rwa [hrepr] at hcomb

end UniformHull

section InteriorTangents

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {C : Set E} {x w : E}

omit [FiniteDimensional ℝ E] in
/-- The normal cone being a cone, strict pairing against its unit vectors is
the same as strict pairing against all its nonzero vectors. -/
theorem forall_inner_lt_zero_iff (hx : x ∈ C) :
    (∀ v ∈ normalCone C x, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0) ↔
      ∀ v ∈ normalCone C x, v ≠ 0 → ⟪v, w⟫_ℝ < 0 := by
  constructor
  · intro h v hv hv0
    have hnpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hunit : ‖v‖⁻¹ • v ∈ normalCone C x :=
      (isCone_normalCone hx).2 hv (inv_pos.2 hnpos)
    have hnorm : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hnpos)]
      exact inv_mul_cancel₀ hnpos.ne'
    have hlt := h _ hunit hnorm
    rw [real_inner_smul_left] at hlt
    nlinarith [inv_pos.2 hnpos]
  · intro h v hv hnorm
    refine h v hv fun h0 ↦ ?_
    rw [h0, norm_zero] at hnorm
    norm_num at hnorm

/-- **Theorem 6.36**, (a) ⟺ (e): interiority of the regular tangent cone is
strict pairing against the unit normals.  This is 6.22 read through the
polarity 6.28(b). -/
theorem mem_interior_regularTangentCone_iff (hlc : IsLocallyClosedAt C x) (hx : x ∈ C) :
    w ∈ interior (regularTangentCone C x) ↔
      ∀ v ∈ normalCone C x, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0 := by
  rw [regularTangentCone_eq_polarCone_normalCone hx hlc,
    mem_interior_polarCone_iff_inner_lt_zero (isClosed_normalCone C x)
      (isCone_normalCone hx)]
  exact (forall_inner_lt_zero_iff hx).symm

/-- **Theorem 6.36**, (e) ⟹ (d): the strict pairing propagates to nearby
points of `C`.  Failure would produce unit normals at points approaching `x̄`
pairing nonnegatively with `w`, and a cluster point of those is a unit normal
at `x̄` by 6.6. -/
theorem exists_nhds_forall_inner_lt_zero (hx : x ∈ C)
    (he : ∀ v ∈ normalCone C x, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0) :
    ∃ V ∈ nhds x, ∀ y ∈ C ∩ V, ∀ v ∈ normalCone C y, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0 := by
  by_contra hcon
  push_neg at hcon
  have hpick : ∀ n : ℕ, ∃ y : E, ∃ v : E, y ∈ C ∧ dist y x < 1 / ((n : ℝ) + 1) ∧
      v ∈ normalCone C y ∧ ‖v‖ = 1 ∧ 0 ≤ ⟪v, w⟫_ℝ := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨y, hy, v, hv, hnorm, hnlt⟩ := hcon (ball x (1 / ((n : ℝ) + 1)))
      (ball_mem_nhds x hpos)
    exact ⟨y, v, hy.1, mem_ball.1 hy.2, hv, hnorm, hnlt⟩
  choose ys vs hyC hyd hvs hvnorm hvinner using hpick
  have hyto : Tendsto ys atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hyd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hmem : ∀ n, vs n ∈ closedBall (0 : E) 1 := fun n ↦ by
    rw [mem_closedBall, dist_zero_right, hvnorm n]
  obtain ⟨v, -, φ, hφ, hvto⟩ := (isCompact_closedBall (0 : E) 1).tendsto_subseq hmem
  have hφat : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hvnorm' : ‖v‖ = 1 := by
    refine tendsto_nhds_unique hvto.norm ?_
    simp only [Function.comp_apply, hvnorm]
    exact tendsto_const_nhds
  have hvmem : v ∈ normalCone C x :=
    mem_normalCone_of_tendsto hx (fun n ↦ hyC (φ n)) (hyto.comp hφat)
      (fun n ↦ hvs (φ n)) hvto
  have hvge : 0 ≤ ⟪v, w⟫_ℝ := by
    have hcont : Continuous fun u : E ↦ ⟪u, w⟫_ℝ := by fun_prop
    refine ge_of_tendsto' ((hcont.tendsto v).comp hvto) fun k ↦ ?_
    exact hvinner (φ k)
  exact absurd (he v hvmem hvnorm') (not_lt.2 hvge)

/-- **Theorem 6.36**, the identity `int T̂_C(x̄) = int R_C(x̄)`: an interior
regular tangent direction recedes locally, by 6.35. -/
theorem interior_regularTangentCone_eq_interior_localRecessionCone
    (hlc : IsLocallyClosedAt C x) (hx : x ∈ C) :
    interior (regularTangentCone C x) = interior (localRecessionCone C x) := by
  have hsub : interior (regularTangentCone C x) ⊆ localRecessionCone C x := by
    intro u hu
    have he : ∀ v ∈ normalCone C x, ‖v‖ = 1 → ⟪v, u⟫_ℝ < 0 :=
      (mem_interior_regularTangentCone_iff hlc hx).1 hu
    obtain ⟨V, hV, hprop⟩ := exists_nhds_forall_inner_lt_zero hx he
    refine (mem_localRecessionCone_iff_forall_inner_nonpos_normalCone hlc).2
      ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV, fun y hy v hv ↦ ?_⟩
    rcases eq_or_ne v 0 with rfl | hv0
    · simp
    · exact le_of_lt ((forall_inner_lt_zero_iff (w := u) hy.1).1
        (hprop y ⟨hy.1, interior_subset hy.2⟩) v hv hv0)
  refine Subset.antisymm ?_ (interior_mono (localRecessionCone_subset_regularTangentCone C x))
  exact interior_maximal hsub isOpen_interior

/-- **Theorem 6.36**, (b) ⟺ (e). -/
theorem mem_interior_localRecessionCone_iff (hlc : IsLocallyClosedAt C x) (hx : x ∈ C) :
    w ∈ interior (localRecessionCone C x) ↔
      ∀ v ∈ normalCone C x, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0 := by
  rw [← interior_regularTangentCone_eq_interior_localRecessionCone hlc hx]
  exact mem_interior_regularTangentCone_iff hlc hx

/-- **Theorem 6.36**, (d) ⟺ (e). -/
theorem exists_nhds_forall_inner_lt_zero_iff (hx : x ∈ C) :
    (∃ V ∈ nhds x, ∀ y ∈ C ∩ V, ∀ v ∈ normalCone C y, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0) ↔
      ∀ v ∈ normalCone C x, ‖v‖ = 1 → ⟪v, w⟫_ℝ < 0 := by
  constructor
  · rintro ⟨V, hV, hprop⟩
    exact hprop x ⟨hx, mem_of_mem_nhds hV⟩
  · exact exists_nhds_forall_inner_lt_zero hx

end InteriorTangents

section UniformNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {C : Set E} {x w : E}

omit [FiniteDimensional ℝ E] in
/-- **Theorem 6.36**, (c) ⟹ (b): a neighborhood of directions that may all be
added consists of local recession vectors. -/
theorem mem_interior_localRecessionCone_of_uniform
    {W : Set E} (hW : W ∈ nhds w) {V : Set E} (hV : V ∈ nhds x) {ε : ℝ} (hε : 0 < ε)
    (hprop : ∀ y ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε, ∀ u ∈ W, y + τ • u ∈ C) :
    w ∈ interior (localRecessionCone C x) := by
  have hsub : W ⊆ localRecessionCone C x := fun u hu ↦
    ⟨V, hV, ε, hε, fun y hy τ hτ ↦ hprop y hy τ hτ u hu⟩
  exact mem_interior_iff_mem_nhds.2 (mem_of_superset hW hsub)

/-- **Theorem 6.36**, (b) ⟹ (c): an interior local recession direction has a
whole neighborhood of directions that may be added uniformly.  A polytope is
squeezed between the point and the cone, and 6.34(a) is uniform on its convex
hull. -/
theorem exists_uniform_nhds_of_mem_interior_localRecessionCone
    (hw : w ∈ interior (localRecessionCone C x)) :
    ∃ W ∈ nhds w, ∃ V ∈ nhds x, ∃ ε > 0,
      ∀ y ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε, ∀ u ∈ W, y + τ • u ∈ C := by
  obtain ⟨u, hu1, hu2⟩ :=
    (convex_singleton w).exists_subset_interior_convexHull_finset_of_isCompact
      isCompact_singleton (by
        rw [nhdsSet_singleton]
        exact mem_interior_iff_mem_nhds.1 hw)
  obtain ⟨V, hV, ε, hε, hprop⟩ :=
    exists_uniform_localRecession_convexHull (C := C) (x := x) (u := u)
      fun v hv ↦ hu2 (subset_convexHull ℝ (u : Set E) hv)
  refine ⟨interior (convexHull ℝ (u : Set E)),
    isOpen_interior.mem_nhds (hu1 (mem_singleton w)), V, hV, ε, hε, ?_⟩
  exact fun y hy τ hτ v hv ↦ hprop y hy τ hτ v (interior_subset hv)

/-- **Theorem 6.36**, the existence clause: an interior regular tangent
direction exists exactly when the normal cone is pointed. -/
theorem interior_regularTangentCone_nonempty_iff_isPointed
    (hlc : IsLocallyClosedAt C x) (hx : x ∈ C) :
    (interior (regularTangentCone C x)).Nonempty ↔ IsPointed (normalCone C x) := by
  rw [regularTangentCone_eq_polarCone_normalCone hx hlc]
  exact interior_polarCone_nonempty_iff_isPointed (isClosed_normalCone C x)
    (isCone_normalCone hx)

/-- **Theorem 6.36**, the closing statement: when interior directions exist the
regular tangent cone is the closure of the local recession cone. -/
theorem closure_localRecessionCone_eq_regularTangentCone
    (hlc : IsLocallyClosedAt C x) (hx : x ∈ C)
    (hne : (interior (regularTangentCone C x)).Nonempty) :
    closure (localRecessionCone C x) = regularTangentCone C x := by
  have hpolar := regularTangentCone_eq_polarCone_normalCone hx hlc
  have hTconv : Convex ℝ (regularTangentCone C x) := by
    rw [hpolar]
    exact convex_polarCone _
  have hTclosed : IsClosed (regularTangentCone C x) := by
    rw [hpolar]
    exact isClosed_polarCone _
  have heq := interior_regularTangentCone_eq_interior_localRecessionCone hlc hx
  have h1 : closure (interior (regularTangentCone C x)) = regularTangentCone C x := by
    rw [hTconv.closure_interior_eq_closure_of_nonempty_interior hne, hTclosed.closure_eq]
  refine Subset.antisymm ?_ ?_
  · have hmono := closure_mono (localRecessionCone_subset_regularTangentCone C x)
    rwa [hTclosed.closure_eq] at hmono
  · rw [← h1, heq]
    exact closure_mono interior_subset

/-- **Corollary 6.37**, internal approximation: a compact set of interior
regular tangent directions may be added uniformly.  Each point of the compact
set is covered by a polytope inside the local recession cone; finitely many
suffice, and the *union* of their vertex sets gives a single polytope, so one
neighborhood and one step size serve the whole compact set. -/
theorem exists_uniform_of_isCompact_subset_interior_regularTangentCone
    (hlc : IsLocallyClosedAt C x) (hx : x ∈ C) {B : Set E} (hB : IsCompact B)
    (hBsub : B ⊆ interior (regularTangentCone C x)) :
    ∃ V ∈ nhds x, ∃ ε > 0, ∀ y ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε, ∀ u ∈ B, y + τ • u ∈ C := by
  classical
  have hBR : B ⊆ interior (localRecessionCone C x) := by
    rw [← interior_regularTangentCone_eq_interior_localRecessionCone hlc hx]
    exact hBsub
  have hstep : ∀ p : B, ∃ up : Finset E,
      (p : E) ∈ interior (convexHull ℝ (up : Set E)) ∧
        convexHull ℝ (up : Set E) ⊆ localRecessionCone C x := by
    intro p
    obtain ⟨up, h1, h2⟩ :=
      (convex_singleton (p : E)).exists_subset_interior_convexHull_finset_of_isCompact
        isCompact_singleton (by
          rw [nhdsSet_singleton]
          exact mem_interior_iff_mem_nhds.1 (hBR p.2))
    exact ⟨up, h1 (mem_singleton _), h2⟩
  choose us hus1 hus2 using hstep
  obtain ⟨t, ht⟩ := hB.elim_finite_subcover
    (fun p : B ↦ interior (convexHull ℝ (us p : Set E)))
    (fun _ ↦ isOpen_interior)
    (fun v hv ↦ mem_iUnion.2 ⟨⟨v, hv⟩, hus1 ⟨v, hv⟩⟩)
  set U : Finset E := t.biUnion us with hUdef
  have hUsub : ∀ v ∈ U, v ∈ localRecessionCone C x := by
    intro v hv
    obtain ⟨p, -, hvp⟩ := Finset.mem_biUnion.1 hv
    exact hus2 p (subset_convexHull ℝ (us p : Set E) hvp)
  obtain ⟨V, hV, ε, hε, hprop⟩ :=
    exists_uniform_localRecession_convexHull (C := C) (x := x) (u := U) hUsub
  refine ⟨V, hV, ε, hε, fun y hy τ hτ v hv ↦ ?_⟩
  obtain ⟨p, hpt, hvp⟩ := mem_iUnion₂.1 (ht hv)
  refine hprop y hy τ hτ v ?_
  refine convexHull_mono ?_ (interior_subset hvp)
  exact_mod_cast Finset.coe_subset.2 (Finset.subset_biUnion_of_mem us hpt)

/-- **Corollary 6.37** in the printed magnified form: the compact set is
contained in every magnified difference set at nearby points and small
scales. -/
theorem exists_uniform_blowUp_of_isCompact_subset_interior_regularTangentCone
    (hlc : IsLocallyClosedAt C x) (hx : x ∈ C) {B : Set E} (hB : IsCompact B)
    (hBsub : B ⊆ interior (regularTangentCone C x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ∃ ε > 0,
      ∀ y ∈ C ∩ V, ∀ τ ∈ Ioo (0 : ℝ) ε, B ⊆ blowUp C y τ := by
  obtain ⟨V, hV, ε, hε, hprop⟩ :=
    exists_uniform_of_isCompact_subset_interior_regularTangentCone hlc hx hB hBsub
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ε, hε,
    fun y hy τ hτ u hu ↦ ?_⟩
  rw [blowUp_eq_preimage (ne_of_gt hτ.1)]
  exact hprop y ⟨hy.1, interior_subset hy.2⟩ τ ⟨hτ.1.le, hτ.2.le⟩ u hu

/-- **Corollary 6.37**, the tangential consequence: nearby tangent cones all
contain the compact set. -/
theorem exists_isOpen_subset_tangentCone_of_isCompact
    (hlc : IsLocallyClosedAt C x) (hx : x ∈ C) {B : Set E} (hB : IsCompact B)
    (hBsub : B ⊆ interior (regularTangentCone C x)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ C ∩ V,
      B ⊆ localRecessionCone C y ∧ B ⊆ tangentCone C y := by
  obtain ⟨V, hV, ε, hε, hprop⟩ :=
    exists_uniform_of_isCompact_subset_interior_regularTangentCone hlc hx hB hBsub
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV, fun y hy ↦ ?_⟩
  have hrec : B ⊆ localRecessionCone C y := fun u hu ↦
    ⟨interior V, isOpen_interior.mem_nhds hy.2, ε, hε, fun z hz τ hτ ↦
      hprop z ⟨hz.1, interior_subset hz.2⟩ τ hτ u hu⟩
  exact ⟨hrec, hrec.trans (localRecessionCone_subset_tangentCone hy.1)⟩

/-- **Corollary 6.37**, the parenthetical variant: at a point of Clarke
regularity the ordinary tangent cone may be used, the two cones agreeing
there by 6.29. -/
theorem exists_uniform_of_isCompact_subset_interior_tangentCone
    (hreg : IsClarkeRegularAt C x) (hx : x ∈ C) {B : Set E} (hB : IsCompact B)
    (hBsub : B ⊆ interior (tangentCone C x)) :
    ∃ V ∈ nhds x, ∃ ε > 0, ∀ y ∈ C ∩ V, ∀ τ ∈ Icc (0 : ℝ) ε, ∀ u ∈ B, y + τ • u ∈ C := by
  refine exists_uniform_of_isCompact_subset_interior_regularTangentCone hreg.1 hx hB ?_
  rw [← (isClarkeRegularAt_iff_tangentCone_eq hx hreg.1).1 hreg]
  exact hBsub

end UniformNeighborhood

end RW
