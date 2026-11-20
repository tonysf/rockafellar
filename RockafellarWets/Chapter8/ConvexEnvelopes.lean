/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Affine supports of closed convex functions

For each point below the epigraph, a small-parameter Moreau envelope
separates it from the graph. Its proximal point gives a touching affine
minorant, even if the function takes the value positive infinity at the
original point.
-/

import RockafellarWets.Chapter7.ProximalEstimates
import RockafellarWets.Chapter7.MoreauEpiCharacterization
import RockafellarWets.Chapter3.HomogeneousOperations
import RockafellarWets.Chapter3.PolyhedralOperations.Affine
import RockafellarWets.Chapter3.ConvexHullFunctionSharp
import RockafellarWets.Chapter7.ConvexEpiConvergence

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An affine support is a global affine minorant that agrees with the
function at some point. -/
def IsAffineSupport (f : E → EReal) (l : E →L[ℝ] ℝ) (b : ℝ) : Prop :=
  (∀ y, ((l y + b : ℝ) : EReal) ≤ f y) ∧ ∃ y, f y = ((l y + b : ℝ) : EReal)

private theorem proximal_affine_support {f : E → EReal} (hc : Convex ℝ (epigraph f))
    (hp : IsProper f) {x y : E} {t m : ℝ} (ht : 0 < t)
    (hy : y ∈ proximalMappingEReal f t x) (hm : moreauEnvelopeEReal f t x = m) :
    ∃ l : E →L[ℝ] ℝ, ∃ b : ℝ, IsAffineSupport f l b ∧ m ≤ l x + b := by
  let l : E →L[ℝ] ℝ := t⁻¹ • innerSL ℝ (x - y)
  let c := (f y).toReal
  have hobj := (mem_proximalMappingEReal_iff.mp hy).1.trans hm
  have hyfin : f y ≠ ⊤ := by
    intro he
    rw [proximalObjectiveEReal, he, EReal.top_add_coe] at hobj
    exact EReal.coe_ne_top _ hobj.symm
  have hcy : (c : EReal) = f y := EReal.coe_toReal hyfin (hp.2 y).ne'
  have hmeq : c + (1 / (2*t)) * ‖y - x‖^2 = m := by
    apply EReal.coe_injective
    rwa [EReal.coe_add, hcy]
  have hld (z : E) : l z - l y = t⁻¹ * ⟪x-y,z-y⟫_ℝ := by
    rw [← map_sub]
    rfl
  refine ⟨l, c - l y, ⟨?_, ⟨y, by simpa using hcy.symm⟩⟩, ?_⟩
  · intro z
    by_cases hzt : f z = ⊤
    · simp [hzt]
    have hzr := EReal.coe_toReal hzt (hp.2 z).ne'
    let d := (f z).toReal
    have hobjz : proximalObjectiveEReal f t x z ≤ ((d + (1/(2*t))*‖z-x‖^2 : ℝ) : EReal) := by
      rw [proximalObjectiveEReal, EReal.coe_add, show (d : EReal) = f z from hzr]
    have hg := proximalObjectiveEReal_quadratic_growth hc hy hm hobjz
    have hn : ‖z-x‖^2 = ‖z-y‖^2 + 2 * ⟪y-x,z-y⟫_ℝ + ‖y-x‖^2 := by
      rw [show z-x = (y-x)+(z-y) by abel, norm_add_sq_real]
      ring
    rw [hn, norm_sub_rev y z, ← hmeq] at hg
    rw [← hzr]
    apply EReal.coe_le_coe_iff.mpr
    rw [show l z + (c - l y) = c + (l z - l y) by ring, hld,
      show x-y = -(y-x) by abel, inner_neg_left]
    change _ ≤ d
    field_simp [ht.ne'] at hg ⊢
    nlinarith
  · rw [show l x + (c - l y) = c + (l x - l y) by ring, hld, real_inner_self_eq_norm_sq,
      ← hmeq, norm_sub_rev x y]
    have h : 0 ≤ ‖y-x‖^2 := sq_nonneg _
    field_simp [ht.ne']
    nlinarith

/-- Each strict lower test height is separated by an actual touching
affine support. This also holds outside the effective domain. -/
theorem exists_affineSupport_gt_of_lt [FiniteDimensional ℝ E]
    {f : E → EReal} (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f)
    (hp : IsProper f) {x : E} {a : ℝ} (ha : (a : EReal) < f x) :
    ∃ l : E →L[ℝ] ℝ, ∃ b : ℝ, IsAffineSupport f l b ∧ a < l x + b := by
  obtain ⟨β, hab, hβ⟩ := EReal.exists_between_coe_real ha
  have hprox : IsProxBounded f := (isProxBounded_iff_exists_moreauEnvelopeEReal f).2
    ⟨1, one_pos, x, (moreauEnvelopeEReal_finite hc hl hp one_pos x).1⟩
  obtain ⟨δ, hδ, henv⟩ := eventually_le_moreauEnvelope_at_zero hprox hl hβ
  let t := δ / 2
  have ht : 0 < t := half_pos hδ
  obtain ⟨y, hy⟩ := proximalMappingEReal_nonempty hc hl hp ht x
  obtain ⟨hmb, hmt⟩ := moreauEnvelopeEReal_finite hc hl hp ht x
  have hm := EReal.coe_toReal hmt.ne hmb.ne'
  obtain ⟨l, b, hs, hmx⟩ := proximal_affine_support hc hp ht hy hm.symm
  refine ⟨l, b, hs, (EReal.coe_lt_coe_iff.mp hab).trans_le ((EReal.coe_le_coe_iff.mp ?_).trans hmx)⟩
  rw [hm]
  exact henv t ⟨ht, half_lt_self hδ⟩

/-- **Theorem 8.13.** A proper lower semicontinuous convex function is
the pointwise supremum of its affine supports. -/
theorem eq_iSup_affineSupports [FiniteDimensional ℝ E]
    {f : E → EReal} (hc : Convex ℝ (epigraph f)) (hl : LowerSemicontinuous f)
    (hp : IsProper f) (x : E) :
    f x = ⨆ p : {p : (E →L[ℝ] ℝ) × ℝ // IsAffineSupport f p.1 p.2},
      ((p.val.1 x + p.val.2 : ℝ) : EReal) := by
  apply le_antisymm _ (iSup_le fun p ↦ p.property.1 x)
  by_contra! h
  obtain ⟨a, hlow, hhigh⟩ := EReal.exists_between_coe_real h
  obtain ⟨l, b, hs, hlt⟩ := exists_affineSupport_gt_of_lt hc hl hp hhigh
  let p : {p : (E →L[ℝ] ℝ) × ℝ // IsAffineSupport f p.1 p.2} := ⟨(l, b), hs⟩
  exact (not_lt_of_ge (le_iSup (fun q : {p : (E →L[ℝ] ℝ) × ℝ // IsAffineSupport f p.1 p.2} ↦
    ((q.val.1 x + q.val.2 : ℝ) : EReal)) p)) (hlow.trans (EReal.coe_lt_coe_iff.mpr hlt))

/-- A proper convex function has a touching affine support at every interior
point of its effective domain. Global lower semicontinuity is unnecessary. -/
theorem exists_affineSupport_at_of_mem_interior [FiniteDimensional ℝ E]
    {f : E → EReal} (hc : Convex ℝ (epigraph f)) (hp : IsProper f)
    {x : E} (hx : x ∈ interior (effectiveDomain f)) :
    ∃ l : E →L[ℝ] ℝ, ∃ b : ℝ, IsAffineSupport f l b ∧ f x = ((l x + b : ℝ) : EReal) := by
  let c := (f x).toReal
  have hcx : (c : EReal) = f x :=
    EReal.coe_toReal (show x ∈ effectiveDomain f from interior_subset hx).ne (hp.2 x).ne'
  have hi : (x, c+1) ∈ interior (epigraph f) :=
    mem_interior_epigraph_of_mem_interior_effectiveDomain hc hx (by
      rw [← hcx]
      exact EReal.coe_lt_coe_iff.mpr (lt_add_one _))
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open hc.interior isOpen_interior
    (graphPoint_not_mem_interior_epigraph hcx)
  let a := L (0,1)
  let A : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hsplit (z : E) (r : ℝ) : L (z,r) = A z + r*a := by
    have heq : (z,r) = (z,0) + r • ((0,1) : E × ℝ) := by simp
    rw [heq, map_add, map_smul]
    rfl
  have ha : 0 < a := by
    have h := hL _ hi
    rw [hsplit, hsplit] at h
    linarith
  have hhalf : epigraph f ⊆ {p | L (x,c) ≤ L p} := by
    have h := closure_minimal (fun y (hy : y ∈ interior (epigraph f)) ↦ (hL _ hy).le)
      (isClosed_le continuous_const L.continuous)
    rw [hc.closure_interior_eq_closure_of_nonempty_interior ⟨_, hi⟩] at h
    exact subset_closure.trans h
  let l : E →L[ℝ] ℝ := -(a⁻¹ • A)
  have hs : ∀ z, ((l z + (c-l x) : ℝ) : EReal) ≤ f z := by
    intro z
    by_cases hzt : f z = ⊤
    · simp [hzt]
    have hzr := EReal.coe_toReal hzt (hp.2 z).ne'
    have h := hhalf (show (z,(f z).toReal) ∈ epigraph f from hzr.ge)
    change L (x,c) ≤ L (z,(f z).toReal) at h
    rw [hsplit, hsplit] at h
    rw [← hzr]
    apply EReal.coe_le_coe_iff.mpr
    change -(a⁻¹*A z)+(c - -(a⁻¹*A x)) ≤ _
    field_simp [ha.ne']
    linarith
  have htouch : f x = ((l x + (c-l x) : ℝ) : EReal) := by simpa using hcx.symm
  exact ⟨l, c-l x, ⟨hs, x, htouch⟩, htouch⟩

/-- An affine support of a proper positively homogeneous function has zero
intercept. Its minorant inequality can be tested at zero and at twice a
point of contact. -/
theorem IsAffineSupport.intercept_eq_zero {h : E → EReal} {l : E →L[ℝ] ℝ} {b : ℝ}
    (hs : IsAffineSupport h l b) (hh : PositivelyHomogeneous h) (hp : IsProper h) : b = 0 := by
  have h0 := hh.zero_eq_zero_or_bot.resolve_right (hp.2 0).ne'
  have hb := hs.1 0
  rw [h0, map_zero, zero_add, ← EReal.coe_zero] at hb
  obtain ⟨y, hy⟩ := hs.2
  have h2 := hs.1 ((2 : ℝ) • y)
  rw [hh.2 (show (0:ℝ) < 2 by norm_num), hy, ← EReal.coe_mul, map_smul, smul_eq_mul] at h2
  linarith [EReal.coe_le_coe_iff.mp hb, EReal.coe_le_coe_iff.mp h2]

/-- **Theorem 8.13**, homogeneous case. Every proper lower semicontinuous
sublinear function is the supremum of its continuous linear minorants. -/
theorem eq_iSup_linearMinorants [FiniteDimensional ℝ E] {h : E → EReal} (hs : Sublinear h)
    (hl : LowerSemicontinuous h) (hp : IsProper h) (x : E) :
    h x = ⨆ l : {l : E →L[ℝ] ℝ // ∀ y, (l y : EReal) ≤ h y}, (l.val x : EReal) := by
  apply le_antisymm _ (iSup_le fun l ↦ l.property x)
  rw [eq_iSup_affineSupports (convex_epigraph_of_sublinear hs) hl hp x]
  apply iSup_le
  rintro ⟨⟨l, b⟩, hsup⟩
  obtain rfl := hsup.intercept_eq_zero hs.1 hp
  let L : {l : E →L[ℝ] ℝ // ∀ y, (l y : EReal) ≤ h y} := ⟨l, by simpa using hsup.1⟩
  simpa [L] using (le_iSup (fun l : {l : E →L[ℝ] ℝ // ∀ y, (l y : EReal) ≤ h y} ↦
    (l.val x : EReal)) L)

/-- **Theorem 8.13**, converse and family formulation. A nonempty supremum
of affine functions defines a proper closed convex function exactly when it
has a point of finite cost. -/
theorem proper_closed_convex_iff_iSup_affine [FiniteDimensional ℝ E] (f : E → EReal) :
    IsProper f ∧ LowerSemicontinuous f ∧ Convex ℝ (epigraph f) ↔
    (∃ x, f x < ⊤) ∧ ∃ A : Set ((E →L[ℝ] ℝ) × ℝ), A.Nonempty ∧
      ∀ x, f x = ⨆ p : A, ((p.val.1 x + p.val.2 : ℝ) : EReal) := by
  constructor
  · rintro ⟨hp, hl, hc⟩
    let A := {p : (E →L[ℝ] ℝ) × ℝ | IsAffineSupport f p.1 p.2}
    obtain ⟨a, _, ha⟩ := EReal.exists_between_coe_real (hp.2 0)
    obtain ⟨l, b, hs, _⟩ := exists_affineSupport_gt_of_lt hc hl hp ha
    exact ⟨hp.1, A, ⟨(l,b),hs⟩, eq_iSup_affineSupports hc hl hp⟩
  · rintro ⟨hdom, A, ⟨p, hp⟩, hrep⟩
    have heq := funext hrep
    have hpiece (q : A) := isConvexPiecewiseLinear_affine q.val.1.toLinearMap q.val.2
    refine ⟨⟨hdom, fun x ↦ ?_⟩, ?_, ?_⟩
    · rw [hrep]
      exact (EReal.bot_lt_coe _).trans_le (le_iSup (fun q : A ↦
        ((q.val.1 x + q.val.2 : ℝ) : EReal)) ⟨p,hp⟩)
    · rw [heq]
      exact lowerSemicontinuous_iSup fun q ↦ (hpiece q).lowerSemicontinuous
    · rw [heq]
      exact convex_epigraph_iSup fun q ↦ (hpiece q).convex_epigraph

/-- A nonempty supremum of linear functionals is proper, lower
semicontinuous, and sublinear, including when it takes infinite values. -/
theorem iSup_linear_proper_lsc_sublinear {ι : Type*} [Nonempty ι] (L : ι → E →L[ℝ] ℝ) :
    let h := fun x ↦ ⨆ i, ((L i x : ℝ) : EReal)
    IsProper h ∧ LowerSemicontinuous h ∧ Sublinear h := by
  let F := fun i (x : E) ↦ (L i x : EReal)
  refine ⟨⟨⟨0, ?_⟩, fun x ↦ ?_⟩, ?_, ?_⟩
  · change (⨆ i, ((L i 0 : ℝ) : EReal)) < ⊤
    simp
  · exact (EReal.bot_lt_coe _).trans_le (le_iSup (fun i ↦ F i x) (Classical.arbitrary ι))
  · exact lowerSemicontinuous_iSup fun i ↦
      (continuous_coe_real_ereal.comp (L i).continuous).lowerSemicontinuous
  · apply Sublinear.iSup (h := F)
    intro i
    refine ⟨⟨by simp [F], fun {x c} _ ↦ ?_⟩, fun x y ↦ ?_⟩
    · simp [F, map_smul, smul_eq_mul, EReal.coe_mul]
    · simp [F, map_add, EReal.coe_add]

end RW
