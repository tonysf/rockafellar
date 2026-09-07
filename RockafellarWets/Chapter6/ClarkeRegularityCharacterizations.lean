/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangent-Normal Polarity and Clarke Regularity

Theorem 6.28(a) and the characterizations of Corollary 6.29 that follow from
it.

6.28(a) merely restates formula 6(6) in polar form: `N̂_C(x̄) = T_C(x̄)*`.  The
conditions of 6.29 then fall into two groups, each of which is available
without the second polarity relation 6.28(b):

* the *normal* group -- 6.29(a), (c), (e), (f) -- turning on `N̂_C = T_C*`
  and on the limit formula 6(7) `N_C = lim sup N̂_C`;
* the *tangent* group -- 6.29(b), (g) -- turning on the limit formula 6(16)
  `T̂_C = lim inf T_C`.

What is *not* available here is the link between the two groups, and with it
6.29(d); the book supplies it by the second polarity relation 6.28(b),
`T̂_C(x̄) = N_C(x̄)*`, whose proof runs through 6.27(b) and 6.18(b).
-/

import RockafellarWets.Chapter6.Polarity
import RockafellarWets.Chapter6.RegularTangents

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

section NormalGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Corollary 6.29**, the equivalence of (a) with (f): all normal vectors at
`x̄` are regular exactly when the regular normal cone mapping is outer
semicontinuous at `x̄` relative to `C`.  This is the limit formula 6(7) and
nothing else, so it needs no hypothesis beyond `x̄ ∈ C`. -/
theorem normalCone_eq_regularNormalCone_iff_svOscWithinAt {C : Set E} {x : E}
    (hx : x ∈ C) :
    normalCone C x = regularNormalCone C x ↔
      SvOscWithinAt (regularNormalCone C) C x := by
  have h := normalCone_eq_svOuterLimitWithin hx
  constructor
  · intro heq
    have hsub : svOuterLimitWithin (regularNormalCone C) C x
        ⊆ regularNormalCone C x := by rw [← h, heq]
    exact hsub
  · intro hosc
    refine Subset.antisymm ?_ (regularNormalCone_subset_normalCone C x)
    rw [h]
    exact hosc

end NormalGroup

section Polarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Theorem 6.28(a)**: the regular normal cone is the polar of the tangent
cone.  This merely restates formula 6(6). -/
theorem regularNormalCone_eq_polarCone_tangentCone {C : Set E} {x : E} (hx : x ∈ C) :
    regularNormalCone C x = polarCone (tangentCone C x) := by
  ext v
  rw [mem_regularNormalCone_iff_inner_nonpos hx, mem_polarCone]

/-- **Corollary 6.29**, the equivalence of (a) with (c). -/
theorem normalCone_eq_regularNormalCone_iff_eq_polarCone {C : Set E} {x : E}
    (hx : x ∈ C) :
    normalCone C x = regularNormalCone C x ↔
      normalCone C x = polarCone (tangentCone C x) := by
  rw [regularNormalCone_eq_polarCone_tangentCone hx]

/-- **Corollary 6.29**, the equivalence of (a) with (e): regularity is the
nonpositivity of every pairing of a normal vector with a tangent vector. -/
theorem normalCone_eq_regularNormalCone_iff_inner_nonpos {C : Set E} {x : E}
    (hx : x ∈ C) :
    normalCone C x = regularNormalCone C x ↔
      ∀ v ∈ normalCone C x, ∀ w ∈ tangentCone C x, ⟪v, w⟫_ℝ ≤ 0 := by
  constructor
  · intro heq v hv w hw
    rw [heq] at hv
    exact inner_nonpos_of_mem_regularNormalCone hv hw
  · intro hpair
    refine Subset.antisymm (fun v hv ↦ ?_) (regularNormalCone_subset_normalCone C x)
    rw [regularNormalCone_eq_polarCone_tangentCone hx, mem_polarCone]
    exact hpair v hv

/-- **Corollary 6.29**, the equivalence of (b) with (g): all tangent vectors at
`x̄` are regular exactly when the tangent cone mapping is inner semicontinuous
at `x̄` relative to `C`.  This is the limit formula 6(16). -/
theorem tangentCone_eq_regularTangentCone_iff_svIscWithinAt {C : Set E} {x : E}
    (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    tangentCone C x = regularTangentCone C x ↔
      SvIscWithinAt (tangentCone C) C x := by
  have h := regularTangentCone_eq_svInnerLimitWithin_tangentCone hx hlc
  constructor
  · intro heq
    have hsub : tangentCone C x ⊆ svInnerLimitWithin (tangentCone C) C x := by
      rw [heq, h]
    exact hsub
  · intro hisc
    refine Subset.antisymm ?_ (regularTangentCone_subset_tangentCone hx)
    rw [h]
    exact hisc

/-- **Corollary 6.29** in the form the book states it: at a locally closed
point, Clarke regularity is condition (c). -/
theorem isClarkeRegularAt_iff_normalCone_eq_polarCone {C : Set E} {x : E}
    (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔ normalCone C x = polarCone (tangentCone C x) := by
  rw [IsClarkeRegularAt, normalCone_eq_regularNormalCone_iff_eq_polarCone hx]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hlc, h⟩⟩

/-- **Corollary 6.29** in the form the book states it: at a locally closed
point, Clarke regularity is condition (e). -/
theorem isClarkeRegularAt_iff_inner_nonpos {C : Set E} {x : E} (hx : x ∈ C)
    (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔
      ∀ v ∈ normalCone C x, ∀ w ∈ tangentCone C x, ⟪v, w⟫_ℝ ≤ 0 := by
  rw [IsClarkeRegularAt, normalCone_eq_regularNormalCone_iff_inner_nonpos hx]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hlc, h⟩⟩

omit [FiniteDimensional ℝ E] in
/-- **Corollary 6.29** in the form the book states it: at a locally closed
point, Clarke regularity is condition (f). -/
theorem isClarkeRegularAt_iff_svOscWithinAt {C : Set E} {x : E} (hx : x ∈ C)
    (hlc : IsLocallyClosedAt C x) :
    IsClarkeRegularAt C x ↔ SvOscWithinAt (regularNormalCone C) C x := by
  rw [IsClarkeRegularAt, normalCone_eq_regularNormalCone_iff_svOscWithinAt hx]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hlc, h⟩⟩

/-- **Corollary 6.30**, the normal half: at a point of Clarke regularity the
normal cone is the polar of the tangent cone, hence convex. -/
theorem IsClarkeRegularAt.normalCone_eq_polarCone {C : Set E} {x : E} (hx : x ∈ C)
    (h : IsClarkeRegularAt C x) : normalCone C x = polarCone (tangentCone C x) := by
  rw [h.2]
  exact regularNormalCone_eq_polarCone_tangentCone hx

/-- **Corollary 6.30**, the normal half: the normal cone at a point of Clarke
regularity is convex. -/
theorem IsClarkeRegularAt.convex_normalCone {C : Set E} {x : E} (hx : x ∈ C)
    (h : IsClarkeRegularAt C x) : Convex ℝ (normalCone C x) := by
  rw [h.normalCone_eq_polarCone hx]
  exact convex_polarCone _

/-- **Theorem 6.28(b)**, the inclusion `⊆`: a regular tangent vector pairs
nonpositively with every normal vector.  This half needs only the limit
formula 6(16) of 6.26 and the polarity 6.28(a) at the *nearby* points: a
normal vector at `x̄` is a limit of regular normals `vν` at points `xν`, and
6(16) supplies tangent vectors `wν ∈ T_C(xν)` converging to `w`, so each
pairing `⟪vν, wν⟫` is nonpositive and the limit is too. -/
theorem regularTangentCone_subset_polarCone_normalCone {C : Set E} {x : E}
    (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    regularTangentCone C x ⊆ polarCone (normalCone C x) := by
  intro w hw v hv
  obtain ⟨-, xs, vs, hxC, hxto, hvs, hvto⟩ := hv
  obtain ⟨ws, hws, hwsto⟩ :=
    (mem_regularTangentCone_iff_forall_tangent_sequences hx hlc).1 hw xs hxC hxto
  have hle : ∀ n, ⟪ws n, vs n⟫_ℝ ≤ 0 := by
    intro n
    have h := inner_nonpos_of_mem_regularNormalCone (hvs n) (hws n)
    rwa [real_inner_comm] at h
  exact le_of_tendsto (hwsto.inner hvto) (Eventually.of_forall hle)

/-- **Corollary 6.29**, the implication (b) ⟹ (a): if every tangent vector at
`x̄` is regular then every normal vector there is regular.  This is the one
direction between 6.29's two groups that the easy half of 6.28(b) supplies. -/
theorem normalCone_eq_regularNormalCone_of_tangentCone_eq {C : Set E} {x : E}
    (hx : x ∈ C) (hlc : IsLocallyClosedAt C x)
    (h : tangentCone C x = regularTangentCone C x) :
    normalCone C x = regularNormalCone C x := by
  rw [normalCone_eq_regularNormalCone_iff_inner_nonpos hx]
  intro v hv w hw
  rw [h] at hw
  have hpair := regularTangentCone_subset_polarCone_normalCone hx hlc hw v hv
  rwa [real_inner_comm] at hpair

/-- **Corollary 6.29**, the implication (b) ⟹ Clarke regularity. -/
theorem isClarkeRegularAt_of_tangentCone_eq {C : Set E} {x : E} (hx : x ∈ C)
    (hlc : IsLocallyClosedAt C x) (h : tangentCone C x = regularTangentCone C x) :
    IsClarkeRegularAt C x :=
  ⟨hlc, normalCone_eq_regularNormalCone_of_tangentCone_eq hx hlc h⟩

end Polarity

end RW
