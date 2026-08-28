/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Perturbed Mappings

Exercise 5.24 says that adding a continuous, locally bounded mapping `T` to a
mapping `S₀` preserves outer semicontinuity, inner semicontinuity and
continuity at a point.

The two halves consume different hypotheses, and are stated separately.
Inner semicontinuity of the sum follows from inner semicontinuity of the two
summands alone: local boundedness plays no part.  Outer semicontinuity is
where local boundedness of `T` is needed, and it does two jobs.  It makes
`T(x̄)` compact, so that `S₀(x̄) + T(x̄)` is closed -- the sum of two merely
closed sets need not be -- and it supplies the compact set on which the
extraction lemma of `SetLimitsAlong.lean` can act.

Both arguments go through the product mapping `x → S(x) × T(x)`, which keeps
the two summands apart; the sum is recovered at the end by adding the
coordinates.  Without it one would have to extract a limit of the second
summands and separately recover the first, which is the same work done twice.
-/

import RockafellarWets.Chapter5.LocallyBoundedContinuity

open scoped Pointwise
open Bornology Filter Metric Set Topology

namespace RW

section Products

variable {E F G : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
variable {S : E → Set F} {T : E → Set G} {x : E}

/-- The product mapping `x → S(x) × T(x)`. -/
def svProd (S : E → Set F) (T : E → Set G) : E → Set (F × G) := fun x ↦ S x ×ˢ T x

omit [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] in
@[simp]
theorem mem_svProd {p : F × G} : p ∈ svProd S T x ↔ p.1 ∈ S x ∧ p.2 ∈ T x := Iff.rfl

/-- The outer limit of a product mapping sits inside the product of the outer
limits: a neighborhood of one coordinate is a neighborhood of the pair once
the other coordinate is left free. -/
theorem svOuterLimit_svProd_subset (S : E → Set F) (T : E → Set G) (x : E) :
    svOuterLimit (svProd S T) x ⊆ svOuterLimit S x ×ˢ svOuterLimit T x := by
  rintro ⟨a, b⟩ hab
  constructor
  · intro W hW
    refine (hab (W ×ˢ univ) (prod_mem_nhds hW univ_mem)).mono ?_
    rintro y ⟨⟨a', _b'⟩, ⟨ha', _hb'⟩, hW', _hu'⟩
    exact ⟨a', ha', hW'⟩
  · intro W hW
    refine (hab (univ ×ˢ W) (prod_mem_nhds univ_mem hW)).mono ?_
    rintro y ⟨⟨_a', b'⟩, ⟨_ha', hb'⟩, _hu', hW'⟩
    exact ⟨b', hb', hW'⟩

/-- Outer semicontinuity is inherited by the product mapping. -/
theorem svOscAt_svProd (hS : SvOscAt S x) (hT : SvOscAt T x) :
    SvOscAt (svProd S T) x := fun _ hp ↦
  ⟨hS (svOuterLimit_svProd_subset S T x hp).1, hT (svOuterLimit_svProd_subset S T x hp).2⟩

/-- Inner semicontinuity is inherited by the product mapping. -/
theorem svIscAt_svProd (hS : SvIscAt S x) (hT : SvIscAt T x) :
    SvIscAt (svProd S T) x := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩ W hW
  rw [nhds_prod_eq] at hW
  obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := Filter.mem_prod_iff.1 hW
  filter_upwards [hS ha W₁ hW₁, hT hb W₂ hW₂] with y hy₁ hy₂
  obtain ⟨a', ha'S, ha'W⟩ := hy₁
  obtain ⟨b', hb'T, hb'W⟩ := hy₂
  exact ⟨(a', b'), ⟨ha'S, hb'T⟩, hsub ⟨ha'W, hb'W⟩⟩

end Products

section Constants

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- Both limits of a constant mapping are the closure of the constant value. -/
theorem svOuterLimit_const (C : Set F) (x : E) :
    svOuterLimit (fun _ : E ↦ C) x = closure C := by
  ext u
  simp only [svOuterLimit, mem_outerSetLimitAlong, frequently_const, mem_closure_iff_nhds]
  exact forall₂_congr fun W _ ↦ by rw [inter_comm]

theorem svInnerLimit_const (C : Set F) (x : E) :
    svInnerLimit (fun _ : E ↦ C) x = closure C := by
  ext u
  simp only [svInnerLimit, mem_innerSetLimitAlong, eventually_const, mem_closure_iff_nhds]
  exact forall₂_congr fun W _ ↦ by rw [inter_comm]

/-- A constant mapping is outer semicontinuous exactly when its value is
closed. -/
theorem svOscAt_const {C : Set F} (hC : IsClosed C) (x : E) :
    SvOscAt (fun _ : E ↦ C) x := by
  rw [SvOscAt, svOuterLimit_const, hC.closure_eq]

/-- A constant mapping is always inner semicontinuous. -/
theorem svIscAt_const (C : Set F) (x : E) : SvIscAt (fun _ : E ↦ C) x := by
  rw [SvIscAt, svInnerLimit_const]
  exact subset_closure

end Constants

section Sums

variable {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
variable {S T : E → Set F} {x : E}

/-- The pointwise sum `(S₀ + T)(x) = S₀(x) + T(x)` of 5.24. -/
def svAdd (S T : E → Set F) : E → Set F := fun x ↦ S x + T x

omit [TopologicalSpace E] in
@[simp]
theorem mem_svAdd {u : F} : u ∈ svAdd S T x ↔ ∃ a ∈ S x, ∃ b ∈ T x, a + b = u :=
  Set.mem_add

/-- **Exercise 5.24**, inner semicontinuity.  This half needs no local
boundedness: inner semicontinuity of both summands is enough. -/
theorem svIscAt_svAdd (hS : SvIscAt S x) (hT : SvIscAt T x) :
    SvIscAt (svAdd S T) x := by
  intro u hu W hW
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_svAdd.1 hu
  have hpre : (fun p : F × F ↦ p.1 + p.2) ⁻¹' W ∈ nhds ((a, b) : F × F) :=
    continuous_add.continuousAt hW
  filter_upwards [svIscAt_svProd hS hT ⟨ha, hb⟩ _ hpre] with y hy
  obtain ⟨⟨a', b'⟩, ⟨ha', hb'⟩, hmem⟩ := hy
  exact ⟨a' + b', mem_svAdd.2 ⟨a', ha', b', hb', rfl⟩, hmem⟩

variable [ProperSpace F]

/-- **Exercise 5.24**, outer semicontinuity.  Here local boundedness of `T` is
needed, and it is used twice: to make `T(x̄)` compact, so that `S₀(x̄) + T(x̄)`
is closed, and to confine the second summands to a ball, so that the pairs
`(a, b)` producing points near `ū` lie in a compact set to which the
extraction lemma applies. -/
theorem svOscAt_svAdd (hS : SvOscAt S x) (hT : SvOscAt T x)
    (hlb : SvLocallyBoundedAt T x) : SvOscAt (svAdd S T) x := by
  obtain ⟨V₀, hV₀, hbdd⟩ := hlb
  obtain ⟨ρ, hρsub⟩ := (isBounded_iff_subset_closedBall (0 : F)).1 hbdd
  have hTcompact : IsCompact (T x) :=
    isCompact_iff_isClosed_bounded.2
      ⟨hT.isClosed,
        isBounded_closedBall.subset ((subset_svImage (mem_of_mem_nhds hV₀)).trans hρsub)⟩
  have hcomm : svAdd S T x = T x + S x := add_comm (S x) (T x)
  have hclosed : IsClosed (svAdd S T x) := by
    rw [hcomm]
    exact hS.isClosed.add_left_of_isCompact hTcompact
  intro u hu
  rw [← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  set K : Set (F × F) :=
    {p : F × F | ‖p.2‖ ≤ ρ} ∩ {p : F × F | ‖p.1 + p.2 - u‖ ≤ ε / 2} with hKdef
  have hKcompact : IsCompact K := by
    refine isCompact_iff_isClosed_bounded.2
      ⟨(isClosed_le (by fun_prop) continuous_const).inter
        (isClosed_le (by fun_prop) continuous_const), ?_⟩
    refine IsBounded.subset
      ((isBounded_closedBall (x := (0 : F)) (r := ε / 2 + ‖u‖ + ρ)).prod
        (isBounded_closedBall (x := (0 : F)) (r := ρ))) ?_
    rintro ⟨a, b⟩ ⟨hb, hab⟩
    have hbn : ‖b‖ ≤ ρ := hb
    have habn : ‖a + b - u‖ ≤ ε / 2 := hab
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have e : ‖a‖ = ‖(a + b - u) + u - b‖ := by congr 1; abel
      rw [e]
      calc ‖(a + b - u) + u - b‖ ≤ ‖(a + b - u) + u‖ + ‖b‖ := norm_sub_le _ _
        _ ≤ ε / 2 + ‖u‖ + ρ := by linarith [norm_add_le (a + b - u) u]
    · rw [mem_closedBall, dist_zero_right]
      exact hbn
  have hfreq : ∃ᶠ y in nhds x, (svProd S T y ∩ K).Nonempty := by
    refine ((hu (ball u (ε / 2)) (ball_mem_nhds u (by positivity))).and_eventually
      (Filter.eventually_mem_set.2 hV₀)).mono ?_
    rintro y ⟨⟨w, hwS, hwball⟩, hyV₀⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_svAdd.1 hwS
    refine ⟨(a, b), ⟨ha, hb⟩, ?_, ?_⟩
    · simpa [mem_closedBall, dist_zero_right] using
        hρsub (mem_svImage.2 ⟨y, hyV₀, hb⟩)
    · exact le_of_lt (by simpa [dist_eq_norm] using mem_ball.1 hwball)
  obtain ⟨⟨a, b⟩, hablim, -, habu⟩ :=
    outerSetLimitAlong_inter_nonempty_of_frequently hKcompact hfreq
  obtain ⟨ha, hb⟩ := svOuterLimit_svProd_subset S T x hablim
  refine ⟨a + b, mem_svAdd.2 ⟨a, hS ha, b, hT hb, rfl⟩, ?_⟩
  have : ‖a + b - u‖ ≤ ε / 2 := habu
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  linarith

/-- **Exercise 5.24** as printed: at a point where `T` is continuous and
locally bounded, each of outer semicontinuity, inner semicontinuity and
continuity passes from `S₀` to `S₀ + T`. -/
theorem svContinuousAt_svAdd (hS : SvContinuousAt S x) (hT : SvContinuousAt T x)
    (hlb : SvLocallyBoundedAt T x) : SvContinuousAt (svAdd S T) x :=
  ⟨svOscAt_svAdd hS.1 hT.1 hlb, svIscAt_svAdd hS.2 hT.2⟩

/-- **Exercise 5.24**, the "in particular" case `S(x) = C + F(x)` for a closed
set `C` and a continuous single-valued `F`: such an `S` is continuous
everywhere. -/
theorem svContinuous_const_add {C : Set F} (hC : IsClosed C) {g : E → F}
    (hg : Continuous g) : SvContinuous (fun x ↦ C + ({g x} : Set F)) := fun x ↦
  svContinuousAt_svAdd (S := fun _ ↦ C) (T := svSingleton g)
    ⟨svOscAt_const hC x, svIscAt_const C x⟩
    (svContinuousAt_svSingleton_iff g x |>.2 hg.continuousAt)
    (svLocallyBoundedAt_svSingleton_of_continuousAt hg.continuousAt)

end Sums

end RW
