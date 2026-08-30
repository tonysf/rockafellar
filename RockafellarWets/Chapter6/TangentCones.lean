/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Tangent Cones

Section A of Chapter 6 is Definition 6.1 and Proposition 6.2: the tangent
cone `T_C(x̄)`, the derivable tangent vectors inside it, and the reading of
both as limits of the magnified difference sets `τ⁻¹(C - x̄)` as `τ ↓ 0`.

Formula 6(3) is a Painleve--Kuratowski limit indexed by the *scaling
parameter* rather than by the argument, so the filter-native set limits built
for formula 5(1) in
[`SetLimitsAlong.lean`](RockafellarWets/Chapter5/SetLimitsAlong.lean) apply
with no change at all: the index filter is `𝓝[>] 0` on `ℝ`, and 6.2 is the
statement that Definition 6.1 computes `outerSetLimitAlong` of the family
`τ ↦ τ⁻¹(C - x̄)`, with the derivable vectors computing
`innerSetLimitAlong` of the same family.  Closedness of both cones is then
`isClosed_outerSetLimitAlong` and `isClosed_innerSetLimitAlong`, and the
concluding clause -- geometric derivability is convergence of the magnified
sets -- is the equality of the two limits.

Two things are worth naming in the proofs.

* Definition 6.1 prints `xν →_C x̄` alongside `[xν - x̄]/τν → w`, but the
  convergence of the `xν` is implied by the rest, the differences being `τν`
  times a convergent sequence; `mem_tangentCone_of_forall` is the resulting
  constructor, which does not ask for it.
* The hard half of 6.2 is that an inner-limit vector is *derivable*, since a
  path `ξ` has to be produced.  It is produced by choice, one point per `τ`,
  taken within `τ` of the best point of `τ⁻¹(C - x̄)` available -- the same
  slack device the pointwise selection remark before 5.57 uses.  What makes
  this legitimate is that Definition 6.1 asks no continuity of `ξ` anywhere
  but at `0`, so an arbitrary selection is admissible.

The hypothesis `x̄ ∈ C` is needed for the derivable half, and only there:
`ξ(0) = x̄` forces `x̄ ∈ C`, whereas the inner limit by itself puts `x̄` only
in `cl C`.  Formula 6(3) holds at every `x̄`, in or out of `C`.

The unnumbered example of Figure 6-4 -- the closed subset of `IR²` given by
`x₂ = x₁ sin(log x₁)`, whose tangent cone is a half-plane while its derivable
cone is `{0}` -- is not formalized.
-/

import RockafellarWets.Chapter5

open Filter Metric Set Topology

namespace RW

section TangentCones

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The magnified difference set `τ⁻¹(C - x̄)` of formula 6(3). -/
def blowUp (C : Set E) (x : E) (τ : ℝ) : Set E := (fun y ↦ τ⁻¹ • (y - x)) '' C

@[simp]
theorem mem_blowUp {C : Set E} {x : E} {τ : ℝ} {u : E} :
    u ∈ blowUp C x τ ↔ ∃ y ∈ C, τ⁻¹ • (y - x) = u := Iff.rfl

/-- **Definition 6.1**: `w` is tangent to `C` at `x̄`. -/
def tangentCone (C : Set E) (x : E) : Set E :=
  {w | ∃ (xs : ℕ → E) (τs : ℕ → ℝ), (∀ n, xs n ∈ C) ∧
    Tendsto xs atTop (nhds x) ∧ (∀ n, 0 < τs n) ∧ Tendsto τs atTop (nhds 0) ∧
    Tendsto (fun n ↦ (τs n)⁻¹ • (xs n - x)) atTop (nhds w)}

/-- The convergence `xν → x̄` printed in 6(2) is implied by the rest: the
differences are `τν` times a convergent sequence. -/
theorem mem_tangentCone_of_forall {C : Set E} {x w : E} {xs : ℕ → E} {τs : ℕ → ℝ}
    (hx : ∀ n, xs n ∈ C) (hτ : ∀ n, 0 < τs n) (hτ0 : Tendsto τs atTop (nhds 0))
    (hq : Tendsto (fun n ↦ (τs n)⁻¹ • (xs n - x)) atTop (nhds w)) :
    w ∈ tangentCone C x := by
  refine ⟨xs, τs, hx, ?_, hτ, hτ0, hq⟩
  have h : Tendsto (fun n ↦ τs n • ((τs n)⁻¹ • (xs n - x))) atTop (nhds ((0 : ℝ) • w)) :=
    hτ0.smul hq
  rw [zero_smul] at h
  have heq : ∀ n, τs n • ((τs n)⁻¹ • (xs n - x)) = xs n - x := fun n ↦ by
    rw [smul_smul, mul_inv_cancel₀ (hτ n).ne', one_smul]
  simp only [heq] at h
  have := h.const_add x
  simpa using this

/-- **Proposition 6.2**, formula 6(3): the tangent cone is the outer limit of
the magnified difference sets as `τ ↓ 0`. -/
theorem tangentCone_eq_outerSetLimitAlong (C : Set E) (x : E) :
    tangentCone C x = outerSetLimitAlong (nhdsWithin 0 (Ioi (0 : ℝ))) (blowUp C x) := by
  ext w
  constructor
  · rintro ⟨xs, τs, hxC, -, hτpos, hτ0, hq⟩ V hV
    have hτin : Tendsto τs atTop (nhdsWithin 0 (Ioi (0 : ℝ))) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ0
        (Eventually.of_forall fun n ↦ hτpos n)
    rw [Filter.frequently_iff]
    intro A hA
    have h1 : ∀ᶠ n in atTop, τs n ∈ A := hτin hA
    have h2 : ∀ᶠ n in atTop, (τs n)⁻¹ • (xs n - x) ∈ V := hq hV
    obtain ⟨n, hnA, hnV⟩ := (h1.and h2).exists
    exact ⟨τs n, hnA, (τs n)⁻¹ • (xs n - x), ⟨xs n, hxC n, rfl⟩, hnV⟩
  · intro hw
    have hpick : ∀ n : ℕ, ∃ τ : ℝ, ∃ y : E,
        (0 < τ ∧ τ < 1 / ((n : ℝ) + 1)) ∧ y ∈ C ∧
          dist (τ⁻¹ • (y - x)) w < 1 / ((n : ℝ) + 1) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨τ, hτA, u, ⟨y, hyC, hyu⟩, huV⟩ :=
        Filter.frequently_iff.1 (hw (ball w (1 / ((n : ℝ) + 1))) (ball_mem_nhds w hpos))
          (Ioo_mem_nhdsGT hpos)
      refine ⟨τ, y, ⟨hτA.1, hτA.2⟩, hyC, ?_⟩
      have hyu' : τ⁻¹ • (y - x) = u := hyu
      rw [hyu']
      exact mem_ball.1 huV
    choose τs xs hτA hxC hd using hpick
    have hτ0 : Tendsto τs atTop (nhds 0) :=
      squeeze_zero (fun n ↦ (hτA n).1.le) (fun n ↦ (hτA n).2.le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    refine mem_tangentCone_of_forall hxC (fun n ↦ (hτA n).1) hτ0 ?_
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Definition 6.1**: `w` is a *derivable* tangent vector to `C` at `x̄` when
some `ξ : [0, ε] → C` with `ξ(0) = x̄` has right derivative `w` at `0`.  No
continuity is asked of `ξ` anywhere but at `0`. -/
def derivableCone (C : Set E) (x : E) : Set E :=
  {w | ∃ ε > 0, ∃ ξ : ℝ → E, ξ 0 = x ∧ (∀ t ∈ Icc (0 : ℝ) ε, ξ t ∈ C) ∧
    Tendsto (fun t ↦ t⁻¹ • (ξ t - x)) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds w)}

/-- **Proposition 6.2**: the derivable tangent vectors are the corresponding
*inner* limit of the magnified difference sets.

Forward, the path itself exhibits a point of `τ⁻¹(C - x̄)` near `w` for every
small `τ`.  Backward, a path is chosen: at each `τ` take a point of
`τ⁻¹(C - x̄)` within `τ` of the best available, so that the error is at most
`d(w, τ⁻¹(C - x̄)) + τ`, and both terms vanish.  Continuity of the path is
never needed, which is what makes the choice legitimate. -/
theorem derivableCone_eq_innerSetLimitAlong {C : Set E} {x : E} (hx : x ∈ C) :
    derivableCone C x = innerSetLimitAlong (nhdsWithin 0 (Ioi (0 : ℝ))) (blowUp C x) := by
  classical
  ext w
  constructor
  · rintro ⟨ε, hε, ξ, hξ0, hξC, hξt⟩ V hV
    have hsmall : ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)), t ∈ Ioo 0 ε :=
      Filter.eventually_of_mem (Ioo_mem_nhdsGT hε) fun _ ht ↦ ht
    filter_upwards [hξt hV, hsmall] with t htV htI
    exact ⟨t⁻¹ • (ξ t - x), ⟨ξ t, hξC t ⟨htI.1.le, htI.2.le⟩, rfl⟩, htV⟩
  · intro hw
    have hne : ∀ τ : ℝ, (blowUp C x τ).Nonempty := fun τ ↦ ⟨τ⁻¹ • (x - x), x, hx, rfl⟩
    have hchoice : ∀ τ : ℝ, ∃ y : E, y ∈ C ∧
        (0 < τ → dist (τ⁻¹ • (y - x)) w < Metric.infDist w (blowUp C x τ) + τ) := by
      intro τ
      by_cases hτ : 0 < τ
      · obtain ⟨u, ⟨y, hyC, hyu⟩, hu⟩ := (Metric.infDist_lt_iff (hne τ)).1
          (by linarith : Metric.infDist w (blowUp C x τ)
            < Metric.infDist w (blowUp C x τ) + τ)
        refine ⟨y, hyC, fun _ ↦ ?_⟩
        have hyu' : τ⁻¹ • (y - x) = u := hyu
        rw [hyu', dist_comm]
        exact hu
      · exact ⟨x, hx, fun h ↦ absurd h hτ⟩
    choose ξ hξC hξd using hchoice
    refine ⟨1, one_pos, fun t ↦ if t = 0 then x else ξ t, by simp, fun t _ ↦ ?_, ?_⟩
    · dsimp only
      by_cases h0 : t = 0
      · rw [if_pos h0]; exact hx
      · rw [if_neg h0]; exact hξC t
    · rw [Metric.tendsto_nhds]
      intro η hη
      have h1 : ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)),
          (blowUp C x t ∩ ball w (η / 2)).Nonempty :=
        hw (ball w (η / 2)) (ball_mem_nhds w (by linarith))
      have h2 : ∀ᶠ t in nhdsWithin 0 (Ioi (0 : ℝ)), t < η / 2 :=
        Filter.eventually_of_mem (Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < η / 2))
          fun _ ht ↦ ht.2
      filter_upwards [h1, h2, self_mem_nhdsWithin] with t ht1 ht2 ht3
      have htpos : (0 : ℝ) < t := ht3
      rw [if_neg htpos.ne']
      obtain ⟨u, huB, huV⟩ := ht1
      have hinf : Metric.infDist w (blowUp C x t) < η / 2 :=
        lt_of_le_of_lt (Metric.infDist_le_dist_of_mem huB)
          (by rw [dist_comm]; exact mem_ball.1 huV)
      exact lt_of_lt_of_le (hξd t htpos) (by linarith)

/-- **Proposition 6.2**: the tangent cone is closed. -/
theorem isClosed_tangentCone (C : Set E) (x : E) : IsClosed (tangentCone C x) := by
  rw [tangentCone_eq_outerSetLimitAlong]
  exact isClosed_outerSetLimitAlong _ _

/-- **Proposition 6.2**: the derivable cone is closed. -/
theorem isClosed_derivableCone {C : Set E} {x : E} (hx : x ∈ C) :
    IsClosed (derivableCone C x) := by
  rw [derivableCone_eq_innerSetLimitAlong hx]
  exact isClosed_innerSetLimitAlong _ _

/-- **Proposition 6.2**: the tangent cone is a cone.  The zero vector comes
from the constant sequence at `x̄`, and rescaling `w` by `c > 0` is rescaling
the step sizes `τν` by `1/c`. -/
theorem isCone_tangentCone {C : Set E} {x : E} (hx : x ∈ C) :
    IsCone (tangentCone C x) := by
  constructor
  · refine mem_tangentCone_of_forall (xs := fun _ ↦ x)
      (τs := fun n ↦ 1 / ((n : ℝ) + 1)) (fun _ ↦ hx) (fun n ↦ by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat ?_
    simp
  · rintro w ⟨xs, τs, hxC, -, hτpos, hτ0, hq⟩ c hc
    have hscale : ∀ n, (τs n / c)⁻¹ • (xs n - x) = c • ((τs n)⁻¹ • (xs n - x)) := by
      intro n
      rw [inv_div, div_eq_mul_inv, mul_smul]
    refine mem_tangentCone_of_forall hxC (τs := fun n ↦ τs n / c)
      (fun n ↦ div_pos (hτpos n) hc) ?_ ?_
    · simpa using hτ0.div_const c
    · simp only [hscale]
      exact hq.const_smul c

/-- **Proposition 6.2**: the derivable cone is a cone.  Rescaling `w` by
`c > 0` is reparameterizing the path by `t ↦ ct`. -/
theorem isCone_derivableCone {C : Set E} {x : E} (hx : x ∈ C) :
    IsCone (derivableCone C x) := by
  constructor
  · exact ⟨1, one_pos, fun _ ↦ x, rfl, fun _ _ ↦ hx, by simp⟩
  · rintro w ⟨ε, hε, ξ, hξ0, hξC, hξt⟩ c hc
    have hscale : ∀ t : ℝ, t⁻¹ • (ξ (c * t) - x)
        = c • ((c * t)⁻¹ • (ξ (c * t) - x)) := by
      intro t
      rw [mul_inv, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    have hmul : Tendsto (fun t : ℝ ↦ c * t) (nhdsWithin 0 (Ioi (0 : ℝ)))
        (nhdsWithin 0 (Ioi (0 : ℝ))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h : Tendsto (fun t : ℝ ↦ c * t) (nhds 0) (nhds (c * 0)) :=
          ((continuous_const (y := c)).mul continuous_id).tendsto 0
        rw [mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos hc ht
    refine ⟨ε / c, by positivity, fun t ↦ ξ (c * t), by simpa using hξ0,
      fun t ht ↦ hξC _ ⟨mul_nonneg hc.le ht.1, ?_⟩, ?_⟩
    · rw [← le_div_iff₀' hc]
      exact ht.2
    · simp only [hscale]
      exact (hξt.comp hmul).const_smul c

/-- **Proposition 6.2**: every derivable tangent vector is a tangent
vector. -/
theorem derivableCone_subset_tangentCone {C : Set E} {x : E} (hx : x ∈ C) :
    derivableCone C x ⊆ tangentCone C x := by
  rw [derivableCone_eq_innerSetLimitAlong hx, tangentCone_eq_outerSetLimitAlong]
  exact innerSetLimitAlong_subset_outerSetLimitAlong _

/-- **Definition 6.1**: `C` is *geometrically derivable* at `x̄` when every
tangent vector there is derivable. -/
def IsGeometricallyDerivable (C : Set E) (x : E) : Prop :=
  tangentCone C x ⊆ derivableCone C x

/-- **Proposition 6.2**, the concluding clause: geometric derivability is
exactly convergence of the magnified difference sets `[C - x̄]/τ` as `τ ↓ 0`,
so that formula 6(3) may then be read as a full limit. -/
theorem isGeometricallyDerivable_iff {C : Set E} {x : E} (hx : x ∈ C) :
    IsGeometricallyDerivable C x ↔
      outerSetLimitAlong (nhdsWithin 0 (Ioi (0 : ℝ))) (blowUp C x)
        = innerSetLimitAlong (nhdsWithin 0 (Ioi (0 : ℝ))) (blowUp C x) := by
  rw [IsGeometricallyDerivable, tangentCone_eq_outerSetLimitAlong,
    derivableCone_eq_innerSetLimitAlong hx]
  exact ⟨fun h ↦ Subset.antisymm h (innerSetLimitAlong_subset_outerSetLimitAlong _),
    fun h ↦ h.subset⟩

/-- At a point of geometric derivability the tangent cone *is* the derivable
cone. -/
theorem tangentCone_eq_derivableCone {C : Set E} {x : E} (hx : x ∈ C)
    (h : IsGeometricallyDerivable C x) : tangentCone C x = derivableCone C x :=
  Subset.antisymm h (derivableCone_subset_tangentCone hx)

end TangentCones

end RW
