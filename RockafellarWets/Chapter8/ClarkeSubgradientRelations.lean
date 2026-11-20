/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Clarke subgradients versus limiting subgradients

Further clauses of Theorem 8.49, at a point where `f` is finite:

* `∂f(x̄) ⊆ ∂̄f(x̄)` and `∂^∞f(x̄) ⊆ ∂̄^∞f(x̄)`;
* `∂̄f(x̄) ≠ ∅` if and only if `∂f(x̄) ≠ ∅`: when `∂f(x̄) = ∅` every normal to
  `epi f` at `(x̄, f(x̄))` is horizontal (8.9 and the cone property), and so is
  every element of the closed convex hull `N̄`;
* `∂̄^∞f(x̄) = ∂̄f(x̄)^∞` whenever `∂̄f(x̄) ≠ ∅`: horizontal elements of the
  closed convex cone `N̄` are exactly the recession directions of its slice at
  height `-1`.

The support-function formula for `d̂f(x̄)` and the convex-hull representations
in the pointed case are not formalized.
-/

import RockafellarWets.Chapter8.ClarkeSubgradients
import RockafellarWets.Chapter3.HorizonCones

open Filter Set Topology Metric
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 8.49**: limiting subgradients are Clarke subgradients. -/
theorem subdifferential_subset_clarkeSubdifferential {f : E → EReal} {x : E} {c : ℝ}
    (hxc : f x = c) : subdifferential f x ⊆ clarkeSubdifferential f x := fun _ hv ↦
  ⟨c, hxc, normalCone_subset_convexifiedNormalCone _ _
    ((mem_subdifferential_iff_epigraph_normal hxc).1 hv)⟩

/-- **Theorem 8.49**: horizon subgradients are Clarke horizon subgradients. -/
theorem horizonSubdifferential_subset_clarkeHorizonSubdifferential {f : E → EReal} {x : E}
    {c : ℝ} (hxc : f x = c) :
    horizonSubdifferential f x ⊆ clarkeHorizonSubdifferential f x := fun _ hv ↦
  ⟨c, hxc, normalCone_subset_convexifiedNormalCone _ _
    (horizontal_normal_of_mem_horizonSubdifferential hxc hv)⟩

/-- **Theorem 8.49**: `∂̄f(x̄) ≠ ∅` if and only if `∂f(x̄) ≠ ∅`. -/
theorem clarkeSubdifferential_nonempty_iff {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c) :
    (clarkeSubdifferential f x).Nonempty ↔ (subdifferential f x).Nonempty := by
  constructor
  · rintro ⟨v, hv⟩
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    have hz : WithLp.toLp 2 (x, c) ∈ euclideanEpigraph f := by
      show f x ≤ (c : EReal)
      rw [hxc]
    have hH : normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) ⊆
        {q : WithLp 2 (E × ℝ) | q.snd = 0} := by
      intro q hq
      obtain ⟨⟨u, β⟩, rfl⟩ : ∃ p : E × ℝ, WithLp.toLp 2 p = q := ⟨WithLp.ofLp q, by simp⟩
      have hβ : β ≤ 0 := vertical_nonpos_of_mem_normalCone_epigraph hq
      show β = 0
      by_contra hβ0
      have hβneg : β < 0 := lt_of_le_of_ne hβ hβ0
      have hscaled := (isCone_normalCone hz).2 hq (inv_pos.2 (neg_pos.2 hβneg))
      have heq : (-β)⁻¹ • WithLp.toLp 2 (u, β) = WithLp.toLp 2 ((-β)⁻¹ • u, (-1 : ℝ)) := by
        rw [← WithLp.toLp_smul, Prod.smul_mk, smul_eq_mul]
        congr 2
        have : β ≠ 0 := hβ0
        field_simp
      rw [heq] at hscaled
      have hsub := (mem_subdifferential_iff_epigraph_normal hxc).2 hscaled
      rw [hempty] at hsub
      exact hsub
    have hHconv : Convex ℝ {q : WithLp 2 (E × ℝ) | q.snd = 0} := by
      intro q₁ h₁ q₂ h₂ a b _ _ _
      have h₁' : q₁.snd = 0 := h₁
      have h₂' : q₂.snd = 0 := h₂
      show (a • q₁ + b • q₂).snd = 0
      simp [h₁', h₂']
    have hHclosed : IsClosed {q : WithLp 2 (E × ℝ) | q.snd = 0} :=
      isClosed_eq (WithLp.continuous_snd 2 E ℝ) continuous_const
    have hN : convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) ⊆
        {q : WithLp 2 (E × ℝ) | q.snd = 0} :=
      closure_minimal (convexHull_min hH hHconv) hHclosed
    rw [clarkeSubdifferential_of_finite hxc] at hv
    have h := hN hv
    have h' : (-1 : ℝ) = 0 := h
    norm_num at h'
  · rintro ⟨v, hv⟩
    exact ⟨v, subdifferential_subset_clarkeSubdifferential hxc hv⟩

/-- **Theorem 8.49**: `∂̄^∞f(x̄) = ∂̄f(x̄)^∞` as long as `∂̄f(x̄) ≠ ∅`. -/
theorem clarkeHorizonSubdifferential_eq_horizonCone {f : E → EReal} {x : E} {c : ℝ}
    (hxc : f x = c) (hne : (clarkeSubdifferential f x).Nonempty) :
    clarkeHorizonSubdifferential f x = horizonCone (clarkeSubdifferential f x) := by
  have hz : WithLp.toLp 2 (x, c) ∈ euclideanEpigraph f := by
    show f x ≤ (c : EReal)
    rw [hxc]
  have hSconv := convex_clarkeSubdifferential hxc
  have hSclosed := isClosed_clarkeSubdifferential hxc
  obtain ⟨v₀, hv₀⟩ := hne
  rw [clarkeSubdifferential_of_finite hxc] at hSconv hSclosed hv₀ ⊢
  rw [clarkeHorizonSubdifferential_of_finite hxc]
  have hNcone := isCone_convexifiedNormalCone hz
  have hNconv := convex_convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))
  have hNclosed := isClosed_convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))
  have hadd : ∀ p q, p ∈ convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) →
      q ∈ convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) →
      p + q ∈ convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) := by
    intro p q hp hq
    have h1 := hNconv hp hq (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    have h2 := hNcone.2 h1 (by norm_num : (0 : ℝ) < 2)
    convert h2 using 1
    rw [smul_add, smul_smul, smul_smul]
    norm_num
  ext u
  constructor
  · intro hu
    apply mem_horizonCone_of_forall_smul_add_mem (x := v₀)
    intro t ht
    show WithLp.toLp 2 (t • u + v₀, (-1 : ℝ)) ∈
      convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))
    rcases ht.eq_or_lt with rfl | htpos
    · simpa using hv₀
    · have := hadd _ _ hv₀ (hNcone.2 hu htpos)
      convert this using 1
      rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
      congr 1
      ext <;> simp [add_comm]
  · intro hu
    have hray : ∀ t : ℝ, 0 ≤ t → t • u + v₀ ∈
        (fun v : E ↦ WithLp.toLp 2 (v, (-1 : ℝ))) ⁻¹'
          convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) :=
      fun t ht ↦ smul_add_mem_of_mem_horizonCone hSconv hSclosed hv₀ hu ht
    have hseq : ∀ n : ℕ, ((n : ℝ) + 1)⁻¹ • WithLp.toLp 2 (((n : ℝ) + 1) • u + v₀, (-1 : ℝ)) ∈
        convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) :=
      fun n ↦ hNcone.2 (hray _ (by positivity)) (by positivity)
    have heq : ∀ n : ℕ, ((n : ℝ) + 1)⁻¹ • WithLp.toLp 2 (((n : ℝ) + 1) • u + v₀, (-1 : ℝ)) =
        WithLp.toLp 2 (u + ((n : ℝ) + 1)⁻¹ • v₀, -((n : ℝ) + 1)⁻¹) := by
      intro n
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      rw [← WithLp.toLp_smul, Prod.smul_mk, smul_add, smul_smul, inv_mul_cancel₀ hn, one_smul,
        smul_eq_mul, mul_neg_one]
    have h1 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h0
    have h2 : Tendsto (fun n : ℕ ↦ (u + ((n : ℝ) + 1)⁻¹ • v₀, -((n : ℝ) + 1)⁻¹)) atTop
        (𝓝 (u, (0 : ℝ))) := by
      have := (tendsto_const_nhds (x := u)).add (h1.smul_const v₀) |>.prodMk_nhds h1.neg
      simpa using this
    have hlim := ((WithLp.prod_continuous_toLp 2 E ℝ).tendsto _).comp h2
    exact hNclosed.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ by
      have := hseq n
      rw [heq n] at this
      exact this)

end RW
