/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: support and convex-hull representations of Clarke subgradients

The remaining clauses of Theorem 8.49, for `f` locally lsc and finite at `x̄`:

* `d̂f(x̄)(w) = sup {⟪v, w⟫ | v ∈ ∂̄f(x̄)}` once `∂̄f(x̄) ≠ ∅`;
* `∂̄^∞f(x̄)` is pointed if and only if `∂^∞f(x̄)` is pointed;
* in that case `∂̄f(x̄) = con ∂f(x̄) + con ∂^∞f(x̄)` and
  `∂̄^∞f(x̄) = con ∂^∞f(x̄)`.

Pointedness of `∂^∞f(x̄)` makes the normal cone `N` to the epigraph pointed
(by 8.9 its horizontal slice is `∂^∞f(x̄)`, and vertical components are
nonpositive), so `con N` is already closed by 3.15 and `N̄ = con N`.  A convex
combination of normals then splits according to the sign of the vertical
components.
-/

import RockafellarWets.Chapter8.ClarkeSubgradientRelations
import RockafellarWets.Chapter8.SupportCorrespondence
import RockafellarWets.Chapter8.HorizontalEpigraphNormals
import RockafellarWets.Chapter3.PointedCones

open Filter Set Topology Metric
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 8.49**: if `∂̄f(x̄) ≠ ∅`, then
`d̂f(x̄)(w) = sup {⟪v, w⟫ | v ∈ ∂̄f(x̄)}` for all `w`. -/
theorem regularSubderivative_eq_supportFunction_clarkeSubdifferential {f : E → EReal} {x : E}
    {c : ℝ} (hxc : f x = c) (hlsc : IsLocallyLscAt f x)
    (hne : (clarkeSubdifferential f x).Nonempty) :
    regularSubderivative f x = supportFunction (clarkeSubdifferential f x) := by
  have hS : clarkeSubdifferential f x = linearMinorantSet (regularSubderivative f x) :=
    clarkeSubdifferential_eq_setOf_inner_le_regularSubderivative hxc hlsc
  obtain ⟨v, hv⟩ := hne
  rw [hS] at hv ⊢
  have hph := positivelyHomogeneous_regularSubderivative hxc
  have hbot : ∀ w, ⊥ < regularSubderivative f x w := fun w ↦
    lt_of_lt_of_le (EReal.bot_lt_coe _) (hv w)
  have hp : IsProper (regularSubderivative f x) := ⟨⟨0, hph.1⟩, hbot⟩
  have hs : Sublinear (regularSubderivative f x) := ⟨hph, fun u w ↦ by
    have h1 := regularSubderivative_subadditive hxc hlsc.lowerSemicontinuousAt u w
    rwa [infAddition_eq_add_of_ne_bot (hbot u).ne' (hbot w).ne'] at h1⟩
  exact (supportFunction_linearMinorantSet hs (lowerSemicontinuous_regularSubderivative f x)
    hp).symm

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem withLp_eq_zero {q : WithLp 2 (E × ℝ)} (h1 : q.fst = 0) (h2 : q.snd = 0) :
    q = 0 := by
  have e : q = WithLp.toLp 2 (q.fst, q.snd) := rfl
  rw [e, h1, h2]
  rfl

omit [FiniteDimensional ℝ E] in
private theorem withLp_smul_eq (r : ℝ) (q : WithLp 2 (E × ℝ)) :
    r • q = WithLp.toLp 2 (r • q.fst, r * q.snd) := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem mem_euclideanEpigraph_of_eq {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c) :
    WithLp.toLp 2 (x, c) ∈ euclideanEpigraph f := by
  show f x ≤ (c : EReal)
  rw [hxc]

/-- `0 ∈ ∂^∞f(x̄)` at a locally lsc finite point. -/
theorem zero_mem_horizonSubdifferential_of_locallyLsc {f : E → EReal} {x : E} {c : ℝ}
    (hxc : f x = c) (hlsc : IsLocallyLscAt f x) : (0 : E) ∈ horizonSubdifferential f x :=
  (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hlsc hxc).2
    (isCone_normalCone (mem_euclideanEpigraph_of_eq hxc)).1

/-- With 8.9, the normal cone to `epi f` at `(x̄, f x̄)` is pointed when `∂^∞f(x̄)` is. -/
theorem isPointed_normalCone_epigraph {f : E → EReal} {x : E} {c : ℝ} (hxc : f x = c)
    (hlsc : IsLocallyLscAt f x) (hp : IsPointed (horizonSubdifferential f x)) :
    IsPointed (normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))) := by
  intro n z hz hsum i
  have hβ : ∀ j, (z j).snd ≤ 0 := fun j ↦ vertical_nonpos_of_mem_normalCone_epigraph
    (show WithLp.toLp 2 ((z j).fst, (z j).snd) ∈
      normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) from hz j)
  have hsnd : ∑ j, (z j).snd = 0 := by
    rw [← show (∑ j, z j).snd = ∑ j, (z j).snd from
      map_sum (WithLp.sndₗ 2 ℝ E ℝ) z Finset.univ, hsum]
    rfl
  have hβ0 : ∀ j, (z j).snd = 0 := fun j ↦
    (Finset.sum_eq_zero_iff_of_nonpos fun j _ ↦ hβ j).1 hsnd j (Finset.mem_univ j)
  have hmem : ∀ j, (z j).fst ∈ horizonSubdifferential f x := fun j ↦ by
    refine (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hlsc hxc).2 ?_
    have e : z j = WithLp.toLp 2 ((z j).fst, (0 : ℝ)) :=
      (show z j = WithLp.toLp 2 ((z j).fst, (z j).snd) from rfl).trans
        (by rw [hβ0 j])
    rw [← e]
    exact hz j
  have hfst : ∑ j, (z j).fst = 0 := by
    rw [← show (∑ j, z j).fst = ∑ j, (z j).fst from
      map_sum (WithLp.fstₗ 2 ℝ E ℝ) z Finset.univ, hsum]
    rfl
  exact withLp_eq_zero (hp n (fun j ↦ (z j).fst) hmem hfst i) (hβ0 i)

/-- With `∂^∞f(x̄)` pointed, `N̄ = con N` for the normal cone `N` to `epi f`
(3.15). -/
theorem convexifiedNormalCone_epigraph_eq_convexHull {f : E → EReal} {x : E} {c : ℝ}
    (hxc : f x = c) (hlsc : IsLocallyLscAt f x) (hp : IsPointed (horizonSubdifferential f x)) :
    convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) =
      convexHull ℝ (normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))) :=
  (isClosed_convexHull_of_isClosed_isPointed (isClosed_normalCone _ _)
    (isCone_normalCone (mem_euclideanEpigraph_of_eq hxc))
    (isPointed_normalCone_epigraph hxc hlsc hp)).closure_eq

/-- **Theorem 8.49**: the cone `∂̄^∞f(x̄)` is pointed if and only if `∂^∞f(x̄)`
is pointed. -/
theorem isPointed_clarkeHorizonSubdifferential_iff {f : E → EReal} {x : E} {c : ℝ}
    (hxc : f x = c) (hlsc : IsLocallyLscAt f x) :
    IsPointed (clarkeHorizonSubdifferential f x) ↔ IsPointed (horizonSubdifferential f x) := by
  refine ⟨fun hp ↦ hp.mono (horizonSubdifferential_subset_clarkeHorizonSubdifferential hxc),
    fun hp ↦ ?_⟩
  have hNp : IsPointed (convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))) := by
    rw [convexifiedNormalCone_epigraph_eq_convexHull hxc hlsc hp]
    exact isPointed_convexHull (isCone_normalCone (mem_euclideanEpigraph_of_eq hxc))
      (isPointed_normalCone_epigraph hxc hlsc hp)
  intro n u hu hsum i
  have hmem : ∀ j, WithLp.toLp 2 (u j, (0 : ℝ)) ∈
      convexifiedNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) := fun j ↦ by
    have h1 := hu j
    rw [clarkeHorizonSubdifferential_of_finite hxc] at h1
    exact h1
  have hsum' : ∑ j, WithLp.toLp 2 (u j, (0 : ℝ)) = 0 := by
    refine withLp_eq_zero ?_ ?_
    · rw [show (∑ j, WithLp.toLp 2 (u j, (0 : ℝ))).fst = ∑ j, u j from
        map_sum (WithLp.fstₗ 2 ℝ E ℝ) (fun j ↦ WithLp.toLp 2 (u j, (0 : ℝ))) Finset.univ]
      exact hsum
    · rw [show (∑ j, WithLp.toLp 2 (u j, (0 : ℝ))).snd = ∑ _j : Fin n, (0 : ℝ) from
        map_sum (WithLp.sndₗ 2 ℝ E ℝ) (fun j ↦ WithLp.toLp 2 (u j, (0 : ℝ))) Finset.univ]
      simp
  have h1 := congrArg WithLp.fst (hNp n _ hmem hsum' i)
  simpa using h1

/-- **Theorem 8.49**: when `∂^∞f(x̄)` is pointed, `∂̄^∞f(x̄) = con ∂^∞f(x̄)`. -/
theorem clarkeHorizonSubdifferential_eq_convexHull {f : E → EReal} {x : E} {c : ℝ}
    (hxc : f x = c) (hlsc : IsLocallyLscAt f x) (hp : IsPointed (horizonSubdifferential f x)) :
    clarkeHorizonSubdifferential f x = convexHull ℝ (horizonSubdifferential f x) := by
  refine Subset.antisymm (fun u hu ↦ ?_)
    (convexHull_min (horizonSubdifferential_subset_clarkeHorizonSubdifferential hxc)
      (convex_clarkeHorizonSubdifferential hxc))
  rw [clarkeHorizonSubdifferential_of_finite hxc] at hu
  have hu' : WithLp.toLp 2 (u, (0 : ℝ)) ∈
      convexHull ℝ (normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))) := by
    rw [← convexifiedNormalCone_epigraph_eq_convexHull hxc hlsc hp]
    exact hu
  obtain ⟨ι, _, t, z, ht0, ht1, hzN, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hu'
  have hβ : ∀ i, (z i).snd ≤ 0 := fun i ↦ vertical_nonpos_of_mem_normalCone_epigraph
    (show WithLp.toLp 2 ((z i).fst, (z i).snd) ∈
      normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) from hzN i)
  have hsnd : ∑ i, t i * (z i).snd = 0 := by
    have h1 := congrArg WithLp.snd hsum
    rw [show (∑ i, t i • z i).snd = ∑ i, t i * (z i).snd from
      map_sum (WithLp.sndₗ 2 ℝ E ℝ) (fun i ↦ t i • z i) Finset.univ] at h1
    simpa using h1
  have hzero : ∀ i, t i * (z i).snd = 0 := fun i ↦
    (Finset.sum_eq_zero_iff_of_nonpos fun i _ ↦
      mul_nonpos_of_nonneg_of_nonpos (ht0 i) (hβ i)).1 hsnd i (Finset.mem_univ i)
  obtain ⟨h', hh'⟩ : ∃ h' : ι → E, ∀ i, h' i = if (z i).snd = 0 then (z i).fst else 0 :=
    ⟨_, fun i ↦ rfl⟩
  have hh'mem : ∀ i, h' i ∈ horizonSubdifferential f x := fun i ↦ by
    rw [hh']
    by_cases hi : (z i).snd = 0
    · rw [if_pos hi]
      refine (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hlsc hxc).2 ?_
      have e : z i = WithLp.toLp 2 ((z i).fst, (0 : ℝ)) :=
        (show z i = WithLp.toLp 2 ((z i).fst, (z i).snd) from rfl).trans
          (by rw [hi])
      rw [← e]
      exact hzN i
    · rw [if_neg hi]
      exact zero_mem_horizonSubdifferential_of_locallyLsc hxc hlsc
  have hfst : ∑ i, t i • h' i = u := by
    have h1 := congrArg WithLp.fst hsum
    rw [show (∑ i, t i • z i).fst = ∑ i, t i • (z i).fst from
      map_sum (WithLp.fstₗ 2 ℝ E ℝ) (fun i ↦ t i • z i) Finset.univ] at h1
    simp only [WithLp.toLp_fst] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hh']
    by_cases hi : (z i).snd = 0
    · rw [if_pos hi]
    · have hti : t i = 0 := (mul_eq_zero.1 (hzero i)).resolve_right hi
      rw [if_neg hi, hti, zero_smul, zero_smul]
  rw [← hfst]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ ↦ ht0 i) ht1
    fun i _ ↦ subset_convexHull ℝ _ (hh'mem i)

/-- **Theorem 8.49**: when `∂^∞f(x̄)` is pointed,
`∂̄f(x̄) = con ∂f(x̄) + con ∂^∞f(x̄)`. -/
theorem clarkeSubdifferential_eq_convexHull_add {f : E → EReal} {x : E} {c : ℝ}
    (hxc : f x = c) (hlsc : IsLocallyLscAt f x) (hp : IsPointed (horizonSubdifferential f x)) :
    clarkeSubdifferential f x =
      convexHull ℝ (subdifferential f x) + convexHull ℝ (horizonSubdifferential f x) := by
  apply Subset.antisymm
  · intro v hv
    obtain ⟨g₀, hg₀⟩ := (clarkeSubdifferential_nonempty_iff hxc).1 ⟨v, hv⟩
    rw [clarkeSubdifferential_of_finite hxc] at hv
    have hv' : WithLp.toLp 2 (v, (-1 : ℝ)) ∈
        convexHull ℝ (normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c))) := by
      rw [← convexifiedNormalCone_epigraph_eq_convexHull hxc hlsc hp]
      exact hv
    obtain ⟨ι, _, t, z, ht0, ht1, hzN, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hv'
    have hβ : ∀ i, (z i).snd ≤ 0 := fun i ↦ vertical_nonpos_of_mem_normalCone_epigraph
      (show WithLp.toLp 2 ((z i).fst, (z i).snd) ∈
        normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x, c)) from hzN i)
    have hsnd : ∑ i, t i * (z i).snd = -1 := by
      have h1 := congrArg WithLp.snd hsum
      rw [show (∑ i, t i • z i).snd = ∑ i, t i * (z i).snd from
        map_sum (WithLp.sndₗ 2 ℝ E ℝ) (fun i ↦ t i • z i) Finset.univ] at h1
      simpa using h1
    have hfst : ∑ i, t i • (z i).fst = v := by
      have h1 := congrArg WithLp.fst hsum
      rw [show (∑ i, t i • z i).fst = ∑ i, t i • (z i).fst from
        map_sum (WithLp.fstₗ 2 ℝ E ℝ) (fun i ↦ t i • z i) Finset.univ] at h1
      simpa using h1
    obtain ⟨s, hs⟩ : ∃ s : ι → ℝ, ∀ i, s i = t i * -(z i).snd := ⟨_, fun i ↦ rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : ι → E,
        ∀ i, g i = if (z i).snd < 0 then (-(z i).snd)⁻¹ • (z i).fst else g₀ :=
      ⟨_, fun i ↦ rfl⟩
    obtain ⟨h', hh'⟩ : ∃ h' : ι → E, ∀ i, h' i = if (z i).snd = 0 then (z i).fst else 0 :=
      ⟨_, fun i ↦ rfl⟩
    have hs0 : ∀ i, 0 ≤ s i := fun i ↦ by
      rw [hs]
      exact mul_nonneg (ht0 i) (neg_nonneg.2 (hβ i))
    have hs1 : ∑ i, s i = 1 := by
      simp only [hs, mul_neg, Finset.sum_neg_distrib, hsnd, neg_neg]
    have hgmem : ∀ i, g i ∈ subdifferential f x := fun i ↦ by
      rw [hg]
      by_cases hi : (z i).snd < 0
      · rw [if_pos hi]
        refine (mem_subdifferential_iff_epigraph_normal hxc).2 ?_
        have hpos : 0 < -(z i).snd := neg_pos.2 hi
        have hsc := (isCone_normalCone (mem_euclideanEpigraph_of_eq hxc)).2 (hzN i)
          (inv_pos.2 hpos)
        convert hsc using 1
        rw [withLp_smul_eq, inv_neg, neg_mul, inv_mul_cancel₀ hi.ne]
      · rw [if_neg hi]
        exact hg₀
    have hh'mem : ∀ i, h' i ∈ horizonSubdifferential f x := fun i ↦ by
      rw [hh']
      by_cases hi : (z i).snd = 0
      · rw [if_pos hi]
        refine (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hlsc hxc).2 ?_
        have e : z i = WithLp.toLp 2 ((z i).fst, (0 : ℝ)) :=
          (show z i = WithLp.toLp 2 ((z i).fst, (z i).snd) from rfl).trans
            (by rw [hi])
        rw [← e]
        exact hzN i
      · rw [if_neg hi]
        exact zero_mem_horizonSubdifferential_of_locallyLsc hxc hlsc
    have hdecomp : ∀ i, t i • (z i).fst = s i • g i + t i • h' i := fun i ↦ by
      rw [hs, hg, hh']
      rcases (hβ i).lt_or_eq with hi | hi
      · have hne : -(z i).snd ≠ 0 := (neg_pos.2 hi).ne'
        rw [if_pos hi, if_neg hi.ne, smul_zero, add_zero, smul_smul,
          mul_inv_cancel_right₀ hne]
      · rw [hi]
        simp
    refine Set.mem_add.2 ⟨∑ i, s i • g i, ?_, ∑ i, t i • h' i, ?_, ?_⟩
    · exact (convex_convexHull ℝ _).sum_mem (fun i _ ↦ hs0 i) hs1
        fun i _ ↦ subset_convexHull ℝ _ (hgmem i)
    · exact (convex_convexHull ℝ _).sum_mem (fun i _ ↦ ht0 i) ht1
        fun i _ ↦ subset_convexHull ℝ _ (hh'mem i)
    · rw [← Finset.sum_add_distrib, ← hfst]
      exact Finset.sum_congr rfl fun i _ ↦ (hdecomp i).symm
  · intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hv
    have haS : a ∈ clarkeSubdifferential f x :=
      convexHull_min (subdifferential_subset_clarkeSubdifferential hxc)
        (convex_clarkeSubdifferential hxc) ha
    have hbS : b ∈ clarkeHorizonSubdifferential f x :=
      convexHull_min (horizonSubdifferential_subset_clarkeHorizonSubdifferential hxc)
        (convex_clarkeHorizonSubdifferential hxc) hb
    rw [clarkeHorizonSubdifferential_eq_horizonCone hxc ⟨a, haS⟩] at hbS
    have h1 := smul_add_mem_of_mem_horizonCone (convex_clarkeSubdifferential hxc)
      (isClosed_clarkeSubdifferential hxc) haS hbS zero_le_one
    rwa [one_smul, add_comm] at h1

end RW
