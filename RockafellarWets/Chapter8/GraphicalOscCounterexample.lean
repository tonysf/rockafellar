/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 8: Pointwise outer semicontinuity does not give the second coderivative inclusion
-/

import RockafellarWets.Chapter8.DerivativesOfDerivatives

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

/-- The graph is the open double cone `|u| < |x|` together with its vertex. -/
def openDoubleConeMapping (x : ℝ) : Set ℝ := {u | (x = 0 ∧ u = 0) ∨ |u| < |x|}

private abbrev Plane := WithLp 2 (ℝ × ℝ)
private abbrev wedge := euclideanSvGraph openDoubleConeMapping

private theorem wedge_le {p : Plane} (hp : p ∈ wedge) : |p.snd| ≤ |p.fst| := by
  rcases hp with h | h
  · rw [h.1, h.2]
  · exact h.le

private theorem wedge_cone : IsCone wedge := by
  refine ⟨Or.inl ⟨rfl,rfl⟩, ?_⟩
  rintro p (h | h) c hc
  · left
    change c * p.fst = 0 ∧ c * p.snd = 0
    simp [h.1, h.2]
  · right
    change |c * p.snd| < |c * p.fst|
    simpa only [abs_mul] using mul_lt_mul_of_pos_left h (abs_pos.mpr hc.ne')

/-- At the vertex of an arbitrary cone the tangent is its closure. -/
theorem tangentCone_zero_of_isCone {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {C : Set V} (hC : IsCone C) : tangentCone C 0 = closure C := by
  apply Subset.antisymm
  · rintro w ⟨xs, τ, hxs, _, hτ, _, hlim⟩
    apply mem_closure_of_tendsto hlim (.of_forall fun n ↦ ?_)
    simpa only [sub_zero] using hC.2 (hxs n) (inv_pos.mpr (hτ n))
  · apply (isClosed_tangentCone _ _).closure_subset_iff.mpr
    intro w hw
    let t (n : ℕ) : ℝ := 1/((n:ℝ)+1)
    have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
    apply mem_tangentCone_of_forall (xs := fun n ↦ t n • w) (fun n ↦ hC.2 hw (ht n))
      ht tendsto_one_div_add_atTop_nhds_zero_nat
    simp [smul_smul, (ht _).ne']

private theorem wedge_vertex_regular_normal {v : Plane} (hv : v ∈ regularNormalCone wedge 0) : v = 0 := by
  have h (q : Plane) (hq : q ∈ wedge) :=
    inner_nonpos_of_mem_regularNormalCone hv (show q ∈ tangentCone wedge 0 from
      (tangentCone_zero_of_isCone wedge_cone).ge (subset_closure hq))
  have v1 := h (WithLp.toLp 2 (1, (0:ℝ))) (Or.inr (by norm_num))
  have v2 := h (WithLp.toLp 2 (-1, (0:ℝ))) (Or.inr (by norm_num))
  have v3 := h (WithLp.toLp 2 (2, (1:ℝ))) (Or.inr (by norm_num))
  have v4 := h (WithLp.toLp 2 (-2, (-1:ℝ))) (Or.inr (by norm_num))
  change 1 * v.fst + 0 * v.snd ≤ 0 at v1
  change (-1) * v.fst + 0 * v.snd ≤ 0 at v2
  change 2 * v.fst + 1 * v.snd ≤ 0 at v3
  change (-2) * v.fst + (-1) * v.snd ≤ 0 at v4
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · change v.fst = 0
    linarith
  · change v.snd = 0
    linarith

private theorem wedge_normal {v : Plane} (hv : v ∈ normalCone wedge 0) : v = 0 := by
  obtain ⟨_, ps, vs, _, _, hvs, hlim⟩ := hv
  have hzero (n : ℕ) : vs n = 0 := by
    by_cases hp : ps n = 0
    · exact wedge_vertex_regular_normal (hp ▸ hvs n)
    have hmem := (hvs n).1
    rcases hmem with h | h
    · exfalso
      apply hp
      apply (WithLp.equiv 2 _).injective
      exact Prod.ext h.1 h.2
    · let U : Set Plane := {p | |p.snd| < |p.fst|}
      have hopen : IsOpen U := isOpen_lt (WithLp.continuous_snd 2 ℝ ℝ).abs (WithLp.continuous_fst 2 ℝ ℝ).abs
      have hi : ps n ∈ interior wedge := interior_maximal (fun p (hp : p ∈ U) ↦ Or.inr hp) hopen h
      have hn := hvs n
      rw [regularNormalCone_eq_singleton_of_mem_interior hi] at hn
      exact hn
  exact tendsto_nhds_unique hlim (by simpa only [funext hzero] using (tendsto_const_nhds (x := (0:Plane))))

private theorem wedge_boundary_mem : WithLp.toLp 2 ((1:ℝ),(1:ℝ)) ∈ closure wedge := by
  let q (a : ℝ) : Plane := WithLp.toLp 2 (1+a,1)
  have hcont : Continuous q := (WithLp.homeomorphProd 2 ℝ ℝ).symm.continuous.comp
    ((continuous_const.add continuous_id).prodMk continuous_const)
  have hlim : Tendsto q (𝓝[>] 0) (𝓝 (WithLp.toLp 2 ((1:ℝ),(1:ℝ)))) := by
    simpa only [q, add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  right
  change |(1:ℝ)| < |1+a|
  rw [abs_one, abs_of_pos (by linarith)]
  linarith

private theorem wedge_boundary_normal : WithLp.toLp 2 ((-1:ℝ),(1:ℝ)) ∈
    normalCone (closure wedge) (WithLp.toLp 2 ((1:ℝ),(1:ℝ))) := by
  let p := WithLp.toLp 2 ((1:ℝ),(1:ℝ))
  have hclosed : IsClosed {q : Plane | |q.snd| ≤ |q.fst|} := isClosed_le
    (WithLp.continuous_snd 2 ℝ ℝ).abs (WithLp.continuous_fst 2 ℝ ℝ).abs
  have hpos : ∀ᶠ q : Plane in 𝓝 p, 0 < q.fst :=
    (WithLp.continuous_fst 2 ℝ ℝ).continuousAt.eventually (Ioi_mem_nhds (show (0:ℝ) < p.fst from zero_lt_one))
  apply regularNormalCone_subset_normalCone
  refine ⟨wedge_boundary_mem, fun ε hε ↦ ?_⟩
  filter_upwards [self_mem_nhdsWithin, hpos.filter_mono nhdsWithin_le_nhds] with q hq hp
  have hh := (closure_minimal (fun _ hw ↦ wedge_le hw) hclosed) hq
  change |q.snd| ≤ |q.fst| at hh
  rw [abs_of_pos hp] at hh
  apply le_trans _ (mul_nonneg hε.le (norm_nonneg _))
  change ⟪WithLp.toLp 2 ((-1:ℝ),(1:ℝ)), q - p⟫_ℝ ≤ 0
  rw [WithLp.prod_inner_apply]
  change (q.fst-1) * (-1) + (q.snd-1)*1 ≤ 0
  linarith [le_abs_self q.snd]

/-- **Obstruction to the printed 8.44(a)**. At zero the mapping is osc.
The tangent graph acquires a boundary ray with a nonzero normal, while the
original graph has only the zero normal. -/
theorem coderivative_graphicalDerivative_oscAt_counterexample :
    let S := openDoubleConeMapping
    let H := graphicalDerivative S 0 0
    SvOscAt S 0 ∧ (0:ℝ) ∈ S 0 ∧ (1:ℝ) ∈ H 1 ∧
      (-1:ℝ) ∈ coderivative H 0 0 (-1) ∧ (-1:ℝ) ∉ coderivative S 0 0 (-1) := by
  let D : ℝ → Set ℝ := fun x ↦ {u | |u| ≤ |x|}
  have hclosed : IsClosed (svGraph D) := isClosed_le continuous_snd.abs continuous_fst.abs
  have hosc : SvOscAt openDoubleConeMapping 0 := by
    intro u hu
    have huD := (isClosed_svGraph_iff_svOsc.mp hclosed) 0
      (outerSetLimitAlong_mono (l := 𝓝 (0:ℝ)) (C := openDoubleConeMapping) (D := D)
        (fun x z hz ↦ wedge_le (p := WithLp.toLp 2 (x,z)) hz) hu)
    change |u| ≤ |(0:ℝ)| at huD
    have hu₀ : u = 0 := by simpa using huD
    exact Or.inl ⟨rfl, hu₀⟩
  have hK := tangentCone_zero_of_isCone wedge_cone
  have hpoint : WithLp.toLp 2 ((1:ℝ), (1:ℝ)) ∈ tangentCone wedge 0 := hK.ge wedge_boundary_mem
  refine ⟨hosc, wedge_cone.1, hpoint, ?_, ?_⟩
  · change WithLp.toLp 2 ((-1:ℝ), - -1) ∈ normalCone (tangentCone wedge 0) 0
    rw [neg_neg]
    apply normalCone_subset_normalCone_zero_of_isCone (isClosed_tangentCone wedge 0)
      (isCone_tangentCone wedge_cone.1) (WithLp.toLp 2 ((1:ℝ),(1:ℝ)))
    rw [hK]
    exact wedge_boundary_normal
  · intro hv
    have heq := wedge_normal (v := WithLp.toLp 2 ((-1:ℝ), - -1)) hv
    have h := congrArg (fun p : Plane ↦ p.fst) heq
    norm_num at h

end RW
