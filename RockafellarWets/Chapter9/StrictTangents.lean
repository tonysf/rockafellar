/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Moving-base outer tangent cones
-/

import RockafellarWets.Chapter6.RegularTangents

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The moving-base outer tangent cone underlying the strict derivative in9.53. -/
def strictTangentCone (C : Set E) (x : E) : Set E :=
  outerSetLimitAlong ((𝓝[C] x) ×ˢ (𝓝[>] (0:ℝ)))
    (fun p : E × ℝ ↦ blowUp C p.1 p.2)

theorem isClosed_strictTangentCone (C : Set E) (x : E) : IsClosed (strictTangentCone C x) :=
  isClosed_outerSetLimitAlong _ _

/-- The exact sequence form of the moving-base outer limit. -/
theorem mem_strictTangentCone_iff_exists_sequences {C : Set E} {x w : E} :
    w ∈ strictTangentCone C x ↔
      ∃ (a b : ℕ → E) (τ : ℕ → ℝ), (∀ n, a n ∈ C) ∧ (∀ n, b n ∈ C) ∧
        Tendsto a atTop (𝓝 x) ∧ (∀ n, 0 < τ n) ∧ Tendsto τ atTop (𝓝 0) ∧
        Tendsto (fun n ↦ (τ n)⁻¹ • (b n-a n)) atTop (𝓝 w) := by
  constructor
  · intro hw
    have hpick (n : ℕ) : ∃ a b : E, ∃ τ : ℝ,
        a ∈ C ∧ b ∈ C ∧ dist a x < 1/((n:ℝ)+1) ∧
        0 < τ ∧ τ < 1/((n:ℝ)+1) ∧ dist (τ⁻¹ • (b-a)) w < 1/((n:ℝ)+1) := by
      have hpos : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
      have hA : (C ∩ ball x (1/((n:ℝ)+1))) ×ˢ Ioo 0 (1/((n:ℝ)+1)) ∈
          (𝓝[C] x) ×ˢ (𝓝[>] (0:ℝ)) :=
        prod_mem_prod (inter_mem_nhdsWithin C (ball_mem_nhds x hpos)) (Ioo_mem_nhdsGT hpos)
      obtain ⟨⟨a,τ⟩,ha,v,⟨b,hb,hv⟩,hvw⟩ :=
        Filter.frequently_iff.mp (hw (ball w (1/((n:ℝ)+1))) (ball_mem_nhds w hpos)) hA
      exact ⟨a,b,τ,ha.1.1,hb,mem_ball.mp ha.1.2,ha.2.1,ha.2.2,by simpa only [hv] using mem_ball.mp hvw⟩
    choose a b τ ha hb hax hτ hτb hq using hpick
    refine ⟨a,b,τ,ha,hb,?_,hτ,?_,?_⟩
    · rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hax n).le) tendsto_one_div_add_atTop_nhds_zero_nat
    · exact squeeze_zero (fun n ↦ (hτ n).le) (fun n ↦ (hτb n).le) tendsto_one_div_add_atTop_nhds_zero_nat
    · rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hq n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  · rintro ⟨a,b,τ,ha,hb,hat,hτ,hτt,hqt⟩ V hV
    have hp := (tendsto_nhdsWithin_of_forall_mem ha hat).prodMk
      (tendsto_nhdsWithin_of_forall_mem hτ hτt)
    rw [Filter.frequently_iff]
    intro A hA
    have hnA : ∀ᶠ n in atTop, (a n,τ n) ∈ A := hp hA
    obtain ⟨n,hn,hqn⟩ := (hnA.and (hqt hV)).exists
    exact ⟨(a n,τ n),hn,_,⟨b n,hb n,rfl⟩,hqn⟩

/-- The second endpoints converge automatically when the scaled secants converge. -/
theorem tendsto_endpoint_of_scaled_secants {a b : ℕ → E} {τ : ℕ → ℝ} {x w : E}
    (ha : Tendsto a atTop (𝓝 x)) (hτ : ∀ n, 0 < τ n) (hτt : Tendsto τ atTop (𝓝 0))
    (hq : Tendsto (fun n ↦ (τ n)⁻¹ • (b n-a n)) atTop (𝓝 w)) :
    Tendsto b atTop (𝓝 x) := by
  have h := ha.add (hτt.smul hq)
  simpa only [zero_smul,add_zero,smul_smul,mul_inv_cancel₀ (hτ _).ne',one_smul,add_sub_cancel] using h

/-- The moving-base tangent depends only on the local germ of the set. -/
theorem strictTangentCone_congr_nhds {C D : Set E} {x : E} (h : C =ᶠ[𝓝 x] D) :
    strictTangentCone C x = strictTangentCone D x := by
  suffices hsub : ∀ {A B : Set E}, A =ᶠ[𝓝 x] B →
      strictTangentCone A x ⊆ strictTangentCone B x from
    Subset.antisymm (hsub h) (hsub h.symm)
  intro A B hAB w hw
  obtain ⟨a,b,τ,ha,hb,hat,hτ,hτt,hq⟩ := mem_strictTangentCone_iff_exists_sequences.mp hw
  have hbt := tendsto_endpoint_of_scaled_secants hat hτ hτt hq
  have he : ∀ᶠ n in atTop, a n ∈ B ∧ b n ∈ B := by
    filter_upwards [hat.eventually hAB,hbt.eventually hAB] with n han hbn
    exact ⟨Eq.mp han (ha n),Eq.mp hbn (hb n)⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  have ht := tendsto_add_atTop_nat N
  exact mem_strictTangentCone_iff_exists_sequences.mpr
    ⟨fun n ↦ a (n+N),fun n ↦ b (n+N),fun n ↦ τ (n+N),
      fun n ↦ (hN (n+N) (Nat.le_add_left N n)).1,
      fun n ↦ (hN (n+N) (Nat.le_add_left N n)).2,hat.comp ht,
      fun n ↦ hτ (n+N),hτt.comp ht,hq.comp ht⟩

theorem tangentCone_subset_strictTangentCone {C : Set E} {x : E} (hx : x ∈ C) :
    tangentCone C x ⊆ strictTangentCone C x := by
  rintro w ⟨b,τ,hb,_,hτ,hτt,hq⟩
  exact mem_strictTangentCone_iff_exists_sequences.mpr
    ⟨fun _ ↦ x,b,τ,fun _ ↦ hx,hb,tendsto_const_nhds,hτ,hτt,hq⟩

theorem isCone_strictTangentCone {C : Set E} {x : E} (hx : x ∈ C) :
    IsCone (strictTangentCone C x) := by
  refine ⟨tangentCone_subset_strictTangentCone hx (isCone_tangentCone hx).1,?_⟩
  intro w hw c hc
  obtain ⟨a,b,τ,ha,hb,hat,hτ,hτt,hq⟩ := mem_strictTangentCone_iff_exists_sequences.mp hw
  apply mem_strictTangentCone_iff_exists_sequences.mpr
  refine ⟨a,b,fun n ↦ τ n/c,ha,hb,hat,fun n ↦ div_pos (hτ n) hc,?_,?_⟩
  · simpa using hτt.div_const c
  · have he (n : ℕ) : (τ n/c)⁻¹ = c * (τ n)⁻¹ := by
      rw [div_eq_mul_inv,mul_inv,inv_inv,mul_comm]
    simpa only [he,mul_smul] using hq.const_smul c

/-- Moving-base tangents are symmetric even when the ordinary tangent is not. -/
theorem neg_mem_strictTangentCone {C : Set E} {x w : E} (hw : w ∈ strictTangentCone C x) :
    -w ∈ strictTangentCone C x := by
  obtain ⟨a,b,τ,ha,hb,hat,hτ,hτt,hq⟩ := mem_strictTangentCone_iff_exists_sequences.mp hw
  refine mem_strictTangentCone_iff_exists_sequences.mpr
    ⟨b,a,τ,hb,ha,tendsto_endpoint_of_scaled_secants hat hτ hτt hq,hτ,hτt,?_⟩
  have he (n : ℕ) : (τ n)⁻¹ • (a n-b n) = -((τ n)⁻¹ • (b n-a n)) := by
    rw [← smul_neg,neg_sub]
  simpa only [he] using hq.neg

/-- Nearby ordinary tangents may lose information, but every outer limit of
them remains a moving-base tangent. -/
theorem outerLimit_tangentCone_subset_strictTangentCone (C : Set E) (x : E) :
    outerSetLimitAlong (𝓝[C] x) (tangentCone C) ⊆ strictTangentCone C x := by
  intro w hw
  have hpick (n : ℕ) : ∃ a b : E, ∃ τ : ℝ,
      a ∈ C ∧ b ∈ C ∧ dist a x < 1/((n:ℝ)+1) ∧
      0 < τ ∧ τ < 1/((n:ℝ)+1) ∧ dist (τ⁻¹ • (b-a)) w < 1/((n:ℝ)+1) := by
    let r := 1/((n:ℝ)+1)
    have hr : 0 < r := by dsimp only [r]; positivity
    obtain ⟨a,ha,v,hv,hvw⟩ := Filter.frequently_iff.mp
      (hw (ball w (r/2)) (ball_mem_nhds w (by positivity)))
      (inter_mem_nhdsWithin C (ball_mem_nhds x hr))
    rw [tangentCone_eq_outerSetLimitAlong] at hv
    obtain ⟨τ,hτ,q,⟨b,hb,hbq⟩,hqv⟩ := Filter.frequently_iff.mp
      (hv (ball v (r/2)) (ball_mem_nhds v (by positivity))) (Ioo_mem_nhdsGT hr)
    refine ⟨a,b,τ,ha.1,hb,mem_ball.mp ha.2,hτ.1,hτ.2,?_⟩
    change τ⁻¹ • (b-a) = q at hbq
    rw [hbq]
    have h1 := mem_ball.mp hqv
    have h2 := mem_ball.mp hvw
    exact (dist_triangle q v w).trans_lt (by linarith)
  choose a b τ ha hb hax hτ hτb hq using hpick
  apply mem_strictTangentCone_iff_exists_sequences.mpr
  refine ⟨a,b,τ,ha,hb,?_,hτ,?_,?_⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hax n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  · exact squeeze_zero (fun n ↦ (hτ n).le) (fun n ↦ (hτb n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hq n).le) tendsto_one_div_add_atTop_nhds_zero_nat

/-- Moving-base tangent cones commute with continuous linear coordinates. -/
theorem strictTangentCone_preimage_continuousLinearEquiv {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (C : Set F) (x : E) :
    strictTangentCone (e ⁻¹' C) x = e ⁻¹' strictTangentCone C (e x) := by
  ext w
  rw [mem_preimage]
  constructor
  · intro hw
    obtain ⟨a,b,τ,ha,hb,hat,hτ,hτt,hq⟩ := mem_strictTangentCone_iff_exists_sequences.mp hw
    apply mem_strictTangentCone_iff_exists_sequences.mpr
    refine ⟨e ∘ a,e ∘ b,τ,ha,hb,e.continuous.continuousAt.tendsto.comp hat,hτ,hτt,?_⟩
    have h := e.continuous.continuousAt.tendsto.comp hq
    change Tendsto (fun n ↦ e ((τ n)⁻¹ • (b n-a n))) atTop (𝓝 (e w)) at h
    simpa only [Function.comp_apply,map_smul,map_sub] using h
  · intro hw
    obtain ⟨a,b,τ,ha,hb,hat,hτ,hτt,hq⟩ := mem_strictTangentCone_iff_exists_sequences.mp hw
    apply mem_strictTangentCone_iff_exists_sequences.mpr
    refine ⟨e.symm ∘ a,e.symm ∘ b,τ,?_,?_,?_,hτ,hτt,?_⟩
    · simpa only [mem_preimage,Function.comp_apply,e.apply_symm_apply] using ha
    · simpa only [mem_preimage,Function.comp_apply,e.apply_symm_apply] using hb
    · simpa only [e.symm_apply_apply] using e.symm.continuous.continuousAt.tendsto.comp hat
    · have h := e.symm.continuous.continuousAt.tendsto.comp hq
      change Tendsto (fun n ↦ e.symm ((τ n)⁻¹ • (b n-a n))) atTop (𝓝 (e.symm (e w))) at h
      simpa only [Function.comp_apply,map_smul,map_sub,e.symm_apply_apply] using h

end RW
