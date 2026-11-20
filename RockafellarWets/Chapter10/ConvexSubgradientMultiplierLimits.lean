/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closed convex subgradient graphs and qualified multiplier limits
-/
import RockafellarWets.Chapter10.NormalMultiplierLimits

open Set Filter Topology
open scoped InnerProductSpace

namespace RW
variable {E F G : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Convex subgradient limits need no separate convergence of function values. -/
theorem mem_subdifferential_of_tendsto_of_convex {g : F → EReal}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hc : Convex ℝ (epigraph g))
    {xs vs : ℕ → F} {x v : F} (hx : Tendsto xs atTop (𝓝 x)) (hv : Tendsto vs atTop (𝓝 v))
    (hs : ∀n, vs n ∈ subdifferential g (xs n)) : v ∈ subdifferential g x := by
  choose c hcv using fun n ↦ (hs n).1
  have hbound {z : F} (hz : z ∈ effectiveDomain g) :
      g x ≤ (((g z).toReal-⟪v,z-x⟫_ℝ:ℝ):EReal) := by
    have hzval := (EReal.coe_toReal hz.ne (hp.2 z).ne').symm
    have hseq (n : ℕ) : (xs n,(g z).toReal-⟪vs n,z-xs n⟫_ℝ) ∈ epigraph g := by
      have hh := (mem_subdifferential_iff_of_convex hc hp (hcv n)).mp (hs n) z
      rw [hzval,EReal.coe_le_coe_iff] at hh
      change g (xs n) ≤ _
      rw [hcv n,EReal.coe_le_coe_iff]
      linarith
    exact (isClosed_epigraph_of_lsc_ereal g hl).mem_of_tendsto
      (hx.prodMk_nhds (tendsto_const_nhds.sub (hv.inner (tendsto_const_nhds.sub hx)))) (.of_forall hseq)
  obtain ⟨z,hz⟩ := hp.1
  have hxt : g x ≠ ⊤ := ne_of_lt ((hbound hz).trans_lt (EReal.coe_lt_top _))
  have hxval : g x = ((g x).toReal:EReal) := (EReal.coe_toReal hxt (hp.2 x).ne').symm
  apply (mem_subdifferential_iff_of_convex hc hp hxval).mpr
  intro y
  by_cases hyt : g y = ⊤
  · rw [hyt]; exact le_top
  · have hh := hbound (lt_top_iff_ne_top.mpr hyt)
    rw [hxval,EReal.coe_le_coe_iff] at hh
    rw [← EReal.coe_toReal hyt (hp.2 y).ne',EReal.coe_le_coe_iff]
    linarith

/-- Kernel qualification prevents unbounded convex subgradient multipliers
when their linear images converge, even when finiteness at the limit is unknown. -/
theorem mem_image_subdifferential_of_tendsto_of_convex {g : F → EReal}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hc : Convex ℝ (epigraph g))
    {f : E → F} {A : E → F →L[ℝ] G} {x : E}
    (hf : ContinuousAt f x) (hA : ContinuousAt A x)
    (hQ : ∀v ∈ normalCone (closure (effectiveDomain g)) (f x), A x v = 0 → v = 0)
    {ys : ℕ → E} {us : ℕ → G} {u : G} (hy : Tendsto ys atTop (𝓝 x))
    (hu : Tendsto us atTop (𝓝 u)) (hm : ∀n, us n ∈ A (ys n) '' subdifferential g (f (ys n))) :
    u ∈ A x '' subdifferential g (f x) := by
  choose v hv he using hm
  choose c hcv using fun n ↦ (hv n).1
  obtain ⟨a,z,φ,hφ,ha,hsum,hat,hzt⟩ := exists_normalized_multiplier_subsequence (fun _ ↦ 1) v (fun _ ↦ by norm_num)
  have hyφ := hy.comp hφ.tendsto_atTop
  have hfφ := hf.tendsto.comp hyφ
  have hxD : f x ∈ closure (effectiveDomain g) := isClosed_closure.mem_of_tendsto hfφ
    (.of_forall (fun n ↦ subset_closure ((hcv (φ n)).trans_lt (EReal.coe_lt_top _))))
  have hAt : Tendsto (fun n ↦ A (ys (φ n)) ((1+‖v (φ n)‖)⁻¹ • v (φ n))) atTop (𝓝 (A x z)) :=
    ((continuous_fst.clm_apply continuous_snd : Continuous (fun p : (F →L[ℝ] G) × F ↦ p.1 p.2)).tendsto (A x,z)).comp
      ((hA.tendsto.comp hyφ).prodMk_nhds hzt)
  have hright : Tendsto (fun n ↦ (1/(1+‖v (φ n)‖)) • us (φ n)) atTop (𝓝 (a • u)) :=
    hat.smul (hu.comp hφ.tendsto_atTop)
  have hAz : A x z = a • u := tendsto_nhds_unique hAt (hright.congr (fun n ↦ by simp only [map_smul,he,one_div]))
  have hapos : 0 < a := by
    apply lt_of_le_of_ne ha
    intro heqa
    have ha0 : a = 0 := heqa.symm
    obtain ⟨b,_,hbg⟩ := EReal.exists_between_coe_real (hp.2 (f x))
    have hlow : ∀ᶠ n in atTop, b ≤ c (φ n) := by
      filter_upwards [hfφ.eventually (hl (f x) (b:EReal) hbg)] with n hn
      dsimp only [Function.comp_def] at hn
      rw [hcv (φ n)] at hn
      exact (EReal.coe_lt_coe_iff.mp hn).le
    have hsupport (w : F) (hw : w ∈ effectiveDomain g) : ⟪z,w-f x⟫_ℝ ≤ 0 := by
      have hwval := (EReal.coe_toReal hw.ne (hp.2 w).ne').symm
      have ht := (hat.mul_const b).add (hzt.inner ((tendsto_const_nhds (x := w)).sub hfφ))
      have hright := hat.mul_const (g w).toReal
      have hh : a*b+⟪z,w-f x⟫_ℝ ≤ a*(g w).toReal := by
        apply le_of_tendsto_of_tendsto ht hright
        filter_upwards [hlow] with n hn
        have hs := (mem_subdifferential_iff_of_convex hc hp (hcv (φ n))).mp (hv (φ n)) w
        rw [hwval,EReal.coe_le_coe_iff] at hs
        have hnpos : 0 ≤ 1/(1+‖v (φ n)‖) := by positivity
        have hm1 := mul_le_mul_of_nonneg_left hs hnpos
        have hm2 := mul_le_mul_of_nonneg_left hn hnpos
        rw [mul_add] at hm1
        have hh := (add_le_add hm2 (le_rfl :
          (1/(1+‖v (φ n)‖))*⟪v (φ n),w-f (ys (φ n))⟫_ℝ ≤
          (1/(1+‖v (φ n)‖))*⟪v (φ n),w-f (ys (φ n))⟫_ℝ)).trans hm1
        simpa only [one_div,real_inner_smul_left] using hh
      simpa only [ha0,zero_mul,zero_add] using hh
    have hzN : z ∈ normalCone (closure (effectiveDomain g)) (f x) := by
      rw [normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph hc).closure hxD]
      have hsub : effectiveDomain g ⊆ {w | ⟪z,w-f x⟫_ℝ ≤ 0} := fun w hw ↦ hsupport w hw
      have hclosed : IsClosed {w : F | ⟪z,w-f x⟫_ℝ ≤ 0} := isClosed_le (by fun_prop) continuous_const
      exact closure_minimal hsub hclosed
    have hz0 := hQ z hzN (by simpa only [ha0,zero_smul] using hAz)
    simp only [hz0,norm_zero,add_zero] at hsum
    linarith
  have hvt : Tendsto (fun n ↦ v (φ n)) atTop (𝓝 (a⁻¹ • z)) := by
    have hh := (hat.inv₀ hapos.ne').smul hzt
    apply hh.congr
    intro n
    simp only [one_div,inv_inv,smul_smul,mul_inv_cancel₀ (by positivity : (1+‖v (φ n)‖) ≠ 0),one_smul]
  have hvlim := mem_subdifferential_of_tendsto_of_convex hp hl hc hfφ hvt (fun n ↦ hv (φ n))
  refine ⟨a⁻¹ • z,hvlim,?_⟩
  rw [map_smul,hAz,smul_smul,inv_mul_cancel₀ hapos.ne',one_smul]

end RW
