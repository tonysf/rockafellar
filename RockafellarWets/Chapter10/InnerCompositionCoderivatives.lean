/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Inner composition with a single-valued map
-/

import RockafellarWets.Chapter10.MappingGerms
import RockafellarWets.Chapter9.CoderivativeScalarization
import RockafellarWets.Chapter9.SingleValuedGraphicalDerivatives

open Filter Metric Set Topology
open scoped InnerProductSpace NNReal ENNReal

namespace RW

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  {S : F → Set G} {f : E → F} {x : E} {u : G}

theorem svComp_singleton_inner (S : F → Set G) (f : E → F) :
    svComp S (svSingleton f) = fun a ↦ S (f a) := by
  funext a
  ext u
  simp only [mem_svComp,mem_svSingleton,exists_eq_left]

/-- The unconditional regular-coderivative inclusion in 10.40. -/
theorem regularCoderivative_inner_comp_superset (hf : StrictlyContinuousAt f x)
    (hu : u ∈ S (f x)) (y : G) :
    svComp (regularCoderivative (svSingleton f) x (f x))
      (regularCoderivative S (f x) u) y ⊆ regularCoderivative (fun a ↦ S (f a)) x u y := by
  intro v hv
  obtain ⟨z,hz,hv⟩ := mem_svComp.mp hv
  rw [regularCoderivative_svSingleton_eq_regularSubdifferential hf z] at hv
  obtain ⟨c,hc,Hv⟩ := hv
  have hc' : ⟪z,f x⟫_ℝ = c := EReal.coe_injective hc
  obtain ⟨k,U,hU,hL⟩ := strictlyContinuousAt_iff.mp hf
  have hxU := mem_of_mem_nhds hU
  refine ⟨hu,fun ε hε ↦ ?_⟩
  let δ := ε / ((k:ℝ)+2)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let Ψ (p : WithLp 2 (E × G)) : WithLp 2 (F × G) := WithLp.toLp 2 (f p.fst,p.snd)
  have hΨ : Tendsto Ψ (𝓝[euclideanSvGraph (fun a ↦ S (f a))] (WithLp.toLp 2 (x,u)))
      (𝓝[euclideanSvGraph S] (WithLp.toLp 2 (f x,u))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact ((WithLp.prod_continuous_toLp 2 F G).continuousAt.tendsto.comp
        ((hf.continuousAt.comp (WithLp.continuous_fst 2 E G).continuousAt).tendsto.prodMk_nhds
          (WithLp.continuous_snd 2 E G).continuousAt.tendsto)).mono_left nhdsWithin_le_nhds
    · exact self_mem_nhdsWithin
  have hfst : Tendsto (fun p : WithLp 2 (E × G) ↦ p.fst)
      (𝓝[euclideanSvGraph (fun a ↦ S (f a))] (WithLp.toLp 2 (x,u))) (𝓝 x) :=
    ((WithLp.continuous_fst 2 E G).tendsto _).mono_left nhdsWithin_le_nhds
  filter_upwards [hΨ.eventually (hz.2 δ hδ),hfst.eventually (Hv δ hδ),hfst.eventually hU]
    with p hp hpv hpU
  have hpv' := EReal.coe_le_coe_iff.mp hpv
  have h₁ : ‖p.fst-x‖ ≤ ‖p-WithLp.toLp 2 (x,u)‖ := WithLp.norm_fst_le E (p-WithLp.toLp 2 (x,u))
  have h₂ : ‖p.snd-u‖ ≤ ‖p-WithLp.toLp 2 (x,u)‖ := WithLp.norm_snd_le E (p-WithLp.toLp 2 (x,u))
  have h₃ : ‖f p.fst-f x‖ ≤ (k:ℝ)*‖p.fst-x‖ := by
    simpa only [dist_eq_norm] using hL.dist_le_mul p.fst hpU x hxU
  have h₄ : ‖Ψ p-WithLp.toLp 2 (f x,u)‖ ≤ ‖f p.fst-f x‖+‖p.snd-u‖ := by
    have he := WithLp.prod_norm_sq_eq_of_L2 (Ψ p-WithLp.toLp 2 (f x,u))
    change ‖Ψ p-WithLp.toLp 2 (f x,u)‖^2 = ‖f p.fst-f x‖^2+‖p.snd-u‖^2 at he
    nlinarith [norm_nonneg (Ψ p-WithLp.toLp 2 (f x,u)),norm_nonneg (f p.fst-f x),norm_nonneg (p.snd-u)]
  have h₅ : ‖Ψ p-WithLp.toLp 2 (f x,u)‖+‖p.fst-x‖ ≤
      ((k:ℝ)+2)*‖p-WithLp.toLp 2 (x,u)‖ := by
    calc
      _ ≤ (‖f p.fst-f x‖+‖p.snd-u‖)+‖p.fst-x‖ := add_le_add h₄ le_rfl
      _ ≤ ((k:ℝ)*‖p-WithLp.toLp 2 (x,u)‖+‖p-WithLp.toLp 2 (x,u)‖)+
          ‖p-WithLp.toLp 2 (x,u)‖ := add_le_add
            (add_le_add (h₃.trans (mul_le_mul_of_nonneg_left h₁ k.2)) h₂) h₁
      _ = _ := by ring
  have h₆ := mul_le_mul_of_nonneg_left h₅ hδ.le
  have hd : δ * ((k:ℝ)+2) = ε := div_mul_cancel₀ _ (by positivity)
  simp only [WithLp.prod_inner_apply,WithLp.ofLp_sub,WithLp.ofLp_toLp,Prod.fst_sub,Prod.snd_sub,
    inner_neg_left,inner_sub_right] at hp ⊢
  change ⟪z,f p.fst⟫_ℝ + -⟪y,p.snd⟫_ℝ - (⟪z,f x⟫_ℝ + -⟪y,u⟫_ℝ) ≤
    δ*‖Ψ p-WithLp.toLp 2 (f x,u)‖ at hp
  rw [← mul_assoc,hd] at h₆
  rw [inner_sub_right] at hpv'
  change ⟪v,p.fst⟫_ℝ + -⟪y,p.snd⟫_ℝ - (⟪v,x⟫_ℝ + -⟪y,u⟫_ℝ) ≤
    ε*‖p-WithLp.toLp 2 (x,u)‖
  linarith only [hp,hpv',hc',h₆]

/-- Limiting-coderivative chain inclusion, with only local strict
continuity of the inner map. -/
theorem coderivative_inner_comp_subset (hS : SvOsc S) (hf : StrictlyContinuousAt f x)
    (hQ : ∀ z ∈ coderivative S (f x) u 0,
      (0:E) ∈ coderivative (svSingleton f) x (f x) z → z = 0) (y : G) :
    coderivative (fun a ↦ S (f a)) x u y ⊆
      svComp (coderivative (svSingleton f) x (f x)) (coderivative S (f x) u) y := by
  obtain ⟨g,k,hg,he⟩ := hf.exists_global_lipschitz_germ
  have hx : f x = g x := he.eq_of_nhds
  have hsg : svSingleton f =ᶠ[𝓝 x] svSingleton g := he.mono fun a ha ↦ by simp only [svSingleton,ha]
  have hcg : (fun a ↦ S (f a)) =ᶠ[𝓝 x] (fun a ↦ S (g a)) := he.mono fun a ha ↦ congrArg S ha
  have hgosc : SvOsc (svSingleton g) := fun a ↦ svOscAt_svSingleton_of_continuousAt hg.continuous.continuousAt
  have hgb := svLocallyBoundedAt_svSingleton_of_continuousAt (x := x) hg.continuous.continuousAt
  have hQ' : ∀ w ∈ svCompAux S (svSingleton g) (x,u),
      CompositionCoderivativeQualification S (svSingleton g) x w u := by
    intro w hw z hz hv
    have hwg : w = g x := hw.1
    rw [hwg,← hx] at hz hv
    rw [← coderivative_congr_nhds hsg (f x)] at hv
    exact hQ z hz hv
  intro v hv
  rw [coderivative_congr_nhds hcg u,← svComp_singleton_inner] at hv
  obtain ⟨w,hw,hv⟩ := mem_iUnion₂.mp (coderivative_svComp_subset hgosc hS
    (svLocallyBoundedAt_svCompAux_left hgb u) hQ' y hv)
  have hwg : w = g x := hw.1
  rw [hwg,← hx,← coderivative_congr_nhds hsg (f x)] at hv
  exact hv

theorem coderivative_inner_comp_subset_of_scalar_qualification
    (hS : SvOsc S) (hf : StrictlyContinuousAt f x)
    (hQ : ∀ z ∈ coderivative S (f x) u 0,
      (0:E) ∈ subdifferential (fun a ↦ (⟪z,f a⟫_ℝ:EReal)) x → z = 0) (y : G) :
    coderivative (fun a ↦ S (f a)) x u y ⊆
      svComp (coderivative (svSingleton f) x (f x)) (coderivative S (f x) u) y :=
  coderivative_inner_comp_subset hS hf
    (fun z hz hv ↦ hQ z hz ((coderivative_svSingleton_eq_subdifferential hf z) ▸ hv)) y

end RW
