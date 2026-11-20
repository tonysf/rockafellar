/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Monotone rescaling as minimization over epigraph heights
-/

import RockafellarWets.Chapter10.ParametricLipschitzContinuity
import RockafellarWets.Chapter10.SeparableRegularity
import RockafellarWets.Chapter8.IndicatorSubgradients

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Rescaling with θ(+∞)=+∞. Proper inner functions never take -∞. -/
def extendedRescaling (θ : ℝ → EReal) (f : E → EReal) (x : E) : EReal :=
  if f x = ⊤ then ⊤ else θ (f x).toReal

/-- Minimize θ(a) over the epigraph heights a≥f(x). -/
def rescalingHeightIntegrand (f : E → EReal) (θ : ℝ → EReal)
    (q : WithLp 2 (ℝ × E)) : EReal :=
  indicatorVA (euclideanEpigraph f) (WithLp.toLp 2 (q.snd,q.fst))+θ q.fst

theorem extendedRescaling_of_finite {f : E → EReal} {θ : ℝ → EReal} {x : E} {c : ℝ}
    (hx : f x = c) : extendedRescaling θ f x = θ c := by simp [extendedRescaling,hx]

theorem rescalingHeightIntegrand_apply {f : E → EReal} {θ : ℝ → EReal}
    (hpθ : IsProper θ) (a : ℝ) (x : E) :
    rescalingHeightIntegrand f θ (WithLp.toLp 2 (a,x)) = if f x ≤ (a:EReal) then θ a else ⊤ := by
  by_cases h : f x ≤ (a:EReal)
  · have hm : WithLp.toLp 2 (x,a) ∈ euclideanEpigraph f := h
    simp only [rescalingHeightIntegrand,WithLp.toLp_fst,WithLp.toLp_snd,indicatorVA_apply_mem hm,zero_add,if_pos h]
  · have hm : WithLp.toLp 2 (x,a) ∉ euclideanEpigraph f := h
    simp only [rescalingHeightIntegrand,WithLp.toLp_fst,WithLp.toLp_snd,indicatorVA_apply_not_mem hm,
      if_neg h,EReal.top_add_of_ne_bot (hpθ.2 a).ne']

theorem rescalingHeightIntegrand_le_iff {f : E → EReal} {θ : ℝ → EReal}
    (hpθ : IsProper θ) (a : ℝ) (x : E) (r : ℝ) :
    rescalingHeightIntegrand f θ (WithLp.toLp 2 (a,x)) ≤ r ↔ f x ≤ (a:EReal) ∧ θ a ≤ r := by
  rw [rescalingHeightIntegrand_apply hpθ]
  split_ifs with h <;> simp [h]

theorem parametricValue_rescalingHeightIntegrand {f : E → EReal} {θ : ℝ → EReal}
    (hp : IsProper f) (hpθ : IsProper θ) (hm : Monotone θ) :
    parametricValue (rescalingHeightIntegrand f θ) = extendedRescaling θ f := by
  funext x
  change (⨅ a : ℝ, rescalingHeightIntegrand f θ (WithLp.toLp 2 (a,x))) = _
  by_cases ht : f x = ⊤
  · simp [rescalingHeightIntegrand_apply hpθ,extendedRescaling,ht]
  have hx : f x = ((f x).toReal:EReal) := (EReal.coe_toReal ht (hp.2 x).ne').symm
  rw [extendedRescaling_of_finite hx]
  apply le_antisymm
  · apply iInf_le_of_le (f x).toReal
    rw [rescalingHeightIntegrand_apply hpθ,if_pos hx.le]
  · apply le_iInf
    intro a
    rw [rescalingHeightIntegrand_apply hpθ]
    split_ifs with h
    · exact hm (EReal.coe_le_coe_iff.mp (hx ▸ h))
    · exact le_top

theorem parametricMinimizers_rescalingHeightIntegrand {f : E → EReal} {θ : ℝ → EReal}
    (hp : IsProper f) (hpθ : IsProper θ) (hm : Monotone θ) {x : E} {c d : ℝ}
    (hx : f x = c) (hc : θ c = d) (hstrict : ∀ a : ℝ, c < a → θ c < θ a) :
    parametricMinimizers (rescalingHeightIntegrand f θ) x = {c} := by
  ext a
  rw [mem_parametricMinimizers,parametricValue_rescalingHeightIntegrand hp hpθ hm,
    extendedRescaling_of_finite hx]
  constructor
  · rintro ⟨ha,_⟩
    have hbound := (rescalingHeightIntegrand_le_iff hpθ a x d).mp (ha.trans hc).le
    have hca : c ≤ a := EReal.coe_le_coe_iff.mp (hx ▸ hbound.1)
    have he : θ a = θ c := by simpa only [rescalingHeightIntegrand_apply hpθ,if_pos hbound.1] using ha
    have hac : a ≤ c := by
      by_contra! h
      exact (hstrict a h).ne he.symm
    exact mem_singleton_iff.mpr (le_antisymm hac hca)
  · rintro rfl
    exact ⟨by rw [rescalingHeightIntegrand_apply hpθ,if_pos hx.le],hc.trans_lt (EReal.coe_lt_top _)⟩

theorem isProper_rescalingHeightIntegrand {f : E → EReal} {θ : ℝ → EReal}
    (hpθ : IsProper θ) {x : E} {c d : ℝ} (hx : f x = c) (hc : θ c = d) :
    IsProper (rescalingHeightIntegrand f θ) := by
  have hepi : (euclideanEpigraph f).Nonempty := ⟨WithLp.toLp 2 (x,c),hx.le⟩
  constructor
  · refine ⟨WithLp.toLp 2 (c,x),?_⟩
    rw [rescalingHeightIntegrand_apply hpθ,if_pos hx.le,hc]
    exact EReal.coe_lt_top _
  · intro q
    exact EReal.bot_lt_add_iff.mpr ⟨((indicatorVA_isProper_iff _).mpr hepi).2 _,hpθ.2 _⟩

theorem lowerSemicontinuous_rescalingHeightIntegrand {f : E → EReal} {θ : ℝ → EReal}
    (hp : IsProper f) (hf : LowerSemicontinuous f) (hpθ : IsProper θ) (hθ : LowerSemicontinuous θ) :
    LowerSemicontinuous (rescalingHeightIntegrand f θ) := by
  obtain ⟨x,hx⟩ := hp.1
  have hval : f x = ((f x).toReal:EReal) := (EReal.coe_toReal hx.ne (hp.2 x).ne').symm
  have hepi : (euclideanEpigraph f).Nonempty := ⟨WithLp.toLp 2 (x,(f x).toReal),hval.le⟩
  have hpi := (indicatorVA_isProper_iff _).mpr hepi
  have hswap : Continuous (fun q : WithLp 2 (ℝ × E) ↦ WithLp.toLp 2 (q.snd,q.fst)) :=
    (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ E).continuous
  apply LowerSemicontinuous.add'
    ((lowerSemicontinuous_indicatorVA (isClosed_euclideanEpigraph hf)).comp hswap)
    (hθ.comp (WithLp.fstL 2 ℝ ℝ E).continuous)
  intro q
  exact EReal.continuousAt_add (.inr (hpθ.2 _).ne') (.inl (hpi.2 _).ne')

theorem exists_lt_of_iSup_rescaling_eq_top {θ : ℝ → EReal} (hθ : (⨆ a : ℝ, θ a) = ⊤) (r : ℝ) :
    ∃ a : ℝ, (r:EReal) < θ a := by
  by_contra! h
  have hh : (⨆ a : ℝ, θ a) ≤ (r:EReal) := iSup_le h
  rw [hθ] at hh
  exact (EReal.coe_lt_top r).not_ge hh

/-- The growth and monotonicity assumptions bound all feasible heights on
a neighborhood of each parameter, as required by Theorem 10.13. -/
theorem isParametricallyLevelBounded_rescalingHeightIntegrand {f : E → EReal} {θ : ℝ → EReal}
    (hp : IsProper f) (hf : LowerSemicontinuous f) (hpθ : IsProper θ)
    (hm : Monotone θ) (hsup : (⨆ a : ℝ, θ a) = ⊤) :
    IsParametricallyLevelBounded (rescalingHeightIntegrand f θ) := by
  intro x r
  obtain ⟨c,_,hc⟩ := EReal.exists_between_coe_real (hp.2 x)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hf x (c:EReal) hc)
  obtain ⟨b,hb⟩ := exists_lt_of_iSup_rescaling_eq_top hsup r
  refine ⟨ε/2,by positivity,(isBounded_Icc (a := c) (b := b)).prod
    (isBounded_closedBall (x := x) (r := ε/2)) |>.subset ?_⟩
  rintro ⟨a,z⟩ hq
  have hzb : z ∈ closedBall x (ε/2) := hq.1.2
  have hφ : rescalingHeightIntegrand f θ (WithLp.toLp 2 (a,z)) ≤ (r:EReal) := hq.2
  have hparts := (rescalingHeightIntegrand_le_iff hpθ a z r).mp hφ
  have hzl : (c:EReal) < f z := hball (show z ∈ ball x ε from
    mem_ball.mpr ((mem_closedBall.mp hzb).trans_lt (by linarith)))
  have hca : c ≤ a := (EReal.coe_lt_coe_iff.mp (hzl.trans_le hparts.1)).le
  have hab : a ≤ b := by
    by_contra! h
    exact hb.not_ge ((hm h.le).trans hparts.2)
  exact ⟨⟨hca,hab⟩,hzb⟩

end

end RW
