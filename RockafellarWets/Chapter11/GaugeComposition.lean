/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugate composites from polar gauges

The formula of Proposition 11.21 holds wherever the polar gauge is finite.
In particular it holds globally for bounded closed convex sets. The unrestricted
statement has the obstruction in `GaugeCompositionCounterexample`.
-/
import RockafellarWets.Chapter11.SupportOperations
import RockafellarWets.Chapter11.PolarSetGeometry
import RockafellarWets.Chapter11.FenchelMoreau
import RockafellarWets.Chapter10.MonotoneRescalingRepresentation

open Set Topology Bornology
open scoped InnerProductSpace Pointwise
namespace RW

/-- An even convex extended-real function is increasing on the nonnegative axis. -/
theorem monotoneOn_nonnegative_of_even_convex {θ : ℝ → EReal} (hp : IsProper θ)
    (hc : Convex ℝ (epigraph θ)) (he : ∀r, θ (-r) = θ r) : MonotoneOn θ (Ici 0) := by
  intro r hr s hs hrs
  by_cases htop : θ s = ⊤
  · simp [htop]
  have hval : θ s = ((θ s).toReal:EReal) := (EReal.coe_toReal htop (hp.2 s).ne').symm
  by_cases hs0 : s=0
  · have hr0 : r=0 := by change 0≤r at hr; linarith
    simp [hs0,hr0]
  have hsp : 0<s := lt_of_le_of_ne hs (Ne.symm hs0)
  let a := (s-r)/(2*s)
  let b := (s+r)/(2*s)
  have ha : 0≤a := div_nonneg (sub_nonneg.mpr hrs) (by positivity)
  have hb : 0≤b := div_nonneg (by change 0≤r at hr; linarith) (by positivity)
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have hx : a*(-s)+b*s=r := by dsimp [a,b]; field_simp; ring
  have h := hc (show (-s,(θ s).toReal) ∈ epigraph θ from (he s).trans hval |>.le)
    (show (s,(θ s).toReal) ∈ epigraph θ from hval.le) ha hb hab
  change θ (a*(-s)+b*s) ≤ ((a*(θ s).toReal+b*(θ s).toReal:ℝ):EReal) at h
  rw [hx,← add_mul,hab,one_mul,← hval] at h
  exact h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The gauge form of the polar inequality, including zero gauges. -/
theorem inner_le_mul_gauge_of_finite {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0:E) ∈ C) {x v : E} {r s : ℝ}
    (hx : gaugeFunction C x = (r:EReal)) (hv : gaugeFunction (polarSet C) v = (s:EReal)) :
    ⟪v,x⟫_ℝ ≤ s*r := by
  have hr : 0≤r := EReal.coe_le_coe_iff.mp ((nonneg_gaugeFunction C x).trans_eq hx)
  have hsupp : supportFunction C v = (s:EReal) := by
    rwa [gaugeFunction_polarSet_eq_supportFunction hc hclosed h0] at hv
  have hsub : Ioi (0:ℝ) ⊆ {t | ⟪v,x⟫_ℝ ≤ s*(r+t)} := by
    intro t ht
    have hrt : 0<r+t := by change 0<t at ht; linarith
    obtain ⟨z,hz,rfl⟩ := (gaugeFunction_le_iff_mem_smul hc hclosed h0 hrt).mp
      (by rw [hx]; exact EReal.coe_le_coe_iff.mpr (by change 0<t at ht; linarith))
    have hz' : ⟪v,z⟫_ℝ ≤ s := by
      simpa only [real_inner_comm v] using EReal.coe_le_coe_iff.mp ((inner_le_supportFunction hz v).trans_eq hsupp)
    change ⟪v,(r+t) • z⟫_ℝ ≤ s*(r+t)
    rw [real_inner_smul_right]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hz' hrt.le
  have hcl : IsClosed {t : ℝ | ⟪v,x⟫_ℝ ≤ s*(r+t)} := isClosed_le continuous_const (by fun_prop)
  have hz := closure_minimal hsub hcl (show (0:ℝ) ∈ closure (Ioi (0:ℝ)) by simp [closure_Ioi])
  simpa using hz

theorem extendedRescaling_gauge_le_of_mem_smul {C : Set E} (hc : Convex ℝ C)
    (hclosed : IsClosed C) (h0 : (0:E) ∈ C) {θ : ℝ → EReal}
    (hm : MonotoneOn θ (Ici 0)) {r : ℝ} (hr : 0<r) {x : E} (hx : x ∈ r • C) :
    extendedRescaling θ (gaugeFunction C) x ≤ θ r := by
  have hg := (gaugeFunction_le_iff_mem_smul hc hclosed h0 hr).mpr hx
  have hval : gaugeFunction C x = ((gaugeFunction C x).toReal:EReal) :=
    (EReal.coe_toReal (hg.trans_lt (EReal.coe_lt_top _)).ne (gaugeFunction_ne_bot C x)).symm
  rw [extendedRescaling_of_finite hval]
  apply hm
  · exact EReal.coe_le_coe_iff.mp ((nonneg_gaugeFunction C x).trans_eq hval)
  · exact hr.le
  · exact EReal.coe_le_coe_iff.mp (hval.symm.trans_le hg)

/-- Corrected pointwise form of Proposition 11.21: a finite polar gauge suffices. -/
theorem fenchelConjugate_extendedRescaling_gauge_of_finite {C : Set E}
    (hc : Convex ℝ C) (hclosed : IsClosed C) (h0 : (0:E) ∈ C)
    {θ : ℝ → EReal} (hp : IsProper θ) (hθ : Convex ℝ (epigraph θ))
    (he : ∀r, θ (-r) = θ r) {v : E} {s : ℝ}
    (hv : gaugeFunction (polarSet C) v = (s:EReal)) :
    fenchelConjugate (extendedRescaling θ (gaugeFunction C)) v = fenchelConjugate θ s := by
  have hm := monotoneOn_nonnegative_of_even_convex hp hθ he
  have hs : 0≤s := EReal.coe_le_coe_iff.mp ((nonneg_gaugeFunction (polarSet C) v).trans_eq hv)
  have hsupp : supportFunction C v = (s:EReal) := by
    rwa [gaugeFunction_polarSet_eq_supportFunction hc hclosed h0] at hv
  apply le_antisymm
  · apply iSup_le
    intro x
    by_cases htop : gaugeFunction C x=⊤
    · simp [extendedRescaling,htop]
    have hx : gaugeFunction C x = ((gaugeFunction C x).toReal:EReal) :=
      (EReal.coe_toReal htop (gaugeFunction_ne_bot C x)).symm
    rw [extendedRescaling_of_finite hx]
    apply le_trans (EReal.sub_le_sub (EReal.coe_le_coe_iff.mpr (inner_le_mul_gauge_of_finite hc hclosed h0 hx hv)) le_rfl)
    simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using
      le_fenchelConjugate θ (gaugeFunction C x).toReal s
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro a ha
    have hbound := (fenchelConjugate_le_coe_iff _ _ a).mp ha.le
    have hnonneg (r : ℝ) (hr : 0≤r) : ((s*r-a:ℝ):EReal) ≤ θ r := by
      by_cases hr0 : r=0
      · subst r
        simpa [extendedRescaling_of_finite (gaugeFunction_zero C)] using hbound 0
      have hrp : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
      cases hval : θ r with
      | bot => exact ((hp.2 r).ne' hval).elim
      | top => exact le_top
      | coe c =>
        have hsup : supportFunction (r • C) v ≤ ((c+a:ℝ):EReal) := by
          apply (supportFunction_le_iff _ _ _).mpr
          intro x hx
          have hb := (hbound x).trans (extendedRescaling_gauge_le_of_mem_smul hc hclosed h0 hm hrp hx)
          rw [hval,EReal.coe_le_coe_iff] at hb
          apply EReal.coe_le_coe_iff.mpr
          rw [real_inner_comm]
          linarith
        rw [supportFunction_smul C hrp v,hsupp,← EReal.coe_mul,EReal.coe_le_coe_iff] at hsup
        exact EReal.coe_le_coe_iff.mpr (by nlinarith)
    apply (fenchelConjugate_le_coe_iff θ s a).mpr
    intro r
    by_cases hr : 0≤r
    · simpa only [RCLike.inner_apply,conj_trivial,mul_comm] using hnonneg r hr
    · have hr' : 0≤-r := by linarith
      have hb := hnonneg (-r) hr'
      rw [he r] at hb
      apply le_trans (EReal.coe_le_coe_iff.mpr ?_) hb
      simp only [RCLike.inner_apply,conj_trivial]
      nlinarith

/-- The gauge conjugacy formula is global whenever the original set is bounded. -/
theorem fenchelConjugate_extendedRescaling_gauge_of_bounded {C : Set E}
    (hc : Convex ℝ C) (hclosed : IsClosed C) (h0 : (0:E) ∈ C) (hb : IsBounded C)
    {θ : ℝ → EReal} (hp : IsProper θ) (hθ : Convex ℝ (epigraph θ))
    (he : ∀r, θ (-r) = θ r) :
    fenchelConjugate (extendedRescaling θ (gaugeFunction C)) =
      extendedRescaling (fenchelConjugate θ) (gaugeFunction (polarSet C)) := by
  funext v
  obtain ⟨s,hs⟩ := (nonempty_bounded_iff_supportFunction_finite C).mp ⟨⟨0,h0⟩,hb⟩ v
  have hv : gaugeFunction (polarSet C) v = (s:EReal) := by
    rw [gaugeFunction_polarSet_eq_supportFunction hc hclosed h0]; exact hs
  rw [extendedRescaling_of_finite hv]
  exact fenchelConjugate_extendedRescaling_gauge_of_finite hc hclosed h0 hp hθ he hv

end RW
