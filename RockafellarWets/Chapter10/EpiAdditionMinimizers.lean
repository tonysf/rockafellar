/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Compact minimizers and continuity in epi-addition
-/
import RockafellarWets.Chapter10.ParametricLipschitzContinuity
import RockafellarWets.Chapter3.EpiAddition
import RockafellarWets.Chapter5.ClosedImages

open Set Filter Topology Metric Bornology
open scoped InnerProductSpace

noncomputable section
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The decision-first integrand for epi-addition by a finite function. -/
def epiAdditionIntegrand (g : E → EReal) (h : E → ℝ) (q : WithLp 2 (E × E)) : EReal :=
  g q.fst+(h (q.snd-q.fst):EReal)

/-- The local boundedness hypothesis printed in Theorem 10.56. -/
def EpiAdditionLocallyBounded (g : E → EReal) (h : E → ℝ) : Prop :=
  ∀a : ℝ, SvLocallyBounded (fun x ↦ {w | g w+(h (x-w):EReal) ≤ (a:EReal)})

theorem EpiAdditionLocallyBounded.parametric {g : E → EReal} {h : E → ℝ}
    (hb : EpiAdditionLocallyBounded g h) : IsParametricallyLevelBounded (epiAdditionIntegrand g h) :=
  (isLevelBoundedInXLocallyUniformly_iff_svLocallyBounded _).mpr hb

theorem isProper_epiAdditionIntegrand {g : E → EReal} (hp : IsProper g) (h : E → ℝ) :
    IsProper (epiAdditionIntegrand g h) := by
  obtain ⟨w,hw⟩ := hp.1
  exact ⟨⟨WithLp.toLp 2 (w,w),EReal.add_lt_top hw.ne (EReal.coe_ne_top _)⟩,
    fun q ↦ EReal.bot_lt_add_iff.mpr ⟨hp.2 _,EReal.bot_lt_coe _⟩⟩

theorem lowerSemicontinuous_epiAdditionIntegrand {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : Continuous h) :
    LowerSemicontinuous (epiAdditionIntegrand g h) := by
  apply LowerSemicontinuous.add' (hl.comp (WithLp.continuous_fst 2 E E))
    (continuous_coe_real_ereal.comp (hh.comp ((WithLp.continuous_snd 2 E E).sub (WithLp.continuous_fst 2 E E)))).lowerSemicontinuous
  intro q
  exact EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inl (hp.2 q.fst).ne')

/-- The value is the existing epi-sum, with its conventional argument order. -/
theorem parametricValue_epiAdditionIntegrand (g : E → EReal) (h : E → ℝ) :
    parametricValue (epiAdditionIntegrand g h) = epiSum g (fun x ↦ (h x:EReal)) := by
  funext x
  change (⨅w,g w+(h (x-w):EReal)) = ⨅w,g (x-w)+(h w:EReal)
  apply le_antisymm
  · apply le_iInf
    intro w
    simpa only [sub_sub_cancel] using (iInf_le (fun z ↦ g z+(h (x-z):EReal)) (x-w))
  · apply le_iInf
    intro w
    simpa only [sub_sub_cancel] using (iInf_le (fun z ↦ g (x-z)+(h z:EReal)) (x-w))

theorem epiAddition_value_finite {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : Continuous h)
    (hb : EpiAdditionLocallyBounded g h) (x : E) :
    parametricValue (epiAdditionIntegrand g h) x =
      ((parametricValue (epiAdditionIntegrand g h) x).toReal:EReal) := by
  have hk := isProper_epiAdditionIntegrand hp h
  have hkL := lowerSemicontinuous_epiAdditionIntegrand hp hl hh
  have hpf := isProper_parametricValue hkL hk hb.parametric
  obtain ⟨w,hw⟩ := hp.1
  have hut : parametricValue (epiAdditionIntegrand g h) x < ⊤ :=
    (iInf_le _ w).trans_lt (EReal.add_lt_top hw.ne (EReal.coe_ne_top _))
  exact (EReal.coe_toReal hut.ne (hpf.2 x).ne').symm

theorem upperSemicontinuous_epiAdditionValue {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hh : Continuous h) :
    UpperSemicontinuous (parametricValue (epiAdditionIntegrand g h)) := by
  change UpperSemicontinuous (fun x ↦ ⨅w,g w+(h (x-w):EReal))
  apply upperSemicontinuous_iInf
  intro w
  by_cases hwt : g w = ⊤
  · simpa only [hwt,EReal.top_add_coe] using (upperSemicontinuous_const : UpperSemicontinuous (fun _ : E ↦ (⊤:EReal)))
  · have hval := (EReal.coe_toReal hwt (hp.2 w).ne').symm
    have hc : Continuous (fun x ↦ (((g w).toReal+h (x-w):ℝ):EReal)) :=
      continuous_coe_real_ereal.comp (continuous_const.add (hh.comp (continuous_id.sub continuous_const)))
    have he : (fun x ↦ g w+(h (x-w):EReal)) =
        (fun x ↦ (((g w).toReal+h (x-w):ℝ):EReal)) := by
      funext x
      calc
        _ = (((g w).toReal:EReal))+(h (x-w):EReal) := congrArg (fun z : EReal ↦ z+(h (x-w):EReal)) hval
        _ = _ := (EReal.coe_add _ _).symm
    rw [he]
    exact hc.upperSemicontinuous

theorem continuous_epiAdditionValue {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : Continuous h)
    (hb : EpiAdditionLocallyBounded g h) :
    Continuous (parametricValue (epiAdditionIntegrand g h)) :=
  continuous_iff_lower_upperSemicontinuous.mpr
    ⟨lowerSemicontinuous_parametricValue (lowerSemicontinuous_epiAdditionIntegrand hp hl hh)
      (isProper_epiAdditionIntegrand hp h) hb.parametric,upperSemicontinuous_epiAdditionValue hp hh⟩

theorem continuous_epiAdditionValue_toReal {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : Continuous h)
    (hb : EpiAdditionLocallyBounded g h) :
    Continuous (fun x ↦ (parametricValue (epiAdditionIntegrand g h) x).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hv := epiAddition_value_finite hp hl hh hb x
  exact (EReal.tendsto_toReal (by rw [hv]; exact EReal.coe_ne_top _)
    (by rw [hv]; exact EReal.coe_ne_bot _)).comp (continuous_epiAdditionValue hp hl hh hb).continuousAt

/-- The minimizing map is nonempty, outer semicontinuous and locally bounded. -/
theorem epiAddition_minimizers_properties {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : Continuous h)
    (hb : EpiAdditionLocallyBounded g h) :
    (∀x,(parametricMinimizers (epiAdditionIntegrand g h) x).Nonempty) ∧
    SvOsc (parametricMinimizers (epiAdditionIntegrand g h)) ∧
    SvLocallyBounded (parametricMinimizers (epiAdditionIntegrand g h)) := by
  let k := epiAdditionIntegrand g h
  have hk := isProper_epiAdditionIntegrand hp h
  have hkL := lowerSemicontinuous_epiAdditionIntegrand hp hl hh
  have hc := continuous_epiAdditionValue hp hl hh hb
  have hv := epiAddition_value_finite hp hl hh hb
  have hut (x : E) : parametricValue k x < ⊤ := (hv x).trans_lt (EReal.coe_lt_top _)
  refine ⟨fun x ↦ parametricMinimizers_nonempty hkL hk hb.parametric (hut x),?_,?_⟩
  · intro x
    apply svOscWithinAt_univ.mp
    exact svOscWithinAt_paramArgmin (hkL.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.continuous)
      (hut x) hc.continuousAt.continuousWithinAt.upperSemicontinuousWithinAt
  · intro x
    have hbd : ∃a : ℝ, ∀ᶠ y in 𝓝[univ] x, parametricValue k y ≤ (a:EReal) := by
      refine ⟨(parametricValue k x).toReal+1,?_⟩
      have ht : parametricValue k x < (((parametricValue k x).toReal+1:ℝ):EReal) := by
        rw [hv x,EReal.coe_lt_coe_iff]
        simp only [EReal.toReal_coe]
        linarith
      simpa only [nhdsWithin_univ] using (hc.upperSemicontinuous x _ ht).mono (fun _ h ↦ h.le)
    obtain ⟨V,hV,hBV⟩ := svLocallyBoundedWithinAt_paramArgmin hb.parametric hbd
    exact ⟨V,hV,by simpa using hBV⟩

theorem epiAddition_minimizers_compact {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : Continuous h)
    (hb : EpiAdditionLocallyBounded g h) (x : E) :
    IsCompact (parametricMinimizers (epiAdditionIntegrand g h) x) := by
  obtain ⟨_,ho,hb'⟩ := epiAddition_minimizers_properties hp hl hh hb
  exact Metric.isCompact_of_isClosed_isBounded (ho x).isClosed (hb' x).isBounded_apply

theorem epiAddition_minimizers_compact_image {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : Continuous h)
    (hb : EpiAdditionLocallyBounded g h) {V : Set E} (hV : IsCompact V) :
    IsCompact (svImage (parametricMinimizers (epiAdditionIntegrand g h)) V) := by
  obtain ⟨_,ho,hb'⟩ := epiAddition_minimizers_properties hp hl hh hb
  exact Metric.isCompact_of_isClosed_isBounded (ho.isClosed_svImage_of_isCompact hV)
    (svLocallyBounded_iff_isBounded_svImage.mp hb' V hV.isBounded)

/-- Compact index set used in the subsmooth epi-addition representation. -/
theorem epiAddition_minimizers_compact_graph {g : E → EReal} {h : E → ℝ}
    (hp : IsProper g) (hl : LowerSemicontinuous g) (hh : Continuous h)
    (hb : EpiAdditionLocallyBounded g h) {V : Set E} (hV : IsCompact V) :
    IsCompact {p : E × E | p.1 ∈ V ∧ p.2 ∈ parametricMinimizers (epiAdditionIntegrand g h) p.1} := by
  obtain ⟨_,ho,hb'⟩ := epiAddition_minimizers_properties hp hl hh hb
  have hcl : IsClosed {p : E × E | p.1 ∈ V ∧ p.2 ∈ parametricMinimizers (epiAdditionIntegrand g h) p.1} :=
    (hV.isClosed.preimage continuous_fst).inter (isClosed_svGraph_iff_svOsc.mpr ho)
  apply (hV.prod (epiAddition_minimizers_compact_image hp hl hh hb hV)).of_isClosed_subset hcl
  intro p hp'
  exact ⟨hp'.1,mem_svImage.mpr ⟨p.1,hp'.1,hp'.2⟩⟩

end RW
end
