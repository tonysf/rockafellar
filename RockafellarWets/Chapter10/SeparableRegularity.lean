/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Regularity of separable functions
-/

import RockafellarWets.Chapter10.SeparableSubderivatives
import RockafellarWets.Chapter10.SubgradientGerms
import RockafellarWets.Chapter8.RegularSupportDuality

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {f : E → EReal} {g : F → EReal} {x : E} {y : F} {c d : ℝ}

/-- Local properness near finite points is enough for lower
semicontinuity of a separable sum near its finite base value. -/
theorem isLocallyLscAt_separableSum (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hx : f x = c) (hy : g y = d) :
    IsLocallyLscAt (separableSum f g) (WithLp.toLp 2 (x,y)) := by
  let f' := fun z ↦ max (f z) ((c-1:ℝ):EReal)
  let g' := fun z ↦ max (g z) ((d-1:ℝ):EReal)
  have hfx : f' x = (c:EReal) := by
    change max (f x) ((c-1:ℝ):EReal) = (c:EReal)
    rw [hx]
    exact max_eq_left (EReal.coe_le_coe_iff.mpr (show c-1 ≤ c by linarith))
  have hgy : g' y = (d:EReal) := by
    change max (g y) ((d-1:ℝ):EReal) = (d:EReal)
    rw [hy]
    exact max_eq_left (EReal.coe_le_coe_iff.mpr (show d-1 ≤ d by linarith))
  have hpf : IsProper f' := ⟨⟨x,hfx.trans_lt (EReal.coe_lt_top _)⟩,
    fun z ↦ (EReal.bot_lt_coe (c-1)).trans_le (le_max_right ..)⟩
  have hpg : IsProper g' := ⟨⟨y,hgy.trans_lt (EReal.coe_lt_top _)⟩,
    fun z ↦ (EReal.bot_lt_coe (d-1)).trans_le (le_max_right ..)⟩
  have hfe : f' =ᶠ[𝓝 x] f := by
    filter_upwards [hf x ((c-1:ℝ):EReal) (by change ((c-1:ℝ):EReal) < f x; rw [hx]; exact EReal.coe_lt_coe_iff.mpr (by linarith))] with z hz
    exact max_eq_left hz.le
  have hge : g' =ᶠ[𝓝 y] g := by
    filter_upwards [hg y ((d-1:ℝ):EReal) (by change ((d-1:ℝ):EReal) < g y; rw [hy]; exact EReal.coe_lt_coe_iff.mpr (by linarith))] with z hz
    exact max_eq_left hz.le
  have hse : separableSum f' g' =ᶠ[𝓝 (WithLp.toLp 2 (x,y))] separableSum f g := by
    filter_upwards [((WithLp.fstL 2 ℝ E F).continuous.tendsto _).eventually hfe,
      ((WithLp.sndL 2 ℝ E F).continuous.tendsto _).eventually hge] with q hqf hqg
    change f' q.fst+g' q.snd = f q.fst+g q.snd
    exact congrArg₂ (· + ·) hqf hqg
  have hsl : LowerSemicontinuous (separableSum f' g') :=
    lowerSemicontinuous_separableSum (hf.sup lowerSemicontinuous_const) (hg.sup lowerSemicontinuous_const) hpf hpg
  have hbase : separableSum f' g' (WithLp.toLp 2 (x,y)) = ((c+d:ℝ):EReal) := by
    simp only [separableSum,WithLp.toLp_fst,WithLp.toLp_snd,hfx,hgy,EReal.coe_add]
  exact (locallyLscAt_of_lowerSemicontinuous_finite hsl hbase).congr_nhds hse

/-- **Proposition 10.5**, the upper bound for the regular subderivative. -/
theorem regularSubderivative_separableSum_le (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hx : f x = c) (hy : g y = d) (hf0 : subderivative f x 0 = 0) (hg0 : subderivative g y 0 = 0)
    (w : WithLp 2 (E × F)) :
    regularSubderivative (separableSum f g) (WithLp.toLp 2 (x,y)) w ≤
      regularSubderivative f x w.fst + regularSubderivative g y w.snd := by
  have hdf := (isCalmFromBelowAt_iff_subderivative_ne_bot hx).mp ((isCalmFromBelowAt_iff_subderivative_zero hx).mpr hf0)
  have hdg := (isCalmFromBelowAt_iff_subderivative_ne_bot hy).mp ((isCalmFromBelowAt_iff_subderivative_zero hy).mpr hg0)
  have hnf : regularSubderivative f x w.fst ≠ ⊥ :=
    ((hdf w.fst).trans_le (subderivative_le_regularSubderivative hx w.fst)).ne'
  have hng : regularSubderivative g y w.snd ≠ ⊥ :=
    ((hdg w.snd).trans_le (subderivative_le_regularSubderivative hy w.snd)).ne'
  by_cases hft : regularSubderivative f x w.fst = ⊤
  · rw [hft,EReal.top_add_of_ne_bot hng]
    exact le_top
  by_cases hgt : regularSubderivative g y w.snd = ⊤
  · rw [hgt,EReal.add_top_of_ne_bot hnf]
    exact le_top
  let a := (regularSubderivative f x w.fst).toReal
  let b := (regularSubderivative g y w.snd).toReal
  have ha : regularSubderivative f x w.fst = (a:EReal) := (EReal.coe_toReal hft hnf).symm
  have hb : regularSubderivative g y w.snd = (b:EReal) := (EReal.coe_toReal hgt hng).symm
  have hfa := (regularSubderivative_le_coe_iff_support_polar hx (locallyLscAt_of_lowerSemicontinuous_finite hf hx)).mp ha.le
  have hgb := (regularSubderivative_le_coe_iff_support_polar hy (locallyLscAt_of_lowerSemicontinuous_finite hg hy)).mp hb.le
  have hxy : separableSum f g (WithLp.toLp 2 (x,y)) = ((c+d:ℝ):EReal) := by
    simp only [separableSum,WithLp.toLp_fst,WithLp.toLp_snd,hx,hy,EReal.coe_add]
  rw [ha,hb,← EReal.coe_add]
  apply (regularSubderivative_le_coe_iff_support_polar hxy (isLocallyLscAt_separableSum hf hg hx hy)).mpr
  constructor
  · apply (supportFunction_le_iff _ _ _).mpr
    intro v hv
    obtain ⟨hvf,hvg⟩ := (mem_subdifferential_separableSum_iff (hf x) (hg y) hx hy v).mp hv
    have h1 := EReal.coe_le_coe_iff.mp ((supportFunction_le_iff _ _ _).mp hfa.1 _ hvf)
    have h2 := EReal.coe_le_coe_iff.mp ((supportFunction_le_iff _ _ _).mp hgb.1 _ hvg)
    apply EReal.coe_le_coe_iff.mpr
    change ⟪v.fst,w.fst⟫_ℝ+⟪v.snd,w.snd⟫_ℝ ≤ a+b
    exact add_le_add h1 h2
  · intro v hv
    obtain ⟨hvf,hvg⟩ := horizonSubdifferential_separableSum_subset (hf x) (hg y) hx hy hv
    change ⟪w.fst,v.fst⟫_ℝ+⟪w.snd,v.snd⟫_ℝ ≤ 0
    exact add_nonpos (hfa.2 _ hvf) (hgb.2 _ hvg)

/-- **Proposition 10.5**, regular summands give regular separable sums and
exact lower and regular subderivatives. -/
theorem separableSum_regularity (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hrf : IsSubdifferentiallyRegularAt f x) (hrg : IsSubdifferentiallyRegularAt g y)
    (hf0 : subderivative f x 0 = 0) (hg0 : subderivative g y 0 = 0) :
    IsSubdifferentiallyRegularAt (separableSum f g) (WithLp.toLp 2 (x,y)) ∧
      ∀ w : WithLp 2 (E × F), subderivative (separableSum f g) (WithLp.toLp 2 (x,y)) w =
        subderivative f x w.fst + subderivative g y w.snd := by
  have hx := (EReal.coe_toReal hrf.2.1 hrf.1).symm
  have hy := (EReal.coe_toReal hrg.2.1 hrg.1).symm
  have hxy : separableSum f g (WithLp.toLp 2 (x,y)) = (((f x).toReal+(g y).toReal:ℝ):EReal) := by
    exact (congrArg₂ (· + ·) hx hy).trans (EReal.coe_add _ _).symm
  have hef := (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mp hrf).2
  have heg := (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mp hrg).2
  have hupper (w : WithLp 2 (E × F)) :
      regularSubderivative (separableSum f g) (WithLp.toLp 2 (x,y)) w ≤
        subderivative f x w.fst+subderivative g y w.snd := by
    simpa only [← hef,← heg] using regularSubderivative_separableSum_le hf hg hx hy hf0 hg0 w
  have he : subderivative (separableSum f g) (WithLp.toLp 2 (x,y)) =
      regularSubderivative (separableSum f g) (WithLp.toLp 2 (x,y)) := by
    funext w
    exact le_antisymm (subderivative_le_regularSubderivative hxy w)
      ((hupper w).trans (subderivative_separableSum_ge hx hy w))
  refine ⟨isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mpr
    ⟨isLocallyLscAt_separableSum hf hg hx hy,he⟩,?_⟩
  intro w
  exact le_antisymm ((subderivative_le_regularSubderivative hxy w).trans (hupper w))
    (subderivative_separableSum_ge hx hy w)

/-- **Proposition 10.5**, equality in the horizon product formula for
regular summands under the stated zero-direction hypotheses. -/
theorem horizonSubdifferential_separableSum_eq_of_regular
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
    (hrf : IsSubdifferentiallyRegularAt f x) (hrg : IsSubdifferentiallyRegularAt g y)
    (hf0 : subderivative f x 0 = 0) (hg0 : subderivative g y 0 = 0) :
    horizonSubdifferential (separableSum f g) (WithLp.toLp 2 (x,y)) =
      {v | v.fst ∈ horizonSubdifferential f x ∧ v.snd ∈ horizonSubdifferential g y} := by
  have hx := (EReal.coe_toReal hrf.2.1 hrf.1).symm
  have hy := (EReal.coe_toReal hrg.2.1 hrg.1).symm
  have hreg := separableSum_regularity hf hg hrf hrg hf0 hg0
  apply Subset.antisymm (horizonSubdifferential_separableSum_subset (hf x) (hg y) hx hy)
  intro v hv
  rw [hreg.1.horizonSubdifferential_eq_polar_domain]
  rw [hrf.horizonSubdifferential_eq_polar_domain,hrg.horizonSubdifferential_eq_polar_domain] at hv
  intro w hw
  have hdf := (hrf.isProper_subderivative (by rw [hf0]; norm_num)).2 w.fst
  have hdg := (hrg.isProper_subderivative (by rw [hg0]; norm_num)).2 w.snd
  have hfin : subderivative f x w.fst ≠ ⊤ ∧ subderivative g y w.snd ≠ ⊤ :=
    (EReal.add_ne_top_iff_ne_top₂ hdf.ne' hdg.ne').mp (by
      exact (show subderivative f x w.fst+subderivative g y w.snd < ⊤ from (hreg.2 w) ▸ hw).ne)
  change ⟪v.fst,w.fst⟫_ℝ+⟪v.snd,w.snd⟫_ℝ ≤ 0
  exact add_nonpos (hv.1 _ (lt_top_iff_ne_top.mpr hfin.1)) (hv.2 _ (lt_top_iff_ne_top.mpr hfin.2))

end RW
