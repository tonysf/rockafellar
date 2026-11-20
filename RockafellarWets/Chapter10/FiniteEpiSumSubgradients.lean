/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subgradients of finite epi-sums
-/

import RockafellarWets.Chapter10.FiniteEpiAddition

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

@[simp] theorem epiSumShift_adjoint (q : WithLp 2 (PiLp 2 (fun _ : ι ↦ E) × E)) :
    (parameterShiftDerivative (-(l2CoordinateSum (ι := ι) (E := E)))).adjoint q =
      WithLp.toLp 2 (WithLp.toLp 2 (fun i ↦ q.fst i-q.snd),q.snd) := by
  rw [parameterShiftDerivative_adjoint,map_neg]
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply WithLp.ofLp_injective
    funext i
    simp [l2CoordinateSum_adjoint,sub_eq_add_neg]
  · rfl

private theorem epiSumShift_source_value {f : ι → E → EReal} {a : PiLp 2 (fun _ : ι ↦ E)}
    {u : E} {c : ι → ℝ} (ha : ∀ i, f i (a i) = c i) (hs : (∑ i, a i) = u) :
    separableSum (separablePi f) (indicatorVA ({0} : Set E))
      (parameterShift (-(l2CoordinateSum (ι := ι) (E := E))) (WithLp.toLp 2 (a,u))) =
      ((∑ i, c i : ℝ) : EReal) := by
  have h := finiteEpiSumIntegrand_apply f a u
  change separableSum _ _ _ = _ at h
  rw [h,hs,sub_self,indicatorVA_apply_mem (mem_singleton 0),add_zero]
  exact separablePi_eq_coe ha

/-- A horizontal regular subgradient is a common regular subgradient of
all summands at the chosen decomposition. -/
theorem regularSubgradient_finiteEpiSumIntegrand_iff {f : ι → E → EReal}
    {a : PiLp 2 (fun _ : ι ↦ E)} {u y : E} {c : ι → ℝ}
    (ha : ∀ i, f i (a i) = c i) (hs : (∑ i, a i) = u) :
    WithLp.toLp 2 ((0 : PiLp 2 (fun _ : ι ↦ E)),y) ∈
      regularSubdifferential (finiteEpiSumIntegrand f) (WithLp.toLp 2 (a,u)) ↔
      ∀ i, y ∈ regularSubdifferential (f i) (a i) := by
  let A := -(l2CoordinateSum (ι := ι) (E := E))
  have hd := hasFDerivAt_parameterShift A.hasFDerivAt u (x := a)
  have hh := regularSubdifferential_comp_eq_of_surjective (contDiff_parameterShift A.contDiff)
    (epiSumShift_source_value ha hs) (hd.fderiv.symm ▸ parameterShiftDerivative_surjective A)
  rw [hd.fderiv] at hh
  change regularSubdifferential (finiteEpiSumIntegrand f) (WithLp.toLp 2 (a,u)) = _ at hh
  rw [hh]
  have hbase : parameterShift A (WithLp.toLp 2 (a,u)) = WithLp.toLp 2 (a,(0:E)) := by
    simp [parameterShift,A,hs]
  rw [hbase]
  constructor
  · rintro ⟨q,hq,he⟩
    have hp := (mem_regularSubdifferential_separableSum_iff (separablePi_eq_coe ha)
      (indicatorVA_apply_mem (mem_singleton 0)) q).mp hq
    have hc := (mem_regularSubdifferential_separablePi_iff f a q.fst c ha).mp hp.1
    dsimp [A] at he
    rw [epiSumShift_adjoint] at he
    have hqy : q.snd = y := congrArg WithLp.snd he
    have hqi (i : ι) : q.fst i = y := by
      have h := congrArg (fun q : WithLp 2 (PiLp 2 (fun _ : ι ↦ E) × E) ↦ q.fst i) he
      change q.fst i-q.snd = 0 at h
      exact (sub_eq_zero.mp h).trans hqy
    exact fun i ↦ hqi i ▸ hc i
  · intro hy
    refine ⟨WithLp.toLp 2 (WithLp.toLp 2 (fun _ : ι ↦ y),y),?_,?_⟩
    · apply (mem_regularSubdifferential_separableSum_iff (separablePi_eq_coe ha)
        (indicatorVA_apply_mem (mem_singleton 0)) _).mpr
      constructor
      · exact (mem_regularSubdifferential_separablePi_iff f a _ c ha).mpr hy
      · simp [regularSubdifferential_indicatorVA,regularNormalCone_singleton]
    · simp [A,epiSumShift_adjoint]

/-- A horizontal limiting subgradient is a common limiting subgradient. -/
theorem subgradient_finiteEpiSumIntegrand_iff {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    {a : PiLp 2 (fun _ : ι ↦ E)} {u y : E} {c : ι → ℝ}
    (ha : ∀ i, f i (a i) = c i) (hs : (∑ i, a i) = u) :
    WithLp.toLp 2 ((0 : PiLp 2 (fun _ : ι ↦ E)),y) ∈
      subdifferential (finiteEpiSumIntegrand f) (WithLp.toLp 2 (a,u)) ↔
      ∀ i, y ∈ subdifferential (f i) (a i) := by
  let A := -(l2CoordinateSum (ι := ι) (E := E))
  have hd := hasFDerivAt_parameterShift A.hasFDerivAt u (x := a)
  have hh := subdifferential_comp_eq_of_surjective (contDiff_parameterShift A.contDiff)
    (epiSumShift_source_value ha hs) (hd.fderiv.symm ▸ parameterShiftDerivative_surjective A)
  rw [hd.fderiv] at hh
  change subdifferential (finiteEpiSumIntegrand f) (WithLp.toLp 2 (a,u)) = _ at hh
  rw [hh]
  have hbase : parameterShift A (WithLp.toLp 2 (a,u)) = WithLp.toLp 2 (a,(0:E)) := by
    simp [parameterShift,A,hs]
  rw [hbase]
  constructor
  · rintro ⟨q,hq,he⟩
    have hparts := (mem_subdifferential_separableSum_iff
      (lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2) a)
      (lowerSemicontinuous_indicatorVA isClosed_singleton 0)
      (separablePi_eq_coe ha) (indicatorVA_apply_mem (mem_singleton 0)) q).mp hq
    have hc := (mem_subdifferential_separablePi_iff f hp hf a q.fst c ha).mp hparts.1
    dsimp [A] at he
    rw [epiSumShift_adjoint] at he
    have hqy : q.snd = y := congrArg WithLp.snd he
    have hqi (i : ι) : q.fst i = y := by
      have h := congrArg (fun q : WithLp 2 (PiLp 2 (fun _ : ι ↦ E) × E) ↦ q.fst i) he
      change q.fst i-q.snd = 0 at h
      exact (sub_eq_zero.mp h).trans hqy
    exact fun i ↦ hqi i ▸ hc i
  · intro hy
    refine ⟨WithLp.toLp 2 (WithLp.toLp 2 (fun _ : ι ↦ y),y),?_,?_⟩
    · apply (mem_subdifferential_separableSum_iff
        (lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2) a)
        (lowerSemicontinuous_indicatorVA isClosed_singleton 0)
        (separablePi_eq_coe ha) (indicatorVA_apply_mem (mem_singleton 0)) _).mpr
      constructor
      · exact (mem_subdifferential_separablePi_iff f hp hf a _ c ha).mpr hy
      · simp [subdifferential_indicatorVA,normalCone_singleton]
    · simp [A,epiSumShift_adjoint]

/-- Horizontal horizon subgradients are common horizon subgradients. -/
theorem horizonSubgradient_finiteEpiSumIntegrand {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    {a : PiLp 2 (fun _ : ι ↦ E)} {u y : E} {c : ι → ℝ}
    (ha : ∀ i, f i (a i) = c i) (hs : (∑ i, a i) = u)
    (hy : WithLp.toLp 2 ((0 : PiLp 2 (fun _ : ι ↦ E)),y) ∈
      horizonSubdifferential (finiteEpiSumIntegrand f) (WithLp.toLp 2 (a,u))) :
    ∀ i, y ∈ horizonSubdifferential (f i) (a i) := by
  let A := -(l2CoordinateSum (ι := ι) (E := E))
  have hd := hasFDerivAt_parameterShift A.hasFDerivAt u (x := a)
  have hls := lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2)
  have hli := lowerSemicontinuous_indicatorVA (C := ({0}:Set E)) isClosed_singleton
  have hlg := lowerSemicontinuous_separableSum hls hli (isProper_separablePi hp)
    ((indicatorVA_isProper_iff _).mpr (singleton_nonempty 0))
  have hh := horizonSubdifferential_comp_eq_of_surjective (contDiff_parameterShift A.contDiff)
    hlg (epiSumShift_source_value ha hs) (hd.fderiv.symm ▸ parameterShiftDerivative_surjective A)
  rw [hd.fderiv] at hh
  change horizonSubdifferential (finiteEpiSumIntegrand f) (WithLp.toLp 2 (a,u)) = _ at hh
  rw [hh] at hy
  have hbase : parameterShift A (WithLp.toLp 2 (a,u)) = WithLp.toLp 2 (a,(0:E)) := by
    simp [parameterShift,A,hs]
  rw [hbase] at hy
  obtain ⟨q,hq,he⟩ := hy
  have hparts := horizonSubdifferential_separableSum_subset (hls a) (hli 0)
    (separablePi_eq_coe ha) (indicatorVA_apply_mem (mem_singleton 0)) hq
  have hc := horizonSubdifferential_separablePi_subset f hp hf a c ha hparts.1
  dsimp [A] at he
  rw [epiSumShift_adjoint] at he
  have hqy : q.snd = y := congrArg WithLp.snd he
  have hqi (i : ι) : q.fst i = y := by
    have h := congrArg (fun q : WithLp 2 (PiLp 2 (fun _ : ι ↦ E) × E) ↦ q.fst i) he
    change q.fst i-q.snd = 0 at h
    exact (sub_eq_zero.mp h).trans hqy
  exact fun i ↦ hqi i ▸ hc i

/-- The intersection of all common regular subgradients at optimal decompositions. -/
def regularEpiSumMultipliers (f : ι → E → EReal) (x : E) : Set E :=
  {y | ∀ a ∈ epiSumDecompositions f x, ∀ i, y ∈ regularSubdifferential (f i) (a i)}

/-- The union, over optimal decompositions, of componentwise intersections. -/
def epiSumMultipliers (f : ι → E → EReal) (x : E) : Set E :=
  {y | ∃ a ∈ epiSumDecompositions f x, ∀ i, y ∈ subdifferential (f i) (a i)}

/-- Common horizon subgradients at an optimal decomposition. -/
def horizonEpiSumMultipliers (f : ι → E → EReal) (x : E) : Set E :=
  {y | ∃ a ∈ epiSumDecompositions f x, ∀ i, y ∈ horizonSubdifferential (f i) (a i)}

theorem regularParametricMultipliers_finiteEpiSumIntegrand {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) :
    regularParametricMultipliers (finiteEpiSumIntegrand f) x = regularEpiSumMultipliers f x := by
  ext y
  simp only [regularParametricMultipliers,regularEpiSumMultipliers,mem_setOf_eq,
    parametricMinimizers_finiteEpiSumIntegrand hp]
  apply forall_congr'
  intro a
  apply forall_congr'
  intro ha
  obtain ⟨c,hc⟩ := separablePi_finite_components (ha.2.1.trans hx)
  exact regularSubgradient_finiteEpiSumIntegrand_iff hc ha.1

theorem parametricMultipliers_finiteEpiSumIntegrand {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) :
    parametricMultipliers (finiteEpiSumIntegrand f) x = epiSumMultipliers f x := by
  ext y
  simp only [parametricMultipliers,epiSumMultipliers,mem_setOf_eq,
    parametricMinimizers_finiteEpiSumIntegrand hp]
  apply exists_congr
  intro a
  apply and_congr_right
  intro ha
  obtain ⟨c,hc⟩ := separablePi_finite_components (ha.2.1.trans hx)
  exact subgradient_finiteEpiSumIntegrand_iff hp hf hc ha.1

theorem horizonParametricMultipliers_finiteEpiSumIntegrand_subset {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) :
    horizonParametricMultipliers (finiteEpiSumIntegrand f) x ⊆ horizonEpiSumMultipliers f x := by
  rintro y ⟨a,ha,hy⟩
  rw [parametricMinimizers_finiteEpiSumIntegrand hp] at ha
  obtain ⟨c,hc⟩ := separablePi_finite_components (ha.2.1.trans hx)
  exact ⟨a,ha,horizonSubgradient_finiteEpiSumIntegrand hp hf hc ha.1 hy⟩

/-- **Exercise 10.18**, the regular, limiting, and horizon inclusions,
with intersections across components. -/
theorem subdifferentials_finiteEpiSum_subset {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hb : HasBoundedEpiSumDecompositions f) {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) :
    regularSubdifferential (finiteEpiSumValue f) x ⊆ regularEpiSumMultipliers f x ∧
    subdifferential (finiteEpiSumValue f) x ⊆ epiSumMultipliers f x ∧
    horizonSubdifferential (finiteEpiSumValue f) x ⊆ horizonEpiSumMultipliers f x := by
  have hl := lowerSemicontinuous_finiteEpiSumIntegrand hp hf
  have hlev := isParametricallyLevelBounded_finiteEpiSumIntegrand hp hb
  refine ⟨?_,?_,?_⟩
  · rw [← regularParametricMultipliers_finiteEpiSumIntegrand hp hx]
    exact regularSubdifferential_parametricValue_subset hl hlev hx
  · rw [← parametricMultipliers_finiteEpiSumIntegrand hp hf hx]
    exact subdifferential_parametricValue_subset hl hlev hx
  · exact (horizonSubdifferential_parametricValue_subset hl hlev hx).trans
      (horizonParametricMultipliers_finiteEpiSumIntegrand_subset hp hf hx)

/-- **Exercise 10.18**, closedness and convexity of the regular multiplier
set, closedness of the limiting set, and the two comparison inclusions. -/
theorem finiteEpiSum_multiplier_properties {f : ι → E → EReal}
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (hb : HasBoundedEpiSumDecompositions f) {x : E} {r : ℝ} (hx : finiteEpiSumValue f x = r) :
    IsClosed (regularEpiSumMultipliers f x) ∧ Convex ℝ (regularEpiSumMultipliers f x) ∧
    IsClosed (epiSumMultipliers f x) ∧
    regularEpiSumMultipliers f x ⊆ epiSumMultipliers f x ∧
    horizonCone (epiSumMultipliers f x) ⊆ horizonEpiSumMultipliers f x := by
  have hl := lowerSemicontinuous_finiteEpiSumIntegrand hp hf
  have hlev := isParametricallyLevelBounded_finiteEpiSumIntegrand hp hb
  have he := regularParametricMultipliers_finiteEpiSumIntegrand hp hx
  have he' := parametricMultipliers_finiteEpiSumIntegrand hp hf hx
  have hreg := regularParametricMultipliers_closed_convex hx
  rw [he] at hreg
  refine ⟨hreg.1,hreg.2,?_,?_,?_⟩
  · rw [← he']
    exact (isClosed_parametricMultipliers hl hlev hx).1
  · rw [← he,← he']
    exact regularParametricMultipliers_subset
      (parametricMinimizers_nonempty hl (isProper_finiteEpiSumIntegrand hp) hlev
        (hx.trans_lt (EReal.coe_lt_top _)))
  · rw [← he']
    exact (horizonCone_parametricMultipliers_subset hl hlev hx).trans
      (horizonParametricMultipliers_finiteEpiSumIntegrand_subset hp hf hx)

end

end RW
