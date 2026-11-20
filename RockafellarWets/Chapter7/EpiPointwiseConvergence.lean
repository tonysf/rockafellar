/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pointwise, epigraphical and continuous convergence

Theorems 7.10 and 7.11 use the Chapter 5 definitions of asymptotic
equi-semicontinuity of the profiles. These definitions test bounded heights
and apply throughout the extended reals.
-/
import RockafellarWets.Chapter7.EpiLimitCharacterization
import RockafellarWets.Chapter7.ProfileConvergence
import RockafellarWets.Chapter5.GraphicalContinuousConvergence

open Filter Set Topology

namespace RW

variable {E : Type*} [PseudoMetricSpace E] {f : ℕ → E → EReal} {g : E → EReal}
variable {X : Set E} {x : E}

/-- Epi-convergence at a point with arguments restricted to a set. -/
def EpiConvergesWithinAt (f : ℕ → E → EReal) (g : E → EReal) (X : Set E) (x : E) : Prop :=
  GraphicalConvergesWithinAt (fun n ↦ epiProfile (f n)) (epiProfile g) X x

theorem epiConverges_iff_forall_epiConvergesWithinAt :
    EpiConverges f g ↔ ∀ x, EpiConvergesWithinAt f g univ x := by
  rw [epiConverges_iff_graphicalConverges, graphicalConverges_iff_forall_graphicalConvergesAt]
  exact forall_congr' fun _ ↦ graphicalConvergesWithinAt_univ_iff.symm

/-- The hypographical counterpart of relative epi-convergence. -/
def HypoConvergesWithinAt (f : ℕ → E → EReal) (g : E → EReal) (X : Set E) (x : E) : Prop :=
  GraphicalConvergesWithinAt (fun n ↦ hypoProfile (f n)) (hypoProfile g) X x

/-- Asymptotic equi-lower semicontinuity, defined using the epi profiles. -/
def AsymptoticallyEquiLscWithinAt (f : ℕ → E → EReal) (X : Set E) (x : E) : Prop :=
  SvAsymptoticallyEquiOscWithinAt (fun n ↦ epiProfile (f n)) X x

/-- Asymptotic equi-upper semicontinuity, defined using the hypo profiles. -/
def AsymptoticallyEquiUscWithinAt (f : ℕ → E → EReal) (X : Set E) (x : E) : Prop :=
  SvAsymptoticallyEquiOscWithinAt (fun n ↦ hypoProfile (f n)) X x

/-- **Theorem 7.10**, equality of both lower and both upper limit values. -/
theorem epiLimits_eq_pointwiseLimits_of_asymptoticallyEquiLsc
    (h : AsymptoticallyEquiLscWithinAt f univ x) :
    epiLowerLimit f x = liminf (fun n ↦ f n x) atTop ∧
      epiUpperLimit f x = limsup (fun n ↦ f n x) atTop := by
  constructor
  · refine le_antisymm (epiLowerLimit_le_liminf tendsto_const_nhds) ?_
    by_contra! hlt
    obtain ⟨b, hlb, hb⟩ := EReal.exists_between_coe_real hlt
    have ho : b ∈ graphicalOuterLimit (fun n ↦ epiProfile (f n)) x := by
      change (x, b) ∈ outerSetLimit (fun n ↦ epigraph (f n))
      rw [← epigraph_epiLowerLimit]
      exact hlb.le
    rw [graphicalOuterLimit_eq_pointwiseOuterLimit h] at ho
    have hi : outerSetLimitAlong (map (fun n ↦ f n x) atTop) (epiProfile id) ⊆
        epiProfile id (liminf (fun n ↦ f n x) atTop) := by
      apply (outerSetLimitAlong_epiProfile_subset_iff ..).2
      exact ((le_liminf_iff).1 le_rfl)
    exact hb.not_ge (hi ho)
  · refine le_antisymm (epiUpperLimit_le_limsup tendsto_const_nhds) ?_
    have hi : epiProfile id (epiUpperLimit f x) ⊆
        innerSetLimitAlong (map (fun n ↦ f n x) atTop) (epiProfile id) := by
      intro b hb
      have hm : b ∈ graphicalInnerLimit (fun n ↦ epiProfile (f n)) x := by
        change (x, b) ∈ innerSetLimit (fun n ↦ epigraph (f n))
        rw [← epigraph_epiUpperLimit]
        exact hb
      rwa [graphicalInnerLimit_eq_pointwiseInnerLimit h] at hm
    exact (limsup_le_iff).2 ((epiProfile_subset_innerSetLimitAlong_iff ..).1 hi)

/-- **Theorem 7.10**, the global convergence equivalence. -/
theorem epiConverges_iff_pointwise_of_asymptoticallyEquiLsc
    (h : ∀ x, AsymptoticallyEquiLscWithinAt f univ x) :
    EpiConverges f g ↔ ∀ x, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
  rw [epiConverges_iff_graphicalConverges, graphicalConverges_iff_pointwiseConverges h]
  exact forall_congr' fun x ↦ pkConverges_epiProfile_iff_tendsto _ _

/-- Theorem 7.10 relative to a set: (a) and (b) imply (c). -/
theorem EpiConvergesWithinAt.tendsto_of_asymptoticallyEquiLsc (hx : x ∈ X)
    (hb : EpiConvergesWithinAt f g X x) (ha : AsymptoticallyEquiLscWithinAt f X x) :
    Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) :=
  (pkConverges_epiProfile_iff_tendsto ..).1
    (PointwiseConvergesAt.of_graphicalConvergesWithinAt hx ha hb)

/-- Theorem 7.10 relative to a set: (a) and (c) imply (b). -/
theorem epiConvergesWithinAt_of_tendsto_of_asymptoticallyEquiLsc (hx : x ∈ X)
    (hc : Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) (ha : AsymptoticallyEquiLscWithinAt f X x) :
    EpiConvergesWithinAt f g X x :=
  GraphicalConvergesWithinAt.of_pointwiseConvergesAt hx ha
    ((pkConverges_epiProfile_iff_tendsto ..).2 hc)

/-- Theorem 7.10 relative to a set: (b) and (c) imply (a). -/
theorem EpiConvergesWithinAt.asymptoticallyEquiLsc_of_tendsto (hx : x ∈ X)
    (hb : EpiConvergesWithinAt f g X x) (hc : Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    AsymptoticallyEquiLscWithinAt f X x :=
  svAsymptoticallyEquiOscWithinAt_of_graphicalConvergesWithinAt_of_pointwiseConvergesAt hx hb
    ((pkConverges_epiProfile_iff_tendsto ..).2 hc)

/-- **Theorem 7.11** (a) ↔ (b): both graphical inequalities for the epi and
hypo profiles force convergence along each sequence of arguments. -/
theorem convergesContinuouslyWithinAt_iff_epi_and_hypo (hx : x ∈ X) :
    ConvergesContinuouslyWithinAt f g X x ↔
      EpiConvergesWithinAt f g X x ∧ HypoConvergesWithinAt f g X x := by
  constructor
  · intro h
    exact ⟨(svConvergesContinuouslyWithinAt_epiProfile_iff.2 h).graphicalConvergesWithinAt hx,
      (svConvergesContinuouslyWithinAt_hypoProfile_iff.2 h).graphicalConvergesWithinAt hx⟩
  · rintro ⟨he, hh⟩ z hz hzx
    let l := map (fun n ↦ f n (z n)) atTop
    have hlo : outerSetLimitAlong l (epiProfile id) ⊆ epiProfile id (g x) := by
      intro b hb
      exact he.1 (mem_graphicalOuterLimitWithin_iff.2 ⟨z, ⟨hz, hzx⟩, hb⟩)
    have hhi : outerSetLimitAlong l (hypoProfile id) ⊆ hypoProfile id (g x) := by
      intro b hb
      exact hh.1 (mem_graphicalOuterLimitWithin_iff.2 ⟨z, ⟨hz, hzx⟩, hb⟩)
    exact tendsto_order.2 ⟨(outerSetLimitAlong_epiProfile_subset_iff ..).1 hlo,
      (outerSetLimitAlong_hypoProfile_subset_iff ..).1 hhi⟩

private theorem equiSemicontinuity_of_continuous (hx : x ∈ X)
    (h : ConvergesContinuouslyWithinAt f g X x) :
    AsymptoticallyEquiLscWithinAt f X x ∧ AsymptoticallyEquiUscWithinAt f X x := by
  have he := svConvergesContinuouslyWithinAt_epiProfile_iff.2 h
  have hh := svConvergesContinuouslyWithinAt_hypoProfile_iff.2 h
  exact ⟨(he.svAsymptoticallyEquicontinuousWithinAt hx).2,
    (hh.svAsymptoticallyEquicontinuousWithinAt hx).2⟩

/-- **Theorem 7.11** (a) ↔ (c), using asymptotic equi-semicontinuity of
both profiles. -/
theorem convergesContinuouslyWithinAt_iff_epi_and_equiSemicontinuity (hx : x ∈ X) :
    ConvergesContinuouslyWithinAt f g X x ↔ EpiConvergesWithinAt f g X x ∧
      AsymptoticallyEquiLscWithinAt f X x ∧ AsymptoticallyEquiUscWithinAt f X x := by
  constructor
  · intro h
    exact ⟨((convergesContinuouslyWithinAt_iff_epi_and_hypo hx).1 h).1,
      equiSemicontinuity_of_continuous hx h⟩
  · rintro ⟨he, hl, hu⟩
    apply (convergesContinuouslyWithinAt_iff_epi_and_hypo hx).2
    exact ⟨he, GraphicalConvergesWithinAt.of_pointwiseConvergesAt hx hu
      ((pkConverges_hypoProfile_iff_tendsto ..).2 (he.tendsto_of_asymptoticallyEquiLsc hx hl))⟩

/-- **Theorem 7.11** (a) ↔ (d), the corresponding hypographical formula. -/
theorem convergesContinuouslyWithinAt_iff_hypo_and_equiSemicontinuity (hx : x ∈ X) :
    ConvergesContinuouslyWithinAt f g X x ↔ HypoConvergesWithinAt f g X x ∧
      AsymptoticallyEquiLscWithinAt f X x ∧ AsymptoticallyEquiUscWithinAt f X x := by
  constructor
  · intro h
    exact ⟨((convergesContinuouslyWithinAt_iff_epi_and_hypo hx).1 h).2,
      equiSemicontinuity_of_continuous hx h⟩
  · rintro ⟨hh, hl, hu⟩
    have hpoint : PointwiseConvergesAt (fun n ↦ hypoProfile (f n)) (hypoProfile g) x :=
      PointwiseConvergesAt.of_graphicalConvergesWithinAt hx hu hh
    have hp := (pkConverges_hypoProfile_iff_tendsto (fun n ↦ f n x) (g x)).1 hpoint
    exact (convergesContinuouslyWithinAt_iff_epi_and_hypo hx).2
      ⟨epiConvergesWithinAt_of_tendsto_of_asymptoticallyEquiLsc hx hp hl, hh⟩

end RW
