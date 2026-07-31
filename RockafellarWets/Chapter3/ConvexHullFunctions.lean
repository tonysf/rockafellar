/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3F: Convex Hulls of Coercive Functions

This file formalizes the epigraphical core of Corollary 3.47:

* the convex hull of a function is the lower boundary of the convex hull of
  its epigraph;
* coercivity forces the horizon cone of the epigraph to be the nonnegative
  vertical ray;
* consequently, for a proper lower-semicontinuous coercive function in finite
  dimension, the convexified epigraph is closed and the convex hull function
  is proper, lower-semicontinuous, and coercive;
* every value on the effective domain is realized by a finite convex
  combination of points in the original effective domain.

The final finite representation below has the ambient Carathéodory bound
`finrank E + 2`.  The sharper `finrank E + 1` bound in Proposition 2.31 needs
the boundary-point refinement of Carathéodory's theorem, which is not yet
present in the Chapter 2 API.
-/

import RockafellarWets.Chapter3.Coercivity
import RockafellarWets.Chapter3.CosmicClosure

open Set EReal Filter Topology
open scoped BigOperators Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The nonnegative vertical ray in `E × ℝ`. -/
def nonnegativeVerticalRay : Set (E × ℝ) :=
  ({0} : Set E) ×ˢ Set.Ici 0

omit [NormedSpace ℝ E] in
@[simp]
theorem mem_nonnegativeVerticalRay_iff {p : E × ℝ} :
    p ∈ nonnegativeVerticalRay (E := E) ↔ p.1 = 0 ∧ 0 ≤ p.2 :=
  Iff.rfl

/-- The nonnegative vertical ray is convex. -/
theorem convex_nonnegativeVerticalRay :
    Convex ℝ (nonnegativeVerticalRay (E := E)) :=
  convex_singleton 0 |>.prod (convex_Ici 0)

/-- The nonnegative vertical ray is pointed. -/
theorem isPointed_nonnegativeVerticalRay :
    IsPointed (nonnegativeVerticalRay (E := E)) := by
  intro n z hz hsum i
  have hsecond : ∑ j, (z j).2 = 0 := by
    have h := congrArg (LinearMap.snd ℝ E ℝ) hsum
    rw [map_sum] at h
    simpa using h
  have hsecond_nonneg : ∀ j, 0 ≤ (z j).2 := fun j => (hz j).2
  have hsecond_zero_fun : (fun j => (z j).2) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg hsecond_nonneg).mp hsecond
  have hsecond_zero : ∀ j, (z j).2 = 0 := by
    intro j
    simpa using congrFun hsecond_zero_fun j
  have hfirst_zero : (z i).1 = 0 := (hz i).1
  exact Prod.ext hfirst_zero (hsecond_zero i)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The epigraph of a function is upward closed in its real coordinate. -/
theorem add_nonnegative_vertical_mem_epigraph
    {f : E → EReal} {x : E} {a d : ℝ}
    (ha : (x, a) ∈ epigraph f) (hd : 0 ≤ d) :
    (x, a + d) ∈ epigraph f := by
  rw [mem_epigraph_iff] at ha ⊢
  exact ha.trans (by exact_mod_cast le_add_of_nonneg_right hd)

/-- Upward closure in the real coordinate is inherited by the convex hull of
an epigraph. -/
theorem add_nonnegative_vertical_mem_convexHull_epigraph
    {f : E → EReal} {p : E × ℝ} {d : ℝ}
    (hp : p ∈ convexHull ℝ (epigraph f)) (hd : 0 ≤ d) :
    (p.1, p.2 + d) ∈ convexHull ℝ (epigraph f) := by
  let A : (E × ℝ) →ᵃ[ℝ] (E × ℝ) := {
    toFun q := (q.1, q.2 + d)
    linear := LinearMap.id
    map_vadd' q v := by
      ext <;> simp [add_left_comm, add_comm] }
  have hgenerators :
      epigraph f ⊆ A ⁻¹' convexHull ℝ (epigraph f) := by
    intro q hq
    apply subset_convexHull ℝ (epigraph f)
    exact add_nonnegative_vertical_mem_epigraph hq hd
  have hpreimage : Convex ℝ (A ⁻¹' convexHull ℝ (epigraph f)) :=
    (convex_convexHull ℝ (epigraph f)).affine_preimage A
  have hpA : p ∈ A ⁻¹' convexHull ℝ (epigraph f) :=
    convexHull_min hgenerators hpreimage hp
  exact hpA

/-- The epigraph determined by an affine norm lower bound. -/
private def affineNormEpigraph (γ β : ℝ) : Set (E × ℝ) :=
  {p | γ * ‖p.1‖ + β ≤ p.2}

private theorem affineNormEpigraph_convex {γ β : ℝ} (hγ : 0 ≤ γ) :
    Convex ℝ (affineNormEpigraph (E := E) γ β) := by
  let g : E → ℝ := fun x => γ * ‖x‖ + β
  have hg : ConvexOn ℝ Set.univ g := by
    simpa [g, smul_eq_mul] using (convexOn_univ_norm.smul hγ).add_const β
  have hepi : Convex ℝ {p : E × ℝ | p.1 ∈ Set.univ ∧ g p.1 ≤ p.2} :=
    (convex_epigraph_iff_convexOn g Set.univ convex_univ).2 hg
  simpa [affineNormEpigraph, g] using hepi

omit [NormedSpace ℝ E] in
private theorem affineNormEpigraph_isClosed (γ β : ℝ) :
    IsClosed (affineNormEpigraph (E := E) γ β) := by
  apply isClosed_le
  · exact
      (continuous_const.mul (continuous_norm.comp continuous_fst)).add
        continuous_const
  · exact continuous_snd

omit [NormedSpace ℝ E] in
private theorem zero_beta_mem_affineNormEpigraph {γ β : ℝ} :
    ((0 : E), β) ∈ affineNormEpigraph (E := E) γ β := by
  simp [affineNormEpigraph]

/-- An affine norm lower bound traps every epigraph horizon direction above
the corresponding homogeneous norm cone. -/
theorem norm_bound_of_mem_horizonCone_epigraph
    {f : E → EReal} {γ β : ℝ} (hγ : 0 ≤ γ)
    (hminor : HasAffineNormLowerBound f γ β)
    {w : E} {a : ℝ} (hwa : (w, a) ∈ horizonCone (epigraph f)) :
    γ * ‖w‖ ≤ a := by
  have hepi :
      epigraph f ⊆ affineNormEpigraph (E := E) γ β := by
    intro p hp
    rw [mem_epigraph_iff] at hp
    exact_mod_cast (hminor p.1).trans hp
  have hwa' :
      (w, a) ∈ horizonCone (affineNormEpigraph (E := E) γ β) :=
    horizonCone_mono hepi hwa
  have hray :
      (1 : ℝ) • (w, a) + ((0 : E), β) ∈
        affineNormEpigraph (E := E) γ β :=
    smul_add_mem_of_mem_horizonCone
      (affineNormEpigraph_convex (E := E) hγ)
      (affineNormEpigraph_isClosed (E := E) γ β)
      zero_beta_mem_affineNormEpigraph hwa' zero_le_one
  simpa [affineNormEpigraph] using hray

/-- Coercivity forces every horizon direction of the epigraph to be vertical
and nonnegative. -/
theorem horizonCone_epigraph_subset_nonnegativeVerticalRay_of_isCoercive
    {f : E → EReal} (hf : IsCoercive f) :
    horizonCone (epigraph f) ⊆ nonnegativeVerticalRay (E := E) := by
  rintro ⟨w, a⟩ hwa
  have ha : 0 ≤ a := by
    obtain ⟨β, hβ⟩ := hf 1 zero_lt_one
    have hbound :=
      norm_bound_of_mem_horizonCone_epigraph
        (E := E) (γ := 1) (β := β) zero_le_one hβ hwa
    have hbound' : ‖w‖ ≤ a := by simpa using hbound
    exact (norm_nonneg w).trans hbound'
  have hw : w = 0 := by
    by_contra hw0
    let γ : ℝ := (|a| + 1) / ‖w‖
    have hγ : 0 < γ := by
      unfold γ
      positivity
    obtain ⟨β, hβ⟩ := hf γ hγ
    have hbound :
        γ * ‖w‖ ≤ a :=
      norm_bound_of_mem_horizonCone_epigraph
        (E := E) hγ.le hβ hwa
    have hγnorm : γ * ‖w‖ = |a| + 1 := by
      unfold γ
      field_simp [norm_ne_zero_iff.mpr hw0]
    rw [hγnorm] at hbound
    linarith [le_abs_self a]
  exact ⟨hw, ha⟩

/-- Properness supplies the reverse inclusion: every nonnegative vertical
direction is a horizon direction of the epigraph. -/
theorem nonnegativeVerticalRay_subset_horizonCone_epigraph_of_isProper
    {f : E → EReal} (hproper : IsProper f) :
    nonnegativeVerticalRay (E := E) ⊆ horizonCone (epigraph f) := by
  rcases epigraph_nonempty_of_isProper hproper with ⟨⟨x, b⟩, hxb⟩
  rintro ⟨w, a⟩ hwa
  have hw : w = 0 := (mem_nonnegativeVerticalRay_iff.mp hwa).1
  have ha : 0 ≤ a := (mem_nonnegativeVerticalRay_iff.mp hwa).2
  subst w
  apply mem_horizonCone_of_forall_smul_add_mem
    (C := epigraph f) (x := (x, b)) (w := ((0 : E), a))
  intro τ hτ
  rw [mem_epigraph_iff] at hxb ⊢
  have hab : b ≤ τ * a + b := le_add_of_nonneg_left (mul_nonneg hτ ha)
  have hab' : (b : EReal) ≤ ((τ * a + b : ℝ) : EReal) := by
    exact_mod_cast hab
  simpa [Prod.smul_mk, smul_eq_mul] using hxb.trans hab'

/-- For a proper coercive function, the horizon cone of the epigraph is
exactly the nonnegative vertical ray. -/
theorem horizonCone_epigraph_eq_nonnegativeVerticalRay
    {f : E → EReal} (hproper : IsProper f) (hf : IsCoercive f) :
    horizonCone (epigraph f) = nonnegativeVerticalRay (E := E) :=
  le_antisymm
    (horizonCone_epigraph_subset_nonnegativeVerticalRay_of_isCoercive hf)
    (nonnegativeVerticalRay_subset_horizonCone_epigraph_of_isProper hproper)

/-- A proper coercive function has a pointed epigraph horizon cone. -/
theorem isPointed_horizonCone_epigraph_of_isCoercive
    {f : E → EReal} (hproper : IsProper f) (hf : IsCoercive f) :
    IsPointed (horizonCone (epigraph f)) := by
  rw [horizonCone_epigraph_eq_nonnegativeVerticalRay hproper hf]
  exact isPointed_nonnegativeVerticalRay

/-- The convex hull of the epigraph of a proper lsc coercive function is
closed.  This is the set-theoretic core of Corollary 3.47. -/
theorem isClosed_convexHull_epigraph_of_isCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hf : IsCoercive f) :
    IsClosed (convexHull ℝ (epigraph f)) := by
  apply isClosed_of_closure_subset
  rw [closure_convexHull_eq_add_convexHull_horizonCone
    (isClosed_epigraph_of_lsc_ereal f hlsc)
    (isPointed_horizonCone_epigraph_of_isCoercive hproper hf)]
  rintro p ⟨q, hq, r, hr, rfl⟩
  have hrVertical : r ∈ nonnegativeVerticalRay (E := E) := by
    apply
      convexHull_min
        (horizonCone_epigraph_subset_nonnegativeVerticalRay_of_isCoercive hf)
        convex_nonnegativeVerticalRay
        hr
  rcases q with ⟨x, a⟩
  rcases r with ⟨w, d⟩
  rcases hrVertical with ⟨rfl, hd⟩
  simpa using
    add_nonnegative_vertical_mem_convexHull_epigraph
      (f := f) (p := (x, a)) hq hd

/-- The convex hull function is the lower boundary of the convex hull of the
original epigraph. -/
noncomputable def convexHullFunction (f : E → EReal) (x : E) : EReal :=
  ⨅ a : {a : ℝ // (x, a) ∈ convexHull ℝ (epigraph f)}, (a : EReal)

/-- Every point in the convexified epigraph lies on or above the convex hull
function. -/
theorem convexHullFunction_le_of_mem_convexHull_epigraph
    {f : E → EReal} {x : E} {a : ℝ}
    (ha : (x, a) ∈ convexHull ℝ (epigraph f)) :
    convexHullFunction f x ≤ (a : EReal) :=
  iInf_le
    (fun b : {a : ℝ // (x, a) ∈ convexHull ℝ (epigraph f)} => (b : EReal))
    ⟨a, ha⟩

/-- The convexified epigraph is always contained in the epigraph of the convex
hull function. -/
theorem convexHull_epigraph_subset_epigraph_convexHullFunction
    (f : E → EReal) :
    convexHull ℝ (epigraph f) ⊆ epigraph (convexHullFunction f) := by
  rintro ⟨x, a⟩ hxa
  rw [mem_epigraph_iff]
  exact convexHullFunction_le_of_mem_convexHull_epigraph hxa

/-- If the convexified epigraph is closed, its lower-boundary function has
exactly that epigraph. -/
theorem epigraph_convexHullFunction_eq
    {f : E → EReal} (hne : (epigraph f).Nonempty)
    (hclosed : IsClosed (convexHull ℝ (epigraph f))) :
    epigraph (convexHullFunction f) = convexHull ℝ (epigraph f) := by
  apply le_antisymm
  · rintro ⟨x, α⟩ hxα
    have hα : convexHullFunction f x ≤ (α : EReal) := by
      simpa [mem_epigraph_iff] using hxα
    let A : Type := {a : ℝ // (x, a) ∈ convexHull ℝ (epigraph f)}
    have hfun :
        convexHullFunction f x = ⨅ a : A, (a : EReal) := by
      rfl
    have hA_nonempty : Nonempty A := by
      rcases hne with ⟨⟨y, b⟩, hyb⟩
      have hyb' : (y, b) ∈ convexHull ℝ (epigraph f) :=
        subset_convexHull ℝ (epigraph f) hyb
      by_contra hA
      letI : IsEmpty A := not_nonempty_iff.mp hA
      have htop : convexHullFunction f x = ⊤ := by
        rw [convexHullFunction]
        exact iInf_of_empty _
      rw [htop] at hα
      simp at hα
    letI : Nonempty A := hA_nonempty
    by_cases hlt : convexHullFunction f x < (α : EReal)
    · have hltA : (⨅ a : A, (a : EReal)) < (α : EReal) := by
        simpa [hfun] using hlt
      obtain ⟨b, hb⟩ := exists_lt_of_ciInf_lt hltA
      have hb_real : (b : ℝ) < α := by
        exact_mod_cast hb
      have hmem :=
        add_nonnegative_vertical_mem_convexHull_epigraph
          (f := f) (p := (x, (b : ℝ))) (d := α - (b : ℝ))
          b.property (sub_nonneg.mpr hb_real.le)
      simpa using hmem
    · have hEq : convexHullFunction f x = (α : EReal) :=
        le_antisymm hα (le_of_not_gt hlt)
      have happrox :
          ∀ n : ℕ, ∃ a : A,
            (a : EReal) < ((α + ((n : ℝ) + 1)⁻¹ : ℝ) : EReal) := by
        intro n
        have hltα :
            (α : EReal) < ((α + ((n : ℝ) + 1)⁻¹ : ℝ) : EReal) := by
          exact_mod_cast
            (lt_add_of_pos_right α (by positivity : 0 < ((n : ℝ) + 1)⁻¹))
        have hltn :
            convexHullFunction f x <
              ((α + ((n : ℝ) + 1)⁻¹ : ℝ) : EReal) := by
          simpa [hEq] using hltα
        have hltA :
            (⨅ a : A, (a : EReal)) <
              ((α + ((n : ℝ) + 1)⁻¹ : ℝ) : EReal) := by
          simpa [hfun] using hltn
        exact exists_lt_of_ciInf_lt hltA
      choose b hb using happrox
      have hb_lower : ∀ n : ℕ, (α : EReal) ≤ ((b n : A) : EReal) := by
        intro n
        calc
          (α : EReal) = convexHullFunction f x := hEq.symm
          _ = ⨅ a : A, (a : EReal) := hfun
          _ ≤ ((b n : A) : EReal) := iInf_le _ (b n)
      have hb_lower_real : ∀ n : ℕ, α ≤ ((b n : A) : ℝ) := by
        intro n
        exact_mod_cast hb_lower n
      have hb_upper_real :
          ∀ n : ℕ, ((b n : A) : ℝ) ≤ α + ((n : ℝ) + 1)⁻¹ := by
        intro n
        exact_mod_cast le_of_lt (hb n)
      have hupper_tendsto :
          Tendsto (fun n : ℕ => α + ((n : ℝ) + 1)⁻¹) atTop (𝓝 α) := by
        simpa [one_div] using
          (tendsto_const_nhds (x := α)).add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hb_tendsto :
          Tendsto (fun n : ℕ => ((b n : A) : ℝ)) atTop (𝓝 α) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds hupper_tendsto hb_lower_real hb_upper_real
      have hp_tendsto :
          Tendsto (fun n : ℕ => (x, ((b n : A) : ℝ))) atTop (𝓝 (x, α)) := by
        have hpair :
            Tendsto (fun a : ℝ => (x, a)) (𝓝 α) (𝓝 (x, α)) := by
          simpa using
            (continuous_const.prodMk continuous_id).continuousAt.tendsto
        exact hpair.comp hb_tendsto
      have hb_mem :
          ∀ᶠ n in atTop,
            (x, ((b n : A) : ℝ)) ∈ convexHull ℝ (epigraph f) :=
        Filter.Eventually.of_forall fun n => (b n).property
      exact hclosed.mem_of_tendsto hp_tendsto hb_mem
  · exact convexHull_epigraph_subset_epigraph_convexHullFunction f

/-- For a proper lsc coercive function, the epigraph of its convex hull
function is exactly the convex hull of its original epigraph. -/
theorem epigraph_convexHullFunction_eq_of_isCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hf : IsCoercive f) :
    epigraph (convexHullFunction f) = convexHull ℝ (epigraph f) :=
  epigraph_convexHullFunction_eq
    (epigraph_nonempty_of_isProper hproper)
    (isClosed_convexHull_epigraph_of_isCoercive hlsc hproper hf)

/-- The convex hull function of a proper lsc coercive function is convex,
expressed in the project's epigraph convention. -/
theorem convex_epigraph_convexHullFunction_of_isCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hf : IsCoercive f) :
    Convex ℝ (epigraph (convexHullFunction f)) := by
  rw [epigraph_convexHullFunction_eq_of_isCoercive hlsc hproper hf]
  exact convex_convexHull ℝ (epigraph f)

/-- The convex hull function of a proper lsc coercive function is lower
semicontinuous. -/
theorem lowerSemicontinuous_convexHullFunction_of_isCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hf : IsCoercive f) :
    LowerSemicontinuous (convexHullFunction f) := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  rw [epigraph_convexHullFunction_eq_of_isCoercive hlsc hproper hf]
  exact isClosed_convexHull_epigraph_of_isCoercive hlsc hproper hf

/-- An affine norm lower bound passes from a function to its convex hull
function. -/
theorem HasAffineNormLowerBound.convexHullFunction
    {f : E → EReal} {γ β : ℝ} (hγ : 0 ≤ γ)
    (hminor : HasAffineNormLowerBound f γ β) :
    HasAffineNormLowerBound (convexHullFunction f) γ β := by
  intro x
  rw [RW.convexHullFunction]
  refine le_iInf fun a => ?_
  have hepi :
      epigraph f ⊆ affineNormEpigraph (E := E) γ β := by
    intro p hp
    rw [mem_epigraph_iff] at hp
    exact_mod_cast (hminor p.1).trans hp
  have ha : γ * ‖x‖ + β ≤ (a : ℝ) :=
    convexHull_min hepi (affineNormEpigraph_convex (E := E) hγ) a.property
  exact_mod_cast ha

/-- Coercivity passes from a function to its convex hull function. -/
theorem IsCoercive.convexHullFunction
    {f : E → EReal} (hf : IsCoercive f) :
    IsCoercive (convexHullFunction f) := by
  intro γ hγ
  obtain ⟨β, hminor⟩ := hf γ hγ
  exact ⟨β, hminor.convexHullFunction hγ.le⟩

/-- The convex hull function lies below the original proper function. -/
theorem convexHullFunction_le
    {f : E → EReal} (hproper : IsProper f) (x : E) :
    convexHullFunction f x ≤ f x := by
  by_cases htop : f x = ⊤
  · simp [htop]
  have hbot : f x ≠ ⊥ := ne_of_gt (hproper.2 x)
  have hgraph : (x, (f x).toReal) ∈ epigraph f := by
    rw [mem_epigraph_iff, EReal.coe_toReal htop hbot]
  calc
    convexHullFunction f x ≤ ((f x).toReal : EReal) :=
      convexHullFunction_le_of_mem_convexHull_epigraph
        (subset_convexHull ℝ (epigraph f) hgraph)
    _ = f x := EReal.coe_toReal htop hbot

/-- The convex hull function of a proper coercive function is proper. -/
theorem isProper_convexHullFunction
    {f : E → EReal} (hproper : IsProper f) (hf : IsCoercive f) :
    IsProper (convexHullFunction f) := by
  constructor
  · obtain ⟨x, hx⟩ := hproper.1
    exact ⟨x, (convexHullFunction_le hproper x).trans_lt hx⟩
  · intro x
    obtain ⟨β, hminor⟩ := hf 1 zero_lt_one
    have hlower :=
      hminor.convexHullFunction (E := E) zero_le_one x
    exact (EReal.bot_lt_coe (‖x‖ + β)).trans_le (by simpa using hlower)

/-- Corollary 3.47, regularity part: the convex hull function of a proper lsc
coercive function is proper, lsc, coercive, and convex. -/
theorem convexHullFunction_regular_of_isCoercive
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hf : IsCoercive f) :
    IsProper (convexHullFunction f) ∧
      LowerSemicontinuous (convexHullFunction f) ∧
      IsCoercive (convexHullFunction f) ∧
      Convex ℝ (epigraph (convexHullFunction f)) :=
  ⟨isProper_convexHullFunction hproper hf,
    lowerSemicontinuous_convexHullFunction_of_isCoercive hlsc hproper hf,
    hf.convexHullFunction,
    convex_epigraph_convexHullFunction_of_isCoercive hlsc hproper hf⟩

/-- Corollary 3.47, domain part: the effective domain of the convex hull
function is the convex hull of the original effective domain. -/
theorem effectiveDomain_convexHullFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hf : IsCoercive f) :
    effectiveDomain (convexHullFunction f) =
      convexHull ℝ (effectiveDomain f) := by
  rw [← epigraph_proj_eq_effectiveDomain (convexHullFunction f),
    epigraph_convexHullFunction_eq_of_isCoercive hlsc hproper hf]
  change (LinearMap.fst ℝ E ℝ) '' convexHull ℝ (epigraph f) =
    convexHull ℝ (effectiveDomain f)
  rw [LinearMap.image_convexHull]
  change convexHull ℝ (Prod.fst '' epigraph f) =
    convexHull ℝ (effectiveDomain f)
  rw [epigraph_proj_eq_effectiveDomain]

/-- Corollary 3.47, attainment part.  Every finite value of the convex hull
function is attained by a convex combination of values of the original
function.  The selected family has at most `finrank E + 2` members, the
ambient Carathéodory bound obtained by applying Theorem 2.29 in `E × ℝ`.

The points are indexed by a finite set of epigraph points; only their first
coordinates and the corresponding values of `f` occur in the resulting
convex combination. -/
theorem exists_finite_convexCombination_eq_convexHullFunction
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hf : IsCoercive f) {x : E}
    (hx : x ∈ effectiveDomain (convexHullFunction f)) :
    ∃ (T : Finset (E × ℝ)) (w : E × ℝ → ℝ),
      T.card ≤ Module.finrank ℝ E + 2 ∧
      (∀ p ∈ T, 0 ≤ w p) ∧
      ∑ p ∈ T, w p = 1 ∧
      (∀ p ∈ T, p.1 ∈ effectiveDomain f) ∧
      ∑ p ∈ T, w p • p.1 = x ∧
      ∑ p ∈ T, w p * (f p.1).toReal =
        (convexHullFunction f x).toReal := by
  let g : E → EReal := convexHullFunction f
  have hgproper : IsProper g := by
    simpa [g] using isProper_convexHullFunction hproper hf
  have hxtop : g x ≠ ⊤ := ne_of_lt hx
  have hxbot : g x ≠ ⊥ := ne_of_gt (hgproper.2 x)
  have hcoe : ((g x).toReal : EReal) = g x :=
    EReal.coe_toReal hxtop hxbot
  have hboundary_epi :
      (x, (g x).toReal) ∈ epigraph g := by
    rw [mem_epigraph_iff, hcoe]
  have hboundary_hull :
      (x, (g x).toReal) ∈ convexHull ℝ (epigraph f) := by
    rw [← epigraph_convexHullFunction_eq_of_isCoercive
      hlsc hproper hf]
    simpa [g] using hboundary_epi
  obtain ⟨T, hTepi, hTcard, hboundaryT⟩ :=
    caratheodory (E := E × ℝ) (epigraph f)
      (x, (g x).toReal) hboundary_hull
  obtain ⟨w, hw0, hw1, hwsum⟩ :=
    (Finset.mem_convexHull').mp hboundaryT
  have hp_top : ∀ p ∈ T, f p.1 ≠ ⊤ := by
    intro p hp
    have hle : f p.1 ≤ (p.2 : EReal) :=
      (mem_epigraph_iff f p.1 p.2).mp (hTepi hp)
    exact ne_of_lt (hle.trans_lt (EReal.coe_lt_top p.2))
  have hp_dom : ∀ p ∈ T, p.1 ∈ effectiveDomain f := by
    intro p hp
    exact lt_top_iff_ne_top.mpr (hp_top p hp)
  have hp_value_le : ∀ p ∈ T, (f p.1).toReal ≤ p.2 := by
    intro p hp
    have hle : f p.1 ≤ (p.2 : EReal) :=
      (mem_epigraph_iff f p.1 p.2).mp (hTepi hp)
    have hcoe_p : ((f p.1).toReal : EReal) = f p.1 :=
      EReal.coe_toReal (hp_top p hp) (ne_of_gt (hproper.2 p.1))
    rw [← hcoe_p] at hle
    exact_mod_cast hle
  have hxsum : ∑ p ∈ T, w p • p.1 = x := by
    have h := congrArg (LinearMap.fst ℝ E ℝ) hwsum
    simpa using h
  have hasum :
      ∑ p ∈ T, w p * p.2 = (g x).toReal := by
    have h := congrArg (LinearMap.snd ℝ E ℝ) hwsum
    simpa [smul_eq_mul] using h
  let β : ℝ := ∑ p ∈ T, w p * (f p.1).toReal
  have hβ_le : β ≤ (g x).toReal := by
    calc
      β ≤ ∑ p ∈ T, w p * p.2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_left (hp_value_le p hp) (hw0 p hp)
      _ = (g x).toReal := hasum
  have hgraph : ∀ p ∈ T, (p.1, (f p.1).toReal) ∈ epigraph f := by
    intro p hp
    rw [mem_epigraph_iff,
      EReal.coe_toReal (hp_top p hp) (ne_of_gt (hproper.2 p.1))]
  have hgraph_sum :
      ∑ p ∈ T, w p • (p.1, (f p.1).toReal) = (x, β) := by
    apply Prod.ext
    · change
        (LinearMap.fst ℝ E ℝ)
            (∑ p ∈ T, w p • (p.1, (f p.1).toReal)) = x
      rw [map_sum]
      simpa using hxsum
    · change
        (LinearMap.snd ℝ E ℝ)
            (∑ p ∈ T, w p • (p.1, (f p.1).toReal)) = β
      rw [map_sum]
      simp [β, smul_eq_mul]
  have hgraph_hull : (x, β) ∈ convexHull ℝ (epigraph f) := by
    have hmem :=
      T.centerMass_mem_convexHull
        (s := epigraph f) hw0 (by rw [hw1]; exact zero_lt_one) hgraph
    rw [T.centerMass_eq_of_sum_1 _ hw1] at hmem
    rw [hgraph_sum] at hmem
    exact hmem
  have hg_le_beta : g x ≤ (β : EReal) := by
    simpa [g] using
      (convexHullFunction_le_of_mem_convexHull_epigraph hgraph_hull)
  have hα_le : (g x).toReal ≤ β := by
    exact_mod_cast (hcoe.trans_le hg_le_beta)
  have hβ_eq : β = (g x).toReal :=
    le_antisymm hβ_le hα_le
  refine ⟨T, w, ?_, hw0, hw1, hp_dom, hxsum, ?_⟩
  · simpa [Module.finrank_prod] using hTcard
  · simpa [β, g] using hβ_eq

end RW
