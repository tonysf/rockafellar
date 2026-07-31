/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3G*: Polyhedral Closures from Minkowski--Weyl

This file records the unconditional function-operation consequences unlocked
by the H/V equivalence.  The older injective, surjective, diagonal, and
ray-space formulations remain available in `LinearPreimages` as useful
certificates, but are no longer needed for the basic closure theorems.
-/

import RockafellarWets.Chapter3.MinkowskiWeyl
import RockafellarWets.Chapter3.PolyhedralOperations.LinearPreimages

open Set EReal Filter
open scoped Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section PropernessFromOneFiniteValue

/-- A function with closed convex epigraph is proper as soon as it has one
finite value.  If it took `-∞` anywhere, convexity and closedness would force
every real height above the finite point into the epigraph. -/
theorem isProper_of_convex_closed_epigraph_of_exists_finite
    {f : E → EReal}
    (hconv : Convex ℝ (epigraph f)) (hclosed : IsClosed (epigraph f))
    (hfin : ∃ x, (⊥ : EReal) < f x ∧ f x < ⊤) :
    IsProper f := by
  rcases hfin with ⟨x₀, hx₀bot, hx₀top⟩
  refine ⟨⟨x₀, hx₀top⟩, ?_⟩
  intro x
  apply bot_lt_iff_ne_bot.mpr
  intro hxbot
  let a₀ : ℝ := (f x₀).toReal
  have ha₀ : (a₀ : EReal) = f x₀ :=
    EReal.coe_toReal (ne_of_lt hx₀top) (ne_of_gt hx₀bot)
  have hx₀epi : (x₀, a₀) ∈ epigraph f := by
    rw [mem_epigraph_iff, ha₀]
  have hall : ∀ b : ℝ, f x₀ ≤ (b : EReal) := by
    intro b
    let t : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
    let c : ℕ → ℝ := fun n => a₀ + (b - a₀) / t n
    have htpos : ∀ n, 0 < t n := by
      intro n
      exact one_div_pos.mpr (Nat.cast_add_one_pos n)
    have htle : ∀ n, t n ≤ 1 := by
      intro n
      simpa [t] using
        (Nat.one_div_le_one_div (α := ℝ)
          (n := 0) (m := n) (Nat.zero_le n))
    have hxepi : ∀ n, (x, c n) ∈ epigraph f := by
      intro n
      simp [mem_epigraph_iff, hxbot]
    have hline :
        ∀ n,
          AffineMap.lineMap (x₀, a₀) (x, c n) (t n) =
            (t n • (x - x₀) + x₀, b) := by
      intro n
      ext
      · simp [AffineMap.lineMap_apply_module', Prod.smul_mk]
      · rw [AffineMap.lineMap_apply_module']
        change t n * (c n - a₀) + a₀ = b
        have htne : t n ≠ 0 := (htpos n).ne'
        dsimp [c]
        field_simp [htne]
        ring
    have hmem :
        ∀ n, (t n • (x - x₀) + x₀, b) ∈ epigraph f := by
      intro n
      rw [← hline n]
      exact hconv.lineMap_mem hx₀epi (hxepi n)
        ⟨(htpos n).le, htle n⟩
    have htend :
        Tendsto t atTop (nhds (0 : ℝ)) := by
      simpa [t] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hfirst :
        Tendsto (fun n => t n • (x - x₀) + x₀)
          atTop (nhds x₀) := by
      simpa using
        (htend.smul_const (x - x₀)).add
          (tendsto_const_nhds (x := x₀))
    have hpair :
        Tendsto (fun n => (t n • (x - x₀) + x₀, b))
          atTop (nhds (x₀, b)) := by
      simpa [nhds_prod_eq] using hfirst.prodMk tendsto_const_nhds
    have hlimit : (x₀, b) ∈ epigraph f :=
      hclosed.mem_of_tendsto hpair
        (Filter.Eventually.of_forall hmem)
    exact (mem_epigraph_iff f x₀ b).mp hlimit
  have hx₀eqbot : f x₀ = ⊥ := by
    rw [EReal.eq_bot_iff_forall_lt]
    intro b
    exact (hall (b - 1)).trans_lt <| by
      exact_mod_cast sub_one_lt b
  exact (ne_of_gt hx₀bot) hx₀eqbot

/-- Closed polyhedral epigraphs therefore enter the project's proper CPL
wrapper exactly when they possess one finite value. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_of_exists_finite
    [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f)
    (hfin : ∃ x, (⊥ : EReal) < f x ∧ f x < ⊤) :
    IsConvexPiecewiseLinear f :=
  ⟨isProper_of_convex_closed_epigraph_of_exists_finite
      hf.convex hf.isClosed hfin,
    hf⟩

end PropernessFromOneFiniteValue

section PolyhedralProjections

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the projected epigraph is closed, then it is exactly the epigraph of
the value function.  Closedness supplies attainment at a finite boundary
height; heights strictly above the infimum are represented directly. -/
theorem epigraph_valueFunction_eq_valueProjection_image_epigraph_of_isClosed
    {f : E × F → EReal}
    (hclosed : IsClosed (valueProjection '' epigraph f)) :
    epigraph (valueFunction f) = valueProjection '' epigraph f := by
  refine le_antisymm ?_
    valueProjection_image_epigraph_subset_epigraph_valueFunction
  rintro ⟨u, a⟩ hp
  rw [mem_epigraph_iff] at hp
  have hxapprox :
      ∀ n : ℕ,
        ∃ x : E,
          f (x, u) <
            (((a + 1 / (n + 1 : ℝ)) : ℝ) : EReal) := by
    intro n
    apply exists_lt_of_ciInf_lt
    refine lt_of_le_of_lt hp ?_
    exact_mod_cast
      (lt_add_of_pos_right a
        (one_div_pos.2 (Nat.cast_add_one_pos n)))
  choose x hx using hxapprox
  have hprojected :
      ∀ n : ℕ,
        (u, a + 1 / (n + 1 : ℝ)) ∈
          valueProjection '' epigraph f := by
    intro n
    refine
      ⟨((x n, u), a + 1 / (n + 1 : ℝ)), ?_, ?_⟩
    · rw [mem_epigraph_iff]
      exact (hx n).le
    · simp [valueProjection]
  have hheight :
      Tendsto (fun n : ℕ => a + 1 / (n + 1 : ℝ))
        atTop (nhds a) := by
    simpa using
      (tendsto_const_nhds (x := a)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpair :
      Tendsto (fun n : ℕ => (u, a + 1 / (n + 1 : ℝ)))
        atTop (nhds (u, a)) := by
    simpa [nhds_prod_eq] using tendsto_const_nhds.prodMk hheight
  exact hclosed.mem_of_tendsto hpair
    (Filter.Eventually.of_forall hprojected)

/-- A parametric infimum of a finite-dimensional polyhedral-epigraph
function again has a polyhedral epigraph, with no level-boundedness or horizon
positivity hypothesis. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_valueFunction
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasPolyhedralEpigraph f) :
    HasPolyhedralEpigraph (valueFunction f) := by
  have himage :
      IsPolyhedral (valueProjection '' epigraph f) :=
    IsPolyhedral.linear_image
      (C := epigraph f) hf valueProjection
  change IsPolyhedral (epigraph (valueFunction f))
  rw [epigraph_valueFunction_eq_valueProjection_image_epigraph_of_isClosed
    (IsPolyhedral.isClosed himage)]
  exact himage

/-- A parametric infimum of a closed-polyhedral-epigraph function has a
closed polyhedral epigraph. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_valueFunction
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f) :
    HasClosedPolyhedralEpigraph (valueFunction f) :=
  (hf.hasPolyhedralEpigraph.hasPolyhedralEpigraph_valueFunction :
    HasPolyhedralEpigraph (valueFunction f)).hasClosedPolyhedralEpigraph

/-- A polyhedral parametric infimum is CPL whenever it is proper.  This
properness assumption is the extended-real version of Proposition 3.55's
exception for degenerate value functions. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hproper : IsProper (valueFunction f)) :
    IsConvexPiecewiseLinear (valueFunction f) :=
  ⟨hproper, hf.hasClosedPolyhedralEpigraph_valueFunction⟩

/-- Exact nondegenerate form of Proposition 3.55's parametric-infimum
clause: one finite value rules out the exceptional function whose values are
only `+∞` and `-∞`. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_valueFunction_of_exists_finite
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (hfin : ∃ u, (⊥ : EReal) < valueFunction f u ∧
      valueFunction f u < ⊤) :
    IsConvexPiecewiseLinear (valueFunction f) :=
  hf.hasClosedPolyhedralEpigraph_valueFunction
    |>.isConvexPiecewiseLinear_of_exists_finite hfin

end PolyhedralProjections

section ArbitraryLinearPrecomposition

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A polyhedral epigraph remains polyhedral after precomposition by an
arbitrary linear map between finite-dimensional spaces.  No injectivity or
surjectivity hypothesis is needed. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearMap
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f) (L : F →ₗ[ℝ] E) :
    HasPolyhedralEpigraph (fun y : F => f (L y)) := by
  let M : (F × ℝ) →ₗ[ℝ] (E × ℝ) :=
    (L.comp (LinearMap.fst ℝ F ℝ)).prod (LinearMap.snd ℝ F ℝ)
  have hpre : M ⁻¹' epigraph f = epigraph (fun y : F => f (L y)) := by
    ext z
    rcases z with ⟨y, t⟩
    simp [M, mem_epigraph_iff]
  change IsPolyhedral (epigraph (fun y : F => f (L y)))
  rw [← hpre]
  exact IsPolyhedral.linear_preimage (C := epigraph f) hf M

/-- Closed polyhedral epigraphs remain closed polyhedral under arbitrary
finite-dimensional linear precomposition. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_linearMap
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f) (L : F →ₗ[ℝ] E) :
    HasClosedPolyhedralEpigraph (fun y : F => f (L y)) := by
  let M : (F × ℝ) →ₗ[ℝ] (E × ℝ) :=
    (L.comp (LinearMap.fst ℝ F ℝ)).prod (LinearMap.snd ℝ F ℝ)
  have hpre : M ⁻¹' epigraph f = epigraph (fun y : F => f (L y)) := by
    ext z
    rcases z with ⟨y, t⟩
    simp [M, mem_epigraph_iff]
  change IsClosedPolyhedral (epigraph (fun y : F => f (L y)))
  rw [← hpre]
  exact IsClosedPolyhedral.linear_preimage (C := epigraph f) hf M

/-- At the project's proper-function layer, arbitrary linear precomposition
is convex piecewise-linear whenever the composite is proper. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E) (hproper : IsProper (fun y : F => f (L y))) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) :=
  ⟨hproper, hf.hasClosedPolyhedralEpigraph_precompose_linearMap L⟩

/-- Nondegenerate arbitrary linear precomposition, phrased with the book's
"has a finite value" condition rather than an explicit properness proof. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_of_exists_finite
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E)
    (hfin : ∃ y, (⊥ : EReal) < f (L y) ∧ f (L y) < ⊤) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) :=
  (hf.hasClosedPolyhedralEpigraph_precompose_linearMap L)
    |>.isConvexPiecewiseLinear_of_exists_finite hfin

/-- A checkable properness condition for arbitrary linear precomposition:
the range of the map meets the effective domain. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_precompose_linearMap
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : IsConvexPiecewiseLinear f)
    (L : F →ₗ[ℝ] E)
    (hdom : (effectiveDomain f ∩ (LinearMap.range L : Set E)).Nonempty) :
    IsConvexPiecewiseLinear (fun y : F => f (L y)) :=
  hf.hasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap
    L (isProper_precompose_linearMap_of_nonempty_effectiveDomain_inter_range
      hf.isProper L hdom)

/-- A polyhedral epigraph remains polyhedral after an arbitrary affine
precomposition `y ↦ L y + u`. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_precompose_linearMap_add
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E) (u : E) :
    HasPolyhedralEpigraph (fun y : F => f (L y + u)) := by
  have hshift :
      HasPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasPolyhedralEpigraph_precompose_add u
  simpa using hshift.hasPolyhedralEpigraph_precompose_linearMap L

/-- Closed polyhedral epigraphs remain closed polyhedral after an arbitrary
affine precomposition `y ↦ L y + u`. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_precompose_linearMap_add
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E) (u : E) :
    HasClosedPolyhedralEpigraph (fun y : F => f (L y + u)) := by
  have hshift :
      HasClosedPolyhedralEpigraph (fun x : E => f (x + u)) :=
    hf.hasClosedPolyhedralEpigraph_precompose_add u
  simpa using hshift.hasClosedPolyhedralEpigraph_precompose_linearMap L

/-- Proper arbitrary affine precomposition preserves convex
piecewise-linearity. -/
theorem HasClosedPolyhedralEpigraph.isConvexPiecewiseLinear_precompose_linearMap_add
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → EReal} (hf : HasClosedPolyhedralEpigraph f)
    (L : F →ₗ[ℝ] E) (u : E)
    (hproper : IsProper (fun y : F => f (L y + u))) :
    IsConvexPiecewiseLinear (fun y : F => f (L y + u)) :=
  ⟨hproper, hf.hasClosedPolyhedralEpigraph_precompose_linearMap_add L u⟩

end ArbitraryLinearPrecomposition

section MaximaAndAddition

/-- The pointwise maximum of two polyhedral-epigraph functions has a
polyhedral epigraph. -/
theorem HasPolyhedralEpigraph.hasPolyhedralEpigraph_sup
    [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : HasPolyhedralEpigraph f) (hg : HasPolyhedralEpigraph g) :
    HasPolyhedralEpigraph (fun x : E => f x ⊔ g x) := by
  change IsPolyhedral (epigraph (fun x : E => f x ⊔ g x))
  rw [epigraph_sup]
  exact IsPolyhedral.inter (C := epigraph f) (D := epigraph g) hf hg

/-- The pointwise maximum of two closed-polyhedral-epigraph functions again
has a closed polyhedral epigraph. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup
    [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f)
    (hg : HasClosedPolyhedralEpigraph g) :
    HasClosedPolyhedralEpigraph (fun x : E => f x ⊔ g x) := by
  change IsClosedPolyhedral (epigraph (fun x : E => f x ⊔ g x))
  rw [epigraph_sup]
  exact IsClosedPolyhedral.inter (C := epigraph f) (D := epigraph g) hf hg

/-- The pointwise maximum of two CPL functions is CPL when their finite
domains have a common point (the necessary properness condition in the
project's `IsConvexPiecewiseLinear` wrapper). -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_sup
    [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsConvexPiecewiseLinear (fun x : E => f x ⊔ g x) :=
  ⟨isProper_sup_of_isProper_of_nonempty_effectiveDomain_inter
      hf.isProper hg.isProper hdom,
    hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_sup
      hg.hasClosedPolyhedralEpigraph⟩

/-- Pointwise addition preserves closed polyhedral epigraphs for proper
inputs.  It is the arbitrary linear preimage of separated addition along the
diagonal, so no diagonal ray-space certificate is required. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_add
    [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f)
    (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g) :
    HasClosedPolyhedralEpigraph (fun x : E => f x + g x) := by
  let Δ : E →ₗ[ℝ] E × E :=
    (LinearMap.id : E →ₗ[ℝ] E).prod (LinearMap.id : E →ₗ[ℝ] E)
  have hsep :
      HasClosedPolyhedralEpigraph (fun p : E × E => f p.1 + g p.2) :=
    hf.hasClosedPolyhedralEpigraph_separatedAdd hg hproperf hproperg
  simpa [Δ] using hsep.hasClosedPolyhedralEpigraph_precompose_linearMap Δ

/-- Pointwise addition of CPL functions is CPL when their finite domains
have a common point. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_add
    [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f) (hg : IsConvexPiecewiseLinear g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsConvexPiecewiseLinear (fun x : E => f x + g x) :=
  ⟨isProper_add_of_nonempty_effectiveDomain_inter
      hf.isProper hg.isProper hdom,
    hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_add
      hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper⟩

/-! ### Epigraphical addition -/

/-- Epigraphical addition of proper closed-polyhedral-epigraph inputs has a
closed polyhedral epigraph.  No coercivity or strict horizon-positivity
condition is required. -/
theorem HasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum
    [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : HasClosedPolyhedralEpigraph f)
    (hg : HasClosedPolyhedralEpigraph g)
    (hproperf : IsProper f) (hproperg : IsProper g) :
    HasClosedPolyhedralEpigraph (epiSum f g) := by
  have hint :
      HasClosedPolyhedralEpigraph (RW.epiSumIntegrand f g) :=
    hf.hasClosedPolyhedralEpigraph_epiSumIntegrand
      hg hproperf hproperg
  simpa [epiSum] using
    hint.hasClosedPolyhedralEpigraph_valueFunction

/-- Epigraphical addition of CPL functions is CPL whenever the resulting
infimal convolution is proper. -/
theorem IsConvexPiecewiseLinear.isConvexPiecewiseLinear_epiSum
    [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : IsConvexPiecewiseLinear f)
    (hg : IsConvexPiecewiseLinear g)
    (hproper : IsProper (epiSum f g)) :
    IsConvexPiecewiseLinear (epiSum f g) :=
  ⟨hproper,
    hf.hasClosedPolyhedralEpigraph.hasClosedPolyhedralEpigraph_epiSum
      hg.hasClosedPolyhedralEpigraph hf.isProper hg.isProper⟩

end MaximaAndAddition

end RW
