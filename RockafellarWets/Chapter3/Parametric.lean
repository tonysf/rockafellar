/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3E: Parametric Minimization

This file starts the parametric-minimization layer from Chapter 3 of
Rockafellar & Wets, "Variational Analysis":
- Theorem 3.31: the horizon-function criterion for local uniform
  level-boundedness in the decision variable.
-/

import RockafellarWets.Chapter3.PointedCones
import RockafellarWets.Chapter3.Pointwise
import RockafellarWets.Chapter3.SetOperations
import RockafellarWets.Chapter3.HorizonFunctions
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Pointwise
open Set Bornology Metric EReal Filter

namespace RW

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The sublevel slice used in local uniform level-boundedness for a function
`f(x,u)`: restrict `u` to a closed ball around `uBar` and cut by a level `α`. -/
def localUniformSublevel (f : E × F → EReal) (uBar : F) (eps : ℝ) (α : ℝ) :
    Set (E × F) :=
  (Set.univ ×ˢ closedBall uBar eps) ∩ levelSet f α

/-- `f(x,u)` is level-bounded in `x` locally uniformly in `u` if around every
parameter `uBar` and level `α`, some closed parameter ball cuts out a bounded
sublevel set in the product space. This is a closed-ball version of Definition
1.16, convenient in Lean. -/
def IsLevelBoundedInXLocallyUniformly (f : E × F → EReal) : Prop :=
  ∀ uBar : F, ∀ α : ℝ, ∃ eps > 0, IsBounded (localUniformSublevel f uBar eps α)

/-- The marginal/value function associated with `f(x,u)`, obtained by taking
the infimum over the decision variable `x`. -/
noncomputable def valueFunction (f : E × F → EReal) (u : F) : EReal :=
  ⨅ x : E, f (x, u)

/-- The finite minimizer set of the slice `x ↦ f (x,u)`. This is the
parametric argmin set from Corollary 3.32, adjusted to avoid the degenerate
case `inf = ⊤`, where the raw equality-based `argmin` would be too large in
the extended-real setting. -/
def paramArgmin (f : E × F → EReal) (u : F) : Set E :=
  {x | valueFunction f u = f (x, u) ∧ valueFunction f u < ⊤ ∧ valueFunction f u > ⊥}

private def valueProjection : ((E × F) × ℝ) →ₗ[ℝ] F × ℝ where
  toFun p := (p.1.2, p.2)
  map_add' p q := by
    ext <;> rfl
  map_smul' c p := by
    ext <;> rfl

@[simp] private theorem valueProjection_apply (p : ((E × F) × ℝ)) :
    valueProjection p = (p.1.2, p.2) := rfl

/-- A finite lower level set is convex whenever the epigraph is convex. -/
theorem convex_levelSet_of_convex_epigraph
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → EReal} (hconv : Convex ℝ (epigraph f)) (α : ℝ) :
    Convex ℝ (levelSet f α) := by
  intro x hx y hy a b ha hb hab
  have hxepi : (x, α) ∈ epigraph f := by
    simpa [mem_epigraph_iff] using hx
  have hyepi : (y, α) ∈ epigraph f := by
    simpa [mem_epigraph_iff] using hy
  have hxyepi := hconv hxepi hyepi ha hb hab
  have ha' : (0 : EReal) ≤ (a : EReal) := EReal.coe_nonneg.mpr ha
  have hb' : (0 : EReal) ≤ (b : EReal) := EReal.coe_nonneg.mpr hb
  have hxy :
      f (a • x + b • y) ≤
        (a : EReal) * (α : EReal) + (b : EReal) * (α : EReal) := by
    simpa [mem_epigraph_iff, Prod.smul_mk, smul_eq_mul] using hxyepi
  calc
    f (a • x + b • y)
        ≤ (a : EReal) * (α : EReal) + (b : EReal) * (α : EReal) := hxy
    _ = ((a : EReal) + (b : EReal)) * (α : EReal) :=
          (EReal.right_distrib_of_nonneg ha' hb').symm
    _ = (α : EReal) := by rw [← EReal.coe_add, hab, EReal.coe_one, one_mul]

/-- A finite lower level set of an `EReal`-valued lsc function is closed. -/
theorem isClosed_levelSet_of_lsc_ereal
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → EReal} (hlsc : LowerSemicontinuous f) (α : ℝ) :
    IsClosed (levelSet f α) := by
  let phi : G → G × ℝ := fun x => (x, α)
  have hphi : Continuous phi := continuous_id.prodMk continuous_const
  have hclosed : IsClosed (epigraph f) := (lsc_iff_epigraph_closed_ereal f).1 hlsc
  have hpreimage : levelSet f α = phi ⁻¹' epigraph f := by
    ext x
    simp [phi, mem_epigraph_iff, levelSet]
  rw [hpreimage]
  exact hclosed.preimage hphi

/-- The horizon cone of a local-uniform sublevel slice is the intersection of
the horizon cones of its two defining factors. -/
theorem horizonCone_localUniformSublevel_eq
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    {uBar : F} {eps : ℝ} {α : ℝ}
    (hne : (localUniformSublevel f uBar eps α).Nonempty) :
    horizonCone (localUniformSublevel f uBar eps α) =
      horizonCone (Set.univ ×ˢ closedBall uBar eps : Set (E × F)) ∩
        horizonCone (levelSet f α) := by
  let S : Bool → Set (E × F) := fun b =>
    cond b (levelSet f α) (Set.univ ×ˢ closedBall uBar eps)
  have hSconv : ∀ b, Convex ℝ (S b) := by
    intro b
    cases b
    · simpa [S] using (convex_univ.prod (convex_closedBall uBar eps))
    · simpa [S] using convex_levelSet_of_convex_epigraph hconv α
  have hSclosed : ∀ b, IsClosed (S b) := by
    intro b
    cases b
    · simpa [S] using (isClosed_univ.prod isClosed_closedBall : IsClosed
        ((Set.univ : Set E) ×ˢ closedBall uBar eps))
    · simpa [S] using isClosed_levelSet_of_lsc_ereal hlsc α
  have hSnonempty : (⋂ b, S b).Nonempty := by
    rcases hne with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    simpa [S, localUniformSublevel] using hp
  have hSeq : localUniformSublevel f uBar eps α = ⋂ b, S b := by
    ext p
    simp [S, localUniformSublevel]
  calc
    horizonCone (localUniformSublevel f uBar eps α)
        = horizonCone (⋂ b, S b) := by rw [hSeq]
    _ = ⋂ b, horizonCone (S b) :=
      horizonCone_iInter_eq_iInter_horizonCone hSconv hSclosed hSnonempty
    _ = horizonCone (Set.univ ×ˢ closedBall uBar eps : Set (E × F)) ∩
          horizonCone (levelSet f α) := by
          ext p
          simp [S]

/-- **Theorem 3.31** (sufficiency part): if the horizon function is strictly
positive on directions `(x,0)` with `x ≠ 0`, then `f(x,u)` is level-bounded in
`x` locally uniformly in `u`. -/
theorem isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal}
    (hf : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    IsLevelBoundedInXLocallyUniformly f := by
  intro uBar α
  refine ⟨1, zero_lt_one, ?_⟩
  let C : Set (E × F) := localUniformSublevel f uBar 1 α
  have hprod :
      horizonCone (Set.univ ×ˢ closedBall uBar 1 : Set (E × F)) =
        (Set.univ : Set E) ×ˢ ({0} : Set F) := by
    calc
      horizonCone (Set.univ ×ˢ closedBall uBar 1 : Set (E × F))
          = horizonCone (Set.univ : Set E) ×ˢ ({0} : Set F) := by
              exact horizonCone_prod_eq_of_bounded_right
                (C := Set.univ) (D := closedBall uBar 1)
                (by exact ⟨uBar, by simp⟩) isBounded_closedBall
      _ = (Set.univ : Set E) ×ˢ ({0} : Set F) := by
            simp [horizonCone, asymptoticCone_univ]
  have hsubset : horizonCone C ⊆ ({0} : Set (E × F)) := by
    intro w hw
    have hwprod :
        w ∈ horizonCone (Set.univ ×ˢ closedBall uBar 1 : Set (E × F)) :=
      horizonCone_mono (by intro p hp; exact hp.1) hw
    have hwlevel :
        w ∈ levelSet (horizonFunction f) (0 : EReal) :=
      horizonCone_levelSet_subset_levelSet_horizonFunction (f := f) α <|
        horizonCone_mono (by intro p hp; exact hp.2) hw
    rcases w with ⟨x, u⟩
    have hu0 : u = 0 := by
      have : (x, u) ∈ (Set.univ : Set E) ×ˢ ({0} : Set F) := by
        simpa [hprod] using hwprod
      simpa using this.2
    subst u
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hpos : 0 < horizonFunction f (x, (0 : F)) := hf hx0
      have hle : horizonFunction f (x, (0 : F)) ≤ 0 := by
        simpa [levelSet] using hwlevel
      exact (not_le_of_gt hpos hle).elim
  have hzero : horizonCone C = ({0} : Set (E × F)) := by
    refine le_antisymm hsubset ?_
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact zero_mem_horizonCone C
  exact (isBounded_iff_horizonCone_eq_singleton_zero (C := C)).2 hzero

/-- **Theorem 3.31** (necessity part in the convex case): for a proper lsc
convex function, local uniform level-boundedness in `x` forces positivity of
the horizon function on directions `(x,0)` with `x ≠ 0`. -/
theorem horizonFunction_pos_of_isLevelBoundedInXLocallyUniformly
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal}
    (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) (hLB : IsLevelBoundedInXLocallyUniformly f) :
    ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F)) := by
  intro x hx0
  obtain ⟨z, hzTop⟩ := hproper.1
  obtain ⟨eps, heps, hbounded⟩ := hLB z.2 (f z).toReal
  have hzBot : f z ≠ ⊥ := (ne_of_gt (hproper.2 z))
  have hzEq : f z = (((f z).toReal : ℝ) : EReal) := by
    symm
    exact EReal.coe_toReal (ne_of_lt hzTop) hzBot
  have hzMem :
      z ∈ localUniformSublevel f z.2 eps (f z).toReal := by
    refine ⟨?_, ?_⟩
    · exact ⟨by simp, by simpa [Metric.mem_closedBall, le_of_lt heps]⟩
    · exact hzEq.le
  have hCne : (localUniformSublevel f z.2 eps (f z).toReal).Nonempty := ⟨z, hzMem⟩
  have hCzero :
      horizonCone (localUniformSublevel f z.2 eps (f z).toReal) =
        ({0} : Set (E × F)) :=
    (isBounded_iff_horizonCone_eq_singleton_zero
      (C := localUniformSublevel f z.2 eps (f z).toReal)).mp hbounded
  have hprod :
      horizonCone (Set.univ ×ˢ closedBall z.2 eps : Set (E × F)) =
        (Set.univ : Set E) ×ˢ ({0} : Set F) := by
    calc
      horizonCone (Set.univ ×ˢ closedBall z.2 eps : Set (E × F))
          = horizonCone (Set.univ : Set E) ×ˢ ({0} : Set F) := by
              exact horizonCone_prod_eq_of_bounded_right
                (C := Set.univ) (D := closedBall z.2 eps)
                (by exact ⟨z.2, by simpa [Metric.mem_closedBall, le_of_lt heps]⟩)
                isBounded_closedBall
      _ = (Set.univ : Set E) ×ˢ ({0} : Set F) := by
            simp [horizonCone, asymptoticCone_univ]
  have hlevelNe : (levelSet f (f z).toReal).Nonempty := by
    refine ⟨z, ?_⟩
    exact hzEq.le
  have hCeq :
      horizonCone (localUniformSublevel f z.2 eps (f z).toReal) =
        ((Set.univ : Set E) ×ˢ ({0} : Set F)) ∩
          levelSet (horizonFunction f) (0 : EReal) := by
    calc
      horizonCone (localUniformSublevel f z.2 eps (f z).toReal)
          = horizonCone (Set.univ ×ˢ closedBall z.2 eps : Set (E × F)) ∩
              horizonCone (levelSet f (f z).toReal) := by
                exact horizonCone_localUniformSublevel_eq hconv hlsc hCne
      _ = ((Set.univ : Set E) ×ˢ ({0} : Set F)) ∩
            levelSet (horizonFunction f) (0 : EReal) := by
              rw [hprod, horizonCone_levelSet_eq_levelSet_horizonFunction hconv hlsc hlevelNe]
  have hnotle : ¬ horizonFunction f (x, (0 : F)) ≤ 0 := by
    intro hle
    have hxMem :
        (x, (0 : F)) ∈ horizonCone (localUniformSublevel f z.2 eps (f z).toReal) := by
      have hxInter :
          (x, (0 : F)) ∈
            ((Set.univ : Set E) ×ˢ ({0} : Set F)) ∩
              levelSet (horizonFunction f) (0 : EReal) := by
        refine ⟨by simp, ?_⟩
        simpa [levelSet] using hle
      simpa [hCeq] using hxInter
    have hxPair :
        (x, (0 : F)) = (0 : E × F) := by
      have : (x, (0 : F)) ∈ ({0} : Set (E × F)) := by
        simpa [hCzero] using hxMem
      exact Set.mem_singleton_iff.mp this
    exact hx0 (by simpa using congrArg Prod.fst hxPair)
  exact lt_of_not_ge hnotle

/-- **Theorem 3.31** in the convex case: for a proper lsc convex function,
local uniform level-boundedness in `x` is equivalent to positivity of
`f∞(x,0)` away from `0`. -/
theorem isLevelBoundedInXLocallyUniformly_iff_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal}
    (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) :
    IsLevelBoundedInXLocallyUniformly f ↔
      ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F)) := by
  constructor
  · exact horizonFunction_pos_of_isLevelBoundedInXLocallyUniformly hconv hlsc hproper
  · exact isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos

/-- Every point of the projected epigraph gives a point in the epigraph of the
value function. -/
theorem valueProjection_image_epigraph_subset_epigraph_valueFunction
    {f : E × F → EReal} :
    valueProjection '' epigraph f ⊆ epigraph (valueFunction f) := by
  rintro p ⟨q, hq, rfl⟩
  rcases q with ⟨⟨x, u⟩, a⟩
  rw [mem_epigraph_iff] at hq ⊢
  exact (iInf_le (fun x' : E => f (x', u)) x).trans hq

/-- Local uniform level-boundedness plus lower semicontinuity identifies the
epigraph of the value function with the projected epigraph of `f`. -/
theorem epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    [FiniteDimensional ℝ E]
    {f : E × F → EReal} (hlsc : LowerSemicontinuous f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) :
    epigraph (valueFunction f) = valueProjection '' epigraph f := by
  refine le_antisymm ?_ valueProjection_image_epigraph_subset_epigraph_valueFunction
  rintro ⟨u, a⟩ hp
  rw [mem_epigraph_iff] at hp
  obtain ⟨eps, heps, hbounded⟩ := hLB u (a + 1)
  have hxapprox : ∀ n : ℕ, ∃ x : E, f (x, u) < (((a + 1 / (n + 1 : ℝ)) : ℝ) : EReal) := by
    intro n
    apply exists_lt_of_ciInf_lt
    refine lt_of_le_of_lt hp ?_
    exact_mod_cast (lt_add_of_pos_right a (one_div_pos.2 (Nat.cast_add_one_pos n)))
  choose x hx using hxapprox
  have hxpair_mem : ∀ n : ℕ, (x n, u) ∈ localUniformSublevel f u eps (a + 1) := by
    intro n
    refine ⟨?_, ?_⟩
    · exact ⟨by simp, by simpa [Metric.mem_closedBall, le_of_lt heps]⟩
    · rw [levelSet]
      exact (le_of_lt (hx n)).trans <| by
        have hfrac : (1 : ℝ) / (n + 1 : ℝ) ≤ 1 := by
          simpa using (Nat.one_div_le_one_div (α := ℝ) (n := 0) (m := n) (Nat.zero_le n))
        have haux : a + 1 / (n + 1 : ℝ) ≤ a + 1 := by
          linarith
        exact_mod_cast haux
  have hxbdd_pairs : IsBounded (Set.range fun n => (x n, u)) := by
    refine hbounded.subset ?_
    rintro _ ⟨n, rfl⟩
    exact hxpair_mem n
  have hxbdd : IsBounded (Set.range x) := by
    have hfst :
        Prod.fst '' Set.range (fun n => (x n, u)) = Set.range x := by
      ext y
      constructor
      · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨(x n, u), ⟨n, rfl⟩, rfl⟩
    rw [← hfst]
    exact hxbdd_pairs.image_fst
  rcases tendsto_subseq_of_bounded hxbdd (fun n => Set.mem_range_self n) with
    ⟨xBar, -, φ, hφmono, hφtendsto⟩
  have hxsub : Tendsto (fun n => x (φ n)) atTop (nhds xBar) := by
    simpa using hφtendsto
  have hupair :
      Tendsto (fun n => (x (φ n), u)) atTop (nhds (xBar, u)) := by
    simpa [nhds_prod_eq] using hxsub.prodMk tendsto_const_nhds
  have hdiv :
      Tendsto (fun n => 1 / (φ n + 1 : ℝ)) atTop (nhds (0 : ℝ)) := by
    have hone :
        Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds (0 : ℝ)) := by
      simpa using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds (0 : ℝ)))
    exact hone.comp hφmono.tendsto_atTop
  have hα :
      Tendsto (fun n => a + 1 / (φ n + 1 : ℝ)) atTop (nhds a) := by
    simpa using ((continuous_const.add continuous_id).continuousAt.tendsto.comp hdiv)
  have hqp :
      Tendsto (fun n => ((x (φ n), u), a + 1 / (φ n + 1 : ℝ))) atTop
        (nhds ((xBar, u), a)) := by
    simpa [nhds_prod_eq] using hupair.prodMk hα
  have hqepi :
      ∀ n, ((x (φ n), u), a + 1 / (φ n + 1 : ℝ)) ∈ epigraph f := by
    intro n
    rw [mem_epigraph_iff]
    exact (hx (φ n)).le
  have hlimit : ((xBar, u), a) ∈ epigraph f :=
    (isClosed_epigraph_of_lsc_ereal f hlsc).mem_of_tendsto
      hqp (Filter.Eventually.of_forall hqepi)
  refine ⟨((xBar, u), a), hlimit, ?_⟩
  simp [valueProjection]

/-- A proper function has a nonempty value-function epigraph. -/
theorem epigraph_valueFunction_nonempty_of_isProper
    {f : E × F → EReal} (hproper : IsProper f) :
    (epigraph (valueFunction f)).Nonempty := by
  rcases hproper.1 with ⟨⟨x, u⟩, hfin⟩
  have hbot : f (x, u) ≠ ⊥ := ne_of_gt (hproper.2 (x, u))
  refine ⟨(u, (f (x, u)).toReal), ?_⟩
  rw [mem_epigraph_iff]
  exact (iInf_le (fun x' : E => f (x', u)) x).trans <| by
    simpa [EReal.coe_toReal (ne_of_lt hfin) hbot]

/-- A lower semicontinuous positively homogeneous function coincides with its
horizon function. -/
theorem horizonFunction_eq_self_of_lowerSemicontinuous_of_positivelyHomogeneous
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : G → EReal} (hlsc : LowerSemicontinuous g)
    (hph : PositivelyHomogeneous g) :
    horizonFunction g = g := by
  have hne : (epigraph g).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    rw [mem_epigraph_iff]
    exact hph.map_zero_le_zero
  apply eq_of_epigraph_eq
  calc
    epigraph (horizonFunction g) = horizonCone (epigraph g) :=
      epigraph_horizonFunction_eq_horizonCone_epigraph hne
    _ = epigraph g := by
      exact horizonCone_eq_self_of_isClosed_isCone
        (isClosed_epigraph_of_lsc_ereal g hlsc)
        (isCone_epigraph_of_positivelyHomogeneous hph)

/-- Under condition `3(8)`, the horizon function itself is level-bounded in the
decision variable locally uniformly in the parameter. -/
theorem isLevelBoundedInXLocallyUniformly_horizonFunction
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal}
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    IsLevelBoundedInXLocallyUniformly (horizonFunction f) := by
  apply isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos
  intro x hx
  simpa [horizonFunction_eq_self_of_lowerSemicontinuous_of_positivelyHomogeneous
    (lowerSemicontinuous_horizonFunction f) (positivelyHomogeneous_horizonFunction f)] using hpos hx

private theorem valueProjection_hker
    {f : E × F → EReal} (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    ∀ ⦃v : ((E × F) × ℝ)⦄, v ∈ horizonCone (epigraph f) →
      valueProjection v = 0 → v = 0 := by
  intro v hv hzero
  rcases v with ⟨⟨x, u⟩, a⟩
  have hu0 : u = 0 := by
    simpa using congrArg Prod.fst hzero
  have ha0 : a = 0 := by
    simpa using congrArg Prod.snd hzero
  subst u
  subst a
  have hne : (epigraph f).Nonempty := by
    rcases hproper.1 with ⟨z, hz⟩
    rcases z with ⟨x0, u0⟩
    have hbot : f (x0, u0) ≠ ⊥ := ne_of_gt (hproper.2 (x0, u0))
    refine ⟨((x0, u0), (f (x0, u0)).toReal), ?_⟩
    rw [mem_epigraph_iff]
    simpa [EReal.coe_toReal (ne_of_lt hz) hbot]
  have hmem : ((x, (0 : F)), (0 : ℝ)) ∈ epigraph (horizonFunction f) := by
    simpa [epigraph_horizonFunction_eq_horizonCone_epigraph hne] using hv
  rw [mem_epigraph_iff] at hmem
  by_cases hx0 : x = 0
  · subst x
    rfl
  · exact (not_le_of_gt (hpos hx0) hmem).elim

/-- **Formula `3(9)`** from Theorem 3.31: under condition `3(8)`, horizon
functions commute with the parametric infimum. -/
theorem horizonFunction_valueFunction_eq_valueFunction_horizonFunction
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    horizonFunction (valueFunction f) = valueFunction (horizonFunction f) := by
  let p : F → EReal := valueFunction f
  let q : F → EReal := valueFunction (horizonFunction f)
  have hLBf : IsLevelBoundedInXLocallyUniformly f :=
    isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos
  have hLBh : IsLevelBoundedInXLocallyUniformly (horizonFunction f) :=
    isLevelBoundedInXLocallyUniformly_horizonFunction hpos
  have hne_epi_f : (epigraph f).Nonempty := by
    rcases hproper.1 with ⟨z, hz⟩
    rcases z with ⟨x, u⟩
    have hbot : f (x, u) ≠ ⊥ := ne_of_gt (hproper.2 (x, u))
    refine ⟨((x, u), (f (x, u)).toReal), ?_⟩
    rw [mem_epigraph_iff]
    simpa [EReal.coe_toReal (ne_of_lt hz) hbot]
  have hne_epi_p : (epigraph p).Nonempty := epigraph_valueFunction_nonempty_of_isProper hproper
  apply eq_of_epigraph_eq
  calc
    epigraph (horizonFunction p) = horizonCone (epigraph p) :=
      epigraph_horizonFunction_eq_horizonCone_epigraph hne_epi_p
    _ = horizonCone (valueProjection '' epigraph f) := by
          rw [epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
            (f := f) hlsc hLBf]
    _ = valueProjection '' horizonCone (epigraph f) := by
          symm
          exact linearImage_horizonCone_eq (L := valueProjection)
            (C := epigraph f) (valueProjection_hker hproper hpos)
    _ = valueProjection '' epigraph (horizonFunction f) := by
          rw [epigraph_horizonFunction_eq_horizonCone_epigraph hne_epi_f]
    _ = epigraph q := by
          symm
          exact epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
            (f := horizonFunction f) (lowerSemicontinuous_horizonFunction f) hLBh

/-- If the value function of `f` is finite at `u`, then the infimum over the
decision variable is attained. -/
theorem exists_eq_valueFunction_of_finite_of_lsc_localUniform
    [FiniteDimensional ℝ E]
    {f : E × F → EReal} (hlsc : LowerSemicontinuous f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) {u : F}
    (hfin_top : valueFunction f u < ⊤) (hfin_bot : valueFunction f u > ⊥) :
    ∃ x : E, valueFunction f u = f (x, u) := by
  have hu_epi : (u, (valueFunction f u).toReal) ∈ epigraph (valueFunction f) := by
    rw [mem_epigraph_iff]
    exact (EReal.coe_toReal (ne_of_lt hfin_top) (ne_of_gt hfin_bot)).symm.le
  have hEq :
      epigraph (valueFunction f) = valueProjection '' epigraph f :=
    epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
      (f := f) hlsc hLB
  have hu_img : (u, (valueFunction f u).toReal) ∈ valueProjection '' epigraph f := by
    simpa [hEq] using hu_epi
  rcases hu_img with ⟨⟨⟨x, u'⟩, a⟩, hxepi, hp⟩
  have hu' : u' = u := by
    simpa [valueProjection] using congrArg Prod.fst hp
  have ha : a = (valueFunction f u).toReal := by
    simpa [valueProjection] using congrArg Prod.snd hp
  subst u'
  rw [mem_epigraph_iff] at hxepi
  refine ⟨x, le_antisymm ?_ ?_⟩
  · exact (iInf_le (fun x' : E => f (x', u)) x)
  · calc
      f (x, u) ≤ ((valueFunction f u).toReal : ℝ) := by simpa [ha] using hxepi
      _ = valueFunction f u := EReal.coe_toReal (ne_of_lt hfin_top) (ne_of_gt hfin_bot)

/-- The infimum in formula `3(9)` is attained whenever it is finite. -/
theorem exists_eq_horizonFunction_valueFunction_of_finite
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) {u : F}
    (hfin_top : horizonFunction (valueFunction f) u < ⊤)
    (hfin_bot : horizonFunction (valueFunction f) u > ⊥) :
    ∃ x : E, horizonFunction (valueFunction f) u = horizonFunction f (x, u) := by
  have hEq :
      horizonFunction (valueFunction f) = valueFunction (horizonFunction f) :=
    horizonFunction_valueFunction_eq_valueFunction_horizonFunction hlsc hproper hpos
  have hLBh : IsLevelBoundedInXLocallyUniformly (horizonFunction f) :=
    isLevelBoundedInXLocallyUniformly_horizonFunction hpos
  have hlsc_h : LowerSemicontinuous (horizonFunction f) :=
    lowerSemicontinuous_horizonFunction f
  have htop' : valueFunction (horizonFunction f) u < ⊤ := by
    simpa [hEq] using hfin_top
  have hbot' : valueFunction (horizonFunction f) u > ⊥ := by
    simpa [hEq] using hfin_bot
  rcases exists_eq_valueFunction_of_finite_of_lsc_localUniform
      (f := horizonFunction f) hlsc_h hLBh htop' hbot' with ⟨x, hx⟩
  exact ⟨x, by simpa [hEq] using hx⟩

/-- A bounded nonempty minimizer set for one parameter value forces the
positivity condition `3(8)`. This is the core boundedness step in Corollary
3.32, avoiding the separate formula `3(4)` by using ray monotonicity directly
in the product space. -/
theorem horizonFunction_pos_of_nonempty_bounded_paramArgmin
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) {uBar : F} (hne : (paramArgmin f uBar).Nonempty)
    (hbounded : IsBounded (paramArgmin f uBar)) :
    ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F)) := by
  intro x hx0
  have hnotle : ¬ horizonFunction f (x, (0 : F)) ≤ 0 := by
    intro hxnonpos
    rcases hne with ⟨xBar, hxBar⟩
    rcases hxBar with ⟨hxEq, hxTop, hxBot⟩
    have hray :
        ∀ ⦃τ : ℝ⦄, 0 ≤ τ → τ • x + xBar ∈ paramArgmin f uBar := by
      intro τ hτ
      have hle :
          f (τ • x + xBar, uBar) ≤ valueFunction f uBar := by
        calc
          f (τ • x + xBar, uBar)
              ≤ f (xBar, uBar) := by
                  simpa [Prod.smul_mk, smul_eq_mul, add_comm, add_left_comm, add_assoc] using
                    (apply_smul_add_le_of_horizonFunction_nonpos
                      (f := f) hconv hlsc hproper
                      (x := (xBar, uBar)) (w := (x, (0 : F))) hxnonpos (τ := τ) hτ)
          _ = valueFunction f uBar := hxEq.symm
      have hge : valueFunction f uBar ≤ f (τ • x + xBar, uBar) :=
        iInf_le (fun x' : E => f (x', uBar)) (τ • x + xBar)
      exact ⟨le_antisymm hge hle, hxTop, hxBot⟩
    have hxcone : x ∈ horizonCone (paramArgmin f uBar) := by
      refine mem_horizonCone_of_forall_smul_add_mem
        (C := paramArgmin f uBar) (x := xBar) (w := x) ?_
      intro τ hτ
      exact hray hτ
    have hzero : horizonCone (paramArgmin f uBar) = ({0} : Set E) :=
      (isBounded_iff_horizonCone_eq_singleton_zero (C := paramArgmin f uBar)).mp hbounded
    have hxmem : x ∈ ({0} : Set E) := by
      simpa [hzero] using hxcone
    exact hx0 (by simpa using hxmem)
  exact lt_of_not_ge hnotle

/-- Under the positivity condition `3(8)`, every finite minimizer set of a
slice is bounded. -/
theorem isBounded_paramArgmin_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal}
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) (u : F) :
    IsBounded (paramArgmin f u) := by
  by_cases hne : (paramArgmin f u).Nonempty
  · have hLB : IsLevelBoundedInXLocallyUniformly f :=
      isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos
    obtain ⟨eps, heps, hbounded⟩ := hLB u (valueFunction f u).toReal
    have hpair_bdd : IsBounded ((fun x : E => (x, u)) '' paramArgmin f u) := by
      refine hbounded.subset ?_
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with ⟨hxEq, hxTop, hxBot⟩
      refine ⟨?_, ?_⟩
      · exact ⟨by simp, by simpa [Metric.mem_closedBall, le_of_lt heps]⟩
      · rw [levelSet]
        calc
          f (x, u) = valueFunction f u := hxEq.symm
          _ = (((valueFunction f u).toReal : ℝ) : EReal) := by
                symm
                exact EReal.coe_toReal (ne_of_lt hxTop) (ne_of_gt hxBot)
          _ ≤ (((valueFunction f u).toReal : ℝ) : EReal) := le_rfl
    have hfst :
        Prod.fst '' ((fun x : E => (x, u)) '' paramArgmin f u) = paramArgmin f u := by
      ext x
      constructor
      · rintro ⟨p, ⟨y, hy, rfl⟩, hp⟩
        simpa using hp ▸ hy
      · intro hx
        exact ⟨(x, u), ⟨x, hx, rfl⟩, rfl⟩
    rw [← hfst]
    exact hpair_bdd.image_fst
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isBounded_empty

/-- The convex epigraph of `f` projects to a convex epigraph for its value
function under the positivity condition `3(8)`. -/
theorem convex_epigraph_valueFunction_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    Convex ℝ (epigraph (valueFunction f)) := by
  have hLB : IsLevelBoundedInXLocallyUniformly f :=
    isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos
  rw [epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    (f := f) hlsc hLB]
  exact hconv.linear_image valueProjection

/-- Under `3(8)`, the value function is lower semicontinuous. -/
theorem lowerSemicontinuous_valueFunction_of_horizonFunction_pos
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hpos : ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) :
    LowerSemicontinuous (valueFunction f) := by
  have hLB : IsLevelBoundedInXLocallyUniformly f :=
    isLevelBoundedInXLocallyUniformly_of_horizonFunction_pos hpos
  have hclosed :
      IsClosed (valueProjection '' epigraph f) :=
    isClosed_linearImage_of_horizonCone_ker_trivial
      (L := valueProjection) (C := epigraph f)
      (isClosed_epigraph_of_lsc_ereal f hlsc) (valueProjection_hker hproper hpos)
  apply (lsc_iff_epigraph_closed_ereal _).2
  rw [epigraph_valueFunction_eq_valueProjection_image_epigraph_of_lsc_localUniform
    (f := f) hlsc hLB]
  exact hclosed

/-- **Corollary 3.32** (boundedness part, adapted to the extended-real Lean
setting): if one finite parametric minimizer set is nonempty and bounded, then
all finite parametric minimizer sets are bounded. -/
theorem isBounded_paramArgmin_of_nonempty_bounded_paramArgmin
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) {uBar : F} (hne : (paramArgmin f uBar).Nonempty)
    (hbounded : IsBounded (paramArgmin f uBar)) :
    ∀ u : F, IsBounded (paramArgmin f u) := by
  have hpos :
      ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F)) :=
    horizonFunction_pos_of_nonempty_bounded_paramArgmin hconv hlsc hproper hne hbounded
  intro u
  exact isBounded_paramArgmin_of_horizonFunction_pos hpos u

/-- **Corollary 3.32** (value-function consequences, adapted statement): if one
finite parametric minimizer set is nonempty and bounded, then the value
function is lsc and convex, and its horizon function is given by formula `3(9)`. -/
theorem valueFunction_regular_of_nonempty_bounded_paramArgmin
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal} (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) {uBar : F} (hne : (paramArgmin f uBar).Nonempty)
    (hbounded : IsBounded (paramArgmin f uBar)) :
    LowerSemicontinuous (valueFunction f) ∧
      Convex ℝ (epigraph (valueFunction f)) ∧
      horizonFunction (valueFunction f) = valueFunction (horizonFunction f) := by
  have hpos :
      ∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F)) :=
    horizonFunction_pos_of_nonempty_bounded_paramArgmin hconv hlsc hproper hne hbounded
  exact ⟨lowerSemicontinuous_valueFunction_of_horizonFunction_pos hlsc hproper hpos,
    convex_epigraph_valueFunction_of_horizonFunction_pos hconv hlsc hpos,
    horizonFunction_valueFunction_eq_valueFunction_horizonFunction hlsc hproper hpos⟩

end RW
