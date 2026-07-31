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
import RockafellarWets.Chapter3.PositiveHulls
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

/-- The minimizer set of the slice `x ↦ f (x,u)`, using the book's
`argmin` convention that an identically-`+∞` slice has no minimizers while
points attaining `-∞` remain minimizers. -/
def paramArgmin (f : E × F → EReal) (u : F) : Set E :=
  argmin (fun x : E ↦ f (x, u))

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] in
@[simp]
theorem mem_paramArgmin_iff (f : E × F → EReal) (u : F) (x : E) :
    x ∈ paramArgmin f u ↔
      f (x, u) = valueFunction f u ∧ valueFunction f u < ⊤ := by
  rw [paramArgmin, mem_argmin_iff]
  rfl

def valueProjection : ((E × F) × ℝ) →ₗ[ℝ] F × ℝ where
  toFun p := (p.1.2, p.2)
  map_add' p q := by
    ext <;> rfl
  map_smul' c p := by
    ext <;> rfl

@[simp] theorem valueProjection_apply (p : ((E × F) × ℝ)) :
    valueProjection p = (p.1.2, p.2) := rfl

section EpigraphHeight

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The scalar-height integrand attached to `epi f`: minimizing over the real
height variable recovers `f`. -/
noncomputable def epigraphHeightIntegrand (f : G → EReal) : ℝ × G → EReal :=
  fun p => indicatorVA (epigraph f) (p.2, p.1) + (p.1 : EReal)

@[simp] theorem epigraphHeightIntegrand_apply (f : G → EReal) (r : ℝ) (x : G) :
    epigraphHeightIntegrand f (r, x) = indicatorVA (epigraph f) (x, r) + (r : EReal) :=
  rfl

/-- The scalar-height integrand whose value function is the pointwise
supremum. -/
noncomputable def supHeightIntegrand (f g : G → EReal) : ℝ × G → EReal :=
  fun p =>
    indicatorVA (epigraph f) (p.2, p.1) +
      indicatorVA (epigraph g) (p.2, p.1) + (p.1 : EReal)

@[simp] theorem supHeightIntegrand_apply (f g : G → EReal) (r : ℝ) (x : G) :
    supHeightIntegrand f g (r, x) =
      indicatorVA (epigraph f) (x, r) +
        indicatorVA (epigraph g) (x, r) + (r : EReal) :=
  rfl

theorem supHeightIntegrand_eq_epigraphHeightIntegrand_sup
    (f g : G → EReal) :
    supHeightIntegrand f g = epigraphHeightIntegrand (fun x => f x ⊔ g x) := by
  funext p
  simp [supHeightIntegrand, epigraphHeightIntegrand, epigraph_sup, indicatorVA_inter, add_assoc]

/-- Minimizing the epigraph-height integrand over the height variable recovers
the original function. -/
theorem valueFunction_epigraphHeightIntegrand (f : G → EReal) :
    valueFunction (E := ℝ) (F := G) (epigraphHeightIntegrand f) = f := by
  funext x
  rw [valueFunction]
  change (⨅ r : ℝ, indicatorVA (epigraph f) (x, r) + (r : EReal)) = f x
  calc
    (⨅ r : ℝ, indicatorVA (epigraph f) (x, r) + (r : EReal))
        = ⨅ r : ℝ, ⨅ (_ : f x ≤ (r : EReal)), (r : EReal) := by
            refine iInf_congr ?_
            intro r
            by_cases hr : f x ≤ (r : EReal) <;> simp [indicatorVA, mem_epigraph_iff, hr]
    _ = (⨅ r : {r : ℝ // f x ≤ (r : EReal)}, (r : EReal)) := by
          rw [iInf_subtype']
    _ = f x := iInf_coe_real_ge_eq (f x)

/-- The pointwise supremum is the value function of the scalar-height problem
requiring the height to dominate both epigraphs. -/
theorem valueFunction_sup_eq
    (f g : G → EReal) :
    valueFunction (E := ℝ) (F := G) (supHeightIntegrand f g) =
      fun x => f x ⊔ g x := by
  rw [supHeightIntegrand_eq_epigraphHeightIntegrand_sup]
  exact valueFunction_epigraphHeightIntegrand (fun x => f x ⊔ g x)

/-- Properness of `f` lifts to properness of the scalar-height epigraph
integrand. -/
theorem isProper_epigraphHeightIntegrand
    {f : G → EReal} (hproper : IsProper f) :
    IsProper (epigraphHeightIntegrand f) := by
  constructor
  · rcases hproper.1 with ⟨x, hx⟩
    let r : ℝ := (f x).toReal
    have htoReal : ((r : ℝ) : EReal) = f x := by
      simpa [r] using EReal.coe_toReal (ne_of_lt hx) (ne_of_gt (hproper.2 x))
    have hmem : (x, r) ∈ epigraph f := by
      change f x ≤ (r : EReal)
      simpa using le_of_eq htoReal.symm
    refine ⟨(r, x), ?_⟩
    simpa [epigraphHeightIntegrand_apply, indicatorVA, hmem] using EReal.coe_lt_top r
  · intro p
    rcases p with ⟨r, x⟩
    by_cases hmem : (x, r) ∈ epigraph f
    · simpa [epigraphHeightIntegrand_apply, indicatorVA, hmem] using EReal.bot_lt_coe r
    · simpa [epigraphHeightIntegrand_apply, indicatorVA, hmem] using
        (EReal.bot_lt_top : (⊥ : EReal) < ⊤)

/-- Lower semicontinuity of `f` lifts to lower semicontinuity of the
scalar-height epigraph integrand. -/
theorem lowerSemicontinuous_epigraphHeightIntegrand
    {f : G → EReal} (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous (epigraphHeightIntegrand f) := by
  have hind0 : LowerSemicontinuous (indicatorVA (epigraph f) : G × ℝ → EReal) :=
    lowerSemicontinuous_indicatorVA (C := epigraph f) (isClosed_epigraph_of_lsc_ereal f hlsc)
  have hind : LowerSemicontinuous (fun p : ℝ × G => indicatorVA (epigraph f) (p.2, p.1)) := by
    simpa [Function.comp] using hind0.comp (ContinuousLinearEquiv.prodComm ℝ ℝ G).continuous
  have hcont_r : Continuous (fun p : ℝ × G => ((p.1 : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp continuous_fst
  refine LowerSemicontinuous.add' hind hcont_r.lowerSemicontinuous ?_
  intro p
  exact EReal.continuousAt_add
    (Or.inr (by simpa using EReal.coe_ne_bot p.1))
    (Or.inr (by simpa using EReal.coe_ne_top p.1))

theorem isProper_supHeightIntegrand
    {f g : G → EReal} (hproper : IsProper (fun x => f x ⊔ g x)) :
    IsProper (supHeightIntegrand f g) := by
  simpa [supHeightIntegrand_eq_epigraphHeightIntegrand_sup] using
    isProper_epigraphHeightIntegrand (f := fun x => f x ⊔ g x) hproper

theorem lowerSemicontinuous_supHeightIntegrand
    {f g : G → EReal} (hlsc : LowerSemicontinuous (fun x => f x ⊔ g x)) :
    LowerSemicontinuous (supHeightIntegrand f g) := by
  simpa [supHeightIntegrand_eq_epigraphHeightIntegrand_sup] using
    lowerSemicontinuous_epigraphHeightIntegrand (f := fun x => f x ⊔ g x) hlsc

end EpigraphHeight

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

/-- The scalar-height integrand is level-bounded in the height variable locally
uniformly in the spatial variable, provided the base function is proper and
lower semicontinuous. -/
theorem isLevelBoundedInXLocallyUniformly_epigraphHeightIntegrand
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {f : G → EReal} (hlsc : LowerSemicontinuous f) (hproper : IsProper f) :
    IsLevelBoundedInXLocallyUniformly (epigraphHeightIntegrand f) := by
  intro xBar α
  let K : Set G := closedBall xBar 1 ∩ levelSet f α
  have hdata_of_mem :
      ∀ {r : ℝ} {x : G},
        (r, x) ∈ localUniformSublevel (epigraphHeightIntegrand f) xBar 1 α →
          x ∈ closedBall xBar 1 ∧ (x, r) ∈ epigraph f ∧ ((r : ℝ) : EReal) ≤ α := by
    intro r x hp
    rcases hp with ⟨hball, hpLvl⟩
    have hfxr_le : epigraphHeightIntegrand f (r, x) ≤ (α : EReal) := by
      simpa [levelSet] using hpLvl
    have hxr : (x, r) ∈ epigraph f := by
      by_cases hmem : (x, r) ∈ epigraph f
      · exact hmem
      · exfalso
        have : (⊤ : EReal) ≤ (α : EReal) := by
          simpa [epigraphHeightIntegrand_apply, indicatorVA, hmem] using hfxr_le
        simpa using this
    have hrα : (r : EReal) ≤ (α : EReal) := by
      simpa [epigraphHeightIntegrand_apply, indicatorVA, hxr] using hfxr_le
    exact ⟨hball.2, hxr, hrα⟩
  have hxK_of_mem :
      ∀ {r : ℝ} {x : G},
        (r, x) ∈ localUniformSublevel (epigraphHeightIntegrand f) xBar 1 α →
          x ∈ K := by
    intro r x hp
    rcases hdata_of_mem hp with ⟨hxball, hxr, hrα⟩
    have hfxα : f x ≤ (α : EReal) := by
      exact le_trans (by simpa [mem_epigraph_iff] using hxr) hrα
    exact ⟨hxball, by simpa [K, levelSet] using hfxα⟩
  refine ⟨1, zero_lt_one, ?_⟩
  by_cases hKne : K.Nonempty
  · have hKclosed : IsClosed K := by
      exact isClosed_closedBall.inter (isClosed_levelSet_of_lsc_ereal hlsc α)
    have hKbounded : IsBounded K := by
      exact isBounded_closedBall.subset inter_subset_left
    have hKcompact : IsCompact K := by
      exact Metric.isCompact_iff_isClosed_bounded.2 ⟨hKclosed, hKbounded⟩
    have hreal_lsc : LowerSemicontinuousOn (fun x : G => (f x).toReal) K := by
      rw [← lowerSemicontinuous_restrict_iff, lsc_iff_sublevelSets_closed]
      intro β
      have hEq :
          {x : K | K.restrict (fun x : G => (f x).toReal) x ≤ β} =
            Subtype.val ⁻¹' levelSet f β := by
        ext x
        constructor
        · intro hx
          have hx_top : f x.1 ≠ ⊤ := by
            exact ne_of_lt (lt_of_le_of_lt x.2.2 (EReal.coe_lt_top α))
          have hx_bot : f x.1 ≠ ⊥ := ne_of_gt (hproper.2 x.1)
          have hx' : (((f x.1).toReal : ℝ) : EReal) ≤ (β : EReal) := by
            exact_mod_cast hx
          simpa [levelSet, EReal.coe_toReal hx_top hx_bot] using hx'
        · intro hx
          have hx' : f x.1 ≤ (β : EReal) := by
            simpa [levelSet] using hx
          simpa using
            (EReal.toReal_le_toReal hx' (ne_of_gt (hproper.2 x.1)) (EReal.coe_ne_top β))
      rw [hEq]
      exact (isClosed_levelSet_of_lsc_ereal hlsc β).preimage continuous_subtype_val
    obtain ⟨xMin, hxMinK, hxMin⟩ :=
      exists_min_of_lsc_compact (f := fun x : G => (f x).toReal) hreal_lsc hKcompact hKne
    let m : ℝ := (f xMin).toReal
    have hsub :
        localUniformSublevel (epigraphHeightIntegrand f) xBar 1 α ⊆
          Set.Icc m α ×ˢ closedBall xBar 1 := by
      intro p hp
      rcases p with ⟨r, x⟩
      rcases hdata_of_mem hp with ⟨hxball, hxr, hrα⟩
      have hxK : x ∈ K := hxK_of_mem hp
      have hxmin : m ≤ (f x).toReal := by
        exact hxMin hxK
      have hfxr : f x ≤ (r : EReal) := by
        simpa [mem_epigraph_iff] using hxr
      have htoReal : (f x).toReal ≤ r := by
        exact EReal.toReal_le_toReal hfxr (ne_of_gt (hproper.2 x)) (EReal.coe_ne_top r)
      refine ⟨?_, hxball⟩
      constructor
      · exact le_trans hxmin htoReal
      · exact_mod_cast hrα
    exact (Metric.isBounded_Icc m α).prod isBounded_closedBall |>.subset hsub
  · have hEmpty : localUniformSublevel (epigraphHeightIntegrand f) xBar 1 α = ∅ := by
      ext p
      constructor
      · intro hp
        rcases p with ⟨r, x⟩
        exact (hKne ⟨x, hxK_of_mem hp⟩).elim
      · simp
    simpa [hEmpty] using (isBounded_empty : IsBounded (∅ : Set (ℝ × G)))

theorem isLevelBoundedInXLocallyUniformly_supHeightIntegrand
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {f g : G → EReal} (hlsc : LowerSemicontinuous (fun x => f x ⊔ g x))
    (hproper : IsProper (fun x => f x ⊔ g x)) :
    IsLevelBoundedInXLocallyUniformly (supHeightIntegrand f g) := by
  simpa [supHeightIntegrand_eq_epigraphHeightIntegrand_sup] using
    isLevelBoundedInXLocallyUniformly_epigraphHeightIntegrand
      (f := fun x => f x ⊔ g x) hlsc hproper

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

/-- Positivity of `f∞(x,0)` away from `0` is equivalent to the zero lower
level set of `f∞` meeting the horizontal direction subspace only at `0`. -/
theorem horizonFunction_pos_slice_iff_levelSet_inter_horizontal_zero
    {f : E × F → EReal} :
    (∀ ⦃x : E⦄, x ≠ 0 → 0 < horizonFunction f (x, (0 : F))) ↔
      ((Set.univ : Set E) ×ˢ ({0} : Set F)) ∩
          levelSet (horizonFunction f) (0 : EReal) =
        ({0} : Set (E × F)) := by
  constructor
  · intro hpos
    apply le_antisymm
    · rintro ⟨x, u⟩ ⟨hu, hlevel⟩
      have hu0 : u = 0 := by simpa using hu.2
      subst u
      by_cases hx0 : x = 0
      · simp [hx0]
      · have hstrict : 0 < horizonFunction f (x, (0 : F)) := hpos hx0
        have hle : horizonFunction f (x, (0 : F)) ≤ 0 := by
          simpa [levelSet] using hlevel
        exact (not_le_of_gt hstrict hle).elim
    · intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      refine ⟨by simp, ?_⟩
      simpa [levelSet] using (positivelyHomogeneous_horizonFunction f).map_zero_le_zero
  · intro hzero x hx0
    exact not_le.mp <| by
      intro hle
      have hmem :
          (x, (0 : F)) ∈
            ((Set.univ : Set E) ×ˢ ({0} : Set F)) ∩
              levelSet (horizonFunction f) (0 : EReal) := by
        refine ⟨by simp, ?_⟩
        simpa [levelSet] using hle
      have hpair : (x, (0 : F)) = (0 : E × F) := by
        exact Set.mem_singleton_iff.mp (by simpa [hzero] using hmem)
      exact hx0 (by simpa using congrArg Prod.fst hpair)

/-- Equivalent zero-level horizontal-slice form of Theorem 3.31. -/
theorem isLevelBoundedInXLocallyUniformly_iff_levelSet_inter_horizontal_zero
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → EReal}
    (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hproper : IsProper f) :
    IsLevelBoundedInXLocallyUniformly f ↔
      ((Set.univ : Set E) ×ˢ ({0} : Set F)) ∩
          levelSet (horizonFunction f) (0 : EReal) =
        ({0} : Set (E × F)) :=
  (isLevelBoundedInXLocallyUniformly_iff_horizonFunction_pos
    hconv hlsc hproper).trans
    horizonFunction_pos_slice_iff_levelSet_inter_horizontal_zero

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

/-- If a slice has finite infimum, then local uniform level-boundedness and
lower semicontinuity rule out the value `-∞`. -/
theorem bot_lt_valueFunction_of_lt_top_of_lsc_localUniform
    [FiniteDimensional ℝ E]
    {f : E × F → EReal} (hlsc : LowerSemicontinuous f)
    (hbot : ∀ p : E × F, f p > ⊥)
    (hLB : IsLevelBoundedInXLocallyUniformly f) {u : F}
    (htop : valueFunction f u < ⊤) :
    valueFunction f u > ⊥ := by
  let g : E → EReal := fun x => f (x, u)
  have hg_lsc : LowerSemicontinuous g := by
    simpa [g, Function.comp] using
      hlsc.comp (continuous_id.prodMk continuous_const)
  have hfin : ∃ x : E, g x < ⊤ := by
    by_contra h
    push_neg at h
    have hall : ∀ x : E, g x = ⊤ := by
      intro x
      exact le_antisymm le_top (h x)
    have htop' : valueFunction f u = ⊤ := by
      simp [valueFunction, g, hall]
    exact (ne_of_lt htop) htop'
  rcases hfin with ⟨x0, hx0fin⟩
  let α : ℝ := (g x0).toReal
  let K : Set E := levelSet g α
  have hx0K : x0 ∈ K := by
    change g x0 ≤ (α : EReal)
    simpa [α] using EReal.le_coe_toReal (x := g x0) (ne_of_lt hx0fin)
  have hKne : K.Nonempty := ⟨x0, hx0K⟩
  have hKclosed : IsClosed K := by
    simpa [K] using isClosed_levelSet_of_lsc_ereal hg_lsc α
  obtain ⟨eps, heps, hbounded_prod⟩ := hLB u α
  have hpair_bdd : IsBounded ((fun x : E => (x, u)) '' K) := by
    refine hbounded_prod.subset ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · exact ⟨by simp, by simpa [Metric.mem_closedBall, le_of_lt heps]⟩
    · simpa [K] using hx
  have hfst :
      Prod.fst '' ((fun x : E => (x, u)) '' K) = K := by
    ext x
    constructor
    · rintro ⟨p, ⟨y, hy, rfl⟩, hp⟩
      simpa using hp ▸ hy
    · intro hx
      exact ⟨(x, u), ⟨x, hx, rfl⟩, rfl⟩
  have hKbounded : IsBounded K := by
    rw [← hfst]
    exact hpair_bdd.image_fst
  have hKcompact : IsCompact K := by
    exact Metric.isCompact_iff_isClosed_bounded.2 ⟨hKclosed, hKbounded⟩
  have hreal_lsc : LowerSemicontinuousOn (fun x : E => (g x).toReal) K := by
    rw [← lowerSemicontinuous_restrict_iff, lsc_iff_sublevelSets_closed]
    intro β
    have hEq :
        {x : K | K.restrict (fun x : E => (g x).toReal) x ≤ β} =
          Subtype.val ⁻¹' levelSet g β := by
      ext x
      constructor
      · intro hx
        have hx_top : g x.1 ≠ ⊤ := by
          exact ne_of_lt (lt_of_le_of_lt x.2 (EReal.coe_lt_top α))
        have hx_bot : g x.1 ≠ ⊥ := ne_of_gt (hbot (x.1, u))
        have hx' : (((g x.1).toReal : ℝ) : EReal) ≤ (β : EReal) := by
          exact_mod_cast hx
        simpa [levelSet, EReal.coe_toReal hx_top hx_bot] using hx'
      · intro hx
        have hx' : g x.1 ≤ (β : EReal) := by
          simpa [levelSet] using hx
        simpa using
          (EReal.toReal_le_toReal hx' (ne_of_gt (hbot (x.1, u))) (EReal.coe_ne_top β))
    rw [hEq]
    exact (isClosed_levelSet_of_lsc_ereal hg_lsc β).preimage continuous_subtype_val
  obtain ⟨xMin, hxMinK, hxMin⟩ :=
    exists_min_of_lsc_compact (f := fun x : E => (g x).toReal) hreal_lsc hKcompact hKne
  have hlower : (((g xMin).toReal : ℝ) : EReal) ≤ valueFunction f u := by
    refine le_iInf ?_
    intro x
    by_cases hxK : x ∈ K
    · have hxMin_top : g xMin ≠ ⊤ := by
        exact ne_of_lt (lt_of_le_of_lt hxMinK (EReal.coe_lt_top α))
      have hxMin_bot : g xMin ≠ ⊥ := ne_of_gt (hbot (xMin, u))
      have hx_top : g x ≠ ⊤ := by
        exact ne_of_lt (lt_of_le_of_lt hxK (EReal.coe_lt_top α))
      have hx_bot : g x ≠ ⊥ := ne_of_gt (hbot (x, u))
      have hreal : (g xMin).toReal ≤ (g x).toReal := hxMin hxK
      calc
        (((g xMin).toReal : ℝ) : EReal) ≤ (((g x).toReal : ℝ) : EReal) := by
          exact_mod_cast hreal
        _ = g x := EReal.coe_toReal hx_top hx_bot
        _ = f (x, u) := rfl
    · have hαlt : (α : EReal) < g x := lt_of_not_ge hxK
      have hmin_le_α : (((g xMin).toReal : ℝ) : EReal) ≤ (α : EReal) := by
        have h' : (g xMin).toReal ≤ α := by
          simpa [α] using
            (EReal.toReal_le_toReal hxMinK (ne_of_gt (hbot (xMin, u))) (EReal.coe_ne_top α))
        exact_mod_cast h'
      exact le_trans hmin_le_α hαlt.le
  exact lt_of_lt_of_le (by simp) hlower

/-- Under local uniform level-boundedness, the value function of a proper lsc
integrand is proper. -/
theorem isProper_valueFunction_of_lsc_localUniform
    [FiniteDimensional ℝ E]
    {f : E × F → EReal} (hlsc : LowerSemicontinuous f) (hproper : IsProper f)
    (hLB : IsLevelBoundedInXLocallyUniformly f) :
    IsProper (valueFunction f) := by
  constructor
  · rcases hproper.1 with ⟨⟨x, u⟩, hxu⟩
    exact ⟨u, (iInf_le (fun x' : E => f (x', u)) x).trans_lt hxu⟩
  · intro u
    by_cases htop : valueFunction f u < ⊤
    · exact bot_lt_valueFunction_of_lt_top_of_lsc_localUniform hlsc hproper.2 hLB htop
    · have hu_top : valueFunction f u = ⊤ := le_antisymm le_top (le_of_not_gt htop)
      simpa [hu_top]

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
    rcases (mem_paramArgmin_iff f uBar xBar).1 hxBar with ⟨hxEq, hxTop⟩
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
          _ = valueFunction f uBar := hxEq
      have hge : valueFunction f uBar ≤ f (τ • x + xBar, uBar) :=
        iInf_le (fun x' : E => f (x', uBar)) (τ • x + xBar)
      exact (mem_paramArgmin_iff f uBar _).2 ⟨le_antisymm hle hge, hxTop⟩
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

/-- Under the positivity condition `3(8)`, every minimizer set of a slice is
bounded.  The book-correct `argmin` convention excludes only an
identically-`⊤` slice and retains any `⊥`-valued minimizers. -/
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
      rcases (mem_paramArgmin_iff f u x).1 hx with ⟨hxEq, hxTop⟩
      refine ⟨?_, ?_⟩
      · exact ⟨by simp, by simpa [Metric.mem_closedBall, le_of_lt heps]⟩
      · rw [levelSet]
        calc
          f (x, u) = valueFunction f u := hxEq
          _ ≤ (((valueFunction f u).toReal : ℝ) : EReal) :=
                EReal.le_coe_toReal (ne_of_lt hxTop)
    have hfst :
        Prod.fst '' ((fun x : E => (x, u)) '' paramArgmin f u) = paramArgmin f u := by
      ext x
      constructor
      · rintro ⟨p, ⟨y, hy, rfl⟩, rfl⟩
        exact hy
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

/-- **Corollary 3.32** (boundedness part): if one parametric minimizer set is
nonempty and bounded, then all parametric minimizer sets are bounded. -/
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

/-- **Corollary 3.32** (value-function consequences): if one parametric
minimizer set is nonempty and bounded, then the value function is lsc and
convex, and its horizon function is given by formula `3(9)`. -/
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
