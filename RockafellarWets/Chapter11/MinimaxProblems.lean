/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Minimax problems

Example 11.52.
-/
import RockafellarWets.Chapter11.MinimaxRelations
import RockafellarWets.Chapter11.PrimalDualBestCase

open Set Filter Topology Bornology Classical
open scoped InnerProductSpace
namespace RW
noncomputable section

section Helpers
variable {α : Type*} [TopologicalSpace α]

/-- A function continuous relative to a closed set and `+∞` off it is lsc. -/
theorem lowerSemicontinuous_ite_coe_top {p : α → Prop} {φ : α → ℝ}
    (hp : IsClosed {q | p q}) (hφ : ContinuousOn φ {q | p q}) :
    LowerSemicontinuous (fun q ↦ if p q then (φ q : EReal) else ⊤) := by
  intro y c hc
  by_cases hy : p y
  · simp only [hy, if_true] at hc
    have h₁ : ∀ᶠ y' in 𝓝[{q | p q}] y, c < (φ y' : EReal) :=
      (continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt (hφ y hy)).eventually
        (lt_mem_nhds hc)
    rw [eventually_nhdsWithin_iff] at h₁
    filter_upwards [h₁] with y' hy'
    by_cases h : p y'
    · simpa [h] using hy' h
    · simpa [h] using hc.trans (EReal.coe_lt_top _)
  · have h₂ : ∀ᶠ y' in 𝓝 y, ¬ p y' := hp.isOpen_compl.mem_nhds hy
    filter_upwards [h₂] with y' hy'
    simpa [hy, hy'] using hc

theorem ereal_iInf_neg {ι : Sort*} (g : ι → EReal) : (⨅ i, -g i) = -(⨆ i, g i) := by
  apply le_antisymm
  · rw [EReal.le_neg]
    exact iSup_le fun i ↦ by rw [EReal.le_neg]; exact iInf_le (fun i ↦ -g i) i
  · exact le_iInf fun i ↦ EReal.neg_le_neg_iff.mpr (le_iSup g i)

/-- Maximizers of `g` are the minimizers of `-g`, with both conventions. -/
theorem argmax_eq_argmin_neg {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (g : F → EReal) : argmax g = argmin (fun y ↦ -g y) := by
  ext y
  change (g y = ⨆ z, g z ∧ ⊥ < ⨆ z, g z) ↔ (-g y = ⨅ z, -g z ∧ (⨅ z, -g z) < ⊤)
  rw [ereal_iInf_neg, neg_inj, EReal.neg_lt_comm, EReal.neg_top]

/-- The minimizers of a lsc function with convex epigraph form a closed convex set. -/
theorem isClosed_convex_argmin {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {g : F → EReal} (hl : LowerSemicontinuous g) (hc : Convex ℝ (epigraph g)) :
    IsClosed (argmin g) ∧ Convex ℝ (argmin g) := by
  by_cases ht : (⨅ z, g z) < ⊤
  · have he : argmin g = g ⁻¹' Iic (⨅ z, g z) := by
      ext x
      simp only [mem_argmin_iff, mem_preimage, mem_Iic, ht, and_true]
      exact ⟨le_of_eq, fun h ↦ le_antisymm h (iInf_le g x)⟩
    have hlev : g ⁻¹' Iic (⨅ z, g z) = ⋂ (r : ℝ) (_ : (⨅ z, g z) < (r : EReal)), levelSet g r := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_iInter, levelSet, mem_setOf_eq]
      constructor
      · exact fun h r hr ↦ h.trans hr.le
      · intro h
        by_contra hlt
        obtain ⟨r, hr₁, hr₂⟩ := EReal.lt_iff_exists_real_btwn.mp (not_le.mp hlt)
        exact (h r hr₁).not_gt hr₂
    rw [he]
    refine ⟨hl.isClosed_preimage _, ?_⟩
    rw [hlev]
    exact convex_iInter fun r ↦ convex_iInter fun _ ↦ convex_levelSet_of_convex_epigraph hc r
  · have he : argmin g = ∅ := by
      ext x
      simp [mem_argmin_iff, ht]
    rw [he]
    exact ⟨isClosed_empty, convex_empty⟩

end Helpers

section FirstOrder
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The gradient inequality for a convex function on a convex set, at a point
of differentiability. -/
theorem convexOn_inner_gradient_le_sub {S : Set F} {g : F → ℝ} (hg : ConvexOn ℝ S g)
    {x₀ x g' : F} (hx₀ : x₀ ∈ S) (hx : x ∈ S) (hd : HasGradientAt g g' x₀) :
    ⟪g', x - x₀⟫_ℝ ≤ g x - g x₀ := by
  set d := x - x₀
  have hline : HasDerivAt (fun t : ℝ ↦ x₀ + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x₀
  have hfd : HasFDerivAt g (InnerProductSpace.toDual ℝ F g') (x₀ + (0 : ℝ) • d) := by
    simpa using hd.hasFDerivAt
  have hcomp := hfd.comp_hasDerivAt (0 : ℝ) hline
  have hslope := hcomp.tendsto_slope_zero_right
  rw [InnerProductSpace.toDual_apply_apply] at hslope
  refine le_of_tendsto hslope ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have hc := hg.2 hx₀ hx (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring)
  have heq : (1 - t) • x₀ + t • x = x₀ + t • d := by
    simp only [d, smul_sub, sub_smul, one_smul]
    abel
  rw [heq, smul_eq_mul, smul_eq_mul] at hc
  simp only [Function.comp_apply, zero_add, zero_smul, add_zero, smul_eq_mul]
  rw [inv_mul_le_iff₀ ht.1]
  nlinarith

/-- First-order optimality over a convex set: `x₀` minimizes a convex function
differentiable at `x₀` over `S` iff `-∇g(x₀) ∈ N_S(x₀)`. -/
theorem isMinOn_iff_neg_gradient_mem_normalCone {S : Set F} {g : F → ℝ} {x₀ : F}
    (hS : Convex ℝ S) (hx₀ : x₀ ∈ S) (hg : ConvexOn ℝ S g) (hd : DifferentiableAt ℝ g x₀) :
    (∀ x ∈ S, g x₀ ≤ g x) ↔ -gradient g x₀ ∈ normalCone S x₀ := by
  rw [normalCone_eq_of_convex hS hx₀, mem_setOf_eq]
  have hgr := hd.hasGradientAt
  constructor
  · intro hmin x hx
    have hseg : segment ℝ x₀ (x₀ + (x - x₀)) ⊆ S := by
      rw [add_sub_cancel]
      exact hS.segment_subset hx₀ hx
    have hpos := (IsMinOn.localize (isMinOn_iff.mpr hmin)).hasFDerivWithinAt_nonneg
      hgr.hasFDerivAt.hasFDerivWithinAt (mem_posTangentConeAt_of_segment_subset hseg)
    rw [InnerProductSpace.toDual_apply_apply] at hpos
    rw [inner_neg_left]
    linarith
  · intro hn x hx
    have hin := hn x hx
    rw [inner_neg_left] at hin
    have key := convexOn_inner_gradient_le_sub hg hx₀ hx hgr
    linarith

end FirstOrder


variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The standing assumptions of **Example 11.52**: nonempty closed convex `X`, `Y`
and a continuous `L : X × Y → ℝ`, convex in `x ∈ X` and concave in `y ∈ Y`. -/
structure IsMinimaxProblem (L : E → P → ℝ) (X : Set E) (Y : Set P) : Prop where
  nonempty_left : X.Nonempty
  isClosed_left : IsClosed X
  convex_left : Convex ℝ X
  nonempty_right : Y.Nonempty
  isClosed_right : IsClosed Y
  convex_right : Convex ℝ Y
  continuousOn : ContinuousOn (fun p : E × P ↦ L p.1 p.2) (X ×ˢ Y)
  convexOn_left : ∀ y ∈ Y, ConvexOn ℝ X (fun x ↦ L x y)
  concaveOn_right : ∀ x ∈ X, ConcaveOn ℝ Y (fun y ↦ L x y)

open Classical in
/-- The Lagrangian `l` of **11.52**. -/
def minimaxLagrangian (L : E → P → ℝ) (X : Set E) (Y : Set P) (x : E) (y : P) : EReal :=
  if x ∈ X then (if y ∈ Y then (L x y : EReal) else ⊥) else ⊤

open Classical in
/-- The primal objective `φ(x) = sup_{y ∈ Y} L(x,y)` on `X`, `∞` off `X`. -/
def minimaxPrimal (L : E → P → ℝ) (X : Set E) (Y : Set P) (x : E) : EReal :=
  if x ∈ X then ⨆ y ∈ Y, (L x y : EReal) else ⊤

open Classical in
/-- The dual objective `ψ(y) = inf_{x ∈ X} L(x,y)` on `Y`, `-∞` off `Y`. -/
def minimaxDual (L : E → P → ℝ) (X : Set E) (Y : Set P) (y : P) : EReal :=
  if y ∈ Y then ⨅ x ∈ X, (L x y : EReal) else ⊥

open Classical in
/-- The dualizing parameterization `f(x,u) = sup_{y ∈ Y} {L(x,y) + ⟨y,u⟩}` of **11.52**. -/
def minimaxIntegrand (L : E → P → ℝ) (X : Set E) (Y : Set P) (q : WithLp 2 (E × P)) : EReal :=
  if q.fst ∈ X then ⨆ y ∈ Y, ((L q.fst y + ⟪y, q.snd⟫_ℝ : ℝ) : EReal) else ⊤

open Classical in
/-- `-l(x,·)` for `x ∈ X`. -/
def negMinimaxSlice (L : E → P → ℝ) (Y : Set P) (x : E) (y : P) : EReal :=
  if y ∈ Y then ((-L x y : ℝ) : EReal) else ⊤

variable {L : E → P → ℝ} {X : Set E} {Y : Set P}

namespace IsMinimaxProblem

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem continuousOn_left (h : IsMinimaxProblem L X Y) {y : P} (hy : y ∈ Y) :
    ContinuousOn (fun x ↦ L x y) X :=
  h.continuousOn.comp (continuous_id.prodMk continuous_const : Continuous fun x : E ↦ (x, y)).continuousOn
    fun _ hx ↦ ⟨hx, hy⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem continuousOn_right (h : IsMinimaxProblem L X Y) {x : E} (hx : x ∈ X) :
    ContinuousOn (fun y ↦ L x y) Y :=
  h.continuousOn.comp (continuous_const.prodMk continuous_id : Continuous fun y : P ↦ (x, y)).continuousOn
    fun _ hy ↦ ⟨hx, hy⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem isProper_negMinimaxSlice (h : IsMinimaxProblem L X Y) (x : E) :
    IsProper (negMinimaxSlice L Y x) := by
  obtain ⟨y, hy⟩ := h.nonempty_right
  refine ⟨⟨y, by simp only [negMinimaxSlice, hy, if_true]; exact EReal.coe_lt_top _⟩, fun z ↦ ?_⟩
  unfold negMinimaxSlice
  split_ifs
  · exact EReal.bot_lt_coe _
  · exact bot_lt_top

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem lowerSemicontinuous_negMinimaxSlice (h : IsMinimaxProblem L X Y) {x : E} (hx : x ∈ X) :
    LowerSemicontinuous (negMinimaxSlice L Y x) :=
  lowerSemicontinuous_ite_coe_top (p := fun y ↦ y ∈ Y) h.isClosed_right
    (h.continuousOn_right hx).neg

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem convex_epigraph_negMinimaxSlice (h : IsMinimaxProblem L X Y) {x : E} (hx : x ∈ X) :
    Convex ℝ (epigraph (negMinimaxSlice L Y x)) := by
  have he : epigraph (negMinimaxSlice L Y x) = {p : P × ℝ | p.1 ∈ Y ∧ -L x p.1 ≤ p.2} := by
    ext ⟨y, a⟩
    by_cases hy : y ∈ Y
    · simp only [epigraph, negMinimaxSlice, hy, if_true, mem_setOf_eq, true_and]
      exact EReal.coe_le_coe_iff
    · simp [epigraph, negMinimaxSlice, hy]
  rw [he]
  exact (h.concaveOn_right x hx).neg.convex_epigraph

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem minimaxIntegrand_eq_fenchelConjugate {x : E} (hx : x ∈ X) (u : P) :
    minimaxIntegrand L X Y (WithLp.toLp 2 (x, u)) = fenchelConjugate (negMinimaxSlice L Y x) u := by
  change (if x ∈ X then ⨆ y ∈ Y, ((L x y + ⟪y, u⟫_ℝ : ℝ) : EReal) else ⊤) = _
  rw [if_pos hx]
  refine iSup_congr fun y ↦ ?_
  by_cases hy : y ∈ Y
  · rw [iSup_pos hy]
    simp only [negMinimaxSlice, hy, if_true]
    norm_cast
    rw [real_inner_comm]
    ring
  · rw [iSup_neg hy]
    simp [negMinimaxSlice, hy]

omit [FiniteDimensional ℝ E] in
/-- The Lagrangian of the parameterization in **11.52** is `l`. -/
theorem lagrangian_eq (h : IsMinimaxProblem L X Y) :
    lagrangian (minimaxIntegrand L X Y) = minimaxLagrangian L X Y := by
  funext x y
  by_cases hx : x ∈ X
  · rw [lagrangian_eq_neg_fenchelConjugate]
    have hs : parameterSlice (minimaxIntegrand L X Y) x =
        fenchelConjugate (negMinimaxSlice L Y x) :=
      funext (minimaxIntegrand_eq_fenchelConjugate hx)
    rw [hs, fenchelConjugate_fenchelConjugate_eq (h.isProper_negMinimaxSlice x)
      (h.lowerSemicontinuous_negMinimaxSlice hx) (h.convex_epigraph_negMinimaxSlice hx)]
    unfold negMinimaxSlice minimaxLagrangian
    rw [if_pos hx]
    split_ifs <;> simp
  · unfold lagrangian minimaxLagrangian
    rw [if_neg hx]
    refine iInf_eq_top.mpr fun u ↦ ?_
    change (if x ∈ X then ⨆ y ∈ Y, ((L x y + ⟪y, u⟫_ℝ : ℝ) : EReal) else ⊤) - _ = ⊤
    rw [if_neg hx, EReal.top_sub_coe]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem primalObjective_eq : primalObjective (minimaxIntegrand L X Y) = minimaxPrimal L X Y := by
  funext x
  change (if x ∈ X then ⨆ y ∈ Y, ((L x y + ⟪y, (0 : P)⟫_ℝ : ℝ) : EReal) else ⊤) = _
  simp only [inner_zero_right, add_zero, minimaxPrimal]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem minimaxIntegrand_eq_iSup (h : IsMinimaxProblem L X Y) :
    minimaxIntegrand L X Y = fun q ↦ ⨆ y : Y,
      (if q.fst ∈ X then ((L q.fst y + ⟪(y : P), q.snd⟫_ℝ : ℝ) : EReal) else ⊤) := by
  funext q
  haveI := h.nonempty_right.to_subtype
  by_cases hq : q.fst ∈ X
  · simp only [minimaxIntegrand, hq, if_true, iSup_subtype']
  · simp only [minimaxIntegrand, hq, if_false, iSup_const]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem lowerSemicontinuous_minimaxIntegrand (h : IsMinimaxProblem L X Y) :
    LowerSemicontinuous (minimaxIntegrand L X Y) := by
  rw [h.minimaxIntegrand_eq_iSup]
  refine lowerSemicontinuous_iSup fun y ↦ ?_
  have hS : IsClosed {q : WithLp 2 (E × P) | q.fst ∈ X} :=
    h.isClosed_left.preimage (WithLp.fstL 2 ℝ E P).continuous
  refine lowerSemicontinuous_ite_coe_top (p := fun q : WithLp 2 (E × P) ↦ q.fst ∈ X) hS ?_
  have h₁ : ContinuousOn (fun q : WithLp 2 (E × P) ↦ L q.fst y) {q | q.fst ∈ X} :=
    (h.continuousOn_left y.2).comp (WithLp.fstL 2 ℝ E P).continuous.continuousOn fun _ hq ↦ hq
  exact h₁.add (continuous_const.inner (WithLp.sndL 2 ℝ E P).continuous).continuousOn

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem convex_epigraph_minimaxIntegrand (h : IsMinimaxProblem L X Y) :
    Convex ℝ (epigraph (minimaxIntegrand L X Y)) := by
  rw [h.minimaxIntegrand_eq_iSup]
  refine convex_epigraph_iSup fun y ↦ ?_
  have hS : Convex ℝ {q : WithLp 2 (E × P) | q.fst ∈ X} :=
    h.convex_left.linear_preimage (WithLp.fstL 2 ℝ E P).toLinearMap
  have hcv : ConvexOn ℝ {q : WithLp 2 (E × P) | q.fst ∈ X}
      (fun q ↦ L q.fst y + ⟪(y : P), q.snd⟫_ℝ) :=
    ((h.convexOn_left y y.2).comp_linearMap (WithLp.fstL 2 ℝ E P).toLinearMap).add
      ((((innerSL ℝ (y : P)).comp (WithLp.sndL 2 ℝ E P)).toLinearMap).convexOn hS)
  have he : epigraph (fun q : WithLp 2 (E × P) ↦
      (if q.fst ∈ X then ((L q.fst y + ⟪(y : P), q.snd⟫_ℝ : ℝ) : EReal) else ⊤)) =
      {p | p.1 ∈ {q : WithLp 2 (E × P) | q.fst ∈ X} ∧ L p.1.fst y + ⟪(y : P), p.1.snd⟫_ℝ ≤ p.2} := by
    ext ⟨q, a⟩
    by_cases hq : q.fst ∈ X
    · simp only [epigraph, hq, if_true, mem_setOf_eq, true_and]
      exact EReal.coe_le_coe_iff
    · simp [epigraph, hq]
  rw [he]
  exact hcv.convex_epigraph

omit [FiniteDimensional ℝ E] in
theorem isProper_minimaxIntegrand (h : IsMinimaxProblem L X Y) :
    IsProper (minimaxIntegrand L X Y) := by
  obtain ⟨x, hx⟩ := h.nonempty_left
  obtain ⟨⟨u, hu⟩, -⟩ := isProper_fenchelConjugate (h.isProper_negMinimaxSlice x)
    (h.lowerSemicontinuous_negMinimaxSlice hx) (h.convex_epigraph_negMinimaxSlice hx)
  refine ⟨⟨WithLp.toLp 2 (x, u), by rwa [minimaxIntegrand_eq_fenchelConjugate hx]⟩, fun q ↦ ?_⟩
  obtain ⟨y, hy⟩ := h.nonempty_right
  unfold minimaxIntegrand
  split_ifs
  · exact (EReal.bot_lt_coe _).trans_le (le_iSup₂_of_le y hy le_rfl)
  · exact bot_lt_top

omit [FiniteDimensional ℝ E] in
/-- The parameterization of **11.52** is a dualizing parameterization of the
problem of minimizing `φ`. -/
theorem isDualizingParameterization (h : IsMinimaxProblem L X Y) :
    IsDualizingParameterization (minimaxPrimal L X Y) (minimaxIntegrand L X Y) := by
  have hd := isDualizingParameterization_of_convex h.isProper_minimaxIntegrand
    h.lowerSemicontinuous_minimaxIntegrand h.convex_epigraph_minimaxIntegrand
  rwa [primalObjective_eq] at hd

omit [FiniteDimensional ℝ E] in
/-- The conjugate formula of **11.52**: `-f*(v,y) = inf_{x ∈ X} {L(x,y) - ⟨v,x⟩}`
for `y ∈ Y`, and `-∞` for `y ∉ Y`. -/
theorem neg_fenchelConjugate_minimaxIntegrand (h : IsMinimaxProblem L X Y) (v : E) (y : P) :
    -fenchelConjugate (minimaxIntegrand L X Y) (WithLp.toLp 2 (v, y)) =
      if y ∈ Y then ⨅ x ∈ X, ((L x y - ⟪v, x⟫_ℝ : ℝ) : EReal) else ⊥ := by
  rw [neg_fenchelConjugate_eq_iInf_lagrangian, h.lagrangian_eq]
  by_cases hy : y ∈ Y
  · rw [if_pos hy]
    refine iInf_congr fun x ↦ ?_
    by_cases hx : x ∈ X
    · rw [iInf_pos hx]
      simp [minimaxLagrangian, hx, hy, ← EReal.coe_sub]
    · rw [iInf_neg hx]
      simp [minimaxLagrangian, hx]
  · rw [if_neg hy]
    obtain ⟨x, hx⟩ := h.nonempty_left
    refine le_antisymm ((iInf_le _ x).trans ?_) bot_le
    simp [minimaxLagrangian, hx, hy]

omit [FiniteDimensional ℝ E] in
/-- The dual problem of **11.52** is the maximization of `ψ`. -/
theorem dualObjective_eq (h : IsMinimaxProblem L X Y) :
    dualObjective (minimaxIntegrand L X Y) = minimaxDual L X Y := by
  funext y
  rw [dualObjective, h.neg_fenchelConjugate_minimaxIntegrand]
  simp only [inner_zero_left, sub_zero, minimaxDual]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- **11.52**: the saddle-point set of `L` relative to `X × Y` is that of `l`. -/
theorem argminimaxOn_eq (h : IsMinimaxProblem L X Y) :
    argminimaxOn L X Y = argminimax (minimaxLagrangian L X Y) := by
  ext ⟨x₀, y₀⟩
  constructor
  · rintro ⟨hx₀, hy₀, hs⟩ x y
    constructor
    · by_cases hx : x ∈ X
      · simpa [minimaxLagrangian, hx₀, hy₀, hx] using (hs x hx y₀ hy₀).1
      · simp [minimaxLagrangian, hx]
    · by_cases hy : y ∈ Y
      · simpa [minimaxLagrangian, hx₀, hy₀, hy] using (hs x₀ hx₀ y hy).2
      · simp [minimaxLagrangian, hx₀, hy]
  · intro hs
    obtain ⟨xX, hxX⟩ := h.nonempty_left
    obtain ⟨yY, hyY⟩ := h.nonempty_right
    have hx₀ : x₀ ∈ X := by
      by_contra hx₀
      have h₁ := (hs xX y₀).1
      simp only [minimaxLagrangian, hx₀, hxX, if_false, if_true, top_le_iff] at h₁
      split_ifs at h₁ <;> simp at h₁
    have hy₀ : y₀ ∈ Y := by
      by_contra hy₀
      have h₂ := (hs x₀ yY).2
      simp [minimaxLagrangian, hx₀, hy₀, hyY] at h₂
    refine ⟨hx₀, hy₀, fun x hx y hy ↦ ⟨?_, ?_⟩⟩
    · simpa [minimaxLagrangian, hx₀, hy₀, hx] using (hs x y₀).1
    · simpa [minimaxLagrangian, hx₀, hy₀, hy] using (hs x₀ y).2

theorem weak_duality (h : IsMinimaxProblem L X Y) :
    (⨆ y, minimaxDual L X Y y) ≤ ⨅ x, minimaxPrimal L X Y x := by
  have hw := primal_dual_weak_duality (minimaxIntegrand L X Y)
  rwa [h.dualObjective_eq, primalObjective_eq] at hw

/-- The product structure **11(25)** for the saddle points in **11.52**. -/
theorem argminimaxOn_eq_prod (h : IsMinimaxProblem L X Y)
    (he : (⨅ x, minimaxPrimal L X Y x) = ⨆ y, minimaxDual L X Y y) :
    argminimaxOn L X Y = argmin (minimaxPrimal L X Y) ×ˢ argmax (minimaxDual L X Y) := by
  have hd := h.dualObjective_eq
  rw [h.argminimaxOn_eq, ← h.lagrangian_eq,
    h.isDualizingParameterization.argminimax_eq_prod (by rwa [hd]), hd]

theorem argminimaxOn_eq_empty (h : IsMinimaxProblem L X Y)
    (hlt : (⨆ y, minimaxDual L X Y y) < ⨅ x, minimaxPrimal L X Y x) : argminimaxOn L X Y = ∅ := by
  have hd := h.dualObjective_eq
  rw [h.argminimaxOn_eq, ← h.lagrangian_eq,
    h.isDualizingParameterization.argminimax_eq_empty (by rwa [hd])]

/-- **11.52**: `L` is constant on the saddle-point set, with value
`minimax_{X,Y} L = inf φ = sup ψ`. -/
theorem saddle_value (h : IsMinimaxProblem L X Y) {x₀ : E} {y₀ : P}
    (hs : (x₀, y₀) ∈ argminimaxOn L X Y) :
    (L x₀ y₀ : EReal) = ⨅ x, minimaxPrimal L X Y x ∧ (L x₀ y₀ : EReal) = ⨆ y, minimaxDual L X Y y := by
  have hm := hs
  rw [h.argminimaxOn_eq, ← h.lagrangian_eq] at hm
  obtain ⟨h₁, h₂⟩ := h.isDualizingParameterization.lagrangian_eq_of_mem_argminimax hm
  have hv : lagrangian (minimaxIntegrand L X Y) x₀ y₀ = (L x₀ y₀ : EReal) := by
    rw [h.lagrangian_eq]
    simp [minimaxLagrangian, hs.1, hs.2.1]
  rw [hv] at h₁ h₂
  rw [h.dualObjective_eq] at h₂
  exact ⟨h₁, h₂⟩

/-- **11.52**: the saddle-point set is closed and convex. -/
theorem isClosed_convex_argminimaxOn (h : IsMinimaxProblem L X Y) :
    IsClosed (argminimaxOn L X Y) ∧ Convex ℝ (argminimaxOn L X Y) := by
  obtain ⟨hφl, hφc, hψu, hψc⟩ := primal_dual_objective_geometry h.isProper_minimaxIntegrand
    h.lowerSemicontinuous_minimaxIntegrand h.convex_epigraph_minimaxIntegrand
  rw [primalObjective_eq] at hφl hφc
  rw [h.dualObjective_eq] at hψu hψc
  have h₁ := isClosed_convex_argmin hφl hφc
  have hnl : LowerSemicontinuous (fun y ↦ -minimaxDual L X Y y) :=
    continuous_neg.comp_upperSemicontinuous_antitone hψu EReal.neg_strictAnti.antitone
  have h₂ := isClosed_convex_argmin hnl hψc
  rw [← argmax_eq_argmin_neg] at h₂
  by_cases he : (⨅ x, minimaxPrimal L X Y x) = ⨆ y, minimaxDual L X Y y
  · rw [h.argminimaxOn_eq_prod he]
    exact ⟨h₁.1.prod h₂.1, h₁.2.prod h₂.2⟩
  · rw [h.argminimaxOn_eq_empty (lt_of_le_of_ne h.weak_duality (Ne.symm he))]
    exact ⟨isClosed_empty, convex_empty⟩

/-- **11.52**: the saddle-point set is nonempty and bounded exactly when
`argmin φ` and `argmax ψ` are nonempty and bounded, condition (d) of **11.40**;
by 11.40 this is also equivalent to `0 ∈ int U` and `0 ∈ int V`. -/
theorem argminimaxOn_nonempty_bounded_iff (h : IsMinimaxProblem L X Y) :
    (((argminimaxOn L X Y).Nonempty ∧ IsBounded (argminimaxOn L X Y)) ↔
      ((argmin (minimaxPrimal L X Y)).Nonempty ∧ IsBounded (argmin (minimaxPrimal L X Y))) ∧
      ((argmax (minimaxDual L X Y)).Nonempty ∧ IsBounded (argmax (minimaxDual L X Y)))) ∧
    (((argminimaxOn L X Y).Nonempty ∧ IsBounded (argminimaxOn L X Y)) ↔
      ((0 : P) ∈ interior (effectiveDomain (parametricValue (minimaxIntegrand L X Y))) ∧
        (0 : E) ∈ interior (effectiveDomain (dualParametricValue (minimaxIntegrand L X Y))))) := by
  have hp := h.isProper_minimaxIntegrand
  have hl := h.lowerSemicontinuous_minimaxIntegrand
  have hc := h.convex_epigraph_minimaxIntegrand
  have hbest := (primal_dual_best_case_equivalences hp hl hc).2.2
  simp only [primalObjective_eq, h.dualObjective_eq] at hbest
  have hd : ((argminimaxOn L X Y).Nonempty ∧ IsBounded (argminimaxOn L X Y)) ↔
      ((argmin (minimaxPrimal L X Y)).Nonempty ∧ IsBounded (argmin (minimaxPrimal L X Y))) ∧
      ((argmax (minimaxDual L X Y)).Nonempty ∧ IsBounded (argmax (minimaxDual L X Y))) := by
    constructor
    · rintro ⟨⟨⟨x₀, y₀⟩, hs⟩, hb⟩
      have hm := hs
      rw [h.argminimaxOn_eq, ← h.lagrangian_eq] at hm
      obtain ⟨hx, hy, he⟩ := (h.isDualizingParameterization.minimax_relations x₀ y₀).1.mpr hm
      rw [h.dualObjective_eq] at hy he
      rw [h.argminimaxOn_eq_prod he] at hb
      have hb' := (isBounded_prod_of_nonempty ⟨(x₀, y₀), hx, hy⟩).mp hb
      exact ⟨⟨⟨x₀, hx⟩, hb'.1⟩, ⟨y₀, hy⟩, hb'.2⟩
    · intro hXY
      obtain ⟨hU, hV⟩ := hbest.mpr hXY
      obtain ⟨a, x₀, y₀, hx, hy, ha, hb⟩ := primal_dual_best_case_attainment hp hl hc hU hV
      rw [primalObjective_eq] at hx ha
      rw [h.dualObjective_eq] at hy hb
      rw [h.argminimaxOn_eq_prod (ha.trans hb.symm)]
      exact ⟨⟨(x₀, y₀), hx, hy⟩, hXY.1.2.prod hXY.2.2⟩
  exact ⟨hd, hd.trans hbest.symm⟩

/-- **11.52**: for bounded `X` and `Y` the sets `U` and `V` of **11.40** are the
whole spaces, so the saddle-point set is nonempty and bounded. -/
theorem argminimaxOn_nonempty_bounded_of_bounded (h : IsMinimaxProblem L X Y)
    (hXb : IsBounded X) (hYb : IsBounded Y) :
    effectiveDomain (parametricValue (minimaxIntegrand L X Y)) = univ ∧
      effectiveDomain (dualParametricValue (minimaxIntegrand L X Y)) = univ ∧
      (argminimaxOn L X Y).Nonempty ∧ IsBounded (argminimaxOn L X Y) := by
  have hXk : IsCompact X := Metric.isCompact_of_isClosed_isBounded h.isClosed_left hXb
  have hYk : IsCompact Y := Metric.isCompact_of_isClosed_isBounded h.isClosed_right hYb
  obtain ⟨x₀, hx₀⟩ := h.nonempty_left
  obtain ⟨y₀, hy₀⟩ := h.nonempty_right
  have hU : effectiveDomain (parametricValue (minimaxIntegrand L X Y)) = univ := by
    refine eq_univ_of_forall fun u ↦ ?_
    obtain ⟨y₁, -, hmax⟩ := hYk.exists_isMaxOn ⟨y₀, hy₀⟩
      ((h.continuousOn_right hx₀).add (continuous_id.inner continuous_const).continuousOn :
        ContinuousOn (fun y ↦ L x₀ y + ⟪y, u⟫_ℝ) Y)
    change (⨅ x : E, minimaxIntegrand L X Y (WithLp.toLp 2 (x, u))) < ⊤
    refine (iInf_le _ x₀).trans_lt ?_
    change (if x₀ ∈ X then ⨆ y ∈ Y, ((L x₀ y + ⟪y, u⟫_ℝ : ℝ) : EReal) else ⊤) < ⊤
    rw [if_pos hx₀]
    refine lt_of_le_of_lt (iSup₂_le fun y hy ↦ EReal.coe_le_coe_iff.mpr (hmax hy)) ?_
    exact EReal.coe_lt_top _
  have hV : effectiveDomain (dualParametricValue (minimaxIntegrand L X Y)) = univ := by
    refine eq_univ_of_forall fun v ↦ ?_
    obtain ⟨x₁, -, hmin⟩ := hXk.exists_isMinOn ⟨x₀, hx₀⟩
      ((h.continuousOn_left hy₀).sub (continuous_const.inner continuous_id).continuousOn :
        ContinuousOn (fun x ↦ L x y₀ - ⟪v, x⟫_ℝ) X)
    change (⨅ y : P, fenchelConjugate (minimaxIntegrand L X Y) (WithLp.toLp 2 (v, y))) < ⊤
    refine (iInf_le _ y₀).trans_lt ?_
    have hn := h.neg_fenchelConjugate_minimaxIntegrand v y₀
    rw [if_pos hy₀] at hn
    have hb : ⊥ < -fenchelConjugate (minimaxIntegrand L X Y) (WithLp.toLp 2 (v, y₀)) := by
      rw [hn]
      exact (EReal.bot_lt_coe _).trans_le (le_iInf₂ fun x hx ↦ EReal.coe_le_coe_iff.mpr (hmin hx))
    rwa [EReal.lt_neg_comm, EReal.neg_bot] at hb
  refine ⟨hU, hV, (h.argminimaxOn_nonempty_bounded_iff.2.mpr ?_)⟩
  rw [hU, hV, interior_univ, interior_univ]
  exact ⟨mem_univ _, mem_univ _⟩

/-- **11.52**, smooth case: if `L` is `C¹` on an open set containing `X × Y`, the
saddle points are the pairs in `X × Y` with `-∇ₓL(x̄,ȳ) ∈ N_X(x̄)` and
`∇_yL(x̄,ȳ) ∈ N_Y(ȳ)`. -/
theorem mem_argminimaxOn_iff_normal (h : IsMinimaxProblem L X Y) {O : Set (E × P)}
    (hO : IsOpen O) (hXY : X ×ˢ Y ⊆ O) (hL : ContDiffOn ℝ 1 (fun p : E × P ↦ L p.1 p.2) O)
    (x₀ : E) (y₀ : P) :
    (x₀, y₀) ∈ argminimaxOn L X Y ↔ x₀ ∈ X ∧ y₀ ∈ Y ∧
      -gradient (fun x ↦ L x y₀) x₀ ∈ normalCone X x₀ ∧
      gradient (fun y ↦ L x₀ y) y₀ ∈ normalCone Y y₀ := by
  have key (hx₀ : x₀ ∈ X) (hy₀ : y₀ ∈ Y) :
      ((∀ x ∈ X, L x₀ y₀ ≤ L x y₀) ↔ -gradient (fun x ↦ L x y₀) x₀ ∈ normalCone X x₀) ∧
      ((∀ y ∈ Y, L x₀ y ≤ L x₀ y₀) ↔ gradient (fun y ↦ L x₀ y) y₀ ∈ normalCone Y y₀) := by
    have hD : DifferentiableAt ℝ (fun p : E × P ↦ L p.1 p.2) (x₀, y₀) :=
      (hL.contDiffAt (hO.mem_nhds (hXY ⟨hx₀, hy₀⟩))).differentiableAt one_ne_zero
    have hpx : DifferentiableAt ℝ (fun x : E ↦ (x, y₀)) x₀ :=
      differentiableAt_id.prodMk (differentiableAt_const y₀)
    have hpy : DifferentiableAt ℝ (fun y : P ↦ (x₀, y)) y₀ :=
      (differentiableAt_const x₀).prodMk differentiableAt_id
    have hDx : DifferentiableAt ℝ (fun x ↦ L x y₀) x₀ := by
      have hc := hD.comp x₀ hpx
      exact hc
    have hDy : DifferentiableAt ℝ (fun y ↦ L x₀ y) y₀ := by
      have hc := hD.comp y₀ hpy
      exact hc
    refine ⟨isMinOn_iff_neg_gradient_mem_normalCone h.convex_left hx₀ (h.convexOn_left y₀ hy₀)
      hDx, ?_⟩
    have hneg : HasGradientAt (-(fun y ↦ L x₀ y)) (-gradient (fun y ↦ L x₀ y) y₀) y₀ := by
      rw [hasGradientAt_iff_hasFDerivAt, map_neg]
      exact hDy.hasGradientAt.hasFDerivAt.neg
    have h₂ := isMinOn_iff_neg_gradient_mem_normalCone h.convex_right hy₀
      (h.concaveOn_right x₀ hx₀).neg hneg.differentiableAt
    rw [hneg.gradient, neg_neg] at h₂
    rw [← h₂]
    simp only [Pi.neg_apply, neg_le_neg_iff]
  constructor
  · rintro ⟨hx₀, hy₀, hs⟩
    obtain ⟨k₁, k₂⟩ := key hx₀ hy₀
    exact ⟨hx₀, hy₀, k₁.mp fun x hx ↦ (hs x hx y₀ hy₀).1, k₂.mp fun y hy ↦ (hs x₀ hx₀ y hy).2⟩
  · rintro ⟨hx₀, hy₀, hnx, hny⟩
    obtain ⟨k₁, k₂⟩ := key hx₀ hy₀
    exact ⟨hx₀, hy₀, fun x hx y hy ↦ ⟨k₁.mpr hnx x hx, k₂.mpr hny y hy⟩⟩

end IsMinimaxProblem

end
end RW
