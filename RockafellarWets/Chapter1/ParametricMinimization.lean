/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 1F: Parametric dependence

* **Definition 1.16**: the two printed forms of uniform level boundedness agree with the
  closed-ball form `IsLevelBoundedInXLocallyUniformly` of Chapter 3.
* **Theorem 1.17**: parametric minimization, clauses (a), (b) and (c), for the value function
  `p = valueFunction f` and the optimal-set mapping `P = paramArgmin f`.
* **Proposition 1.18**: the epigraphical projection.
* **Exercise 1.19**: constraints in parametric minimization.
* **Example 1.20**: distance functions and projections.

The book's `ℝⁿ × ℝᵐ` is a product `E × F` of real normed spaces, with `E` finite-dimensional
wherever compactness is used.
-/

import RockafellarWets.Chapter1.Attainment
import RockafellarWets.Chapter7.OptimalSetContinuity
import RockafellarWets.Chapter7.LocalMinimization
import RockafellarWets.Chapter5.ProjectionMappings

open Set Filter Topology Metric Bornology

noncomputable section

namespace RW

/-- A sequence that eventually lies in a bounded set has bounded range. -/
theorem isBounded_range_of_eventually_mem {X : Type*} [PseudoMetricSpace X] {xs : ℕ → X}
    {S : Set X} (hS : IsBounded S) (h : ∀ᶠ n in atTop, xs n ∈ S) : IsBounded (range xs) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have hsub : range xs ⊆ S ∪ xs '' Iio N := by
    rintro _ ⟨n, rfl⟩
    by_cases hn : N ≤ n
    · exact Or.inl (hN n hn)
    · exact Or.inr ⟨n, not_le.1 hn, rfl⟩
  exact (hS.union ((finite_Iio N).image xs).isBounded).subset hsub

/-- The parenthetical case in **Theorem 1.17(b)**: continuity of `p` at `ū` relative to a set `U`
containing the `uν` gives `p(uν) → p(ū)`. -/
theorem tendsto_comp_of_continuousWithinAt {F : Type*} [TopologicalSpace F] {p : F → EReal}
    {U : Set F} {u : F}
    (hc : ContinuousWithinAt p U u) {us : ℕ → F} (hus : Tendsto us atTop (𝓝 u))
    (hU : ∀ n, us n ∈ U) : Tendsto (fun n ↦ p (us n)) atTop (𝓝 (p u)) :=
  hc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hus, Eventually.of_forall hU⟩)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Definition 1.16 -/

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- **Definition 1.16**: `f(x,u)` is level-bounded in `x` locally uniformly in `u` in the
closed-ball form of Chapter 3, iff for each `ū` and `α ∈ ℝ` some `V ∈ N(ū)` and bounded `B` have
`{x | f(x,u) ≤ α} ⊂ B` for all `u ∈ V`, iff some `V ∈ N(ū)` makes
`{(x,u) | u ∈ V, f(x,u) ≤ α}` bounded in `ℝⁿ × ℝᵐ`. -/
theorem isLevelBoundedInXLocallyUniformly_tfae (f : E × F → EReal) :
    List.TFAE [IsLevelBoundedInXLocallyUniformly f,
      ∀ (u : F) (α : ℝ), ∃ V ∈ 𝓝 u, ∃ B : Set E, IsBounded B ∧
        ∀ v ∈ V, ∀ x, f (x, v) ≤ α → x ∈ B,
      ∀ (u : F) (α : ℝ), ∃ V ∈ 𝓝 u, IsBounded {q : E × F | q.2 ∈ V ∧ f q ≤ α}] := by
  tfae_have 1 → 2 := by
    intro h u α
    obtain ⟨ε, hε, hb⟩ := h u α
    refine ⟨closedBall u ε, closedBall_mem_nhds u hε, _, hb.image_fst, fun v hv x hx ↦ ?_⟩
    exact ⟨(x, v), ⟨⟨mem_univ x, hv⟩, hx⟩, rfl⟩
  tfae_have 2 → 3 := by
    intro h u α
    obtain ⟨V, hV, B, hB, hsub⟩ := h u α
    refine ⟨V ∩ closedBall u 1, inter_mem hV (closedBall_mem_nhds u one_pos),
      (hB.prod isBounded_closedBall).subset fun q hq ↦ ⟨hsub q.2 hq.1.1 q.1 hq.2, hq.1.2⟩⟩
  tfae_have 3 → 1 := by
    intro h u α
    obtain ⟨V, hV, hb⟩ := h u α
    obtain ⟨ε, hε, hεV⟩ := nhds_basis_closedBall.mem_iff.1 hV
    exact ⟨ε, hε, hb.subset fun q hq ↦ ⟨hεV hq.1.2, hq.2⟩⟩
  tfae_finish

/-! ## Theorem 1.17 -/

section ParametricMinimization

variable [FiniteDimensional ℝ E]

/-- **Theorem 1.17(a)** (parametric minimization): for `f` proper, lsc and level-bounded in `x`
locally uniformly in `u`, the value function `p(u) = inf_x f(x,u)` is proper and lsc, and
`P(u) = argmin_x f(x,u)` is nonempty and compact for `u ∈ dom p` and empty otherwise. -/
theorem parametric_minimization_a {f : E × F → EReal} (hlsc : LowerSemicontinuous f)
    (hp : IsProper f) (hb : IsLevelBoundedInXLocallyUniformly f) :
    IsProper (valueFunction f) ∧ LowerSemicontinuous (valueFunction f) ∧
      (∀ u ∈ effectiveDomain (valueFunction f),
        (paramArgmin f u).Nonempty ∧ IsCompact (paramArgmin f u)) ∧
      ∀ u ∉ effectiveDomain (valueFunction f), paramArgmin f u = ∅ := by
  refine ⟨isProper_valueFunction_of_lsc_localUniform hlsc hp hb,
    lowerSemicontinuous_valueFunction_of_localUniform hlsc hp hb,
    fun u hu ↦ ⟨paramArgmin_nonempty hlsc hp hb hu, (paramArgmin_compact_and_dom hlsc hp hb).1 u⟩,
    fun u hu ↦ eq_empty_iff_forall_notMem.2 fun x hx ↦ hu ((mem_paramArgmin_iff f u x).1 hx).2⟩

/-- **Theorem 1.17(b)**: if `xν ∈ P(uν)` and `uν → ū ∈ dom p` with `p(uν) → p(ū)`, then
`{xν}` is bounded and all its cluster points lie in `P(ū)`.  Membership `xν ∈ P(uν)` is only
needed for all large `ν`. -/
theorem parametric_minimization_b {f : E × F → EReal} (hlsc : LowerSemicontinuous f)
    (hp : IsProper f) (hb : IsLevelBoundedInXLocallyUniformly f) {us : ℕ → F} {u : F}
    {xs : ℕ → E} (hxs : ∀ᶠ n in atTop, xs n ∈ paramArgmin f (us n))
    (hus : Tendsto us atTop (𝓝 u)) (hu : u ∈ effectiveDomain (valueFunction f))
    (hpu : Tendsto (fun n ↦ valueFunction f (us n)) atTop (𝓝 (valueFunction f u))) :
    IsBounded (range xs) ∧ ∀ x, MapClusterPt x atTop xs → x ∈ paramArgmin f u := by
  have hpp := (parametric_minimization_a hlsc hp hb).1
  set a := (valueFunction f u).toReal with ha_def
  have ha : valueFunction f u = a := (EReal.coe_toReal (ne_of_lt hu) (hpp.2 u).ne').symm
  have hev : ∀ β : ℝ, a < β → ∀ᶠ n in atTop, (xs n, us n) ∈ levelSet f β := by
    intro β hβ
    have : ∀ᶠ n in atTop, valueFunction f (us n) < β :=
      hpu.eventually (gt_mem_nhds (ha ▸ EReal.coe_lt_coe_iff.2 hβ))
    filter_upwards [this, hxs] with n hn hxn
    exact (((mem_paramArgmin_iff f (us n) (xs n)).1 hxn).1.trans_lt hn).le
  have hcl : ∀ β : ℝ, IsClosed (levelSet f β) := lowerSemicontinuous_iff_isClosed_levelSet.1 hlsc
  refine ⟨?_, fun x hx ↦ ?_⟩
  · obtain ⟨ε, hε, hbd⟩ := hb u (a + 1)
    refine isBounded_range_of_eventually_mem hbd.image_fst ?_
    filter_upwards [hev (a + 1) (by linarith), hus.eventually (closedBall_mem_nhds u hε)]
      with n hn hn'
    exact ⟨(xs n, us n), ⟨⟨mem_univ _, hn'⟩, hn⟩, rfl⟩
  · obtain ⟨φ, hφ, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hx
    have hpair : Tendsto (fun k ↦ (xs (φ k), us (φ k))) atTop (𝓝 (x, u)) :=
      hlim.prodMk_nhds (hus.comp hφ.tendsto_atTop)
    have hle : ∀ β : ℝ, a < β → f (x, u) ≤ β := fun β hβ ↦
      (hcl β).mem_of_tendsto hpair ((hev β hβ).filter_mono hφ.tendsto_atTop |>.mono
        fun _ h ↦ h)
    have hfx : f (x, u) ≤ a := ereal_le_coe_of_forall_pos fun ε hε ↦ hle _ (by linarith)
    refine (mem_paramArgmin_iff f u x).2 ⟨le_antisymm (hfx.trans ha.ge) ?_, hu⟩
    exact iInf_le (fun y ↦ f (y, u)) x

/-- **Theorem 1.17(c)**: `p` is continuous at `ū` relative to `U` if some `x̄ ∈ P(ū)` has
`f(x̄, u)` continuous in `u` at `ū` relative to `U`. -/
theorem parametric_minimization_c {f : E × F → EReal} (hlsc : LowerSemicontinuous f)
    (hp : IsProper f) (hb : IsLevelBoundedInXLocallyUniformly f) {U : Set F} {u : F} {x : E}
    (hx : x ∈ paramArgmin f u) (hc : ContinuousWithinAt (fun v ↦ f (x, v)) U u) :
    ContinuousWithinAt (valueFunction f) U u := by
  rw [continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  refine ⟨(parametric_minimization_a hlsc hp hb).2.1.lowerSemicontinuousWithinAt U u, ?_⟩
  intro y hy
  have hfx : f (x, u) = valueFunction f u := ((mem_paramArgmin_iff f u x).1 hx).1
  rw [← hfx] at hy
  exact (hc.upperSemicontinuousWithinAt y hy).mono fun v hv ↦
    lt_of_le_of_lt (iInf_le (fun z ↦ f (z, v)) x) hv

end ParametricMinimization

/-! ## Proposition 1.18 -/

section EpigraphicalProjection

theorem mem_valueProjection_image_epigraph {f : E × F → EReal} {u : F} {a : ℝ} :
    (u, a) ∈ valueProjection '' epigraph f ↔ ∃ x, f (x, u) ≤ a := by
  constructor
  · rintro ⟨⟨⟨x, v⟩, b⟩, hq, he⟩
    simp only [valueProjection_apply, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨x, (mem_epigraph_iff f _ _).1 hq⟩
  · rintro ⟨x, hx⟩
    exact ⟨((x, u), a), (mem_epigraph_iff f _ _).2 hx, rfl⟩

/-- **Proposition 1.18**: if `P(u)` is attained for each `u ∈ dom p`, then `epi p` is the image
`E` of `epi f` under `(x,u,α) ↦ (u,α)`. -/
theorem epigraph_valueFunction_eq_image_of_attained {f : E × F → EReal}
    (h : ∀ u, valueFunction f u < ⊤ → (paramArgmin f u).Nonempty) :
    epigraph (valueFunction f) = valueProjection '' epigraph f := by
  refine subset_antisymm ?_ valueProjection_image_epigraph_subset_epigraph_valueFunction
  rintro ⟨u, a⟩ hua
  have hle : valueFunction f u ≤ a := (mem_epigraph_iff _ _ _).1 hua
  obtain ⟨x, hx⟩ := h u (lt_of_le_of_lt hle (EReal.coe_lt_top a))
  exact mem_valueProjection_image_epigraph.2
    ⟨x, ((mem_paramArgmin_iff f u x).1 hx).1.trans_le hle⟩

/-- **Proposition 1.18**, general case: `epi p` is obtained from `E` by closing its intersection
with each vertical line. -/
theorem epigraph_valueFunction_vertical_closure (f : E × F → EReal) (u : F) :
    {a : ℝ | (u, a) ∈ epigraph (valueFunction f)} =
      closure {a : ℝ | (u, a) ∈ valueProjection '' epigraph f} := by
  have hset : {a : ℝ | (u, a) ∈ epigraph (valueFunction f)} =
      (fun a : ℝ ↦ (a : EReal)) ⁻¹' Ici (valueFunction f u) := by
    ext a; simp [mem_epigraph_iff]
  apply subset_antisymm
  · intro a ha
    have hle : valueFunction f u ≤ a := (mem_epigraph_iff _ _ _).1 ha
    have hseq : Tendsto (fun n : ℕ ↦ a + 1 / ((n : ℝ) + 1)) atTop (𝓝 a) := by
      have := (tendsto_const_nhds (x := a)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa using this
    refine mem_closure_of_tendsto hseq (Eventually.of_forall fun n ↦ ?_)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : valueFunction f u < ((a + 1 / ((n : ℝ) + 1) : ℝ) : EReal) :=
      lt_of_le_of_lt hle (EReal.coe_lt_coe_iff.2 (by linarith))
    obtain ⟨x, hx⟩ := iInf_lt_iff.1 hlt
    exact mem_valueProjection_image_epigraph.2 ⟨x, hx.le⟩
  · rw [hset]
    refine closure_minimal (fun a ha ↦ ?_)
      (isClosed_Ici.preimage continuous_coe_real_ereal)
    obtain ⟨x, hx⟩ := mem_valueProjection_image_epigraph.1 ha
    exact (iInf_le (fun y ↦ f (y, u)) x).trans hx

end EpigraphicalProjection

/-! ## Exercise 1.19 -/

section Constraints

variable {ι : Type*}

/-- The pairs `(x,u) ∈ X × U` satisfying the constraints of Exercise 1.19. -/
def parametricFeasibleSet (fs : ι → E × F → ℝ) (I₁ I₂ : Set ι) (X : Set E) (U : Set F) :
    Set (E × F) :=
  {q | q.1 ∈ X ∧ q.2 ∈ U ∧ (∀ i ∈ I₁, fs i q ≤ 0) ∧ ∀ i ∈ I₂, fs i q = 0}

/-- The objective of Exercise 1.19: `f₀(x,u)` on the feasible pairs and `∞` elsewhere. -/
def parametricConstrainedObjective (f₀ : E × F → ℝ) (fs : ι → E × F → ℝ) (I₁ I₂ : Set ι)
    (X : Set E) (U : Set F) : E × F → EReal :=
  restrictedObjective f₀ (parametricFeasibleSet fs I₁ I₂ X U)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem isClosed_parametricFeasibleSet {fs : ι → E × F → ℝ} {I₁ I₂ : Set ι} {X : Set E}
    {U : Set F} (hX : IsClosed X) (hU : IsClosed U) (hfs : ∀ i, ContinuousOn (fs i) (X ×ˢ U)) :
    IsClosed (parametricFeasibleSet fs I₁ I₂ X U) := by
  have hXU : IsClosed (X ×ˢ U) := hX.prod hU
  have h1 : ∀ i, IsClosed ((X ×ˢ U) ∩ fs i ⁻¹' Iic 0) := fun i ↦
    (hfs i).preimage_isClosed_of_isClosed hXU isClosed_Iic
  have h2 : ∀ i, IsClosed ((X ×ˢ U) ∩ fs i ⁻¹' {0}) := fun i ↦
    (hfs i).preimage_isClosed_of_isClosed hXU isClosed_singleton
  have heq : parametricFeasibleSet fs I₁ I₂ X U = (X ×ˢ U) ∩
      (⋂ i ∈ I₁, (X ×ˢ U) ∩ fs i ⁻¹' Iic 0) ∩ (⋂ i ∈ I₂, (X ×ˢ U) ∩ fs i ⁻¹' {0}) := by
    ext q
    simp only [parametricFeasibleSet, mem_setOf_eq, mem_inter_iff, mem_prod, mem_iInter,
      mem_preimage, mem_Iic, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hu, h₁, h₂⟩
      exact ⟨⟨⟨hx, hu⟩, fun i hi ↦ ⟨⟨hx, hu⟩, h₁ i hi⟩⟩, fun i hi ↦ ⟨⟨hx, hu⟩, h₂ i hi⟩⟩
    · rintro ⟨⟨⟨hx, hu⟩, h₁⟩, h₂⟩
      exact ⟨hx, hu, fun i hi ↦ (h₁ i hi).2, fun i hi ↦ (h₂ i hi).2⟩
  rw [heq]
  exact (hXU.inter (isClosed_biInter fun i _ ↦ h1 i)).inter (isClosed_biInter fun i _ ↦ h2 i)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The integrand of Exercise 1.19 is lsc, never `-∞`, and level-bounded in `x` locally uniformly
in `u` under the hypotheses of the exercise. -/
theorem parametricConstrainedObjective_basic {f₀ : E × F → ℝ} {fs : ι → E × F → ℝ}
    {I₁ I₂ : Set ι} {X : Set E} {U : Set F} (hX : IsClosed X) (hU : IsClosed U)
    (hf₀ : ContinuousOn f₀ (X ×ˢ U)) (hfs : ∀ i, ContinuousOn (fs i) (X ×ˢ U))
    (hbd : ∀ v ∈ U, ∀ ε > (0 : ℝ), ∀ α : ℝ, IsBounded
      {q : E × F | q ∈ parametricFeasibleSet fs I₁ I₂ X U ∧ ‖q.2 - v‖ ≤ ε ∧ f₀ q ≤ α}) :
    LowerSemicontinuous (parametricConstrainedObjective f₀ fs I₁ I₂ X U) ∧
      IsLevelBoundedInXLocallyUniformly (parametricConstrainedObjective f₀ fs I₁ I₂ X U) ∧
      ∀ q, ⊥ < parametricConstrainedObjective f₀ fs I₁ I₂ X U q := by
  set K := parametricFeasibleSet fs I₁ I₂ X U with hKdef
  set g := parametricConstrainedObjective f₀ fs I₁ I₂ X U with hgdef
  have hK : IsClosed K := isClosed_parametricFeasibleSet hX hU hfs
  have hKsub : K ⊆ X ×ˢ U := fun q hq ↦ ⟨hq.1, hq.2.1⟩
  have hgK : ∀ q ∈ K, g q = f₀ q := fun q hq ↦ restrictedObjective_of_mem hq
  have hgnK : ∀ q ∉ K, g q = ⊤ := fun q hq ↦ restrictedObjective_of_not_mem hq
  have hmemK : ∀ q (α : ℝ), g q ≤ α → q ∈ K := by
    intro q α hq
    by_contra hqK
    rw [hgnK q hqK] at hq
    exact absurd hq (by simp)
  refine ⟨?_, ?_, fun q ↦ ?_⟩
  · refine lowerSemicontinuous_iff_isClosed_levelSet.2 fun α ↦ ?_
    rw [hgdef, parametricConstrainedObjective, levelSet_restrictedObjective]
    exact (hf₀.mono hKsub).preimage_isClosed_of_isClosed hK isClosed_Iic
  · intro v α
    by_cases hv : v ∈ U
    · refine ⟨1, one_pos, (hbd v hv 1 one_pos α).subset ?_⟩
      rintro q ⟨⟨-, hq2⟩, hqα⟩
      have hqK : q ∈ K := hmemK q α hqα
      have hle : g q ≤ α := hqα
      rw [hgK q hqK] at hle
      exact ⟨hqK, by simpa [dist_eq_norm] using hq2, EReal.coe_le_coe_iff.1 hle⟩
    · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hU.isOpen_compl.mem_nhds hv)
      refine ⟨ε / 2, by positivity, Bornology.isBounded_empty.subset ?_⟩
      rintro q ⟨⟨-, hq2⟩, hqα⟩
      exact hball (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hq2) (by linarith)))
        (hmemK q α hqα).2.1
  · by_cases hq : q ∈ K
    · rw [hgK q hq]; exact EReal.bot_lt_coe _
    · rw [hgnK q hq]; exact bot_lt_top

variable [FiniteDimensional ℝ E]

/-- **Exercise 1.19** (constraints in parametric minimization), first part: with `X`, `U` closed,
`f₀` and the constraint functions continuous on `X × U`, and the boundedness hypothesis, the
optimal value `p` is lsc (and `∞` off `U`), and `P(u)` is nonempty and compact whenever `u ∈ U`
has `p(u) < ∞`. -/
theorem constraints_in_parametric_minimization {f₀ : E × F → ℝ} {fs : ι → E × F → ℝ}
    {I₁ I₂ : Set ι} {X : Set E} {U : Set F} (hX : IsClosed X) (hU : IsClosed U)
    (hf₀ : ContinuousOn f₀ (X ×ˢ U)) (hfs : ∀ i, ContinuousOn (fs i) (X ×ˢ U))
    (hbd : ∀ v ∈ U, ∀ ε > (0 : ℝ), ∀ α : ℝ, IsBounded
      {q : E × F | q ∈ parametricFeasibleSet fs I₁ I₂ X U ∧ ‖q.2 - v‖ ≤ ε ∧ f₀ q ≤ α}) :
    LowerSemicontinuous (valueFunction (parametricConstrainedObjective f₀ fs I₁ I₂ X U)) ∧
      (∀ u ∉ U, valueFunction (parametricConstrainedObjective f₀ fs I₁ I₂ X U) u = ⊤) ∧
      ∀ u ∈ U, valueFunction (parametricConstrainedObjective f₀ fs I₁ I₂ X U) u < ⊤ →
        (paramArgmin (parametricConstrainedObjective f₀ fs I₁ I₂ X U) u).Nonempty ∧
          IsCompact (paramArgmin (parametricConstrainedObjective f₀ fs I₁ I₂ X U) u) := by
  set K := parametricFeasibleSet fs I₁ I₂ X U with hKdef
  set g := parametricConstrainedObjective f₀ fs I₁ I₂ X U with hgdef
  obtain ⟨hlsc, hlb, hbot⟩ := parametricConstrainedObjective_basic hX hU hf₀ hfs hbd
  have hgK : ∀ q ∈ K, g q = f₀ q := fun q hq ↦ restrictedObjective_of_mem hq
  have hgnK : ∀ q ∉ K, g q = ⊤ := fun q hq ↦ restrictedObjective_of_not_mem hq
  have hoff : ∀ u ∉ U, valueFunction g u = ⊤ := fun u hu ↦
    top_le_iff.1 (le_iInf fun x ↦ (hgnK (x, u) fun hq ↦ hu hq.2.1).ge)
  rcases K.eq_empty_or_nonempty with hKe | ⟨q₀, hq₀⟩
  · have htop : ∀ u, valueFunction g u = ⊤ := fun u ↦
      top_le_iff.1 (le_iInf fun x ↦ (hgnK (x, u) (by simp [hKe])).ge)
    refine ⟨?_, hoff, fun u _ hu ↦ absurd (htop u) hu.ne⟩
    have : valueFunction g = fun _ ↦ ⊤ := funext htop
    rw [this]
    exact lowerSemicontinuous_const
  have hp : IsProper g := ⟨⟨q₀, by rw [hgK q₀ hq₀]; exact EReal.coe_lt_top _⟩, hbot⟩
  obtain ⟨-, hplsc, hP, -⟩ := parametric_minimization_a hlsc hp hlb
  exact ⟨hplsc, hoff, fun u _ hu ↦ hP u hu⟩

/-- **Exercise 1.19**, second part: if only `f₀` depends on `u` and the constraints are satisfied
by at least one `x`, then `dom p = U`, `p` is continuous relative to `U`, and whenever
`xν ∈ P(uν)` with `uν → ū` in `U`, all cluster points of `{xν}` lie in `P(ū)`. -/
theorem constraints_in_parametric_minimization_of_fixed {f₀ : E × F → ℝ} {gs : ι → E → ℝ}
    {I₁ I₂ : Set ι} {X : Set E} {U : Set F} (hX : IsClosed X) (hU : IsClosed U)
    (hf₀ : ContinuousOn f₀ (X ×ˢ U)) (hgs : ∀ i, ContinuousOn (gs i) X)
    (hfeas : ∃ x ∈ X, (∀ i ∈ I₁, gs i x ≤ 0) ∧ ∀ i ∈ I₂, gs i x = 0)
    (hbd : ∀ v ∈ U, ∀ ε > (0 : ℝ), ∀ α : ℝ, IsBounded
      {q : E × F | q ∈ parametricFeasibleSet (fun i q ↦ gs i q.1) I₁ I₂ X U ∧
        ‖q.2 - v‖ ≤ ε ∧ f₀ q ≤ α}) :
    effectiveDomain
        (valueFunction (parametricConstrainedObjective f₀ (fun i q ↦ gs i q.1) I₁ I₂ X U)) = U ∧
      (∀ u ∈ U, ContinuousWithinAt
        (valueFunction (parametricConstrainedObjective f₀ (fun i q ↦ gs i q.1) I₁ I₂ X U)) U u) ∧
      ∀ (us : ℕ → F) (u : F) (xs : ℕ → E), (∀ n, us n ∈ U) → u ∈ U →
        Tendsto us atTop (𝓝 u) →
        (∀ n, xs n ∈ paramArgmin
          (parametricConstrainedObjective f₀ (fun i q ↦ gs i q.1) I₁ I₂ X U) (us n)) →
        ∀ x, MapClusterPt x atTop xs →
          x ∈ paramArgmin (parametricConstrainedObjective f₀ (fun i q ↦ gs i q.1) I₁ I₂ X U) u := by
  set fs : ι → E × F → ℝ := fun i q ↦ gs i q.1 with hfsdef
  set K := parametricFeasibleSet fs I₁ I₂ X U with hKdef
  set g := parametricConstrainedObjective f₀ fs I₁ I₂ X U with hgdef
  have hfs : ∀ i, ContinuousOn (fs i) (X ×ˢ U) := fun i ↦
    (hgs i).comp continuousOn_fst fun q hq ↦ hq.1
  obtain ⟨hlsc, hlb, hbot⟩ := parametricConstrainedObjective_basic hX hU hf₀ hfs hbd
  obtain ⟨-, hoff, -⟩ := constraints_in_parametric_minimization hX hU hf₀ hfs hbd
  have hgK : ∀ q ∈ K, g q = f₀ q := fun q hq ↦ restrictedObjective_of_mem hq
  have hgnK : ∀ q ∉ K, g q = ⊤ := fun q hq ↦ restrictedObjective_of_not_mem hq
  obtain ⟨x₀, hx₀X, hx₀⟩ := hfeas
  have hfeasK : ∀ x u, x ∈ X → u ∈ U → (∀ i ∈ I₁, gs i x ≤ 0) → (∀ i ∈ I₂, gs i x = 0) →
      (x, u) ∈ K := fun x u hx hu h1 h2 ↦ ⟨hx, hu, h1, h2⟩
  have hproper : ∀ u ∈ U, IsProper g := fun u hu ↦
    ⟨⟨(x₀, u), by rw [hgK _ (hfeasK x₀ u hx₀X hu hx₀.1 hx₀.2)]; exact EReal.coe_lt_top _⟩, hbot⟩
  have hdom : effectiveDomain (valueFunction g) = U := by
    ext u
    constructor
    · intro hu
      by_contra hU'
      exact (ne_of_lt hu) (hoff u hU')
    · intro hu
      have hq : (x₀, u) ∈ K := hfeasK x₀ u hx₀X hu hx₀.1 hx₀.2
      exact lt_of_le_of_lt (iInf_le (fun x ↦ g (x, u)) x₀)
        (by rw [hgK _ hq]; exact EReal.coe_lt_top _)
  have hcont : ∀ u ∈ U, ContinuousWithinAt (valueFunction g) U u := by
    intro u hu
    have hp := hproper u hu
    have hud : u ∈ effectiveDomain (valueFunction g) := by rw [hdom]; exact hu
    obtain ⟨x, hx⟩ := ((parametric_minimization_a hlsc hp hlb).2.2.1 u hud).1
    have hxK : (x, u) ∈ K := by
      by_contra h
      have h1 := ((mem_paramArgmin_iff g u x).1 hx)
      rw [hgnK _ h] at h1
      exact (ne_of_lt h1.2) h1.1.symm
    have hc : ContinuousWithinAt (fun v ↦ g (x, v)) U u := by
      have h1 : ContinuousWithinAt (fun v ↦ ((f₀ (x, v) : ℝ) : EReal)) U u :=
        continuous_coe_real_ereal.continuousAt.comp_continuousWithinAt
          ((hf₀.comp (continuousOn_const.prodMk continuousOn_id)
            (fun v hv ↦ ⟨hxK.1, hv⟩)) u hu)
      exact h1.congr (fun v hv ↦ hgK _ (hfeasK x v hxK.1 hv hxK.2.2.1 hxK.2.2.2)) (hgK _ hxK)
    exact parametric_minimization_c hlsc hp hlb hx hc
  refine ⟨hdom, hcont, fun us u xs hus hu hlim hxs x hx ↦ ?_⟩
  have hud : u ∈ effectiveDomain (valueFunction g) := by rw [hdom]; exact hu
  exact (parametric_minimization_b hlsc (hproper u hu) hlb (Eventually.of_forall hxs) hlim hud
    (tendsto_comp_of_continuousWithinAt (hcont u hu) hlim hus)).2 x hx

end Constraints

/-! ## Example 1.20 -/

section Distance

omit [NormedSpace ℝ E] in
/-- A point of `C` is nearest to `x` iff its distance from `x` is `d_C(x)`. -/
theorem mem_projMapping_iff_norm_eq_infDist {C : Set E} (hne : C.Nonempty) {x w : E} :
    w ∈ projMapping C x ↔ w ∈ C ∧ ‖w - x‖ = infDist x C := by
  rw [mem_projMapping]
  constructor
  · rintro ⟨hw, hmin⟩
    refine ⟨hw, le_antisymm ((le_infDist hne).2 fun w' hw' ↦ ?_) ?_⟩
    · rw [dist_comm, dist_eq_norm]; exact hmin w' hw'
    · rw [← dist_eq_norm, dist_comm]; exact infDist_le_dist_of_mem hw
  · rintro ⟨hw, heq⟩
    refine ⟨hw, fun w' hw' ↦ ?_⟩
    rw [heq, ← dist_eq_norm, dist_comm]
    exact infDist_le_dist_of_mem hw'

omit [NormedSpace ℝ E] in
theorem projMapping_eq_inter_closedBall {C : Set E} (hne : C.Nonempty) (x : E) :
    projMapping C x = C ∩ closedBall x (infDist x C) := by
  ext w
  rw [mem_projMapping_iff_norm_eq_infDist hne, mem_inter_iff, mem_closedBall, dist_eq_norm]
  constructor
  · rintro ⟨hw, heq⟩; exact ⟨hw, heq.le⟩
  · rintro ⟨hw, hle⟩
    refine ⟨hw, le_antisymm hle ?_⟩
    rw [← dist_eq_norm, dist_comm]
    exact infDist_le_dist_of_mem hw

variable [FiniteDimensional ℝ E]

/-- **Example 1.20** (distance functions and projections): for a nonempty closed `C`, the
distance `d_C` is continuous, every `P_C(x)` is nonempty and compact, and whenever
`wν ∈ P_C(xν)` with `xν → x̄`, the sequence `{wν}` is bounded with all cluster points in
`P_C(x̄)`. -/
theorem distance_functions_and_projections {C : Set E} (hC : IsClosed C) (hne : C.Nonempty) :
    Continuous (fun x ↦ infDist x C) ∧
      (∀ x, (projMapping C x).Nonempty ∧ IsCompact (projMapping C x)) ∧
      ∀ (xs ws : ℕ → E) (x : E), (∀ n, ws n ∈ projMapping C (xs n)) →
        Tendsto xs atTop (𝓝 x) →
        IsBounded (range ws) ∧ ∀ w, MapClusterPt w atTop ws → w ∈ projMapping C x := by
  refine ⟨continuous_infDist_pt C, fun x ↦ ⟨projMapping_nonempty hC hne x, ?_⟩,
    fun xs ws x hws hxs ↦ ?_⟩
  · rw [projMapping_eq_inter_closedBall hne]
    exact (isCompact_closedBall x _).inter_left hC
  have hd : Tendsto (fun n ↦ infDist (xs n) C) atTop (𝓝 (infDist x C)) :=
    ((continuous_infDist_pt C).tendsto x).comp hxs
  have hnorm : ∀ n, ‖ws n - xs n‖ = infDist (xs n) C := fun n ↦
    ((mem_projMapping_iff_norm_eq_infDist hne).1 (hws n)).2
  refine ⟨?_, fun w hw ↦ ?_⟩
  · obtain ⟨R₁, hR₁⟩ := isBounded_iff_forall_norm_le.1 (isBounded_range_of_tendsto xs hxs)
    obtain ⟨R₂, hR₂⟩ := isBounded_iff_forall_norm_le.1 (isBounded_range_of_tendsto _ hd)
    refine isBounded_iff_forall_norm_le.2 ⟨R₁ + R₂, ?_⟩
    rintro _ ⟨n, rfl⟩
    calc ‖ws n‖ = ‖(ws n - xs n) + xs n‖ := by rw [sub_add_cancel]
      _ ≤ ‖ws n - xs n‖ + ‖xs n‖ := norm_add_le _ _
      _ ≤ R₂ + R₁ := by
          refine add_le_add ?_ (hR₁ _ ⟨n, rfl⟩)
          rw [hnorm]
          exact (le_abs_self _).trans (hR₂ _ ⟨n, rfl⟩)
      _ = R₁ + R₂ := add_comm _ _
  · obtain ⟨φ, hφ, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hw
    have hwC : w ∈ C := hC.mem_of_tendsto hlim (Eventually.of_forall fun k ↦ (hws (φ k)).1)
    have h1 : Tendsto (fun k ↦ ‖ws (φ k) - xs (φ k)‖) atTop (𝓝 ‖w - x‖) :=
      (hlim.sub (hxs.comp hφ.tendsto_atTop)).norm
    have h2 : Tendsto (fun k ↦ ‖ws (φ k) - xs (φ k)‖) atTop (𝓝 (infDist x C)) := by
      simp_rw [hnorm]
      exact hd.comp hφ.tendsto_atTop
    exact (mem_projMapping_iff_norm_eq_infDist hne).2 ⟨hwC, tendsto_nhds_unique h1 h2⟩

end Distance

/-! ## Example 1.21 -/

section Penalty

variable {G : Type*} [NormedAddCommGroup G]

/-- The hypotheses on the penalty function `θ` in Example 1.21: `θ : ℝᵐ × (0,∞) → ℝ̄` is lsc and
`-∞ < θ(u,r) ↗ δ_D(u)` as `r → ∞`. -/
structure IsPenaltyScheme (θ : G × ℝ → EReal) (D : Set G) : Prop where
  lsc : LowerSemicontinuousOn θ (univ ×ˢ Ioi 0)
  bot_lt : ∀ u, ∀ r > (0 : ℝ), ⊥ < θ (u, r)
  mono : ∀ u, MonotoneOn (fun r ↦ θ (u, r)) (Ioi 0)
  tendsto : ∀ u, Tendsto (fun r ↦ θ (u, r)) atTop (𝓝 (indicatorVA D u))

namespace IsPenaltyScheme

variable {θ : G × ℝ → EReal} {D : Set G}

theorem le_indicator (h : IsPenaltyScheme θ D) (u : G) {r : ℝ} (hr : 0 < r) :
    θ (u, r) ≤ indicatorVA D u :=
  ge_of_tendsto (h.tendsto u) ((eventually_ge_atTop r).mono fun _ hs ↦
    h.mono u hr (lt_of_lt_of_le hr hs) hs)

theorem le_of_le (h : IsPenaltyScheme θ D) (u : G) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    θ (u, r) ≤ θ (u, s) :=
  h.mono u hr (lt_of_lt_of_le hr hrs) hrs

/-- The epi-convergence step behind Example 1.21: along `xν → x̄` and `rν → ∞`,
`f(x̄) + δ_D(F(x̄)) ≤ liminf [f(xν) + θ(F(xν), rν)]`. -/
theorem le_liminf {E : Type*} [TopologicalSpace E] (h : IsPenaltyScheme θ D) {f : E → EReal}
    (hf : LowerSemicontinuous f) {F : E → G} (hF : Continuous F) {xs : ℕ → E} {x : E}
    (hxs : Tendsto xs atTop (𝓝 x)) {rs : ℕ → ℝ} (hrs : Tendsto rs atTop atTop) :
    f x + indicatorVA D (F x) ≤
      liminf (fun n ↦ f (xs n) + θ (F (xs n), rs n)) atTop := by
  have h1 : f x ≤ liminf (fun n ↦ f (xs n)) atTop :=
    (lowerSemicontinuousAt_iff_le_liminf.1 (hf x)).trans (liminf_le_liminf_of_le hxs)
  have h2 : indicatorVA D (F x) ≤ liminf (fun n ↦ θ (F (xs n), rs n)) atTop := by
    refine le_of_tendsto (h.tendsto (F x)) ((eventually_gt_atTop 0).mono fun r hr ↦ ?_)
    refine ereal_le_of_forall_coe_lt fun c hc ↦ ?_
    have hlsc := h.lsc (F x, r) ⟨mem_univ _, hr⟩ c hc
    have hto : Tendsto (fun n ↦ (F (xs n), r)) atTop (𝓝[univ ×ˢ Ioi 0] (F x, r)) :=
      tendsto_nhdsWithin_iff.2 ⟨((hF.tendsto x).comp hxs).prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall fun _ ↦ ⟨mem_univ _, hr⟩⟩
    have hev : ∀ᶠ n in atTop, (c : EReal) ≤ θ (F (xs n), rs n) := by
      filter_upwards [hto.eventually hlsc, hrs.eventually_ge_atTop r] with n hn hn'
      exact (lt_of_lt_of_le hn (h.le_of_le _ hr hn')).le
    exact le_liminf_of_le (by isBoundedDefault) hev
  calc f x + indicatorVA D (F x)
      ≤ liminf (fun n ↦ f (xs n)) atTop + liminf (fun n ↦ θ (F (xs n), rs n)) atTop :=
        add_le_add h1 h2
    _ ≤ liminf (fun n ↦ f (xs n) + θ (F (xs n), rs n)) atTop := EReal.le_liminf_add

end IsPenaltyScheme

variable [FiniteDimensional ℝ E] {θ : G × ℝ → EReal} {D : Set G}

/-- **Example 1.21(a)** (convergence of penalty methods): if the level sets of
`x ↦ f(x) + θ(F(x), r̄)` are bounded, then along `rν ≥ r̄` with `rν → ∞` the optimal values
`inf_x f(x) + θ(F(x), rν)` converge to the optimal value `inf_x f(x) + δ_D(F(x))` of the true
problem.  (Properness of `f` and closedness of `D` are not needed: `δ_D` is the supremum of the
lsc functions `θ(·, r)`.) -/
theorem penalty_method_values (hθ : IsPenaltyScheme θ D) {f : E → EReal}
    (hf : LowerSemicontinuous f) {F : E → G} (hF : Continuous F) {rbar : ℝ} (hrbar : 0 < rbar)
    (hlb : IsLevelBounded (fun x ↦ f x + θ (F x, rbar))) {rs : ℕ → ℝ}
    (hrs₁ : ∀ n, rbar ≤ rs n) (hrs : Tendsto rs atTop atTop) :
    Tendsto (fun n ↦ ⨅ x, f x + θ (F x, rs n)) atTop
      (𝓝 (⨅ x, f x + indicatorVA D (F x))) := by
  have hle : ∀ n, (⨅ x, f x + θ (F x, rs n)) ≤ ⨅ x, f x + indicatorVA D (F x) := fun n ↦
    iInf_mono fun x ↦ add_le_add le_rfl (hθ.le_indicator _ (lt_of_lt_of_le hrbar (hrs₁ n)))
  have hliminf : (⨅ x, f x + indicatorVA D (F x)) ≤
      liminf (fun n ↦ ⨅ x, f x + θ (F x, rs n)) atTop := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨β, hβ1, hβ2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    have hfreq : ∃ᶠ n in atTop, (⨅ x, f x + θ (F x, rs n)) < β :=
      frequently_lt_of_liminf_lt (by isBoundedDefault) hβ1
    obtain ⟨ψ, hψ, hψβ⟩ := extraction_of_frequently_atTop hfreq
    have hx : ∀ k, ∃ x, f x + θ (F x, rs (ψ k)) < β := fun k ↦ iInf_lt_iff.1 (hψβ k)
    choose xk hxk using hx
    have hmem : ∀ k, xk k ∈ levelSet (fun x ↦ f x + θ (F x, rbar)) β := fun k ↦
      (add_le_add le_rfl (hθ.le_of_le _ hrbar (hrs₁ _))).trans (hxk k).le
    obtain ⟨x, -, χ, hχ, hlim⟩ := tendsto_subseq_of_bounded (hlb β) hmem
    have hrs' : Tendsto (fun j ↦ rs (ψ (χ j))) atTop atTop :=
      hrs.comp (hψ.comp hχ).tendsto_atTop
    have hkey := hθ.le_liminf hf hF hlim hrs'
    have hub : liminf (fun j ↦ f ((xk ∘ χ) j) + θ (F ((xk ∘ χ) j), rs (ψ (χ j)))) atTop ≤ β :=
      liminf_le_of_frequently_le' (Frequently.of_forall fun j ↦ (hxk (χ j)).le)
    exact absurd (((iInf_le _ x).trans (hkey.trans hub)).trans_lt hβ2) (lt_irrefl _)
  exact tendsto_of_le_liminf_of_limsup_le hliminf
    (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hle))

/-- **Example 1.21(b)**, corrected: when the true problem is feasible, every sequence of optimal
solutions `xν` of the approximate problems is bounded and its cluster points are optimal for the
true problem.  Feasibility cannot be dropped: see `penalty_method_unbounded_counterexample`. -/
theorem penalty_method_solutions (hθ : IsPenaltyScheme θ D) {f : E → EReal}
    (hf : LowerSemicontinuous f) {F : E → G} (hF : Continuous F) {rbar : ℝ} (hrbar : 0 < rbar)
    (hlb : IsLevelBounded (fun x ↦ f x + θ (F x, rbar))) {rs : ℕ → ℝ}
    (hrs₁ : ∀ n, rbar ≤ rs n) (hrs : Tendsto rs atTop atTop)
    (hfeas : ∃ x, f x < ⊤ ∧ F x ∈ D) {xs : ℕ → E}
    (hxs : ∀ n, xs n ∈ argmin (fun x ↦ f x + θ (F x, rs n))) :
    IsBounded (range xs) ∧
      ∀ c, MapClusterPt c atTop xs → c ∈ argmin (fun x ↦ f x + indicatorVA D (F x)) := by
  have hconv := penalty_method_values hθ hf hF hrbar hlb hrs₁ hrs
  have hle : ∀ n, (⨅ x, f x + θ (F x, rs n)) ≤ ⨅ x, f x + indicatorVA D (F x) := fun n ↦
    iInf_mono fun x ↦ add_le_add le_rfl (hθ.le_indicator _ (lt_of_lt_of_le hrbar (hrs₁ n)))
  obtain ⟨x₀, hx₀, hx₀D⟩ := hfeas
  have hfin : (⨅ x, f x + indicatorVA D (F x)) < ⊤ :=
    (iInf_le _ x₀).trans_lt (by rw [indicatorVA_apply_mem hx₀D, add_zero]; exact hx₀)
  obtain ⟨α, hα, -⟩ := EReal.exists_between_coe_real hfin
  have hval : ∀ n, f (xs n) + θ (F (xs n), rs n) = ⨅ x, f x + θ (F x, rs n) := fun n ↦
    (hxs n).1
  have hmem : ∀ n, xs n ∈ levelSet (fun x ↦ f x + θ (F x, rbar)) α := fun n ↦
    (add_le_add le_rfl (hθ.le_of_le _ hrbar (hrs₁ n))).trans
      ((hval n).le.trans ((hle n).trans hα.le))
  refine ⟨(hlb α).subset (range_subset_iff.2 hmem), fun c hc ↦ ?_⟩
  obtain ⟨φ, hφ, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hc
  have hkey := hθ.le_liminf hf hF hlim (hrs.comp hφ.tendsto_atTop)
  have hlimP : liminf (fun k ↦ f ((xs ∘ φ) k) + θ (F ((xs ∘ φ) k), rs (φ k))) atTop =
      ⨅ x, f x + indicatorVA D (F x) := by
    have : (fun k ↦ f ((xs ∘ φ) k) + θ (F ((xs ∘ φ) k), rs (φ k))) =
        (fun n ↦ ⨅ x, f x + θ (F x, rs n)) ∘ φ := funext fun k ↦ hval (φ k)
    rw [this]
    exact (hconv.comp hφ.tendsto_atTop).liminf_eq
  exact ⟨le_antisymm (hkey.trans hlimP.le) (iInf_le _ c), hfin⟩

end Penalty

/-! ### The feasibility hypothesis in Example 1.21(b) -/

section PenaltyCounterexample

/-- Quadratic penalties `θ(u, r) = r u²` for the constraint `u = 0`. -/
def quadraticPenalty : ℝ × ℝ → EReal := fun q ↦ ((q.2 * q.1 ^ 2 : ℝ) : EReal)

theorem isPenaltyScheme_quadraticPenalty : IsPenaltyScheme quadraticPenalty ({0} : Set ℝ) where
  lsc := by
    have hc : Continuous fun q : ℝ × ℝ ↦ ((q.2 * q.1 ^ 2 : ℝ) : EReal) :=
      continuous_coe_real_ereal.comp (by fun_prop)
    exact hc.lowerSemicontinuous.lowerSemicontinuousOn _
  bot_lt := fun _ _ _ ↦ EReal.bot_lt_coe _
  mono := fun u _ _ _ _ hrs ↦
    EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_right hrs (sq_nonneg u))
  tendsto := fun u ↦ by
    by_cases hu : u = 0
    · subst hu
      simp only [quadraticPenalty, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, EReal.coe_zero, indicatorVA_apply_mem (mem_singleton (0 : ℝ))]
      exact tendsto_const_nhds
    · rw [indicatorVA_apply_not_mem (by simpa using hu)]
      exact EReal.tendsto_coe_nhds_top_iff.2
        (tendsto_id.atTop_mul_const (by positivity : (0 : ℝ) < u ^ 2))

theorem isLevelBounded_of_le {f g : ℝ → EReal} (h : ∀ x, f x ≤ g x) (hf : IsLevelBounded f) :
    IsLevelBounded g := fun α ↦ (hf α).subset fun x hx ↦ (h x).trans hx

theorem isLevelBounded_sq : IsLevelBounded (fun x : ℝ ↦ ((x ^ 2 : ℝ) : EReal)) := by
  intro α
  refine (isBounded_closedBall (x := (0 : ℝ)) (r := |α| + 1)).subset fun x hx ↦ ?_
  have hx' : x ^ 2 ≤ α := EReal.coe_le_coe_iff.1 hx
  rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_cases h1 : |x| ≤ 1
  · linarith [abs_nonneg α]
  · have : |x| ≤ x ^ 2 := by
      rw [← sq_abs]
      nlinarith [not_le.1 h1]
    linarith [le_abs_self α]

/-- **Example 1.21(b)** fails without feasibility of the true problem: with `f(x) = x²`,
`F(x) = 1/(1+x²)`, `D = {0}`, `θ(u,r) = ru²`, `r̄ = 1` and `rν = (ν+1)³`, all hypotheses of 1.21
hold, the true problem is infeasible, and every choice of approximate optimal solutions is
unbounded (`1 + xν² ≥ (ν+1)/√2`). -/
theorem penalty_method_unbounded_counterexample :
    ∃ (f : ℝ → EReal) (F : ℝ → ℝ) (θ : ℝ × ℝ → EReal) (D : Set ℝ) (rbar : ℝ) (rs : ℕ → ℝ)
      (xs : ℕ → ℝ),
      IsProper f ∧ LowerSemicontinuous f ∧ Continuous F ∧ IsClosed D ∧ IsPenaltyScheme θ D ∧
      0 < rbar ∧ IsLevelBounded (fun x ↦ f x + θ (F x, rbar)) ∧ (∀ n, rbar ≤ rs n) ∧
      Tendsto rs atTop atTop ∧ (∀ n, xs n ∈ argmin (fun x ↦ f x + θ (F x, rs n))) ∧
      (¬ ∃ x, f x < ⊤ ∧ F x ∈ D) ∧ ¬ IsBounded (range xs) := by
  set f : ℝ → EReal := fun x ↦ ((x ^ 2 : ℝ) : EReal) with hfdef
  set F : ℝ → ℝ := fun x ↦ 1 / (1 + x ^ 2) with hFdef
  set rs : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) ^ 3 with hrsdef
  have hF : Continuous F := by
    refine continuous_const.div (by fun_prop) fun x ↦ ?_
    positivity
  have hg : ∀ r x, f x + quadraticPenalty (F x, r) =
      ((x ^ 2 + r * (1 / (1 + x ^ 2)) ^ 2 : ℝ) : EReal) :=
    fun r x ↦ by simp [f, F, quadraticPenalty, EReal.coe_add]
  have hfp : IsProper f := ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩
  have hfl : LowerSemicontinuous f :=
    (continuous_coe_real_ereal.comp (continuous_pow 2)).lowerSemicontinuous
  have hlb : ∀ r, 0 ≤ r → IsLevelBounded (fun x ↦ f x + quadraticPenalty (F x, r)) := by
    intro r hr
    refine isLevelBounded_of_le (fun x ↦ ?_) isLevelBounded_sq
    rw [hg]
    exact EReal.coe_le_coe_iff.2 (le_add_of_nonneg_right (by positivity))
  have hex : ∀ n, (argmin (fun x ↦ f x + quadraticPenalty (F x, rs n))).Nonempty := by
    intro n
    have hcont : Continuous (fun x ↦ f x + quadraticPenalty (F x, rs n)) := by
      simp_rw [hg]
      refine continuous_coe_real_ereal.comp ?_
      refine (continuous_pow 2).add (continuous_const.mul (hF.pow 2))
    refine (attainment_of_minimum hcont.lowerSemicontinuous (hlb _ (by positivity)) ?_).2.1
    refine ⟨⟨0, ?_⟩, fun x ↦ ?_⟩
    · change f 0 + quadraticPenalty (F 0, rs n) < ⊤
      rw [hg]; exact EReal.coe_lt_top _
    · change ⊥ < f x + quadraticPenalty (F x, rs n)
      rw [hg]; exact EReal.bot_lt_coe _
  choose xs hxs using hex
  refine ⟨f, F, quadraticPenalty, {0}, 1, rs, xs, hfp, hfl, hF, isClosed_singleton,
    isPenaltyScheme_quadraticPenalty, one_pos, hlb 1 zero_le_one, fun n ↦ ?_, ?_, hxs, ?_, ?_⟩
  · have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    exact one_le_pow₀ this
  · refine (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp ?_
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  · rintro ⟨x, -, hx⟩
    have : F x = 0 := hx
    have hpos : 0 < F x := by simp only [F]; positivity
    linarith
  · intro hb
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hb
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * (1 + R ^ 2))
    set k : ℝ := (n : ℝ) + 1 with hk
    have hk1 : 1 ≤ k := by linarith [n.cast_nonneg (α := ℝ)]
    have hkR : 2 * (1 + R ^ 2) < k := by linarith
    set x := xs n
    have hxR : x ^ 2 ≤ R ^ 2 := by
      have := hR x ⟨n, rfl⟩
      rw [Real.norm_eq_abs] at this
      nlinarith [abs_nonneg x, sq_abs x]
    have hle : f x + quadraticPenalty (F x, rs n) ≤
        f (Real.sqrt (k - 1)) + quadraticPenalty (F (Real.sqrt (k - 1)), rs n) := by
      have h := iInf_le (fun y ↦ f y + quadraticPenalty (F y, rs n)) (Real.sqrt (k - 1))
      rw [← (hxs n).1] at h
      exact h
    rw [hg, hg, EReal.coe_le_coe_iff] at hle
    have hsq : Real.sqrt (k - 1) ^ 2 = k - 1 := Real.sq_sqrt (by linarith)
    rw [hsq] at hle
    have hrs : rs n = k ^ 3 := rfl
    rw [hrs] at hle
    have hkpos : 0 < k := by linarith
    have hval : k - 1 + k ^ 3 * (1 / (1 + (k - 1))) ^ 2 = 2 * k - 1 := by
      rw [show 1 + (k - 1) = k by ring]
      field_simp
      ring
    rw [hval] at hle
    set t := 1 + x ^ 2 with ht
    have htpos : 0 < t := by positivity
    have heq : k ^ 3 * (1 / t) ^ 2 = k ^ 3 / t ^ 2 := by field_simp
    rw [heq] at hle
    have h1 : k ^ 3 / t ^ 2 ≤ 2 * k := by nlinarith [sq_nonneg x]
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : k ^ 2 ≤ 2 * t ^ 2 := by nlinarith
    have h3 : t ≤ 1 + R ^ 2 := by linarith
    have h4 : t ^ 2 ≤ (1 + R ^ 2) ^ 2 := by nlinarith
    nlinarith

end PenaltyCounterexample

end RW
