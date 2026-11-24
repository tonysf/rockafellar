/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Graphical subgradient mappings of convex integrands (remark after Theorem 14.56)

After Theorem 14.56, Rockafellar–Wets remark that the graphical mappings `t ↦ gph ∂f(t, ·)` and
`t ↦ gph ∂^∞f(t, ·)` need not be closed-valued in general, but are closed-valued as well as
measurable when `f` is a convex normal integrand.  For `∂f` this holds on every σ-field
(`svMeasurable_svGraph_subdifferential_of_convex`, from the closedness of `gph ∂f` for proper lsc
convex functions, `isClosed_graph_subdifferential_of_convex`).  For `∂^∞f` closed values fail: `0`
is a horizon subgradient at every point of `dom f(t, ·)` and there are none outside it, so a closed
`gph ∂^∞f(t, ·)` forces a closed domain
(`isClosed_effectiveDomain_of_isClosed_svGraph_horizonSubdifferential`).  The convex proper normal
integrand `f(t, x) = 1/x` for `x > 0`, `∞` otherwise, on any σ-field, has the measurable but
non-closed `gph ∂^∞f(t, ·) = (0, ∞) × {0}` (`horizon_graph_not_closed_counterexample`).

Measurability of `t ↦ gph ∂^∞f(t, ·)` for convex `f` holds on every σ-field, with no measure and
no properness (`svMeasurable_svGraph_horizonSubdifferential_of_convex`).  If `(xⱼ(t), αⱼ(t))` is a
Castaing representation of `t ↦ epi f(t, ·)` (14.5), the points `xⱼ(t)` are dense in
`dom f(t, ·)`, so by 8.12 `gph ∂^∞f(t, ·)` is the union over `m ∈ ℕ` of the closed sets
`{(x, v) ∣ f(t, x) ≤ m, ⟪v, xⱼ(t) - x⟫ ≤ 0 for all j}` (`svGraph_horizonSubdifferential_eq_iUnion`),
countable intersections of closed-valued measurable mappings (14.33, 14.15(b), 14.11(a)).  Where
`f(t, ·)` takes the value `-∞` it has no finite value (`eq_bot_of_isClosed_epigraph_of_convex`) and
both graphs are empty.  The corrected remark is `subgradient_graph_mappings_of_convex`: for every
convex normal integrand `t ↦ gph ∂f(t, ·)` is closed-valued and measurable and `t ↦ gph ∂^∞f(t, ·)`
is measurable.  An earlier proof on standard Borel spaces
(`svMeasurable_svGraph_horizonSubdifferential_of_convex_of_standardBorel`) uses the closed slices
`{(x, v) ∣ v ∈ ∂^∞f(t, x), f(t, x) ≤ m}` (`isClosed_horizonSubdifferential_le`) and Novikov's
theorem.  Without convexity the mapping is measurable when the σ-field is complete for an s-finite
measure (`svMeasurable_svGraph_subdifferential_of_isComplete`), but not in general, even on the
Baire space (`RW.HorizonGraph.horizon_graph_counterexample`).
-/

import RockafellarWets.Chapter14.SubgradientMeasurability
import RockafellarWets.Chapter8.ClarkeSubgradientRepresentations
import RockafellarWets.Chapter8.ConvexSubgradients
import RockafellarWets.Chapter11.ConjugateSubgradientGraph
import RockafellarWets.Chapter14.NovikovProjection

open Set Filter Topology MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RW

section Domain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For a proper lsc `f`, `dom f` is the slice of `gph ∂^∞f` at `v = 0`: `0 ∈ ∂^∞f(x)` at every
`x ∈ dom f` (`zero_mem_horizonSubdifferential_of_locallyLsc`), and `∂^∞f(x) = ∅` where
`f(x) = ∞`. -/
theorem effectiveDomain_eq_preimage_svGraph_horizonSubdifferential {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) :
    effectiveDomain f = (fun x ↦ (x, (0 : E))) ⁻¹' svGraph (horizonSubdifferential f) := by
  ext x
  simp only [mem_preimage, mem_svGraph]
  constructor
  · intro hx
    have hfin : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hx.ne (hp.2 x).ne').symm
    exact zero_mem_horizonSubdifferential_of_locallyLsc hfin
      (isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ (hl.lowerSemicontinuousOn _)
        (mem_univ x) (hp.2 x).ne' hx.ne)
  · rintro ⟨⟨c, hc⟩, -⟩
    change f x < ⊤
    rw [hc]
    exact EReal.coe_lt_top c

/-- If `gph ∂^∞f` is closed for a proper lsc `f`, then `dom f` is closed. -/
theorem isClosed_effectiveDomain_of_isClosed_svGraph_horizonSubdifferential {f : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f)
    (h : IsClosed (svGraph (horizonSubdifferential f))) : IsClosed (effectiveDomain f) := by
  rw [effectiveDomain_eq_preimage_svGraph_horizonSubdifferential hp hl]
  exact h.preimage (continuous_id.prodMk continuous_const)

/-- The slices of `gph ∂^∞f` for a proper lsc `f` with convex epigraph: `v ∈ ∂^∞f(x)` with
`f(x) ≤ m` means `f(x) ≤ m` and `⟪v, y - x⟫ ≤ 0` for every `y ∈ dom f`, since
`∂^∞f(x) = N_{dom f}(x)` there (8.12, 6.9). -/
theorem setOf_horizonSubdifferential_le_eq {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (m : ℝ) :
    {q : E × E | q.2 ∈ horizonSubdifferential f q.1 ∧ f q.1 ≤ m} =
      {q : E × E | f q.1 ≤ m} ∩
        ⋂ y ∈ effectiveDomain f, {q : E × E | ⟪q.2, y - q.1⟫_ℝ ≤ 0} := by
  have hdom : Convex ℝ (effectiveDomain f) := convex_effectiveDomain_of_convex_epigraph hc
  have key : ∀ x, f x ≤ m → horizonSubdifferential f x =
      {v : E | ∀ y ∈ effectiveDomain f, ⟪v, y - x⟫_ℝ ≤ 0} := by
    intro x hx
    have hxt : f x < ⊤ := lt_of_le_of_lt hx (EReal.coe_lt_top m)
    have hfin : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hxt.ne (hp.2 x).ne').symm
    have hloc : IsLocallyLscAt f x :=
      isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ (hl.lowerSemicontinuousOn _)
        (mem_univ x) (hp.2 x).ne' hxt.ne
    rw [horizonSubdifferential_eq_normalCone_domain_of_locallyLsc hc hp hloc hfin,
      normalCone_eq_of_convex hdom hxt]
  ext ⟨x, v⟩
  simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hv, hm⟩
    rw [key x hm] at hv
    exact ⟨hm, hv⟩
  · rintro ⟨hm, hv⟩
    refine ⟨?_, hm⟩
    rw [key x hm]
    exact hv

/-- For a proper lsc `f` with convex epigraph, the pairs `(x, v)` with `v ∈ ∂^∞f(x)` and
`f(x) ≤ m` form a closed set: `∂^∞f(x) = N_{dom f}(x)` there (8.12), the inequalities
`⟪v, y - x⟫ ≤ 0` for `y ∈ dom f` are closed conditions, and so is `f(x) ≤ m`. -/
theorem isClosed_horizonSubdifferential_le {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (m : ℝ) :
    IsClosed {q : E × E | q.2 ∈ horizonSubdifferential f q.1 ∧ f q.1 ≤ m} := by
  rw [setOf_horizonSubdifferential_le_eq hp hl hc m]
  refine ((hl.isClosed_preimage (m : EReal)).preimage continuous_fst).inter
    (isClosed_biInter fun y _ ↦ isClosed_le ?_ continuous_const)
  exact continuous_snd.inner (continuous_const.sub continuous_fst)

omit [FiniteDimensional ℝ E] in
/-- A function with closed convex epigraph that takes the value `-∞` has no finite value
(Exercise 2.5 with lower semicontinuity): if `f(x₀) = -∞` and `f(x) < ∞`, the points
`((1 - λ)x + λx₀, α)` lie in `epi f` for every real `α` and `λ ∈ (0, 1)`, and letting `λ ↓ 0`
gives `(x, α) ∈ epi f`. -/
theorem eq_bot_of_isClosed_epigraph_of_convex {f : E → EReal} (hcl : IsClosed (epigraph f))
    (hc : Convex ℝ (epigraph f)) {x₀ : E} (hx₀ : f x₀ = ⊥) {x : E} (hx : f x < ⊤) :
    f x = ⊥ := by
  rcases eq_bot_or_bot_lt (f x) with h | hbot
  · exact h
  set c : ℝ := (f x).toReal with hcdef
  have hfc : f x = (c : EReal) := (EReal.coe_toReal hx.ne hbot.ne').symm
  refine ereal_eq_bot_of_forall_le_neg_nat fun n ↦ ?_
  set α : ℝ := -(n : ℝ)
  have hmem : ∀ lam : ℝ, 0 < lam → lam < 1 →
      ((1 - lam) • x + lam • x₀, α) ∈ epigraph f := by
    intro lam h0 h1
    have hxe : ((x, c) : E × ℝ) ∈ epigraph f := by
      change ((c : ℝ) : EReal) ≥ f x
      rw [hfc]
    have hx₀e : ((x₀, (α - (1 - lam) * c) / lam) : E × ℝ) ∈ epigraph f := by
      change (((α - (1 - lam) * c) / lam : ℝ) : EReal) ≥ f x₀
      rw [hx₀]
      exact bot_le
    have := hc hxe hx₀e (by linarith : (0 : ℝ) ≤ 1 - lam) h0.le (by ring)
    convert this using 1
    ext
    · simp
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
      field_simp
      ring
  have hlim : Tendsto (fun lam : ℝ ↦ (((1 - lam) • x + lam • x₀, α) : E × ℝ))
      (𝓝[>] 0) (𝓝 (x, α)) := by
    have hc0 : Continuous fun lam : ℝ ↦ (((1 - lam) • x + lam • x₀, α) : E × ℝ) := by
      fun_prop
    have h := hc0.tendsto 0
    simp only [sub_zero, one_smul, zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ lam in 𝓝[>] (0 : ℝ), (((1 - lam) • x + lam • x₀, α) : E × ℝ) ∈ epigraph f := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with lam hlam
    exact hmem lam hlam.1 hlam.2
  exact hcl.mem_of_tendsto hlim hev

omit [FiniteDimensional ℝ E] in
/-- Under the hypotheses of `eq_bot_of_isClosed_epigraph_of_convex`, `gph ∂^∞f = ∅`: horizon
subgradients need a finite value. -/
theorem svGraph_horizonSubdifferential_eq_empty_of_bot {f : E → EReal}
    (hcl : IsClosed (epigraph f)) (hc : Convex ℝ (epigraph f)) {x₀ : E} (hx₀ : f x₀ = ⊥) :
    svGraph (horizonSubdifferential f) = ∅ := by
  ext ⟨x, v⟩
  simp only [mem_svGraph, mem_empty_iff_false, iff_false]
  intro hv
  obtain ⟨c, hc'⟩ := hv.1
  have := eq_bot_of_isClosed_epigraph_of_convex hcl hc hx₀ (by rw [hc']; exact EReal.coe_lt_top c)
  rw [hc'] at this
  exact EReal.coe_ne_bot c this

omit [FiniteDimensional ℝ E] in
/-- Under the hypotheses of `eq_bot_of_isClosed_epigraph_of_convex`, `gph ∂f = ∅`: subgradients
need a finite value. -/
theorem svGraph_subdifferential_eq_empty_of_bot {f : E → EReal}
    (hcl : IsClosed (epigraph f)) (hc : Convex ℝ (epigraph f)) {x₀ : E} (hx₀ : f x₀ = ⊥) :
    svGraph (subdifferential f) = ∅ := by
  ext ⟨x, v⟩
  simp only [mem_svGraph, mem_empty_iff_false, iff_false]
  intro hv
  obtain ⟨c, hc'⟩ := hv.1
  have := eq_bot_of_isClosed_epigraph_of_convex hcl hc hx₀ (by rw [hc']; exact EReal.coe_lt_top c)
  rw [hc'] at this
  exact EReal.coe_ne_bot c this

/-- `gph ∂^∞f` for a proper lsc `f` with convex epigraph, from a sequence `y` dense in `epi f`: the
union over `m ∈ ℕ` of the closed sets of pairs `(x, v)` with `f(x) ≤ m` and `⟪v, (y j).1 - x⟫ ≤ 0`
for every `j`.  The first components of `y` lie in `dom f` and are dense in it, so these
inequalities define `N_{dom f}(x) = ∂^∞f(x)` (`setOf_horizonSubdifferential_le_eq`). -/
theorem svGraph_horizonSubdifferential_eq_iUnion {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {y : ℕ → E × ℝ}
    (hy : epigraph f = closure (range y)) :
    svGraph (horizonSubdifferential f) = ⋃ m : ℕ, ({q : E × E | f q.1 ≤ (m : ℝ)} ∩
      ⋂ j, {q : E × E | ⟪q.2, (y j).1 - q.1⟫_ℝ ≤ 0}) := by
  have hdense : ∀ x v : E, (∀ z ∈ effectiveDomain f, ⟪v, z - x⟫_ℝ ≤ 0) ↔
      ∀ j, ⟪v, (y j).1 - x⟫_ℝ ≤ 0 := by
    intro x v
    constructor
    · intro h j
      have hj : y j ∈ epigraph f := by
        rw [hy]
        exact subset_closure ⟨j, rfl⟩
      refine h _ ?_
      change f (y j).1 < ⊤
      exact lt_of_le_of_lt hj (EReal.coe_lt_top _)
    · intro h z hz
      set C : Set (E × ℝ) := {p | ⟪v, p.1 - x⟫_ℝ ≤ 0}
      have hC : IsClosed C :=
        isClosed_le (continuous_const.inner (continuous_fst.sub continuous_const))
          continuous_const
      have hsub : epigraph f ⊆ C := by
        rw [hy]
        exact closure_minimal (range_subset_iff.2 h) hC
      have hzfin : f z = ((f z).toReal : EReal) := (EReal.coe_toReal hz.ne (hp.2 z).ne').symm
      have hze : ((z, (f z).toReal) : E × ℝ) ∈ epigraph f := by
        change (((f z).toReal : ℝ) : EReal) ≥ f z
        rw [← hzfin]
      exact hsub hze
  ext ⟨x, v⟩
  simp only [mem_svGraph, mem_iUnion, mem_inter_iff, mem_setOf_eq, mem_iInter]
  constructor
  · intro hv
    obtain ⟨c, hc'⟩ := hv.1
    obtain ⟨m, hm⟩ := exists_nat_ge c
    have hle : f x ≤ ((m : ℝ) : EReal) := by
      rw [hc']
      exact EReal.coe_le_coe_iff.2 hm
    have hmem : (x, v) ∈ {q : E × E | q.2 ∈ horizonSubdifferential f q.1 ∧ f q.1 ≤ (m : ℝ)} :=
      ⟨hv, hle⟩
    rw [setOf_horizonSubdifferential_le_eq hp hl hc] at hmem
    simp only [mem_inter_iff, mem_setOf_eq, mem_iInter] at hmem
    exact ⟨m, hle, (hdense x v).1 hmem.2⟩
  · rintro ⟨m, hle, hv⟩
    have hmem : (x, v) ∈ {q : E × E | f q.1 ≤ (m : ℝ)} ∩
        ⋂ z ∈ effectiveDomain f, {q : E × E | ⟪q.2, z - q.1⟫_ℝ ≤ 0} := by
      simp only [mem_inter_iff, mem_setOf_eq, mem_iInter]
      exact ⟨hle, (hdense x v).2 hv⟩
    rw [← setOf_horizonSubdifferential_le_eq hp hl hc] at hmem
    exact hmem.1

variable {T : Type*} [MeasurableSpace T] [MeasurableSpace E] [BorelSpace E]

/-- Remark after **Theorem 14.56**, for `∂f`: for a convex proper normal integrand,
`t ↦ gph ∂f(t, ·)` is closed-valued and measurable, on every σ-field
(`subgradient_graph_mappings_of_convex` drops properness and adds `t ↦ gph ∂^∞f(t, ·)`). -/
theorem svMeasurable_svGraph_subdifferential_of_convex {f : T → E → EReal}
    (hf : IsNormalIntegrand f) (hp : ∀ t, IsProper (f t))
    (hc : ∀ t, Convex ℝ (epigraph (f t))) :
    (∀ t, IsClosed (svGraph (subdifferential (f t)))) ∧
      SvMeasurable (fun t ↦ svGraph (subdifferential (f t))) :=
  ⟨fun t ↦ isClosed_graph_subdifferential_of_convex (hp t) (hf.lowerSemicontinuous t) (hc t),
    svMeasurable_svGraph_subdifferential hf⟩

/-- Remark after **Theorem 14.56**, measurability of `t ↦ gph ∂^∞f(t, ·)` for a convex proper
normal integrand on a standard Borel space, with no measure (the conclusion holds on every σ-field:
`svMeasurable_svGraph_horizonSubdifferential_of_convex`).  The inverse image of a compact `K` is
the union over `m ∈ ℕ` of the projections of the Borel sets
`{(t, x, v) ∣ v ∈ ∂^∞f(t, x), f(t, x) ≤ m, (x, v) ∈ K}`, whose sections are closed subsets of `K`
(`isClosed_horizonSubdifferential_le`), hence Borel by Novikov's theorem.  Without convexity this
fails even on the Baire space (`RW.HorizonGraph.horizon_graph_counterexample`), and closed values
fail even with convexity (`horizon_graph_not_closed_counterexample`). -/
theorem svMeasurable_svGraph_horizonSubdifferential_of_convex_of_standardBorel
    [StandardBorelSpace T] {f : T → E → EReal} (hf : IsNormalIntegrand f)
    (hp : ∀ t, IsProper (f t)) (hc : ∀ t, Convex ℝ (epigraph (f t))) :
    SvMeasurable (fun t ↦ svGraph (horizonSubdifferential (f t))) := by
  refine svMeasurable_of_measurableSet_svPreimage_isCompact fun K hK ↦ ?_
  set G : ℕ → Set (T × (E × E)) := fun m ↦
    {p | p.2.2 ∈ horizonSubdifferential (f p.1) p.2.1 ∧ f p.1 p.2.1 ≤ (m : ℝ)} with hG
  have heq : svPreimage (fun t ↦ svGraph (horizonSubdifferential (f t))) K =
      ⋃ m : ℕ, Prod.fst '' (G m ∩ univ ×ˢ K) := by
    ext t
    simp only [mem_svPreimage, mem_iUnion, mem_image, mem_inter_iff, mem_prod, mem_univ,
      true_and, Prod.exists, exists_and_right, exists_eq_right, hG, mem_setOf_eq]
    constructor
    · rintro ⟨⟨x, v⟩, hv, hK'⟩
      obtain ⟨c, hc'⟩ := (show v ∈ horizonSubdifferential (f t) x from hv).1
      obtain ⟨m, hm⟩ := exists_nat_ge c
      refine ⟨m, x, v, ⟨hv, ?_⟩, hK'⟩
      rw [hc']
      exact EReal.coe_le_coe_iff.2 hm
    · rintro ⟨m, x, v, ⟨hv, -⟩, hK'⟩
      exact ⟨(x, v), hv, hK'⟩
  rw [heq]
  refine MeasurableSet.iUnion fun m ↦ measurableSet_image_fst_of_isClosed_sections_of_isCompact
    hK ?_ inter_subset_right fun t ↦ ?_
  · refine MeasurableSet.inter ?_ (MeasurableSet.univ.prod hK.measurableSet)
    have hgr := measurableSet_svGraph_svGraph_horizonSubdifferential hf
    have hfm : Measurable fun p : T × (E × E) ↦ f p.1 p.2.1 :=
      hf.measurable_uncurry.comp (measurable_fst.prodMk measurable_snd.fst)
    exact hgr.inter (hfm measurableSet_Iic)
  · rw [preimage_inter, mk_preimage_prod_right (mem_univ t)]
    exact (isClosed_horizonSubdifferential_le (hp t) (hf.lowerSemicontinuous t) (hc t)
      (m : ℝ)).inter hK.isClosed

/-- Remark after **Theorem 14.56**, measurability on every σ-field: for a normal integrand `f`
with `f(t, ·)` convex, the mapping `t ↦ gph ∂^∞f(t, ·)` is measurable, with no measure, standard
Borel structure or properness.  With `(xⱼ, αⱼ)` a Castaing representation of `t ↦ epi f(t, ·)`
(14.5), `gph ∂^∞f(t, ·)` is the union over `m ∈ ℕ` of the closed sets
`{(x, v) ∣ f(t, x) ≤ m, ⟪v, xⱼ(t) - x⟫ ≤ 0 for all j}` (`svGraph_horizonSubdifferential_eq_iUnion`),
countable intersections of closed-valued measurable mappings (14.33, 14.15(b), 14.11(a)).  Where
`f(t, ·)` takes the value `-∞` it has no finite value and the graph is empty
(`svGraph_horizonSubdifferential_eq_empty_of_bot`); this set of `t` is the domain of
`t ↦ ⋂ₖ {f(t, ·) ≤ -k}`, hence measurable. -/
theorem svMeasurable_svGraph_horizonSubdifferential_of_convex {f : T → E → EReal}
    (hf : IsNormalIntegrand f) (hc : ∀ t, Convex ℝ (epigraph (f t))) :
    SvMeasurable (fun t ↦ svGraph (horizonSubdifferential (f t))) := by
  classical
  obtain ⟨xs, hxs⟩ := hf.2.exists_castaingRepresentation hf.1
  set P : Set T := {t | ∀ x, f t x ≠ ⊥} with hPdef
  have hlev : ∀ k : ℕ, (∀ t, IsClosed {x | f t x ≤ (((fun _ : T ↦ -(k : ℝ)) t : ℝ) : EReal)}) ∧
      SvMeasurable (fun t ↦ {x | f t x ≤ (((fun _ : T ↦ -(k : ℝ)) t : ℝ) : EReal)}) :=
    fun k ↦ hf.levelSet_measurable measurable_const
  have hPm : MeasurableSet P := by
    have hI := SvMeasurable.iInter (fun k ↦ (hlev k).2) (fun k ↦ (hlev k).1)
    have heqP : P = (svDom fun t ↦ ⋂ k : ℕ,
        {x | f t x ≤ (((fun _ : T ↦ -(k : ℝ)) t : ℝ) : EReal)})ᶜ := by
      ext t
      rw [mem_compl_iff]
      constructor
      · rintro h ⟨x, hx⟩
        rw [mem_iInter] at hx
        exact h x (ereal_eq_bot_of_forall_le_neg_nat hx)
      · intro h x hx
        refine h ⟨x, mem_iInter.2 fun k ↦ ?_⟩
        change f t x ≤ _
        rw [hx]
        exact bot_le
    rw [heqP]
    exact hI.measurableSet_svDom.compl
  set L : ℕ → T → Set (E × E) := fun m t ↦ {q | f t q.1 ≤ (m : ℝ)} with hLdef
  set H : ℕ → T → Set (E × E) := fun j t ↦ {q | ⟪q.2, (xs j t).1 - q.1⟫_ℝ ≤ 0} with hHdef
  have hLc : ∀ m t, IsClosed (L m t) := fun m t ↦
    ((hf.lowerSemicontinuous t).isClosed_preimage _).preimage continuous_fst
  have hLm : ∀ m, SvMeasurable (L m) := by
    intro m
    have h := (hf.levelSet_measurable (α := fun _ ↦ (m : ℝ)) measurable_const).2.prod
      (svMeasurable_const (univ : Set E))
    have heq : (fun t ↦ {x | f t x ≤ (((fun _ : T ↦ (m : ℝ)) t : ℝ) : EReal)} ×ˢ
        (univ : Set E)) = L m := by
      funext t
      ext ⟨x, v⟩
      simp [hLdef]
    rwa [heq] at h
  have hH : ∀ j, (∀ t, IsClosed (H j t)) ∧ SvMeasurable (H j) := by
    intro j
    set Φ : T → E × E → ℝ := fun t q ↦ ⟪q.2, (xs j t).1 - q.1⟫_ℝ with hΦdef
    have hΦ : IsCaratheodory Φ := by
      refine ⟨fun q ↦ ?_, fun t ↦ ?_⟩
      · have hcont : Continuous fun p : E × ℝ ↦ ⟪q.2, p.1 - q.1⟫_ℝ :=
          continuous_const.inner (continuous_fst.sub continuous_const)
        exact hcont.measurable.comp (hxs.1 j)
      · exact continuous_snd.inner (continuous_const.sub continuous_fst)
    exact hΦ.svMeasurable_preimage (S := fun _ ↦ Iic (0 : ℝ)) (svMeasurable_const _)
      (fun _ ↦ isClosed_Iic)
  set G : ℕ → T → Set (E × E) := fun m t ↦ L m t ∩ ⋂ j, H j t with hGdef
  have hG : ∀ m, SvMeasurable (G m) := fun m ↦
    (hLm m).inter (SvMeasurable.iInter (fun j ↦ (hH j).2) fun j ↦ (hH j).1) (hLc m)
      fun t ↦ isClosed_iInter fun j ↦ (hH j).1 t
  have heq : (fun t ↦ svGraph (horizonSubdifferential (f t))) =
      fun t ↦ if t ∈ P then ⋃ m, G m t else ∅ := by
    funext t
    by_cases hPt : t ∈ P
    · rw [if_pos hPt]
      by_cases hdom : t ∈ svDom (epiMapping f)
      · have hp : IsProper (f t) := by
          obtain ⟨⟨x, β⟩, hxβ⟩ := hdom
          refine ⟨⟨x, lt_of_le_of_lt (show f t x ≤ β from hxβ) (EReal.coe_lt_top β)⟩,
            fun x ↦ ?_⟩
          exact bot_lt_iff_ne_bot.2 (hPt x)
        exact svGraph_horizonSubdifferential_eq_iUnion hp (hf.lowerSemicontinuous t) (hc t)
          (hxs.2 t hdom)
      · have htop : ∀ x, f t x = ⊤ := by
          intro x
          by_contra hx
          refine hdom ⟨(x, (f t x).toReal), ?_⟩
          change (((f t x).toReal : ℝ) : EReal) ≥ f t x
          rw [EReal.coe_toReal hx (hPt x)]
        have hL0 : ∀ m, L m t = ∅ := by
          intro m
          ext q
          simp only [hLdef, mem_setOf_eq, mem_empty_iff_false, iff_false, htop q.1, top_le_iff]
          exact EReal.coe_ne_top _
        have hlhs : svGraph (horizonSubdifferential (f t)) = ∅ := by
          ext ⟨x, v⟩
          simp only [mem_svGraph, mem_empty_iff_false, iff_false]
          intro hv
          obtain ⟨c, hc'⟩ := hv.1
          rw [htop x] at hc'
          exact EReal.coe_ne_top c hc'.symm
        rw [hlhs]
        ext q
        simp only [mem_empty_iff_false, false_iff, mem_iUnion, not_exists, hGdef, hL0,
          empty_inter, not_false_eq_true, implies_true]
    · rw [if_neg hPt]
      simp only [hPdef, mem_setOf_eq, not_forall, not_not] at hPt
      obtain ⟨x₀, hx₀⟩ := hPt
      exact svGraph_horizonSubdifferential_eq_empty_of_bot (hf.1 t) (hc t) hx₀
  rw [heq]
  exact SvMeasurable.ite hPm (SvMeasurable.iUnion hG) (svMeasurable_const ∅)

/-- Remark after **Theorem 14.56**, corrected: for every convex normal integrand `f` (proper or
not) and every σ-field, `t ↦ gph ∂f(t, ·)` is closed-valued and measurable and
`t ↦ gph ∂^∞f(t, ·)` is measurable.  The latter need not be closed-valued
(`horizon_graph_not_closed_counterexample`).  For improper `f(t, ·)` both graphs are empty
(`svGraph_subdifferential_eq_empty_of_bot`), since subgradients need a finite value. -/
theorem subgradient_graph_mappings_of_convex {f : T → E → EReal} (hf : IsNormalIntegrand f)
    (hc : ∀ t, Convex ℝ (epigraph (f t))) :
    (∀ t, IsClosed (svGraph (subdifferential (f t)))) ∧
      SvMeasurable (fun t ↦ svGraph (subdifferential (f t))) ∧
        SvMeasurable (fun t ↦ svGraph (horizonSubdifferential (f t))) := by
  refine ⟨fun t ↦ ?_, svMeasurable_svGraph_subdifferential hf,
    svMeasurable_svGraph_horizonSubdifferential_of_convex hf hc⟩
  by_cases hp : IsProper (f t)
  · exact isClosed_graph_subdifferential_of_convex hp (hf.lowerSemicontinuous t) (hc t)
  by_cases hbot : ∃ x₀, f t x₀ = ⊥
  · obtain ⟨x₀, hx₀⟩ := hbot
    rw [svGraph_subdifferential_eq_empty_of_bot (hf.1 t) (hc t) hx₀]
    exact isClosed_empty
  have htop : ∀ x, f t x = ⊤ := by
    intro x
    by_contra hx
    refine hp ⟨⟨x, lt_top_iff_ne_top.2 hx⟩, fun x' ↦ ?_⟩
    exact bot_lt_iff_ne_bot.2 fun h ↦ hbot ⟨x', h⟩
  have hempty : svGraph (subdifferential (f t)) = ∅ := by
    ext ⟨x, v⟩
    simp only [mem_svGraph, mem_empty_iff_false, iff_false]
    intro hv
    obtain ⟨c, hc'⟩ := hv.1
    rw [htop x] at hc'
    exact EReal.coe_ne_top c hc'.symm
  rw [hempty]
  exact isClosed_empty

end Domain

section Reciprocal

/-- The proper lsc convex function `x ↦ 1/x` on `(0, ∞)`, `∞` elsewhere. -/
def posReciprocalVA (x : ℝ) : EReal := if 0 < x then ((x⁻¹ : ℝ) : EReal) else ⊤

theorem epigraph_posReciprocalVA :
    epigraph posReciprocalVA = {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 1 ≤ p.1 * p.2} := by
  ext ⟨x, α⟩
  simp only [epigraph, posReciprocalVA, mem_setOf_eq, ge_iff_le]
  split_ifs with hx
  · rw [EReal.coe_le_coe_iff, inv_le_iff_one_le_mul₀' hx]
    constructor
    · intro h
      refine ⟨hx.le, ?_, h⟩
      by_contra hα
      push_neg at hα
      nlinarith
    · exact fun h ↦ h.2.2
  · simp only [top_le_iff, EReal.coe_ne_top, false_iff, not_and, not_le]
    intro h0 _
    have : x = 0 := le_antisymm (not_lt.1 hx) h0
    subst this
    simp

theorem isClosed_epigraph_posReciprocalVA : IsClosed (epigraph posReciprocalVA) := by
  rw [epigraph_posReciprocalVA]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_const (continuous_fst.mul continuous_snd)))

theorem lowerSemicontinuous_posReciprocalVA : LowerSemicontinuous posReciprocalVA :=
  lowerSemicontinuous_of_isClosed_epigraph_ereal _ isClosed_epigraph_posReciprocalVA

theorem convex_epigraph_posReciprocalVA : Convex ℝ (epigraph posReciprocalVA) := by
  rw [epigraph_posReciprocalVA]
  rintro ⟨x₁, α₁⟩ ⟨hx₁, hα₁, h₁⟩ ⟨x₂, α₂⟩ ⟨hx₂, hα₂, h₂⟩ a b ha hb hab
  simp only [mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h₁ h₂ ⊢
  have hcross : 2 ≤ x₁ * α₂ + x₂ * α₁ := by
    nlinarith [sq_nonneg (x₁ * α₂ - x₂ * α₁), mul_nonneg hx₁ hα₂, mul_nonneg hx₂ hα₁,
      mul_le_mul h₁ h₂ zero_le_one (by positivity)]
  refine ⟨by positivity, by positivity, ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg ha hb, mul_nonneg (mul_nonneg ha hb) (sub_nonneg.2 hcross),
    mul_nonneg (mul_nonneg ha ha) (sub_nonneg.2 h₁),
    mul_nonneg (mul_nonneg hb hb) (sub_nonneg.2 h₂)]

theorem isProper_posReciprocalVA : IsProper posReciprocalVA := by
  refine ⟨⟨1, by simp only [posReciprocalVA, if_pos one_pos]; exact EReal.coe_lt_top _⟩,
    fun x ↦ ?_⟩
  unfold posReciprocalVA
  split_ifs
  · exact EReal.bot_lt_coe _
  · exact bot_lt_top

theorem effectiveDomain_posReciprocalVA : effectiveDomain posReciprocalVA = Ioi 0 := by
  ext x
  simp only [effectiveDomain, posReciprocalVA, mem_setOf_eq, mem_Ioi]
  split_ifs with hx
  · simp [hx]
  · simp [hx]

theorem not_isClosed_effectiveDomain_posReciprocalVA :
    ¬ IsClosed (effectiveDomain posReciprocalVA) := by
  rw [effectiveDomain_posReciprocalVA]
  intro h
  have : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact self_mem_Ici
  rw [h.closure_eq] at this
  exact lt_irrefl _ (mem_Ioi.1 this)

/-- `gph ∂^∞f = (0, ∞) × {0}` for `f = posReciprocalVA`: on the open domain the horizon
subgradients form the normal cone `{0}` (8.12). -/
theorem svGraph_horizonSubdifferential_posReciprocalVA :
    svGraph (horizonSubdifferential posReciprocalVA) = Ioi 0 ×ˢ {0} := by
  ext ⟨x, v⟩
  simp only [mem_svGraph, mem_prod, mem_Ioi, mem_singleton_iff]
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := hv.1
    have hx : 0 < x := by
      by_contra hx
      simp [posReciprocalVA, hx] at hc
    refine ⟨hx, ?_⟩
    have hl : IsLocallyLscAt posReciprocalVA x :=
      isLocallyLscAt_of_lowerSemicontinuousOn isOpen_univ
        (lowerSemicontinuous_posReciprocalVA.lowerSemicontinuousOn _) (mem_univ x)
        (by rw [hc]; exact EReal.coe_ne_bot c) (by rw [hc]; exact EReal.coe_ne_top c)
    rw [horizonSubdifferential_eq_normalCone_domain_of_locallyLsc
      convex_epigraph_posReciprocalVA isProper_posReciprocalVA hl hc,
      effectiveDomain_posReciprocalVA,
      normalCone_eq_singleton_of_mem_interior (by rwa [interior_Ioi])] at hv
    exact hv
  · rintro ⟨hx, rfl⟩
    have hd : x ∈ effectiveDomain posReciprocalVA := by
      rw [effectiveDomain_posReciprocalVA]
      exact hx
    rw [effectiveDomain_eq_preimage_svGraph_horizonSubdifferential isProper_posReciprocalVA
      lowerSemicontinuous_posReciprocalVA] at hd
    exact hd

/-- The remark after **Theorem 14.56** fails for `∂^∞`: on every σ-field, the autonomous integrand
`f(t, x) = 1/x` for `x > 0`, `∞` otherwise, is a convex proper normal integrand with
`t ↦ gph ∂f(t, ·)` closed-valued and measurable, while `t ↦ gph ∂^∞f(t, ·)` is measurable but
not closed-valued: `gph ∂^∞f(t, ·) = (0, ∞) × {0}`. -/
theorem horizon_graph_not_closed_counterexample {T : Type*} [MeasurableSpace T] :
    ∃ f : T → ℝ → EReal, IsNormalIntegrand f ∧ (∀ t, IsProper (f t)) ∧
      (∀ t, Convex ℝ (epigraph (f t))) ∧
      ((∀ t, IsClosed (svGraph (subdifferential (f t)))) ∧
        SvMeasurable (fun t ↦ svGraph (subdifferential (f t)))) ∧
      SvMeasurable (fun t ↦ svGraph (horizonSubdifferential (f t))) ∧
      ∀ t, svGraph (horizonSubdifferential (f t)) = Ioi 0 ×ˢ {0} ∧
        ¬ IsClosed (svGraph (horizonSubdifferential (f t))) := by
  have hf : IsNormalIntegrand (fun _ : T ↦ posReciprocalVA) :=
    isNormalIntegrand_const lowerSemicontinuous_posReciprocalVA
  refine ⟨fun _ ↦ posReciprocalVA, hf, fun _ ↦ isProper_posReciprocalVA,
    fun _ ↦ convex_epigraph_posReciprocalVA,
    svMeasurable_svGraph_subdifferential_of_convex hf (fun _ ↦ isProper_posReciprocalVA)
      fun _ ↦ convex_epigraph_posReciprocalVA,
    svMeasurable_const _, fun _ ↦ ⟨svGraph_horizonSubdifferential_posReciprocalVA, fun h ↦ ?_⟩⟩
  exact not_isClosed_effectiveDomain_posReciprocalVA
    (isClosed_effectiveDomain_of_isClosed_svGraph_horizonSubdifferential isProper_posReciprocalVA
      lowerSemicontinuous_posReciprocalVA h)

end Reciprocal

end RW
