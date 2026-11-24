/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 14: Subgradient characterization of convex normality

Proposition 14.57 of Rockafellar–Wets: for `f(t, ·)` proper, lsc and convex, `f` is a normal
integrand exactly when `t ↦ gph ∂f(t, ·)` is measurable and some measurable `x̄(t)` has
`∂f(t, x̄(t)) ≠ ∅` and `t ↦ f(t, x̄(t))` measurable.

Necessity: by the Minty parameterization (12.15, 12.19) `gph ∂f(t, ·)` is the image of the graph of
the proximal mapping `P_1 f(t, ·)` under `(z, x) ↦ (x, z - x)`, measurable by 14.38.  Sufficiency, as
in the proof: `f(t, ·) - f(t, x̄(t))` is Rockafellar's chain function of 12.25 built on `∂f(t, ·)` from a
measurable `(x̄(t), v̄(t))`, and by continuity the chains may be restricted to the points of a Castaing
representation of `gph ∂f(t, ·)`; `f` is then a countable supremum of Carathéodory integrands.
-/

import RockafellarWets.Chapter14.MoreauIntegrands
import RockafellarWets.Chapter12.CyclicalMonotonicity
import RockafellarWets.Chapter12.MaximalMonotoneGraphs
import RockafellarWets.Chapter3.ExtendedCancellationCompletion
import RockafellarWets.Chapter3.Coercivity

open Set Filter Topology Metric
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace RW

section Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A proper lsc convex function has an affine minorant, hence infinite prox-threshold. -/
theorem proxThreshold_eq_top_of_convex {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) : proxThreshold f = ⊤ := by
  obtain ⟨x, hx⟩ := hp.1
  have hxbot : f x ≠ ⊥ := (hp.2 x).ne'
  obtain ⟨l, b, -, hlb⟩ := exists_affine_minorant_gt_of_lt_of_convex_lsc_ereal hc hl hp
    (x := x) (r := (f x).toReal - 1) (by
      calc (((f x).toReal - 1 : ℝ) : EReal) < ((f x).toReal : EReal) :=
            EReal.coe_lt_coe_iff.2 (by linarith)
        _ = f x := EReal.coe_toReal hx.ne hxbot)
  refine proxThreshold_eq_top_of_affineNormLowerBound (γ := -‖l‖) (β := b) fun y ↦ ?_
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (hlb y)
  have := l.le_opNorm y
  have h2 := neg_abs_le (l y)
  have h3 : |l y| ≤ ‖l‖ * ‖y‖ := by rw [← Real.norm_eq_abs]; exact this
  linarith

/-- The Minty form of the subgradient graph of a proper convex function:
`gph ∂f = {(x, z - x) ∣ x ∈ P_1 f(z)}`. -/
theorem svGraph_subdifferential_eq_image {f : E → EReal} (hp : IsProper f)
    (hc : Convex ℝ (epigraph f)) :
    svGraph (subdifferential f) =
      (fun p : E × E ↦ (p.2, p.1 - p.2)) '' svGraph (proximalMappingEReal f 1) := by
  rw [proximalMappingEReal_eq_svResolvent_of_convex hp hc one_pos]
  ext ⟨x, v⟩
  simp only [mem_svGraph, mem_image, mem_svResolvent, one_smul, Prod.mk.injEq, Prod.exists]
  constructor
  · intro hv
    exact ⟨x + v, x, ⟨v, hv, rfl⟩, rfl, add_sub_cancel_left x v⟩
  · rintro ⟨z, y, ⟨w, hw, rfl⟩, rfl, rfl⟩
    simpa only [add_sub_cancel_left] using hw

/-- The subdifferential of Rockafellar's chain function of a maximal cyclically monotone mapping is
that mapping (proof of 12.25). -/
theorem subdifferential_rockafellarFunction {T : E → Set E}
    (hT : SvMaximalCyclicallyMonotone T) {x₀ v₀ : E} (h₀ : v₀ ∈ T x₀) :
    subdifferential (rockafellarFunction T x₀ v₀) = T :=
  hT.2 _ (svCyclicallyMonotone_subdifferential_of_convex
    (isProper_rockafellarFunction hT.1 h₀) convex_epigraph_rockafellarFunction)
    fun _ _ h ↦ mem_subdifferential_rockafellarFunction hT.1 h₀ h

omit [FiniteDimensional ℝ E] in
theorem continuous_chainValue_pair {m : ℕ} (x : E) :
    Continuous fun p : (Fin (m + 1) → E) × (Fin (m + 1) → E) ↦ chainValue p.1 p.2 x := by
  unfold chainValue
  fun_prop

end Convex

section Proposition1457

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Proposition 14.57 (subgradient characterization of convex normality).** For `f(t, ·)`
proper, lsc and convex, `f` is a normal integrand if and only if (a) `t ↦ gph ∂f(t, ·)` is
measurable and (b) there is a measurable `x̄` with `∂f(t, x̄(t)) ≠ ∅` for all `t` and
`t ↦ f(t, x̄(t))` measurable. -/
theorem subgradient_characterization_of_convex_normality {f : T → E → EReal}
    (hp : ∀ t, IsProper (f t)) (hl : ∀ t, LowerSemicontinuous (f t))
    (hc : ∀ t, Convex ℝ (epigraph (f t))) :
    IsNormalIntegrand f ↔ SvMeasurable (fun t ↦ svGraph (subdifferential (f t))) ∧
      ∃ xbar : T → E, Measurable xbar ∧ (∀ t, (subdifferential (f t) (xbar t)).Nonempty) ∧
        Measurable fun t ↦ f t (xbar t) := by
  have hmax : ∀ t, SvMaximalMonotone (subdifferential (f t)) := fun t ↦
    svMaximalMonotone_subdifferential_of_convex (hp t) (hl t) (hc t)
  have hGc : ∀ t, IsClosed (svGraph (subdifferential (f t))) := fun t ↦ (hmax t).isClosed_svGraph
  constructor
  · intro hf
    have hthr : ∀ t, ((1 : ℝ) : EReal) < proxThreshold (f t) := fun t ↦ by
      rw [proxThreshold_eq_top_of_convex (hp t) (hl t) (hc t)]
      exact EReal.coe_lt_top 1
    obtain ⟨-, -, -, ⟨-, hGm⟩, hP, -⟩ := moreau_envelopes_and_proximal_mappings hf hp
      measurable_const (fun _ ↦ one_pos) hthr
    obtain ⟨P, hPc, hPeq⟩ := hP hc
    refine ⟨?_, fun t ↦ P t 0, hPc.1 0, fun t ↦ ⟨0 - P t 0, ?_⟩,
      hf.measurable_comp (hPc.1 0)⟩
    · have heq : (fun t ↦ svGraph (subdifferential (f t))) = fun t ↦
          (fun p : E × E ↦ (p.2, p.1 - p.2)) '' svGraph (proximalMappingEReal (f t) 1) :=
        funext fun t ↦ svGraph_subdifferential_eq_image (hp t) (hc t)
      rw [heq]
      exact hGm.image (continuous_snd.prodMk (continuous_fst.sub continuous_snd))
    · have hmem : ((P t 0, 0 - P t 0) : E × E) ∈ svGraph (subdifferential (f t)) := by
        rw [svGraph_subdifferential_eq_image (hp t) (hc t)]
        refine ⟨(0, P t 0), ?_, rfl⟩
        show P t 0 ∈ proximalMappingEReal (f t) 1 0
        rw [hPeq t 0]
        exact mem_singleton _
      exact hmem
  · rintro ⟨hGm, xbar, hxm, hxne, hfx⟩
    -- a measurable subgradient `v̄(t) ∈ ∂f(t, x̄(t))`
    have hΦ : IsCaratheodory fun (t : T) (v : E) ↦ ((xbar t, v) : E × E) :=
      ⟨fun v ↦ hxm.prodMk measurable_const, fun t ↦ continuous_const.prodMk continuous_id⟩
    obtain ⟨hVc, hVm⟩ := hΦ.svMeasurable_preimage hGm hGc
    obtain ⟨vbar, hvm, hv⟩ := hVm.exists_measurable_selection hVc
    have hvbar : ∀ t, vbar t ∈ subdifferential (f t) (xbar t) := fun t ↦
      hv t (by obtain ⟨w, hw⟩ := hxne t; exact ⟨w, hw⟩)
    -- a Castaing representation of the graphs
    have hdom : ∀ t, t ∈ svDom (fun t ↦ svGraph (subdifferential (f t))) := fun t ↦
      ⟨(xbar t, vbar t), hvbar t⟩
    obtain ⟨y, hym, hy⟩ := hGm.exists_castaingRepresentation hGc
    have hyt : ∀ t, svGraph (subdifferential (f t)) = closure (range fun n ↦ y n t) :=
      fun t ↦ hy t (hdom t)
    have hyG : ∀ n t, (y n t).2 ∈ subdifferential (f t) (y n t).1 := fun n t ↦ by
      have : y n t ∈ svGraph (subdifferential (f t)) := by
        rw [hyt t]
        exact subset_closure ⟨n, rfl⟩
      exact this
    -- the countable family of chains
    set J := Σ m : ℕ, Fin m → ℕ
    set xs : (j : J) → T → Fin (j.1 + 1) → E := fun j t ↦
      Fin.cons (xbar t) fun i ↦ (y (j.2 i) t).1
    set vs : (j : J) → T → Fin (j.1 + 1) → E := fun j t ↦
      Fin.cons (vbar t) fun i ↦ (y (j.2 i) t).2
    set h : J → T → E → ℝ := fun j t x ↦ (f t (xbar t)).toReal + chainValue (xs j t) (vs j t) x
    have hcar : ∀ j, IsCaratheodory (h j) := by
      intro j
      refine ⟨fun x ↦ ?_, fun t ↦ continuous_const.add (continuous_chainValue _ _)⟩
      have hxsm : Measurable (xs j) := by
        refine measurable_pi_lambda _ fun i ↦ ?_
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · simpa [xs] using hxm
        · simpa [xs] using measurable_fst.comp (hym (j.2 i))
      have hvsm : Measurable (vs j) := by
        refine measurable_pi_lambda _ fun i ↦ ?_
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · simpa [vs] using hvm
        · simpa [vs] using measurable_snd.comp (hym (j.2 i))
      exact hfx.ereal_toReal.add
        ((continuous_chainValue_pair x).measurable.comp (hxsm.prodMk hvsm))
    -- `f` is the supremum of the chain integrands
    have hsup : f = fun t x ↦ ⨆ j : J, ((h j t x : ℝ) : EReal) := by
      funext t x
      set Tt := subdifferential (f t)
      have hTt := svMaximalCyclicallyMonotone_subdifferential_of_convex (hp t) (hl t) (hc t)
      set g := rockafellarFunction Tt (xbar t) (vbar t)
      obtain ⟨c, hcg⟩ := exists_eq_add_const_of_subdifferential_eq (hp t) (hl t) (hc t)
        (isProper_rockafellarFunction hTt.1 (hvbar t)) lowerSemicontinuous_rockafellarFunction
        convex_epigraph_rockafellarFunction
        (subdifferential_rockafellarFunction hTt (hvbar t)).symm
      have hfx' : ∀ z, f t z = g z + (c : EReal) := fun z ↦ congrFun hcg z
      have hc0 : f t (xbar t) = (c : EReal) := by
        rw [hfx']
        show rockafellarFunction Tt (xbar t) (vbar t) (xbar t) + (c : EReal) = c
        rw [rockafellarFunction_self hTt.1 (hvbar t), zero_add]
      have hcval : (f t (xbar t)).toReal = c := by rw [hc0, EReal.toReal_coe]
      -- each countable chain is a chain
      have hchainmem : ∀ (j : J) (i : Fin (j.1 + 1)), vs j t i ∈ Tt (xs j t i) := by
        intro j i
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · simpa [xs, vs] using hvbar t
        · simpa [xs, vs] using hyG (j.2 i) t
      -- every chain is approximated by a countable chain
      have happrox : ∀ (ch : SvChain Tt (xbar t) (vbar t)) (ε : ℝ), 0 < ε →
          ∃ j : J, chainValue ch.2.1.1 ch.2.1.2 x - ε < chainValue (xs j t) (vs j t) x := by
        rintro ⟨m, ⟨⟨cx, cv⟩, h0x, h0v, hmem⟩⟩ ε hε
        obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 (continuous_chainValue_pair (m := m) x)
          (cx, cv) ε hε
        have hnear : ∀ i : Fin m, ∃ n, dist ((cx i.succ, cv i.succ) : E × E) (y n t) < δ := by
          intro i
          have hG : ((cx i.succ, cv i.succ) : E × E) ∈ svGraph (subdifferential (f t)) :=
            hmem i.succ
          rw [hyt t] at hG
          exact Metric.mem_closure_range_iff.1 hG δ hδ
        choose ν hν using hnear
        refine ⟨⟨m, ν⟩, ?_⟩
        have hd : dist ((xs ⟨m, ν⟩ t, vs ⟨m, ν⟩ t) : (Fin (m + 1) → E) × (Fin (m + 1) → E))
            (cx, cv) < δ := by
          rw [Prod.dist_eq, max_lt_iff]
          constructor
          · refine (dist_pi_lt_iff hδ).2 fun k ↦ ?_
            refine Fin.cases ?_ (fun i ↦ ?_) k
            · simp only [xs, Fin.cons_zero]
              rw [← h0x, dist_self]
              exact hδ
            · simp only [xs, Fin.cons_succ]
              calc dist (y (ν i) t).1 (cx i.succ) ≤ dist (y (ν i) t) (cx i.succ, cv i.succ) := by
                    rw [Prod.dist_eq]
                    exact le_max_left _ _
                _ < δ := by rw [dist_comm]; exact hν i
          · refine (dist_pi_lt_iff hδ).2 fun k ↦ ?_
            refine Fin.cases ?_ (fun i ↦ ?_) k
            · simp only [vs, Fin.cons_zero]
              rw [← h0v, dist_self]
              exact hδ
            · simp only [vs, Fin.cons_succ]
              calc dist (y (ν i) t).2 (cv i.succ) ≤ dist (y (ν i) t) (cx i.succ, cv i.succ) := by
                    rw [Prod.dist_eq]
                    exact le_max_right _ _
                _ < δ := by rw [dist_comm]; exact hν i
        have := hcont _ hd
        rw [Real.dist_eq, abs_lt] at this
        simp only at this ⊢
        linarith [this.1]
      apply le_antisymm
      · refine le_of_forall_lt fun z hz ↦ ?_
        rw [hfx'] at hz
        induction z using EReal.rec with
        | bot =>
          exact lt_of_lt_of_le (EReal.bot_lt_coe _)
            (le_iSup (fun j : J ↦ ((h j t x : ℝ) : EReal)) ⟨0, Fin.elim0⟩)
        | top => exact absurd hz (not_lt.2 le_top)
        | coe r =>
          have hr : ((r - c : ℝ) : EReal) <
              ⨆ ch : SvChain Tt (xbar t) (vbar t), (chainValue ch.2.1.1 ch.2.1.2 x : EReal) := by
            change ((r - c : ℝ) : EReal) < g x
            induction hg : g x using EReal.rec with
            | bot =>
              rw [hg, EReal.bot_add] at hz
              exact absurd hz (not_lt.2 bot_le)
            | top => exact EReal.coe_lt_top _
            | coe a =>
              rw [hg, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hz
              exact EReal.coe_lt_coe_iff.2 (by linarith)
          obtain ⟨ch, hch⟩ := lt_iSup_iff.1 hr
          have hch' : r - c < chainValue ch.2.1.1 ch.2.1.2 x := EReal.coe_lt_coe_iff.1 hch
          obtain ⟨j, hj⟩ := happrox ch _ (sub_pos.2 hch')
          refine lt_of_lt_of_le ?_ (le_iSup _ j)
          simp only [h, hcval]
          exact EReal.coe_lt_coe_iff.2 (by linarith)
      · refine iSup_le fun j ↦ ?_
        have := chainValue_le_rockafellarFunction (T := Tt) (x₀ := xbar t) (v₀ := vbar t)
          ⟨j.1, ⟨(xs j t, vs j t), by simp [xs], by simp [vs], hchainmem j⟩⟩ x
        change ((chainValue (xs j t) (vs j t) x : ℝ) : EReal) ≤ g x at this
        rw [hfx' x]
        simp only [h, hcval]
        rw [EReal.coe_add, add_comm]
        exact add_le_add this le_rfl
    rw [hsup]
    exact IsNormalIntegrand.iSup fun j ↦ (hcar j).isNormalIntegrand

end Proposition1457

end RW
