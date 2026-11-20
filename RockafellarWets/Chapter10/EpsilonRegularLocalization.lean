/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: ε-regular subgradients under local lower semicontinuity

**Proposition 10.46** under the book's hypothesis that `f` is only locally lsc at `x̄`:
the two descriptions of `∂_ε f(x̄)` agree (`mem_epsRegularSubdifferential_iff_subderivative`, via
8(7) for `f + ε|· - x̄|`), limits along `xᵛ →_f x̄`, `εᵛ ↘ 0` give subgradients and scaled limits
give horizon subgradients (`epsRegular_limits_of_locallyLsc`), and hence the cosmic formula for
`limsup ∂_ε f(x)` in sequential form (`mem_subdifferential_iff_epsRegular_limits_of_locallyLsc`,
`mem_horizonSubdifferential_iff_epsRegular_limits_of_locallyLsc`).  The
truncation `f̃ = max (min f M) L` on a closed ball `IB(x̄, ε)` of local lower semicontinuity
(`∞` outside), with `L < f(x̄) < M = f(x̄) + ε`, is lsc and proper (`lscLocalization`), agrees
with `f` near points `x` close to `x̄` with `f(x)` near `f(x̄)`, and has `∂f̃(x̄) ⊂ ∂f(x̄)`,
`∂^∞f̃(x̄) ⊂ ∂^∞f(x̄)`, so the lsc, proper statements in `EpsilonRegularSubgradients` apply to
`f̃`.
-/

import RockafellarWets.Chapter10.EpsilonRegularSubgradients
import RockafellarWets.Chapter10.SubderivativeSmoothAddition
import RockafellarWets.Chapter8.RegularSubgradientBridge

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
/-- The truncated localization `max (min f M) L` on `IB(x̄, ε)`, `∞` outside. -/
noncomputable def lscLocalization (f : E → EReal) (x : E) (ε L M : ℝ) : E → EReal :=
  fun y ↦ if y ∈ closedBall x ε then max (min (f y) M) L else ⊤

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem lscLocalization_of_mem {f : E → EReal} {x y : E} {ε L M : ℝ} (hy : y ∈ closedBall x ε) :
    lscLocalization f x ε L M y = max (min (f y) M) L := by
  simp [lscLocalization, hy]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem lscLocalization_of_not_mem {f : E → EReal} {x y : E} {ε L M : ℝ}
    (hy : y ∉ closedBall x ε) : lscLocalization f x ε L M y = ⊤ := by
  simp [lscLocalization, hy]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem lscLocalization_eq {f : E → EReal} {x y : E} {ε L M : ℝ} (hy : y ∈ closedBall x ε)
    (hL : (L : EReal) ≤ f y) (hM : f y ≤ M) : lscLocalization f x ε L M y = f y := by
  rw [lscLocalization_of_mem hy, min_eq_left hM, max_eq_left hL]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The localization is lsc when the sublevel sets of `f` in `IB(x̄, ε)` up to level `M` are
closed. -/
theorem lowerSemicontinuous_lscLocalization {f : E → EReal} {x : E} {ε L M : ℝ}
    (hcl : ∀ α : ℝ, α ≤ M → IsClosed (closedBall x ε ∩ {y | f y ≤ α})) :
    LowerSemicontinuous (lscLocalization f x ε L M) := by
  refine lowerSemicontinuous_iff_isClosed_preimage.2 fun α ↦ ?_
  induction α using EReal.rec with
  | bot =>
    convert isClosed_empty
    ext y
    simp only [mem_preimage, mem_Iic, le_bot_iff, mem_empty_iff_false, iff_false]
    by_cases hy : y ∈ closedBall x ε
    · rw [lscLocalization_of_mem hy]
      exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe L) (le_max_right _ _))
    · rw [lscLocalization_of_not_mem hy]
      exact top_ne_bot
  | top =>
    convert isClosed_univ
    ext y
    simp
  | coe r =>
    by_cases hrL : r < L
    · convert isClosed_empty
      ext y
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
      by_cases hy : y ∈ closedBall x ε
      · rw [lscLocalization_of_mem hy]
        exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hrL) (le_max_right _ _)
      · rw [lscLocalization_of_not_mem hy]
        exact EReal.coe_lt_top r
    · push_neg at hrL
      by_cases hrM : r < M
      · convert hcl r hrM.le using 1
        ext y
        simp only [mem_preimage, mem_Iic, mem_inter_iff, mem_setOf_eq]
        by_cases hy : y ∈ closedBall x ε
        · rw [lscLocalization_of_mem hy]
          simp only [hy, true_and, max_le_iff, EReal.coe_le_coe_iff.2 hrL, and_true,
            min_le_iff]
          constructor
          · rintro (h | h)
            · exact h
            · exact absurd (EReal.coe_le_coe_iff.1 h) (not_le.2 hrM)
          · exact Or.inl
        · rw [lscLocalization_of_not_mem hy]
          simp [hy]
      · push_neg at hrM
        convert (isClosed_closedBall : IsClosed (closedBall x ε)) using 1
        ext y
        simp only [mem_preimage, mem_Iic]
        by_cases hy : y ∈ closedBall x ε
        · rw [lscLocalization_of_mem hy]
          simp only [hy, iff_true]
          exact max_le ((min_le_right _ _).trans (EReal.coe_le_coe_iff.2 hrM))
            (EReal.coe_le_coe_iff.2 hrL)
        · rw [lscLocalization_of_not_mem hy]
          simp [hy]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem isProper_lscLocalization {f : E → EReal} {x : E} {ε L M : ℝ} (hε : 0 ≤ ε) :
    IsProper (lscLocalization f x ε L M) := by
  refine ⟨⟨x, ?_⟩, fun y ↦ ?_⟩
  · rw [lscLocalization_of_mem (mem_closedBall_self hε)]
    exact lt_of_le_of_lt (max_le_max (min_le_right _ _) le_rfl)
      (max_lt (EReal.coe_lt_top M) (EReal.coe_lt_top L))
  · by_cases hy : y ∈ closedBall x ε
    · rw [lscLocalization_of_mem hy]
      exact lt_of_lt_of_le (EReal.bot_lt_coe L) (le_max_right _ _)
    · rw [lscLocalization_of_not_mem hy]
      exact bot_lt_top

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem eq_of_max_min_mem_Ioo {a : EReal} {L M : ℝ}
    (h : max (min a M) L ∈ Ioo (L : EReal) M) : max (min a M) L = a := by
  obtain ⟨h1, h2⟩ := h
  have hm : (L : EReal) < min a M := by
    by_contra hc
    push_neg at hc
    rw [max_eq_right hc] at h1
    exact lt_irrefl _ h1
  rw [max_eq_left hm.le] at h2 ⊢
  have ha : a < M := by
    rcases min_lt_iff.1 h2 with h | h
    · exact h
    · exact absurd h (lt_irrefl _)
  exact min_eq_left ha.le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Closed sublevel sets near `x̄` make `f` lsc at nearby points below level `M`. -/
theorem eventually_lt_of_closed_sublevel {f : E → EReal} {x z : E} {ε M α : ℝ}
    (hcl : ∀ a : ℝ, a ≤ M → IsClosed (closedBall x ε ∩ {y | f y ≤ a}))
    (hz : z ∈ ball x ε) (hαM : α ≤ M) (hα : (α : EReal) < f z) :
    ∀ᶠ y in 𝓝 z, (α : EReal) < f y ∧ y ∈ ball x ε := by
  have hopen : IsOpen ((closedBall x ε ∩ {y | f y ≤ α})ᶜ) := (hcl α hαM).isOpen_compl
  have hmem : z ∈ (closedBall x ε ∩ {y | f y ≤ α})ᶜ := fun h ↦ (not_le.2 hα) h.2
  filter_upwards [hopen.mem_nhds hmem, isOpen_ball.mem_nhds hz] with y hy1 hy2
  refine ⟨?_, hy2⟩
  by_contra h
  exact hy1 ⟨ball_subset_closedBall hy2, not_lt.1 h⟩

omit [FiniteDimensional ℝ E] in
/-- `ε`-regular subgradients of `f` at points `z` near `x̄` with `L ≤ f(z) < M` are `ε`-regular
subgradients of the localization. -/
theorem mem_eps_lscLocalization {f : E → EReal} {x z v : E} {ε L M η : ℝ} (hz : z ∈ ball x ε)
    {a : ℝ} (ha : f z = a) (haL : L ≤ a) (haM : a < M)
    (hv : v ∈ epsRegularSubdifferential f η z) :
    v ∈ epsRegularSubdifferential (lscLocalization f x ε L M) η z := by
  obtain ⟨c, hc, h⟩ := hv
  have hca : a = c := by
    rw [ha] at hc
    exact EReal.coe_eq_coe_iff.1 hc
  subst hca
  refine ⟨a, ?_, fun θ hθ ↦ ?_⟩
  · rw [lscLocalization_eq (ball_subset_closedBall hz) (by rw [ha]; exact EReal.coe_le_coe_iff.2 haL)
      (by rw [ha]; exact EReal.coe_le_coe_iff.2 haM.le), ha]
  · have hcont : ContinuousAt (fun y ↦ a + ⟪v, y - z⟫_ℝ - (η + θ) * ‖y - z‖) z := by fun_prop
    have hz0 : a + ⟪v, z - z⟫_ℝ - (η + θ) * ‖z - z‖ < M := by simp [haM]
    filter_upwards [h θ hθ, hcont.tendsto.eventually (gt_mem_nhds hz0), isOpen_ball.mem_nhds hz]
      with y hy hyM hyB
    rw [lscLocalization_of_mem (ball_subset_closedBall hyB)]
    exact le_trans (le_min hy (EReal.coe_le_coe_iff.2 hyM.le)) (le_max_left _ _)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem eventually_attentive_lscLocalization {f : E → EReal} {x : E} {ε L M c : ℝ} (hε : 0 < ε)
    (hc : f x = c) (hLc : L < c) (hcM : c < M) :
    lscLocalization f x ε L M x = c ∧
      ∀ᶠ y in attentiveNhds (lscLocalization f x ε L M) x, y ∈ ball x ε ∧
        lscLocalization f x ε L M y ∈ Ioo (L : EReal) M := by
  have hgx : lscLocalization f x ε L M x = c := by
    rw [lscLocalization_eq (mem_closedBall_self hε.le)
      (by rw [hc]; exact EReal.coe_le_coe_iff.2 hLc.le)
      (by rw [hc]; exact EReal.coe_le_coe_iff.2 hcM.le), hc]
  refine ⟨hgx, ?_⟩
  have h1 : ∀ᶠ y in attentiveNhds (lscLocalization f x ε L M) x, y ∈ ball x ε :=
    (inf_le_left : attentiveNhds (lscLocalization f x ε L M) x ≤ 𝓝 x)
      (isOpen_ball.mem_nhds (mem_ball_self hε))
  have ht : Tendsto (lscLocalization f x ε L M) (attentiveNhds (lscLocalization f x ε L M) x)
      (𝓝 (lscLocalization f x ε L M x)) := tendsto_comap.mono_left inf_le_right
  have h2 : ∀ᶠ y in attentiveNhds (lscLocalization f x ε L M) x,
      lscLocalization f x ε L M y ∈ Ioo (L : EReal) M :=
    ht (isOpen_Ioo.mem_nhds (by
      rw [hgx]
      exact ⟨EReal.coe_lt_coe_iff.2 hLc, EReal.coe_lt_coe_iff.2 hcM⟩))
  filter_upwards [h1, h2] with y hy1 hy2
  exact ⟨hy1, hy2⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem lscLocalization_eq_of_mem_Ioo {f : E → EReal} {x y : E} {ε L M : ℝ}
    (hy : y ∈ ball x ε) (hI : lscLocalization f x ε L M y ∈ Ioo (L : EReal) M) :
    lscLocalization f x ε L M y = f y := by
  rw [lscLocalization_of_mem (ball_subset_closedBall hy)] at hI ⊢
  exact eq_of_max_min_mem_Ioo hI

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem attentiveNhds_lscLocalization_le {f : E → EReal} {x : E} {ε L M c : ℝ} (hε : 0 < ε)
    (hc : f x = c) (hLc : L < c) (hcM : c < M) :
    attentiveNhds (lscLocalization f x ε L M) x ≤ attentiveNhds f x := by
  obtain ⟨hgx, hev⟩ := eventually_attentive_lscLocalization (f := f) hε hc hLc hcM
  have hev' : ∀ᶠ y in attentiveNhds (lscLocalization f x ε L M) x,
      lscLocalization f x ε L M y = f y :=
    hev.mono fun y hy ↦ lscLocalization_eq_of_mem_Ioo hy.1 hy.2
  have ht : Tendsto (lscLocalization f x ε L M) (attentiveNhds (lscLocalization f x ε L M) x)
      (𝓝 (lscLocalization f x ε L M x)) := tendsto_comap.mono_left inf_le_right
  rw [hgx, ← hc] at ht
  exact le_inf inf_le_left (tendsto_iff_comap.1 (ht.congr' hev'))

omit [FiniteDimensional ℝ E] in
theorem regularSubdifferential_lscLocalization_subset {f : E → EReal} {x z : E} {ε L M : ℝ}
    (hLM : L ≤ M) (hcl : ∀ a : ℝ, a ≤ M → IsClosed (closedBall x ε ∩ {y | f y ≤ a}))
    (hz : z ∈ ball x ε) (hzI : lscLocalization f x ε L M z ∈ Ioo (L : EReal) M) :
    regularSubdifferential (lscLocalization f x ε L M) z ⊆ regularSubdifferential f z := by
  have hfz := lscLocalization_eq_of_mem_Ioo hz hzI
  have hfzL : (L : EReal) < f z := by rw [← hfz]; exact hzI.1
  have hev := eventually_lt_of_closed_sublevel hcl hz hLM hfzL
  rintro v ⟨c, hc, h⟩
  refine ⟨c, by rw [← hfz, hc], fun η hη ↦ ?_⟩
  filter_upwards [h η hη, hev] with y hy hy'
  refine hy.trans ?_
  rw [lscLocalization_of_mem (ball_subset_closedBall hy'.2),
    max_eq_left (le_min hy'.1.le (EReal.coe_le_coe_iff.2 hLM))]
  exact min_le_left _ _

omit [FiniteDimensional ℝ E] in
theorem subdifferentials_lscLocalization_subset {f : E → EReal} {x : E} {ε L M c : ℝ}
    (hε : 0 < ε) (hc : f x = c) (hLc : L < c) (hcM : c < M)
    (hcl : ∀ a : ℝ, a ≤ M → IsClosed (closedBall x ε ∩ {y | f y ≤ a})) :
    subdifferential (lscLocalization f x ε L M) x ⊆ subdifferential f x ∧
      horizonSubdifferential (lscLocalization f x ε L M) x ⊆ horizonSubdifferential f x := by
  obtain ⟨hgx, hev⟩ := eventually_attentive_lscLocalization (f := f) hε hc hLc hcM
  have hle := attentiveNhds_lscLocalization_le (f := f) hε hc hLc hcM
  have hsub : ∀ᶠ z in attentiveNhds (lscLocalization f x ε L M) x,
      regularSubdifferential (lscLocalization f x ε L M) z ⊆ regularSubdifferential f z :=
    hev.mono fun z hz ↦ regularSubdifferential_lscLocalization_subset
      (hLc.trans hcM).le hcl hz.1 hz.2
  constructor
  · rw [subdifferential_of_finite hgx, subdifferential_of_finite hc]
    intro v hv
    refine outerSetLimitAlong_mono_filter hle _ fun V hV ↦ ?_
    exact (hv V hV).mp (hsub.mono fun z hz ⟨w, hw, hwV⟩ ↦ ⟨w, hz hw, hwV⟩)
  · rw [horizonSubdifferential_of_finite hgx, horizonSubdifferential_of_finite hc]
    refine cosmicDirectionCone_mono ?_
    intro p hp
    refine outerSetLimitAlong_mono_filter hle _ fun V hV ↦ ?_
    exact (hp V hV).mp (hsub.mono fun z hz ⟨w, hw, hwV⟩ ↦
      ⟨w, cosmicSet_mono hz Subset.rfl hw, hwV⟩)

/-- **Proposition 10.46** for `f` locally lsc at `x̄`: limits of `vᵛ ∈ ∂_{εᵛ} f(xᵛ)` along
`xᵛ →_f x̄`, `εᵛ ↘ 0` lie in `∂f(x̄)`, and limits of `tᵛvᵛ` with `tᵛ ↘ 0` lie in `∂^∞f(x̄)`. -/
theorem epsRegular_limits_of_locallyLsc {f : E → EReal} {x : E} (hl : IsLocallyLscAt f x)
    {xs : ℕ → E} {εs : ℕ → ℝ} {vs : ℕ → E} (hxs : Tendsto xs atTop (attentiveNhds f x))
    (hε0 : ∀ n, 0 ≤ εs n) (hε : Tendsto εs atTop (𝓝 0))
    (hvs : ∀ n, vs n ∈ epsRegularSubdifferential f (εs n) (xs n)) :
    (∀ v, Tendsto vs atTop (𝓝 v) → v ∈ subdifferential f x) ∧
      (∀ (ts : ℕ → ℝ) v, (∀ n, 0 < ts n) → Tendsto ts atTop (𝓝 0) →
        Tendsto (fun n ↦ ts n • vs n) atTop (𝓝 v) → v ∈ horizonSubdifferential f x) := by
  obtain ⟨hbot, htop, ε, hεpos, hcl⟩ := hl
  set c := (f x).toReal with hcdef
  have hc : f x = c := (EReal.coe_toReal htop hbot).symm
  have hcl' : ∀ a : ℝ, a ≤ c + ε → IsClosed (closedBall x ε ∩ {y | f y ≤ a}) := hcl
  have hLc : c - 1 < c := by linarith
  have hcM : c < c + ε := by linarith
  set g := lscLocalization f x ε (c - 1) (c + ε) with hg
  have hgl : LowerSemicontinuous g := lowerSemicontinuous_lscLocalization hcl'
  have hgp : IsProper g := isProper_lscLocalization hεpos.le
  obtain ⟨hgx, -⟩ := eventually_attentive_lscLocalization (f := f) hεpos hc hLc hcM
  obtain ⟨hsub, hhor⟩ := subdifferentials_lscLocalization_subset hεpos hc hLc hcM hcl'
  obtain ⟨hx1, hx2⟩ := tendsto_attentiveNhds_iff.1 hxs
  have hev : ∀ᶠ n in atTop, xs n ∈ ball x ε ∧ f (xs n) ∈ Ioo ((c - 1 : ℝ) : EReal) (c + ε : ℝ) := by
    filter_upwards [hx1 (isOpen_ball.mem_nhds (mem_ball_self hεpos)), hx2 (isOpen_Ioo.mem_nhds (by
      show f x ∈ Ioo ((c - 1 : ℝ) : EReal) (c + ε : ℝ)
      rw [hc]
      exact ⟨EReal.coe_lt_coe_iff.2 hLc, EReal.coe_lt_coe_iff.2 hcM⟩))] with n h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hval : ∀ n, ∃ a : ℝ, f (xs (n + N)) = a ∧ c - 1 < a ∧ a < c + ε := by
    intro n
    obtain ⟨-, h1, h2⟩ := hN (n + N) (Nat.le_add_left N n)
    have hne_top : f (xs (n + N)) ≠ ⊤ := ne_top_of_lt h2
    have hne_bot : f (xs (n + N)) ≠ ⊥ := ne_bot_of_gt h1
    refine ⟨(f (xs (n + N))).toReal, (EReal.coe_toReal hne_top hne_bot).symm, ?_, ?_⟩
    · rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hne_top hne_bot]
      exact h1
    · rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hne_top hne_bot]
      exact h2
  have hvs' : ∀ n, vs (n + N) ∈ epsRegularSubdifferential g (εs (n + N)) (xs (n + N)) := by
    intro n
    obtain ⟨a, ha, haL, haM⟩ := hval n
    exact mem_eps_lscLocalization (hN (n + N) (Nat.le_add_left N n)).1 ha haL.le haM (hvs _)
  have hxs' : Tendsto (fun n ↦ xs (n + N)) atTop (attentiveNhds g x) := by
    refine tendsto_attentiveNhds_iff.2 ⟨(tendsto_add_atTop_iff_nat N).2 hx1, ?_⟩
    have heq : ∀ n, g (xs (n + N)) = f (xs (n + N)) := fun n ↦ by
      obtain ⟨a, ha, haL, haM⟩ := hval n
      exact lscLocalization_eq (ball_subset_closedBall (hN (n + N) (Nat.le_add_left N n)).1)
        (by rw [ha]; exact EReal.coe_le_coe_iff.2 haL.le)
        (by rw [ha]; exact EReal.coe_le_coe_iff.2 haM.le)
    have h := (tendsto_add_atTop_iff_nat N).2 hx2
    rw [hc] at h
    rw [Function.comp_def, show g x = ((c : ℝ) : EReal) from hgx]
    exact h.congr fun n ↦ (heq n).symm
  refine ⟨fun v hv ↦ hsub (mem_subdifferential_of_epsRegular_limits hgl hgp hgx hxs'
    (fun n ↦ hε0 _) ((tendsto_add_atTop_iff_nat N).2 hε) hvs'
    ((tendsto_add_atTop_iff_nat N).2 hv)), fun ts v ht0 ht hv ↦ hhor ?_⟩
  exact mem_horizonSubdifferential_of_epsRegular_limits hgl hgp hgx hxs' (fun n ↦ hε0 _)
    ((tendsto_add_atTop_iff_nat N).2 hε) hvs' (fun n ↦ ht0 _)
    ((tendsto_add_atTop_iff_nat N).2 ht) ((tendsto_add_atTop_iff_nat N).2 hv)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem ereal_coe_sub_le_iff {a : EReal} {s r : ℝ} :
    ((s - r : ℝ) : EReal) ≤ a ↔ ((s : ℝ) : EReal) ≤ a + r := by
  induction a using EReal.rec with
  | bot =>
    rw [EReal.bot_add, le_bot_iff, le_bot_iff]
    exact ⟨fun h ↦ absurd h (EReal.coe_ne_bot _), fun h ↦ absurd h (EReal.coe_ne_bot _)⟩
  | top => rw [EReal.top_add_coe]; exact ⟨fun _ ↦ le_top, fun _ ↦ le_top⟩
  | coe b =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

omit [FiniteDimensional ℝ E] in
/-- Conversely, `∂̂(f + ε|· - x̄|)(x̄) ⊂ ∂_ε f(x̄)`. -/
theorem mem_eps_of_mem_regularSubdifferential_add_norm {f : E → EReal} {ε : ℝ} {x v : E}
    (hv : v ∈ regularSubdifferential (fun y ↦ f y + ((ε * ‖y - x‖ : ℝ) : EReal)) x) :
    v ∈ epsRegularSubdifferential f ε x := by
  obtain ⟨c, hc, h⟩ := hv
  have hfx : f x = c := by simpa using hc
  refine ⟨c, hfx, fun η hη ↦ ?_⟩
  filter_upwards [h η hη] with y hy
  have hy' : ((c + ⟪v, y - x⟫_ℝ - (ε + η) * ‖y - x‖ + ε * ‖y - x‖ : ℝ) : EReal) ≤
      f y + ((ε * ‖y - x‖ : ℝ) : EReal) := by
    convert hy using 2
    ring
  have h2 := (ereal_coe_sub_le_iff (s := c + ⟪v, y - x⟫_ℝ - (ε + η) * ‖y - x‖ + ε * ‖y - x‖)
    (r := ε * ‖y - x‖)).2 hy'
  convert h2 using 2
  ring

omit [FiniteDimensional ℝ E] in
theorem hasDirectionalSemiderivative_mul_norm_sub (ε : ℝ) (x w : E) :
    HasDirectionalSemiderivative (fun y ↦ ε * ‖y - x‖) x w (ε * ‖w‖) := by
  have h : Tendsto (fun p : ℝ × E ↦ ε * ‖p.2‖) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (ε * ‖w‖)) :=
    (tendsto_snd.norm).const_mul ε
  refine h.congr' ?_
  filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p hp
  have hp' : 0 < p.1 := hp
  simp only [add_sub_cancel_left, sub_self, norm_zero, mul_zero, sub_zero, norm_smul,
    Real.norm_of_nonneg hp'.le, smul_eq_mul]
  field_simp

/-- **Proposition 10.46**, the two descriptions of `∂_ε f(x̄)`:
`v ∈ ∂_ε f(x̄)` iff `df(x̄)(w) ≥ ⟪v, w⟫ - ε|w|` for all `w`. -/
theorem mem_epsRegularSubdifferential_iff_subderivative {f : E → EReal} {ε : ℝ} {x v : E} {c : ℝ}
    (hx : f x = c) :
    v ∈ epsRegularSubdifferential f ε x ↔
      ∀ w, ((⟪v, w⟫_ℝ - ε * ‖w‖ : ℝ) : EReal) ≤ subderivative f x w := by
  have hg : f x + ((ε * ‖x - x‖ : ℝ) : EReal) = (c : EReal) := by simp [hx]
  have hd : ∀ w, subderivative (fun y ↦ f y + ((ε * ‖y - x‖ : ℝ) : EReal)) x w =
      subderivative f x w + ((ε * ‖w‖ : ℝ) : EReal) := fun w ↦
    subderivative_add_real_of_hasDirectionalSemiderivative hx
      (hasDirectionalSemiderivative_mul_norm_sub ε x w)
  have heq : (fun y ↦ ((ε * ‖y - x‖ : ℝ) : EReal) + f y) =
      fun y ↦ f y + ((ε * ‖y - x‖ : ℝ) : EReal) := funext fun y ↦ add_comm _ _
  constructor
  · intro hv w
    have hreg := mem_regularSubdifferential_add_norm hv
    rw [heq] at hreg
    have h := (mem_regularSubdifferential_iff_inner_le_subderivative
      (f := fun y ↦ f y + ((ε * ‖y - x‖ : ℝ) : EReal)) (x := x) hg).1 hreg w
    rw [hd] at h
    exact ereal_coe_sub_le_iff.2 h
  · intro h
    apply mem_eps_of_mem_regularSubdifferential_add_norm
    refine (mem_regularSubdifferential_iff_inner_le_subderivative
      (f := fun y ↦ f y + ((ε * ‖y - x‖ : ℝ) : EReal)) (x := x) hg).2 fun w ↦ ?_
    rw [hd]
    exact ereal_coe_sub_le_iff.1 (h w)

/-- **Proposition 10.46**, the formula `limsup_{x →_f x̄, ε ↘ 0} ∂_ε f(x) = ∂f(x̄) ∪ dir ∂^∞f(x̄)`
for `f` locally lsc at `x̄`, finite part in sequential form. -/
theorem mem_subdifferential_iff_epsRegular_limits_of_locallyLsc {f : E → EReal} {x v : E}
    (hl : IsLocallyLscAt f x) :
    v ∈ subdifferential f x ↔ ∃ (xs : ℕ → E) (εs : ℕ → ℝ) (vs : ℕ → E),
      Tendsto xs atTop (attentiveNhds f x) ∧ (∀ n, 0 ≤ εs n) ∧ Tendsto εs atTop (𝓝 0) ∧
        (∀ n, vs n ∈ epsRegularSubdifferential f (εs n) (xs n)) ∧ Tendsto vs atTop (𝓝 v) := by
  have hc : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hl.2.1 hl.1).symm
  constructor
  · intro hv
    rw [subdifferential_of_finite hc] at hv
    obtain ⟨xs, vs, hxs, hvs, hvl⟩ := mem_outerSetLimitAlong_iff_exists_seq.1 hv
    exact ⟨xs, fun _ ↦ 0, vs, hxs, fun _ ↦ le_rfl, tendsto_const_nhds,
      fun n ↦ regularSubdifferential_subset_eps le_rfl (xs n) (hvs n), hvl⟩
  · rintro ⟨xs, εs, vs, hxs, hε0, hε, hvs, hvl⟩
    exact (epsRegular_limits_of_locallyLsc hl hxs hε0 hε hvs).1 v hvl

/-- **Proposition 10.46**, the limsup formula for `f` locally lsc at `x̄`, direction part in
sequential form. -/
theorem mem_horizonSubdifferential_iff_epsRegular_limits_of_locallyLsc {f : E → EReal} {x v : E}
    (hl : IsLocallyLscAt f x) :
    v ∈ horizonSubdifferential f x ↔ v = 0 ∨ ∃ (xs : ℕ → E) (εs ts : ℕ → ℝ) (vs : ℕ → E),
      Tendsto xs atTop (attentiveNhds f x) ∧ (∀ n, 0 ≤ εs n) ∧ Tendsto εs atTop (𝓝 0) ∧
        (∀ n, vs n ∈ epsRegularSubdifferential f (εs n) (xs n)) ∧ (∀ n, 0 < ts n) ∧
        Tendsto ts atTop (𝓝 0) ∧ Tendsto (fun n ↦ ts n • vs n) atTop (𝓝 v) := by
  have hc : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hl.2.1 hl.1).symm
  constructor
  · intro hv
    rcases (mem_horizonSubdifferential_iff_zero_or_scaledSeq hc).1 hv with h0 | ⟨xs, vs, ts, hxs,
      hvs, ht0, ht, hvl⟩
    · exact Or.inl h0
    · exact Or.inr ⟨xs, fun _ ↦ 0, ts, vs, hxs, fun _ ↦ le_rfl, tendsto_const_nhds,
        fun n ↦ regularSubdifferential_subset_eps le_rfl (xs n) (hvs n), ht0, ht, hvl⟩
  · rintro (rfl | ⟨xs, εs, ts, vs, hxs, hε0, hε, hvs, ht0, ht, hvl⟩)
    · exact (subdifferential_properties hc).2.2.2.2.1.1
    · exact (epsRegular_limits_of_locallyLsc hl hxs hε0 hε hvs).2 ts v ht0 ht hvl

end RW
