/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Perturbation of saddle values (Golshtein)

Theorem 11.53.
-/
import RockafellarWets.Chapter11.MinimaxProblems
import RockafellarWets.Chapter5.LocallyBoundedContinuity
import RockafellarWets.Chapter5.Semicontinuity

open Set Filter Topology Bornology Metric Classical
open scoped InnerProductSpace
namespace RW
noncomputable section

section Helpers
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [InnerProductSpace ℝ F] in
theorem mem_cthickening_iff_infDist_le_of_nonempty {s : Set F} (hs : s.Nonempty) {δ : ℝ}
    (hδ : 0 ≤ δ) (x : F) : x ∈ cthickening δ s ↔ infDist x s ≤ δ := by
  rw [mem_cthickening_iff, infDist, ← ENNReal.ofReal_le_ofReal_iff hδ,
    ENNReal.ofReal_toReal (infEDist_ne_top hs)]

omit [InnerProductSpace ℝ F] in
theorem ball_subset_cthickening_of_infDist_lt {s : Set F} (hs : s.Nonempty) {δ : ℝ} {x₀ : F}
    (hx₀ : infDist x₀ s < δ) : ball x₀ (δ - infDist x₀ s) ⊆ cthickening δ s := by
  intro x hx
  have hδ : 0 ≤ δ := infDist_nonneg.trans hx₀.le
  rw [mem_cthickening_iff_infDist_le_of_nonempty hs hδ]
  have := infDist_le_infDist_add_dist (x := x) (y := x₀) (s := s)
  rw [mem_ball] at hx
  linarith

end Helpers

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

namespace IsMinimaxProblem
variable {L : E → P → ℝ} {X : Set E} {Y : Set P}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem mono (h : IsMinimaxProblem L X Y) {X' : Set E} {Y' : Set P} (hX' : X' ⊆ X)
    (hY' : Y' ⊆ Y) (hX'n : X'.Nonempty) (hX'c : IsClosed X') (hX'v : Convex ℝ X')
    (hY'n : Y'.Nonempty) (hY'c : IsClosed Y') (hY'v : Convex ℝ Y') : IsMinimaxProblem L X' Y' :=
  ⟨hX'n, hX'c, hX'v, hY'n, hY'c, hY'v, h.continuousOn.mono (prod_mono hX' hY'),
    fun y hy ↦ (h.convexOn_left y (hY' hy)).subset hX' hX'v,
    fun x hx ↦ (h.concaveOn_right x (hX' hx)).subset hY' hY'v⟩

theorem iInf_eq_iSup_of_nonempty (h : IsMinimaxProblem L X Y)
    (hne : (argminimaxOn L X Y).Nonempty) :
    (⨅ x, minimaxPrimal L X Y x) = ⨆ y, minimaxDual L X Y y := by
  obtain ⟨⟨x₀, y₀⟩, hs⟩ := hne
  have hm := hs
  rw [h.argminimaxOn_eq, ← h.lagrangian_eq] at hm
  obtain ⟨-, -, he⟩ := (h.isDualizingParameterization.minimax_relations x₀ y₀).1.mpr hm
  rwa [h.dualObjective_eq] at he

theorem apply_eq_of_mem (h : IsMinimaxProblem L X Y) {p q : E × P}
    (hp : p ∈ argminimaxOn L X Y) (hq : q ∈ argminimaxOn L X Y) : L p.1 p.2 = L q.1 q.2 := by
  have h₁ := (h.saddle_value (x₀ := p.1) (y₀ := p.2) hp).1
  have h₂ := (h.saddle_value (x₀ := q.1) (y₀ := q.2) hq).1
  exact EReal.coe_injective (h₁.trans h₂.symm)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- A saddle point relative to `X' × Y'` whose coordinates have relative
neighborhoods inside `X'` and `Y'` is a saddle point relative to `X × Y`. -/
theorem mem_argminimaxOn_of_local (h : IsMinimaxProblem L X Y) {X' : Set E} {Y' : Set P}
    {x₀ : E} {y₀ : P} (hs : (x₀, y₀) ∈ argminimaxOn L X' Y') (hX' : X' ⊆ X) (hY' : Y' ⊆ Y)
    {r : ℝ} (hr : 0 < r) (hxn : ball x₀ r ∩ X ⊆ X') (hyn : ball y₀ r ∩ Y ⊆ Y') :
    (x₀, y₀) ∈ argminimaxOn L X Y := by
  obtain ⟨hx₀, hy₀, hsad⟩ := hs
  have hx₀X := hX' hx₀
  have hy₀Y := hY' hy₀
  have hmin : IsMinOn (fun x ↦ L x y₀) X x₀ := by
    refine IsMinOn.of_isLocalMinOn_of_convexOn hx₀X ?_ (h.convexOn_left y₀ hy₀Y)
    exact Filter.mem_of_superset (inter_mem_nhdsWithin X (ball_mem_nhds x₀ hr))
      fun x hx ↦ (hsad x (hxn ⟨hx.2, hx.1⟩) y₀ hy₀).1
  have hmax : IsMaxOn (fun y ↦ L x₀ y) Y y₀ := by
    refine IsMaxOn.of_isLocalMaxOn_of_concaveOn hy₀Y ?_ (h.concaveOn_right x₀ hx₀X)
    exact Filter.mem_of_superset (inter_mem_nhdsWithin Y (ball_mem_nhds y₀ hr))
      fun y hy ↦ (hsad x₀ hx₀ y (hyn ⟨hy.2, hy.1⟩)).2
  exact ⟨hx₀X, hy₀Y, fun x hx y hy ↦ ⟨isMinOn_iff.mp hmin x hx, isMaxOn_iff.mp hmax y hy⟩⟩

/-- Restricted saddle points are global once the global saddle set sits inside
the restriction with relative neighborhoods: the step in **11.53** at `t = 0`. -/
theorem restricted_argminimaxOn_subset (h : IsMinimaxProblem L X Y)
    (hS : (argminimaxOn L X Y).Nonempty) {X' : Set E} {Y' : Set P} (hX' : X' ⊆ X) (hY' : Y' ⊆ Y)
    (hX'c : IsClosed X') (hX'v : Convex ℝ X') (hY'c : IsClosed Y') (hY'v : Convex ℝ Y')
    (hsub : argminimaxOn L X Y ⊆ X' ×ˢ Y')
    (hloc : ∀ p ∈ argminimaxOn L X Y, ∃ r > 0, ball p.1 r ∩ X ⊆ X' ∧ ball p.2 r ∩ Y ⊆ Y') :
    argminimaxOn L X' Y' ⊆ argminimaxOn L X Y := by
  obtain ⟨q, hq⟩ := hS
  have hq' : q ∈ argminimaxOn L X' Y' :=
    ⟨(hsub hq).1, (hsub hq).2, fun x hx y hy ↦ hq.2.2 x (hX' hx) y (hY' hy)⟩
  have h' := h.mono hX' hY' ⟨_, (hsub hq).1⟩ hX'c hX'v ⟨_, (hsub hq).2⟩ hY'c hY'v
  have hglob := h.argminimaxOn_eq_prod (h.iInf_eq_iSup_of_nonempty ⟨q, hq⟩)
  have hres := h'.argminimaxOn_eq_prod (h'.iInf_eq_iSup_of_nonempty ⟨q, hq'⟩)
  obtain ⟨r, hr, hrx, hry⟩ := hloc q hq
  intro p hp
  have hp' : p ∈ argmin (minimaxPrimal L X' Y') ×ˢ argmax (minimaxDual L X' Y') := hres ▸ hp
  have hq'' : q ∈ argmin (minimaxPrimal L X' Y') ×ˢ argmax (minimaxDual L X' Y') := hres ▸ hq'
  have h₁ : (p.1, q.2) ∈ argminimaxOn L X' Y' := by rw [hres]; exact ⟨hp'.1, hq''.2⟩
  have h₂ : (q.1, p.2) ∈ argminimaxOn L X' Y' := by rw [hres]; exact ⟨hq''.1, hp'.2⟩
  have hv₁ : L p.1 q.2 = L q.1 q.2 := h'.apply_eq_of_mem h₁ hq'
  have hv₂ : L q.1 p.2 = L q.1 q.2 := h'.apply_eq_of_mem h₂ hq'
  have g₁ : (p.1, q.2) ∈ argminimaxOn L X Y := by
    refine ⟨hX' h₁.1, hY' h₁.2.1, fun x hx y hy ↦ ⟨?_, ?_⟩⟩
    · show L p.1 q.2 ≤ L x q.2
      rw [hv₁]
      exact (hq.2.2 x hx q.2 hq.2.1).1
    · show L p.1 y ≤ L p.1 q.2
      have hmax : IsMaxOn (fun y ↦ L p.1 y) Y q.2 := by
        refine IsMaxOn.of_isLocalMaxOn_of_concaveOn hq.2.1 ?_ (h.concaveOn_right p.1 (hX' h₁.1))
        exact Filter.mem_of_superset (inter_mem_nhdsWithin Y (ball_mem_nhds q.2 hr))
          fun y hy ↦ (h₁.2.2 p.1 h₁.1 y (hry ⟨hy.2, hy.1⟩)).2
      exact isMaxOn_iff.mp hmax y hy
  have g₂ : (q.1, p.2) ∈ argminimaxOn L X Y := by
    refine ⟨hX' h₂.1, hY' h₂.2.1, fun x hx y hy ↦ ⟨?_, ?_⟩⟩
    · show L q.1 p.2 ≤ L x p.2
      have hmin : IsMinOn (fun x ↦ L x p.2) X q.1 := by
        refine IsMinOn.of_isLocalMinOn_of_convexOn hq.1 ?_ (h.convexOn_left p.2 (hY' h₂.2.1))
        exact Filter.mem_of_superset (inter_mem_nhdsWithin X (ball_mem_nhds q.1 hr))
          fun x hx ↦ (h₂.2.2 x (hrx ⟨hx.2, hx.1⟩) p.2 h₂.2.1).1
      exact isMinOn_iff.mp hmin x hx
    · show L q.1 y ≤ L q.1 p.2
      rw [hv₂]
      exact (hq.2.2 q.1 hq.1 y hy).2
  rw [hglob] at g₁ g₂ ⊢
  exact ⟨g₁.1, g₂.2⟩

end IsMinimaxProblem

/-- The standing assumptions of **Theorem 11.53**: nonempty closed convex `X`, `Y`,
and `L : [0,T] × X × Y → ℝ` continuous, convex in `x` and concave in `y`. -/
structure IsSaddlePerturbation (L : ℝ → E → P → ℝ) (T : ℝ) (X : Set E) (Y : Set P) : Prop where
  pos : 0 < T
  nonempty_left : X.Nonempty
  isClosed_left : IsClosed X
  convex_left : Convex ℝ X
  nonempty_right : Y.Nonempty
  isClosed_right : IsClosed Y
  convex_right : Convex ℝ Y
  continuousOn : ContinuousOn (fun p : ℝ × E × P ↦ L p.1 p.2.1 p.2.2) (Icc 0 T ×ˢ (X ×ˢ Y))
  convexOn_left : ∀ t ∈ Icc 0 T, ∀ y ∈ Y, ConvexOn ℝ X (fun x ↦ L t x y)
  concaveOn_right : ∀ t ∈ Icc 0 T, ∀ x ∈ X, ConcaveOn ℝ Y (fun y ↦ L t x y)

/-- The saddle value `λ(t) = minimax_{X,Y} L(t,·,·)`, read off as `inf φ_t`. -/
def saddleValue (L : ℝ → E → P → ℝ) (X : Set E) (Y : Set P) (t : ℝ) : ℝ :=
  (⨅ x, minimaxPrimal (L t) X Y x).toReal

namespace IsSaddlePerturbation
variable {L : ℝ → E → P → ℝ} {T : ℝ} {X : Set E} {Y : Set P}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem minimax (h : IsSaddlePerturbation L T X Y) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IsMinimaxProblem (L t) X Y :=
  ⟨h.nonempty_left, h.isClosed_left, h.convex_left, h.nonempty_right, h.isClosed_right,
    h.convex_right, h.continuousOn.comp
      (continuous_const.prodMk continuous_id : Continuous fun p : E × P ↦ (t, p)).continuousOn
      fun _ hp ↦ ⟨ht, hp⟩, h.convexOn_left t ht, h.concaveOn_right t ht⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem tendsto_apply (h : IsSaddlePerturbation L T X Y) {ts : ℕ → ℝ} {xs : ℕ → E} {ys : ℕ → P}
    {t : ℝ} {x : E} {y : P} (hev : ∀ᶠ n in atTop, ts n ∈ Icc 0 T ∧ xs n ∈ X ∧ ys n ∈ Y)
    (htm : t ∈ Icc 0 T) (hxm : x ∈ X) (hym : y ∈ Y) (ht : Tendsto ts atTop (𝓝 t))
    (hx : Tendsto xs atTop (𝓝 x)) (hy : Tendsto ys atTop (𝓝 y)) :
    Tendsto (fun n ↦ L (ts n) (xs n) (ys n)) atTop (𝓝 (L t x y)) := by
  have hc := (h.continuousOn (t, x, y) ⟨htm, hxm, hym⟩).tendsto
  exact hc.comp (tendsto_nhdsWithin_iff.mpr ⟨ht.prodMk_nhds (hx.prodMk_nhds hy),
    hev.mono fun n hn ↦ ⟨hn.1, hn.2.1, hn.2.2⟩⟩)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- Limits of saddle points are saddle points (the closed-graph step of 11.53). -/
theorem mem_argminimaxOn_of_tendsto (h : IsSaddlePerturbation L T X Y) {X' : Set E}
    {Y' : Set P} (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) (hX'c : IsClosed X') (hY'c : IsClosed Y')
    {ts : ℕ → ℝ} {ps : ℕ → E × P} {t : ℝ} {p : E × P} (hts : ∀ᶠ n in atTop, ts n ∈ Icc 0 T)
    (hps : ∀ᶠ n in atTop, ps n ∈ argminimaxOn (L (ts n)) X' Y') (htm : t ∈ Icc 0 T)
    (ht : Tendsto ts atTop (𝓝 t)) (hp : Tendsto ps atTop (𝓝 p)) :
    p ∈ argminimaxOn (L t) X' Y' := by
  have hx : Tendsto (fun n ↦ (ps n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hp
  have hy : Tendsto (fun n ↦ (ps n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hp
  have hpx : p.1 ∈ X' := hX'c.mem_of_tendsto hx (hps.mono fun n hn ↦ hn.1)
  have hpy : p.2 ∈ Y' := hY'c.mem_of_tendsto hy (hps.mono fun n hn ↦ hn.2.1)
  refine ⟨hpx, hpy, fun x hx' y hy' ↦ ⟨?_, ?_⟩⟩
  · refine le_of_tendsto_of_tendsto (h.tendsto_apply ?_ htm (hX' hpx) (hY' hpy) ht hx hy)
      (h.tendsto_apply ?_ htm (hX' hx') (hY' hpy) ht tendsto_const_nhds hy) ?_
    · filter_upwards [hts, hps] with n hn hpn using ⟨hn, hX' hpn.1, hY' hpn.2.1⟩
    · filter_upwards [hts, hps] with n hn hpn using ⟨hn, hX' hx', hY' hpn.2.1⟩
    · filter_upwards [hps] with n hpn using (hpn.2.2 x hx' (ps n).2 hpn.2.1).1
  · refine le_of_tendsto_of_tendsto (h.tendsto_apply ?_ htm (hX' hpx) (hY' hy') ht hx
      tendsto_const_nhds) (h.tendsto_apply ?_ htm (hX' hpx) (hY' hpy) ht hx hy) ?_
    · filter_upwards [hts, hps] with n hn hpn using ⟨hn, hX' hpn.1, hY' hy'⟩
    · filter_upwards [hts, hps] with n hn hpn using ⟨hn, hX' hpn.1, hY' hpn.2.1⟩
    · filter_upwards [hps] with n hpn using (hpn.2.2 (ps n).1 hpn.1 y hy').2

theorem apply_eq_saddleValue (h : IsSaddlePerturbation L T X Y) {t : ℝ} (ht : t ∈ Icc 0 T)
    {p : E × P} (hp : p ∈ argminimaxOn (L t) X Y) : L t p.1 p.2 = saddleValue L X Y t := by
  have := ((h.minimax ht).saddle_value (x₀ := p.1) (y₀ := p.2) hp).1
  rw [saddleValue, ← this, EReal.toReal_coe]

/-- **Theorem 11.53**, first part: if the saddle-point set at `t = 0` is nonempty and
bounded, then on some `[0,ε]` the saddle-point sets are nonempty and bounded, the
mapping `t ↦ argminimax L(t,·,·)` is osc and locally bounded at `0` relative to
`[0,ε]`, and the saddle value `λ(t)` converges to `λ(0)`. -/
theorem golshtein_saddle_sets (h : IsSaddlePerturbation L T X Y)
    (hS0 : (argminimaxOn (L 0) X Y).Nonempty) (hS0b : IsBounded (argminimaxOn (L 0) X Y)) :
    ∃ ε > 0, ε ≤ T ∧
      (∀ t ∈ Icc 0 ε, (argminimaxOn (L t) X Y).Nonempty ∧ IsBounded (argminimaxOn (L t) X Y)) ∧
      SvOscWithinAt (fun t ↦ argminimaxOn (L t) X Y) (Icc 0 ε) 0 ∧
      SvLocallyBoundedWithinAt (fun t ↦ argminimaxOn (L t) X Y) (Icc 0 ε) 0 ∧
      Tendsto (saddleValue L X Y) (𝓝[Icc 0 ε] 0) (𝓝 (saddleValue L X Y 0)) := by
  have h0m : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, h.pos.le⟩
  have h0 := h.minimax h0m
  set X₀ := argmin (minimaxPrimal (L 0) X Y)
  set Y₀ := argmax (minimaxDual (L 0) X Y)
  have hS0eq : argminimaxOn (L 0) X Y = X₀ ×ˢ Y₀ :=
    h0.argminimaxOn_eq_prod (h0.iInf_eq_iSup_of_nonempty hS0)
  obtain ⟨q, hq⟩ := hS0
  have hq' : q ∈ X₀ ×ˢ Y₀ := hS0eq ▸ hq
  have hX₀n : X₀.Nonempty := ⟨q.1, hq'.1⟩
  have hY₀n : Y₀.Nonempty := ⟨q.2, hq'.2⟩
  have hb := (isBounded_prod_of_nonempty ⟨q, hq'⟩).mp (hS0eq ▸ hS0b)
  have hX₀X : X₀ ⊆ X := fun x hx ↦
    (show (x, q.2) ∈ argminimaxOn (L 0) X Y by rw [hS0eq]; exact ⟨hx, hq'.2⟩).1
  have hY₀Y : Y₀ ⊆ Y := fun y hy ↦
    (show (q.1, y) ∈ argminimaxOn (L 0) X Y by rw [hS0eq]; exact ⟨hq'.1, hy⟩).2.1
  have hS0v := h0.isClosed_convex_argminimaxOn.2
  have hX₀v : Convex ℝ X₀ := by
    intro x₁ hx₁ x₂ hx₂ a b ha hb' hab
    have h₁ : (x₁, q.2) ∈ argminimaxOn (L 0) X Y := by rw [hS0eq]; exact ⟨hx₁, hq'.2⟩
    have h₂ : (x₂, q.2) ∈ argminimaxOn (L 0) X Y := by rw [hS0eq]; exact ⟨hx₂, hq'.2⟩
    have hc := hS0v h₁ h₂ ha hb' hab
    rw [hS0eq, Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at hc
    exact hc.1
  have hY₀v : Convex ℝ Y₀ := by
    intro y₁ hy₁ y₂ hy₂ a b ha hb' hab
    have h₁ : (q.1, y₁) ∈ argminimaxOn (L 0) X Y := by rw [hS0eq]; exact ⟨hq'.1, hy₁⟩
    have h₂ : (q.1, y₂) ∈ argminimaxOn (L 0) X Y := by rw [hS0eq]; exact ⟨hq'.1, hy₂⟩
    have hc := hS0v h₁ h₂ ha hb' hab
    rw [hS0eq, Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at hc
    exact hc.2
  -- the restricted problems on `X_δ × Y_δ`, with `δ = 1`
  set δ : ℝ := 1
  have hδ : (0 : ℝ) < δ := one_pos
  set Xδ := X ∩ cthickening δ X₀
  set Yδ := Y ∩ cthickening δ Y₀
  have hXδX : Xδ ⊆ X := inter_subset_left
  have hYδY : Yδ ⊆ Y := inter_subset_left
  have hX₀δ : X₀ ⊆ Xδ := fun x hx ↦ ⟨hX₀X hx, self_subset_cthickening _ hx⟩
  have hY₀δ : Y₀ ⊆ Yδ := fun y hy ↦ ⟨hY₀Y hy, self_subset_cthickening _ hy⟩
  have hXδc : IsClosed Xδ := h.isClosed_left.inter isClosed_cthickening
  have hYδc : IsClosed Yδ := h.isClosed_right.inter isClosed_cthickening
  have hXδv : Convex ℝ Xδ := h.convex_left.inter (hX₀v.cthickening δ)
  have hYδv : Convex ℝ Yδ := h.convex_right.inter (hY₀v.cthickening δ)
  have hXδb : IsBounded Xδ := hb.1.cthickening.subset inter_subset_right
  have hYδb : IsBounded Yδ := hb.2.cthickening.subset inter_subset_right
  have hXδk : IsCompact Xδ := Metric.isCompact_of_isClosed_isBounded hXδc hXδb
  have hYδk : IsCompact Yδ := Metric.isCompact_of_isClosed_isBounded hYδc hYδb
  have hres (t : ℝ) (ht : t ∈ Icc 0 T) : IsMinimaxProblem (L t) Xδ Yδ :=
    (h.minimax ht).mono hXδX hYδY (hX₀n.mono hX₀δ) hXδc hXδv (hY₀n.mono hY₀δ) hYδc hYδv
  have hresne (t : ℝ) (ht : t ∈ Icc 0 T) : (argminimaxOn (L t) Xδ Yδ).Nonempty :=
    ((hres t ht).argminimaxOn_nonempty_bounded_of_bounded hXδb hYδb).2.2.1
  have hmemδ {x : E} (hxX : x ∈ X) (hx : infDist x X₀ ≤ δ) : x ∈ Xδ :=
    ⟨hxX, (mem_cthickening_iff_infDist_le_of_nonempty hX₀n hδ.le x).mpr hx⟩
  have hmemδ' {y : P} (hyY : y ∈ Y) (hy : infDist y Y₀ ≤ δ) : y ∈ Yδ :=
    ⟨hyY, (mem_cthickening_iff_infDist_le_of_nonempty hY₀n hδ.le y).mpr hy⟩
  -- at `t = 0`, restricted saddle points are global
  have hA0 : argminimaxOn (L 0) Xδ Yδ ⊆ X₀ ×ˢ Y₀ := by
    rw [← hS0eq]
    refine h0.restricted_argminimaxOn_subset ⟨q, hq⟩ hXδX hYδY hXδc hXδv hYδc hYδv ?_ ?_
    · rw [hS0eq]
      exact prod_mono hX₀δ hY₀δ
    · intro p hp
      rw [hS0eq] at hp
      refine ⟨δ, hδ, fun x hx ↦ ⟨hx.2, ?_⟩, fun y hy ↦ ⟨hy.2, ?_⟩⟩
      · have h0d : infDist p.1 X₀ = 0 := infDist_zero_of_mem hp.1
        exact ball_subset_cthickening_of_infDist_lt hX₀n (by rw [h0d]; exact hδ)
          (by rw [h0d, sub_zero]; exact hx.1)
      · have h0d : infDist p.2 Y₀ = 0 := infDist_zero_of_mem hp.2
        exact ball_subset_cthickening_of_infDist_lt hY₀n (by rw [h0d]; exact hδ)
          (by rw [h0d, sub_zero]; exact hy.1)
  -- for small `t`, restricted saddle points stay strictly inside the thickening
  set Bad : Set (E × P) := {p | δ ≤ infDist p.1 X₀ ∨ δ ≤ infDist p.2 Y₀}
  have hBad : IsClosed Bad :=
    (isClosed_le continuous_const ((continuous_infDist_pt X₀).comp continuous_fst)).union
      (isClosed_le continuous_const ((continuous_infDist_pt Y₀).comp continuous_snd))
  have hA : ∃ ε, 0 < ε ∧ ε ≤ T ∧ ∀ t ∈ Icc 0 ε, ∀ p ∈ argminimaxOn (L t) Xδ Yδ, p ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    choose t ht p hp hbad using fun n : ℕ ↦
      hcon (min T (1 / ((n : ℝ) + 1))) (lt_min h.pos (by positivity)) (min_le_left _ _)
    have htT (n : ℕ) : t n ∈ Icc 0 T := ⟨(ht n).1, (ht n).2.trans (min_le_left _ _)⟩
    have htlim : Tendsto t atTop (𝓝 0) := by
      refine squeeze_zero (fun n ↦ (ht n).1) (fun n ↦ (ht n).2.trans (min_le_right _ _)) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨p', -, φ, hφ, hlim⟩ := (hXδk.prod hYδk).tendsto_subseq
      (fun n ↦ (⟨(hp n).1, (hp n).2.1⟩ : p n ∈ Xδ ×ˢ Yδ))
    have hmem := h.mem_argminimaxOn_of_tendsto hXδX hYδY hXδc hYδc
      (Eventually.of_forall fun n ↦ htT (φ n)) (Eventually.of_forall fun n ↦ hp (φ n)) h0m
      (htlim.comp hφ.tendsto_atTop) hlim
    have hb' : p' ∈ Bad := hBad.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ hbad (φ n))
    have hin := hA0 hmem
    rcases hb' with hb₁ | hb₂
    · rw [infDist_zero_of_mem hin.1] at hb₁
      linarith
    · rw [infDist_zero_of_mem hin.2] at hb₂
      linarith
  obtain ⟨ε, hε, hεT, hgood⟩ := hA
  have hεT' {t : ℝ} (ht : t ∈ Icc 0 ε) : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hεT⟩
  have hgood' {t : ℝ} (ht : t ∈ Icc 0 ε) {p : E × P} (hp : p ∈ argminimaxOn (L t) Xδ Yδ) :
      infDist p.1 X₀ < δ ∧ infDist p.2 Y₀ < δ := by
    have := hgood t ht p hp
    simp only [Bad, mem_setOf_eq, not_or, not_le] at this
    exact this
  -- interior restricted saddle points are global saddle points
  have hB {t : ℝ} (ht : t ∈ Icc 0 ε) : argminimaxOn (L t) Xδ Yδ ⊆ argminimaxOn (L t) X Y := by
    intro p hp
    obtain ⟨g₁, g₂⟩ := hgood' ht hp
    have hr : 0 < min (δ - infDist p.1 X₀) (δ - infDist p.2 Y₀) := lt_min (by linarith) (by linarith)
    refine (h.minimax (hεT' ht)).mem_argminimaxOn_of_local hp hXδX hYδY hr ?_ ?_
    · intro x hx
      exact ⟨hx.2, ball_subset_cthickening_of_infDist_lt hX₀n g₁
        (ball_subset_ball (min_le_left _ _) hx.1)⟩
    · intro y hy
      exact ⟨hy.2, ball_subset_cthickening_of_infDist_lt hY₀n g₂
        (ball_subset_ball (min_le_right _ _) hy.1)⟩
  -- all saddle points lie in `X_δ × Y_δ`
  have hC {t : ℝ} (ht : t ∈ Icc 0 ε) : argminimaxOn (L t) X Y ⊆ Xδ ×ˢ Yδ := by
    intro p hp
    have hm := h.minimax (hεT' ht)
    obtain ⟨p₀, hp₀⟩ := hresne t (hεT' ht)
    have hp₀g := hB ht hp₀
    obtain ⟨g₀₁, g₀₂⟩ := hgood' ht hp₀
    have hconv := hm.isClosed_convex_argminimaxOn.2
    have hprod := hm.argminimaxOn_eq_prod (hm.iInf_eq_iSup_of_nonempty ⟨p₀, hp₀g⟩)
    have hpP : p ∈ argmin (minimaxPrimal (L t) X Y) ×ˢ argmax (minimaxDual (L t) X Y) :=
      hprod ▸ hp
    have hp₀P : p₀ ∈ argmin (minimaxPrimal (L t) X Y) ×ˢ argmax (minimaxDual (L t) X Y) :=
      hprod ▸ hp₀g
    have hx : infDist p.1 X₀ ≤ δ := by
      by_contra hgt
      push_neg at hgt
      have hq₁ : (p.1, p₀.2) ∈ argminimaxOn (L t) X Y := by
        rw [hprod]
        exact ⟨hpP.1, hp₀P.2⟩
      have hcont : ContinuousOn (fun s : ℝ ↦ infDist (p₀.1 + s • (p.1 - p₀.1)) X₀) (Icc 0 1) :=
        ((continuous_infDist_pt X₀).comp (by fun_prop)).continuousOn
      obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc zero_le_one hcont
        (show δ ∈ Icc (infDist (p₀.1 + (0 : ℝ) • (p.1 - p₀.1)) X₀)
            (infDist (p₀.1 + (1 : ℝ) • (p.1 - p₀.1)) X₀) by
          simp only [zero_smul, add_zero, one_smul, add_sub_cancel]
          exact ⟨g₀₁.le, hgt.le⟩)
      have hz : (p₀.1 + s • (p.1 - p₀.1), p₀.2) ∈ argminimaxOn (L t) X Y := by
        have hc := hconv hp₀g hq₁ (sub_nonneg.mpr hs.2) hs.1 (by ring)
        have he : (1 - s) • p₀ + s • (p.1, p₀.2) = (p₀.1 + s • (p.1 - p₀.1), p₀.2) := by
          ext <;> simp <;> module
        rwa [he] at hc
      have hzr : (p₀.1 + s • (p.1 - p₀.1), p₀.2) ∈ argminimaxOn (L t) Xδ Yδ :=
        ⟨hmemδ hz.1 hseq.le, (hp₀).2.1, fun x hx y hy ↦ hz.2.2 x hx.1 y hy.1⟩
      have hlt := (hgood' ht hzr).1
      dsimp only at hlt
      exact (ne_of_lt hlt) hseq
    have hy : infDist p.2 Y₀ ≤ δ := by
      by_contra hgt
      push_neg at hgt
      have hq₂ : (p₀.1, p.2) ∈ argminimaxOn (L t) X Y := by
        rw [hprod]
        exact ⟨hp₀P.1, hpP.2⟩
      have hcont : ContinuousOn (fun s : ℝ ↦ infDist (p₀.2 + s • (p.2 - p₀.2)) Y₀) (Icc 0 1) :=
        ((continuous_infDist_pt Y₀).comp (by fun_prop)).continuousOn
      obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc zero_le_one hcont
        (show δ ∈ Icc (infDist (p₀.2 + (0 : ℝ) • (p.2 - p₀.2)) Y₀)
            (infDist (p₀.2 + (1 : ℝ) • (p.2 - p₀.2)) Y₀) by
          simp only [zero_smul, add_zero, one_smul, add_sub_cancel]
          exact ⟨g₀₂.le, hgt.le⟩)
      have hz : (p₀.1, p₀.2 + s • (p.2 - p₀.2)) ∈ argminimaxOn (L t) X Y := by
        have hc := hconv hp₀g hq₂ (sub_nonneg.mpr hs.2) hs.1 (by ring)
        have he : (1 - s) • p₀ + s • (p₀.1, p.2) = (p₀.1, p₀.2 + s • (p.2 - p₀.2)) := by
          ext <;> simp <;> module
        rwa [he] at hc
      have hzr : (p₀.1, p₀.2 + s • (p.2 - p₀.2)) ∈ argminimaxOn (L t) Xδ Yδ :=
        ⟨(hp₀).1, hmemδ' hz.2.1 hseq.le, fun x hx y hy ↦ hz.2.2 x hx.1 y hy.1⟩
      have hlt := (hgood' ht hzr).2
      dsimp only at hlt
      exact (ne_of_lt hlt) hseq
    exact ⟨hmemδ hp.1 hx, hmemδ' hp.2.1 hy⟩
  have hne {t : ℝ} (ht : t ∈ Icc 0 ε) : (argminimaxOn (L t) X Y).Nonempty :=
    (hresne t (hεT' ht)).mono (hB ht)
  refine ⟨ε, hε, hεT, fun t ht ↦ ⟨hne ht, (hXδb.prod hYδb).subset (hC ht)⟩, ?_, ?_, ?_⟩
  · intro v hv
    rw [svOuterLimitWithin, mem_outerSetLimitAlong_iff_exists_seq] at hv
    obtain ⟨ts, vs, hts, hvs, hvlim⟩ := hv
    have hts' := tendsto_nhdsWithin_iff.mp hts
    exact h.mem_argminimaxOn_of_tendsto subset_rfl subset_rfl h.isClosed_left h.isClosed_right
      (hts'.2.mono fun n hn ↦ hεT' hn) (Eventually.of_forall hvs) h0m hts'.1 hvlim
  · refine ⟨univ, univ_mem, (hXδb.prod hYδb).subset ?_⟩
    intro v hv
    obtain ⟨t, ht, hvt⟩ := mem_svImage.mp hv
    exact hC ht.1 hvt
  · refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    have hns' := tendsto_nhdsWithin_iff.mp hns
    obtain ⟨pd, hpd⟩ := hresne 0 h0m
    let ps : ℕ → E × P := fun n ↦
      if hn : ns n ∈ Icc 0 ε then (hne hn).some else pd
    have hpsK (n : ℕ) : ps n ∈ Xδ ×ˢ Yδ := by
      by_cases hn : ns n ∈ Icc 0 ε
      · simp only [ps, hn, dite_true]
        exact hC hn (hne hn).some_mem
      · simp only [ps, hn, dite_false]
        exact ⟨hpd.1, hpd.2.1⟩
    obtain ⟨p', -, φ, hφ, hlim⟩ := (hXδk.prod hYδk).tendsto_subseq hpsK
    refine ⟨φ, ?_⟩
    have hev : ∀ᶠ n in atTop, ns (φ n) ∈ Icc 0 ε := hφ.tendsto_atTop.eventually hns'.2
    have hpsS : ∀ᶠ n in atTop, ps (φ n) ∈ argminimaxOn (L (ns (φ n))) X Y := by
      filter_upwards [hev] with n hn
      simp only [ps, hn, dite_true]
      exact (hne hn).some_mem
    have htlim : Tendsto (fun n ↦ ns (φ n)) atTop (𝓝 0) := hns'.1.comp hφ.tendsto_atTop
    have hmem := h.mem_argminimaxOn_of_tendsto subset_rfl subset_rfl h.isClosed_left
      h.isClosed_right (hev.mono fun n hn ↦ hεT' hn) hpsS h0m htlim hlim
    have hL := h.tendsto_apply (ts := fun n ↦ ns (φ n)) (xs := fun n ↦ (ps (φ n)).1)
      (ys := fun n ↦ (ps (φ n)).2)
      ((hev.and hpsS).mono fun n hn ↦ ⟨hεT' hn.1, hn.2.1, hn.2.2.1⟩) h0m hmem.1 hmem.2.1
      htlim ((continuous_fst.tendsto p').comp hlim) ((continuous_snd.tendsto p').comp hlim)
    rw [h.apply_eq_saddleValue h0m hmem] at hL
    refine hL.congr' ?_
    filter_upwards [hev, hpsS] with n hn hps
    exact h.apply_eq_saddleValue (hεT' hn) hps

/-- The structure of the saddle set at `t = 0` used in the second part of 11.53. -/
theorem zero_structure (h : IsSaddlePerturbation L T X Y)
    (hS0 : (argminimaxOn (L 0) X Y).Nonempty) (hS0b : IsBounded (argminimaxOn (L 0) X Y)) :
    let X₀ := argmin (minimaxPrimal (L 0) X Y)
    let Y₀ := argmax (minimaxDual (L 0) X Y)
    argminimaxOn (L 0) X Y = X₀ ×ˢ Y₀ ∧ X₀.Nonempty ∧ Y₀.Nonempty ∧ IsBounded X₀ ∧
      IsBounded Y₀ ∧ IsClosed X₀ ∧ IsClosed Y₀ ∧ Convex ℝ X₀ ∧ Convex ℝ Y₀ ∧ X₀ ⊆ X ∧ Y₀ ⊆ Y ∧
      ∀ x ∈ X₀, ∀ y ∈ Y₀, L 0 x y = saddleValue L X Y 0 := by
  intro X₀ Y₀
  have h0m : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, h.pos.le⟩
  have h0 := h.minimax h0m
  have hS0eq : argminimaxOn (L 0) X Y = X₀ ×ˢ Y₀ :=
    h0.argminimaxOn_eq_prod (h0.iInf_eq_iSup_of_nonempty hS0)
  obtain ⟨q, hq⟩ := hS0
  have hq' : q ∈ X₀ ×ˢ Y₀ := hS0eq ▸ hq
  have hb := (isBounded_prod_of_nonempty ⟨q, hq'⟩).mp (hS0eq ▸ hS0b)
  have hcc := h0.isClosed_convex_argminimaxOn
  have hslx : X₀ = (fun x : E ↦ (x, q.2)) ⁻¹' argminimaxOn (L 0) X Y := by
    ext x
    simp only [mem_preimage, hS0eq, mem_prod]
    exact ⟨fun hx ↦ ⟨hx, hq'.2⟩, fun hx ↦ hx.1⟩
  have hsly : Y₀ = (fun y : P ↦ (q.1, y)) ⁻¹' argminimaxOn (L 0) X Y := by
    ext y
    simp only [mem_preimage, hS0eq, mem_prod]
    exact ⟨fun hy ↦ ⟨hq'.1, hy⟩, fun hy ↦ hy.2⟩
  have hXv : Convex ℝ X₀ := by
    intro x₁ hx₁ x₂ hx₂ a b ha hb' hab
    have h₁ : (x₁, q.2) ∈ argminimaxOn (L 0) X Y := by rw [hS0eq]; exact ⟨hx₁, hq'.2⟩
    have h₂ : (x₂, q.2) ∈ argminimaxOn (L 0) X Y := by rw [hS0eq]; exact ⟨hx₂, hq'.2⟩
    have hc := hcc.2 h₁ h₂ ha hb' hab
    rw [hS0eq, Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at hc
    exact hc.1
  have hYv : Convex ℝ Y₀ := by
    intro y₁ hy₁ y₂ hy₂ a b ha hb' hab
    have h₁ : (q.1, y₁) ∈ argminimaxOn (L 0) X Y := by rw [hS0eq]; exact ⟨hq'.1, hy₁⟩
    have h₂ : (q.1, y₂) ∈ argminimaxOn (L 0) X Y := by rw [hS0eq]; exact ⟨hq'.1, hy₂⟩
    have hc := hcc.2 h₁ h₂ ha hb' hab
    rw [hS0eq, Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul] at hc
    exact hc.2
  refine ⟨hS0eq, ⟨q.1, hq'.1⟩, ⟨q.2, hq'.2⟩, hb.1, hb.2, ?_, ?_, hXv, hYv, ?_, ?_, ?_⟩
  · rw [hslx]
    exact hcc.1.preimage (continuous_id.prodMk continuous_const)
  · rw [hsly]
    exact hcc.1.preimage (continuous_const.prodMk continuous_id)
  · intro x hx
    exact (show (x, q.2) ∈ argminimaxOn (L 0) X Y by rw [hS0eq]; exact ⟨hx, hq'.2⟩).1
  · intro y hy
    exact (show (q.1, y) ∈ argminimaxOn (L 0) X Y by rw [hS0eq]; exact ⟨hq'.1, hy⟩).2.1
  · intro x hx y hy
    exact h.apply_eq_saddleValue h0m (p := (x, y)) (by rw [hS0eq]; exact ⟨hx, hy⟩)

/-- **Theorem 11.53**, second part (Golshtein): if the limit
`L₊(0,x,y) = lim_{t↘0, x'→_X x, y'→_Y y} [L(t,x',y') - L(0,x',y')]/t` exists for all
`(x,y) ∈ X₀ × Y₀`, then `L₊(0,·,·)` is continuous on `X₀ × Y₀`, convex in `x ∈ X₀` and
concave in `y ∈ Y₀`, it has saddle points on `X₀ × Y₀`, and the right derivative
`λ₊(0)` exists and equals `minimax_{X₀,Y₀} L₊(0,·,·)`. -/
theorem golshtein_derivative (h : IsSaddlePerturbation L T X Y)
    (hS0 : (argminimaxOn (L 0) X Y).Nonempty) (hS0b : IsBounded (argminimaxOn (L 0) X Y))
    {Lp : E → P → ℝ}
    (hLp : ∀ x ∈ argmin (minimaxPrimal (L 0) X Y), ∀ y ∈ argmax (minimaxDual (L 0) X Y),
      Tendsto (fun p : ℝ × (E × P) ↦ (L p.1 p.2.1 p.2.2 - L 0 p.2.1 p.2.2) / p.1)
        (𝓝[>] 0 ×ˢ 𝓝[X ×ˢ Y] (x, y)) (𝓝 (Lp x y))) :
    ContinuousOn (fun p : E × P ↦ Lp p.1 p.2)
        (argmin (minimaxPrimal (L 0) X Y) ×ˢ argmax (minimaxDual (L 0) X Y)) ∧
      (∀ y ∈ argmax (minimaxDual (L 0) X Y),
        ConvexOn ℝ (argmin (minimaxPrimal (L 0) X Y)) (fun x ↦ Lp x y)) ∧
      (∀ x ∈ argmin (minimaxPrimal (L 0) X Y),
        ConcaveOn ℝ (argmax (minimaxDual (L 0) X Y)) (fun y ↦ Lp x y)) ∧
      (argminimaxOn Lp (argmin (minimaxPrimal (L 0) X Y)) (argmax (minimaxDual (L 0) X Y))).Nonempty ∧
      ∀ p ∈ argminimaxOn Lp (argmin (minimaxPrimal (L 0) X Y)) (argmax (minimaxDual (L 0) X Y)),
        Tendsto (fun t ↦ (saddleValue L X Y t - saddleValue L X Y 0) / t) (𝓝[>] 0)
          (𝓝 (Lp p.1 p.2)) := by
  set X₀ := argmin (minimaxPrimal (L 0) X Y)
  set Y₀ := argmax (minimaxDual (L 0) X Y)
  obtain ⟨hS0eq, hX₀n, hY₀n, hX₀b, hY₀b, hX₀c, hY₀c, hX₀v, hY₀v, hX₀X, hY₀Y, hconst⟩ :=
    h.zero_structure hS0 hS0b
  set v₀ := saddleValue L X Y 0
  set D : ℝ × (E × P) → ℝ := fun p ↦ (L p.1 p.2.1 p.2.2 - L 0 p.2.1 p.2.2) / p.1
  -- pointwise limits as `t ↘ 0`
  have hpt {x : E} {y : P} (hx : x ∈ X₀) (hy : y ∈ Y₀) :
      Tendsto (fun t ↦ D (t, x, y)) (𝓝[>] 0) (𝓝 (Lp x y)) :=
    (hLp x hx y hy).comp (tendsto_id.prodMk (tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_const_nhds, Eventually.of_forall fun _ ↦ ⟨hX₀X hx, hY₀Y hy⟩⟩))
  have hTpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 T := Ioo_mem_nhdsGT h.pos
  -- continuity
  have hcont : ContinuousOn (fun p : E × P ↦ Lp p.1 p.2) (X₀ ×ˢ Y₀) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
    have hev := (hLp x hx y hy).eventually (closedBall_mem_nhds (Lp x y) (half_pos hε))
    obtain ⟨pa, hpa, pb, hpb, hall⟩ := eventually_prod_iff.mp hev
    have hpb' : pb ∈ 𝓝[X₀ ×ˢ Y₀] (x, y) := nhdsWithin_mono _ (prod_mono hX₀X hY₀Y) hpb
    filter_upwards [hpb', self_mem_nhdsWithin] with q hq hqS
    have hmem : Lp q.1 q.2 ∈ closedBall (Lp x y) (ε / 2) :=
      isClosed_closedBall.mem_of_tendsto (hpt hqS.1 hqS.2) (hpa.mono fun t ht ↦ hall ht hq)
    exact lt_of_le_of_lt (mem_closedBall.mp hmem) (half_lt_self hε)
  -- convexity and concavity
  have hconvx : ∀ y ∈ Y₀, ConvexOn ℝ X₀ (fun x ↦ Lp x y) := by
    intro y hy
    refine ⟨hX₀v, fun x₁ hx₁ x₂ hx₂ a b ha hb hab ↦ ?_⟩
    have hz := hX₀v hx₁ hx₂ ha hb hab
    refine le_of_tendsto_of_tendsto (hpt hz hy)
      (((hpt hx₁ hy).const_smul a).add ((hpt hx₂ hy).const_smul b)) ?_
    filter_upwards [hTpos] with t ht
    have htT : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
    have hc := (h.convexOn_left t htT y (hY₀Y hy)).2 (hX₀X hx₁) (hX₀X hx₂) ha hb hab
    simp only [D, smul_eq_mul, hconst _ hz _ hy, hconst _ hx₁ _ hy, hconst _ hx₂ _ hy]
    rw [div_le_iff₀ ht.1]
    have hsum : a * ((L t x₁ y - v₀) / t) * t + b * ((L t x₂ y - v₀) / t) * t =
        a * L t x₁ y + b * L t x₂ y - v₀ := by
      rw [mul_assoc, div_mul_cancel₀ _ ht.1.ne', mul_assoc, div_mul_cancel₀ _ ht.1.ne']
      have : a = 1 - b := by linarith
      subst this
      ring
    rw [add_mul, hsum]
    simp only [smul_eq_mul] at hc
    linarith
  have hconcy : ∀ x ∈ X₀, ConcaveOn ℝ Y₀ (fun y ↦ Lp x y) := by
    intro x hx
    refine ⟨hY₀v, fun y₁ hy₁ y₂ hy₂ a b ha hb hab ↦ ?_⟩
    have hz := hY₀v hy₁ hy₂ ha hb hab
    refine le_of_tendsto_of_tendsto
      (((hpt hx hy₁).const_smul a).add ((hpt hx hy₂).const_smul b)) (hpt hx hz) ?_
    filter_upwards [hTpos] with t ht
    have htT : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
    have hc := (h.concaveOn_right t htT x (hX₀X hx)).2 (hY₀Y hy₁) (hY₀Y hy₂) ha hb hab
    simp only [D, smul_eq_mul, hconst _ hx _ hz, hconst _ hx _ hy₁, hconst _ hx _ hy₂]
    rw [le_div_iff₀ ht.1]
    have hsum : a * ((L t x y₁ - v₀) / t) * t + b * ((L t x y₂ - v₀) / t) * t =
        a * L t x y₁ + b * L t x y₂ - v₀ := by
      rw [mul_assoc, div_mul_cancel₀ _ ht.1.ne', mul_assoc, div_mul_cancel₀ _ ht.1.ne']
      have : a = 1 - b := by linarith
      subst this
      ring
    rw [add_mul, hsum]
    simp only [smul_eq_mul] at hc
    linarith
  -- saddle points of `L₊` on `X₀ × Y₀`
  have hLpm : IsMinimaxProblem Lp X₀ Y₀ :=
    ⟨hX₀n, hX₀c, hX₀v, hY₀n, hY₀c, hY₀v, hcont, hconvx, hconcy⟩
  have hLpne := (hLpm.argminimaxOn_nonempty_bounded_of_bounded hX₀b hY₀b).2.2.1
  refine ⟨hcont, hconvx, hconcy, hLpne, ?_⟩
  -- the right derivative of the saddle value
  rintro ⟨xh, yh⟩ ⟨hxh, hyh, hsad⟩
  obtain ⟨ε, hε, hεT, hne, -, ⟨V, hV, hVb⟩, -⟩ := h.golshtein_saddle_sets hS0 hS0b
  have hK := hVb.isCompact_closure
  have h0m : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, h.pos.le⟩
  have hεT' {t : ℝ} (ht : t ∈ Icc 0 ε) : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hεT⟩
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hns' := tendsto_nhdsWithin_iff.mp hns
  have hnsV : ∀ᶠ n in atTop, ns n ∈ Icc 0 ε ∩ V := by
    filter_upwards [hns'.1.eventually hV, hns'.1.eventually (gt_mem_nhds hε), hns'.2]
      with n hn₁ hn₂ hn₃
    exact ⟨⟨le_of_lt hn₃, hn₂.le⟩, hn₁⟩
  obtain ⟨pd, hpd⟩ := hS0
  let ps : ℕ → E × P := fun n ↦
    if hn : ns n ∈ Icc 0 ε ∩ V then (hne _ hn.1).1.some else pd
  have hpsK (n : ℕ) :
      ps n ∈ closure (svImage (fun t ↦ argminimaxOn (L t) X Y) (Icc 0 ε ∩ V)) := by
    by_cases hn : ns n ∈ Icc 0 ε ∩ V
    · simp only [ps, hn, dite_true]
      exact subset_closure (mem_svImage.mpr ⟨ns n, hn, (hne _ hn.1).1.some_mem⟩)
    · simp only [ps, hn, dite_false]
      exact subset_closure (mem_svImage.mpr
        ⟨0, ⟨⟨le_rfl, hε.le⟩, mem_of_mem_nhds hV⟩, hpd⟩)
  obtain ⟨p', -, φ, hφ, hlim⟩ := hK.tendsto_subseq hpsK
  refine ⟨φ, ?_⟩
  have hev : ∀ᶠ n in atTop, ns (φ n) ∈ Icc 0 ε ∩ V := hφ.tendsto_atTop.eventually hnsV
  have hpos : ∀ᶠ n in atTop, ns (φ n) ∈ Ioi 0 := hφ.tendsto_atTop.eventually hns'.2
  have hpsS : ∀ᶠ n in atTop, ps (φ n) ∈ argminimaxOn (L (ns (φ n))) X Y := by
    filter_upwards [hev] with n hn
    simp only [ps, hn, dite_true]
    exact (hne _ hn.1).1.some_mem
  have htlim : Tendsto (fun n ↦ ns (φ n)) atTop (𝓝 0) := hns'.1.comp hφ.tendsto_atTop
  have htlim' : Tendsto (fun n ↦ ns (φ n)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨htlim, hpos⟩
  have hp'S : p' ∈ argminimaxOn (L 0) X Y :=
    h.mem_argminimaxOn_of_tendsto subset_rfl subset_rfl h.isClosed_left h.isClosed_right
      (hev.mono fun n hn ↦ hεT' hn.1) hpsS h0m htlim hlim
  rw [hS0eq] at hp'S
  have hxs : Tendsto (fun n ↦ (ps (φ n)).1) atTop (𝓝 p'.1) := (continuous_fst.tendsto _).comp hlim
  have hys : Tendsto (fun n ↦ (ps (φ n)).2) atTop (𝓝 p'.2) := (continuous_snd.tendsto _).comp hlim
  have hup : Tendsto (fun n ↦ D (ns (φ n), xh, (ps (φ n)).2)) atTop (𝓝 (Lp xh p'.2)) :=
    (hLp xh hxh p'.2 hp'S.2).comp (htlim'.prodMk (tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_const_nhds.prodMk_nhds hys, hpsS.mono fun n hn ↦ ⟨hX₀X hxh, hn.2.1⟩⟩))
  have hlow : Tendsto (fun n ↦ D (ns (φ n), (ps (φ n)).1, yh)) atTop (𝓝 (Lp p'.1 yh)) :=
    (hLp p'.1 hp'S.1 yh hyh).comp (htlim'.prodMk (tendsto_nhdsWithin_iff.mpr
      ⟨hxs.prodMk_nhds tendsto_const_nhds, hpsS.mono fun n hn ↦ ⟨hn.1, hY₀Y hyh⟩⟩))
  have hbounds : ∀ᶠ n in atTop,
      D (ns (φ n), (ps (φ n)).1, yh) ≤ (saddleValue L X Y (ns (φ n)) - v₀) / ns (φ n) ∧
      (saddleValue L X Y (ns (φ n)) - v₀) / ns (φ n) ≤ D (ns (φ n), xh, (ps (φ n)).2) := by
    filter_upwards [hev, hpos, hpsS] with n hn hp hS
    have hv₀ := h.apply_eq_saddleValue (hεT' hn.1) hS
    obtain ⟨hxn, hyn, hsadn⟩ := hS
    have h₁ : L (ns (φ n)) (ps (φ n)).1 (ps (φ n)).2 ≤ L (ns (φ n)) xh (ps (φ n)).2 :=
      (hsadn xh (hX₀X hxh) (ps (φ n)).2 hyn).1
    have h₂ : L 0 xh (ps (φ n)).2 ≤ v₀ := by
      obtain ⟨y0, hy0⟩ := hY₀n
      have hs0 : (xh, y0) ∈ argminimaxOn (L 0) X Y := by rw [hS0eq]; exact ⟨hxh, hy0⟩
      have hh := (hs0.2.2 xh (hX₀X hxh) (ps (φ n)).2 hyn).2
      rwa [show L 0 (xh, y0).1 (xh, y0).2 = v₀ from hconst xh hxh y0 hy0] at hh
    have h₃ : L (ns (φ n)) (ps (φ n)).1 yh ≤ L (ns (φ n)) (ps (φ n)).1 (ps (φ n)).2 :=
      (hsadn (ps (φ n)).1 hxn yh (hY₀Y hyh)).2
    have h₄ : v₀ ≤ L 0 (ps (φ n)).1 yh := by
      obtain ⟨x0, hx0⟩ := hX₀n
      have hs0 : (x0, yh) ∈ argminimaxOn (L 0) X Y := by rw [hS0eq]; exact ⟨hx0, hyh⟩
      have hh := (hs0.2.2 (ps (φ n)).1 hxn yh (hY₀Y hyh)).1
      rwa [show L 0 (x0, yh).1 (x0, yh).2 = v₀ from hconst x0 hx0 yh hyh] at hh
    rw [← hv₀]
    have hp' : (0 : ℝ) ≤ ns (φ n) := le_of_lt hp
    exact ⟨div_le_div_of_nonneg_right (by linarith) hp',
      div_le_div_of_nonneg_right (by linarith) hp'⟩
  have hupμ : Lp xh p'.2 ≤ Lp xh yh := (hsad xh hxh p'.2 hp'S.2).2
  have hlowμ : Lp xh yh ≤ Lp p'.1 yh := (hsad p'.1 hp'S.1 yh hyh).1
  have hle : Lp p'.1 yh ≤ Lp xh p'.2 :=
    le_of_tendsto_of_tendsto hlow hup (hbounds.mono fun n hn ↦ hn.1.trans hn.2)
  have e₁ : Lp p'.1 yh = Lp xh yh := le_antisymm (hle.trans hupμ) hlowμ
  have e₂ : Lp xh p'.2 = Lp xh yh := le_antisymm hupμ (hlowμ.trans hle)
  rw [e₁] at hlow
  rw [e₂] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup (hbounds.mono fun n hn ↦ hn.1)
    (hbounds.mono fun n hn ↦ hn.2)

end IsSaddlePerturbation

end
end RW
