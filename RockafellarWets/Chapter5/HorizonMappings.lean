/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Horizon Mappings and the Horizon Criterion

Formula 5(5) attaches to a set-valued mapping `S` its horizon mapping `S∞`,
specified graphically by `gph S∞ := (gph S)∞`.  Since a mapping is determined
by its graph, this is a definition rather than a theorem, and it is
implemented here by reading the horizon cone of the graph fibrewise.  The
identity `gph S∞ = (gph S)∞` then holds by `rfl`.

Theorem 5.18 gives the criterion `S∞(0) = {0}` for local boundedness.  The
argument is the one in the book: a failure of local boundedness produces, by
5.15, a bounded sequence of arguments carrying values of unbounded norm, and
rescaling by those norms produces a nonzero horizon direction over `0`.  The
rescaled values live in the unit ball, so a convergent subsequence exists;
this is where finite-dimensionality of the target enters.

The second assertion of 5.18 is free: `(gph S)∞` is a closed cone, hence its
own horizon cone, so `(S∞)∞ = S∞` and the criterion propagates from `S` to
`S∞`.

The condition is sufficient but not necessary; the book's example `S(u) = u²`
on `IR` is locally bounded with `S∞(0) = [0, ∞)`.
-/

import RockafellarWets.Chapter3.LinearImages
import RockafellarWets.Chapter3.PointedCones
import RockafellarWets.Chapter5.ConvexSemicontinuity
import RockafellarWets.Chapter5.LocalBoundedness

open scoped Pointwise
open Bornology Filter Metric Set Topology

namespace RW

section Definition

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Formula 5(5)**: the horizon mapping `S∞`, specified by
`gph S∞ = (gph S)∞`. -/
def svHorizon (S : E → Set F) : E → Set F :=
  fun x ↦ {u | (x, u) ∈ horizonCone (svGraph S)}

@[simp]
theorem mem_svHorizon {S : E → Set F} {x : E} {u : F} :
    u ∈ svHorizon S x ↔ (x, u) ∈ horizonCone (svGraph S) := Iff.rfl

/-- **Formula 5(5)**: the graph of the horizon mapping is the horizon cone of
the graph. -/
theorem svGraph_svHorizon (S : E → Set F) :
    svGraph (svHorizon S) = horizonCone (svGraph S) := rfl

/-- The graph of `S∞` is closed, being a horizon cone. -/
theorem isClosed_svGraph_svHorizon (S : E → Set F) :
    IsClosed (svGraph (svHorizon S)) := by
  rw [svGraph_svHorizon]
  exact isClosed_horizonCone _

/-- The remark after 5(5): `S∞` is outer semicontinuous, by 5.7(a). -/
theorem svOsc_svHorizon (S : E → Set F) : SvOsc (svHorizon S) :=
  isClosed_svGraph_iff_svOsc.1 (isClosed_svGraph_svHorizon S)

/-- The remark after 5(5): `0 ∈ S∞(0)`. -/
theorem zero_mem_svHorizon_zero (S : E → Set F) : (0 : F) ∈ svHorizon S 0 :=
  zero_mem_horizonCone _

/-- The remark after 5(5): `S∞` is positively homogeneous,
`S∞(λx) = λS∞(x)` for `λ > 0`. -/
theorem svHorizon_smul (S : E → Set F) {c : ℝ} (hc : 0 < c) (x : E) :
    svHorizon S (c • x) = c • svHorizon S x := by
  have hcone := isCone_horizonCone (svGraph S)
  ext u
  constructor
  · intro hu
    refine ⟨c⁻¹ • u, ?_, by simp [smul_smul, mul_inv_cancel₀ hc.ne']⟩
    have := hcone.2 hu (inv_pos.2 hc)
    rwa [Prod.smul_mk, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
  · rintro ⟨w, hw, rfl⟩
    have := hcone.2 hw hc
    rwa [Prod.smul_mk] at this

/-- The remark after 5(5): graph-convexity passes to the horizon mapping. -/
theorem SvGraphConvex.svHorizon {S : E → Set F} (h : SvGraphConvex S) :
    SvGraphConvex (svHorizon S) := by
  rw [SvGraphConvex, svGraph_svHorizon]
  exact convex_horizonCone h

/-- Since `(gph S)∞` is a closed cone, it is its own horizon cone; hence
`(S∞)∞ = S∞`. -/
theorem svHorizon_svHorizon (S : E → Set F) :
    svHorizon (svHorizon S) = svHorizon S := by
  funext x
  ext u
  rw [mem_svHorizon, mem_svHorizon, svGraph_svHorizon,
    horizonCone_eq_self_of_isClosed_isCone (isClosed_horizonCone _)
      (isCone_horizonCone _)]

end Definition

section HorizonCriterion

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Theorem 5.18**, first assertion: `S∞(0) = {0}` forces `S` to be locally
bounded.

If `S` were not locally bounded, 5.15 would supply a bounded set of arguments
whose image is unbounded; normalizing the resulting values by their own norms
produces a unit vector in `S∞(0)`. -/
theorem svLocallyBounded_of_svHorizon_zero {S : E → Set F}
    (h : svHorizon S 0 = ({0} : Set F)) : SvLocallyBounded S := by
  by_contra hnot
  rw [svLocallyBounded_iff_isBounded_svImage] at hnot
  push_neg at hnot
  obtain ⟨B, hB, hunb⟩ := hnot
  obtain ⟨us, husmem, husdiv⟩ := exists_seq_mem_norm_atTop_of_not_isBounded hunb
  choose xs hxsB hxsmem using fun n ↦ mem_svImage.1 (husmem n)
  obtain ⟨M, hM⟩ := hB.exists_norm_le
  -- Rescale by `max ‖uν‖ 1`, which diverges and never vanishes.
  set c : ℕ → ℝ := fun n ↦ max ‖us n‖ 1 with hcdef
  have hc1 : ∀ n, (1 : ℝ) ≤ c n := fun n ↦ le_max_right _ _
  have hcpos : ∀ n, 0 < c n := fun n ↦ lt_of_lt_of_le one_pos (hc1 n)
  have hctop : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_max_left _ _) husdiv
  have hcinv : Tendsto (fun n ↦ (c n)⁻¹) atTop (𝓝 0) := hctop.inv_tendsto_atTop
  set vs : ℕ → F := fun n ↦ (c n)⁻¹ • us n with hvsdef
  have hvsnorm : ∀ n, ‖vs n‖ = ‖us n‖ / c n := fun n ↦ by
    rw [hvsdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hcpos n),
      div_eq_inv_mul]
  have hvsball : ∀ n, vs n ∈ closedBall (0 : F) 1 := fun n ↦ by
    rw [mem_closedBall, dist_zero_right, hvsnorm n]
    exact div_le_one_of_le₀ (le_max_left _ _) (hcpos n).le
  obtain ⟨v, -, φ, hφ, hvtend⟩ :=
    (isCompact_closedBall (0 : F) 1).tendsto_subseq hvsball
  -- The rescaled values have norm tending to `1`, so the limit is a unit vector.
  have hvsnorm_one : Tendsto (fun n ↦ ‖vs n‖) atTop (𝓝 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [husdiv.eventually_ge_atTop 1] with n hn
    have hne : ‖us n‖ ≠ 0 := by linarith
    have hcn : c n = ‖us n‖ := max_eq_left hn
    rw [hvsnorm n, hcn, div_self hne]
  have hvnorm : ‖v‖ = 1 :=
    tendsto_nhds_unique (hvtend.norm) (hvsnorm_one.comp hφ.tendsto_atTop)
  -- The rescaled arguments tend to `0`, since they were bounded to begin with.
  set ws : ℕ → E := fun n ↦ (c n)⁻¹ • xs n with hwsdef
  have hwtend : Tendsto ws atTop (𝓝 0) := by
    have hMc : Tendsto (fun n ↦ M * (c n)⁻¹) atTop (𝓝 0) := by
      simpa using hcinv.const_mul M
    refine squeeze_zero_norm (fun n ↦ ?_) hMc
    rw [hwsdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hcpos n),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _ (hxsB n)) (by positivity)
  -- Hence `(0, v)` is a horizon direction of the graph.
  have hmem : ∀ n, c (φ n) • (ws (φ n), vs (φ n)) ∈ svGraph S := fun n ↦ by
    rw [Prod.smul_mk, hwsdef, hvsdef, smul_smul, smul_smul,
      mul_inv_cancel₀ (hcpos (φ n)).ne', one_smul, one_smul]
    exact hxsmem (φ n)
  have hzero : (0, v) ∈ horizonCone (svGraph S) :=
    Set.mem_insert_of_mem 0 <| mem_asymptoticCone_of_seq_smul
      (hctop.comp hφ.tendsto_atTop)
      ((hwtend.comp hφ.tendsto_atTop).prodMk_nhds hvtend) hmem
  have : v ∈ ({0} : Set F) := h ▸ hzero
  rw [mem_singleton_iff] at this
  rw [this, norm_zero] at hvnorm
  exact absurd hvnorm zero_ne_one

/-- **Theorem 5.18**, second assertion: under the same criterion the horizon
mapping `S∞` is locally bounded as well.  This is the first assertion applied
to `S∞`, whose own horizon mapping is itself. -/
theorem svLocallyBounded_svHorizon_of_svHorizon_zero {S : E → Set F}
    (h : svHorizon S 0 = ({0} : Set F)) : SvLocallyBounded (svHorizon S) :=
  svLocallyBounded_of_svHorizon_zero (by rw [svHorizon_svHorizon]; exact h)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Theorem 5.18**, final assertion: for a graph-convex outer semicontinuous
mapping the criterion holds as soon as one value is nonempty and bounded.

A horizon direction `u` over `0` makes the whole ray `ū + τu` stay in `S(x̄)`,
by 3.6; boundedness of `S(x̄)` leaves only `u = 0`. -/
theorem svHorizon_zero_eq_singleton_zero_of_graphConvex {S : E → Set F}
    (hconv : SvGraphConvex S) (hosc : SvOsc S) {x : E}
    (hne : (S x).Nonempty) (hbdd : IsBounded (S x)) :
    svHorizon S 0 = ({0} : Set F) := by
  have hclosed : IsClosed (svGraph S) := isClosed_svGraph_iff_svOsc.2 hosc
  obtain ⟨u₀, hu₀⟩ := hne
  refine Set.eq_singleton_iff_unique_mem.2 ⟨zero_mem_svHorizon_zero S, ?_⟩
  intro u hu
  by_contra hune
  -- The ray `ū + τu` lies in `S(x̄)` for every `τ ≥ 0`.
  have hray : ∀ τ : ℝ, 0 ≤ τ → u₀ + τ • u ∈ S x := by
    intro τ hτ
    have := smul_add_mem_of_mem_horizonCone hconv hclosed
      (x := (x, u₀)) (w := (0, u)) hu₀ hu hτ
    rw [Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add] at this
    rw [add_comm]
    exact this
  -- Such a ray is unbounded, contradicting boundedness of `S(x̄)`.
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  have hR0 : 0 ≤ R := le_trans (norm_nonneg u₀) (hR _ hu₀)
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hune
  obtain ⟨τ, hτ⟩ := exists_gt ((R + ‖u₀‖) / ‖u‖)
  have hτpos : 0 < τ :=
    lt_of_le_of_lt (div_nonneg (by linarith [norm_nonneg u₀]) (norm_nonneg u)) hτ
  have hle : ‖u₀ + τ • u‖ ≤ R := hR _ (hray τ hτpos.le)
  have hgt : R + ‖u₀‖ < τ * ‖u‖ := by
    rw [div_lt_iff₀ hupos] at hτ
    exact hτ
  have hlb : τ * ‖u‖ ≤ ‖u₀ + τ • u‖ + ‖u₀‖ := by
    have h1 : ‖τ • u‖ ≤ ‖u₀ + τ • u‖ + ‖u₀‖ := by
      calc ‖τ • u‖ = ‖(u₀ + τ • u) - u₀‖ := by congr 1; abel
        _ ≤ ‖u₀ + τ • u‖ + ‖u₀‖ := norm_sub_le _ _
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hτpos] at h1
  linarith

end HorizonCriterion

end RW
