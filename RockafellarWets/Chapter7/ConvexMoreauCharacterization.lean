/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Characterization by a single convex Moreau envelope

For the last assertion of Theorem 7.37, pointwise convergence at one positive
parameter bounds the proximal points at the origin. Comparison with centers
`x` and `-x` bounds every scalar product with those points. Uniform boundedness
then supplies a bound on their norms, excluding escape of the epigraphs.
-/

import RockafellarWets.Chapter7.MoreauEpiCharacterization
import RockafellarWets.Chapter7.ConvexFunctionBounds
import RockafellarWets.Chapter7.ConvexEpiConvergence
import RockafellarWets.Chapter7.EpiCompactness
import RockafellarWets.Chapter4.HorizonLimits
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Bornology Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 7.37**, a converging sequence of closed proper convex functions
with proper epi-limit has infinite threshold of eventual prox-boundedness. -/
theorem eventualProxThreshold_eq_top_of_convex_epiConverges {f : ℕ → E → EReal} {g : E → EReal}
    (he : EpiConverges f g) (hf : ∀ n, Convex ℝ (epigraph (f n)))
    (hl : ∀ n, LowerSemicontinuous (f n)) (hp : ∀ n, IsProper (f n)) (hg : IsProper g) :
    eventualProxThreshold f = ⊤ := by
  obtain ⟨r, _, _, hr⟩ := exists_uniform_linear_lower_bound_of_convex_epiConverges he hf hl hp hg
  let q := fun w : E ↦ ((-r*(‖w‖+1) : ℝ) : EReal)
  have hq : HasAffineNormLowerBound q (-r) (-r) := fun w ↦ EReal.coe_le_coe_iff.2 (by ring_nf; rfl)
  by_contra hfinite
  obtain ⟨a, ha, _⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.2 hfinite)
  let t := max 1 a
  have ht : 0 < t := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨b,hb⟩ := exists_proxThreshold_witness_of_affineNormLowerBound ht hq
  have hQ : moreauEnvelopeEReal q t b ≤ liminf (fun n ↦ moreauEnvelopeEReal (f n) t b) atTop :=
    le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun n ↦ iInf_mono fun w ↦
      add_le_add (hr n w) le_rfl)
  have hthr : (t : EReal) ≤ eventualProxThreshold f :=
    le_iSup_of_le t (le_iSup_of_le ⟨ht,b,hb.trans_le hQ⟩ le_rfl)
  exact ha.not_ge ((EReal.coe_le_coe_iff.2 (le_max_right 1 a)).trans hthr)

private theorem bounded_epigraph_witness_of_tendsto_envelopes {f : ℕ → E → EReal} {g : E → EReal}
    (hf : ∀ n, Convex ℝ (epigraph (f n))) (hl : ∀ n, LowerSemicontinuous (f n))
    (hp : ∀ n, IsProper (f n)) (hg : Convex ℝ (epigraph g)) (hgl : LowerSemicontinuous g)
    (hgp : IsProper g) {t : ℝ} (ht : 0 < t)
    (he : ∀ x, Tendsto (fun n ↦ moreauEnvelopeEReal (f n) t x) atTop (𝓝 (moreauEnvelopeEReal g t x))) :
    ∃ (ws : ℕ → E) (R A : ℝ), ∀ n, ‖ws n‖ ≤ R ∧ f n (ws n) ≤ (A : EReal) := by
  let v := fun (n : ℕ) (x : E) ↦ (moreauEnvelopeEReal (f n) t x).toReal
  let k := 1 / (2*t)
  have hk : 0 < k := by dsimp [k]; positivity
  have hrv (n : ℕ) (x : E) : (v n x : EReal) = moreauEnvelopeEReal (f n) t x :=
    let h := moreauEnvelopeEReal_finite (hf n) (hl n) (hp n) ht x
    EReal.coe_toReal h.2.ne h.1.ne'
  have hB (x : E) : ∃ A : ℝ, ∀ n, |v n x| ≤ A := by
    obtain ⟨hb,ha⟩ := moreauEnvelopeEReal_finite hg hgl hgp ht x
    have hv := (EReal.tendsto_toReal ha.ne hb.ne').comp (he x)
    obtain ⟨A,hA⟩ := (isBounded_range_of_tendsto _ hv).exists_norm_le
    exact ⟨A, fun n ↦ hA _ (mem_range_self n)⟩
  choose ws hws using fun n ↦ proximalMappingEReal_nonempty (hf n) (hl n) (hp n) ht (0 : E)
  let c := fun n ↦ (f n (ws n)).toReal
  have hc (n : ℕ) : (c n : EReal) = f n (ws n) := EReal.coe_toReal
    (show f n (ws n) < ⊤ from mem_effectiveDomain_of_mem_proximalMappingEReal
      (hf n) (hl n) (hp n) ht (hws n)).ne ((hp n).2 _).ne'
  have hzero (n : ℕ) : c n + k*‖ws n‖^2 = v n 0 := by
    apply EReal.coe_eq_coe_iff.1
    rw [EReal.coe_add, hrv, hc]
    simpa [proximalObjectiveEReal, k] using (mem_proximalMappingEReal_iff.1 (hws n)).1
  have hprox (n : ℕ) (x : E) : v n x ≤ c n + k*‖ws n-x‖^2 := by
    apply EReal.coe_le_coe_iff.1
    rw [EReal.coe_add, hc, hrv]
    exact iInf_le (proximalObjectiveEReal (f n) t x) (ws n)
  obtain ⟨A,hA⟩ := hB 0
  have hinner (x : E) : ∃ M : ℝ, ∀ n, ⟪ws n,x⟫_ℝ ≤ M := by
    obtain ⟨B,hBx⟩ := hB x
    refine ⟨(A+B+k*‖x‖^2)/(2*k), fun n ↦ (le_div_iff₀ (by positivity)).2 ?_⟩
    have h := hprox n x
    rw [norm_sub_sq_real] at h
    nlinarith [hzero n, (abs_le.mp (hA n)).2, (abs_le.mp (hBx n)).1]
  obtain ⟨R,hR⟩ := banach_steinhaus (g := fun n ↦ innerSL ℝ (ws n)) (by
    intro x
    obtain ⟨M,hM⟩ := hinner x
    obtain ⟨N,hN⟩ := hinner (-x)
    refine ⟨max M N, fun n ↦ ?_⟩
    rw [innerSL_apply_apply, Real.norm_eq_abs, abs_le]
    exact ⟨by have := hN n; rw [inner_neg_right] at this; linarith [le_max_right M N],
      (hM n).trans (le_max_left M N)⟩)
  refine ⟨ws,R,A, fun n ↦ ⟨by simpa only [innerSL_apply_norm] using hR n, ?_⟩⟩
  rw [← hc n, EReal.coe_le_coe_iff]
  nlinarith [hzero n, (abs_le.mp (hA n)).2, mul_nonneg hk.le (sq_nonneg ‖ws n‖)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem epiConverges_of_all_subsequences {f : ℕ → E → EReal} {g : E → EReal}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ EpiConverges ((f ∘ φ) ∘ ψ) g) :
    EpiConverges f g := by
  let C := fun n ↦ epigraph (f n)
  have hin : epigraph g ⊆ innerSetLimit C := by
    intro z hz
    apply mem_innerSetLimit_iff_forall_subsequence_outerSetLimit.2
    intro φ hφ
    obtain ⟨ψ,hψ,he⟩ := h φ hφ
    exact outerSetLimit_subsequence_subset hψ ((PKConverges.outer_eq he).symm ▸ hz)
  have hout : outerSetLimit C ⊆ epigraph g := by
    intro z hz
    obtain ⟨φ,ws,hφ,hws,hwt⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hz
    obtain ⟨ψ,hψ,he⟩ := h φ hφ
    apply (PKConverges.outer_eq he).subset
    exact mem_outerSetLimit_iff_exists_subsequence.2 ⟨id,ws ∘ ψ,strictMono_id,
      fun n ↦ hws (ψ n), hwt.comp hψ.tendsto_atTop⟩
  exact ⟨((innerSetLimit_subset_outerSetLimit _).trans hout).antisymm hin,
    hout.antisymm (hin.trans (innerSetLimit_subset_outerSetLimit _))⟩

/-- **Theorem 7.37(b′)**, for closed proper convex objectives it suffices to
test pointwise convergence of a single positive-parameter envelope. -/
theorem convex_epiConverges_iff_tendsto_one_moreauEnvelope {f : ℕ → E → EReal} {g : E → EReal}
    (hf : ∀ n, Convex ℝ (epigraph (f n))) (hl : ∀ n, LowerSemicontinuous (f n))
    (hp : ∀ n, IsProper (f n)) (hg : Convex ℝ (epigraph g)) (hgl : LowerSemicontinuous g) (hgp : IsProper g) :
    EpiConverges f g ↔ ∃ t > 0, ∀ x, Tendsto (fun n ↦ moreauEnvelopeEReal (f n) t x) atTop
      (𝓝 (moreauEnvelopeEReal g t x)) := by
  constructor
  · intro h
    have hthr := eventualProxThreshold_eq_top_of_convex_epiConverges h hf hl hp hgp
    exact ⟨1,one_pos, fun x ↦ (tendsto_moreauEnvelopeEReal_of_epiConverges h hl hgp
      (tendsto_const_nhds (x := x)) tendsto_const_nhds one_pos (hthr ▸ EReal.coe_lt_top 1)).2⟩
  · rintro ⟨t,ht,he⟩
    obtain ⟨ws,R,A,hw⟩ := bounded_epigraph_witness_of_tendsto_envelopes hf hl hp hg hgl hgp ht he
    have hminor : ∃ β : ℝ, ∀ᶠ n in atTop, ∀ w, ((β-1/(2*t)*‖w-(0:E)‖^2 : ℝ) : EReal) ≤ f n w := by
      obtain ⟨β,_,hβ⟩ := EReal.exists_between_coe_real (moreauEnvelopeEReal_finite hg hgl hgp ht 0).1
      exact ⟨β, ((he 0).eventually_const_lt hβ).mono fun n hn ↦
        (le_moreauEnvelopeEReal_iff_quadratic_minorant t β 0).1 hn.le⟩
    obtain ⟨β,hβ⟩ := hminor
    apply epiConverges_of_all_subsequences
    intro φ hφ
    have hnon : ¬ EpiConverges (f ∘ φ) (fun _ ↦ ⊤) := by
      intro hesc
      let M := max (max R A) 0 + 1
      have hM : 0 < M := by dsimp [M]; positivity
      obtain ⟨n,hn⟩ := ((epiConverges_top_iff_eventually_on_closedBall _).1 hesc M hM).exists
      have hmR : R ≤ M := by dsimp [M]; linarith [le_max_left R A, le_max_left (max R A) 0]
      have hmA : A < M := by dsimp [M]; linarith [le_max_right R A, le_max_left (max R A) 0]
      exact (EReal.coe_lt_coe_iff.2 hmA).not_ge ((hn _ (mem_closedBall_zero_iff.2 ((hw _).1.trans hmR))).trans (hw _).2)
    obtain ⟨ψ,h,hψ,hne,hh⟩ := exists_epiConvergent_subsequence_of_not_escape hnon
    have hθ := hφ.comp hψ
    have hproper : IsProper h := by
      constructor
      · by_contra! htop
        exact hne (funext fun x ↦ top_unique (htop x))
      · intro x
        obtain ⟨ys,hy,hv⟩ := hh.exists_tendsto_values x
        have hlow := le_of_tendsto_of_tendsto (EReal.tendsto_coe.2 (tendsto_const_nhds.sub
          (((hy.sub_const 0).norm.pow 2).const_mul (1/(2*t))))) hv
          ((hθ.tendsto_atTop.eventually hβ).mono fun n hn ↦ hn (ys n))
        exact (EReal.bot_lt_coe _).trans_le hlow
    have hhconv := hh.convex_epigraph (fun n ↦ hf (φ (ψ n)))
    have hhl := lowerSemicontinuous_of_isClosed_epigraph_ereal h (PKConverges.isClosed hh)
    have hthr := eventualProxThreshold_eq_top_of_convex_epiConverges hh
      (fun n ↦ hf (φ (ψ n))) (fun n ↦ hl (φ (ψ n))) (fun n ↦ hp (φ (ψ n))) hproper
    have heq : moreauEnvelopeEReal h t = moreauEnvelopeEReal g t := by
      funext x
      have htend := (tendsto_moreauEnvelopeEReal_of_epiConverges hh (fun n ↦ hl (φ (ψ n))) hproper
        (tendsto_const_nhds (x := x)) tendsto_const_nhds ht (hthr ▸ EReal.coe_lt_top t)).2
      exact tendsto_nhds_unique htend ((he x).comp hθ.tendsto_atTop)
    have hfg := corollary336_eq_of_moreauEnvelopeEReal_eq hhconv hhl hproper hg hgl hgp ht heq
    exact ⟨ψ,hψ,hfg ▸ hh⟩

end RW
