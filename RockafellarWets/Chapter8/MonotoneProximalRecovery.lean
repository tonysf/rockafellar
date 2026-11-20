/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Monotone horizon scales for proximal recovery

Subsequences allow strictly decreasing scales by extraction. Under full
epi-convergence, choose a sequence of proximal subgradients of the limit
function first. Recover each fixed member for all large indices and increase
the recovery stage slowly. Its scale then decreases along the full sequence.
-/

import RockafellarWets.Chapter8.ProximalSubgradientLimits
import RockafellarWets.Chapter7.LevelSetConvergence

open Filter Metric Set Topology

namespace RW

private theorem strictAnti_subsequence_on_eventual {P : ℕ → Prop} {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hP : ∀ᶠ n in atTop, P n ∧ 0 < t n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictAnti (t ∘ φ) ∧ ∀ n, P (φ n) ∧ 0 < t (φ n) := by
  classical
  let A := {n : ℕ // P n ∧ 0 < t n}
  have hstep (a : A) : ∃ b : A, a.val < b.val ∧ t b.val < t a.val := by
    obtain ⟨n,hn,hi,ht'⟩ := (hP.and ((eventually_gt_atTop a.val).and (ht.eventually_lt_const a.2.2))).exists
    exact ⟨⟨n,hn⟩,hi,ht'⟩
  choose next hindex hscale using hstep
  obtain ⟨n₀,hn₀⟩ := hP.exists
  let a : ℕ → A := Nat.rec ⟨n₀,hn₀⟩ fun _ prev ↦ next prev
  exact ⟨fun n ↦ (a n).val,strictMono_nat_of_lt_succ (fun n ↦ hindex (a n)),
    strictAnti_nat_of_succ_lt (fun n ↦ hscale (a n)),fun n ↦ (a n).property⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {F : ℕ → E → EReal} {x v : E} {c : ℝ}

/-- **8.47(b)**, strictly decreasing horizon scales along the selected subsequence. -/
theorem exists_subsequence_strictAnti_proximal_recovery (hF : ∀ n, LowerSemicontinuous (F n))
    (hlim : epiLowerLimit F = f) (hx : f x = c) (hv : v ∈ horizonSubdifferential f x) :
    ∃ (φ : ℕ → ℕ) (y u : ℕ → E) (r t : ℕ → ℝ), StrictMono φ ∧ StrictAnti t ∧
      Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 c) ∧ Tendsto t atTop (𝓝 0) ∧
      Tendsto (fun n ↦ t n • u n) atTop (𝓝 v) ∧
      ∀ n, 0 < t n ∧ F (φ n) (y n) = (r n : EReal) ∧ u n ∈ proximalSubdifferential (F (φ n)) (y n) := by
  obtain ⟨ψ,hψ,y,u,r,t,hy,hr,ht,hu,hmem⟩ := exists_subsequence_horizonProximalSubgradientRecovery hF hlim hx hv
  obtain ⟨φ,hφ,hd,hφm⟩ := strictAnti_subsequence_on_eventual ht (hmem.mono fun _ h ↦ ⟨h.2,h.1⟩)
  exact ⟨ψ ∘ φ,y ∘ φ,u ∘ φ,r ∘ φ,t ∘ φ,hψ.comp hφ,hd,hy.comp hφ.tendsto_atTop,
    hr.comp hφ.tendsto_atTop,ht.comp hφ.tendsto_atTop,hu.comp hφ.tendsto_atTop,fun n ↦ ⟨(hφm n).2,(hφm n).1⟩⟩

/-- **8.47(b)**, decreasing horizon scales on a cofinite set of indices for
an epi-convergent sequence of lower semicontinuous functions. -/
theorem exists_antitone_proximal_recovery_of_epiConverges (hF : ∀ n, LowerSemicontinuous (F n))
    (hlim : EpiConverges F f) (hx : f x = c) (hv : v ∈ horizonSubdifferential f x) :
    ∃ (y u : ℕ → E) (r t : ℕ → ℝ), Antitone t ∧ (∀ n, 0 < t n) ∧
      Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 c) ∧ Tendsto t atTop (𝓝 0) ∧
      Tendsto (fun n ↦ t n • u n) atTop (𝓝 v) ∧
      ∀ᶠ n in atTop, F n (y n) = (r n : EReal) ∧ u n ∈ proximalSubdifferential (F n) (y n) := by
  classical
  have hl : LowerSemicontinuous f := (epiConverges_iff_epiLimits_eq.mp hlim).1 ▸ lowerSemicontinuous_epiLowerLimit _
  have he : EpiConverges (fun _ : ℕ ↦ f) f := pkConverges_const_of_isClosed (isClosed_epigraph_of_lsc_ereal f hl)
  obtain ⟨_,y,u,r,t,_,hd,hy,hr,ht,hu,hprox⟩ := exists_subsequence_strictAnti_proximal_recovery (fun _ ↦ hl)
    (epiConverges_iff_epiLimits_eq.mp he).1 hx hv
  let ε (j : ℕ) : ℝ := 1 / ((j:ℝ)+1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  let P (j n : ℕ) (a : (E × ℝ) × E) : Prop :=
    F n a.1.1 = (a.1.2 : EReal) ∧ a.2 ∈ proximalSubdifferential (F n) a.1.1 ∧
      dist (y j) a.1.1 < ε j ∧ dist (r j) a.1.2 < ε j ∧ dist (t j • u j) (t j • a.2) < ε j
  have hall (j : ℕ) : ∀ᶠ n in atTop, ∃ a, P j n a := by
    obtain ⟨_,hfj,huj⟩ := hprox j
    have hsj := regularSubdifferential_subset_subdifferential _ _ (proximalSubdifferential_subset_regularSubdifferential _ _ huj)
    obtain ⟨Y,U,R,hY,hR,hU,hm⟩ := proximalSubgradientRecovery_of_epiConverges hF hlim hfj hsj
    filter_upwards [hm,hY.eventually (ball_mem_nhds _ (hε j)),hR.eventually (ball_mem_nhds _ (hε j)),
      (hU.const_smul (t j)).eventually (ball_mem_nhds _ (hε j))] with n hn hY' hR' hU'
    exact ⟨((Y n,R n),U n),hn.1,hn.2,by simpa only [mem_ball,dist_comm (Y n)] using hY',
      by simpa only [mem_ball,dist_comm (R n)] using hR',
      by simpa only [mem_ball,dist_comm (t j • U n)] using hU'⟩
  obtain ⟨q,hqmono,hq,hpick⟩ := exists_diagonal_stage (fun j n ↦ ∃ a, P j n a) hall
  let a (n : ℕ) := if hn : ∃ a, P (q n) n a then hn.choose else ((0,0),0)
  have ha : ∀ᶠ n in atTop, P (q n) n (a n) := hpick.mono fun n hn ↦ by simpa only [a,dif_pos hn] using hn.choose_spec
  have heps : Tendsto (ε ∘ q) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.comp hq
  have hdlim {d : ℕ → ℝ} (h0 : ∀ n, 0 ≤ d n) (hbound : ∀ᶠ n in atTop, d n < ε (q n)) :
      Tendsto d atTop (𝓝 0) := squeeze_zero' (.of_forall h0) (hbound.mono fun _ h ↦ h.le) heps
  exact ⟨fun n ↦ (a n).1.1,fun n ↦ (a n).2,fun n ↦ (a n).1.2,t ∘ q,hd.antitone.comp_monotone hqmono,
    fun n ↦ (hprox _).1,(hy.comp hq).congr_dist (hdlim (fun _ ↦ dist_nonneg) (ha.mono fun _ h ↦ h.2.2.1)),
    (hr.comp hq).congr_dist (hdlim (fun _ ↦ dist_nonneg) (ha.mono fun _ h ↦ h.2.2.2.1)),ht.comp hq,
    (hu.comp hq).congr_dist (hdlim (fun _ ↦ dist_nonneg) (ha.mono fun _ h ↦ h.2.2.2.2)),ha.mono fun _ h ↦ ⟨h.1,h.2.1⟩⟩

end RW
