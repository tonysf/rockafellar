/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuous convergence at a finite value

The finite-height criterion at the end of Theorem 7.11 concerns the graph at
the point where continuous convergence is tested. Local boundedness rules
out sequences of finite heights escaping to infinity, as well as infinite
function values.
-/
import RockafellarWets.Chapter7.EpiFromUniform
import RockafellarWets.Chapter5.GraphicalLimitFormulas

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [PseudoMetricSpace E] {f : ℕ → E → EReal} {g : E → EReal}
variable {X : Set E} {x : E}

/-- Continuous convergence at a point controls all nearby arguments in a
single neighborhood after a single index. -/
theorem ConvergesContinuouslyWithinAt.exists_nhds_eventually_mem (hx : x ∈ X)
    (h : ConvergesContinuouslyWithinAt f g X x) {W : Set EReal} (hW : W ∈ 𝓝 (g x)) :
    ∃ V ∈ 𝓝 x, ∀ᶠ n in atTop, ∀ y ∈ V ∩ X, f n y ∈ W := by
  classical
  by_contra! hn
  have hbad (k : ℕ) : ∃ᶠ n in atTop,
      ∃ y ∈ ball x (1 / ((k : ℝ) + 1)) ∩ X, f n y ∉ W := by
    simpa using hn (ball x (1 / ((k : ℝ) + 1))) (ball_mem_nhds _ (by positivity))
  obtain ⟨φ, hφ, hhit⟩ := extraction_forall_of_frequently hbad
  choose y hy hybad using hhit
  have hyx : Tendsto y atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (mem_ball.1 (hy k).1).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  let z := Function.extend φ y (fun _ ↦ x)
  have hzX : ∀ n, z n ∈ X := by
    intro n
    by_cases hm : ∃ k, φ k = n
    · obtain ⟨k, rfl⟩ := hm
      simp only [z, hφ.injective.extend_apply]
      exact (hy k).2
    · simpa [z, Function.extend_apply' _ _ _ hm] using hx
  have hz := (h z hzX (tendsto_extend_of_strictMono hφ hyx)).eventually_mem hW
  obtain ⟨k, hk⟩ := (hφ.tendsto_atTop.eventually hz).exists
  exact hybad k (by simpa [z, hφ.injective.extend_apply] using hk)

/-- Uniform finite bounds near a point, eventually in the sequence index. -/
def EventuallyLocallyBoundedWithinAt (f : ℕ → E → EReal) (X : Set E) (x : E) : Prop :=
  ∃ V ∈ 𝓝 x, ∃ M : ℝ, ∀ᶠ n in atTop, ∀ y ∈ V ∩ X, f n y ∈ Icc ((-M : ℝ) : EReal) (M : EReal)

theorem ConvergesContinuouslyWithinAt.eventuallyLocallyBounded_of_finite (hx : x ∈ X)
    (h : ConvergesContinuouslyWithinAt f g X x) {r : ℝ} (hr : g x = r) :
    EventuallyLocallyBoundedWithinAt f X x := by
  let M := |r| + 1
  have hW : Ioo ((-M : ℝ) : EReal) (M : EReal) ∈ 𝓝 (g x) := by
    rw [hr]
    apply Ioo_mem_nhds <;> apply EReal.coe_lt_coe_iff.2 <;> dsimp [M]
    · linarith [neg_abs_le r]
    · linarith [le_abs_self r]
  obtain ⟨V, hV, hv⟩ := h.exists_nhds_eventually_mem hx hW
  exact ⟨V, hV, M, hv.mono fun n hn y hy ↦ ⟨(hn y hy).1.le, (hn y hy).2.le⟩⟩

/-- Eventual local boundedness makes graphical convergence at the point
sufficient for continuous convergence there. -/
theorem convergesContinuouslyWithinAt_of_finiteGraph_of_eventuallyLocallyBounded
    (hb : EventuallyLocallyBoundedWithinAt f X x)
    (hg : GraphicalConvergesWithinAt (fun n ↦ finiteGraphFiber (f n)) (finiteGraphFiber g) X x) :
    ConvergesContinuouslyWithinAt f g X x := by
  obtain ⟨V, hV, M, hb⟩ := hb
  intro z hz hzx
  let a := fun n ↦ f n (z n)
  have hI : ∀ᶠ n in atTop, a n ∈ Icc ((-M : ℝ) : EReal) (M : EReal) := by
    filter_upwards [hb, hzx.eventually_mem hV] with n hn hzn
    exact hn _ ⟨hzn, hz n⟩
  have hreal : ∀ᶠ n in atTop, ((a n).toReal : EReal) = a n :=
    hI.mono fun n hn ↦ EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hn.2)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hn.1)
  by_contra hnot
  obtain ⟨W, hW, hbad⟩ := not_tendsto_iff_exists_frequently_notMem.1 hnot
  obtain ⟨U, hUW, hU, hxU⟩ := _root_.mem_nhds_iff.1 hW
  let K := Icc (-M) M ∩ ((↑) : ℝ → EReal) ⁻¹' Uᶜ
  have hK : IsCompact K :=
    isCompact_Icc.inter_right (hU.isClosed_compl.preimage continuous_coe_real_ereal)
  have hkfreq : ∃ᶠ n in atTop, (a n).toReal ∈ K := by
    apply (hbad.and_eventually (hI.and hreal)).mono
    rintro n ⟨hn, hIn, hfn⟩
    refine ⟨⟨EReal.coe_le_coe_iff.1 (by rw [hfn]; exact hIn.1),
      EReal.coe_le_coe_iff.1 (by rw [hfn]; exact hIn.2)⟩, ?_⟩
    change ((a n).toReal : EReal) ∉ U
    rw [hfn]
    exact fun hnu ↦ hn (hUW hnu)
  obtain ⟨r, hrK, φ, hφ, hr⟩ := hK.tendsto_subseq' hkfreq
  have hrmem : r ∈ outerSetLimit (fun n ↦ finiteGraphFiber (f n) (z n)) := by
    intro B hB
    apply Frequently.filter_mono _ hφ.tendsto_atTop
    apply (frequently_map (m := φ)).2
    exact ((hφ.tendsto_atTop.eventually hreal).and (hr.eventually_mem hB)).frequently.mono
      fun n hn ↦ ⟨_, hn.1, hn.2⟩
  have hre : (r : EReal) = g x :=
    hg.1 (mem_graphicalOuterLimitWithin_iff.2 ⟨z, ⟨hz, hzx⟩, hrmem⟩)
  exact hrK.2 (hre.symm ▸ hxU)

/-- **Theorem 7.11**, the finite-value graphical criterion at `x`.
Finiteness of the limit at `x` suffices. -/
theorem convergesContinuouslyWithinAt_iff_finiteGraph_and_eventuallyLocallyBounded
    (hx : x ∈ X) {r : ℝ} (hr : g x = r) :
    ConvergesContinuouslyWithinAt f g X x ↔
      GraphicalConvergesWithinAt (fun n ↦ finiteGraphFiber (f n)) (finiteGraphFiber g) X x ∧
      EventuallyLocallyBoundedWithinAt f X x :=
  ⟨fun h ↦ ⟨h.graphicalConvergesWithinAt_finiteGraphFiber hx,
      h.eventuallyLocallyBounded_of_finite hx hr⟩,
    fun ⟨hg, hb⟩ ↦ convergesContinuouslyWithinAt_of_finiteGraph_of_eventuallyLocallyBounded hb hg⟩

end RW
