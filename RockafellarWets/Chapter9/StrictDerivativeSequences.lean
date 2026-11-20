/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fixed directions in strict graphical derivatives
-/

import RockafellarWets.Chapter9.StrictGraphicalDerivatives
import RockafellarWets.Chapter9.LipschitzModulus
import RockafellarWets.Chapter8.SubderivativeFormulas

open Filter Metric Set Topology

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Formula 9(28).** Local Lipschitz continuity permits fixing the input
 direction in the sequences defining the strict graphical derivative. -/
theorem mem_strictGraphicalDerivative_singleton_iff_fixed_sequences
    {f : E → F} {x w : E} {z : F} (hf : StrictlyContinuousAt f x) :
    z ∈ strictGraphicalDerivative (fun a ↦ {f a}) x (f x) w ↔
      ∃ (τ : ℕ → ℝ) (a : ℕ → E), (∀ n, 0 < τ n) ∧
        Tendsto τ atTop (𝓝 0) ∧ Tendsto a atTop (𝓝 x) ∧
        Tendsto (fun n ↦ (τ n)⁻¹ • (f (a n + τ n • w) - f (a n))) atTop (𝓝 z) := by
  constructor
  · intro hz
    obtain ⟨τ,a,b,v,q,hτ,hτt,hab,hat,hbt,hvt,hqt,hmem⟩ :=
      mem_strictGraphicalDerivative_iff_sequences.mp hz
    have he (n : ℕ) : q n = (τ n)⁻¹ • (f (a n + τ n • v n) - f (a n)) := by
      obtain ⟨y,hy,hyq⟩ := hmem n
      simpa only [mem_singleton_iff.mp hy,mem_singleton_iff.mp (hab n)] using hyq.symm
    obtain ⟨k,U,hU,hLip⟩ := strictlyContinuousAt_iff.mp hf
    have hvend : Tendsto (fun n ↦ a n + τ n • v n) atTop (𝓝 x) := by
      simpa using hat.add (hτt.smul hvt)
    have hwend : Tendsto (fun n ↦ a n + τ n • w) atTop (𝓝 x) := by
      simpa using hat.add (hτt.smul tendsto_const_nhds)
    refine ⟨τ,a,hτ,hτt,hat,hqt.congr_dist ?_⟩
    apply squeeze_zero' (g := fun n ↦ (k:ℝ) * dist (v n) w)
      (Eventually.of_forall fun _ ↦ dist_nonneg)
    · filter_upwards [hvend hU,hwend hU] with n hvn hwn
      rw [he,dist_smul₀,dist_sub_right]
      calc
        ‖(τ n)⁻¹‖ * dist (f (a n + τ n • v n)) (f (a n + τ n • w)) ≤
            ‖(τ n)⁻¹‖ * ((k:ℝ) * dist (a n + τ n • v n) (a n + τ n • w)) :=
          mul_le_mul_of_nonneg_left (hLip.dist_le_mul _ hvn _ hwn) (norm_nonneg _)
        _ = (k:ℝ) * dist (v n) w := by
          rw [dist_add_left,dist_smul₀,Real.norm_eq_abs,Real.norm_eq_abs,
            abs_of_pos (hτ n),abs_inv,abs_of_pos (hτ n)]
          field_simp [(hτ n).ne']
    · simpa using (hvt.dist (tendsto_const_nhds (x := w))).const_mul (k:ℝ)
  · rintro ⟨τ,a,hτ,hτt,hat,hqt⟩
    apply mem_strictGraphicalDerivative_iff_sequences.mpr
    refine ⟨τ,a,fun n ↦ f (a n),fun _ ↦ w,
      fun n ↦ (τ n)⁻¹ • (f (a n + τ n • w)-f (a n)),hτ,hτt,
      fun _ ↦ mem_singleton _,hat,hf.continuousAt.tendsto.comp hat,tendsto_const_nhds,hqt,?_⟩
    intro n
    exact ⟨f (a n + τ n • w),mem_singleton _,rfl⟩

/-- The fixed-direction outer-limit version of formula 9(28). -/
theorem strictGraphicalDerivative_singleton_eq_outerLimit
    {f : E → F} {x : E} (hf : StrictlyContinuousAt f x) (w : E) :
    strictGraphicalDerivative (fun a ↦ {f a}) x (f x) w =
      outerSetLimitAlong ((𝓝 x) ×ˢ (𝓝[>] (0:ℝ)))
        (fun p : E × ℝ ↦ {p.2⁻¹ • (f (p.1+p.2 • w)-f p.1)}) := by
  ext z
  rw [mem_strictGraphicalDerivative_singleton_iff_fixed_sequences hf,
    mem_outerSetLimitAlong_iff_exists_seq]
  constructor
  · rintro ⟨τ,a,hτ,hτt,hat,hqt⟩
    exact ⟨fun n ↦ (a n,τ n),_,hat.prodMk (tendsto_nhdsWithin_of_forall_mem hτ hτt),
      fun _ ↦ mem_singleton _,hqt⟩
  · rintro ⟨p,q,hpt,hmem,hqt⟩
    have hpos : ∀ᶠ n in atTop, 0 < (p n).2 := hpt.snd self_mem_nhdsWithin
    obtain ⟨N,hN⟩ := eventually_atTop.mp hpos
    refine ⟨fun n ↦ (p (n+N)).2,fun n ↦ (p (n+N)).1,
      fun n ↦ hN (n+N) (by omega),
      (hpt.snd.mono_right nhdsWithin_le_nhds).comp (tendsto_add_atTop_nat N),?_,?_⟩
    · exact hpt.fst.comp (tendsto_add_atTop_nat N)
    · convert hqt.comp (tendsto_add_atTop_nat N) using 1
      funext n
      exact (mem_singleton_iff.mp (hmem (n+N))).symm

end RW
