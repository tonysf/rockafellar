/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite infima with a common base value
-/
import RockafellarWets.Chapter10.SubderivativeSmoothAddition
import Mathlib.Topology.Order.Lattice

open Set Filter Topology
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Difference quotients have the same germ when the functions agree near
both the base point and the approaching argument. -/
theorem differenceQuotient_eventuallyEq_of_eventuallyEq {f g : E → EReal} {x w : E}
    (he : f =ᶠ[𝓝 x] g) :
    (fun p : ℝ × E ↦ differenceQuotient f x p.1 p.2) =ᶠ[𝓝[>] (0 : ℝ) ×ˢ 𝓝 w]
      (fun p ↦ differenceQuotient g x p.1 p.2) := by
  have ht : Tendsto (Prod.fst : ℝ × E → ℝ) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 0) :=
    tendsto_fst.mono_right nhdsWithin_le_nhds
  have hy : Tendsto (fun p : ℝ × E ↦ x+p.1 • p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 x) := by
    simpa using (tendsto_const_nhds (x := x)).add (ht.smul tendsto_snd)
  filter_upwards [hy.eventually he] with p hp
  simp only [differenceQuotient,hp,he.self_of_nhds]

theorem subderivative_congr_nhds {f g : E → EReal} {x : E}
    (he : f =ᶠ[𝓝 x] g) (w : E) : subderivative f x w = subderivative g x w :=
  Filter.liminf_congr (differenceQuotient_eventuallyEq_of_eventuallyEq he)

theorem HasOneSidedDirDeriv.congr_nhds {f g : E → EReal} {x w : E} {d : EReal}
    (hf : HasOneSidedDirDeriv f x w d) (he : f =ᶠ[𝓝 x] g) : HasOneSidedDirDeriv g x w d := by
  refine ⟨he.self_of_nhds ▸ hf.1,he.self_of_nhds ▸ hf.2.1,?_⟩
  exact hf.2.2.congr' ((tendsto_pair_const w).eventually
    (differenceQuotient_eventuallyEq_of_eventuallyEq he))

/-- At a common finite base value, positive difference quotients commute
with nonempty finite infima. -/
theorem differenceQuotient_finset_inf' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → E → EReal} {x : E} {c : ℝ} (hx : ∀ i ∈ s, f i x = c)
    {t : ℝ} (ht : 0 < t) (w : E) :
    differenceQuotient (fun y ↦ s.inf' hs (fun i ↦ f i y)) x t w =
      s.inf' hs (fun i ↦ differenceQuotient (f i) x t w) := by
  have hbase : s.inf' hs (fun i ↦ f i x) = (c : EReal) := Finset.inf'_eq_of_forall hs _ hx
  have hmono : Monotone (fun a : EReal ↦ (t⁻¹ : ℝ) * (a-(c:EReal))) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left (show a-(c:EReal) ≤ b-(c:EReal) from add_le_add hab le_rfl) (by positivity)
  unfold differenceQuotient
  dsimp only
  rw [hbase,Finset.comp_inf'_eq_inf'_comp hs (fun a : EReal ↦ (t⁻¹ : ℝ) * (a-(c:EReal)))
    (fun a b ↦ hmono.map_inf a b)]
  apply Finset.inf'_congr hs rfl
  intro i hi
  simp only [Function.comp_def,hx i hi]

/-- The subderivative of a nonempty finite minimum with a common base
value is the minimum of the subderivatives. -/
theorem subderivative_finset_inf' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → E → EReal} {x w : E} {c : ℝ} (hx : ∀ i ∈ s, f i x = c) :
    subderivative (fun y ↦ s.inf' hs (fun i ↦ f i y)) x w =
      s.inf' hs (fun i ↦ subderivative (f i) x w) := by
  have he : (fun p : ℝ × E ↦ differenceQuotient (fun y ↦ s.inf' hs (fun i ↦ f i y)) x p.1 p.2) =ᶠ[𝓝[>] (0 : ℝ) ×ˢ 𝓝 w]
      (fun p ↦ s.inf' hs (fun i ↦ differenceQuotient (f i) x p.1 p.2)) := by
    filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p hp
    exact differenceQuotient_finset_inf' s hs hx hp p.2
  unfold subderivative
  rw [Filter.liminf_congr he,liminf_finset_inf' hs]

/-- The analogous limit rule for one-sided directional derivatives. -/
theorem HasOneSidedDirDeriv.finset_inf' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → E → EReal} {x w : E} {c : ℝ} {d : ι → EReal}
    (hx : ∀ i ∈ s, f i x = c) (hd : ∀ i ∈ s, HasOneSidedDirDeriv (f i) x w (d i)) :
    HasOneSidedDirDeriv (fun y ↦ s.inf' hs (fun i ↦ f i y)) x w (s.inf' hs d) := by
  have hbase : s.inf' hs (fun i ↦ f i x) = (c : EReal) := Finset.inf'_eq_of_forall hs _ hx
  refine ⟨by dsimp only; rw [hbase]; exact EReal.coe_ne_bot _,
    by dsimp only; rw [hbase]; exact EReal.coe_ne_top _,?_⟩
  apply (Filter.Tendsto.finset_inf'_nhds_apply hs (fun i hi ↦ (hd i hi).2.2)).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (differenceQuotient_finset_inf' s hs hx ht w).symm

end RW
