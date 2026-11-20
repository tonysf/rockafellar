/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Regular subderivatives of indicators
-/

import RockafellarWets.Chapter8.RegularSubderivatives

open Filter Function Set Topology

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Independent selections for the two factors give the regular tangent
cone of an ordinary Cartesian product. -/
theorem regularTangentCone_prod {C : Set E} {D : Set F} {x : E} {y : F} (hx : x ∈ C) (hy : y ∈ D) :
    regularTangentCone (C ×ˢ D) (x, y) = regularTangentCone C x ×ˢ regularTangentCone D y := by
  ext ⟨u, v⟩
  rw [mem_regularTangentCone_iff_forall_sequences (mk_mem_prod hx hy), mem_prod,
    mem_regularTangentCone_iff_forall_sequences hx, mem_regularTangentCone_iff_forall_sequences hy]
  constructor
  · intro h
    constructor
    · intro s z hs hs0 hz hzx
      obtain ⟨p, hp, ht, hv⟩ := h s (fun n ↦ (z n, y)) hs hs0 (fun n ↦ mk_mem_prod (hz n) hy)
        (hzx.prodMk_nhds tendsto_const_nhds)
      exact ⟨fun n ↦ (p n).1, fun n ↦ (hp n).1, (continuous_fst.tendsto _).comp ht,
        (continuous_fst.tendsto _).comp hv⟩
    · intro s z hs hs0 hz hzy
      obtain ⟨p, hp, ht, hv⟩ := h s (fun n ↦ (x, z n)) hs hs0 (fun n ↦ mk_mem_prod hx (hz n))
        (tendsto_const_nhds.prodMk_nhds hzy)
      exact ⟨fun n ↦ (p n).2, fun n ↦ (hp n).2, (continuous_snd.tendsto _).comp ht,
        (continuous_snd.tendsto _).comp hv⟩
  · rintro ⟨hu, hv⟩ s z hs hs0 hz hzt
    obtain ⟨p, hp, hpt, hpu⟩ := hu s (fun n ↦ (z n).1) hs hs0 (fun n ↦ (hz n).1)
      ((continuous_fst.tendsto _).comp hzt)
    obtain ⟨q, hq, hqt, hqv⟩ := hv s (fun n ↦ (z n).2) hs hs0 (fun n ↦ (hz n).2)
      ((continuous_snd.tendsto _).comp hzt)
    exact ⟨fun n ↦ (p n, q n), fun n ↦ mk_mem_prod (hp n) (hq n), hpt.prodMk_nhds hqt,
      hpu.prodMk_nhds hqv⟩

theorem regularTangentCone_Ici_zero : regularTangentCone (Ici (0 : ℝ)) 0 = Ici 0 := by
  ext w
  rw [mem_regularTangentCone_iff_forall_sequences (self_mem_Ici (a := (0 : ℝ)))]
  constructor
  · intro h
    let s := fun n : ℕ ↦ 1 / ((n : ℝ) + 1)
    have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
    obtain ⟨p, hp, _, ht⟩ := h s (fun _ ↦ 0) hs tendsto_one_div_add_atTop_nhds_zero_nat
      (fun _ ↦ self_mem_Ici) tendsto_const_nhds
    exact ge_of_tendsto' ht fun n ↦ by simpa using mul_nonneg (inv_nonneg.mpr (hs n).le) (hp n)
  · intro hw s z hs hs0 hz hzt
    refine ⟨fun n ↦ z n + s n * w, fun n ↦ add_nonneg (hz n) (mul_nonneg (hs n).le hw), ?_, ?_⟩
    · simpa using hzt.add (hs0.mul_const w)
    · simpa only [add_sub_cancel_left, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (hs _).ne', one_mul] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ w) atTop (𝓝 w))

/-- **Theorem 8.17(b)** for an arbitrary set, including a nonclosed set. -/
theorem regularSubderivative_indicatorVA {C : Set E} {x : E} (hx : x ∈ C) :
    regularSubderivative (indicatorVA C) x = indicatorVA (regularTangentCone C x) := by
  have hval : indicatorVA C x = ((0 : ℝ) : EReal) := by simp [hx]
  have hl : LowerSemicontinuousAt (indicatorVA C) x := by
    intro a ha
    rw [hval] at ha
    exact Eventually.of_forall fun y ↦ ha.trans_le (by by_cases hy : y ∈ C <;> simp [hy])
  apply eq_of_epigraph_eq
  rw [epigraph_regularSubderivative_eq_regularTangentCone hval hl, epigraph_indicatorVA,
    epigraph_indicatorVA, regularTangentCone_prod hx self_mem_Ici, regularTangentCone_Ici_zero]

end RW
