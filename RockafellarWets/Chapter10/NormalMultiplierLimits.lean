/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closedness of normal multiplier images under a kernel qualification
-/
import RockafellarWets.Chapter10.AmenableCompositionNeighborhoods

open Set Filter Topology

namespace RW
variable {E F G : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A convergent sequence of images of normal multipliers has a normal
multiplier at the limit if the kernel qualification excludes escape to infinity. -/
theorem mem_image_normalCone_of_tendsto {D : Set F} (hD : IsClosed D)
    {f : E → F} {A : E → F →L[ℝ] G} {x : E}
    (hf : ContinuousAt f x) (hA : ContinuousAt A x)
    (hQ : ∀v ∈ normalCone D (f x), A x v = 0 → v = 0)
    {ys : ℕ → E} {us : ℕ → G} {u : G} (hy : Tendsto ys atTop (𝓝 x))
    (hu : Tendsto us atTop (𝓝 u)) (hm : ∀n, us n ∈ A (ys n) '' normalCone D (f (ys n))) :
    u ∈ A x '' normalCone D (f x) := by
  choose v hv he using hm
  obtain ⟨a,z,φ,hφ,ha,hsum,hat,hzt⟩ := exists_normalized_multiplier_subsequence (fun _ ↦ 1) v (fun _ ↦ by norm_num)
  have hyφ := hy.comp hφ.tendsto_atTop
  have hfφ := hf.tendsto.comp hyφ
  have hxD : f x ∈ D := hD.mem_of_tendsto hfφ (.of_forall (fun n ↦ (hv (φ n)).1))
  have hzN : z ∈ normalCone D (f x) := by
    apply mem_normalCone_of_tendsto hxD (fun n ↦ (hv (φ n)).1) hfφ ?_ hzt
    intro n
    exact (isCone_normalCone (hv (φ n)).1).2 (hv (φ n)) (by positivity)
  have hAt : Tendsto (fun n ↦ A (ys (φ n)) ((1+‖v (φ n)‖)⁻¹ • v (φ n))) atTop (𝓝 (A x z)) :=
    ((continuous_fst.clm_apply continuous_snd : Continuous (fun p : (F →L[ℝ] G) × F ↦ p.1 p.2)).tendsto (A x,z)).comp
      ((hA.tendsto.comp hyφ).prodMk_nhds hzt)
  have hright : Tendsto (fun n ↦ (1/(1+‖v (φ n)‖)) • us (φ n)) atTop (𝓝 (a • u)) :=
    hat.smul (hu.comp hφ.tendsto_atTop)
  have hAz : A x z = a • u := tendsto_nhds_unique hAt (hright.congr (fun n ↦ by simp only [map_smul,he,one_div]))
  have hapos : 0 < a := by
    apply lt_of_le_of_ne ha
    intro heq
    have hz0 := hQ z hzN (by simpa only [← heq,zero_smul] using hAz)
    simp only [hz0,norm_zero,add_zero] at hsum
    linarith
  refine ⟨a⁻¹ • z,(isCone_normalCone hxD).2 hzN (inv_pos.mpr hapos),?_⟩
  rw [map_smul,hAz,smul_smul,inv_mul_cancel₀ hapos.ne',one_smul]

end RW
