/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lipschitz limits determined on a dense subset
-/

import RockafellarWets.Chapter9.HilbertLipschitzExtension
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli

open Filter Metric Set Topology Bornology
open scoped NNReal

namespace RW

section Metric

variable {E F : Type*} [MetricSpace E] [MetricSpace F]
  {f : ℕ → E → F} {g : E → F} {k : ℝ≥0} {X : Set E}

/-- A pointwise limit preserves a common Lipschitz constant. -/
theorem lipschitzOnWith_of_pointwise_limit (hf : ∀ n, LipschitzOnWith k (f n) X)
    (hlim : ∀ x ∈ X, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) : LipschitzOnWith k g X := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact le_of_tendsto ((hlim x hx).dist (hlim y hy))
    (Eventually.of_forall fun n ↦ (hf n).dist_le_mul x hx y hy)

/-- Moving input points preserve convergence for a uniformly Lipschitz family. -/
theorem tendsto_lipschitz_values_of_tendsto (hf : ∀ n, LipschitzWith k (f n))
    {x : E} {v : F} (hlim : Tendsto (fun n ↦ f n x) atTop (𝓝 v))
    {z : ℕ → E} (hz : Tendsto z atTop (𝓝 x)) : Tendsto (fun n ↦ f n (z n)) atTop (𝓝 v) := by
  apply tendsto_of_tendsto_of_dist hlim
  apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (hf n).dist_le_mul x (z n))
  simpa only [dist_self,mul_zero] using (tendsto_const_nhds (x := (k:ℝ))).mul
    ((tendsto_const_nhds (x := x)).dist hz)

/-- Equicontinuity turns pointwise convergence on a compact set into uniform convergence. -/
theorem tendstoUniformlyOn_compact_of_lipschitz (hf : ∀ n, LipschitzWith k (f n))
    {K : Set E} (hK : IsCompact K) (hlim : ∀ x ∈ K, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he : Equicontinuous (fun n (z : K) ↦ f n z) :=
    (LipschitzWith.uniformEquicontinuous _ k (fun n ↦ by
      simpa only [mul_one,Function.comp_def] using (hf n).comp (isometry_subtype_coe (s := K)).lipschitz)).equicontinuous
  have hu := (he.tendsto_uniformFun_iff_pi atTop (fun z : K ↦ g z)).mpr
    (tendsto_pi_nhds.mpr fun z ↦ hlim z z.2)
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

end Metric

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {f : ℕ → E → F} {g : E → F} {k : ℝ≥0} {X D : Set E}

/-- **Proposition 9.59(a,b)**, the convergence assertion. A common Lipschitz
constant and convergence on a relatively dense subset determine a Lipschitz
limit, with uniform convergence on every bounded subset of the original set.
The limit is supplied as a global extension, so nonclosed sets cause no loss. -/
theorem exists_lipschitz_limit_of_dense (hf : ∀ n, LipschitzOnWith k (f n) X)
    (hDX : D ⊆ X) (hXD : X ⊆ closure D)
    (hlim : ∀ x ∈ D, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    ∃ G : E → F, LipschitzWith k G ∧ EqOn g G D ∧
      (∀ x ∈ X, Tendsto (fun n ↦ f n x) atTop (𝓝 (G x))) ∧
      ∀ B ⊆ X, IsBounded B → TendstoUniformlyOn f G atTop B := by
  have hg : LipschitzOnWith k g D := lipschitzOnWith_of_pointwise_limit
    (fun n ↦ (hf n).mono hDX) hlim
  obtain ⟨G,hG,heg⟩ := exists_lipschitz_extension_same_constant hg
  choose H hH heH using fun n ↦ exists_lipschitz_extension_same_constant (hf n)
  have hD (x : E) (hx : x ∈ D) : Tendsto (fun n ↦ H n x) atTop (𝓝 (G x)) := by
    rw [← heg hx]
    exact (hlim x hx).congr fun n ↦ heH n (hDX hx)
  have hcl (x : E) (hx : x ∈ closure D) : Tendsto (fun n ↦ H n x) atTop (𝓝 (G x)) :=
    ((LipschitzWith.uniformEquicontinuous H k hH).equicontinuous x).tendsto_of_mem_closure
      (hG.continuous.continuousAt.mono_left nhdsWithin_le_nhds) hD hx
  refine ⟨G,hG,heg,fun x hx ↦ (hcl x (hXD hx)).congr (fun n ↦ (heH n hx).symm),?_⟩
  intro B hBX hB
  have hu := tendstoUniformlyOn_compact_of_lipschitz hH hB.isCompact_closure
    (fun x hx ↦ hcl x (closure_minimal (hBX.trans hXD) isClosed_closure hx))
  exact (hu.mono subset_closure).congr (Eventually.of_forall fun n x hx ↦ (heH n (hBX hx)).symm)

/-- **Proposition 9.59(a,b)** with only existence of the pointwise limits
on the dense set as input. -/
theorem exists_lipschitz_limit_of_convergent_dense (hf : ∀ n, LipschitzOnWith k (f n) X)
    (hDX : D ⊆ X) (hXD : X ⊆ closure D)
    (hlim : ∀ x ∈ D, ∃ v : F, Tendsto (fun n ↦ f n x) atTop (𝓝 v)) :
    ∃ G : E → F, LipschitzWith k G ∧
      (∀ x ∈ X, Tendsto (fun n ↦ f n x) atTop (𝓝 (G x))) ∧
      ∀ B ⊆ X, IsBounded B → TendstoUniformlyOn f G atTop B := by
  classical
  have h : ∀ x, ∃ v : F, x ∈ D → Tendsto (fun n ↦ f n x) atTop (𝓝 v) := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨v,hv⟩ := hlim x hx
      exact ⟨v,fun _ ↦ hv⟩
    · exact ⟨0,fun h ↦ (hx h).elim⟩
  choose g hg using h
  obtain ⟨G,hG,_,hp,hu⟩ := exists_lipschitz_limit_of_dense hf hDX hXD hg
  exact ⟨G,hG,hp,hu⟩

end RW
