/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fixed-covector coderivative recovery for Lipschitz limits
-/

import RockafellarWets.Chapter9.LipschitzSubgradientLimits
import RockafellarWets.Chapter9.CoderivativeScalarization

open Filter Metric Set Topology
open scoped NNReal InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Proposition 9.59(b)**, coderivative recovery with the covector held
fixed. All indices are represented, and the base points stay in the interior
of the original set. -/
theorem exists_coderivative_recovery_of_lipschitz_limit {f : ℕ → E → F} {g : E → F}
    {X : Set E} {k : ℝ≥0} (hf : ∀ n, LipschitzOnWith k (f n) X)
    (hlim : ∀ x ∈ X, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    {x v : E} (hx : x ∈ interior X) (w : F) (hv : v ∈ coderivative (svSingleton g) x (g x) w) :
    ∃ y z : ℕ → E, Tendsto y atTop (𝓝 x) ∧ Tendsto z atTop (𝓝 v) ∧
      ∀ n, y n ∈ interior X ∧ z n ∈ coderivative (svSingleton (f n)) (y n) (f n (y n)) w := by
  have hg := lipschitzOnWith_of_pointwise_limit hf hlim
  have hgstrict : StrictlyContinuousAt g x :=
    strictlyContinuousAt_iff.mpr ⟨k,X,mem_interior_iff_mem_nhds.mp hx,hg⟩
  rw [coderivative_svSingleton_eq_subdifferential hgstrict w] at hv
  have hscalar (n : ℕ) : LipschitzOnWith (‖innerSL ℝ w‖₊ * k) (fun a ↦ ⟪w,f n a⟫_ℝ) X :=
    (innerSL ℝ w).lipschitz.comp_lipschitzOnWith (hf n)
  have hpoint (a : E) (ha : a ∈ X) :
      Tendsto (fun n ↦ ⟪w,f n a⟫_ℝ) atTop (𝓝 ⟪w,g a⟫_ℝ) :=
    ((innerSL ℝ w).continuous.tendsto (g a)).comp (hlim a ha)
  obtain ⟨y,z,hy,hz,hm⟩ := exists_subgradient_recovery_of_lipschitz_limit hscalar hpoint hx hv
  refine ⟨y,z,hy,hz,fun n ↦ ⟨(hm n).1,?_⟩⟩
  have hn : StrictlyContinuousAt (f n) (y n) :=
    strictlyContinuousAt_iff.mpr ⟨k,X,mem_interior_iff_mem_nhds.mp (hm n).1,hf n⟩
  rw [coderivative_svSingleton_eq_subdifferential hn w]
  exact (hm n).2

/-- **Proposition 9.59(b)**, both conclusions for one common limit. -/
theorem exists_lipschitz_limit_and_coderivative_recovery {f : ℕ → E → F} {X D : Set E}
    {k : ℝ≥0} (hf : ∀ n, LipschitzOnWith k (f n) X) (hDX : D ⊆ X) (hXD : X ⊆ closure D)
    (hlim : ∀ x ∈ D, ∃ v : F, Tendsto (fun n ↦ f n x) atTop (𝓝 v)) :
    ∃ g : E → F, LipschitzWith k g ∧
      (∀ B ⊆ X, Bornology.IsBounded B → TendstoUniformlyOn f g atTop B) ∧
      ∀ x ∈ interior X, ∀ w : F, ∀ v ∈ coderivative (svSingleton g) x (g x) w,
        ∃ y z : ℕ → E, Tendsto y atTop (𝓝 x) ∧ Tendsto z atTop (𝓝 v) ∧
          ∀ n, y n ∈ interior X ∧ z n ∈ coderivative (svSingleton (f n)) (y n) (f n (y n)) w := by
  obtain ⟨g,hg,hpoint,hu⟩ := exists_lipschitz_limit_of_convergent_dense hf hDX hXD hlim
  exact ⟨g,hg,hu,fun x hx w v hv ↦ exists_coderivative_recovery_of_lipschitz_limit hf hpoint hx w hv⟩

end RW
