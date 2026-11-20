/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Recovery of coderivatives under graphical limits
-/

import RockafellarWets.Chapter8.GraphicalDerivatives
import RockafellarWets.Chapter6.NormalApproximation
import RockafellarWets.Chapter7.EpiDistances

open Filter Set Topology

namespace RW

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {T : ℕ → E → Set F} {x z : E} {u y : F}

/-- The primal and dual graph points converge simultaneously. The approximating
coderivatives can be chosen regular. -/
def CoderivativeRecovery (T : ℕ → E → Set F) (x : E) (u y : F) (z : E) : Prop :=
  ∃ (p : ℕ → E × F) (v : ℕ → F × E), Tendsto p atTop (𝓝 (x,u)) ∧ Tendsto v atTop (𝓝 (y,z)) ∧
    ∀ᶠ n in atTop, (p n).2 ∈ T n (p n).1 ∧ (v n).2 ∈ regularCoderivative (T n) (p n).1 (p n).2 (v n).1 ∧
      (v n).2 ∈ coderivative (T n) (p n).1 (p n).2 (v n).1

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem coderivativeRecovery_of_proximalNormals
    {p v : ℕ → WithLp 2 (E × F)}
    (hp : Tendsto p atTop (𝓝 (WithLp.toLp 2 (x,u)))) (hv : Tendsto v atTop (𝓝 (WithLp.toLp 2 (z,-y))))
    (hmem : ∀ᶠ n in atTop, v n ∈ proximalNormalCone (euclideanSvGraph (T n)) (p n)) :
    CoderivativeRecovery T x u y z := by
  refine ⟨fun n ↦ (p n).ofLp,fun n ↦ (-(v n).snd,(v n).fst),
    ((WithLp.homeomorphProd 2 E F).continuous.tendsto _).comp hp,?_,?_⟩
  · simpa using ((((WithLp.continuous_snd 2 E F).tendsto _).comp hv).neg.prodMk_nhds
      (((WithLp.continuous_fst 2 E F).tendsto _).comp hv))
  · filter_upwards [hmem] with n hn
    have hr := proximalNormalCone_subset_regularNormalCone hn
    refine ⟨hr.1,?_,?_⟩
    · simpa only [regularCoderivative,svOfEuclideanNormals,neg_neg,mem_setOf_eq] using hr
    · simpa only [coderivative,svOfEuclideanNormals,neg_neg,mem_setOf_eq] using regularNormalCone_subset_normalCone _ _ hr

/-- **Exercise 8.48.** Every coderivative of the graphical outer limit is
recovered along a subsequence of the approximating graphs. -/
theorem exists_subsequence_coderivativeRecovery (hosc : ∀ n, SvOsc (T n)) (hl : graphicalOuterLimit T = S)
    (hz : z ∈ coderivative S x u y) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ CoderivativeRecovery (T ∘ φ) x u y z := by
  have he : outerSetLimit (fun n ↦ euclideanSvGraph (T n)) = euclideanSvGraph S := by
    change outerSetLimit (fun n ↦ (WithLp.homeomorphProd 2 E F) ⁻¹' svGraph (T n)) = _
    rw [outerSetLimit_preimage_homeomorph,← svGraph_graphicalOuterLimit,hl]
    rfl
  have hcl : ∀ n, IsClosed (euclideanSvGraph (T n)) := fun n ↦
    (isClosed_svGraph_iff_svOsc.mpr (hosc n)).preimage (WithLp.homeomorphProd 2 E F).continuous
  have h := mem_graphicalOuterLimit_proximalNormalCone_of_mem_normalCone (he ▸ isClosed_outerSetLimit _)
    hcl he (show WithLp.toLp 2 (z,-y) ∈ normalCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)) from hz)
  obtain ⟨φ,p,v,hφ,hm,hp,hv⟩ := mem_graphicalOuterLimit_iff.mp h
  exact ⟨φ,hφ,coderivativeRecovery_of_proximalNormals hp hv (Eventually.of_forall hm)⟩

/-- **Exercise 8.48**, cofinite recovery under graphical convergence. -/
theorem coderivativeRecovery_of_graphicalConverges (hosc : ∀ n, SvOsc (T n)) (hl : GraphicalConverges T S)
    (hz : z ∈ coderivative S x u y) : CoderivativeRecovery T x u y z := by
  have hconv : PKConverges (fun n ↦ euclideanSvGraph (T n)) (euclideanSvGraph S) :=
    (pkConverges_preimage_homeomorph_iff (WithLp.homeomorphProd 2 E F)).mpr hl
  have hcl : ∀ n, IsClosed (euclideanSvGraph (T n)) := fun n ↦
    (isClosed_svGraph_iff_svOsc.mpr (hosc n)).preimage (WithLp.homeomorphProd 2 E F).continuous
  obtain ⟨p,v,hm,hp,hv⟩ := mem_graphicalInnerLimit_iff.mp (mem_graphicalInnerLimit_proximalNormalCone_of_mem_normalCone
    hcl hconv (show WithLp.toLp 2 (z,-y) ∈ normalCone (euclideanSvGraph S) (WithLp.toLp 2 (x,u)) from hz))
  exact coderivativeRecovery_of_proximalNormals hp hv hm

end RW
