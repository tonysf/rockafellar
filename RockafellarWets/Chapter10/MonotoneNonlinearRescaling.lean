/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Monotone nonlinear rescaling

The valid inclusions in Theorem 10.19(b), with the zero-multiplier branch
specified more precisely than in the printed statement.
-/

import RockafellarWets.Chapter10.RescalingHeightSubgradients

open Set
open scoped InnerProductSpace

namespace RW
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 10.19(b)**: both limiting and horizon inclusions, retaining the
zero-outer-multiplier condition on the horizon branch. -/
theorem nonlinearRescaling_monotone_subgradients {f : E → EReal} {θ : ℝ → EReal} {x : E} {c d : ℝ}
    (hp : IsProper f) (hf : LowerSemicontinuous f) (hpθ : IsProper θ) (hθ : LowerSemicontinuous θ)
    (hm : Monotone θ) (hsup : (⨆ a : ℝ, θ a) = ⊤)
    (hx : f x = c) (hc : θ c = d) (hstrict : ∀ a : ℝ, c < a → θ c < θ a)
    (hQ : 0 ∉ subdifferential f x ∨ horizonSubdifferential θ c = {0}) :
    subdifferential (extendedRescaling θ f) x ⊆ rescalingSubgradientSet (subdifferential θ c) f x ∧
    horizonSubdifferential (extendedRescaling θ f) x ⊆ rescalingSubgradientSet (horizonSubdifferential θ c) f x := by
  have hl := lowerSemicontinuous_rescalingHeightIntegrand hp hf hpθ hθ
  have hb := isParametricallyLevelBounded_rescalingHeightIntegrand hp hf hpθ hm hsup
  have he := parametricValue_rescalingHeightIntegrand hp hpθ hm
  have hu : parametricValue (rescalingHeightIntegrand f θ) x = d := by
    rw [he,extendedRescaling_of_finite hx,hc]
  have hmin := parametricMinimizers_rescalingHeightIntegrand hp hpθ hm hx hc hstrict
  obtain ⟨hs,hh⟩ := rescalingHeightIntegrand_subgradients hf hpθ hθ hx hc hQ
  constructor
  · intro v hv
    rw [← he] at hv
    obtain ⟨a,ha,hv⟩ := subdifferential_parametricValue_subset hl hb hu hv
    have ha' : a = c := mem_singleton_iff.mp (hmin ▸ ha)
    exact hs (ha' ▸ hv)
  · intro v hv
    rw [← he] at hv
    obtain ⟨a,ha,hv⟩ := horizonSubdifferential_parametricValue_subset hl hb hu hv
    have ha' : a = c := mem_singleton_iff.mp (hmin ▸ ha)
    exact hh (ha' ▸ hv)

/-- The two printed inclusions follow from the more precise multiplier formula. -/
theorem nonlinearRescaling_monotone_printed_inclusions {f : E → EReal} {θ : ℝ → EReal} {x : E} {c d : ℝ}
    (hp : IsProper f) (hf : LowerSemicontinuous f) (hpθ : IsProper θ) (hθ : LowerSemicontinuous θ)
    (hm : Monotone θ) (hsup : (⨆ a : ℝ, θ a) = ⊤)
    (hx : f x = c) (hc : θ c = d) (hstrict : ∀ a : ℝ, c < a → θ c < θ a)
    (hQ : 0 ∉ subdifferential f x ∨ horizonSubdifferential θ c = {0}) :
    subdifferential (extendedRescaling θ f) x ⊆
      {v | ∃ t ∈ subdifferential θ c, ∃ w ∈ subdifferential f x, v = t • w} ∪ horizonSubdifferential f x ∧
    horizonSubdifferential (extendedRescaling θ f) x ⊆
      {v | ∃ t ∈ horizonSubdifferential θ c, ∃ w ∈ subdifferential f x, v = t • w} ∪ horizonSubdifferential f x := by
  obtain ⟨hs,hh⟩ := nonlinearRescaling_monotone_subgradients hp hf hpθ hθ hm hsup hx hc hstrict hQ
  exact ⟨hs.trans (rescalingSubgradientSet_subset_printed _ _ _),
    hh.trans (rescalingSubgradientSet_subset_printed _ _ _)⟩

end
end RW
