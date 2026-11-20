/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Regular, limiting, and horizon subgradients

Definition 8.3. At finite points the regular subgradient inequality is
written with an arbitrarily small multiple of the norm. The other two
subdifferentials are its ordinary and horizon outer limits along sequences
that approach the point in both argument and function value.
-/

import RockafellarWets.Chapter5.CosmicSemicontinuity
import RockafellarWets.Chapter7.Semiderivatives

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- The filter of `f`-attentive convergence to `x` (formula 8(5)). -/
def attentiveNhds (f : E → EReal) (x : E) : Filter E :=
  𝓝 x ⊓ comap f (𝓝 (f x))

@[simp]
theorem tendsto_attentiveNhds_iff {ι : Type*} {l : Filter ι} {f : E → EReal}
    {y : ι → E} {x : E} :
    Tendsto y l (attentiveNhds f x) ↔ Tendsto y l (𝓝 x) ∧ Tendsto (f ∘ y) l (𝓝 (f x)) := by
  rw [attentiveNhds, tendsto_inf, tendsto_comap_iff]

variable [InnerProductSpace ℝ E]

/-- **Definition 8.3(a).** The regular subdifferential is supported at finite
points. Its moving affine lower bound is the epsilon form of 8(3). -/
def regularSubdifferential (f : E → EReal) (x : E) : Set E :=
  {v | ∃ c : ℝ, f x = c ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x,
    ((c + ⟪v, y - x⟫_ℝ - ε * ‖y - x‖ : ℝ) : EReal) ≤ f y}

/-- **Definition 8.3(b).** The limiting subdifferential. -/
noncomputable def subdifferential (f : E → EReal) (x : E) : Set E :=
  {v | (∃ c : ℝ, f x = c) ∧ v ∈ outerSetLimitAlong (attentiveNhds f x)
    (regularSubdifferential f)}

/-- **Definition 8.3(c).** The horizon subdifferential. The horizon cone
includes the zero vector at every finite base value. -/
noncomputable def horizonSubdifferential (f : E → EReal) (x : E) : Set E :=
  {v | (∃ c : ℝ, f x = c) ∧ v ∈ horizonOuterSetLimitAlong (attentiveNhds f x)
    (regularSubdifferential f)}

theorem subdifferential_of_finite {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    subdifferential f x = outerSetLimitAlong (attentiveNhds f x) (regularSubdifferential f) := by
  ext v
  exact ⟨And.right, fun hv ↦ ⟨⟨c, hx⟩, hv⟩⟩

theorem horizonSubdifferential_of_finite {f : E → EReal} {x : E} {c : ℝ} (hx : f x = c) :
    horizonSubdifferential f x =
      horizonOuterSetLimitAlong (attentiveNhds f x) (regularSubdifferential f) := by
  ext v
  exact ⟨And.right, fun hv ↦ ⟨⟨c, hx⟩, hv⟩⟩

end RW
