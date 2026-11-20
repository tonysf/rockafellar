/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Epigraphical nesting and approximate minimizers

Proposition 7.30. The book's definition 1(18) of the epsilon-argmin uses a
weak inequality. The project's ordinary `argmin` excludes problems of value
`⊤`. The last example shows why this convention matters in the conclusion
about cluster points.
-/

import RockafellarWets.Chapter7.MinimizationCriteria
import Mathlib.Topology.Instances.EReal.Lemmas

open Filter Metric Set Topology

namespace RW

variable {E : Type*}

/-- Approximate minimizers, formula 1(18). The tolerance is a real number. -/
def approxArgmin (f : E → EReal) (ε : ℝ) : Set E :=
  {x | f x ≤ (⨅ y, f y) + (ε : EReal)}

@[simp] theorem approxArgmin_zero {f : E → EReal} (hf : (⨅ x, f x) < ⊤) :
    approxArgmin f 0 = argmin f := by
  ext x
  simp only [approxArgmin, mem_setOf_eq, EReal.coe_zero, add_zero, mem_argmin_iff, hf,
    and_true]
  exact ⟨fun h ↦ le_antisymm h (iInf_le f x), Eq.le⟩

/-- **Proposition 7.30**, the bound on optimal values under epigraphical nesting. -/
theorem limsup_iInf_le_of_epigraph_subset_innerSetLimit [PseudoMetricSpace E]
    {f : ℕ → E → EReal} {g : E → EReal}
    (h : epigraph g ⊆ innerSetLimit (fun n ↦ epigraph (f n))) :
    limsup (fun n ↦ ⨅ x, f n x) atTop ≤ ⨅ x, g x := by
  simpa only [infimumOn_univ] using
    (epigraph_subset_innerSetLimit_iff_infimumOn_open.1 h) univ isOpen_univ

/-- The value of a sequence of approximate minimizers has upper limit at most
`a + e` if the optimal values have upper limit at most `a` and the tolerances
tend to the real number `e`. This holds on every subsequence. -/
theorem limsup_le_of_mem_approxArgmin {f : ℕ → E → EReal} {a : EReal}
    (ha : limsup (fun n ↦ ⨅ x, f n x) atTop ≤ a) {ε : ℕ → ℝ} {e : ℝ}
    (hε : Tendsto ε atTop (𝓝 e)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {xs : ℕ → E} (hxs : ∀ᶠ k in atTop, xs k ∈ approxArgmin (f (φ k)) (ε (φ k))) :
    limsup (fun k ↦ f (φ k) (xs k)) atTop ≤ a + (e : EReal) := by
  let vs : ℕ → EReal := fun k ↦ ⨅ x, f (φ k) x
  let es : ℕ → EReal := fun k ↦ (ε (φ k) : EReal)
  have he : limsup es atTop = (e : EReal) :=
    (EReal.tendsto_coe.2 (hε.comp hφ.tendsto_atTop)).limsup_eq
  have hv : limsup vs atTop ≤ a := by
    change limsup ((fun n ↦ ⨅ x, f n x) ∘ φ) atTop ≤ a
    rw [limsup_comp]
    exact (limsup_le_limsup_of_le hφ.tendsto_atTop).trans ha
  calc
    _ ≤ limsup (vs + es) atTop := limsup_le_limsup hxs
    _ ≤ limsup vs atTop + limsup es atTop :=
      EReal.limsup_add_le (.inr (he ▸ EReal.coe_ne_top _)) (.inr (he ▸ EReal.coe_ne_bot _))
    _ ≤ _ := by rw [he]; exact add_le_add hv le_rfl

/-- **Proposition 7.30**, cluster points of approximate minimizers are
minimizers when their values converge to the corresponding values of `g`.
The condition on `inf g` expresses the chapter's ordinary `argmin` convention. -/
theorem outerSetLimit_approxArgmin_subset_argmin_of_values_tendsto [PseudoMetricSpace E]
    {f : ℕ → E → EReal} {g : E → EReal}
    (hnest : epigraph g ⊆ innerSetLimit (fun n ↦ epigraph (f n)))
    (hg : (⨅ x, g x) < ⊤) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hvals : ∀ (φ : ℕ → ℕ) (xs : ℕ → E) (x : E), StrictMono φ →
      (∀ k, xs k ∈ approxArgmin (f (φ k)) (ε (φ k))) → Tendsto xs atTop (𝓝 x) →
      Tendsto (fun k ↦ f (φ k) (xs k)) atTop (𝓝 (g x))) :
    outerSetLimit (fun n ↦ approxArgmin (f n) (ε n)) ⊆ argmin g := by
  intro x hx
  obtain ⟨φ, xs, hφ, hxs, hto⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hx
  have hval := (hvals φ xs x hφ hxs hto).limsup_eq
  have hle := limsup_le_of_mem_approxArgmin
    (limsup_iInf_le_of_epigraph_subset_innerSetLimit hnest) hε hφ (Eventually.of_forall hxs)
  rw [hval, EReal.coe_zero, add_zero] at hle
  exact ⟨le_antisymm hle (iInf_le g x), hg⟩

/-- The limit problem in the last part of 7.30 may have value `⊤`. For the
constant functions `fₙ(x) = n`, every sequence of their values tends to `⊤`
and every point minimizes each `fₙ`. The limiting function has empty `argmin`. -/
theorem epigraphicalNesting_top_argmin_obstruction :
    let f := fun (n : ℕ) (_ : ℝ) ↦ ((n : ℝ) : EReal)
    let g := fun _ : ℝ ↦ (⊤ : EReal)
    epigraph g ⊆ innerSetLimit (fun n ↦ epigraph (f n)) ∧
      (∀ (φ : ℕ → ℕ) (_ : ℕ → ℝ) (x : ℝ), StrictMono φ →
        Tendsto (fun k ↦ ((φ k : ℝ) : EReal)) atTop (𝓝 (g x))) ∧
      ¬ outerSetLimit (fun n ↦ approxArgmin (f n) 0) ⊆ argmin g := by
  dsimp only
  refine ⟨?_, fun φ _ _ hφ ↦ EReal.tendsto_coe_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop), ?_⟩
  · intro p hp
    exact (EReal.coe_ne_top _ (top_unique hp)).elim
  · have hset : ∀ n : ℕ, approxArgmin (fun _ : ℝ ↦ ((n : ℝ) : EReal)) 0 = univ := by
      intro n
      simp [approxArgmin]
    simp only [hset, outerSetLimit_univ, argmin_const_top]
    simp

end RW
