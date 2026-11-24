/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Nonexpansive set-valued mappings

Section 12.B casts nonexpansivity graphically: `S : ℝⁿ ⇉ ℝⁿ` is nonexpansive if
`|w₁ - w₀| ≤ |z₁ - z₀|` whenever `w₀ ∈ S(z₀)` and `w₁ ∈ S(z₁)`, and contractive if
the inequality is moreover strict when `z₁ ≠ z₀`.  Such a mapping is
single-valued on its domain and is there a Lipschitz map with constant one, as
in 9.4; `svNonexpansive_iff_lipschitzOnWith` records the equivalence.

Exercise 12.10 shows that compositions and combinations `λ₀ S₀ + λ₁ S₁` with
`|λ₀| + |λ₁| ≤ 1` of nonexpansive mappings are nonexpansive.  Compositions and
sums are the Chapter 5 operations `svComp` and `svAdd`.
-/

import RockafellarWets.Chapter5.MappingOperations

open Set
open scoped Pointwise

namespace RW

section Nonexpansive

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

/-- A set-valued mapping is nonexpansive if `‖w₁ - w₀‖ ≤ ‖z₁ - z₀‖` whenever
`w₀ ∈ S z₀` and `w₁ ∈ S z₁`. -/
def SvNonexpansive (S : E → Set F) : Prop :=
  ∀ ⦃z₀ w₀⦄, w₀ ∈ S z₀ → ∀ ⦃z₁ w₁⦄, w₁ ∈ S z₁ → ‖w₁ - w₀‖ ≤ ‖z₁ - z₀‖

/-- A set-valued mapping is contractive if it is nonexpansive and the
inequality is strict whenever `z₁ ≠ z₀`. -/
def SvContractive (S : E → Set F) : Prop :=
  SvNonexpansive S ∧
    ∀ ⦃z₀ w₀⦄, w₀ ∈ S z₀ → ∀ ⦃z₁ w₁⦄, w₁ ∈ S z₁ → z₁ ≠ z₀ → ‖w₁ - w₀‖ < ‖z₁ - z₀‖

/-- A nonexpansive mapping is single-valued on its domain. -/
theorem SvNonexpansive.eq_of_mem {S : E → Set F} (hS : SvNonexpansive S) {x : E} {w₀ w₁ : F}
    (h₀ : w₀ ∈ S x) (h₁ : w₁ ∈ S x) : w₀ = w₁ := by
  have h := hS h₀ h₁
  rw [sub_self, norm_zero] at h
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h)).symm

theorem SvNonexpansive.eq_singleton {S : E → Set F} (hS : SvNonexpansive S) {x : E} {w : F}
    (hw : w ∈ S x) : S x = {w} :=
  Subset.antisymm (fun _ hu ↦ mem_singleton_iff.2 (hS.eq_of_mem hu hw)) (by simpa)

theorem SvNonexpansive.mono {S S' : E → Set F} (hS : SvNonexpansive S)
    (h : ∀ x, S' x ⊆ S x) : SvNonexpansive S' :=
  fun _ _ h₀ _ _ h₁ ↦ hS (h _ h₀) (h _ h₁)

/-- The graphical definition of nonexpansivity agrees with the single-valued
one of 9.4: a mapping is nonexpansive exactly when it is single-valued on its
domain and given there by a Lipschitz map with constant one. -/
theorem svNonexpansive_iff_lipschitzOnWith {S : E → Set F} :
    SvNonexpansive S ↔
      ∃ f : E → F, LipschitzOnWith 1 f (svDom S) ∧ ∀ z ∈ svDom S, S z = {f z} := by
  classical
  constructor
  · intro hS
    refine ⟨fun z ↦ if h : (S z).Nonempty then h.some else 0, ?_, fun z hz ↦ ?_⟩
    · refine LipschitzOnWith.of_dist_le_mul fun z₀ h₀ z₁ h₁ ↦ ?_
      simp only [dif_pos (show (S z₀).Nonempty from h₀), dif_pos (show (S z₁).Nonempty from h₁),
        NNReal.coe_one, one_mul, dist_eq_norm]
      exact hS h₁.some_mem h₀.some_mem
    · simp only [dif_pos (show (S z).Nonempty from hz)]
      exact hS.eq_singleton hz.some_mem
  · rintro ⟨f, hf, hS⟩ z₀ w₀ h₀ z₁ w₁ h₁
    have hz₀ : z₀ ∈ svDom S := ⟨w₀, h₀⟩
    have hz₁ : z₁ ∈ svDom S := ⟨w₁, h₁⟩
    rw [hS z₀ hz₀, mem_singleton_iff] at h₀
    rw [hS z₁ hz₁, mem_singleton_iff] at h₁
    subst h₀ h₁
    have := hf.dist_le_mul z₁ hz₁ z₀ hz₀
    simpa [dist_eq_norm] using this

/-- A single-valued mapping is nonexpansive exactly when it is Lipschitz with
constant one. -/
theorem svNonexpansive_singleton_iff {f : E → F} :
    SvNonexpansive (fun z ↦ ({f z} : Set F)) ↔ LipschitzWith 1 f := by
  constructor
  · intro hf
    refine LipschitzWith.of_dist_le_mul fun z₀ z₁ ↦ ?_
    simpa [dist_eq_norm] using hf (mem_singleton (f z₁)) (mem_singleton (f z₀))
  · intro hf z₀ w₀ h₀ z₁ w₁ h₁
    rw [mem_singleton_iff] at h₀ h₁
    subst h₀ h₁
    simpa [dist_eq_norm] using hf.dist_le_mul z₁ z₀

/-- A single-valued mapping is contractive exactly when it is Lipschitz with
constant one and strictly decreases distances between distinct points. -/
theorem svContractive_singleton_iff {f : E → F} :
    SvContractive (fun z ↦ ({f z} : Set F)) ↔
      LipschitzWith 1 f ∧ ∀ z₀ z₁, z₁ ≠ z₀ → dist (f z₁) (f z₀) < dist z₁ z₀ := by
  rw [SvContractive, svNonexpansive_singleton_iff]
  refine and_congr_right fun _ ↦ ⟨fun h z₀ z₁ hz ↦ ?_, fun h z₀ w₀ h₀ z₁ w₁ h₁ hz ↦ ?_⟩
  · simpa [dist_eq_norm] using h (mem_singleton (f z₀)) (mem_singleton (f z₁)) hz
  · rw [mem_singleton_iff] at h₀ h₁
    subst h₀ h₁
    simpa [dist_eq_norm] using h z₀ z₁ hz

/-- **Exercise 12.10(a).** The composition of nonexpansive mappings is
nonexpansive. -/
theorem SvNonexpansive.comp {S₀ : E → Set F} {S₁ : F → Set G} (h₁ : SvNonexpansive S₁)
    (h₀ : SvNonexpansive S₀) : SvNonexpansive (svComp S₁ S₀) := by
  intro z₀ w₀ hw₀ z₁ w₁ hw₁
  obtain ⟨y₀, hy₀, hw₀⟩ := mem_svComp.1 hw₀
  obtain ⟨y₁, hy₁, hw₁⟩ := mem_svComp.1 hw₁
  exact (h₁ hw₀ hw₁).trans (h₀ hy₀ hy₁)

/-- **Exercise 12.10(b).** If `|λ₀| + |λ₁| ≤ 1`, then `λ₀ S₀ + λ₁ S₁` is
nonexpansive for nonexpansive `S₀` and `S₁`. -/
theorem SvNonexpansive.linearCombination [NormedSpace ℝ F] {S₀ S₁ : E → Set F}
    (h₀ : SvNonexpansive S₀) (h₁ : SvNonexpansive S₁) {l₀ l₁ : ℝ} (hl : |l₀| + |l₁| ≤ 1) :
    SvNonexpansive (svAdd (fun z ↦ l₀ • S₀ z) (fun z ↦ l₁ • S₁ z)) := by
  intro z₀ w₀ hw₀ z₁ w₁ hw₁
  obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := mem_svAdd.1 hw₀
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := mem_svAdd.1 hw₁
  obtain ⟨c₀, hc₀, rfl⟩ := mem_smul_set.1 ha₀
  obtain ⟨c₁, hc₁, rfl⟩ := mem_smul_set.1 ha₁
  obtain ⟨d₀, hd₀, rfl⟩ := mem_smul_set.1 hb₀
  obtain ⟨d₁, hd₁, rfl⟩ := mem_smul_set.1 hb₁
  have e : l₀ • c₁ + l₁ • d₁ - (l₀ • c₀ + l₁ • d₀) = l₀ • (c₁ - c₀) + l₁ • (d₁ - d₀) := by
    rw [smul_sub, smul_sub]; abel
  rw [e]
  have hc := h₀ hc₀ hc₁
  have hd := h₁ hd₀ hd₁
  calc ‖l₀ • (c₁ - c₀) + l₁ • (d₁ - d₀)‖
      ≤ ‖l₀ • (c₁ - c₀)‖ + ‖l₁ • (d₁ - d₀)‖ := norm_add_le _ _
    _ = |l₀| * ‖c₁ - c₀‖ + |l₁| * ‖d₁ - d₀‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ |l₀| * ‖z₁ - z₀‖ + |l₁| * ‖z₁ - z₀‖ := by gcongr
    _ = (|l₀| + |l₁|) * ‖z₁ - z₀‖ := by ring
    _ ≤ 1 * ‖z₁ - z₀‖ := by gcongr
    _ = ‖z₁ - z₀‖ := one_mul _

end Nonexpansive

end RW
