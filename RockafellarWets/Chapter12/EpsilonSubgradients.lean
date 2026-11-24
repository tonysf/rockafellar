/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 12: Strict continuity of ε-subgradient mappings

Proposition 12.68.  For a proper lsc convex `f` and `ε > 0`, the ε-subgradients
`∂_ε f(x) = {v | f(x') ≥ f(x) + ⟪v, x' - x⟫ - ε for all x'}` form the set
`{v | f(x) + f*(v) - ⟪v, x⟫ ≤ ε} = ε-argmin (f* - ⟪·, x⟫)` described before the
proposition (`epsSubdifferential_eq_approxArgmin`).

**Correction.**  The book bounds `dl̂_ρ(∂_ε f(x'), ∂_ε f(x))` by
`(2ρ/ε)(ρ + ε)|x' - x|` when `|x' - x| < ε/(ρ + ε)`, citing a form of Theorem 7.69 with the
factor `2ρ/ε`.  The printed 7.69 (formalized in `ApproximateSolutionEstimates`)
gives `(1 + 4ρε⁻¹) dl̂⁺_ρ`, and the printed constant of 12.68 is false: for
`f = |·|` on `ℝ`, `ρ₀ = 1`, `ε = 1/10`, `ρ = 6/5`, `x = 1/20`, `x' = 3/50`, one
has `∂_ε f(x) ∋ -1` while `∂_ε f(x') ⊂ [-2/3, ∞)`, so the distance is at least
`1/3 > 0.312 = (2ρ/ε)(ρ + ε)|x' - x|` (`epsSubdifferential_printed_bound_fails`).

What holds, by the book's argument with the printed 7.69, is
`dl̂_ρ(∂_ε f(x'), ∂_ε f(x)) ≤ ρ(1 + 4ρ/ε)|x' - x|` for all `x, x' ∈ X` and every
`ρ ≥ ρ₀`: the functions `g_i = f* - ⟪·, x_i⟫` have `inf g_i = -f(x_i) ≥ -ρ₀`, their
minimizers `∂f(x_i)` meet `ρ₀B`, and `dl̂⁺_ρ(g₁, g₂) ≤ ρ|x₁ - x₂|`.  Through the
comparison 4.37 of `dl_ρ` with `dl̂_{2ρ+ρ₀}` this gives the strict continuity of
`∂_ε f` relative to `X` (Definition 9.28), the qualitative conclusion of 12.68.
The hypothesis `d(0, ∂f(x)) ≤ ρ₀` is read with the book's convention
`d(0, ∅) = ∞`, as the existence of `v ∈ ∂f(x)` with `|v| ≤ ρ₀`.
-/

import RockafellarWets.Chapter7.ApproximateSolutionEstimates
import RockafellarWets.Chapter9.SetValuedLipschitz
import RockafellarWets.Chapter11.SubgradientConjugacy
import RockafellarWets.Chapter11.FenchelMoreau
import RockafellarWets.Chapter11.ProximalTransform
import RockafellarWets.Chapter11.ProductConjugacy
import RockafellarWets.Chapter12.StrongConvexity

open Set Filter Topology Metric
open scoped InnerProductSpace NNReal ENNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The ε-subgradients of a (convex) function, as defined before Proposition
12.68. -/
def epsSubdifferential (f : E → EReal) (ε : ℝ) (x : E) : Set E :=
  {v | ∀ y, f x + ((⟪v, y - x⟫_ℝ - ε : ℝ) : EReal) ≤ f y}

/-- The tilted conjugate `v ↦ f*(v) - ⟪v, x⟫`. -/
noncomputable def tiltedConjugate (f : E → EReal) (x v : E) : EReal :=
  fenchelConjugate f v - ((⟪v, x⟫_ℝ : ℝ) : EReal)

/-- `v ∈ ∂_ε f(x)` exactly when `f*(v) ≤ ⟪v, x⟫ - f(x) + ε`, i.e.
`f(x) + f*(v) - ⟪v, x⟫ ≤ ε`, at a point where `f` is finite. -/
theorem mem_epsSubdifferential_iff {f : E → EReal} {ε : ℝ} {x v : E} {c : ℝ}
    (hx : f x = c) :
    v ∈ epsSubdifferential f ε x ↔ fenchelConjugate f v ≤ ((⟪v, x⟫_ℝ - c + ε : ℝ) : EReal) := by
  rw [fenchelConjugate_le_coe_iff]
  simp only [epsSubdifferential, mem_setOf_eq, hx, ← EReal.coe_add]
  refine forall_congr' fun y ↦ ?_
  rw [inner_sub_right]
  constructor <;> intro h <;> convert h using 2 <;> ring

/-- The tilted conjugate is the conjugate of the translate `f(· + x)`. -/
theorem tiltedConjugate_eq_fenchelConjugate (f : E → EReal) (x : E) :
    tiltedConjugate f x = fenchelConjugate (fun z ↦ f (z + x)) := by
  funext v
  rw [tiltedConjugate, fenchelConjugate, fenchelConjugate, sub_eq_add_neg, ← EReal.coe_neg,
    ereal_iSup_add]
  refine le_antisymm (iSup_le fun y ↦ ?_) (iSup_le fun z ↦ ?_)
  · refine le_iSup_of_le (y - x) (le_of_eq ?_)
    rw [sub_add_cancel]
    induction f y using EReal.rec with
    | bot => simp
    | top => simp
    | coe a =>
      norm_cast
      rw [inner_sub_right]
      ring
  · refine le_iSup_of_le (z + x) (le_of_eq ?_)
    induction f (z + x) using EReal.rec with
    | bot => simp
    | top => simp
    | coe a =>
      norm_cast
      rw [inner_add_right]
      ring

theorem convex_epigraph_tiltedConjugate (f : E → EReal) (x : E) :
    Convex ℝ (epigraph (tiltedConjugate f x)) := by
  rw [tiltedConjugate_eq_fenchelConjugate]
  exact convex_epigraph_fenchelConjugate _

theorem lowerSemicontinuous_tiltedConjugate (f : E → EReal) (x : E) :
    LowerSemicontinuous (tiltedConjugate f x) := by
  rw [tiltedConjugate_eq_fenchelConjugate]
  exact lowerSemicontinuous_fenchelConjugate _

theorem ereal_neg_coe_sub_eq_sub_coe (r : ℝ) (a : EReal) :
    -((r : EReal) - a) = a - (r : EReal) := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe a => rw [← EReal.coe_sub, ← EReal.coe_neg, ← EReal.coe_sub]; congr 1; ring

theorem ereal_neg_iSup' {ι : Sort*} (g : ι → EReal) : -(⨆ i, g i) = ⨅ i, -g i := by
  have h := ereal_neg_iInf (fun i ↦ -g i)
  simp only [neg_neg] at h
  rw [← h, neg_neg]

section ProperFunctions

variable [FiniteDimensional ℝ E]

/-- For proper lsc convex `f`, `inf_v (f*(v) - ⟪v, x⟫) = -f**(x) = -f(x)`. -/
theorem iInf_tiltedConjugate {f : E → EReal} (hp : IsProper f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ (epigraph f)) (x : E) : (⨅ v, tiltedConjugate f x v) = -f x := by
  have hbi := congrFun (fenchelConjugate_fenchelConjugate_eq hp hl hc) x
  rw [← hbi, fenchelConjugate, ereal_neg_iSup']
  refine iInf_congr fun v ↦ ?_
  rw [tiltedConjugate, ereal_neg_coe_sub_eq_sub_coe, real_inner_comm]

/-- **Before 12.68**: `∂_ε f(x) = ε-argmin_v {f*(v) - ⟪v, x⟫}` for proper lsc
convex `f` at a point of `dom f`. -/
theorem epsSubdifferential_eq_approxArgmin {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {ε : ℝ} {x : E} {c : ℝ}
    (hx : f x = c) : epsSubdifferential f ε x = approxArgmin (tiltedConjugate f x) ε := by
  ext v
  rw [mem_epsSubdifferential_iff hx, approxArgmin, mem_setOf_eq, iInf_tiltedConjugate hp hl hc,
    hx, tiltedConjugate, ← EReal.coe_neg, ← EReal.coe_add,
    EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
    ← EReal.coe_add]
  constructor <;> intro h <;> convert h using 2 <;> ring

theorem subdifferential_subset_epsSubdifferential {f : E → EReal} (hp : IsProper f)
    (hc : Convex ℝ (epigraph f)) {ε : ℝ} (hε : 0 ≤ ε) {x : E} {c : ℝ} (hx : f x = c) :
    subdifferential f x ⊆ epsSubdifferential f ε x := by
  intro v hv y
  have h := (mem_subdifferential_iff_of_convex hc hp hx).1 hv y
  rw [hx, ← EReal.coe_add]
  exact (EReal.coe_le_coe_iff.2 (by linarith)).trans h

theorem isClosed_epsSubdifferential {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) (ε : ℝ) {x : E} {c : ℝ}
    (hx : f x = c) : IsClosed (epsSubdifferential f ε x) := by
  rw [epsSubdifferential_eq_approxArgmin hp hl hc hx]
  exact (lowerSemicontinuous_tiltedConjugate f x).isClosed_preimage _

omit [FiniteDimensional ℝ E] in
/-- The auxiliary epi-distance between two tilted conjugates is at most
`ρ|x₁ - x₂|`, by comparing each function with the other at the same point. -/
theorem auxEpiDistance_tiltedConjugate_le (f : E → EReal) (ρ : ℝ≥0) (x₁ x₂ : E) :
    auxEpiDistance ρ (tiltedConjugate f x₁) (tiltedConjugate f x₂) ≤ ρ * ‖x₁ - x₂‖ := by
  have hdir : ∀ a b : E, auxEpiComparison ρ (tiltedConjugate f a) (tiltedConjugate f b)
      (ρ * ‖a - b‖) := by
    intro a b v hv
    refine ⟨v, by rw [dist_self]; positivity, ?_⟩
    have hv' : ‖v‖ ≤ ρ := by simpa using hv
    have e : tiltedConjugate f b v = tiltedConjugate f a v + ((⟪v, a - b⟫_ℝ : ℝ) : EReal) := by
      simp only [tiltedConjugate]
      induction fenchelConjugate f v using EReal.rec with
      | bot => simp
      | top => simp
      | coe r =>
        rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_eq_coe_iff,
          inner_sub_right]
        ring
    rw [e]
    have hin : ⟪v, a - b⟫_ℝ ≤ ρ * ‖a - b‖ :=
      (real_inner_le_norm v (a - b)).trans (mul_le_mul_of_nonneg_right hv' (norm_nonneg _))
    exact add_le_add (le_max_left _ _) (EReal.coe_le_coe_iff.2 hin)
  have hadm : auxEpiAdmissible ρ (tiltedConjugate f x₁) (tiltedConjugate f x₂) (ρ * ‖x₁ - x₂‖) :=
    ⟨by positivity, hdir x₁ x₂, by rw [norm_sub_rev]; exact hdir x₂ x₁⟩
  exact csInf_le (auxEpiAdmissible_bddBelow _ _ _) hadm

/-- **Proposition 12.68**, corrected estimate: if `f` is proper lsc convex, `ε > 0`
and `f(x) ≤ ρ₀` and `d(0, ∂f(x)) ≤ ρ₀` on `X`, then for every `ρ ≥ ρ₀`,
`dl̂_ρ(∂_ε f(x'), ∂_ε f(x)) ≤ ρ(1 + 4ρ/ε)|x' - x|` for all `x, x' ∈ X`. -/
theorem rhoHatDistance_epsSubdifferential_le {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {ε : ℝ} (hε : 0 < ε)
    {X : Set E} {ρ₀ : ℝ≥0}
    (hX : ∀ x ∈ X, f x ≤ ((ρ₀ : ℝ) : EReal) ∧ ∃ v ∈ subdifferential f x, ‖v‖ ≤ ρ₀)
    {ρ : ℝ≥0} (hρ : ρ₀ ≤ ρ) {x x' : E} (hx : x ∈ X) (hx' : x' ∈ X) :
    rhoHatDistance ρ (epsSubdifferential f ε x') (epsSubdifferential f ε x) ≤
      ρ * (1 + 4 * ρ / ε) * ‖x' - x‖ := by
  -- finite values on `X`
  have hfin : ∀ z ∈ X, ∃ c : ℝ, f z = c ∧ c ≤ ρ₀ := by
    intro z hz
    obtain ⟨hle, -⟩ := hX z hz
    have hne : f z ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
    refine ⟨(f z).toReal, (EReal.coe_toReal hne (hp.2 z).ne').symm, ?_⟩
    have := EReal.toReal_le_toReal hle (hp.2 z).ne' (EReal.coe_ne_top _)
    simpa using this
  obtain ⟨c, hcx, hcρ⟩ := hfin x hx
  obtain ⟨c', hcx', hcρ'⟩ := hfin x' hx'
  have hdata : ∀ z ∈ X, ∀ a : ℝ, f z = a →
      IsProper (tiltedConjugate f z) ∧ (⨅ v, tiltedConjugate f z v) = ((-a : ℝ) : EReal) ∧
        (argmin (tiltedConjugate f z) ∩ closedBall (0 : E) (ρ₀ : ℝ)).Nonempty := by
    intro z hz a ha
    have hinf : (⨅ v, tiltedConjugate f z v) = ((-a : ℝ) : EReal) := by
      rw [iInf_tiltedConjugate hp hl hc, ha, EReal.coe_neg]
    have hprop : IsProper (tiltedConjugate f z) := by
      have := isProper_sub_coe (isProper_fenchelConjugate hp hl hc) (fun v ↦ ⟪v, z⟫_ℝ)
      exact this
    refine ⟨hprop, hinf, ?_⟩
    obtain ⟨-, v, hv, hvρ⟩ := hX z hz
    refine ⟨v, ⟨?_, ?_⟩, by simpa using hvρ⟩
    · have heq := (mem_subdifferential_iff_fenchelConjugate_eq hp hc ha).1 hv
      rw [hinf, tiltedConjugate, heq, ← EReal.coe_sub]
      congr 1
      ring
    · rw [hinf]
      exact EReal.coe_lt_top _
  obtain ⟨hp₁, hinf₁, hmin₁⟩ := hdata x' hx' c' hcx'
  obtain ⟨hp₂, hinf₂, hmin₂⟩ := hdata x hx c hcx
  have h769 := rhoHatDistance_approxArgmin_le_of_convex hp₁ hp₂
    (convex_epigraph_tiltedConjugate f x') (convex_epigraph_tiltedConjugate f x) hinf₁ hinf₂ hρ
    hmin₁ hmin₂ (by linarith) (by linarith) hε
  rw [epsSubdifferential_eq_approxArgmin hp hl hc hcx',
    epsSubdifferential_eq_approxArgmin hp hl hc hcx]
  have haux := auxEpiDistance_tiltedConjugate_le f ρ x' x
  calc rhoHatDistance ρ (approxArgmin (tiltedConjugate f x') ε)
        (approxArgmin (tiltedConjugate f x) ε)
      ≤ (1 + 4 * (ρ : ℝ) / ε) * auxEpiDistance ρ (tiltedConjugate f x') (tiltedConjugate f x) :=
        h769.1.trans h769.2
    _ ≤ (1 + 4 * (ρ : ℝ) / ε) * ((ρ : ℝ) * ‖x' - x‖) :=
        mul_le_mul_of_nonneg_left haux (by positivity)
    _ = (ρ : ℝ) * (1 + 4 * (ρ : ℝ) / ε) * ‖x' - x‖ := by ring

/-- **Proposition 12.68 (strict continuity of ε-subgradient mappings)**, in the
corrected form: for proper lsc convex `f`, `ε > 0` and `X` on which `f ≤ ρ₀` and
`d(0, ∂f(x)) ≤ ρ₀`, every `ρ ≥ ρ₀` gives
`dl̂_ρ(∂_ε f(x'), ∂_ε f(x)) ≤ ρ(1 + 4ρ/ε)|x' - x|` on `X`, and `∂_ε f` is strictly
continuous relative to `X`. -/
theorem strict_continuity_of_epsSubdifferential {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) {ε : ℝ} (hε : 0 < ε)
    {X : Set E} {ρ₀ : ℝ≥0}
    (hX : ∀ x ∈ X, f x ≤ ((ρ₀ : ℝ) : EReal) ∧ ∃ v ∈ subdifferential f x, ‖v‖ ≤ ρ₀) :
    (∀ ρ : ℝ≥0, ρ₀ ≤ ρ → ∀ x ∈ X, ∀ x' ∈ X,
      rhoHatDistance ρ (epsSubdifferential f ε x') (epsSubdifferential f ε x) ≤
        ρ * (1 + 4 * ρ / ε) * ‖x' - x‖) ∧
      SvStrictlyContinuousOn (epsSubdifferential f ε) X := by
  refine ⟨fun ρ hρ x hx x' hx' ↦ rhoHatDistance_epsSubdifferential_le hp hl hc hε hX hρ hx hx',
    fun xb hxb ↦ ?_⟩
  have hfin : ∀ z ∈ X, ∃ c : ℝ, f z = c := by
    intro z hz
    have hne : f z ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hX z hz).1
    exact ⟨(f z).toReal, (EReal.coe_toReal hne (hp.2 z).ne').symm⟩
  have hnc : ∀ z ∈ X, (epsSubdifferential f ε z).Nonempty ∧ IsClosed (epsSubdifferential f ε z) ∧
      infDist 0 (epsSubdifferential f ε z) ≤ ρ₀ := by
    intro z hz
    obtain ⟨c, hcz⟩ := hfin z hz
    obtain ⟨-, v, hv, hvρ⟩ := hX z hz
    have hvε := subdifferential_subset_epsSubdifferential hp hc hε.le hcz hv
    refine ⟨⟨v, hvε⟩, isClosed_epsSubdifferential hp hl hc ε hcz, ?_⟩
    exact (infDist_le_dist_of_mem hvε).trans (by rw [dist_comm, dist_zero_right]; exact hvρ)
  refine ⟨hxb, eventually_nhdsWithin_of_forall fun z hz ↦ ⟨(hnc z hz).1, (hnc z hz).2.1⟩,
    fun r ↦ ?_⟩
  set s : ℝ≥0 := 2 * r + ρ₀ with hsdef
  have hs : ρ₀ ≤ s := le_add_of_nonneg_left (by positivity)
  set K : ℝ := s * (1 + 4 * s / ε) with hK
  have hK0 : 0 ≤ K := by positivity
  have hLip : LipschitzOnWith (Real.toNNReal K)
      (fun a ↦ distanceProfile r (epsSubdifferential f ε a)) X := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
    rw [Real.coe_toNNReal _ hK0]
    change rhoDistance r _ _ ≤ _
    obtain ⟨hna, hca, hda⟩ := hnc a ha
    obtain ⟨hnb, hcb, hdb⟩ := hnc b hb
    have h437 := rhoDistance_le_rhoHatDistance_of_two_mul (r := r) (s := s) hca hcb hna hnb
      (by rw [hsdef]; push_cast; linarith [max_le hda hdb])
    refine h437.trans ?_
    have := rhoHatDistance_epsSubdifferential_le hp hl hc hε hX hs hb ha
    rw [dist_eq_norm]
    exact this
  exact (lipschitzModulusWithin_le self_mem_nhdsWithin hLip).trans_lt ENNReal.coe_lt_top

end ProperFunctions

section Counterexample

/-- The absolute value as an extended-real function on `ℝ`. -/
noncomputable def absEReal (x : ℝ) : EReal := ((|x| : ℝ) : EReal)

theorem isProper_absEReal : IsProper absEReal :=
  ⟨⟨0, EReal.coe_lt_top _⟩, fun _ ↦ EReal.bot_lt_coe _⟩

theorem convex_epigraph_absEReal : Convex ℝ (epigraph absEReal) := by
  intro p hp q hq a b ha hb hab
  change ((p.2 : ℝ) : EReal) ≥ ((|p.1| : ℝ) : EReal) at hp
  change ((q.2 : ℝ) : EReal) ≥ ((|q.1| : ℝ) : EReal) at hq
  change (((a • p + b • q).2 : ℝ) : EReal) ≥ ((|(a • p + b • q).1| : ℝ) : EReal)
  rw [ge_iff_le, EReal.coe_le_coe_iff] at hp hq ⊢
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  calc |a * p.1 + b * q.1| ≤ |a * p.1| + |b * q.1| := abs_add_le _ _
    _ = a * |p.1| + b * |q.1| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * p.2 + b * q.2 := by nlinarith

theorem lowerSemicontinuous_absEReal : LowerSemicontinuous absEReal :=
  (continuous_coe_real_ereal.comp continuous_abs).lowerSemicontinuous

theorem inner_real_eq (x y : ℝ) : ⟪x, y⟫_ℝ = x * y := by
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **Correction to 12.68**: the printed estimate `(2ρ/ε)(ρ + ε)|x' - x|` fails for
`f = |·|`, `ρ₀ = 1`, `ε = 1/10`, `ρ = 6/5`, `x = 1/20`, `x' = 3/50`, which satisfy all
of its hypotheses. -/
theorem epsSubdifferential_printed_bound_fails :
    IsProper absEReal ∧ LowerSemicontinuous absEReal ∧ Convex ℝ (epigraph absEReal) ∧
      (∀ z ∈ ({1 / 20, 3 / 50} : Set ℝ),
        absEReal z ≤ (((1 : ℝ≥0) : ℝ) : EReal) ∧ ∃ v ∈ subdifferential absEReal z, ‖v‖ ≤ 1) ∧
      ((1 : ℝ≥0) : ℝ) + 1 / 10 < ((6 / 5 : ℝ≥0) : ℝ) ∧
      |(3 / 50 : ℝ) - 1 / 20| < (1 / 10) / (((6 / 5 : ℝ≥0) : ℝ) + 1 / 10) ∧
      (2 * ((6 / 5 : ℝ≥0) : ℝ) / (1 / 10)) * (((6 / 5 : ℝ≥0) : ℝ) + 1 / 10) *
          |(3 / 50 : ℝ) - 1 / 20| <
        rhoHatDistance (6 / 5) (epsSubdifferential absEReal (1 / 10) (3 / 50))
          (epsSubdifferential absEReal (1 / 10) (1 / 20)) := by
  have h65 : ((6 / 5 : ℝ≥0) : ℝ) = 6 / 5 := by norm_num
  have hpos : ∀ z : ℝ, 0 < z → 1 ∈ subdifferential absEReal z := by
    intro z hz
    rw [mem_subdifferential_iff_of_convex convex_epigraph_absEReal isProper_absEReal
      (c := |z|) rfl]
    intro w
    change ((|z| + ⟪(1 : ℝ), w - z⟫_ℝ : ℝ) : EReal) ≤ ((|w| : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff, inner_real_eq, abs_of_pos hz]
    linarith [le_abs_self w]
  refine ⟨isProper_absEReal, lowerSemicontinuous_absEReal, convex_epigraph_absEReal, ?_, ?_, ?_,
    ?_⟩
  · intro z hz
    have hz' : z = 1 / 20 ∨ z = 3 / 50 := hz
    have hzpos : 0 < z := by rcases hz' with rfl | rfl <;> norm_num
    refine ⟨?_, 1, hpos z hzpos, by norm_num⟩
    change ((|z| : ℝ) : EReal) ≤ (((1 : ℝ≥0) : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff, abs_of_pos hzpos]
    rcases hz' with rfl | rfl <;> norm_num
  · rw [h65]; norm_num
  · rw [h65]; norm_num [abs_of_pos]
  · -- `-1 ∈ ∂_ε f(1/20)` but `∂_ε f(3/50) ⊂ [-2/3, ∞)`
    set C := epsSubdifferential absEReal (1 / 10) (3 / 50) with hC
    set D := epsSubdifferential absEReal (1 / 10) (1 / 20) with hD
    have hmD : (-1 : ℝ) ∈ D := by
      intro y
      change ((|(1 / 20 : ℝ)| : ℝ) : EReal) + ((⟪(-1 : ℝ), y - 1 / 20⟫_ℝ - 1 / 10 : ℝ) : EReal) ≤
        ((|y| : ℝ) : EReal)
      rw [← EReal.coe_add, EReal.coe_le_coe_iff, inner_real_eq]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)]
      linarith [neg_abs_le y]
    have hC_ge : ∀ c ∈ C, -(2 / 3 : ℝ) ≤ c := by
      intro c hc
      have h := hc 0
      change ((|(3 / 50 : ℝ)| : ℝ) : EReal) + ((⟪c, 0 - 3 / 50⟫_ℝ - 1 / 10 : ℝ) : EReal) ≤
        ((|(0 : ℝ)| : ℝ) : EReal) at h
      rw [← EReal.coe_add, EReal.coe_le_coe_iff, inner_real_eq,
        abs_of_pos (by norm_num : (0 : ℝ) < 3 / 50)] at h
      norm_num at h
      linarith
    have hCne : C.Nonempty := ⟨1, subdifferential_subset_epsSubdifferential isProper_absEReal
      convex_epigraph_absEReal (by norm_num) (c := |(3 / 50 : ℝ)|) rfl (hpos _ (by norm_num))⟩
    have hDne : D.Nonempty := ⟨-1, hmD⟩
    rw [h65]
    by_contra hcon
    push_neg at hcon
    have hle := (rhoHatDistance_le_iff (6 / 5) hCne hDne (by norm_num [abs_of_pos])).1 hcon
    have hmem : (-1 : ℝ) ∈ D ∩ closedBall (0 : ℝ) ((6 / 5 : ℝ≥0) : ℝ) := by
      refine ⟨hmD, ?_⟩
      rw [mem_closedBall, dist_zero_right, h65]
      norm_num
    have hth := hle.2 hmem
    rw [mem_cthickening_iff] at hth
    have hlow : ENNReal.ofReal (1 / 3) ≤ infEDist (-1 : ℝ) C := by
      rw [le_infEDist]
      intro c hc
      rw [edist_dist, Real.dist_eq]
      apply ENNReal.ofReal_le_ofReal
      have := hC_ge c hc
      rw [abs_of_nonpos (by linarith)]
      linarith
    have := hlow.trans hth
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num [abs_of_pos])] at this
    norm_num [abs_of_pos] at this

end Counterexample

end RW
