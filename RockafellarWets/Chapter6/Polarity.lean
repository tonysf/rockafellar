/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Polar Cones

Formula 6(14), Corollary 6.21, Exercise 6.22, and Examples 6.23--6.24.
The sign convention here is the nonpositive convention of Rockafellar--Wets.
-/

import RockafellarWets.Chapter3.GeneratedCones
import RockafellarWets.Chapter6.ConvexSets
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open Set
open scoped InnerProductSpace Pointwise

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Formula 6(14): the (nonpositive) polar cone. -/
def polarCone (K : Set E) : Set E :=
  {v | ∀ w ∈ K, ⟪v, w⟫_ℝ ≤ 0}

@[simp]
theorem mem_polarCone {K : Set E} {v : E} :
    v ∈ polarCone K ↔ ∀ w ∈ K, ⟪v, w⟫_ℝ ≤ 0 :=
  Iff.rfl

@[simp]
theorem zero_mem_polarCone (K : Set E) : (0 : E) ∈ polarCone K := by
  simp [polarCone]

/-- Polarity reverses inclusions. -/
theorem polarCone_antitone {K L : Set E} (hKL : K ⊆ L) :
    polarCone L ⊆ polarCone K := by
  intro v hv w hw
  exact hv w (hKL hw)

/-- Consequently, taking two polars preserves inclusions. -/
theorem polarCone_bipolar_mono {K L : Set E} (hKL : K ⊆ L) :
    polarCone (polarCone K) ⊆ polarCone (polarCone L) :=
  polarCone_antitone (polarCone_antitone hKL)

/-- Every set is contained in its bipolar. -/
theorem subset_polarCone_bipolar (K : Set E) : K ⊆ polarCone (polarCone K) := by
  intro w hw v hv
  simpa [real_inner_comm] using hv w hw

/-- A polar cone is closed. -/
theorem isClosed_polarCone (K : Set E) : IsClosed (polarCone K) := by
  rw [show polarCone K = ⋂ w ∈ K, {v : E | ⟪v, w⟫_ℝ ≤ 0} by
    ext v
    simp [polarCone]]
  exact isClosed_biInter fun _ _ ↦ isClosed_le (by fun_prop) continuous_const

/-- A polar cone is convex. -/
theorem convex_polarCone (K : Set E) : Convex ℝ (polarCone K) := by
  intro v hv u hu a b ha hb hab w hw
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  nlinarith [hv w hw, hu w hw]

/-- A polar cone is a cone in the Chapter 3 sense. -/
theorem isCone_polarCone (K : Set E) : IsCone (polarCone K) := by
  refine ⟨zero_mem_polarCone K, ?_⟩
  intro v hv c hc w hw
  rw [real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos hc.le (hv w hw)

/-- Closing a set does not change its polar. -/
@[simp]
theorem polarCone_closure (K : Set E) : polarCone (closure K) = polarCone K := by
  apply Set.Subset.antisymm
  · exact polarCone_antitone subset_closure
  · intro v hv w hw
    let H : Set E := {z | ⟪v, z⟫_ℝ ≤ 0}
    have hHclosed : IsClosed H := isClosed_le (by fun_prop) continuous_const
    have hKH : K ⊆ H := fun z hz ↦ hv z hz
    exact closure_minimal hKH hHclosed hw

/-- Passing to the convex conic hull does not change the polar. -/
@[simp]
theorem polarCone_conicHull (K : Set E) : polarCone (conicHull K) = polarCone K := by
  apply Set.Subset.antisymm
  · exact polarCone_antitone subset_conicHull
  · intro v hv w hw
    let H : Set E := {z | ⟪v, z⟫_ℝ ≤ 0}
    have hHconv : Convex ℝ H := by
      intro x hx y hy a b ha hb hab
      change ⟪v, a • x + b • y⟫_ℝ ≤ 0
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
        (mul_nonpos_of_nonneg_of_nonpos hb hy)
    have hHcone : IsCone H := by
      refine ⟨by simp [H], ?_⟩
      intro x hx c hc
      change ⟪v, c • x⟫_ℝ ≤ 0
      rw [real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos hc.le hx
    exact conicHull_minimal hHconv hHcone (fun z hz ↦ hv z hz) hw

/-- Corollary 6.21: polarity ignores convex-conic closure. -/
@[simp]
theorem polarCone_closure_conicHull (K : Set E) :
    polarCone (closure (conicHull K)) = polarCone K := by
  rw [polarCone_closure, polarCone_conicHull]

section Complete

variable [CompleteSpace E]

/-- The sign conversion from the book's polar to Mathlib's nonnegative inner dual. -/
theorem polarCone_eq_neg_innerDual (K : Set E) :
    polarCone K = -(ProperCone.innerDual K : Set E) := by
  ext v
  simp only [mem_polarCone, Set.mem_neg]
  constructor
  · intro hv w hw
    simpa [real_inner_comm] using hv w hw
  · intro hv w hw
    have h := hv hw
    simpa [real_inner_comm] using h

/-- Corollary 6.21: the bipolar is the closed convex conic hull. -/
theorem polarCone_bipolar (K : Set E) :
    polarCone (polarCone K) = closure (conicHull K) := by
  calc
    polarCone (polarCone K) =
        (ProperCone.innerDual (ProperCone.innerDual K : Set E) : Set E) := by
      ext x
      simp only [mem_polarCone]
      constructor
      · intro hx y hy
        have hneg : -y ∈ polarCone K := by
          intro z hz
          have h := hy hz
          simpa [real_inner_comm] using h
        have h := hx (-y) hneg
        simpa [real_inner_comm] using h
      · intro hx y hy
        have hneg : -y ∈ ProperCone.innerDual K := by
          intro z hz
          have h := hy z hz
          simpa [real_inner_comm] using h
        have h := hx hneg
        simpa [real_inner_comm] using h
    _ = closure (conicHull K) := innerDual_innerDual_eq_closure_conicHull K

/-- A closed convex cone equals its bipolar. -/
theorem polarCone_bipolar_eq_self {K : Set E}
    (hKclosed : IsClosed K) (hKconv : Convex ℝ K) (hKcone : IsCone K) :
    polarCone (polarCone K) = K := by
  rw [polarCone_bipolar, conicHull_eq_self_of_convex_isCone hKconv hKcone,
    hKclosed.closure_eq]

/-- Polarity is involutive on closed convex cones. -/
theorem polarCone_involutive_on_closedConvexCone {K : Set E}
    (hKclosed : IsClosed K) (hKconv : Convex ℝ K) (hKcone : IsCone K) :
    polarCone (polarCone K) = K :=
  polarCone_bipolar_eq_self hKclosed hKconv hKcone

/-- Polarity is injective on the class of closed convex cones. -/
theorem polarCone_injective_on_closedConvexCone {K L : Set E}
    (hKclosed : IsClosed K) (hKconv : Convex ℝ K) (hKcone : IsCone K)
    (hLclosed : IsClosed L) (hLconv : Convex ℝ L) (hLcone : IsCone L)
    (hpolar : polarCone K = polarCone L) : K = L := by
  calc
    K = polarCone (polarCone K) :=
      (polarCone_bipolar_eq_self hKclosed hKconv hKcone).symm
    _ = polarCone (polarCone L) := congrArg polarCone hpolar
    _ = L := polarCone_bipolar_eq_self hLclosed hLconv hLcone

end Complete

@[simp]
theorem polarCone_singleton_zero : polarCone ({0} : Set E) = Set.univ := by
  ext v
  simp [polarCone]

@[simp]
theorem polarCone_univ : polarCone (Set.univ : Set E) = ({0} : Set E) := by
  ext v
  constructor
  · intro hv
    have h := hv v (Set.mem_univ v)
    have hv0 : v = 0 := by
      simpa using (real_inner_self_nonpos.mp h)
    simp [hv0]
  · rintro hv
    have hv0 : v = 0 := by simpa using hv
    simp [hv0]

/-- The polar of a ray is its homogeneous nonpositive halfspace. -/
theorem polarCone_ray (u : E) :
    polarCone (conicHull ({u} : Set E)) = {v : E | ⟪v, u⟫_ℝ ≤ 0} := by
  rw [polarCone_conicHull]
  ext v
  simp [polarCone]

/-- The ray and homogeneous halfspace form a polar pair in finite dimensions. -/
theorem polarCone_homogeneousHalfspace [FiniteDimensional ℝ E] (u : E) :
    polarCone {v : E | ⟪v, u⟫_ℝ ≤ 0} = conicHull ({u} : Set E) := by
  rw [← polarCone_ray u]
  exact polarCone_bipolar_eq_self
    (by
      simpa only [Finset.coe_singleton] using
        (show IsClosed (conicHull (({u} : Finset E) : Set E)) by
          rw [← closure_conicHull_finset ({u} : Finset E)]
          exact isClosed_closure))
    (convex_conicHull ({u} : Set E)) (isCone_conicHull ({u} : Set E))

private theorem vectorSpan_eq_span_of_isCone {K : Set E} (hKcone : IsCone K) :
    vectorSpan ℝ K = Submodule.span ℝ K := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ hKcone.1]
  simp

private theorem interior_nonempty_iff_span_eq_top_of_convex_isCone
    [FiniteDimensional ℝ E] {K : Set E} (hKconv : Convex ℝ K) (hKcone : IsCone K) :
    (interior K).Nonempty ↔ Submodule.span ℝ K = ⊤ := by
  rw [hKconv.interior_nonempty_iff_affineSpan_eq_top,
    AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty
      ℝ E E ⟨0, hKcone.1⟩,
    vectorSpan_eq_span_of_isCone hKcone]

private theorem polarCone_inter_neg_eq_orthogonal_span (K : Set E) :
    polarCone K ∩ -polarCone K = ((Submodule.span ℝ K)ᗮ : Set E) := by
  ext v
  change (v ∈ polarCone K ∧ v ∈ -polarCone K) ↔ v ∈ (Submodule.span ℝ K)ᗮ
  rw [(Submodule.span ℝ K).mem_orthogonal']
  constructor
  · rintro ⟨hv, hvneg⟩
    have hneg : -v ∈ polarCone K := by
      simpa only [Set.mem_neg, neg_neg] using hvneg
    have hspan :
        Submodule.span ℝ K ≤ (innerSL ℝ v).toLinearMap.ker := by
      refine Submodule.span_le.mpr ?_
      intro z hz
      change ⟪v, z⟫_ℝ = 0
      apply le_antisymm (hv z hz)
      have h := hneg z hz
      simpa using h
    intro z hz
    have h := hspan hz
    change ⟪v, z⟫_ℝ = 0 at h
    simpa using h
  · intro hv
    constructor
    · intro z hz
      rw [hv z (Submodule.subset_span hz)]
    · rw [Set.mem_neg]
      intro z hz
      rw [inner_neg_left, hv z (Submodule.subset_span hz), neg_zero]

/-- Exercise 6.22: a convex cone has nonempty interior exactly when its polar is pointed. -/
theorem interior_nonempty_iff_isPointed_polarCone [FiniteDimensional ℝ E]
    {K : Set E} (hKconv : Convex ℝ K) (hKcone : IsCone K) :
    (interior K).Nonempty ↔ IsPointed (polarCone K) := by
  constructor
  · intro hKint
    apply (isPointed_iff_inter_neg_eq_singleton_zero
      (convex_polarCone K) (isCone_polarCone K)).2
    rw [polarCone_inter_neg_eq_orthogonal_span K]
    have hspan : Submodule.span ℝ K = ⊤ :=
      (interior_nonempty_iff_span_eq_top_of_convex_isCone hKconv hKcone).1 hKint
    rw [hspan, Submodule.top_orthogonal_eq_bot]
    ext v
    simp
  · intro hpointed
    apply (interior_nonempty_iff_span_eq_top_of_convex_isCone hKconv hKcone).2
    have hset : ((Submodule.span ℝ K)ᗮ : Set E) = ({0} : Set E) := by
      rw [← polarCone_inter_neg_eq_orthogonal_span K]
      exact (isPointed_iff_inter_neg_eq_singleton_zero
        (convex_polarCone K) (isCone_polarCone K)).1 hpointed
    have horth : (Submodule.span ℝ K)ᗮ = ⊥ := by
      apply SetLike.coe_injective
      simpa using hset
    exact (Submodule.orthogonal_eq_bot_iff).1 horth

/-- Exercise 6.22: interior points pair strictly negatively with every nonzero polar vector. -/
theorem mem_interior_iff_inner_lt_zero_on_polarCone [FiniteDimensional ℝ E]
    {K : Set E} (hKconv : Convex ℝ K) (hKcone : IsCone K) {w : E} :
    w ∈ interior K ↔
      ∀ v ∈ polarCone K, v ≠ 0 → ⟪v, w⟫_ℝ < 0 := by
  constructor
  · intro hw v hv hv0
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
    let τ : ℝ := ε / (2 * (‖v‖ + 1))
    have hdenom : 0 < 2 * (‖v‖ + 1) := by positivity
    have hτ : 0 < τ := div_pos hε hdenom
    have hnear : w + τ • v ∈ Metric.ball w ε := by
      simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hτ, τ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hdenom]
      nlinarith [norm_nonneg v]
    have hmem : w + τ • v ∈ K := interior_subset (hball hnear)
    have hpair := hv (w + τ • v) hmem
    rw [inner_add_right, real_inner_smul_right] at hpair
    have hself : 0 < ⟪v, v⟫_ℝ := real_inner_self_pos.2 hv0
    nlinarith [mul_pos hτ hself]
  · intro hstrict
    have hPpointed : IsPointed (polarCone K) := by
      apply (isPointed_iff_inter_neg_eq_singleton_zero
        (convex_polarCone K) (isCone_polarCone K)).2
      ext v
      constructor
      · rintro ⟨hv, hvneg⟩
        by_cases hv0 : v = 0
        · simp [hv0]
        have hneg : -v ∈ polarCone K := by
          simpa only [Set.mem_neg, neg_neg] using hvneg
        have hposneg := hstrict (-v) hneg (neg_ne_zero.mpr hv0)
        rw [inner_neg_left] at hposneg
        have hnegval := hstrict v hv hv0
        exfalso
        linarith
      · intro hv
        have hv0 : v = 0 := by simpa using hv
        subst v
        simp
    have hKint : (interior K).Nonempty :=
      (interior_nonempty_iff_isPointed_polarCone hKconv hKcone).2 hPpointed
    by_contra hw
    obtain ⟨f, hf⟩ :=
      geometric_hahn_banach_open_point hKconv.interior isOpen_interior hw
    have hfne : f ≠ 0 := by
      intro hf0
      obtain ⟨a, ha⟩ := hKint
      have hfa := hf a ha
      rw [hf0] at hfa
      simp at hfa
    have hclosure : closure (interior K) = closure K :=
      hKconv.closure_interior_eq_closure_of_nonempty_interior hKint
    have hKle : ∀ z ∈ K, f z ≤ f w := by
      intro z hz
      have hzcl : z ∈ closure (interior K) := by
        rw [hclosure]
        exact subset_closure hz
      exact closure_minimal (fun a ha ↦ (hf a ha).le)
        (isClosed_le f.continuous continuous_const) hzcl
    have hfw : 0 ≤ f w := by
      simpa using hKle 0 hKcone.1
    have hfnonpos : ∀ z ∈ K, f z ≤ 0 := by
      intro z hz
      by_contra hnpos
      have hfz : 0 < f z := lt_of_not_ge hnpos
      let c : ℝ := (f w + 1) / f z
      have hc : 0 < c := div_pos (by linarith) hfz
      have hcz : c • z ∈ K := hKcone.2 hz hc
      have hle := hKle (c • z) hcz
      have hval : f (c • z) = f w + 1 := by
        calc
          f (c • z) = c * f z := by simp [smul_eq_mul]
          _ = f w + 1 := by
            dsimp [c]
            field_simp
      rw [hval] at hle
      linarith
    let v : E := (InnerProductSpace.toDual ℝ E).symm f
    have hv : v ∈ polarCone K := by
      intro z hz
      simpa [v] using hfnonpos z hz
    have hv0 : v ≠ 0 := by
      intro hvzero
      apply hfne
      apply (InnerProductSpace.toDual ℝ E).symm.injective
      simpa [v] using hvzero
    have hlt := hstrict v hv hv0
    have : f w < 0 := by simpa [v] using hlt
    linarith

private theorem isPointed_of_strict_inner_witness {K : Set E} {w : E}
    (hstrict : ∀ v ∈ K, v ≠ 0 → ⟪v, w⟫_ℝ < 0) : IsPointed K := by
  intro n z hz hsum i
  by_contra hi
  have hle : ∀ j, ⟪z j, w⟫_ℝ ≤ 0 := by
    intro j
    by_cases hj : z j = 0
    · simp [hj]
    · exact (hstrict (z j) (hz j) hj).le
  have hlt :
      (∑ j, ⟪z j, w⟫_ℝ) < ∑ _j : Fin n, (0 : ℝ) := by
    apply Finset.sum_lt_sum (s := Finset.univ)
    · exact fun j _ ↦ hle j
    · exact ⟨i, Finset.mem_univ i, hstrict (z i) (hz i) hi⟩
  have hpairsum : ⟪(∑ j, z j), w⟫_ℝ = ∑ j, ⟪z j, w⟫_ℝ := by
    simpa using sum_inner (s := Finset.univ) z w
  rw [← hpairsum, hsum] at hlt
  simp at hlt

/-- Exercise 6.22, printed replacement clause: if `K` is the polar of a closed cone
`K₀`, the strict test may quantify over `K₀` itself instead of the bipolar. -/
theorem mem_interior_polarCone_iff_inner_lt_zero [FiniteDimensional ℝ E]
    {K₀ : Set E} (hK₀closed : IsClosed K₀) (hK₀cone : IsCone K₀) {w : E} :
    w ∈ interior (polarCone K₀) ↔
      ∀ v ∈ K₀, v ≠ 0 → ⟪v, w⟫_ℝ < 0 := by
  constructor
  · intro hw v hv hv0
    exact (mem_interior_iff_inner_lt_zero_on_polarCone
      (convex_polarCone K₀) (isCone_polarCone K₀)).1 hw
        v (subset_polarCone_bipolar K₀ hv) hv0
  · intro hstrict
    have hK₀pointed : IsPointed K₀ := isPointed_of_strict_inner_witness hstrict
    have hHullclosed : IsClosed (convexHull ℝ K₀) :=
      isClosed_convexHull_of_isClosed_isPointed hK₀closed hK₀cone hK₀pointed
    have hConicHull : conicHull K₀ = convexHull ℝ K₀ := by
      rw [conicHull_eq_convexHull_positiveHull, positiveHull_eq_self hK₀cone]
    apply (mem_interior_iff_inner_lt_zero_on_polarCone
      (convex_polarCone K₀) (isCone_polarCone K₀)).2
    intro v hv hv0
    have hvHull : v ∈ convexHull ℝ K₀ := by
      rw [polarCone_bipolar, hConicHull, hHullclosed.closure_eq] at hv
      exact hv
    rcases (mem_convexHull_iff_exists_fintype_sum_mem hK₀cone).1 hvHull with
      ⟨ι, _, z, hz, hsum⟩
    have hex : ∃ i, z i ≠ 0 := by
      by_contra hzero
      push_neg at hzero
      apply hv0
      rw [← hsum]
      simp [hzero]
    have hle : ∀ i, ⟪z i, w⟫_ℝ ≤ 0 := by
      intro i
      by_cases hi : z i = 0
      · simp [hi]
      · exact (hstrict (z i) (hz i) hi).le
    obtain ⟨i, hi⟩ := hex
    have hlt :
        (∑ j, ⟪z j, w⟫_ℝ) < ∑ _j : ι, (0 : ℝ) := by
      apply Finset.sum_lt_sum (s := Finset.univ)
      · exact fun j _ ↦ hle j
      · exact ⟨i, Finset.mem_univ i, hstrict (z i) (hz i) hi⟩
    calc
      ⟪v, w⟫_ℝ = ⟪(∑ j, z j), w⟫_ℝ := by rw [hsum]
      _ = ∑ j, ⟪z j, w⟫_ℝ := by
        simpa using sum_inner (s := Finset.univ) z w
      _ < ∑ _j : ι, (0 : ℝ) := hlt
      _ = 0 := by simp

/-- Exercise 6.22, pointedness form of the printed replacement clause. -/
theorem interior_polarCone_nonempty_iff_isPointed [FiniteDimensional ℝ E]
    {K₀ : Set E} (hK₀closed : IsClosed K₀) (hK₀cone : IsCone K₀) :
    (interior (polarCone K₀)).Nonempty ↔ IsPointed K₀ := by
  constructor
  · intro hint
    have hdouble : IsPointed (polarCone (polarCone K₀)) :=
      (interior_nonempty_iff_isPointed_polarCone
        (convex_polarCone K₀) (isCone_polarCone K₀)).1 hint
    exact hdouble.mono (subset_polarCone_bipolar K₀)
  · intro hK₀pointed
    apply (interior_nonempty_iff_isPointed_polarCone
      (convex_polarCone K₀) (isCone_polarCone K₀)).2
    have hHullclosed : IsClosed (convexHull ℝ K₀) :=
      isClosed_convexHull_of_isClosed_isPointed hK₀closed hK₀cone hK₀pointed
    have hConicHull : conicHull K₀ = convexHull ℝ K₀ := by
      rw [conicHull_eq_convexHull_positiveHull, positiveHull_eq_self hK₀cone]
    rw [polarCone_bipolar, hConicHull, hHullclosed.closure_eq]
    exact isPointed_convexHull hK₀cone hK₀pointed

/-- Example 6.23: the polar of a subspace is its orthogonal complement. -/
theorem polarCone_submodule (M : Submodule ℝ E) :
    polarCone (M : Set E) = (Mᗮ : Set E) := by
  ext v
  change v ∈ polarCone (M : Set E) ↔ v ∈ Mᗮ
  rw [M.mem_orthogonal']
  constructor
  · intro hv w hw
    apply le_antisymm (hv w hw)
    have hneg := hv (-w) (M.neg_mem hw)
    simpa using hneg
  · intro hv w hw
    simp [hv w hw]

/-- Example 6.23: double orthogonal complementation in finite dimensions. -/
theorem orthogonal_orthogonal_eq_self [FiniteDimensional ℝ E] (M : Submodule ℝ E) :
    Mᗮᗮ = M := by
  exact M.orthogonal_orthogonal

/-- Example 6.24: the normal cone to a convex set is the polar of its tangent cone. -/
theorem normalCone_eq_polarCone_tangentCone {C : Set E} {x : E}
    (hC : Convex ℝ C) (hx : x ∈ C) :
    normalCone C x = polarCone (tangentCone C x) := by
  ext v
  constructor
  · intro hv w hw
    have hvreg : v ∈ regularNormalCone C x := by
      rw [← normalCone_eq_regularNormalCone_of_convex hC hx]
      exact hv
    exact inner_nonpos_of_mem_regularNormalCone hvreg hw
  · intro hv
    rw [normalCone_eq_of_convex hC hx]
    intro y hy
    apply hv (y - x)
    rw [tangentCone_eq_closure_radialCone hC hx]
    apply subset_closure
    refine ⟨1, one_pos, ?_⟩
    simpa only [one_smul, add_sub_cancel] using hy

/-- Example 6.24: the tangent cone to a convex set is the polar of its normal cone. -/
theorem tangentCone_eq_polarCone_normalCone [FiniteDimensional ℝ E]
    {C : Set E} {x : E} (hC : Convex ℝ C) (hx : x ∈ C) :
    tangentCone C x = polarCone (normalCone C x) := by
  have hTconv : Convex ℝ (tangentCone C x) := by
    rw [tangentCone_eq_closure_radialCone hC hx]
    exact (convex_radialCone hC x).closure
  have hTcone : IsCone (tangentCone C x) := isCone_tangentCone hx
  have hTclosed : IsClosed (tangentCone C x) := isClosed_tangentCone C x
  symm
  rw [normalCone_eq_polarCone_tangentCone hC hx]
  exact polarCone_bipolar_eq_self hTclosed hTconv hTcone

private theorem radialCone_nonempty_iff {S : Set E} {x : E} :
    (radialCone S x).Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨w, lam, hlam, hmem⟩
    exact ⟨x + lam • w, hmem⟩
  · rintro ⟨y, hy⟩
    refine ⟨y - x, 1, one_pos, ?_⟩
    simpa only [one_smul, add_sub_cancel] using hy

/-- Example 6.24: the normal cone is pointed exactly when the convex set has interior. -/
theorem isPointed_normalCone_iff_interior_nonempty [FiniteDimensional ℝ E]
    {C : Set E} {x : E} (hC : Convex ℝ C) (hx : x ∈ C) :
    IsPointed (normalCone C x) ↔ (interior C).Nonempty := by
  have hTconv : Convex ℝ (tangentCone C x) := by
    rw [tangentCone_eq_closure_radialCone hC hx]
    exact (convex_radialCone hC x).closure
  have hTcone : IsCone (tangentCone C x) := isCone_tangentCone hx
  rw [normalCone_eq_polarCone_tangentCone hC hx,
    ← interior_nonempty_iff_isPointed_polarCone hTconv hTcone,
    interior_tangentCone_of_convex hC hx]
  exact radialCone_nonempty_iff

end RW
