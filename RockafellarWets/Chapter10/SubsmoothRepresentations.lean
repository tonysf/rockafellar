/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: common representations of subsmooth functions

**Proposition 10.54**: if `f` is lower-`C¹` (or lower-`C²`) on an open set `O`, then for every
compact `B ⊂ O` there is an open `O'` with `B ⊂ O' ⊂ O` and a single representation
`f = max_{t ∈ T} f_t` valid on all of `O'` (`IsLowerCOn.exists_common_representation`).
-/

import RockafellarWets.Chapter10.SubsmoothCalculus

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A lower-`C¹` function is continuous (10.31). -/
theorem IsLowerCOn.continuousOn {k : ℕ∞} {f : E → ℝ} {O : Set E} (hf : IsLowerCOn k f O)
    (hk : 1 ≤ k) : ContinuousOn f O := fun x hx ↦ by
  obtain ⟨V, hV, hxV, -, ⟨R⟩⟩ := hf x hx
  exact (R.continuousAt hk hV hxV).continuousWithinAt

omit [FiniteDimensional ℝ E] in
/-- A finite cover of a compact `B ⊂ O` by half balls of balls carrying local representations. -/
theorem IsLowerCOn.exists_finite_cover {k : ℕ∞} {f : E → ℝ} {O : Set E} (hf : IsLowerCOn k f O)
    {B : Set E} (hB : IsCompact B) (hBO : B ⊆ O) :
    ∃ (ι : Type u) (_ : Fintype ι) (w : ι → E) (r : ι → ℝ) (V : ι → Set E)
      (_ : ∀ i, LowerRepresentation k f (V i)),
      (∀ i, 0 < r i ∧ IsOpen (V i) ∧ closedBall (w i) (r i) ⊆ V i ∧ V i ⊆ O) ∧
        B ⊆ ⋃ i, ball (w i) (r i / 2) := by
  have h : ∀ x ∈ B, ∃ r : ℝ, ∃ V : Set E, 0 < r ∧ IsOpen V ∧ closedBall x r ⊆ V ∧ V ⊆ O ∧
      Nonempty (LowerRepresentation k f V) := by
    intro x hx
    obtain ⟨V, hV, hxV, hVO, hR⟩ := hf x (hBO hx)
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV x hxV
    exact ⟨r / 2, V, half_pos hr, hV, (closedBall_subset_ball (half_lt_self hr)).trans hrV, hVO,
      hR⟩
  choose! r V hr hV hrV hVO hR using h
  obtain ⟨t, ht⟩ := hB.elim_finite_subcover (fun x : B ↦ ball (x : E) (r x / 2))
    (fun _ ↦ isOpen_ball) (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (half_pos (hr x hx))⟩)
  refine ⟨t, inferInstance, fun i ↦ (i.1 : E), fun i ↦ r i.1, fun i ↦ V i.1,
    fun i ↦ (hR i.1 i.1.2).some, fun i ↦ ⟨hr i.1 i.1.2, hV i.1 i.1.2, hrV i.1 i.1.2, hVO i.1 i.1.2⟩,
    fun x hx ↦ ?_⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
  exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩

/-- The far-field estimate behind the global quadratic minorants. -/
theorem quadratic_far_bound {ρ M₁ M₂ C r d : ℝ} (hr : 0 < r) (hd : r / 2 < d) (hM₂ : 0 ≤ M₂)
    (h₁ : 8 * |M₁ + C| / r ^ 2 ≤ ρ) (h₂ : 4 * M₂ / r ≤ ρ) : M₁ + M₂ * d - ρ * d ^ 2 ≤ -C := by
  have hd0 : 0 < d := lt_trans (half_pos hr) hd
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) h₂
  have hdd : (r / 2) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by positivity) hd.le 2
  have hdd' : r / 2 * d ≤ d ^ 2 := by nlinarith
  have e1 : |M₁ + C| ≤ ρ / 2 * d ^ 2 := by
    have : 8 * |M₁ + C| / r ^ 2 * ((r / 2) ^ 2) = 2 * |M₁ + C| := by
      field_simp
      ring
    nlinarith [abs_nonneg (M₁ + C), mul_le_mul_of_nonneg_right h₁ (sq_nonneg (r / 2)),
      mul_le_mul_of_nonneg_left hdd hρ0]
  have e2 : M₂ * d ≤ ρ / 2 * d ^ 2 := by
    have : 4 * M₂ / r * (r / 2 * d) = 2 * (M₂ * d) := by
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_right h₂ (by positivity : (0 : ℝ) ≤ r / 2 * d),
      mul_le_mul_of_nonneg_left hdd' hρ0]
  nlinarith [le_abs_self (M₁ + C)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem compactSpace_sigma {ι : Type*} [Finite ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompactSpace (X i)] : CompactSpace (Σ i, X i) := by
  refine ⟨?_⟩
  have h : (univ : Set (Σ i, X i)) = ⋃ i, range (Sigma.mk i) := by
    ext ⟨i, x⟩
    simp only [mem_univ, mem_iUnion, mem_range, true_iff]
    exact ⟨i, x, rfl⟩
  rw [h]
  exact isCompact_iUnion fun i ↦ isCompact_range continuous_sigmaMk

/-- **Proposition 10.54** for lower-`C²` functions: one quadratic representation
`f(x) = max {f(y) + ⟪∇f_t(y), x - y⟫ - ρ|x - y|²}` on a neighborhood of a compact set. -/
theorem IsLowerCOn.exists_common_representation_two {f : E → ℝ} {O : Set E}
    (hf : IsLowerCOn 2 f O) {B : Set E} (hB : IsCompact B) (hBO : B ⊆ O) :
    ∃ O' : Set E, IsOpen O' ∧ B ⊆ O' ∧ O' ⊆ O ∧ Nonempty (LowerRepresentation ⊤ f O') := by
  obtain ⟨ι, hι, w, r, V, R, hprop, hcov⟩ := hf.exists_finite_cover hB hBO
  have hr : ∀ i, 0 < r i := fun i ↦ (hprop i).1
  have hhalf : ∀ i, closedBall (w i) (r i / 2) ⊆ V i := fun i ↦
    (closedBall_subset_closedBall (by linarith [hr i])).trans (hprop i).2.2.1
  set O' := ⋃ i, ball (w i) (r i / 2) with hO'
  set K := ⋃ i, closedBall (w i) (r i / 2) with hK
  have hO'K : O' ⊆ K := iUnion_mono fun i ↦ ball_subset_closedBall
  have hKO : K ⊆ O := iUnion_subset fun i ↦ (hhalf i).trans (hprop i).2.2.2
  have hKc : IsCompact K := isCompact_iUnion fun i ↦ isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
    ((hf.continuousOn one_le_two).mono hKO)
  have hρi : ∀ i, ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ t, ∀ y ∈ closedBall (w i) (r i),
      ‖fderiv ℝ (fderiv ℝ ((R i).F t)) y‖ ≤ ρ := fun i ↦
    (R i).exists_bound_fderiv_fderiv le_rfl (hprop i).2.2.1
  choose ρi hρi0 hρi using hρi
  have hM1 : ∀ i, ∃ M : ℝ, ∀ p ∈ (univ : Set (R i).T) ×ˢ closedBall (w i) (r i / 2),
      ‖(R i).F p.1 p.2‖ ≤ M := fun i ↦
    (isCompact_univ.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn
      ((R i).continuousOn_val.mono (prod_mono Subset.rfl (hhalf i)))
  choose M₁ hM₁ using hM1
  have hM2 : ∀ i, ∃ M : ℝ, ∀ p ∈ (univ : Set (R i).T) ×ˢ closedBall (w i) (r i / 2),
      ‖fderiv ℝ ((R i).F p.1) p.2‖ ≤ M := fun i ↦
    (isCompact_univ.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn
      (((R i).continuousOn_fderiv one_le_two).mono (prod_mono Subset.rfl (hhalf i)))
  choose M₂ hM₂ using hM2
  set term : ι → ℝ := fun i ↦ ρi i + 8 * |M₁ i + C| / r i ^ 2 + 4 * |M₂ i| / r i with hterm
  have hterm0 : ∀ i, 0 ≤ term i := fun i ↦ by
    have := hρi0 i
    have := hr i
    positivity
  set ρ := ∑ i, term i with hρ
  have hle_ρ : ∀ i, term i ≤ ρ := fun i ↦
    Finset.single_le_sum (fun j _ ↦ hterm0 j) (Finset.mem_univ i)
  have hρ1 : ∀ i, ρi i ≤ ρ := fun i ↦ by
    have := hle_ρ i
    have : 0 ≤ 8 * |M₁ i + C| / r i ^ 2 := by have := hr i; positivity
    have : 0 ≤ 4 * |M₂ i| / r i := by have := hr i; positivity
    simp only [hterm] at *
    linarith
  have hρ2 : ∀ i, 8 * |M₁ i + C| / r i ^ 2 ≤ ρ := fun i ↦ by
    have := hle_ρ i
    have := hρi0 i
    have : 0 ≤ 4 * |M₂ i| / r i := by have := hr i; positivity
    simp only [hterm] at *
    linarith
  have hρ3 : ∀ i, 4 * |M₂ i| / r i ≤ ρ := fun i ↦ by
    have := hle_ρ i
    have := hρi0 i
    have : 0 ≤ 8 * |M₁ i + C| / r i ^ 2 := by have := hr i; positivity
    simp only [hterm] at *
    linarith
  haveI : ∀ i, CompactSpace (closedBall (w i) (r i / 2)) := fun i ↦
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  haveI : CompactSpace (Σ i, (R i).T × closedBall (w i) (r i / 2)) := compactSpace_sigma
  let c : (Σ i, (R i).T × closedBall (w i) (r i / 2)) → ℝ × (E →L[ℝ] ℝ) × E := fun s ↦
    ((R s.1).F s.2.1 s.2.2, fderiv ℝ ((R s.1).F s.2.1) s.2.2, (s.2.2 : E))
  have hc : Continuous c := by
    refine continuous_sigma fun i ↦ ?_
    have hmap : Continuous fun s : (R i).T × closedBall (w i) (r i / 2) ↦
        ((s.1, (s.2 : E)) : (R i).T × E) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hmem : ∀ s : (R i).T × closedBall (w i) (r i / 2), ((s.1, (s.2 : E)) : (R i).T × E) ∈
        univ ×ˢ V i := fun s ↦ ⟨trivial, hhalf i s.2.2⟩
    exact ((R i).continuousOn_val.comp_continuous hmap hmem).prodMk
      ((((R i).continuousOn_fderiv one_le_two).comp_continuous hmap hmem).prodMk
        (continuous_subtype_val.comp continuous_snd))
  refine ⟨O', isOpen_iUnion fun i ↦ isOpen_ball, hcov, hO'K.trans hKO, ⟨?_⟩⟩
  refine LowerRepresentation.ofParam (n := ⊤) (Σ i, (R i).T × closedBall (w i) (r i / 2)) c hc
    (LowerRepresentation.quadraticModel ρ) (LowerRepresentation.contDiff_quadraticModel ρ) ?_ ?_
  · rintro ⟨i, t, y, hy⟩ x hx
    have hxK : x ∈ K := hO'K hx
    have hfx : -C ≤ f x := by
      have := hC x hxK
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (f x)]
    show (R i).F t y + fderiv ℝ ((R i).F t) y (x - y) - ρ * ‖x - y‖ ^ 2 ≤ f x
    by_cases hd : ‖x - y‖ ≤ r i / 2
    · have hy' : y ∈ closedBall (w i) (r i) :=
        closedBall_subset_closedBall (by linarith [hr i]) hy
      have hx' : x ∈ closedBall (w i) (r i) := by
        rw [mem_closedBall] at hy ⊢
        calc dist x (w i) ≤ dist x y + dist y (w i) := dist_triangle _ _ _
          _ ≤ r i / 2 + r i / 2 := add_le_add (by rwa [dist_eq_norm]) hy
          _ = r i := by ring
      have h1 := (R i).quadratic_lower_bound le_rfl (hprop i).2.1 (hprop i).2.2.1 (hρi i) t hx' hy'
      have h2 := (R i).le t x ((hprop i).2.2.1 hx')
      nlinarith [mul_le_mul_of_nonneg_right (hρ1 i) (sq_nonneg ‖x - y‖)]
    · push_neg at hd
      have hy2 : (⟨t, y⟩ : (R i).T × E) ∈ (univ : Set (R i).T) ×ˢ closedBall (w i) (r i / 2) :=
        ⟨trivial, hy⟩
      have e1 : (R i).F t y ≤ M₁ i := by
        have := hM₁ i _ hy2
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
      have e2 : fderiv ℝ ((R i).F t) y (x - y) ≤ |M₂ i| * ‖x - y‖ := by
        have h := (fderiv ℝ ((R i).F t) y).le_opNorm (x - y)
        rw [Real.norm_eq_abs] at h
        exact (le_abs_self _).trans (h.trans (mul_le_mul_of_nonneg_right
          ((hM₂ i _ hy2).trans (le_abs_self _)) (norm_nonneg _)))
      have h3 := quadratic_far_bound (hr i) hd (abs_nonneg (M₂ i)) (hρ2 i) (hρ3 i)
      linarith
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨t, ht⟩ := (R i).exists_eq x (hhalf i (ball_subset_closedBall hi))
    refine ⟨⟨i, t, x, ball_subset_closedBall hi⟩, ?_⟩
    show (R i).F t x + fderiv ℝ ((R i).F t) x (x - x) - ρ * ‖x - x‖ ^ 2 = f x
    simp [ht]

omit [FiniteDimensional ℝ E] in
theorem iteratedFDeriv_one_eq' (g : E → ℝ) (x : E) :
    iteratedFDeriv ℝ 1 g x = (continuousMultilinearCurryFin1 ℝ E ℝ).symm (fderiv ℝ g x) := by
  ext m
  simp [iteratedFDeriv_one_apply]

namespace LowerRepresentation

variable {k : ℕ∞} {f : E → ℝ} {V : Set E} (R : LowerRepresentation k f V) {w : E}
  (φ : ContDiffBump w) (c : ℝ)

theorem eventually_cutoff_eq_const (hball : closedBall w φ.rOut ⊆ V) {x : E} (hx : x ∉ V) :
    ∀ᶠ y in 𝓝 x, φ y = 0 := by
  have hx' : φ.rOut < dist x w := by
    by_contra h
    exact hx (hball (mem_closedBall.2 (not_lt.1 h)))
  filter_upwards [isOpen_lt continuous_const (continuous_id.dist continuous_const) |>.mem_nhds hx']
    with y hy
  exact φ.zero_of_le_dist (le_of_lt hy)

/-- The cut-off modification `c + φ (f_t - c)` is jointly continuous. -/
theorem continuous_cutoff (hV : IsOpen V) (hball : closedBall w φ.rOut ⊆ V) :
    Continuous fun p : R.T × E ↦ c + φ p.2 * (R.F p.1 p.2 - c) := by
  refine continuous_iff_continuousAt.2 ?_
  rintro ⟨t, x⟩
  by_cases hx : x ∈ V
  · have h := R.continuousOn_val.continuousAt ((isOpen_univ.prod hV).mem_nhds
      (show ((t, x) : R.T × E) ∈ univ ×ˢ V from ⟨trivial, hx⟩))
    exact continuousAt_const.add ((φ.continuous.comp continuous_snd).continuousAt.mul
      (h.sub continuousAt_const))
  · have hev := eventually_cutoff_eq_const φ hball hx
    refine (continuousAt_const : ContinuousAt (fun _ : R.T × E ↦ c) (t, x)).congr ?_
    filter_upwards [continuous_snd.continuousAt.eventually hev] with p hp
    simp [hp]

theorem hasFDerivAt_cutoff (hk : 1 ≤ k) (hV : IsOpen V) (t : R.T) {x : E} (hx : x ∈ V) :
    HasFDerivAt (fun y ↦ c + φ y * (R.F t y - c))
      (φ x • fderiv ℝ (R.F t) x + (R.F t x - c) • fderiv ℝ φ x) x := by
  have hφ : HasFDerivAt φ (fderiv ℝ φ x) x :=
    ((φ.contDiff (n := 1)).differentiable (by norm_num) x).hasFDerivAt
  have hF : HasFDerivAt (fun y ↦ R.F t y - c) (fderiv ℝ (R.F t) x) x :=
    (R.differentiableAt hk hV t hx).hasFDerivAt.sub_const c
  exact (hφ.mul hF).const_add c

theorem contDiff_cutoff (hk : 1 ≤ k) (hV : IsOpen V) (hball : closedBall w φ.rOut ⊆ V)
    (t : R.T) : ContDiff ℝ 1 (fun y ↦ c + φ y * (R.F t y - c)) := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  by_cases hx : x ∈ V
  · have hF : ContDiffAt ℝ 1 (R.F t) x :=
      ((R.contDiffOn t).contDiffAt (hV.mem_nhds hx)).of_le (by exact_mod_cast hk)
    exact contDiffAt_const.add (φ.contDiff.contDiffAt.mul (hF.sub contDiffAt_const))
  · refine (contDiffAt_const (c := c)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_cutoff_eq_const φ hball hx] with y hy
    simp [hy]

theorem continuous_fderiv_cutoff (hk : 1 ≤ k) (hV : IsOpen V) (hball : closedBall w φ.rOut ⊆ V) :
    Continuous fun p : R.T × E ↦ fderiv ℝ (fun y ↦ c + φ y * (R.F p.1 y - c)) p.2 := by
  refine continuous_iff_continuousAt.2 ?_
  rintro ⟨t, x⟩
  by_cases hx : x ∈ V
  · have hU : (univ : Set R.T) ×ˢ V ∈ 𝓝 ((t, x) : R.T × E) :=
      (isOpen_univ.prod hV).mem_nhds ⟨trivial, hx⟩
    have hcont : ContinuousAt (fun p : R.T × E ↦
        φ p.2 • fderiv ℝ (R.F p.1) p.2 + (R.F p.1 p.2 - c) • fderiv ℝ φ p.2) (t, x) := by
      have h1 := R.continuousOn_val.continuousAt hU
      have h2 := (R.continuousOn_fderiv hk).continuousAt hU
      have h3 : Continuous fun y ↦ fderiv ℝ φ y :=
        (φ.contDiff (n := 1)).continuous_fderiv (by norm_num)
      exact ((φ.continuous.comp continuous_snd).continuousAt.smul h2).add
        ((h1.sub continuousAt_const).smul (h3.comp continuous_snd).continuousAt)
    refine hcont.congr ?_
    filter_upwards [hU] with p hp
    exact ((R.hasFDerivAt_cutoff φ c hk hV p.1 hp.2).fderiv).symm
  · have hev := eventually_cutoff_eq_const φ hball hx
    refine (continuousAt_const : ContinuousAt (fun _ : R.T × E ↦ (0 : E →L[ℝ] ℝ)) (t, x)).congr ?_
    filter_upwards [continuous_snd.continuousAt.eventually (eventually_eventually_nhds.2 hev)]
      with p hp
    have he : (fun y ↦ c + φ y * (R.F p.1 y - c)) =ᶠ[𝓝 p.2] fun _ ↦ c := by
      filter_upwards [hp] with y hy
      simp [hy]
    rw [he.fderiv_eq, fderiv_const_apply]

end LowerRepresentation

omit [FiniteDimensional ℝ E] in
/-- Lowering the smoothness order of a representation. -/
def LowerRepresentation.of_le {k m : ℕ∞} {f : E → ℝ} {V : Set E} (R : LowerRepresentation k f V)
    (h : m ≤ k) : LowerRepresentation m f V :=
  LowerRepresentation.mk R.T R.F (fun t ↦ (R.contDiffOn t).of_le (by exact_mod_cast h))
    (fun j hj ↦ R.continuousOn_iteratedFDeriv j (hj.trans h)) R.le R.exists_eq

/-- **Proposition 10.54** for lower-`C¹` functions: the local families, modified by cut-offs
`c + φᵢ (f_t - c)`, glue to one representation on a neighborhood of a compact set. -/
theorem IsLowerCOn.exists_common_representation_one {f : E → ℝ} {O : Set E}
    (hf : IsLowerCOn 1 f O) {B : Set E} (hB : IsCompact B) (hBO : B ⊆ O) :
    ∃ O' : Set E, IsOpen O' ∧ B ⊆ O' ∧ O' ⊆ O ∧ Nonempty (LowerRepresentation 1 f O') := by
  obtain ⟨ι, hι, w, r, V, R, hprop, hcov⟩ := hf.exists_finite_cover hB hBO
  have hr : ∀ i, 0 < r i := fun i ↦ (hprop i).1
  have hhalf : ∀ i, closedBall (w i) (r i / 2) ⊆ V i := fun i ↦
    (closedBall_subset_closedBall (by linarith [hr i])).trans (hprop i).2.2.1
  set O' := ⋃ i, ball (w i) (r i / 2) with hO'
  set K := ⋃ i, closedBall (w i) (r i / 2) with hK
  have hO'K : O' ⊆ K := iUnion_mono fun i ↦ ball_subset_closedBall
  have hKO : K ⊆ O := iUnion_subset fun i ↦ (hhalf i).trans (hprop i).2.2.2
  have hKc : IsCompact K := isCompact_iUnion fun i ↦ isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn ((hf.continuousOn le_rfl).mono hKO)
  have hβ : ∀ i, ∃ M : ℝ, ∀ p ∈ (univ : Set (R i).T) ×ˢ closedBall (w i) (r i),
      ‖(R i).F p.1 p.2‖ ≤ M := fun i ↦
    (isCompact_univ.prod (isCompact_closedBall _ _)).exists_bound_of_continuousOn
      ((R i).continuousOn_val.mono (prod_mono Subset.rfl (hprop i).2.2.1))
  choose β hβ using hβ
  set c : ℝ := -(|C| + ∑ i, |β i|) with hcdef
  have hsum0 : 0 ≤ ∑ i, |β i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hcC : c ≤ -C := by
    have := le_abs_self C
    rw [hcdef]
    linarith
  have hcβ : ∀ i, c ≤ -|β i| := fun i ↦ by
    have h1 : |β i| ≤ ∑ j, |β j| :=
      Finset.single_le_sum (f := fun j ↦ |β j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
    have := abs_nonneg C
    rw [hcdef]
    linarith
  let φ : ∀ i, ContDiffBump (w i) := fun i ↦ ⟨r i / 2, r i, half_pos (hr i), half_lt_self (hr i)⟩
  have hball : ∀ i, closedBall (w i) (φ i).rOut ⊆ V i := fun i ↦ (hprop i).2.2.1
  haveI : CompactSpace (Σ i, (R i).T) := compactSpace_sigma
  refine ⟨O', isOpen_iUnion fun i ↦ isOpen_ball, hcov, hO'K.trans hKO,
    ⟨LowerRepresentation.mk (Σ i, (R i).T) (fun s y ↦ c + φ s.1 y * ((R s.1).F s.2 y - c))
      ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact ((R s.1).contDiff_cutoff (φ s.1) c le_rfl (hprop s.1).2.1 (hball s.1) s.2).contDiffOn
  · intro j hj
    have hj' : j ≤ 1 := by exact_mod_cast hj
    refine Continuous.continuousOn (continuous_iff_continuousAt.2 ?_)
    rintro ⟨⟨i, t⟩, x⟩
    have hψ : IsOpenEmbedding (Prod.map (Sigma.mk (β := fun i ↦ (R i).T) i) (id : E → E)) :=
      (Topology.IsOpenEmbedding.sigmaMk (σ := fun i ↦ (R i).T) (i := i)).prodMap
        Topology.IsOpenEmbedding.id
    have hcomp : Continuous fun q : (R i).T × E ↦
        iteratedFDeriv ℝ j (fun y ↦ c + φ i y * ((R i).F q.1 y - c)) q.2 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj' with rfl | rfl
      · refine ((continuousMultilinearCurryFin0 ℝ E ℝ).symm.continuous.comp
          ((R i).continuous_cutoff (φ i) c (hprop i).2.1 (hball i))).congr fun q ↦ ?_
        rw [iteratedFDeriv_zero_eq_comp]
        rfl
      · refine ((continuousMultilinearCurryFin1 ℝ E ℝ).symm.continuous.comp
          ((R i).continuous_fderiv_cutoff (φ i) c le_rfl (hprop i).2.1 (hball i))).congr fun q ↦ ?_
        exact (iteratedFDeriv_one_eq' _ _).symm
    exact (hψ.continuousAt_iff (g := fun p : (Σ i, (R i).T) × E ↦
      iteratedFDeriv ℝ j (fun y ↦ c + φ p.1.1 y * ((R p.1.1).F p.1.2 y - c)) p.2)
      (x := (t, x))).1 hcomp.continuousAt
  · rintro ⟨i, t⟩ x hx
    show c + φ i x * ((R i).F t x - c) ≤ f x
    have hfx : -C ≤ f x := by
      have := hC x (hO'K hx)
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (f x)]
    by_cases hd : x ∈ ball (w i) (r i)
    · have hxV : x ∈ V i := (hprop i).2.2.1 (ball_subset_closedBall hd)
      have hF : -|β i| ≤ (R i).F t x := by
        have h := hβ i (t, x) ⟨trivial, ball_subset_closedBall hd⟩
        rw [Real.norm_eq_abs] at h
        linarith [neg_abs_le ((R i).F t x), le_abs_self (β i)]
      have h1 : 0 ≤ (R i).F t x - c := by linarith [hcβ i]
      have h2 : φ i x ≤ 1 := (φ i).le_one
      have h4 := (R i).le t x hxV
      nlinarith [mul_le_mul_of_nonneg_right h2 h1]
    · have hφ0 : φ i x = 0 := (φ i).zero_of_le_dist (by
        rw [mem_ball, not_lt] at hd
        exact hd)
      rw [hφ0, zero_mul, add_zero]
      linarith
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨t, ht⟩ := (R i).exists_eq x (hhalf i (ball_subset_closedBall hi))
    refine ⟨⟨i, t⟩, ?_⟩
    show c + φ i x * ((R i).F t x - c) = f x
    rw [(φ i).one_of_mem_closedBall (ball_subset_closedBall hi), one_mul, ht]
    ring

/-- **Proposition 10.54** (representations of subsmoothness): if `f` is lower-`Cᵏ` (`k ≥ 1`) on
an open set `O`, then for every compact `B ⊂ O` there is an open `O'` with `B ⊂ O' ⊂ O` and a
single representation of `f` valid on all of `O'`. -/
theorem IsLowerCOn.exists_common_representation {k : ℕ∞} {f : E → ℝ} {O : Set E}
    (hf : IsLowerCOn k f O) (hk : 1 ≤ k) {B : Set E} (hB : IsCompact B) (hBO : B ⊆ O) :
    ∃ O' : Set E, IsOpen O' ∧ B ⊆ O' ∧ O' ⊆ O ∧ Nonempty (LowerRepresentation k f O') := by
  by_cases hk2 : 2 ≤ k
  · obtain ⟨O', h1, h2, h3, ⟨R⟩⟩ := (hf.mono hk2).exists_common_representation_two hB hBO
    exact ⟨O', h1, h2, h3, ⟨R.of_le le_top⟩⟩
  · induction k using ENat.recTopCoe with
    | top => exact absurd le_top hk2
    | coe n =>
      have h1 : 1 ≤ n := by exact_mod_cast hk
      have h2 : ¬ 2 ≤ n := fun h ↦ hk2 (by exact_mod_cast h)
      obtain rfl : n = 1 := by omega
      exact hf.exists_common_representation_one hB hBO

end RW
