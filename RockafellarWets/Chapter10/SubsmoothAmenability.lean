/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: subsmoothness and amenability

**Exercise 10.36**: a function `f : E → ℝ̄` is lower-`C²` around `x̄` (`IsLowerC2Around`: finite
on an open neighborhood of `x̄` on which it is lower-`C²`) if and only if `f` is strongly
amenable at `x̄` and `x̄ ∈ int (dom f)`.

* (⇒) `IsLowerC2Around.stronglyAmenableAt`: by 10.33, near `x̄` the function is
  `g - ρ|·|²` with `g` finite convex; this is `g̃ ∘ F` for the C² mapping
  `F(y) = (y, ρ|y|²)` into `ℓ²(E × ℝ)` and the proper lsc convex
  `g̃(u, s) = g(u) - s` on `IB(x̄, δ) × ℝ` (`∞` elsewhere), whose domain has `F(x̄)` in its
  interior, so the constraint qualification holds trivially (compare 10.24(g)).
* (⇐) `StronglyAmenableAt.isLowerC2Around`: following the guide, for a representation
  `f = g ∘ F` the finiteness of `f` near `x̄` and the constraint qualification force
  `F(x̄) ∈ int (dom g)`: a normal `v` to `cl (dom g)` at `F(x̄)` makes `⟪v, F(·)⟫` locally
  maximal at `x̄`, so `∇F(x̄)* v = 0` and `v = 0`; then 6.19 and `int (cl C) = int C` for convex
  `C`.  There `g` is finite and convex, hence lower-`C^∞` (10.33), and 10.35(b) applies to `F`
  made globally `C²` by a smooth cutoff equal to `1` near `x̄`.
* `isLowerC2Around_iff_stronglyAmenableAt` combines the two directions.
-/

import RockafellarWets.Chapter10.SubsmoothCalculus
import RockafellarWets.Chapter10.Amenability
import RockafellarWets.Chapter6.BoundaryNormals
import RockafellarWets.Chapter6.Optimality

open Filter Function Metric Set Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff

namespace RW

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `f` is lower-`C²` around `x̄`: finite on an open neighborhood `U` of `x̄`, on which its real
values form a lower-`C²` function (Exercise 10.36). -/
def IsLowerC2Around (f : E → EReal) (x : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ (∀ y ∈ U, f y ≠ ⊥ ∧ f y ≠ ⊤) ∧
    IsLowerCOn 2 (fun y ↦ (f y).toReal) U

/-- **Exercise 10.36** (⇒): a function that is lower-`C²` around `x̄` is strongly amenable at
`x̄`, and `x̄` is an interior point of its domain. -/
theorem IsLowerC2Around.stronglyAmenableAt {f : E → EReal} {x : E} (hf : IsLowerC2Around f x) :
    StronglyAmenableAt f x ∧ x ∈ interior (effectiveDomain f) := by
  classical
  obtain ⟨U, hU, hxU, hfin, hlow⟩ := hf
  refine ⟨?_, interior_maximal (fun y hy ↦ lt_top_iff_ne_top.2 (hfin y hy).2) hU hxU⟩
  obtain ⟨δ, hδ, hδU, ρ, hρ, hconv⟩ := hlow.exists_convex_sub_quadratic x hxU
  set fR : E → ℝ := fun y ↦ (f y).toReal with hfR
  set g : E → ℝ := fun y ↦ fR y + ρ * ‖y‖ ^ 2 with hg
  set B := closedBall x (δ / 2) with hB
  have hBδ : B ⊆ ball x δ := closedBall_subset_ball (half_lt_self hδ)
  have hgc : ContinuousOn g (ball x δ) := hconv.continuousOn isOpen_ball
  set outer : WithLp 2 (E × ℝ) → EReal := fun p ↦
    if p.fst ∈ B then ((g p.fst - p.snd : ℝ) : EReal) else ⊤ with houter
  have hin : ∀ p : WithLp 2 (E × ℝ), p.fst ∈ B → outer p = ((g p.fst - p.snd : ℝ) : EReal) :=
    fun p hp ↦ if_pos hp
  have hout : ∀ p : WithLp 2 (E × ℝ), p.fst ∉ B → outer p = ⊤ := fun p hp ↦ if_neg hp
  set inner : E → WithLp 2 (E × ℝ) := fun y ↦ WithLp.toLp 2 (y, ρ * ‖y‖ ^ 2) with hinner
  have hinner_fst : ∀ y, (inner y).fst = y := fun y ↦ rfl
  have hinner_snd : ∀ y, (inner y).snd = ρ * ‖y‖ ^ 2 := fun y ↦ rfl
  have hfst_cont : Continuous fun p : WithLp 2 (E × ℝ) ↦ p.fst := WithLp.continuous_fst 2 E ℝ
  have hsnd_cont : Continuous fun p : WithLp 2 (E × ℝ) ↦ p.snd := WithLp.continuous_snd 2 E ℝ
  -- properness
  have hprop : IsProper outer := by
    refine ⟨⟨inner x, ?_⟩, fun p ↦ ?_⟩
    · rw [hin _ (by rw [hinner_fst]; exact mem_closedBall_self (by linarith))]
      exact EReal.coe_lt_top _
    · by_cases hp : p.fst ∈ B
      · rw [hin p hp]; exact EReal.bot_lt_coe _
      · rw [hout p hp]; exact bot_lt_top
  -- lower semicontinuity
  have hlsc : LowerSemicontinuous outer := by
    intro p c hc
    by_cases hp : p.fst ∈ B
    · rw [hin p hp] at hc
      have h1 : ContinuousAt g p.fst := hgc.continuousAt (isOpen_ball.mem_nhds (hBδ hp))
      have hcont : ContinuousAt (fun q : WithLp 2 (E × ℝ) ↦ ((g q.fst - q.snd : ℝ) : EReal)) p :=
        continuous_coe_real_ereal.continuousAt.comp
          ((h1.comp hfst_cont.continuousAt).sub hsnd_cont.continuousAt)
      filter_upwards [hcont.eventually (lt_mem_nhds hc)] with q hq
      by_cases hq' : q.fst ∈ B
      · rw [hin q hq']; exact hq
      · rw [hout q hq']; exact lt_of_lt_of_le hq le_top
    · have hopen : IsOpen {q : WithLp 2 (E × ℝ) | q.fst ∉ B} :=
        (isClosed_closedBall.preimage hfst_cont).isOpen_compl
      rw [hout p hp] at hc
      filter_upwards [hopen.mem_nhds hp] with q hq
      rw [hout q hq]
      exact hc
  -- convexity of the epigraph
  have hconvex : Convex ℝ (epigraph outer) := by
    intro P hP Q hQ a b ha hb hab
    have hP' : outer P.1 ≤ (P.2 : EReal) := hP
    have hQ' : outer Q.1 ≤ (Q.2 : EReal) := hQ
    have hP1 : P.1.fst ∈ B := by
      by_contra h
      rw [hout _ h] at hP'
      exact (not_le.2 (EReal.coe_lt_top _)) hP'
    have hQ1 : Q.1.fst ∈ B := by
      by_contra h
      rw [hout _ h] at hQ'
      exact (not_le.2 (EReal.coe_lt_top _)) hQ'
    rw [hin _ hP1, EReal.coe_le_coe_iff] at hP'
    rw [hin _ hQ1, EReal.coe_le_coe_iff] at hQ'
    have hfst : (a • P + b • Q).1.fst = a • P.1.fst + b • Q.1.fst := by
      simp [WithLp.add_fst, WithLp.smul_fst]
    have hsnd : (a • P + b • Q).1.snd = a * P.1.snd + b * Q.1.snd := by
      simp [WithLp.add_snd, WithLp.smul_snd]
    have hmem : a • P.1.fst + b • Q.1.fst ∈ B := (convex_closedBall x (δ / 2)) hP1 hQ1 ha hb hab
    show outer (a • P + b • Q).1 ≤ (((a • P + b • Q).2 : ℝ) : EReal)
    rw [hin _ (hfst ▸ hmem), EReal.coe_le_coe_iff, hfst, hsnd]
    have hgconv := hconv.2 (hBδ hP1) (hBδ hQ1) ha hb hab
    simp only [smul_eq_mul, Prod.snd_add, Prod.smul_snd] at hgconv ⊢
    nlinarith [mul_le_mul_of_nonneg_left hP' ha, mul_le_mul_of_nonneg_left hQ' hb]
  -- smoothness of the inner mapping
  have hsmooth : ContDiffOn ℝ 2 inner (ball x (δ / 2)) := by
    have h1 : ContDiff ℝ 2 fun y : E ↦ ((y, ρ * ‖y‖ ^ 2) : E × ℝ) :=
      contDiff_id.prodMk (contDiff_const.mul (contDiff_id.norm_sq ℝ))
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.contDiff.comp h1).contDiffOn
  -- the representation
  have heqOn : ∀ y ∈ ball x (δ / 2), f y = outer (inner y) := by
    intro y hy
    rw [hin _ (by rw [hinner_fst]; exact ball_subset_closedBall hy), hinner_fst, hinner_snd]
    have hyU : y ∈ U := hδU (ball_subset_ball (half_le_self hδ.le) hy)
    rw [show g y - ρ * ‖y‖ ^ 2 = fR y by rw [hg]; ring]
    exact (EReal.coe_toReal (hfin y hyU).2 (hfin y hyU).1).symm
  -- the constraint qualification
  have hqual : ∀ v ∈ normalCone (closure (effectiveDomain outer)) (inner x),
      (fderiv ℝ inner x).adjoint v = 0 → v = 0 := by
    intro v hv _
    have hint : inner x ∈ interior (closure (effectiveDomain outer)) := by
      have hsub : {q : WithLp 2 (E × ℝ) | q.fst ∈ ball x (δ / 2)} ⊆
          closure (effectiveDomain outer) := fun q hq ↦ subset_closure (by
            show outer q < ⊤
            rw [hin q (ball_subset_closedBall hq)]
            exact EReal.coe_lt_top _)
      exact interior_maximal hsub (isOpen_ball.preimage hfst_cont)
        (by show (inner x).fst ∈ ball x (δ / 2); rw [hinner_fst]; exact mem_ball_self (half_pos hδ))
    rw [normalCone_eq_singleton_of_mem_interior hint] at hv
    exact hv
  exact ⟨AmenableFunctionModel.mk (WithLp 2 (E × ℝ)) outer inner (ball x (δ / 2)) isOpen_ball
    (mem_ball_self (half_pos hδ)) (hfin x hxU) hprop hlsc hconvex hsmooth heqOn hqual
    (fun h ↦ absurd h (by decide))⟩

omit [FiniteDimensional ℝ E] in
/-- Restriction of a lower-`Cᵏ` function to an open subset. -/
theorem IsLowerCOn.mono_set {k : ℕ∞} {f : E → ℝ} {O O' : Set E} (hf : IsLowerCOn k f O)
    (hO' : IsOpen O') (hsub : O' ⊆ O) : IsLowerCOn k f O' := by
  intro x hx
  obtain ⟨V, hV, hxV, -, ⟨R⟩⟩ := hf x (hsub hx)
  exact ⟨V ∩ O', hV.inter hO', ⟨hxV, hx⟩, inter_subset_right, ⟨R.restrict inter_subset_left⟩⟩

private theorem interior_closure_eq_interior_of_convex' {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {S : Set F} (hS : Convex ℝ S) :
    interior (closure S) = interior S := by
  by_cases hSne : (interior S).Nonempty
  · exact hS.interior_closure_eq_interior_of_nonempty_interior hSne
  · have hSempty : interior S = ∅ := not_nonempty_iff_eq_empty.1 hSne
    rw [hSempty]
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    apply hSne
    rw [Convex.interior_nonempty_iff_affineSpan_eq_top hS]
    apply top_unique
    have hclosureSub : closure S ⊆ affineSpan ℝ S :=
      closure_minimal (subset_affineSpan ℝ S) (affineSpan ℝ S).closed_of_finiteDimensional
    have hspanClosure : affineSpan ℝ (closure S) = ⊤ :=
      (Convex.interior_nonempty_iff_affineSpan_eq_top hS.closure).1 ⟨x, hx⟩
    rw [← hspanClosure]
    exact affineSpan_le.2 hclosureSub

/-- **Exercise 10.36** (⇐): a function strongly amenable at `x̄` with `x̄ ∈ int (dom f)` is
lower-`C²` around `x̄`. -/
theorem StronglyAmenableAt.isLowerC2Around {f : E → EReal} {x : E} (hf : StronglyAmenableAt f x)
    (hx : x ∈ interior (effectiveDomain f)) : IsLowerC2Around f x := by
  classical
  obtain ⟨M⟩ := hf
  haveI := M.finiteTarget
  set G := M.inner with hGdef
  set g := M.outer with hgdef
  set N := M.neighborhood with hNdef
  have hN : IsOpen N := M.isOpen
  have hxN : x ∈ N := M.mem
  set W := N ∩ interior (effectiveDomain f) with hWdef
  have hW : IsOpen W := hN.inter isOpen_interior
  have hxW : x ∈ W := ⟨hxN, hx⟩
  have hgbot : ∀ z, g z ≠ ⊥ := fun z ↦ ne_of_gt (M.proper.2 z)
  have hGdom : ∀ y ∈ W, G y ∈ effectiveDomain g := fun y hy ↦ by
    have h0 : y ∈ effectiveDomain f := interior_subset hy.2
    have h1 : f y < ⊤ := h0
    rw [M.eqOn y hy.1] at h1
    exact h1
  -- the domain of `g` is convex
  have hdomconv : Convex ℝ (effectiveDomain g) := by
    intro a ha b hb s t hs ht hst
    have hca : g a = ((g a).toReal : EReal) := (EReal.coe_toReal (ne_of_lt ha) (hgbot a)).symm
    have hcb : g b = ((g b).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hb) (hgbot b)).symm
    have hea : (a, (g a).toReal) ∈ epigraph g := by show g a ≤ _; rw [← hca]
    have heb : (b, (g b).toReal) ∈ epigraph g := by show g b ≤ _; rw [← hcb]
    have hc := M.convex hea heb hs ht hst
    exact lt_of_le_of_lt (show g (s • a + t • b) ≤ _ from hc) (EReal.coe_lt_top _)
  -- the normal cone to the closure of the domain at `G x` is trivial
  set D := closure (effectiveDomain g) with hDdef
  have hDconv : Convex ℝ D := hdomconv.closure
  have hGxD : G x ∈ D := subset_closure (hGdom x hxW)
  have hnormal : normalCone D (G x) = {0} := by
    refine Subset.antisymm (fun v hv ↦ ?_) (singleton_subset_iff.2 ?_)
    · have hv' : ∀ z ∈ D, ⟪v, z - G x⟫_ℝ ≤ 0 := by
        have h1 := (neg_mem_normalCone_iff_forall_inner_nonneg_of_convex hDconv hGxD
          (g := -v)).1 (by rwa [neg_neg])
        intro z hz
        have h2 := h1 z hz
        rw [inner_neg_left] at h2
        linarith
      have hmax : IsLocalMax (fun y ↦ ⟪v, G y⟫_ℝ) x := by
        filter_upwards [hW.mem_nhds hxW] with y hy
        have h1 := hv' (G y) (subset_closure (hGdom y hy))
        rw [inner_sub_right] at h1
        linarith
      have hGd : HasFDerivAt G (fderiv ℝ G x) x :=
        ((M.smooth.differentiableOn (by norm_num) x hxN).differentiableAt
          (hN.mem_nhds hxN)).hasFDerivAt
      have hφd : HasFDerivAt (fun y ↦ ⟪v, G y⟫_ℝ) ((innerSL ℝ v).comp (fderiv ℝ G x)) x :=
        (innerSL ℝ v).hasFDerivAt.comp x hGd
      have h0 := hmax.hasFDerivAt_eq_zero hφd
      have hadj : (fderiv ℝ G x).adjoint v = 0 := by
        refine ext_inner_right ℝ fun h ↦ ?_
        rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
        have h2 := congrArg (fun L : E →L[ℝ] ℝ ↦ L h) h0
        simpa using h2
      rw [M.qualification v hv hadj]
      exact mem_singleton 0
    · have h1 := (neg_mem_normalCone_iff_forall_inner_nonneg_of_convex hDconv hGxD
        (g := (0 : M.Target))).2 (fun z _ ↦ by simp)
      rwa [neg_zero] at h1
  have hGint : G x ∈ interior (effectiveDomain g) := by
    rw [← interior_closure_eq_interior_of_convex' hdomconv]
    exact (mem_interior_iff_normalCone_eq_singleton isClosed_closure).2 hnormal
  -- on the interior of the domain, `g` is a finite convex function
  set O' := interior (effectiveDomain g) with hO'def
  have hO'conv : Convex ℝ O' := hdomconv.interior
  set gR : M.Target → ℝ := fun z ↦ (g z).toReal with hgR
  have hgfin : ∀ z ∈ O', g z = (gR z : EReal) := fun z hz ↦ by
    have h0 : z ∈ effectiveDomain g := interior_subset hz
    have h1 : g z < ⊤ := h0
    exact (EReal.coe_toReal (ne_of_lt h1) (hgbot z)).symm
  have hgconv : ConvexOn ℝ O' gR := by
    refine ⟨hO'conv, fun a ha b hb s t hs ht hst ↦ ?_⟩
    have hea : (a, gR a) ∈ epigraph g := by show g a ≤ _; rw [hgfin a ha]
    have heb : (b, gR b) ∈ epigraph g := by show g b ≤ _; rw [hgfin b hb]
    have hc : g (s • a + t • b) ≤ ((s * gR a + t * gR b : ℝ) : EReal) := M.convex hea heb hs ht hst
    rw [hgfin _ (hO'conv ha hb hs ht hst), EReal.coe_le_coe_iff] at hc
    simpa [smul_eq_mul] using hc
  have hglow : IsLowerCOn 2 gR O' := (ConvexOn.isLowerCOn isOpen_interior hgconv).mono le_top
  -- a globally `C²` modification of `G` agreeing with `G` near `x`
  obtain ⟨r, hr, hrN⟩ := Metric.isOpen_iff.1 hN x hxN
  let φ : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hsupp : tsupport φ ⊆ N := by
    rw [φ.tsupport_eq]
    exact (closedBall_subset_ball (by linarith : r / 2 < r)).trans hrN
  set Gt : E → M.Target := fun y ↦ φ y • G y with hGt
  have hGtc : ContDiff ℝ 2 Gt := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ N
    · exact φ.contDiff.contDiffAt.smul (M.smooth.contDiffAt (hN.mem_nhds hy))
    · have hy' : y ∉ tsupport φ := fun h ↦ hy (hsupp h)
      have hzero : Gt =ᶠ[𝓝 y] fun _ ↦ 0 := by
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hy'] with z hz
        simp only [hGt, image_eq_zero_of_notMem_tsupport hz, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  have hGt_eq : ∀ y ∈ ball x (r / 4), Gt y = G y := fun y hy ↦ by
    simp only [hGt, φ.one_of_mem_closedBall (ball_subset_closedBall hy), one_smul]
  have hcomp := hglow.comp_two hGtc
  set U := ball x (r / 4) ∩ W ∩ Gt ⁻¹' O' with hUdef
  have hU : IsOpen U := (isOpen_ball.inter hW).inter (isOpen_interior.preimage hGtc.continuous)
  have hx4 : x ∈ ball x (r / 4) := mem_ball_self (by positivity)
  have hxU : x ∈ U := ⟨⟨hx4, hxW⟩, by show Gt x ∈ O'; rw [hGt_eq x hx4]; exact hGint⟩
  refine ⟨U, hU, hxU, fun y hy ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [M.eqOn y hy.1.2.1]
    exact hgbot _
  · have h0 : y ∈ effectiveDomain f := interior_subset hy.1.2.2
    have h1 : f y < ⊤ := h0
    exact ne_of_lt h1
  · refine (hcomp.mono_set hU inter_subset_right).congr fun y hy ↦ ?_
    show gR (Gt y) = (f y).toReal
    rw [hGt_eq y hy.1.1, M.eqOn y hy.1.2.1]

/-- **Exercise 10.36**: `f` is lower-`C²` around `x̄` if and only if it is strongly amenable at
`x̄` and `x̄ ∈ int (dom f)`. -/
theorem isLowerC2Around_iff_stronglyAmenableAt {f : E → EReal} {x : E} :
    IsLowerC2Around f x ↔ StronglyAmenableAt f x ∧ x ∈ interior (effectiveDomain f) :=
  ⟨fun h ↦ h.stronglyAmenableAt, fun h ↦ h.1.isLowerC2Around h.2⟩

end RW
