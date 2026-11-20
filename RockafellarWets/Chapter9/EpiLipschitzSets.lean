/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Local Lipschitz epigraphs

The ambient extension of the height function below is constant along the
vertical direction. Its restriction to the perpendicular hyperplane is
therefore exactly the height function in the geometric definition.
-/

import RockafellarWets.Chapter6.InteriorTangents
import RockafellarWets.Chapter6.ConvexifiedCones
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A local epigraph viewed in the unit direction `e`. The function is extended
constantly off the perpendicular hyperplane, so no choice of coordinates on
that hyperplane is needed. At a boundary point its value at `x` is zero. -/
def IsEpiLipschitzAt (C : Set E) (x : E) : Prop :=
  ∃ (e : E) (g : E → ℝ) (k : ℝ≥0), ‖e‖ = 1 ∧ LipschitzWith k g ∧
    (∀ (y : E) (t : ℝ), g (y + t • e) = g y) ∧
    ∀ᶠ y in nhds x, y ∈ C ↔ g y ≤ ⟪e, y - x⟫_ℝ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem exists_lipschitz_minimum {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (φ : E → E → ℝ) (k : ℝ≥0)
    (hc : ∀ y, ContinuousOn (φ y) K)
    (hL : ∀ a ∈ K, LipschitzWith k (fun y ↦ φ y a)) :
    ∃ g : E → ℝ, LipschitzWith k g ∧
      ∀ y, ∃ a ∈ K, g y = φ y a ∧ ∀ b ∈ K, g y ≤ φ y b := by
  classical
  have hmin (y : E) := hK.exists_isMinOn hne (hc y)
  choose a ha hm using hmin
  let g := fun y ↦ φ y (a y)
  have hb (y b : E) (hb : b ∈ K) : g y ≤ φ y b := hm y hb
  refine ⟨g, LipschitzWith.of_le_add_mul k (fun y z ↦ ?_), ?_⟩
  · have hd := (hL (a z) (ha z)).dist_le_mul y z
    rw [Real.dist_eq] at hd
    have hh := le_abs_self (φ y (a z) - φ z (a z))
    have hm' := hb y (a z) (ha z)
    change φ y (a y) ≤ φ z (a z) + (k:ℝ) * dist y z
    dsimp [g] at hm'
    linarith
  · intro y
    exact ⟨a y,ha y,rfl,hb y⟩

private theorem exists_unit_interior_tangent [Nontrivial E]
    {C : Set E} {x : E} (hx : x ∈ C) (hl : IsLocallyClosedAt C x)
    (hp : IsPointed (normalCone C x)) :
    ∃ e : E, ‖e‖ = 1 ∧ e ∈ interior (regularTangentCone C x) := by
  obtain ⟨w,hw⟩ := (isPointed_normalCone_iff_interior_regularTangentCone_nonempty hx hl).mp hp
  have hinf := infinite_of_mem_nhds w (isOpen_interior.mem_nhds hw)
  obtain ⟨v,hv,hv0⟩ := (hinf.diff (finite_singleton (0:E))).nonempty
  have hv0' : v ≠ 0 := by simpa using hv0
  refine ⟨‖v‖⁻¹ • v,norm_smul_inv_norm hv0',?_⟩
  rw [mem_interior_regularTangentCone_iff_unit_normal_inner_lt hx hl] at hv ⊢
  intro n hn hnorm
  rw [real_inner_smul_right]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr (norm_pos_iff.mpr hv0')) (hv n hn hnorm)

/-- The geometric construction behind Exercise 9.42(a): a compact local slice
and the upward cones based at its points produce a Lipschitz height function. -/
theorem isEpiLipschitzAt_of_pointed [Nontrivial E]
    {C : Set E} {x : E} (hx : x ∈ C) (hl : IsLocallyClosedAt C x)
    (hp : IsPointed (normalCone C x)) : IsEpiLipschitzAt C x := by
  classical
  obtain ⟨e,he,het⟩ := exists_unit_interior_tangent hx hl hp
  obtain ⟨W,hW,V,hV,ε,hε,hstep⟩ :=
    (mem_interior_regularTangentCone_iff_uniform_recession hx hl).mp het
  obtain ⟨δ,hδ,hδW⟩ := Metric.mem_nhds_iff.mp hW
  obtain ⟨T,hT,hTc,hCT⟩ := hl
  obtain ⟨d,hd,hdVT⟩ := Metric.mem_nhds_iff.mp (inter_mem hV hT)
  let r := min d ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrd : r < d := by dsimp [r]; linarith [min_le_left d ε]
  have hrε : 2*r < ε := by dsimp [r]; linarith [min_le_right d ε]
  let K := C ∩ closedBall x r
  have hKT : closedBall x r ⊆ T := fun a ha ↦
    (hdVT ((mem_closedBall.mp ha).trans_lt hrd)).2
  have hKclosed : IsClosed K := by
    have heq : K = (C ∩ T) ∩ closedBall x r := by
      ext a; constructor
      · intro h; exact ⟨⟨h.1,hKT h.2⟩,h.2⟩
      · intro h; exact ⟨h.1.1,h.2⟩
    rw [heq]; exact hCT.inter isClosed_closedBall
  have hK : IsCompact K := (isCompact_closedBall x r).of_isClosed_subset hKclosed inter_subset_right
  have hxK : x ∈ K := ⟨hx,mem_closedBall_self hr.le⟩
  let P : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - (innerSL ℝ e).smulRight e
  have hP (y : E) : P y = y - ⟪e,y⟫_ℝ • e := rfl
  have hee : ⟪e,e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  have hPe : P e = 0 := by rw [hP,hee,one_smul,sub_self]
  let L := 2 / δ
  have hL : 0 < L := by dsimp [L]; positivity
  let k : ℝ≥0 := ⟨L * ‖P‖,mul_nonneg hL.le (norm_nonneg _)⟩
  let φ := fun (y a : E) ↦ ⟪e,a-x⟫_ℝ + L * ‖P (y-a)‖
  have hφL (a : E) : LipschitzWith k (fun y ↦ φ y a) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simp only [φ,Real.dist_eq,add_sub_add_left_eq_sub]
    rw [← mul_sub,abs_mul,abs_of_pos hL]
    calc
      L * |‖P (y-a)‖ - ‖P (z-a)‖| ≤ L * ‖P (y-a) - P (z-a)‖ :=
        mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) hL.le
      _ = L * ‖P (y-z)‖ := by rw [← map_sub]; congr 2; abel
      _ ≤ L * (‖P‖ * ‖y-z‖) := mul_le_mul_of_nonneg_left (P.le_opNorm _) hL.le
      _ = (k:ℝ) * dist y z := by rw [dist_eq_norm]; dsimp [k]; ring
  obtain ⟨g,hg,hmin⟩ := exists_lipschitz_minimum hK ⟨x,hxK⟩ φ k
    (fun y ↦ by dsimp [φ]; fun_prop) (fun a _ ↦ hφL a)
  have hginv (y : E) (t : ℝ) : g (y+t•e) = g y := by
    have hφeq (a : E) : φ (y+t•e) a = φ y a := by
      dsimp [φ]
      congr 2
      have heq : y+t•e-a = (y-a)+t•e := by abel
      rw [heq,map_add,map_smul,hPe,smul_zero,add_zero]
    obtain ⟨a,ha,hga,hmina⟩ := hmin y
    obtain ⟨b,hb,hgb,hminb⟩ := hmin (y+t•e)
    apply le_antisymm
    · rw [hga,← hφeq]; exact hminb a ha
    · rw [hgb,hφeq]; exact hmina b hb
  refine ⟨e,g,k,he,hg,hginv,?_⟩
  filter_upwards [ball_mem_nhds x hr] with y hy
  constructor
  · intro hyC
    obtain ⟨a,ha,hga,hmina⟩ := hmin y
    have hb := hmina y ⟨hyC,mem_closedBall.mpr (mem_ball.mp hy).le⟩
    simpa [φ] using hb
  · intro hyheight
    obtain ⟨a,ha,hga,hmina⟩ := hmin y
    have haV : a ∈ V := (hdVT ((mem_closedBall.mp ha.2).trans_lt hrd)).1
    have hsmall : ‖y-a‖ < 2*r := by
      calc
        ‖y-a‖ = dist y a := (dist_eq_norm _ _).symm
        _ ≤ dist y x + dist a x := dist_triangle_right _ _ _
        _ < 2*r := by linarith [mem_ball.mp hy,mem_closedBall.mp ha.2]
    let t := ⟪e,y-a⟫_ℝ
    have hcone : L * ‖P (y-a)‖ ≤ t := by
      rw [hga] at hyheight
      dsimp [φ] at hyheight
      dsimp [t]
      simp only [inner_sub_right] at hyheight ⊢
      linarith
    have ht : 0 ≤ t := (mul_nonneg hL.le (norm_nonneg _)).trans hcone
    have htε : t ≤ ε := by
      have hh := real_inner_le_norm e (y-a)
      rw [he,one_mul] at hh
      exact hh.trans (hsmall.le.trans hrε.le)
    by_cases ht0 : t = 0
    · have hP0 : P (y-a) = 0 := by
        apply norm_eq_zero.mp
        nlinarith [norm_nonneg (P (y-a))]
      have hya : y = a := by
        have hh := hP (y-a)
        rw [hP0,show ⟪e,y-a⟫_ℝ = 0 from ht0,zero_smul,sub_zero] at hh
        exact sub_eq_zero.mp hh.symm
      exact hya ▸ ha.1
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      let z := e + t⁻¹ • P (y-a)
      have hz : z ∈ W := by
        apply hδW
        rw [mem_ball,dist_eq_norm]
        have hze : z-e = t⁻¹ • P (y-a) := by dsimp [z]; abel
        rw [hze,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr htpos)]
        have hpbound : ‖P (y-a)‖ ≤ t*δ/2 := by
          dsimp [L] at hcone
          have hh := (div_le_iff₀ hδ).mp (show 2*‖P (y-a)‖/δ ≤ t by simpa only [div_mul_eq_mul_div] using hcone)
          nlinarith
        calc
          t⁻¹ * ‖P (y-a)‖ ≤ t⁻¹ * (t*δ/2) := mul_le_mul_of_nonneg_left hpbound (inv_nonneg.mpr ht)
          _ = δ/2 := by field_simp
          _ < δ := by linarith
      have hrec := hstep a ⟨ha.1,haV⟩ t ⟨ht,htε⟩ z hz
      have heq : a+t•z = y := by
        dsimp [z]
        rw [smul_add,smul_smul,mul_inv_cancel₀ ht0,one_smul,hP]
        change a + (t • e + (y-a-t•e)) = y
        abel
      rwa [heq] at hrec


omit [FiniteDimensional ℝ E] in
/-- Local Lipschitz epigraphs are locally closed. -/
theorem IsEpiLipschitzAt.isLocallyClosedAt {C : Set E} {x : E}
    (h : IsEpiLipschitzAt C x) : IsLocallyClosedAt C x := by
  obtain ⟨e,g,k,he,hg,hgi,hrep⟩ := h
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hrep
  let Q := {y : E | g y ≤ ⟪e,y-x⟫_ℝ}
  have hQc : IsClosed Q := isClosed_le hg.continuous (by fun_prop)
  have heq : C ∩ closedBall x (r/2) = Q ∩ closedBall x (r/2) := by
    ext y
    by_cases hy : y ∈ closedBall x (r/2)
    · have hyr : y ∈ ball x r := by
        rw [mem_ball]; have hh := mem_closedBall.mp hy; linarith
      simp only [mem_inter_iff,hy,and_true]
      exact hrsub hyr
    · simp [hy]
  refine ⟨closedBall x (r/2),closedBall_mem_nhds x (by positivity),isClosed_closedBall,?_⟩
  rw [heq]
  exact hQc.inter isClosed_closedBall

/-- The vertical axis of a Lipschitz epigraph is an interior regular tangent
direction. The proof gives uniform steps for a whole cone of directions. -/
theorem IsEpiLipschitzAt.interior_regularTangentCone_nonempty {C : Set E} {x : E}
    (h : IsEpiLipschitzAt C x) (hx : x ∈ C) :
    (interior (regularTangentCone C x)).Nonempty := by
  have hl := h.isLocallyClosedAt
  obtain ⟨e,g,k,he,hg,hgi,hrep⟩ := h
  refine ⟨e,(mem_interior_regularTangentCone_iff_uniform_recession hx hl).mpr ?_⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hrep
  let δ : ℝ := 1/(2*((k:ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : ((k:ℝ)+1)*δ = 1/2 := by dsimp [δ]; field_simp
  have hδ1 : δ < 1 := by
    calc
      δ = 1*δ := (one_mul δ).symm
      _ ≤ ((k:ℝ)+1)*δ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left k.2) hδ.le
      _ = 1/2 := hδeq
      _ < 1 := by norm_num
  refine ⟨ball e δ,ball_mem_nhds e hδ,ball x (r/2),
    ball_mem_nhds x (by positivity),r/8,by positivity,?_⟩
  intro y hy τ hτ z hz
  have hze : ‖z-e‖ < δ := by simpa [dist_eq_norm] using hz
  have hzn : ‖z‖ < 2 := by
    have hh := norm_add_le (z-e) e
    rw [sub_add_cancel,he] at hh
    linarith
  have hnew : y+τ•z ∈ ball x r := by
    rw [mem_ball,dist_eq_norm]
    have heq : y+τ•z-x = (y-x)+τ•z := by abel
    rw [heq]
    calc
      ‖y-x+τ•z‖ ≤ ‖y-x‖+‖τ•z‖ := norm_add_le _ _
      _ = ‖y-x‖+τ*‖z‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hτ.1]
      _ < r := by have hh : ‖y-x‖ < r/2 := by simpa [dist_eq_norm] using hy.2
                  nlinarith [hτ.1,hτ.2]
  apply (hrsub hnew).mpr
  have hyheight : g y ≤ ⟪e,y-x⟫_ℝ := (hrsub (by
    rw [mem_ball]; have hh := mem_ball.mp hy.2; linarith)).mp hy.1
  have hee : ⟪e,e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  have hin : 1-‖z-e‖ ≤ ⟪e,z⟫_ℝ := by
    have hh := abs_real_inner_le_norm e (z-e)
    rw [he,one_mul,inner_sub_right,hee] at hh
    have hh' := neg_le_abs (⟪e,z⟫_ℝ-1)
    linarith
  have hkz : (k:ℝ)*‖z-e‖ ≤ ⟪e,z⟫_ℝ := by nlinarith [k.2]
  have heq : y+τ•(z-e)+τ•e = y+τ•z := by rw [smul_sub]; abel
  have hgeq : g (y+τ•z) = g (y+τ•(z-e)) := by
    simpa only [heq] using hgi (y+τ•(z-e)) τ
  have hgdiff := hg.dist_le_mul (y+τ•(z-e)) y
  rw [Real.dist_eq,dist_eq_norm,add_sub_cancel_left,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg hτ.1] at hgdiff
  have hgle := le_abs_self (g (y+τ•(z-e))-g y)
  have heq' : y+τ•z-x = (y-x)+τ•z := by abel
  rw [hgeq,heq',inner_add_right,real_inner_smul_right]
  nlinarith [mul_le_mul_of_nonneg_left hkz hτ.1]

/-- **Exercise 9.42(a)**: a local epigraph representation is equivalent to
local closedness and pointedness of the limiting normal cone. -/
theorem isEpiLipschitzAt_iff_locallyClosed_pointed [Nontrivial E]
    {C : Set E} {x : E} (hx : x ∈ C) :
    IsEpiLipschitzAt C x ↔ IsLocallyClosedAt C x ∧ IsPointed (normalCone C x) := by
  constructor
  · intro h
    have hl := h.isLocallyClosedAt
    exact ⟨hl,(isPointed_normalCone_iff_interior_regularTangentCone_nonempty hx hl).mpr
      (h.interior_regularTangentCone_nonempty hx)⟩
  · rintro ⟨hl,hp⟩
    exact isEpiLipschitzAt_of_pointed hx hl hp

/-- The boundary-point form has no positive-dimension assumption: a
zero-dimensional space has no feasible boundary points. -/
theorem isEpiLipschitzAt_iff_at_boundary {C : Set E} {x : E}
    (hx : x ∈ C) (hb : x ∉ interior C) :
    IsEpiLipschitzAt C x ↔ IsLocallyClosedAt C x ∧ IsPointed (normalCone C x) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hC : C = univ := eq_univ_of_forall (fun y ↦ (Subsingleton.elim x y) ▸ hx)
    simp [hC] at hb
  · exact isEpiLipschitzAt_iff_locallyClosed_pointed hx

/-- **Exercise 9.42(a)** with the book's literal boundary-point hypothesis.
Local closedness supplies membership in the set at a point of its frontier. -/
theorem isEpiLipschitzAt_iff_at_frontier {C : Set E} {x : E}
    (hx : x ∈ frontier C) :
    IsEpiLipschitzAt C x ↔ IsLocallyClosedAt C x ∧ IsPointed (normalCone C x) := by
  have hmem (hl : IsLocallyClosedAt C x) : x ∈ C := by
    obtain ⟨V,hV,_,hCV⟩ := hl
    have hcl : x ∈ closure (C ∩ V) := by
      apply _root_.mem_closure_iff.mpr
      intro O hO hxO
      obtain ⟨y,⟨hyO,hyV⟩,hyC⟩ := _root_.mem_closure_iff.mp hx.1 (O ∩ interior V)
        (hO.inter isOpen_interior) ⟨hxO,mem_interior_iff_mem_nhds.mpr hV⟩
      exact ⟨y,hyO,hyC,interior_subset hyV⟩
    rw [hCV.closure_eq] at hcl
    exact hcl.1
  constructor
  · intro h
    exact (isEpiLipschitzAt_iff_at_boundary (hmem h.isLocallyClosedAt) hx.2).mp h
  · intro h
    exact (isEpiLipschitzAt_iff_at_boundary (hmem h.1) hx.2).mpr h

omit [FiniteDimensional ℝ E] in
/-- At a boundary point, the epigraph height vanishes at the base point. -/
theorem IsEpiLipschitzAt.exists_height_zero {C : Set E} {x : E}
    (h : IsEpiLipschitzAt C x) (hx : x ∈ C) (hboundary : x ∉ interior C) :
    ∃ (e : E) (g : E → ℝ) (k : ℝ≥0), ‖e‖ = 1 ∧ LipschitzWith k g ∧
      g x = 0 ∧ (∀ (y : E) (t : ℝ), g (y+t•e) = g y) ∧
      ∀ᶠ y in nhds x, y ∈ C ↔ g y ≤ ⟪e,y-x⟫_ℝ := by
  obtain ⟨e,g,k,he,hg,hgi,hrep⟩ := h
  refine ⟨e,g,k,he,hg,?_,hgi,hrep⟩
  have hxheight : g x ≤ 0 := by simpa using (mem_of_mem_nhds hrep).mp hx
  apply le_antisymm hxheight
  by_contra! hneg
  have hcont : Continuous (fun y ↦ g y - ⟪e,y-x⟫_ℝ) := hg.continuous.sub (by fun_prop)
  have hstrict : ∀ᶠ y in nhds x, g y < ⟪e,y-x⟫_ℝ := by
    have hh := hcont.continuousAt.eventually (gt_mem_nhds (show g x-⟪e,x-x⟫_ℝ < 0 by simpa using hneg))
    filter_upwards [hh] with y hy
    exact sub_neg.mp hy
  apply hboundary
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hrep,hstrict] with y hy hys
  exact hy.mpr hys.le

end RW
