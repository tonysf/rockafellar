/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 9: Truncating mappings with convex graphs
-/

import RockafellarWets.Chapter5.ConvexSemicontinuity
import RockafellarWets.Chapter9.ConvexSetValuedBounds

open Filter Metric Set Topology
open scoped ENNReal NNReal

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {S : E → Set F} {X : Set E}

/-- The distance from zero to the most distant fiber on the reference set,
with the value infinity allowed for empty fibers. -/
noncomputable def svZeroRadius (S : E → Set F) (X : Set E) : ℝ≥0∞ :=
  ⨆ a : X, infEDist 0 (S a)

/-- The distance from the reference set to the inputs whose fibers miss
the open ball of radius `R`. It is infinity if no fiber misses the ball. -/
noncomputable def svBadFiberDistance (S : E → Set F) (X : Set E) (R : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ a : {z | R ≤ infEDist 0 (S z)}, infEDist (a : E) X

/-- Convex interpolation gives a single explicit transport step toward a
fiber, provided bounded fibers exist throughout a ball about the target. -/
theorem SvGraphConvex.truncation_transport_step (h : SvGraphConvex S) {a b : E} {d r : ℝ}
    (hd : 0 < d) (hcover : ∀ c ∈ closedBall a d, (S c ∩ closedBall (0:F) r).Nonempty)
    {v : F} (hv : v ∈ S b ∩ closedBall (0:F) r) :
    ∃ w ∈ S a ∩ closedBall (0:F) r,
      dist v w ≤ (2*r*dist a b)/(d+dist a b) := by
  rcases eq_or_ne a b with rfl | hab
  · exact ⟨v,hv,by simp⟩
  let t := dist a b
  have ht : 0 < t := dist_pos.2 hab
  let c := a + (d/t) • (a-b)
  have hc : c ∈ closedBall a d := by
    rw [mem_closedBall,dist_eq_norm,show c-a = (d/t) • (a-b) by dsimp [c]; abel,
      norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hd ht),← dist_eq_norm]
    exact (div_mul_cancel₀ d ht.ne').le
  obtain ⟨u,hu,hur⟩ := hcover c hc
  let s := t/(d+t)
  have hs : 0 ≤ s := div_nonneg ht.le (by positivity)
  have hsone : s ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hsdt : s*(d/t) = 1-s := by dsimp [s]; field_simp; ring
  have hav : (1-s) • b+s • c = a := by
    dsimp only [c]; rw [smul_add,smul_smul,hsdt]; module
  have hg := h (x := (b,v)) hv.1 (y := (c,u)) hu (sub_nonneg.2 hsone) hs (show 1-s+s=1 by ring)
  change (1-s) • v+s • u ∈ S ((1-s) • b+s • c) at hg
  rw [hav] at hg
  refine ⟨_,⟨hg,convex_closedBall (0:F) r hv.2 hur (sub_nonneg.2 hsone) hs (by ring)⟩,?_⟩
  rw [dist_eq_norm,show v - ((1-s) • v+s • u) = s • (v-u) by module,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  calc
    _ ≤ s*(2*r) := mul_le_mul_of_nonneg_left ((norm_sub_le v u).trans (by
      linarith [mem_closedBall_zero_iff.1 hv.2,mem_closedBall_zero_iff.1 hur])) hs
    _ = _ := by dsimp [s,t]; ring

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem truncation_nonempty_of_lt_badFiberDistance {r : ℝ≥0} {R : ℝ≥0∞} (hR : R ≤ r) {a c : E} (ha : a ∈ X)
    (hc : edist c a < svBadFiberDistance S X R) : (S c ∩ closedBall (0:F) (r:ℝ)).Nonempty := by
  have hf : infEDist 0 (S c) < (r : ℝ≥0∞) := by
    by_contra! h
    exact hc.not_ge ((iInf_le (fun w : {z | R ≤ infEDist 0 (S z)} ↦ infEDist (w:E) X) ⟨c,hR.trans h⟩).trans
      (infEDist_le_edist_of_mem ha))
  obtain ⟨u,hu,hur⟩ := infEDist_lt_iff.1 hf
  rw [edist_nndist,ENNReal.coe_lt_coe] at hur
  exact ⟨u,hu,mem_closedBall_zero_iff.2 (by simpa only [← dist_zero_left] using (show dist 0 u ≤ r from hur.le))⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem SvIscAt.upperSemicontinuousAt_infEDist (x : E) (hi : SvIscAt S x) (u : F) :
    UpperSemicontinuousAt (fun a ↦ infEDist u (S a)) x := by
  intro k hk
  obtain ⟨v,hv,hvk⟩ := infEDist_lt_iff.1 hk
  have hV : {z | edist u z < k} ∈ 𝓝 v := (isOpen_lt (by fun_prop) continuous_const).mem_nhds hvk
  filter_upwards [hi hv _ hV] with a ha
  obtain ⟨w,hw,hwk⟩ := ha
  exact infEDist_lt_iff.2 ⟨w,hw,hwk⟩

/-- The radius in Theorem 9.33(b) is finite, including on the empty set. -/
theorem SvGraphConvex.svZeroRadius_lt_top (h : SvGraphConvex S) (hX : IsCompact X)
    (hi : X ⊆ interior (svDom S)) : svZeroRadius S X < ⊤ := by
  rcases X.eq_empty_or_nonempty with rfl | hn
  · simp [svZeroRadius]
  have hcont : UpperSemicontinuousOn (fun a ↦ infEDist 0 (S a)) X := fun a ha ↦
    ((h.svIscAt (hi ha)).upperSemicontinuousAt_infEDist _ 0).upperSemicontinuousWithinAt X
  obtain ⟨a,ha,hmax⟩ := hcont.exists_isMaxOn hn hX
  exact lt_of_le_of_lt (iSup_le fun z : X ↦ hmax z.property) (lt_top_iff_ne_top.2
    (infEDist_ne_top (show (S a).Nonempty from interior_subset (s := svDom S) (hi ha))))

/-- The denominator in the explicit estimate of 9.33(b) is positive,
including the infinite-distance case. -/
theorem SvGraphConvex.svBadFiberDistance_pos (h : SvGraphConvex S) (hX : IsCompact X)
    (hi : X ⊆ interior (svDom S)) {R : ℝ≥0∞} (hR : svZeroRadius S X < R) :
    0 < svBadFiberDistance S X R := by
  let U := {a | infEDist 0 (S a) < R}
  have hsub : X ⊆ interior U := by
    intro a ha
    apply mem_interior_iff_mem_nhds.2
    exact (h.svIscAt (hi ha)).upperSemicontinuousAt_infEDist _ 0 R
      ((le_iSup (fun z : X ↦ infEDist 0 (S z)) ⟨a,ha⟩).trans_lt hR)
  obtain ⟨r,hr,hu⟩ := exists_pos_forall_lt_edist hX isOpen_interior.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 hsub)
  apply lt_of_lt_of_le (ENNReal.coe_pos.2 hr) (le_iInf fun z ↦ le_infEDist.2 (fun a ha ↦ ?_))
  rw [edist_comm]
  have zout : (z : E) ∉ interior U := by
    intro hz
    have hlt : infEDist 0 (S z) < R := interior_subset (s := U) hz
    exact (show R ≤ infEDist 0 (S z) from z.property).not_gt hlt
  exact (hu a ha z zout).le

omit [FiniteDimensional ℝ E] in
/-- In (9.16) the distance to the bad fibers gives the exact displayed
constant. A missing bad set yields constant zero. -/
theorem SvGraphConvex.truncation_transport (h : SvGraphConvex S) (hclosed : ∀ a ∈ X, IsClosed (S a))
    {R : ℝ≥0∞} (hD : 0 < svBadFiberDistance S X R) {r : ℝ≥0} (hr : R ≤ r)
    {a : E} (ha : a ∈ X) (b : E) {v : F} (hv : v ∈ S b ∩ closedBall (0:F) (r:ℝ)) :
    ∃ w ∈ S a ∩ closedBall (0:F) (r:ℝ),
      dist v w ≤ (2/(svBadFiberDistance S X R).toReal)*(r:ℝ)*dist a b := by
  let η := svBadFiberDistance S X R
  have hη : 0 < η := hD
  have hn := truncation_nonempty_of_lt_badFiberDistance hr ha (c := a) (by simpa using hD)
  obtain ⟨w,hw,hmin⟩ := ((hclosed a ha).inter isClosed_closedBall).exists_infDist_eq_dist hn v
  refine ⟨w,hw,?_⟩
  by_contra! hbad
  let M := 2*(r:ℝ)*dist a b
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hp : 0 < dist v w := lt_of_le_of_lt (by positivity) hbad
  have hlt : ENNReal.ofReal (M/(dist v w)) < η := by
    rcases eq_or_ne η ⊤ with he | he
    · rw [he]; exact ENNReal.ofReal_lt_top
    · have hepos : 0 < η.toReal := ENNReal.toReal_pos hη.ne' he
      conv_rhs => rw [← ENNReal.ofReal_toReal he]
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (div_nonneg hM hp.le)).2
      apply (div_lt_iff₀ hp).2
      have hb : M/η.toReal < dist v w := by
        convert hbad using 1; dsimp [M,η]; ring
      linarith [(div_lt_iff₀ hepos).1 hb]
  obtain ⟨d,hlo,hhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  have hd' : M/dist v w < (d:ℝ) := by
    rw [← ENNReal.ofReal_coe_nnreal] at hlo
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (div_nonneg hM hp.le)).1 hlo
  have hd : 0 < (d:ℝ) := (div_nonneg hM hp.le).trans_lt hd'
  obtain ⟨z,hz,hzdist⟩ := h.truncation_transport_step (a := a) hd (fun c hc ↦
    truncation_nonempty_of_lt_badFiberDistance hr ha (lt_of_le_of_lt (by
      rw [edist_nndist,ENNReal.coe_le_coe]; exact (show dist c a ≤ d from hc)) hhi)) hv
  have hcomp : dist v w ≤ dist v z := hmin ▸ infDist_le_dist_of_mem hz
  have hd0 := (div_lt_iff₀ hp).1 hd'
  have hden : 0 < (d:ℝ) + dist a b := by positivity
  have hfrac := (le_div_iff₀ hden).1 (hcomp.trans hzdist)
  dsimp only [M] at hd0
  nlinarith [mul_nonneg hp.le (dist_nonneg (x := a) (y := b))]

/-- **Theorem 9.33(b).** The initial and separation radii are uniform on
compact subsets of the interior of the domain. The estimate holds for every
source input, including inputs outside the compact set. -/
theorem SvGraphConvex.exists_truncation_transport (h : SvGraphConvex S)
    (hclosed : ∀ a ∈ X, IsClosed (S a)) (hX : IsCompact X) (hi : X ⊆ interior (svDom S)) :
    ∃ R₀ ≥ (0:ℝ), ∃ l ≥ (0:ℝ), ∀ r ≥ R₀+1, ∀ a ∈ X, ∀ b v,
      v ∈ S b ∩ closedBall (0:F) r → ∃ w ∈ S a ∩ closedBall (0:F) r,
        dist v w ≤ l*r*dist a b := by
  let R₀ := (svZeroRadius S X).toNNReal
  have hfin := h.svZeroRadius_lt_top hX hi
  have heq : (R₀ : ℝ≥0∞) = svZeroRadius S X := ENNReal.coe_toNNReal hfin.ne
  let R := R₀+1
  have hR : svZeroRadius S X < (R : ℝ≥0∞) := by rw [← heq,ENNReal.coe_lt_coe]; exact lt_add_of_pos_right _ zero_lt_one
  have hD := h.svBadFiberDistance_pos hX hi hR
  refine ⟨R₀,R₀.2,2/(svBadFiberDistance S X R).toReal,by positivity,fun r hr a ha b v hv ↦ ?_⟩
  have hr' : 0 ≤ r := add_nonneg R₀.2 zero_le_one |>.trans hr
  exact h.truncation_transport hclosed hD (r := ⟨r,hr'⟩) (ENNReal.coe_le_coe.2 (by exact_mod_cast hr)) ha b hv

end RW
