/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subderivatives and regularity of finite separable sums
-/

import RockafellarWets.Chapter10.FiniteSeparableSubgradients
import RockafellarWets.Chapter10.SeparableRegularity
import RockafellarWets.Chapter10.CoordinateSubderivatives
import RockafellarWets.Chapter8.SmoothSubderivativeRegularity

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem subderivatives_zero_function {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] [FiniteDimensional ℝ A] (x w : A) :
    subderivative (fun _ : A ↦ (0:EReal)) x w = 0 ∧
    regularSubderivative (fun _ : A ↦ (0:EReal)) x w = 0 := by
  have h := smooth_subderivatives_eq_inner_gradient (k := fun _ : A ↦ (0:ℝ))
    (x := x) (U := univ) (Filter.univ_mem) contDiff_const.contDiffOn w
  simpa using h

set_option maxHeartbeats 1000000 in
/-- The finite lower-subderivative inequality. -/
theorem subderivative_separableFin_ge (n : ℕ) (f : Fin n → E → EReal)
    (x w : PiLp 2 (fun _ : Fin n ↦ E)) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) :
    (∑ i, subderivative (f i) (x i) (w i)) ≤ subderivative (separablePi f) x w := by
  induction n with
  | zero =>
    have he : separablePi f = fun _ ↦ (0:EReal) := by funext z; simp [separablePi]
    simp only [he,Finset.univ_eq_empty,Finset.sum_empty,(subderivatives_zero_function x w).1,le_refl]
  | succ n ih =>
    let L := l2FinSuccSplit (E := E) n
    let g := separableSum (f 0) (separablePi (fun i : Fin n ↦ f i.succ))
    have ht := separablePi_eq_coe (x := WithLp.toLp 2 (fun i : Fin n ↦ x i.succ))
      (fun i ↦ hx i.succ)
    have hval : g (L x) = ((∑ i, c i : ℝ) : EReal) := by
      have h := separablePi_eq_coe hx
      rw [separablePi_finSucc] at h
      exact h
    have hd := subderivative_comp_eq_of_surjective L.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
      hval (by simpa only [ContinuousLinearMap.fderiv] using L.surjective) w
    rw [ContinuousLinearMap.fderiv] at hd
    change subderivative (g ∘ L) x w = subderivative g (L x) (L w) at hd
    have he : separablePi f = g ∘ L := separablePi_finSucc n f
    rw [he,hd,Fin.sum_univ_succ]
    exact (add_le_add le_rfl (ih (fun i : Fin n ↦ f i.succ)
      (WithLp.toLp 2 (fun i ↦ x i.succ)) (WithLp.toLp 2 (fun i ↦ w i.succ))
      (fun i ↦ c i.succ) (fun i ↦ hx i.succ))).trans
        (subderivative_separableSum_ge (hx 0) ht (L w))

theorem subderivative_separableFin_zero (n : ℕ) (f : Fin n → E → EReal)
    (x : PiLp 2 (fun _ : Fin n ↦ E)) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i)
    (h0 : ∀ i, subderivative (f i) (x i) 0 = 0) :
    subderivative (separablePi f) x 0 = 0 := by
  have hlow := subderivative_separableFin_ge n f x 0 c hx
  simp only [PiLp.zero_apply,h0,Finset.sum_const_zero] at hlow
  exact (lowerSemicontinuous_positivelyHomogeneous_subderivative (separablePi_eq_coe hx)).2.zero_eq_zero_or_bot.resolve_right
    (fun hb ↦ EReal.zero_ne_bot (le_bot_iff.mp (hb ▸ hlow)))

set_option maxHeartbeats 1000000 in
/-- The finite regular-subderivative inequality under the zero-direction
hypotheses in Proposition 10.5. -/
theorem regularSubderivative_separableFin_le (n : ℕ) (f : Fin n → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x w : PiLp 2 (fun _ : Fin n ↦ E)) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i)
    (h0 : ∀ i, subderivative (f i) (x i) 0 = 0) :
    regularSubderivative (separablePi f) x w ≤ (∑ i, regularSubderivative (f i) (x i) (w i)) := by
  induction n with
  | zero =>
    have he : separablePi f = fun _ ↦ (0:EReal) := by funext z; simp [separablePi]
    simp only [he,Finset.univ_eq_empty,Finset.sum_empty,(subderivatives_zero_function x w).2,le_refl]
  | succ n ih =>
    let L := l2FinSuccSplit (E := E) n
    let g := separableSum (f 0) (separablePi (fun i : Fin n ↦ f i.succ))
    have ht := separablePi_eq_coe (x := WithLp.toLp 2 (fun i : Fin n ↦ x i.succ))
      (fun i ↦ hx i.succ)
    have hlt := lowerSemicontinuous_separablePi (fun i : Fin n ↦ hf i.succ) (fun i ↦ (hp i.succ).2)
    have hlg := lowerSemicontinuous_separableSum (hf 0) hlt (hp 0)
      (isProper_separablePi (fun i : Fin n ↦ hp i.succ))
    have hval : g (L x) = ((∑ i, c i : ℝ) : EReal) := by
      have h := separablePi_eq_coe hx
      rw [separablePi_finSucc] at h
      exact h
    have hd := regularSubderivative_comp_eq_of_surjective L.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
      hlg hval (by simpa only [ContinuousLinearMap.fderiv] using L.surjective) w
    rw [ContinuousLinearMap.fderiv] at hd
    change regularSubderivative (g ∘ L) x w = regularSubderivative g (L x) (L w) at hd
    have he : separablePi f = g ∘ L := separablePi_finSucc n f
    rw [he,hd,Fin.sum_univ_succ]
    exact (regularSubderivative_separableSum_le (hf 0) hlt (hx 0) ht (h0 0)
      (subderivative_separableFin_zero n (fun i : Fin n ↦ f i.succ)
        (WithLp.toLp 2 (fun i ↦ x i.succ)) (fun i ↦ c i.succ) (fun i ↦ hx i.succ) (fun i ↦ h0 i.succ))
      (L w)).trans (add_le_add le_rfl (ih (fun i : Fin n ↦ f i.succ)
        (fun i ↦ hp i.succ) (fun i ↦ hf i.succ)
        (WithLp.toLp 2 (fun i ↦ x i.succ)) (WithLp.toLp 2 (fun i ↦ w i.succ))
        (fun i ↦ c i.succ) (fun i ↦ hx i.succ) (fun i ↦ h0 i.succ)))

/-- **Proposition 10.5**, the lower bound for an arbitrary finite family. -/
theorem subderivative_separablePi_ge (f : ι → E → EReal)
    (x w : PiLp 2 (fun _ : ι ↦ E)) (c : ι → ℝ) (hx : ∀ i, f i (x i) = c i) :
    (∑ i, subderivative (f i) (x i) (w i)) ≤ subderivative (separablePi f) x w := by
  let e := Fintype.equivFin ι
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ E e
  let g := fun j : Fin (Fintype.card ι) ↦ f (e.symm j)
  have he : separablePi f = separablePi g ∘ L := separablePi_reindex e f
  have hxval : separablePi g (L x) = ((∑ i, c i : ℝ):EReal) := by
    have h := separablePi_eq_coe hx
    rw [he] at h
    exact h
  have hd := subderivative_comp_eq_of_surjective L.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
    hxval (by simpa only [ContinuousLinearMap.fderiv] using L.surjective) w
  rw [ContinuousLinearMap.fderiv] at hd
  change subderivative (separablePi g ∘ L) x w = subderivative (separablePi g) (L x) (L w) at hd
  have hsum : (∑ j, subderivative (g j) (L x j) (L w j)) =
      ∑ i, subderivative (f i) (x i) (w i) := by
    symm
    apply Fintype.sum_equiv e
    intro i
    simp [L,g]
  rw [he,hd,← hsum]
  exact subderivative_separableFin_ge _ g (L x) (L w) (fun j ↦ c (e.symm j)) (fun j ↦ hx (e.symm j))

/-- **Proposition 10.5**, the regular upper bound for an arbitrary finite family. -/
theorem regularSubderivative_separablePi_le (f : ι → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x w : PiLp 2 (fun _ : ι ↦ E)) (c : ι → ℝ) (hx : ∀ i, f i (x i) = c i)
    (h0 : ∀ i, subderivative (f i) (x i) 0 = 0) :
    regularSubderivative (separablePi f) x w ≤ ∑ i, regularSubderivative (f i) (x i) (w i) := by
  let e := Fintype.equivFin ι
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ E e
  let g := fun j : Fin (Fintype.card ι) ↦ f (e.symm j)
  have he : separablePi f = separablePi g ∘ L := separablePi_reindex e f
  have hxval : separablePi g (L x) = ((∑ i, c i : ℝ):EReal) := by
    have h := separablePi_eq_coe hx
    rw [he] at h
    exact h
  have hlg := lowerSemicontinuous_separablePi (fun j ↦ hf (e.symm j)) (fun j ↦ (hp (e.symm j)).2)
  have hd := regularSubderivative_comp_eq_of_surjective L.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
    hlg hxval (by simpa only [ContinuousLinearMap.fderiv] using L.surjective) w
  rw [ContinuousLinearMap.fderiv] at hd
  change regularSubderivative (separablePi g ∘ L) x w = regularSubderivative (separablePi g) (L x) (L w) at hd
  have hsum : (∑ j, regularSubderivative (g j) (L x j) (L w j)) =
      ∑ i, regularSubderivative (f i) (x i) (w i) := by
    symm
    apply Fintype.sum_equiv e
    intro i
    simp [L,g]
  rw [he,hd,← hsum]
  exact regularSubderivative_separableFin_le _ g (fun j ↦ hp (e.symm j)) (fun j ↦ hf (e.symm j))
    (L x) (L w) (fun j ↦ c (e.symm j)) (fun j ↦ hx (e.symm j)) (fun j ↦ h0 (e.symm j))

/-- **Proposition 10.5**, finite separable regularity and exact directional
sums under the stated zero-direction hypotheses. -/
theorem separablePi_regularity (f : ι → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 (fun _ : ι ↦ E)) (hr : ∀ i, IsSubdifferentiallyRegularAt (f i) (x i))
    (h0 : ∀ i, subderivative (f i) (x i) 0 = 0) :
    IsSubdifferentiallyRegularAt (separablePi f) x ∧
      ∀ w, subderivative (separablePi f) x w = ∑ i, subderivative (f i) (x i) (w i) := by
  let c := fun i ↦ (f i (x i)).toReal
  have hx (i : ι) : f i (x i) = (c i:EReal) := (EReal.coe_toReal (hr i).2.1 (hr i).1).symm
  have he (i : ι) := (isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mp (hr i)).2
  have hupper (w : PiLp 2 (fun _ : ι ↦ E)) : regularSubderivative (separablePi f) x w ≤
      ∑ i, subderivative (f i) (x i) (w i) := by
    simpa only [← he] using regularSubderivative_separablePi_le f hp hf x w c hx h0
  have hlower := subderivative_separablePi_ge f x
  have hval := separablePi_eq_coe hx
  refine ⟨isSubdifferentiallyRegularAt_iff_subderivative_eq_regularSubderivative.mpr
    ⟨locallyLscAt_of_lowerSemicontinuous_finite (lowerSemicontinuous_separablePi hf (fun i ↦ (hp i).2)) hval,?_⟩,?_⟩
  · funext w
    exact le_antisymm (subderivative_le_regularSubderivative hval w) ((hupper w).trans (hlower w c hx))
  · intro w
    exact le_antisymm ((subderivative_le_regularSubderivative hval w).trans (hupper w)) (hlower w c hx)

/-- **Proposition 10.5**, equality in the finite horizon product formula
when every summand is regular and has zero lower subderivative at zero. -/
theorem horizonSubdifferential_separablePi_eq_of_regular (f : ι → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 (fun _ : ι ↦ E)) (hr : ∀ i, IsSubdifferentiallyRegularAt (f i) (x i))
    (h0 : ∀ i, subderivative (f i) (x i) 0 = 0) :
    horizonSubdifferential (separablePi f) x = {v | ∀ i, v i ∈ horizonSubdifferential (f i) (x i)} := by
  classical
  let c := fun i ↦ (f i (x i)).toReal
  have hx (i : ι) : f i (x i) = (c i:EReal) := (EReal.coe_toReal (hr i).2.1 (hr i).1).symm
  have hreg := separablePi_regularity f hp hf x hr h0
  apply Subset.antisymm (horizonSubdifferential_separablePi_subset f hp hf x c hx)
  intro v hv
  rw [hreg.1.horizonSubdifferential_eq_polar_domain]
  intro w hw
  have hbot (i : ι) : ⊥ < subderivative (f i) (x i) (w i) :=
    ((hr i).isProper_subderivative (by rw [h0 i]; norm_num)).2 (w i)
  have hb : ⊥ < ∑ i, subderivative (f i) (x i) (w i) := by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => rw [Finset.sum_insert hi]; exact EReal.bot_lt_add_iff.mpr ⟨hbot i,ih⟩
  have ht : (∑ i, subderivative (f i) (x i) (w i)) < ⊤ := (hreg.2 w) ▸ hw
  have hc : (∑ i, subderivative (f i) (x i) (w i)) =
      (((∑ i, subderivative (f i) (x i) (w i)).toReal : ℝ):EReal) :=
    (EReal.coe_toReal ht.ne hb.ne').symm
  have hfinite (i : ι) : subderivative (f i) (x i) (w i) < ⊤ := by
    have he : subderivative (f i) (x i) (w i)+
        (∑ j ∈ Finset.univ.erase i, subderivative (f j) (x j) (w j)) =
        (((∑ j, subderivative (f j) (x j) (w j)).toReal : ℝ):EReal) := by
      rw [Finset.add_sum_erase Finset.univ (fun j ↦ subderivative (f j) (x j) (w j)) (Finset.mem_univ i)]
      exact hc
    obtain ⟨a,b,ha,_⟩ := exists_coe_components_of_add_eq_coe he
    rw [ha]
    exact EReal.coe_lt_top _
  rw [l2Pi_inner_apply]
  apply Finset.sum_nonpos
  intro i _
  have hh := hv i
  rw [(hr i).horizonSubdifferential_eq_polar_domain] at hh
  exact hh (w i) (hfinite i)

end

end RW
