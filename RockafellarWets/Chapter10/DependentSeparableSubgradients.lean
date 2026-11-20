/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Separable functions with factors of different dimensions
-/

import RockafellarWets.Chapter10.FiniteSeparableSubgradients

open Filter Set Topology
open scoped InnerProductSpace

namespace RW
noncomputable section
section Generic
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]

/-- A finite sum with one function for each independent coordinate. -/
def dependentSeparablePi (f : ∀ i, E i → EReal) (x : PiLp 2 E) : EReal := ∑ i, f i (x i)

theorem dependentSeparablePi_eq_coe {f : ∀ i, E i → EReal} {x : PiLp 2 E} {c : ι → ℝ}
    (hx : ∀ i, f i (x i) = c i) : dependentSeparablePi f x = ((∑ i, c i : ℝ) : EReal) := by
  classical
  simp only [dependentSeparablePi,hx]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,ih,EReal.coe_add]

theorem bot_lt_dependentSeparablePi {f : ∀ i, E i → EReal} (hf : ∀ i, ∀ x, ⊥ < f i x)
    (x : PiLp 2 E) : ⊥ < dependentSeparablePi f x := by
  classical
  unfold dependentSeparablePi
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact EReal.bot_lt_add_iff.mpr ⟨hf i _,ih⟩

theorem isProper_dependentSeparablePi {f : ∀ i, E i → EReal} (hf : ∀ i, IsProper (f i)) :
    IsProper (dependentSeparablePi f) := by
  choose xs hxs using fun i ↦ (hf i).1
  have hfin (i : ι) : f i (xs i) = ((f i (xs i)).toReal : EReal) :=
    (EReal.coe_toReal (hxs i).ne ((hf i).2 (xs i)).ne' |>.symm)
  refine ⟨⟨WithLp.toLp 2 xs,?_⟩,bot_lt_dependentSeparablePi (fun i ↦ (hf i).2)⟩
  rw [dependentSeparablePi_eq_coe hfin]
  exact EReal.coe_lt_top _

theorem lowerSemicontinuous_dependentSeparablePi {f : ∀ i, E i → EReal}
    (hf : ∀ i, LowerSemicontinuous (f i)) (hb : ∀ i, ∀ x, ⊥ < f i x) :
    LowerSemicontinuous (dependentSeparablePi f) := by
  classical
  unfold dependentSeparablePi
  have hnb (s : Finset ι) (x : PiLp 2 E) : ⊥ < ∑ i ∈ s, f i (x i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simpa only [Finset.sum_insert hi] using EReal.bot_lt_add_iff.mpr ⟨hb i _,ih⟩
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => exact continuous_const.lowerSemicontinuous
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    apply LowerSemicontinuous.add' ((hf i).comp (PiLp.continuous_apply 2 _ i)) ih
    intro x
    exact EReal.continuousAt_add (.inr (hnb s x).ne') (.inl (hb i (x i)).ne')

end Generic

/-- Splitting off the first coordinate preserves the Euclidean norm. -/
def l2DependentFinSuccSplit (n : ℕ) (E : Fin (n+1) → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] :
    PiLp 2 E ≃ₗᵢ[ℝ] WithLp 2 (E 0 × PiLp 2 (fun i : Fin n ↦ E i.succ)) :=
  LinearEquiv.isometryOfInner
    { toFun := fun v ↦ WithLp.toLp 2 (v 0,WithLp.toLp 2 (fun i : Fin n ↦ v i.succ))
      invFun := fun q ↦ WithLp.toLp 2 (Fin.cons q.fst (fun i ↦ q.snd i))
      left_inv := by intro v; apply WithLp.ofLp_injective; funext i; exact Fin.cases rfl (fun _ ↦ rfl) i
      right_inv := by intro q; rfl
      map_add' := by intro v w; rfl
      map_smul' := by intro r v; rfl }
    (by intro v w; simp [WithLp.prod_inner_apply,l2Pi_inner_apply,Fin.sum_univ_succ])

@[simp] theorem l2DependentFinSuccSplit_apply (n : ℕ) (E : Fin (n+1) → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] (v : PiLp 2 E) :
    l2DependentFinSuccSplit n E v = WithLp.toLp 2 (v 0,WithLp.toLp 2 (fun i : Fin n ↦ v i.succ)) := rfl

theorem dependentSeparablePi_finSucc (n : ℕ) (E : Fin (n+1) → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)] (f : ∀ i, E i → EReal) :
    dependentSeparablePi f = separableSum (f 0) (dependentSeparablePi (fun i : Fin n ↦ f i.succ)) ∘ l2DependentFinSuccSplit n E := by
  funext x
  exact Fin.sum_univ_succ _

set_option maxHeartbeats 1000000 in
/-- The regular subgradient product formula for any finite number of factors. -/
theorem mem_regularSubdifferential_dependentSeparableFin_iff (n : ℕ) (E : Fin n → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)] (f : ∀ i, E i → EReal)
    (x v : PiLp 2 E) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) :
    v ∈ regularSubdifferential (dependentSeparablePi f) x ↔ ∀ i, v i ∈ regularSubdifferential (f i) (x i) := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _
      refine ⟨0,by simp [dependentSeparablePi],fun ε hε ↦ Eventually.of_forall fun q ↦ ?_⟩
      have hq : q = x := Subsingleton.elim _ _
      simp [dependentSeparablePi,hq]
  | succ n ih =>
    have ht : dependentSeparablePi (fun i : Fin n ↦ f i.succ) (WithLp.toLp 2 (fun i : Fin n ↦ x i.succ)) =
        ((∑ i : Fin n, c i.succ : ℝ) : EReal) := dependentSeparablePi_eq_coe (fun i ↦ hx i.succ)
    have hxval := dependentSeparablePi_eq_coe hx
    rw [dependentSeparablePi_finSucc] at hxval ⊢
    rw [mem_regularSubdifferential_comp_isometry (l2DependentFinSuccSplit n E)
      (g := separableSum (f 0) (dependentSeparablePi (fun i : Fin n ↦ f i.succ))) (x := x) (v := v) (a := ∑ i, c i) hxval]
    simp only [l2DependentFinSuccSplit_apply]
    rw [mem_regularSubdifferential_separableSum_iff (x := x 0)
      (y := WithLp.toLp 2 (fun i : Fin n ↦ x i.succ)) (hx 0) ht
      (WithLp.toLp 2 (v 0,WithLp.toLp 2 (fun i : Fin n ↦ v i.succ)))]
    change (v 0 ∈ regularSubdifferential (f 0) (x 0) ∧
      WithLp.toLp 2 (fun i : Fin n ↦ v i.succ) ∈ regularSubdifferential (dependentSeparablePi (fun i : Fin n ↦ f i.succ))
        (WithLp.toLp 2 (fun i : Fin n ↦ x i.succ))) ↔ _
    rw [ih (fun i : Fin n ↦ E i.succ) (fun i : Fin n ↦ f i.succ) (WithLp.toLp 2 (fun i : Fin n ↦ x i.succ))
      (WithLp.toLp 2 (fun i : Fin n ↦ v i.succ)) (fun i ↦ c i.succ) (fun i ↦ hx i.succ)]
    exact ⟨fun h i ↦ Fin.cases h.1 h.2 i,fun h ↦ ⟨h 0,fun i ↦ h i.succ⟩⟩

/-- The limiting subgradient product formula, with proper lsc factors. -/
theorem mem_subdifferential_dependentSeparableFin_iff (n : ℕ) (E : Fin n → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)] (f : ∀ i, E i → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x v : PiLp 2 E) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) :
    v ∈ subdifferential (dependentSeparablePi f) x ↔ ∀ i, v i ∈ subdifferential (f i) (x i) := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _
      exact regularSubdifferential_subset_subdifferential _ _
        ((mem_regularSubdifferential_dependentSeparableFin_iff 0 E f x v c hx).mpr (fun i ↦ Fin.elim0 i))
  | succ n ih =>
    have ht : dependentSeparablePi (fun i : Fin n ↦ f i.succ) (WithLp.toLp 2 (fun i : Fin n ↦ x i.succ)) =
        ((∑ i : Fin n, c i.succ : ℝ) : EReal) := dependentSeparablePi_eq_coe (fun i ↦ hx i.succ)
    have hlt := lowerSemicontinuous_dependentSeparablePi (fun i : Fin n ↦ hf i.succ)
      (fun i ↦ (hp i.succ).2)
    have hxval := dependentSeparablePi_eq_coe hx
    rw [dependentSeparablePi_finSucc] at hxval ⊢
    rw [mem_subdifferential_comp_isometry (l2DependentFinSuccSplit n E)
      (g := separableSum (f 0) (dependentSeparablePi (fun i : Fin n ↦ f i.succ))) (x := x) (v := v) (a := ∑ i, c i) hxval]
    simp only [l2DependentFinSuccSplit_apply]
    rw [mem_subdifferential_separableSum_iff (hf 0 _) (hlt _) (hx 0) ht]
    change (v 0 ∈ subdifferential (f 0) (x 0) ∧
      WithLp.toLp 2 (fun i : Fin n ↦ v i.succ) ∈ subdifferential (dependentSeparablePi (fun i : Fin n ↦ f i.succ))
        (WithLp.toLp 2 (fun i : Fin n ↦ x i.succ))) ↔ _
    rw [ih (fun i : Fin n ↦ E i.succ) (fun i : Fin n ↦ f i.succ) (fun i ↦ hp i.succ) (fun i ↦ hf i.succ)
      (WithLp.toLp 2 (fun i : Fin n ↦ x i.succ)) (WithLp.toLp 2 (fun i : Fin n ↦ v i.succ))
      (fun i ↦ c i.succ) (fun i ↦ hx i.succ)]
    exact ⟨fun h i ↦ Fin.cases h.1 h.2 i,fun h ↦ ⟨h 0,fun i ↦ h i.succ⟩⟩

theorem horizonSubdifferential_dependentSeparableFin_subset (n : ℕ) (E : Fin n → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)] (f : ∀ i, E i → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 E) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) :
    horizonSubdifferential (dependentSeparablePi f) x ⊆ {v | ∀ i, v i ∈ horizonSubdifferential (f i) (x i)} := by
  induction n with
  | zero => intro v hv i; exact Fin.elim0 i
  | succ n ih =>
    have ht : dependentSeparablePi (fun i : Fin n ↦ f i.succ) (WithLp.toLp 2 (fun i : Fin n ↦ x i.succ)) =
        ((∑ i : Fin n, c i.succ : ℝ) : EReal) := dependentSeparablePi_eq_coe (fun i ↦ hx i.succ)
    have hlt := lowerSemicontinuous_dependentSeparablePi (fun i : Fin n ↦ hf i.succ)
      (fun i ↦ (hp i.succ).2)
    have hls : LowerSemicontinuous (separableSum (f 0) (dependentSeparablePi (fun i : Fin n ↦ f i.succ))) := by
      apply LowerSemicontinuous.add' ((hf 0).comp (WithLp.fstL 2 ℝ _ _).continuous)
        (hlt.comp (WithLp.sndL 2 ℝ _ _).continuous)
      intro q
      exact EReal.continuousAt_add (.inr (bot_lt_dependentSeparablePi (fun i : Fin n ↦ (hp i.succ).2) q.snd).ne')
        (.inl ((hp 0).2 q.fst).ne')
    have hxval := dependentSeparablePi_eq_coe hx
    rw [dependentSeparablePi_finSucc] at hxval
    intro v hv
    rw [dependentSeparablePi_finSucc,mem_horizonSubdifferential_comp_isometry (l2DependentFinSuccSplit n E)
      (g := separableSum (f 0) (dependentSeparablePi (fun i : Fin n ↦ f i.succ))) (x := x) (v := v) (a := ∑ i, c i) hls hxval] at hv
    simp only [l2DependentFinSuccSplit_apply] at hv
    have hparts := horizonSubdifferential_separableSum_subset (hf 0 _) (hlt _) (hx 0) ht hv
    have htail := ih (fun i : Fin n ↦ E i.succ) (fun i : Fin n ↦ f i.succ) (fun i ↦ hp i.succ) (fun i ↦ hf i.succ)
      (WithLp.toLp 2 (fun i : Fin n ↦ x i.succ)) (fun i ↦ c i.succ) (fun i ↦ hx i.succ) hparts.2
    exact fun i ↦ Fin.cases hparts.1 htail i


end
end RW
