/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite separable sums on Euclidean products
-/

import RockafellarWets.Chapter10.SeparableSubgradients
import RockafellarWets.Chapter10.CoordinateSubgradients
import RockafellarWets.Chapter6.FiniteProductCones

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite sum with one function for each independent coordinate. -/
def separablePi (f : ι → E → EReal) (x : PiLp 2 (fun _ : ι ↦ E)) : EReal := ∑ i, f i (x i)

theorem separablePi_eq_coe {f : ι → E → EReal} {x : PiLp 2 (fun _ : ι ↦ E)} {c : ι → ℝ}
    (hx : ∀ i, f i (x i) = c i) : separablePi f x = ((∑ i, c i : ℝ) : EReal) := by
  classical
  simp only [separablePi,hx]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi,ih,EReal.coe_add]

theorem bot_lt_separablePi {f : ι → E → EReal} (hf : ∀ i, ∀ x, ⊥ < f i x)
    (x : PiLp 2 (fun _ : ι ↦ E)) : ⊥ < separablePi f x := by
  classical
  unfold separablePi
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact EReal.bot_lt_add_iff.mpr ⟨hf i _,ih⟩

theorem isProper_separablePi {f : ι → E → EReal} (hf : ∀ i, IsProper (f i)) :
    IsProper (separablePi f) := by
  choose xs hxs using fun i ↦ (hf i).1
  have hfin (i : ι) : f i (xs i) = ((f i (xs i)).toReal : EReal) :=
    (EReal.coe_toReal (hxs i).ne ((hf i).2 (xs i)).ne' |>.symm)
  refine ⟨⟨WithLp.toLp 2 xs,?_⟩,bot_lt_separablePi (fun i ↦ (hf i).2)⟩
  rw [separablePi_eq_coe hfin]
  exact EReal.coe_lt_top _

theorem lowerSemicontinuous_separablePi {f : ι → E → EReal}
    (hf : ∀ i, LowerSemicontinuous (f i)) (hb : ∀ i, ∀ x, ⊥ < f i x) :
    LowerSemicontinuous (separablePi f) := by
  classical
  unfold separablePi
  have hnb (s : Finset ι) (x : PiLp 2 (fun _ : ι ↦ E)) : ⊥ < ∑ i ∈ s, f i (x i) := by
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

/-- Splitting off the first coordinate preserves the Euclidean norm. -/
def l2FinSuccSplit (n : ℕ) :
    PiLp 2 (fun _ : Fin (n+1) ↦ E) ≃ₗᵢ[ℝ] WithLp 2 (E × PiLp 2 (fun _ : Fin n ↦ E)) :=
  LinearEquiv.isometryOfInner
    { toFun := fun v ↦ WithLp.toLp 2 (v 0,WithLp.toLp 2 (fun i ↦ v i.succ))
      invFun := fun q ↦ WithLp.toLp 2 (Fin.cons q.fst (fun i ↦ q.snd i))
      left_inv := by intro v; apply WithLp.ofLp_injective; funext i; exact Fin.cases rfl (fun _ ↦ rfl) i
      right_inv := by intro q; rfl
      map_add' := by intro v w; rfl
      map_smul' := by intro r v; rfl }
    (by intro v w; simp [WithLp.prod_inner_apply,l2Pi_inner_apply,Fin.sum_univ_succ])

@[simp] theorem l2FinSuccSplit_apply (n : ℕ) (v : PiLp 2 (fun _ : Fin (n+1) ↦ E)) :
    l2FinSuccSplit n v = WithLp.toLp 2 (v 0,WithLp.toLp 2 (fun i ↦ v i.succ)) := rfl

theorem separablePi_finSucc (n : ℕ) (f : Fin (n+1) → E → EReal) :
    separablePi f = separableSum (f 0) (separablePi (fun i : Fin n ↦ f i.succ)) ∘ l2FinSuccSplit n := by
  funext x
  exact Fin.sum_univ_succ _

section Isometry

variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]

theorem mem_regularSubdifferential_comp_isometry (L : A ≃ₗᵢ[ℝ] B) {g : B → EReal} {x v : A} {a : ℝ}
    (hx : g (L x) = a) : v ∈ regularSubdifferential (g ∘ L) x ↔ L v ∈ regularSubdifferential g (L x) := by
  have he := regularSubdifferential_comp_eq_of_surjective L.toContinuousLinearEquiv.toContinuousLinearMap.contDiff hx
    (by simpa only [ContinuousLinearMap.fderiv] using L.surjective)
  rw [ContinuousLinearMap.fderiv,LinearIsometryEquiv.adjoint_eq_symm] at he
  change regularSubdifferential (g ∘ L) x = L.symm '' regularSubdifferential g (L x) at he
  rw [he]
  exact ⟨fun ⟨y,hy,he⟩ ↦ by simpa only [← he,L.apply_symm_apply] using hy,
    fun h ↦ ⟨L v,h,L.symm_apply_apply v⟩⟩

theorem mem_subdifferential_comp_isometry (L : A ≃ₗᵢ[ℝ] B) {g : B → EReal} {x v : A} {a : ℝ}
    (hx : g (L x) = a) : v ∈ subdifferential (g ∘ L) x ↔ L v ∈ subdifferential g (L x) := by
  have he := subdifferential_comp_eq_of_surjective L.toContinuousLinearEquiv.toContinuousLinearMap.contDiff hx
    (by simpa only [ContinuousLinearMap.fderiv] using L.surjective)
  rw [ContinuousLinearMap.fderiv,LinearIsometryEquiv.adjoint_eq_symm] at he
  change subdifferential (g ∘ L) x = L.symm '' subdifferential g (L x) at he
  rw [he]
  exact ⟨fun ⟨y,hy,he⟩ ↦ by simpa only [← he,L.apply_symm_apply] using hy,
    fun h ↦ ⟨L v,h,L.symm_apply_apply v⟩⟩

theorem mem_horizonSubdifferential_comp_isometry (L : A ≃ₗᵢ[ℝ] B) {g : B → EReal} {x v : A} {a : ℝ}
    (hl : LowerSemicontinuous g) (hx : g (L x) = a) :
    v ∈ horizonSubdifferential (g ∘ L) x ↔ L v ∈ horizonSubdifferential g (L x) := by
  have he := horizonSubdifferential_comp_eq_of_surjective L.toContinuousLinearEquiv.toContinuousLinearMap.contDiff hl hx
    (by simpa only [ContinuousLinearMap.fderiv] using L.surjective)
  rw [ContinuousLinearMap.fderiv,LinearIsometryEquiv.adjoint_eq_symm] at he
  change horizonSubdifferential (g ∘ L) x = L.symm '' horizonSubdifferential g (L x) at he
  rw [he]
  exact ⟨fun ⟨y,hy,he⟩ ↦ by simpa only [← he,L.apply_symm_apply] using hy,
    fun h ↦ ⟨L v,h,L.symm_apply_apply v⟩⟩

end Isometry

set_option maxHeartbeats 1000000 in
/-- The regular subgradient product formula for any finite number of factors. -/
theorem mem_regularSubdifferential_separableFin_iff (n : ℕ) (f : Fin n → E → EReal)
    (x v : PiLp 2 (fun _ : Fin n ↦ E)) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) :
    v ∈ regularSubdifferential (separablePi f) x ↔ ∀ i, v i ∈ regularSubdifferential (f i) (x i) := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _
      refine ⟨0,by simp [separablePi],fun ε hε ↦ Eventually.of_forall fun q ↦ ?_⟩
      have hq : q = x := Subsingleton.elim _ _
      simp [separablePi,hq]
  | succ n ih =>
    have ht : separablePi (fun i : Fin n ↦ f i.succ) (WithLp.toLp 2 (fun i ↦ x i.succ)) =
        ((∑ i : Fin n, c i.succ : ℝ) : EReal) := separablePi_eq_coe (fun i ↦ hx i.succ)
    have hxval := separablePi_eq_coe hx
    rw [separablePi_finSucc] at hxval ⊢
    rw [mem_regularSubdifferential_comp_isometry (l2FinSuccSplit (E := E) n)
      (g := separableSum (f 0) (separablePi (fun i : Fin n ↦ f i.succ))) (x := x) (v := v) (a := ∑ i, c i) hxval]
    simp only [l2FinSuccSplit_apply]
    rw [mem_regularSubdifferential_separableSum_iff (x := x 0)
      (y := WithLp.toLp 2 (fun i : Fin n ↦ x i.succ)) (hx 0) ht
      (WithLp.toLp 2 (v 0,WithLp.toLp 2 (fun i : Fin n ↦ v i.succ)))]
    change (v 0 ∈ regularSubdifferential (f 0) (x 0) ∧
      WithLp.toLp 2 (fun i ↦ v i.succ) ∈ regularSubdifferential (separablePi (fun i : Fin n ↦ f i.succ))
        (WithLp.toLp 2 (fun i ↦ x i.succ))) ↔ _
    rw [ih (fun i : Fin n ↦ f i.succ) (WithLp.toLp 2 (fun i ↦ x i.succ))
      (WithLp.toLp 2 (fun i ↦ v i.succ)) (fun i ↦ c i.succ) (fun i ↦ hx i.succ)]
    exact ⟨fun h i ↦ Fin.cases h.1 h.2 i,fun h ↦ ⟨h 0,fun i ↦ h i.succ⟩⟩

/-- The limiting subgradient product formula, with proper lsc factors. -/
theorem mem_subdifferential_separableFin_iff (n : ℕ) (f : Fin n → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x v : PiLp 2 (fun _ : Fin n ↦ E)) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) :
    v ∈ subdifferential (separablePi f) x ↔ ∀ i, v i ∈ subdifferential (f i) (x i) := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _
      exact regularSubdifferential_subset_subdifferential _ _
        ((mem_regularSubdifferential_separableFin_iff 0 f x v c hx).mpr (fun i ↦ Fin.elim0 i))
  | succ n ih =>
    have ht : separablePi (fun i : Fin n ↦ f i.succ) (WithLp.toLp 2 (fun i ↦ x i.succ)) =
        ((∑ i : Fin n, c i.succ : ℝ) : EReal) := separablePi_eq_coe (fun i ↦ hx i.succ)
    have hlt := lowerSemicontinuous_separablePi (fun i : Fin n ↦ hf i.succ)
      (fun i ↦ (hp i.succ).2)
    have hxval := separablePi_eq_coe hx
    rw [separablePi_finSucc] at hxval ⊢
    rw [mem_subdifferential_comp_isometry (l2FinSuccSplit (E := E) n)
      (g := separableSum (f 0) (separablePi (fun i : Fin n ↦ f i.succ))) (x := x) (v := v) (a := ∑ i, c i) hxval]
    simp only [l2FinSuccSplit_apply]
    rw [mem_subdifferential_separableSum_iff (hf 0 _) (hlt _) (hx 0) ht]
    change (v 0 ∈ subdifferential (f 0) (x 0) ∧
      WithLp.toLp 2 (fun i ↦ v i.succ) ∈ subdifferential (separablePi (fun i : Fin n ↦ f i.succ))
        (WithLp.toLp 2 (fun i ↦ x i.succ))) ↔ _
    rw [ih (fun i : Fin n ↦ f i.succ) (fun i ↦ hp i.succ) (fun i ↦ hf i.succ)
      (WithLp.toLp 2 (fun i ↦ x i.succ)) (WithLp.toLp 2 (fun i ↦ v i.succ))
      (fun i ↦ c i.succ) (fun i ↦ hx i.succ)]
    exact ⟨fun h i ↦ Fin.cases h.1 h.2 i,fun h ↦ ⟨h 0,fun i ↦ h i.succ⟩⟩

theorem horizonSubdifferential_separableFin_subset (n : ℕ) (f : Fin n → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 (fun _ : Fin n ↦ E)) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) :
    horizonSubdifferential (separablePi f) x ⊆ {v | ∀ i, v i ∈ horizonSubdifferential (f i) (x i)} := by
  induction n with
  | zero => intro v hv i; exact Fin.elim0 i
  | succ n ih =>
    have ht : separablePi (fun i : Fin n ↦ f i.succ) (WithLp.toLp 2 (fun i ↦ x i.succ)) =
        ((∑ i : Fin n, c i.succ : ℝ) : EReal) := separablePi_eq_coe (fun i ↦ hx i.succ)
    have hlt := lowerSemicontinuous_separablePi (fun i : Fin n ↦ hf i.succ)
      (fun i ↦ (hp i.succ).2)
    have hls : LowerSemicontinuous (separableSum (f 0) (separablePi (fun i : Fin n ↦ f i.succ))) := by
      apply LowerSemicontinuous.add' ((hf 0).comp (WithLp.fstL 2 ℝ _ _).continuous)
        (hlt.comp (WithLp.sndL 2 ℝ _ _).continuous)
      intro q
      exact EReal.continuousAt_add (.inr (bot_lt_separablePi (fun i : Fin n ↦ (hp i.succ).2) q.snd).ne')
        (.inl ((hp 0).2 q.fst).ne')
    have hxval := separablePi_eq_coe hx
    rw [separablePi_finSucc] at hxval
    intro v hv
    rw [separablePi_finSucc,mem_horizonSubdifferential_comp_isometry (l2FinSuccSplit (E := E) n)
      (g := separableSum (f 0) (separablePi (fun i : Fin n ↦ f i.succ))) (x := x) (v := v) (a := ∑ i, c i) hls hxval] at hv
    simp only [l2FinSuccSplit_apply] at hv
    have hparts := horizonSubdifferential_separableSum_subset (hf 0 _) (hlt _) (hx 0) ht hv
    have htail := ih (fun i : Fin n ↦ f i.succ) (fun i ↦ hp i.succ) (fun i ↦ hf i.succ)
      (WithLp.toLp 2 (fun i ↦ x i.succ)) (fun i ↦ c i.succ) (fun i ↦ hx i.succ) hparts.2
    exact fun i ↦ Fin.cases hparts.1 htail i

theorem separablePi_reindex {κ : Type*} [Fintype κ] (e : ι ≃ κ) (f : ι → E → EReal) :
    separablePi f = separablePi (fun j : κ ↦ f (e.symm j)) ∘
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ E e := by
  funext x
  apply Fintype.sum_equiv e
  intro i
  simp [LinearIsometryEquiv.piLpCongrLeft_apply]

theorem mem_regularSubdifferential_separablePi_iff (f : ι → E → EReal)
    (x v : PiLp 2 (fun _ : ι ↦ E)) (c : ι → ℝ) (hx : ∀ i, f i (x i) = c i) :
    v ∈ regularSubdifferential (separablePi f) x ↔ ∀ i, v i ∈ regularSubdifferential (f i) (x i) := by
  let e := Fintype.equivFin ι
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ E e
  let g := fun j : Fin (Fintype.card ι) ↦ f (e.symm j)
  have he : separablePi f = separablePi g ∘ L := separablePi_reindex e f
  have hxval : separablePi g (L x) = ((∑ i, c i : ℝ) : EReal) := by
    have h := separablePi_eq_coe hx
    rw [he] at h
    exact h
  rw [he,mem_regularSubdifferential_comp_isometry L (g := separablePi g) (x := x) (v := v) (a := ∑ i, c i) hxval]
  rw [mem_regularSubdifferential_separableFin_iff _ g (L x) (L v) (fun j ↦ c (e.symm j))
    (fun j ↦ hx (e.symm j))]
  exact ⟨fun h i ↦ by simpa [L,g] using h (e i),fun h j ↦ h (e.symm j)⟩

theorem mem_subdifferential_separablePi_iff (f : ι → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x v : PiLp 2 (fun _ : ι ↦ E)) (c : ι → ℝ) (hx : ∀ i, f i (x i) = c i) :
    v ∈ subdifferential (separablePi f) x ↔ ∀ i, v i ∈ subdifferential (f i) (x i) := by
  let e := Fintype.equivFin ι
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ E e
  let g := fun j : Fin (Fintype.card ι) ↦ f (e.symm j)
  have he : separablePi f = separablePi g ∘ L := separablePi_reindex e f
  have hxval : separablePi g (L x) = ((∑ i, c i : ℝ) : EReal) := by
    have h := separablePi_eq_coe hx
    rw [he] at h
    exact h
  rw [he,mem_subdifferential_comp_isometry L (g := separablePi g) (x := x) (v := v) (a := ∑ i, c i) hxval]
  rw [mem_subdifferential_separableFin_iff _ g (fun j ↦ hp (e.symm j)) (fun j ↦ hf (e.symm j))
    (L x) (L v) (fun j ↦ c (e.symm j)) (fun j ↦ hx (e.symm j))]
  exact ⟨fun h i ↦ by simpa [L,g] using h (e i),fun h j ↦ h (e.symm j)⟩

theorem horizonSubdifferential_separablePi_subset (f : ι → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 (fun _ : ι ↦ E)) (c : ι → ℝ) (hx : ∀ i, f i (x i) = c i) :
    horizonSubdifferential (separablePi f) x ⊆ {v | ∀ i, v i ∈ horizonSubdifferential (f i) (x i)} := by
  let e := Fintype.equivFin ι
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ E e
  let g := fun j : Fin (Fintype.card ι) ↦ f (e.symm j)
  have he : separablePi f = separablePi g ∘ L := separablePi_reindex e f
  have hxval : separablePi g (L x) = ((∑ i, c i : ℝ) : EReal) := by
    have h := separablePi_eq_coe hx
    rw [he] at h
    exact h
  intro v hv i
  rw [he,mem_horizonSubdifferential_comp_isometry L
    (lowerSemicontinuous_separablePi (fun j ↦ hf (e.symm j)) (fun j ↦ (hp (e.symm j)).2)) hxval] at hv
  have hh := horizonSubdifferential_separableFin_subset _ g (fun j ↦ hp (e.symm j))
    (fun j ↦ hf (e.symm j)) (L x) (fun j ↦ c (e.symm j)) (fun j ↦ hx (e.symm j)) hv (e i)
  simpa [L,g] using hh

end

end RW
