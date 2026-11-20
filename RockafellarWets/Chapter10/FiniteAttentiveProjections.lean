/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Attentive convergence in a finite separable product
-/

import RockafellarWets.Chapter10.FiniteSeparableSubgradients

open Filter Set Topology

namespace RW

noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
theorem tendsto_separableFin_attentive_coordinate (n : ℕ) (f : Fin n → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 (fun _ : Fin n ↦ E)) (c : Fin n → ℝ) (hx : ∀ i, f i (x i) = c i) :
    ∀ i, Tendsto (fun q : PiLp 2 (fun _ : Fin n ↦ E) ↦ q i)
      (attentiveNhds (separablePi f) x) (attentiveNhds (f i) (x i)) := by
  induction n with
  | zero => exact fun i ↦ Fin.elim0 i
  | succ n ih =>
    let L := l2FinSuccSplit (E := E) n
    let g := separableSum (f 0) (separablePi (fun i : Fin n ↦ f i.succ))
    have he : separablePi f = g ∘ L := separablePi_finSucc n f
    have hL : Tendsto L (attentiveNhds (separablePi f) x) (attentiveNhds g (L x)) := by
      apply tendsto_attentiveNhds_iff.mpr
      refine ⟨L.continuous.continuousAt.mono_left inf_le_left,?_⟩
      have h := (tendsto_attentiveNhds_iff.mp (tendsto_id (x := attentiveNhds (separablePi f) x))).2
      simpa only [Function.comp_id,he] using h
    have ht := separablePi_eq_coe (x := WithLp.toLp 2 (fun i : Fin n ↦ x i.succ))
      (fun i ↦ hx i.succ)
    have hlt := lowerSemicontinuous_separablePi (fun i : Fin n ↦ hf i.succ) (fun i ↦ (hp i.succ).2)
    have hfirst := (tendsto_separable_attentive_fst (hf 0 _) (hlt _) (hx 0) ht).comp hL
    have htail := (tendsto_separable_attentive_snd (hf 0 _) (hlt _) (hx 0) ht).comp hL
    intro i
    exact Fin.cases hfirst (fun j ↦
      (ih (fun i : Fin n ↦ f i.succ) (fun i ↦ hp i.succ) (fun i ↦ hf i.succ)
        (WithLp.toLp 2 (fun i ↦ x i.succ)) (fun i ↦ c i.succ) (fun i ↦ hx i.succ) j).comp htail) i

/-- Attentive convergence of a finite separable sum gives attentive
convergence in every coordinate. -/
theorem tendsto_separablePi_attentive_coordinate (f : ι → E → EReal)
    (hp : ∀ i, IsProper (f i)) (hf : ∀ i, LowerSemicontinuous (f i))
    (x : PiLp 2 (fun _ : ι ↦ E)) (c : ι → ℝ) (hx : ∀ i, f i (x i) = c i) (i : ι) :
    Tendsto (fun q : PiLp 2 (fun _ : ι ↦ E) ↦ q i)
      (attentiveNhds (separablePi f) x) (attentiveNhds (f i) (x i)) := by
  let e := Fintype.equivFin ι
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℝ E e
  let g := fun j : Fin (Fintype.card ι) ↦ f (e.symm j)
  have he : separablePi f = separablePi g ∘ L := separablePi_reindex e f
  have hL : Tendsto L (attentiveNhds (separablePi f) x) (attentiveNhds (separablePi g) (L x)) := by
    apply tendsto_attentiveNhds_iff.mpr
    refine ⟨L.continuous.continuousAt.mono_left inf_le_left,?_⟩
    have h := (tendsto_attentiveNhds_iff.mp (tendsto_id (x := attentiveNhds (separablePi f) x))).2
    simpa only [Function.comp_id,he] using h
  have h := (tendsto_separableFin_attentive_coordinate _ g
    (fun j ↦ hp (e.symm j)) (fun j ↦ hf (e.symm j)) (L x) (fun j ↦ c (e.symm j))
    (fun j ↦ hx (e.symm j)) (e i)).comp hL
  simpa [L,g,Function.comp_def] using h

end

end RW
