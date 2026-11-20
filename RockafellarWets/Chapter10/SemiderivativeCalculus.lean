/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite semiderivative calculus
-/
import RockafellarWets.Chapter7.Semiderivatives
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Set Filter Topology
open scoped BigOperators

namespace RW
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The finite, vector-valued version of the joint limit in Definition 7.20. -/
def HasDirectionalSemiderivative (f : E → F) (x w : E) (z : F) : Prop :=
  Tendsto (fun p : ℝ × E ↦ p.1⁻¹ • (f (x + p.1 • p.2) - f x))
    (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 z)

theorem hasDirectionalSemiderivative_iff {f : E → ℝ} {x w : E} {z : ℝ} :
    HasDirectionalSemiderivative f x w z ↔
      HasSemiderivative (fun a ↦ (f a : EReal)) x w z := by
  unfold HasDirectionalSemiderivative HasSemiderivative
  dsimp only
  simp only [differenceQuotient, ← EReal.coe_sub, ← EReal.coe_mul, EReal.tendsto_coe, smul_eq_mul]
  exact ⟨fun h ↦ ⟨EReal.coe_ne_bot _,EReal.coe_ne_top _,h⟩,fun h ↦ h.2.2⟩

theorem HasDirectionalSemiderivative.subderivative_eq {f : E → ℝ} {x w : E} {z : ℝ}
    (h : HasDirectionalSemiderivative f x w z) :
    subderivative (fun a ↦ (f a : EReal)) x w = z :=
  (hasDirectionalSemiderivative_iff.mp h).subderivative_eq

/-- **Exercise 10.27(a)**, addition, at a specified direction. -/
theorem HasDirectionalSemiderivative.add {f g : E → F} {x w : E} {u v : F}
    (hf : HasDirectionalSemiderivative f x w u)
    (hg : HasDirectionalSemiderivative g x w v) :
    HasDirectionalSemiderivative (fun a ↦ f a + g a) x w (u + v) := by
  unfold HasDirectionalSemiderivative at *
  convert Filter.Tendsto.add hf hg using 1
  ext p
  simp only [smul_sub,smul_add]
  abel

/-- Arbitrary real coefficients are allowed in 10.27(a). -/
theorem HasDirectionalSemiderivative.const_smul {f : E → F} {x w : E} {u : F}
    (hf : HasDirectionalSemiderivative f x w u) (a : ℝ) :
    HasDirectionalSemiderivative (fun y ↦ a • f y) x w (a • u) := by
  unfold HasDirectionalSemiderivative at *
  convert (tendsto_const_nhds (x := a)).smul hf using 1
  ext p
  simp [← smul_sub,smul_comm p.1⁻¹ a]

theorem HasDirectionalSemiderivative.const (a : F) (x w : E) :
    HasDirectionalSemiderivative (fun _ ↦ a) x w 0 := by
  simpa [HasDirectionalSemiderivative] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ × E ↦ (0 : F)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 0))

/-- The finite sum form of **Exercise 10.27(a)**. -/
theorem HasDirectionalSemiderivative.sum {ι : Type*} (s : Finset ι)
    {f : ι → E → F} {x w : E} {u : ι → F}
    (hf : ∀ i ∈ s, HasDirectionalSemiderivative (f i) x w (u i)) :
    HasDirectionalSemiderivative (fun y ↦ ∑ i ∈ s, f i y) x w (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasDirectionalSemiderivative.const (0 : F) x w
  | @insert a s ha ih =>
    simpa [Finset.sum_insert,ha] using
      (hf a (Finset.mem_insert_self _ _)).add (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

/-- **Exercise 10.27(b)**, including a merely semidifferentiable inner map. -/
theorem HasDirectionalSemiderivative.comp {f : E → F} {g : F → G}
    {x w : E} {u : F} {v : G}
    (hg : HasDirectionalSemiderivative g (f x) u v)
    (hf : HasDirectionalSemiderivative f x w u) :
    HasDirectionalSemiderivative (g ∘ f) x w v := by
  unfold HasDirectionalSemiderivative at *
  have hp := Filter.Tendsto.comp hg (tendsto_fst.prodMk hf)
  apply hp.congr'
  filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p ht
  simp [Function.comp_def,smul_smul,mul_inv_cancel₀ (ne_of_gt ht)]

/-- A classical derivative supplies the inner semiderivative in 10.27(b). -/
theorem _root_.HasFDerivAt.hasDirectionalSemiderivative {f : E → F} {x : E}
    {A : E →L[ℝ] F} (hf : HasFDerivAt f A x) (w : E) :
    HasDirectionalSemiderivative f x w (A w) := by
  apply hf.hasFDerivWithinAt (s := univ) |>.lim
  · have ht : Tendsto (Prod.fst : ℝ × E → ℝ) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 0) :=
      tendsto_fst.mono_right nhdsWithin_le_nhds
    simpa using ht.smul (tendsto_snd : Tendsto (Prod.snd : ℝ × E → E)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 w))
  · exact .of_forall fun _ ↦ mem_univ _
  · apply tendsto_snd.congr'
    filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p ht
    simp [smul_smul,inv_mul_cancel₀ (ne_of_gt ht)]

end RW
