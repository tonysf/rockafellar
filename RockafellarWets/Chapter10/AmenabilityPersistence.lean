/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Persistence of the amenability qualification
-/
import RockafellarWets.Chapter10.Amenability
import RockafellarWets.Chapter6.BoundaryNormals

open Set Filter Topology Metric

namespace RW
variable {E F G : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The normal-kernel qualification persists under continuous perturbation
of the base point and the linear operator. -/
theorem normalKernelQualification_eventually {D : Set F} (hD : IsClosed D)
    {f : E → F} {A : E → F →L[ℝ] G} {x : E}
    (hf : ContinuousAt f x) (hA : ContinuousAt A x)
    (hQ : ∀ v ∈ normalCone D (f x), A x v = 0 → v = 0) :
    ∀ᶠ y in 𝓝 x, ∀ v ∈ normalCone D (f y), A y v = 0 → v = 0 := by
  by_contra hn
  obtain ⟨ys,hys,hbad⟩ := exists_seq_forall_of_frequently (not_eventually.mp hn)
  have hex : ∀ n, ∃ v, v ∈ normalCone D (f (ys n)) ∧ A (ys n) v = 0 ∧ v ≠ 0 := by
    intro n
    have h := hbad n
    push_neg at h
    exact h
  choose v hv hvA hvne using hex
  let z (n : ℕ) : F := ‖v n‖⁻¹ • v n
  have hznorm (n : ℕ) : ‖z n‖ = 1 := by
    simp [z,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hvne n))]
  have hzN (n : ℕ) : z n ∈ normalCone D (f (ys n)) :=
    (isCone_normalCone (hv n).1).2 (hv n) (inv_pos.mpr (norm_pos_iff.mpr (hvne n)))
  have hzA (n : ℕ) : A (ys n) (z n) = 0 := by simp [z,map_smul,hvA n]
  obtain ⟨z₀,hz₀,φ,hφ,hzto⟩ := (isCompact_sphere (0 : F) 1).tendsto_subseq
    (fun n ↦ show z n ∈ sphere (0 : F) 1 by simpa using hznorm n)
  have hyto := hys.comp hφ.tendsto_atTop
  have hfto := hf.tendsto.comp hyto
  have hxD : f x ∈ D := hD.mem_of_tendsto hfto (.of_forall fun n ↦ (hv (φ n)).1)
  have hnormal := mem_normalCone_of_tendsto hxD (fun n ↦ (hv (φ n)).1) hfto
    (fun n ↦ hzN (φ n)) hzto
  have hAt : Tendsto (fun n ↦ A (ys (φ n)) (z (φ n))) atTop (𝓝 (A x z₀)) :=
    ((continuous_fst.clm_apply continuous_snd : Continuous (fun p : (F →L[ℝ] G) × F ↦ p.1 p.2)).tendsto (A x,z₀)).comp
      ((hA.tendsto.comp hyto).prodMk_nhds hzto)
  have hzero : A x z₀ = 0 := tendsto_nhds_unique hAt
    (tendsto_const_nhds.congr fun n ↦ (hzA (φ n)).symm)
  have hz0 := hQ z₀ hnormal hzero
  simpa [hz0] using hz₀

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Theorem 10.25(b)**, the original function model works at all nearby
domain points, for each of the three amenability variants. -/
theorem AmenableFunctionModel.eventually_models {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain f → Nonempty (AmenableFunctionModel f y r full) := by
  have hcont : ContinuousAt M.inner x := M.smooth.continuousOn.continuousAt (M.isOpen.mem_nhds M.mem)
  have hder : ContinuousAt (fderiv ℝ M.inner) x :=
    (M.smooth.continuousOn_fderiv_of_isOpen M.isOpen (by exact_mod_cast hr)).continuousAt (M.isOpen.mem_nhds M.mem)
  have hQ := normalKernelQualification_eventually isClosed_closure hcont
    (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hder) M.qualification
  filter_upwards [hQ,M.isOpen.mem_nhds M.mem] with y hy hyV hdom
  refine ⟨{ M with mem := hyV, finite := ?_, qualification := hy }⟩
  refine ⟨?_,ne_of_lt hdom⟩
  rw [M.eqOn y hyV]
  exact ne_of_gt (M.proper.2 _)

/-- **Theorem 10.25(d)**, persistence of every set-amenability variant. -/
theorem AmenableSetModel.eventually_models {C : Set E} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableSetModel C x r full) (hr : 1 ≤ r) :
    ∀ᶠ y in 𝓝 x, y ∈ C → Nonempty (AmenableSetModel C y r full) := by
  have hcont : ContinuousAt M.inner x := M.smooth.continuousOn.continuousAt (M.isOpen.mem_nhds M.mem)
  have hder : ContinuousAt (fderiv ℝ M.inner) x :=
    (M.smooth.continuousOn_fderiv_of_isOpen M.isOpen (by exact_mod_cast hr)).continuousAt (M.isOpen.mem_nhds M.mem)
  have hQ := normalKernelQualification_eventually M.closed hcont
    (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hder) M.qualification
  filter_upwards [hQ,M.isOpen.mem_nhds M.mem] with y hy hyV hC
  exact ⟨{ M with mem := hyV,base := hC,qualification := hy }⟩

theorem AmenableAt.eventually {f : E → EReal} {x : E} (h : AmenableAt f x) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain f → AmenableAt f y := by
  obtain ⟨M⟩ := h
  exact M.eventually_models le_rfl

theorem StronglyAmenableAt.eventually {f : E → EReal} {x : E} (h : StronglyAmenableAt f x) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain f → StronglyAmenableAt f y := by
  obtain ⟨M⟩ := h
  exact M.eventually_models (by norm_num)

theorem FullyAmenableAt.eventually {f : E → EReal} {x : E} (h : FullyAmenableAt f x) :
    ∀ᶠ y in 𝓝 x, y ∈ effectiveDomain f → FullyAmenableAt f y := by
  obtain ⟨M⟩ := h
  exact M.eventually_models (by norm_num)

theorem SetAmenableAt.eventually {C : Set E} {x : E} (h : SetAmenableAt C x) :
    ∀ᶠ y in 𝓝 x, y ∈ C → SetAmenableAt C y := by
  obtain ⟨M⟩ := h
  exact M.eventually_models le_rfl

theorem SetStronglyAmenableAt.eventually {C : Set E} {x : E} (h : SetStronglyAmenableAt C x) :
    ∀ᶠ y in 𝓝 x, y ∈ C → SetStronglyAmenableAt C y := by
  obtain ⟨M⟩ := h
  exact M.eventually_models (by norm_num)

theorem SetFullyAmenableAt.eventually {C : Set E} {x : E} (h : SetFullyAmenableAt C x) :
    ∀ᶠ y in 𝓝 x, y ∈ C → SetFullyAmenableAt C y := by
  obtain ⟨M⟩ := h
  exact M.eventually_models (by norm_num)

end RW
