/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite amenable objectives with amenable constraints
-/
import RockafellarWets.Chapter10.AmenableSums
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set Filter Topology
open scoped InnerProductSpace

noncomputable section
namespace RW
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- An amenable function that is finite near its base has no nonzero
horizon subgradient. Finiteness is needed only locally. -/
theorem AmenableFunctionModel.horizon_eq_zero_of_finite {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r)
    (hfinite : ∀ᶠ y in 𝓝 x, f y ≠ ⊤) : horizonSubdifferential f x = {0} := by
  have hval : M.outer (M.inner x) = ((f x).toReal:EReal) := by
    rw [← M.eqOn x M.mem]
    exact (EReal.coe_toReal M.finite.2 M.finite.1).symm
  have hxd : M.inner x ∈ closure (effectiveDomain M.outer) :=
    subset_closure (hval.trans_lt (EReal.coe_lt_top _))
  have hN : normalCone (closure (effectiveDomain M.outer)) (M.inner x) = {0} := by
    apply Subset.antisymm
    · intro v hv
      apply mem_singleton_iff.mpr
      apply M.qualification v hv
      have hn := hv
      rw [normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph M.convex).closure hxd] at hn
      have hmax : IsLocalMax (fun y ↦ ⟪v,M.inner y⟫_ℝ) x := by
        filter_upwards [hfinite,M.isOpen.mem_nhds M.mem] with y hy hyV
        have hyd : M.inner y ∈ closure (effectiveDomain M.outer) := by
          apply subset_closure
          change M.outer (M.inner y) < ⊤
          rw [← M.eqOn y hyV]
          exact lt_top_iff_ne_top.mpr hy
        simpa only [inner_sub_right,sub_nonpos] using hn (M.inner y) hyd
      have hmd := ((M.smooth x M.mem).contDiffAt (M.isOpen.mem_nhds M.mem)).differentiableAt
        (by exact_mod_cast (show r ≠ 0 by omega))
      have hd := (innerSL ℝ v).hasFDerivAt.comp x hmd.hasFDerivAt
      have hzero := hmax.hasFDerivAt_eq_zero hd
      apply ext_inner_right ℝ
      intro w
      rw [ContinuousLinearMap.adjoint_inner_left,inner_zero_left]
      exact congrArg (fun A : E →L[ℝ] ℝ ↦ A w) hzero
    · rintro v rfl
      exact (isCone_normalCone hxd).1
  rw [(M.derivatives hr).2.1,horizonSubdifferential_eq_normalCone_closure_domain M.proper M.lsc M.convex hval,hN]
  simp

/-- **Example 10.24(f)**: a finite amenable objective plus the indicator of
an amenable set preserves the representation order and its full variant. -/
def AmenableFunctionModel.add_indicator {f : E → EReal} {C : Set E} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (N : AmenableSetModel C x r full) (hr : 1 ≤ r)
    (hfinite : ∀ᶠ y in 𝓝 x, f y ≠ ⊤) : AmenableFunctionModel (fun y ↦ f y+indicatorVA C y) x r full :=
  M.add N.indicator hr (by
    intro v hv w hw he
    rw [M.horizon_eq_zero_of_finite hr hfinite,mem_singleton_iff] at hv
    exact ⟨hv,by simpa only [hv,zero_add] using he⟩)

/-- **Example 10.24(f)**, ordinary amenability. -/
theorem AmenableAt.add_indicator {f : E → EReal} {C : Set E} {x : E}
    (hf : AmenableAt f x) (hC : SetAmenableAt C x) (hfinite : ∀ᶠ y in 𝓝 x, f y ≠ ⊤) :
    AmenableAt (fun y ↦ f y+indicatorVA C y) x := by
  obtain ⟨M⟩ := hf
  obtain ⟨N⟩ := hC
  exact ⟨M.add_indicator N le_rfl hfinite⟩

/-- **Example 10.24(f)**, strong amenability. -/
theorem StronglyAmenableAt.add_indicator {f : E → EReal} {C : Set E} {x : E}
    (hf : StronglyAmenableAt f x) (hC : SetStronglyAmenableAt C x) (hfinite : ∀ᶠ y in 𝓝 x, f y ≠ ⊤) :
    StronglyAmenableAt (fun y ↦ f y+indicatorVA C y) x := by
  obtain ⟨M⟩ := hf
  obtain ⟨N⟩ := hC
  exact ⟨M.add_indicator N (by norm_num) hfinite⟩

/-- **Example 10.24(f)**, full amenability. -/
theorem FullyAmenableAt.add_indicator {f : E → EReal} {C : Set E} {x : E}
    (hf : FullyAmenableAt f x) (hC : SetFullyAmenableAt C x) (hfinite : ∀ᶠ y in 𝓝 x, f y ≠ ⊤) :
    FullyAmenableAt (fun y ↦ f y+indicatorVA C y) x := by
  obtain ⟨M⟩ := hf
  obtain ⟨N⟩ := hC
  exact ⟨M.add_indicator N (by norm_num) hfinite⟩

end RW
end
