/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Density of qualified inverse images of convex domains
-/
import RockafellarWets.Chapter9.FeasibleSetSemidifferentiability
import RockafellarWets.Chapter6.RelativeInteriorQualification
import Mathlib.Analysis.Convex.Intrinsic

open Set Filter Topology Metric
open scoped InnerProductSpace

namespace RW
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Mixing a closure point with a relative-interior point enters the convex set. -/
theorem Convex.combo_closure_intrinsicInterior_mem {D : Set F} (hD : Convex ℝ D)
    {c z : F} (hc : c ∈ closure D) (hz : z ∈ intrinsicInterior ℝ D)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a+b = 1) : a • c+b • z ∈ D := by
  obtain ⟨p,hp,rfl⟩ := mem_intrinsicInterior.mp hz
  obtain ⟨cs,hcs,hct⟩ := mem_closure_iff_seq_limit.mp hc
  have hcS : c ∈ affineSpan ℝ D :=
    closure_minimal (subset_affineSpan ℝ D) (affineSpan ℝ D).closed_of_finiteDimensional hc
  have hmem (n : ℕ) : (p:F)+(a/b) • (c-cs n) ∈ affineSpan ℝ D := by
    have hd := AffineSubspace.vsub_mem_direction hcS (subset_affineSpan ℝ D (hcs n))
    have hh := AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ (a/b) hd) p.property
    simpa only [vadd_eq_add,add_comm] using hh
  let zs (n : ℕ) : affineSpan ℝ D := ⟨(p:F)+(a/b) • (c-cs n),hmem n⟩
  have ht : Tendsto zs atTop (𝓝 p) := by
    apply tendsto_subtype_rng.mpr
    have hh : Tendsto (fun n ↦ (p:F)+(a/b) • (c-cs n)) atTop
        (𝓝 ((p:F)+(a/b) • (c-c))) :=
      tendsto_const_nhds.add ((tendsto_const_nhds.sub hct).const_smul (a/b))
    simpa only [sub_self,smul_zero,add_zero] using hh
  obtain ⟨n,hn⟩ := (ht.eventually (mem_interior_iff_mem_nhds.mp hp)).exists
  have hh := hD (hcs n) hn ha hb.le hab
  convert hh using 1
  dsimp [zs]
  rw [smul_add,smul_smul]
  have hba : b*(a/b) = a := by field_simp [hb.ne']
  rw [hba,smul_sub]
  abel

/-- Under the normal-kernel qualification, a point mapping into the closure
of a convex set is approached by points mapping into the set itself. -/
theorem mem_closure_preimage_of_convex_qualification {D : Set F} {G : E → F} {x : E}
    (hD : Convex ℝ D) (hG : ContDiff ℝ 1 G) (hx : G x ∈ closure D)
    (hQ : ∀v ∈ normalCone (closure D) (G x), (fderiv ℝ G x).adjoint v = 0 → v = 0) :
    x ∈ closure (G ⁻¹' D) := by
  have hne : D.Nonempty := (show (closure D).Nonempty from ⟨G x,hx⟩).of_closure
  obtain ⟨z,hz⟩ := hne.intrinsicInterior hD
  let H : E × ℝ → F := fun p ↦ (1+p.2) • G p.1-p.2 • z
  have hH : ContDiff ℝ 1 H := by
    dsimp [H]
    exact ((contDiff_const.add contDiff_snd).smul (hG.comp contDiff_fst)).sub (contDiff_snd.smul contDiff_const)
  have hH0 : H (x,0) = G x := by simp [H]
  have hd : (fderiv ℝ H (x,0)).comp (ContinuousLinearMap.inl ℝ E ℝ) = fderiv ℝ G x := by
    have hh := (hH.differentiable (by norm_num) (x,0)).hasFDerivAt.comp x
      (ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt
    have he : (H ∘ (ContinuousLinearMap.inl ℝ E ℝ)) = G := by funext y; simp [H]
    rw [he] at hh
    exact hh.fderiv.symm
  have hbase : x ∈ parameterConstraintMapping (univ : Set E) (closure D) H 0 := by
    exact ⟨mem_univ _,by simpa only [hH0] using hx⟩
  have hCQ : ∀v ∈ normalCone (closure D) (H (x,0)),
      -(((fderiv ℝ H (x,0)).comp (ContinuousLinearMap.inl ℝ E ℝ)).adjoint v) ∈
        normalCone (univ : Set E) x → v = 0 := by
    intro v hv hn
    rw [normalCone_univ,mem_singleton_iff,neg_eq_zero,hd] at hn
    exact hQ v (hH0 ▸ hv) hn
  have hA := (parameterConstraintMapping_semidifferentiability isClosed_univ isClosed_closure hH hbase
    (isClarkeRegularAt_univ x) (by rw [hH0]; exact isClarkeRegularAt_of_convex hD.closure hx (RW.IsClosed.isLocallyClosedAt isClosed_closure _)) hCQ).1
  obtain ⟨k,V,hV,W,hW,hest⟩ := hA.2.2.2
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have htend : Tendsto (fun t : ℝ ↦ (k:ℝ)*|t|) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ ↦ (k:ℝ)*|t|) := continuous_const.mul continuous_abs
    simpa using hc.tendsto (0:ℝ)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ V ∧ (k:ℝ)*|t| < ε :=
    ((show ∀ᶠ t : ℝ in 𝓝 0,t ∈ V from hV).and (htend.eventually (Iio_mem_nhds hε))).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,⟨htV,htε⟩,ht⟩ := (hsmall.and eventually_mem_nhdsWithin).exists
  have htpos : 0 < t := ht
  obtain ⟨y,hy,hdist⟩ := hest 0 ⟨mem_univ _,mem_of_mem_nhds hV⟩ t ⟨mem_univ _,htV⟩ x
    ⟨hbase,mem_of_mem_nhds hW⟩
  refine ⟨y,?_,?_⟩
  · have hp : 0 < 1+t := by linarith
    have hh := Convex.combo_closure_intrinsicInterior_mem hD hy.2 hz
      (a := 1/(1+t)) (b := t/(1+t)) (by positivity) (by positivity) (by field_simp [hp.ne'])
    have he : (1/(1+t)) • H (y,t)+(t/(1+t)) • z = G y := by
      dsimp [H]
      rw [smul_sub,smul_smul,smul_smul]
      have h1 : 1/(1+t)*(1+t) = (1:ℝ) := div_mul_cancel₀ _ hp.ne'
      have h2 : 1/(1+t)*t = t/(1+t) := by ring
      rw [h1,h2,one_smul]
      abel
    rwa [he] at hh
  · exact (hdist.trans_lt (by simpa only [Real.dist_eq,zero_sub,abs_neg] using htε))

end RW
