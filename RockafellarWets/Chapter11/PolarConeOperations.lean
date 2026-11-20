/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Rules for polar cones

Corollary 11.25, including the hypotheses permitting removal of closures.
-/
import RockafellarWets.Chapter11.SupportConjugates
import RockafellarWets.Chapter6.StrictConeSeparation
import RockafellarWets.Chapter6.ConstraintQualifications

open Set Topology
open scoped InnerProductSpace Pointwise
namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem polarCone_add {K L : Set E} (hk : IsCone K) (hl : IsCone L) :
    polarCone (K+L) = polarCone K ∩ polarCone L := by
  ext v
  constructor
  · intro h
    exact ⟨fun x hx ↦ by simpa using h (x+0) ⟨x,hx,0,hl.1,rfl⟩,
      fun y hy ↦ by simpa using h (0+y) ⟨0,hk.1,y,hy,rfl⟩⟩
  · rintro ⟨h1,h2⟩ _ ⟨x,hx,y,hy,rfl⟩
    simpa only [inner_add_right] using add_nonpos (h1 x hx) (h2 y hy)

theorem polarCone_iUnion {ι : Sort*} (K : ι → Set E) :
    polarCone (⋃i,K i) = ⋂i,polarCone (K i) := by
  ext v
  simp only [mem_polarCone,mem_iUnion,forall_exists_index,mem_iInter]
  exact forall_comm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem polarCone_linear_image (A : E →L[ℝ] F) (K : Set E) :
    polarCone (A '' K) = A.adjoint ⁻¹' polarCone K := by
  ext v
  constructor
  · intro h x hx
    simpa only [ContinuousLinearMap.adjoint_inner_left] using h (A x) ⟨x,hx,rfl⟩
  · rintro h _ ⟨x,hx,rfl⟩
    simpa only [ContinuousLinearMap.adjoint_inner_left] using h x hx

theorem polarCone_inter {K L : Set E} (hkc : Convex ℝ K) (hlc : Convex ℝ L)
    (hkclosed : IsClosed K) (hlclosed : IsClosed L) (hk : IsCone K) (hl : IsCone L) :
    polarCone (K∩L) = closure (polarCone K+polarCone L) := by
  letI := FiniteDimensional.complete ℝ E
  have he : polarCone (polarCone K+polarCone L) = K∩L := by
    rw [polarCone_add (isCone_polarCone K) (isCone_polarCone L),
      polarCone_bipolar_eq_self hkclosed hkc hk, polarCone_bipolar_eq_self hlclosed hlc hl]
  rw [← he, polarCone_bipolar, conicHull_eq_self_of_convex_isCone
    ((convex_polarCone K).add (convex_polarCone L)) (isCone_add (isCone_polarCone K) (isCone_polarCone L))]

theorem polarCone_linear_preimage (A : E →L[ℝ] F) {H : Set F} (hc : Convex ℝ H)
    (hclosed : IsClosed H) (hcone : IsCone H) :
    polarCone (A ⁻¹' H) = closure (A.adjoint '' polarCone H) := by
  letI := FiniteDimensional.complete ℝ E
  letI := FiniteDimensional.complete ℝ F
  have he : polarCone (A.adjoint '' polarCone H) = A ⁻¹' H := by
    rw [polarCone_linear_image, ContinuousLinearMap.adjoint_adjoint,
      polarCone_bipolar_eq_self hclosed hc hcone]
  have himconv : Convex ℝ (A.adjoint '' polarCone H) :=
    (convex_polarCone H).linear_image A.adjoint.toLinearMap
  have himcone : IsCone (A.adjoint '' polarCone H) :=
    LinearMap.isCone_image A.adjoint.toLinearMap (isCone_polarCone H)
  rw [← he, polarCone_bipolar, conicHull_eq_self_of_convex_isCone himconv himcone]

/-- The zero-interior qualification forces every polar multiplier to vanish. -/
theorem eq_zero_of_mem_polarCone_of_zero_mem_interior {K : Set E} (hc : Convex ℝ K)
    (hk : IsCone K) (h0 : (0:E) ∈ interior K) {v : E} (hv : v ∈ polarCone K) : v = 0 := by
  by_contra hn
  have h := (mem_interior_iff_inner_lt_zero_on_polarCone hc hk).mp h0 v hv hn
  simpa using h

/-- Under the qualification in 11.25(b), the sum of the polar cones is closed. -/
theorem isClosed_add_polarCones_of_zero_mem_interior {K L : Set E}
    (hkc : Convex ℝ K) (hlc : Convex ℝ L) (hk : IsCone K) (hl : IsCone L)
    (hq : (0:E) ∈ interior (K + -L)) : IsClosed (polarCone K+polarCone L) := by
  apply isClosed_add_of_horizonCone_no_cancel (isClosed_polarCone K) (isClosed_polarCone L)
  intro u v hu hv huv
  rw [horizonCone_eq_self_of_isClosed_isCone (isClosed_polarCone K) (isCone_polarCone K)] at hu
  rw [horizonCone_eq_self_of_isClosed_isCone (isClosed_polarCone L) (isCone_polarCone L)] at hv
  have hum : u ∈ polarCone (K + -L) := by
    rw [polarCone_add_neg hk hl]
    exact ⟨hu, show -u ∈ polarCone L from (neg_eq_iff_add_eq_zero.mpr huv).symm ▸ hv⟩
  have hu0 := eq_zero_of_mem_polarCone_of_zero_mem_interior (hkc.add hlc.neg)
    (isCone_add hk (isCone_neg hl)) hq hum
  exact ⟨hu0, by simpa [hu0] using huv⟩

theorem polarCone_inter_of_zero_mem_interior {K L : Set E}
    (hkc : Convex ℝ K) (hlc : Convex ℝ L) (hkclosed : IsClosed K) (hlclosed : IsClosed L)
    (hk : IsCone K) (hl : IsCone L) (hq : (0:E) ∈ interior (K + -L)) :
    polarCone (K∩L) = polarCone K+polarCone L := by
  rw [polarCone_inter hkc hlc hkclosed hlclosed hk hl,
    (isClosed_add_polarCones_of_zero_mem_interior hkc hlc hk hl hq).closure_eq]

/-- Under the qualification in 11.25(d), the adjoint polar image is closed. -/
theorem isClosed_adjoint_image_polarCone_of_zero_mem_interior (A : E →L[ℝ] F)
    {H : Set F} (hc : Convex ℝ H) (hcone : IsCone H)
    (hq : (0:F) ∈ interior (H + -(Set.range A))) : IsClosed (A.adjoint '' polarCone H) := by
  apply isClosed_linearImage_of_horizonCone_ker_trivial (L := A.adjoint.toLinearMap) (isClosed_polarCone H)
  intro v hv hAv
  change A.adjoint v = 0 at hAv
  rw [horizonCone_eq_self_of_isClosed_isCone (isClosed_polarCone H) (isCone_polarCone H)] at hv
  have hrcone : IsCone (Set.range A) := ⟨⟨0,A.map_zero⟩, fun {x} hx {t} _ ↦ by
    obtain ⟨z,rfl⟩ := hx; exact ⟨t • z, A.map_smul t z⟩⟩
  have hrconv : Convex ℝ (Set.range A) := by
    simpa only [image_univ] using convex_univ.linear_image A.toLinearMap
  apply eq_zero_of_mem_polarCone_of_zero_mem_interior (hc.add hrconv.neg)
    (isCone_add hcone (isCone_neg hrcone)) hq
  rw [polarCone_add_neg hcone hrcone]
  refine ⟨hv, ?_⟩
  rintro _ ⟨x,rfl⟩
  have hz : ⟪v,A x⟫_ℝ = 0 := by rw [← ContinuousLinearMap.adjoint_inner_left, hAv, inner_zero_left]
  simp [inner_neg_left,hz]

theorem polarCone_linear_preimage_of_zero_mem_interior (A : E →L[ℝ] F)
    {H : Set F} (hc : Convex ℝ H) (hclosed : IsClosed H) (hcone : IsCone H)
    (hq : (0:F) ∈ interior (H + -(Set.range A))) :
    polarCone (A ⁻¹' H) = A.adjoint '' polarCone H := by
  rw [polarCone_linear_preimage A hc hclosed hcone,
    (isClosed_adjoint_image_polarCone_of_zero_mem_interior A hc hcone hq).closure_eq]

end RW
