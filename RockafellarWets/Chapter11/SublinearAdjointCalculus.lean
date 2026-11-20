/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Duality in calculating adjoints of sublinear mappings

Exercise 11.31. The graph of a composition and the graph of a sum are linear
images of the intersection of two graph cylinders in a product of three
spaces. A polar direction that cancels between the two cylinders vanishes at
a common relative-interior point, so it annihilates both cylinders by the
vanishing principle of Exercise 6.39(b). Projecting out this common
annihilator leaves no cancellation, and the horizon criterion of Exercise
3.12 makes the sum of the two polars closed. Relative-interior points of the
graphs over the qualifying point then show that the closures of the
cylinders meet inside the closure of their intersection, so no closure is
needed even when the graphs are not closed.
-/
import RockafellarWets.Chapter11.SublinearAdjointOperations
import RockafellarWets.Chapter6.RelativeInteriorQualification
import RockafellarWets.Chapter10.ConvexDomainDensity

open Set Filter Topology
open scoped InnerProductSpace Pointwise

namespace RW

section RelativeInteriorImages

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

omit [FiniteDimensional ℝ V] in
/-- Mixing a point of a convex set with a relative-interior point, with a
positive weight on the latter, stays in the relative interior. -/
theorem Convex.combo_mem_intrinsicInterior {C : Set V} (hC : Convex ℝ C) {c z : V}
    (hc : c ∈ C) (hz : z ∈ intrinsicInterior ℝ C) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a + b = 1) : a • c + b • z ∈ intrinsicInterior ℝ C := by
  obtain ⟨p, hp, rfl⟩ := mem_intrinsicInterior.mp hz
  have hcS : c ∈ affineSpan ℝ C := subset_affineSpan ℝ C hc
  have ha' : a = 1 - b := by linarith
  have hq : a • c + b • (p : V) ∈ affineSpan ℝ C := by
    have h := AffineMap.lineMap_mem b hcS p.2
    rwa [AffineMap.lineMap_apply_module, ← ha'] at h
  let ψ : affineSpan ℝ C → affineSpan ℝ C := fun s ↦
    ⟨AffineMap.lineMap c (s : V) b⁻¹, AffineMap.lineMap_mem _ hcS s.2⟩
  have hψ : Continuous ψ :=
    (continuous_const.lineMap continuous_subtype_val continuous_const).subtype_mk _
  have hψq : ψ ⟨_, hq⟩ = p := by
    apply Subtype.ext
    change AffineMap.lineMap c (a • c + b • (p : V)) b⁻¹ = (p : V)
    rw [AffineMap.lineMap_apply_module, ha']
    match_scalars
    · field_simp; ring
    · field_simp
  refine mem_intrinsicInterior.mpr ⟨⟨_, hq⟩, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds]
  have hU : ψ ⁻¹' interior (((↑) : affineSpan ℝ C → V) ⁻¹' C) ∈
      𝓝 (⟨_, hq⟩ : affineSpan ℝ C) :=
    (isOpen_interior.preimage hψ).mem_nhds (by rw [mem_preimage, hψq]; exact hp)
  refine mem_of_superset hU fun s hs ↦ ?_
  have hs' : ψ s ∈ ((↑) : affineSpan ℝ C → V) ⁻¹' C :=
    interior_subset (show ψ s ∈ interior (((↑) : affineSpan ℝ C → V) ⁻¹' C) from hs)
  have he : a • c + b • ((ψ s : affineSpan ℝ C) : V) = (s : V) := by
    change a • c + b • AffineMap.lineMap c (s : V) b⁻¹ = (s : V)
    rw [AffineMap.lineMap_apply_module, ha']
    match_scalars
    · field_simp; ring
    · field_simp
  change (s : V) ∈ C
  rw [← he]
  exact hC hc hs' ha hb.le hab

/-- Every relative-interior point of a linear image of a convex set is the
image of a relative-interior point. -/
theorem exists_mem_intrinsicInterior_of_mem_intrinsicInterior_image (A : V →ₗ[ℝ] W)
    {C : Set V} (hC : Convex ℝ C) {w : W} (hw : w ∈ intrinsicInterior ℝ (A '' C)) :
    ∃ c ∈ intrinsicInterior ℝ C, A c = w := by
  have hne : C.Nonempty := by
    obtain ⟨c, hc, -⟩ := (intrinsicInterior_subset hw : w ∈ A '' C)
    exact ⟨c, hc⟩
  obtain ⟨c₁, hc₁⟩ := hne.intrinsicInterior hC
  obtain ⟨ε, hε, hmem⟩ := exists_pos_add_smul_sub_mem_of_mem_intrinsicInterior hw
    ⟨c₁, intrinsicInterior_subset hc₁, rfl⟩
  obtain ⟨c₂, hc₂, hAc₂⟩ := hmem
  have h1 : (0 : ℝ) < 1 + ε := by linarith
  refine ⟨(1 + ε)⁻¹ • c₂ + (ε * (1 + ε)⁻¹) • c₁,
    Convex.combo_mem_intrinsicInterior hC hc₂ hc₁ (by positivity) (by positivity)
      (by field_simp), ?_⟩
  rw [map_add, map_smul, map_smul, hAc₂]
  match_scalars
  · field_simp
  · field_simp; ring

end RelativeInteriorImages

section PolarIntersection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- If every polar direction cancelling between two cones annihilates both of
them, the sum of the polar cones is closed. -/
theorem isClosed_add_polarCone_of_annihilating {C D : Set V}
    (hann : ∀ u, u ∈ polarCone C → -u ∈ polarCone D → ∀ x ∈ C ∪ D, ⟪u, x⟫_ℝ = 0) :
    IsClosed (polarCone C + polarCone D) := by
  set N : Submodule ℝ V := (Submodule.span ℝ (C ∪ D))ᗮ with hNdef
  have hNperp : ∀ n ∈ N, ∀ x ∈ C ∪ D, ⟪n, x⟫_ℝ = 0 := fun n hn x hx ↦
    (Submodule.mem_orthogonal' _ n).mp hn x (Submodule.subset_span hx)
  have hNmem : ∀ u : V, (∀ x ∈ C ∪ D, ⟪u, x⟫_ℝ = 0) → u ∈ N := by
    intro u hu
    rw [hNdef, Submodule.mem_orthogonal']
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hu x hx
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  have hNC : (N : Set V) ⊆ polarCone C := fun n hn x hx ↦ (hNperp n hn x (Or.inl hx)).le
  have hND : (N : Set V) ⊆ polarCone D := fun n hn x hx ↦ (hNperp n hn x (Or.inr hx)).le
  have hzero : ∀ u : V, u ∈ N → u ∈ Nᗮ → u = 0 := fun u h1 h2 ↦ by
    have h : u ∈ N ⊓ Nᗮ := ⟨h1, h2⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h
  have hNclosed : IsClosed (N : Set V) := N.closed_of_finiteDimensional
  have hNoclosed : IsClosed (Nᗮ : Set V) := Nᗮ.closed_of_finiteDimensional
  have hNcone : IsCone (N : Set V) := ⟨N.zero_mem, fun x hx c _ ↦ N.smul_mem c hx⟩
  set Q₁ := polarCone C ∩ (Nᗮ : Set V) with hQ₁def
  set Q₂ := polarCone D ∩ (Nᗮ : Set V) with hQ₂def
  have hQ₁ : IsClosed Q₁ := (isClosed_polarCone C).inter hNoclosed
  have hQ₂ : IsClosed Q₂ := (isClosed_polarCone D).inter hNoclosed
  have hQ₁c : IsCone Q₁ := ⟨⟨zero_mem_polarCone C, Nᗮ.zero_mem⟩,
    fun x hx c hc ↦ ⟨(isCone_polarCone C).2 hx.1 hc, Nᗮ.smul_mem c hx.2⟩⟩
  have hQ₂c : IsCone Q₂ := ⟨⟨zero_mem_polarCone D, Nᗮ.zero_mem⟩,
    fun x hx c hc ↦ ⟨(isCone_polarCone D).2 hx.1 hc, Nᗮ.smul_mem c hx.2⟩⟩
  have hQsum : IsClosed (Q₁ + Q₂) := by
    apply isClosed_add_of_horizonCone_no_cancel hQ₁ hQ₂
    intro u v hu hv huv
    rw [horizonCone_eq_self_of_isClosed_isCone hQ₁ hQ₁c] at hu
    rw [horizonCone_eq_self_of_isClosed_isCone hQ₂ hQ₂c] at hv
    obtain rfl : v = -u := eq_neg_of_add_eq_zero_right huv
    have hu0 : u = 0 := hzero u (hNmem u (hann u hu.1 hv.1)) hu.2
    exact ⟨hu0, by rw [hu0, neg_zero]⟩
  have hdecomp : polarCone C + polarCone D = (Q₁ + Q₂) + (N : Set V) := by
    apply Subset.antisymm
    · rintro _ ⟨p, hp, q, hq, rfl⟩
      have hp' : p - N.starProjection p ∈ polarCone C := by
        rw [sub_eq_add_neg]
        exact add_mem_of_convex_isCone (convex_polarCone C) (isCone_polarCone C) hp
          (hNC (N.neg_mem (N.starProjection_apply_mem p)))
      have hq' : q - N.starProjection q ∈ polarCone D := by
        rw [sub_eq_add_neg]
        exact add_mem_of_convex_isCone (convex_polarCone D) (isCone_polarCone D) hq
          (hND (N.neg_mem (N.starProjection_apply_mem q)))
      refine ⟨(p - N.starProjection p) + (q - N.starProjection q),
        ⟨_, ⟨hp', N.sub_starProjection_mem_orthogonal p⟩, _,
          ⟨hq', N.sub_starProjection_mem_orthogonal q⟩, rfl⟩,
        N.starProjection p + N.starProjection q,
        N.add_mem (N.starProjection_apply_mem p) (N.starProjection_apply_mem q),
        by dsimp only; abel⟩
    · rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, n, hn, rfl⟩
      exact ⟨a, ha.1, b + n, add_mem_of_convex_isCone (convex_polarCone D) (isCone_polarCone D)
        hb.1 (hND hn), by dsimp only; abel⟩
  rw [hdecomp]
  apply isClosed_add_of_horizonCone_no_cancel hQsum hNclosed
  intro u v hu hv huv
  rw [horizonCone_eq_self_of_isClosed_isCone hQsum (isCone_add hQ₁c hQ₂c)] at hu
  rw [horizonCone_eq_self_of_isClosed_isCone hNclosed hNcone] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := hu
  have hab : a + b ∈ Nᗮ := Nᗮ.add_mem ha.2 hb.2
  obtain rfl : v = -(a + b) := eq_neg_of_add_eq_zero_right huv
  have habN : a + b ∈ N := by simpa using N.neg_mem hv
  have h0 : a + b = 0 := hzero _ habN hab
  exact ⟨h0, by rw [h0, neg_zero]⟩

/-- Polar of an intersection of convex cones without closure: it suffices that
cancelling polar directions annihilate both cones and that the closures of
the cones meet inside the closure of their intersection. -/
theorem polarCone_inter_eq_add_of_annihilating {C D : Set V}
    (hCc : Convex ℝ C) (hCk : IsCone C) (hDc : Convex ℝ D) (hDk : IsCone D)
    (hann : ∀ u, u ∈ polarCone C → -u ∈ polarCone D → ∀ x ∈ C ∪ D, ⟪u, x⟫_ℝ = 0)
    (hcl : closure C ∩ closure D ⊆ closure (C ∩ D)) :
    polarCone (C ∩ D) = polarCone C + polarCone D := by
  letI := FiniteDimensional.complete ℝ V
  apply Subset.antisymm
  · intro v hv
    have hPc : IsClosed (polarCone C + polarCone D) := isClosed_add_polarCone_of_annihilating hann
    have hPk : IsCone (polarCone C + polarCone D) := isCone_add (isCone_polarCone C)
      (isCone_polarCone D)
    have hPv : Convex ℝ (polarCone C + polarCone D) :=
      (convex_polarCone C).add (convex_polarCone D)
    rw [← polarCone_bipolar_eq_self hPc hPv hPk]
    intro x hx
    rw [polarCone_add (isCone_polarCone C) (isCone_polarCone D), polarCone_bipolar,
      polarCone_bipolar, conicHull_eq_self_of_convex_isCone hCc hCk,
      conicHull_eq_self_of_convex_isCone hDc hDk] at hx
    rw [← polarCone_closure] at hv
    exact hv x (hcl hx)
  · rintro _ ⟨a, ha, b, hb, rfl⟩ x hx
    rw [inner_add_left]
    exact add_nonpos (ha x hx.1) (hb x hx.2)

omit [FiniteDimensional ℝ V] in
/-- Closures of two linear cylinders meet inside the closure of their
intersection once some point maps into both relative interiors. -/
theorem closure_inter_preimage_subset {W₁ W₂ : Type*}
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
    (A₁ : V →L[ℝ] W₁) (A₂ : V →L[ℝ] W₂) {S₁ : Set W₁} {S₂ : Set W₂}
    (hS₁ : Convex ℝ S₁) (hS₂ : Convex ℝ S₂) {k : V}
    (hk₁ : A₁ k ∈ intrinsicInterior ℝ S₁) (hk₂ : A₂ k ∈ intrinsicInterior ℝ S₂) :
    closure (A₁ ⁻¹' S₁) ∩ closure (A₂ ⁻¹' S₂) ⊆ closure (A₁ ⁻¹' S₁ ∩ A₂ ⁻¹' S₂) := by
  rintro p ⟨hp₁, hp₂⟩
  have hc₁ : A₁ p ∈ closure S₁ := map_mem_closure A₁.continuous hp₁ (fun _ h ↦ h)
  have hc₂ : A₂ p ∈ closure S₂ := map_mem_closure A₂.continuous hp₂ (fun _ h ↦ h)
  let γ : ℝ → V := fun t ↦ (1 - t) • p + t • k
  have hγ : Tendsto γ (𝓝[>] 0) (𝓝 p) := by
    have hc : Continuous γ := by fun_prop
    have h0 : γ 0 = p := by simp [γ]
    rw [← h0]
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto hγ
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hev] with t ht ht1
  have ht0 : (0 : ℝ) < t := ht
  refine ⟨?_, ?_⟩
  · change A₁ ((1 - t) • p + t • k) ∈ S₁
    rw [map_add, map_smul, map_smul]
    exact Convex.combo_closure_intrinsicInterior_mem hS₁ hc₁ hk₁ (by linarith) ht0
      (by ring)
  · change A₂ ((1 - t) • p + t • k) ∈ S₂
    rw [map_add, map_smul, map_smul]
    exact Convex.combo_closure_intrinsicInterior_mem hS₂ hc₂ hk₂ (by linarith) ht0
      (by ring)

end PolarIntersection

section Calculus

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem inner_tripleLp (u p : WithLp 2 (WithLp 2 (E × F) × G)) :
    ⟪u, p⟫_ℝ = ⟪u.fst.fst, p.fst.fst⟫_ℝ + ⟪u.fst.snd, p.fst.snd⟫_ℝ + ⟪u.snd, p.snd⟫_ℝ := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem inner_tripleLp_toLp (u : WithLp 2 (WithLp 2 (E × F) × G)) (x : E) (y : F) (z : G) :
    ⟪u, WithLp.toLp 2 (WithLp.toLp 2 (x, y), z)⟫_ℝ =
      ⟪u.fst.fst, x⟫_ℝ + ⟪u.fst.snd, y⟫_ℝ + ⟪u.snd, z⟫_ℝ := rfl

/-- The middle and last coordinates of a triple. -/
def tripleMidLast : WithLp 2 (WithLp 2 (E × F) × G) →L[ℝ] WithLp 2 (F × G) :=
  let L : WithLp 2 (WithLp 2 (E × F) × G) →ₗ[ℝ] WithLp 2 (F × G) :=
    { toFun := fun p ↦ WithLp.toLp 2 (p.fst.snd, p.snd)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  ⟨L, L.continuous_of_finiteDimensional⟩

/-- The first and last coordinates of a triple. -/
def tripleFirstLast : WithLp 2 (WithLp 2 (E × F) × G) →L[ℝ] WithLp 2 (E × G) :=
  let L : WithLp 2 (WithLp 2 (E × F) × G) →ₗ[ℝ] WithLp 2 (E × G) :=
    { toFun := fun p ↦ WithLp.toLp 2 (p.fst.fst, p.snd)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  ⟨L, L.continuous_of_finiteDimensional⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem svRange_eq_image_euclideanSvGraph (H : E → Set F) :
    svRange H = WithLp.sndₗ 2 ℝ E F '' euclideanSvGraph H := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨WithLp.toLp 2 (x, y), hx, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.fst, hq⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem svDom_eq_image_euclideanSvGraph (H : E → Set F) :
    svDom H = WithLp.fstₗ 2 ℝ E F '' euclideanSvGraph H := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨WithLp.toLp 2 (x, y), hy, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.snd, hq⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
theorem eq_zero_of_forall_inner_nonpos {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] {v : X} (h : ∀ x, ⟪v, x⟫_ℝ ≤ 0) : v = 0 :=
  real_inner_self_nonpos.mp (h v)

/-- **Exercise 11.31(a)**, upper adjoints of a composition. -/
theorem svUpperAdjoint_svComp_of_intrinsicInterior {H : E → Set F} {K : F → Set G}
    (hH : SvSublinear H) (hK : SvSublinear K)
    (hq : (intrinsicInterior ℝ (svRange H) ∩ intrinsicInterior ℝ (svDom K)).Nonempty) :
    svUpperAdjoint (svComp K H) = svComp (svUpperAdjoint H) (svUpperAdjoint K) := by
  refine le_antisymm ?_ (svComp_upperAdjoints_subset H K)
  intro z' v hv
  obtain ⟨w, hwH, hwK⟩ := hq
  let A₁ : WithLp 2 (WithLp 2 (E × F) × G) →L[ℝ] WithLp 2 (E × F) :=
    WithLp.fstL 2 ℝ (WithLp 2 (E × F)) G
  let C₁ := A₁ ⁻¹' euclideanSvGraph H
  let C₂ := (tripleMidLast (E := E)) ⁻¹' euclideanSvGraph K
  have hm₁ : ∀ x y z, WithLp.toLp 2 (WithLp.toLp 2 (x, y), z) ∈ C₁ ↔ y ∈ H x :=
    fun _ _ _ ↦ Iff.rfl
  have hm₂ : ∀ x y z, WithLp.toLp 2 (WithLp.toLp 2 (x, y), z) ∈ C₂ ↔ z ∈ K y :=
    fun _ _ _ ↦ Iff.rfl
  have hC₁c : Convex ℝ C₁ := hH.convex_euclideanSvGraph.linear_preimage A₁.toLinearMap
  have hC₂c : Convex ℝ C₂ :=
    hK.convex_euclideanSvGraph.linear_preimage (tripleMidLast (E := E)).toLinearMap
  have hC₁k : IsCone C₁ := LinearMap.isCone_preimage A₁.toLinearMap hH.isCone_euclideanSvGraph
  have hC₂k : IsCone C₂ :=
    LinearMap.isCone_preimage (tripleMidLast (E := E)).toLinearMap hK.isCone_euclideanSvGraph
  -- the last coordinate of a polar of the first cylinder vanishes
  have hlast : ∀ u ∈ polarCone C₁, u.snd = 0 := by
    intro u hu
    refine eq_zero_of_forall_inner_nonpos fun z ↦ ?_
    have h := hu _ ((hm₁ 0 0 z).mpr hH.1.1)
    simpa [inner_tripleLp_toLp] using h
  -- the first coordinate of a polar of the second cylinder vanishes
  have hfirst : ∀ u ∈ polarCone C₂, u.fst.fst = 0 := by
    intro u hu
    refine eq_zero_of_forall_inner_nonpos fun x ↦ ?_
    have h := hu _ ((hm₂ x 0 0).mpr hK.1.1)
    simpa [inner_tripleLp_toLp] using h
  have hann : ∀ u, u ∈ polarCone C₁ → -u ∈ polarCone C₂ → ∀ x ∈ C₁ ∪ C₂, ⟪u, x⟫_ℝ = 0 := by
    intro u hu hu'
    have hz := hlast u hu
    have hx : u.fst.fst = 0 := by simpa using hfirst _ hu'
    have hR : ∀ l ∈ svRange H, ⟪u.fst.snd, l⟫_ℝ ≤ 0 := by
      rintro l ⟨x, hl⟩
      have h := hu _ ((hm₁ x l 0).mpr hl)
      simpa [inner_tripleLp_toLp, hx] using h
    have hD : ∀ l ∈ svDom K, ⟪-u.fst.snd, l⟫_ℝ ≤ 0 := by
      rintro l ⟨z, hl⟩
      have h := hu' _ ((hm₂ 0 l z).mpr hl)
      simpa [inner_tripleLp_toLp, hz] using h
    have hw0 : ⟪u.fst.snd, w⟫_ℝ = 0 := by
      have h1 := hR w (intrinsicInterior_subset hwH)
      have h2 := hD w (intrinsicInterior_subset hwK)
      rw [inner_neg_left] at h2
      linarith
    have hR0 := inner_eq_zero_of_mem_intrinsicInterior hR hwH hw0
    have hD0 := inner_eq_zero_of_mem_intrinsicInterior hD hwK
      (by rw [inner_neg_left, hw0, neg_zero])
    rintro p (hp | hp)
    · rw [inner_tripleLp, hx, hz, hR0 p.fst.snd ⟨p.fst.fst, hp⟩]
      simp
    · have h := hD0 p.fst.snd ⟨p.snd, hp⟩
      rw [inner_neg_left, neg_eq_zero] at h
      rw [inner_tripleLp, hx, hz, h]
      simp
  -- relative-interior graph points over the qualifying point
  obtain ⟨g₁, hg₁, hg₁w⟩ := exists_mem_intrinsicInterior_of_mem_intrinsicInterior_image
    (WithLp.sndₗ 2 ℝ E F) hH.convex_euclideanSvGraph
    (by rwa [← svRange_eq_image_euclideanSvGraph])
  obtain ⟨g₂, hg₂, hg₂w⟩ := exists_mem_intrinsicInterior_of_mem_intrinsicInterior_image
    (WithLp.fstₗ 2 ℝ F G) hK.convex_euclideanSvGraph
    (by rwa [← svDom_eq_image_euclideanSvGraph])
  have hcl : closure C₁ ∩ closure C₂ ⊆ closure (C₁ ∩ C₂) := by
    refine closure_inter_preimage_subset A₁ (tripleMidLast (E := E))
      hH.convex_euclideanSvGraph hK.convex_euclideanSvGraph (k := WithLp.toLp 2 (g₁, g₂.snd))
      hg₁ ?_
    have he : (tripleMidLast (E := E)) (WithLp.toLp 2 (g₁, g₂.snd)) = g₂ := by
      change WithLp.toLp 2 (g₁.snd, g₂.snd) = g₂
      have h1 : g₁.snd = w := hg₁w
      have h2 : g₂.fst = w := hg₂w
      rw [h1, ← h2]
      rfl
    rw [he]
    exact hg₂
  have hpol := polarCone_inter_eq_add_of_annihilating hC₁c hC₁k hC₂c hC₂k hann hcl
  have hu₀ : WithLp.toLp 2 (WithLp.toLp 2 (v, (0 : F)), -z') ∈ polarCone (C₁ ∩ C₂) := by
    rintro p ⟨hp₁, hp₂⟩
    have h := hv p.fst.fst p.snd (mem_svComp.mpr ⟨p.fst.snd, hp₁, hp₂⟩)
    rw [real_inner_comm, inner_tripleLp_toLp]
    simp only [inner_zero_right, add_zero, inner_neg_right]
    linarith [real_inner_comm z' p.snd, real_inner_comm v p.fst.fst]
  rw [hpol] at hu₀
  obtain ⟨u₁, hu₁, u₂, hu₂, hsum⟩ := hu₀
  have hz₁ := hlast u₁ hu₁
  have hx₂ := hfirst u₂ hu₂
  have hsx : u₁.fst.fst + u₂.fst.fst = v := congrArg (fun p ↦ p.fst.fst) hsum
  have hsy : u₁.fst.snd + u₂.fst.snd = 0 := congrArg (fun p ↦ p.fst.snd) hsum
  have hsz : u₁.snd + u₂.snd = -z' := congrArg (fun p ↦ p.snd) hsum
  rw [hx₂, add_zero] at hsx
  rw [hz₁, zero_add] at hsz
  have hy₁ : u₁.fst.snd = -u₂.fst.snd := eq_neg_of_add_eq_zero_left hsy
  refine mem_svComp.mpr ⟨u₂.fst.snd, ?_, ?_⟩
  · intro y z hz
    have h := hu₂ _ ((hm₂ 0 y z).mpr hz)
    rw [inner_tripleLp_toLp, hsz, inner_neg_left] at h
    simp only [inner_zero_right, zero_add] at h
    linarith
  · intro x y hy
    have h := hu₁ _ ((hm₁ x y 0).mpr hy)
    rw [inner_tripleLp_toLp, hsx, hy₁, inner_neg_left] at h
    simp only [inner_zero_right, add_zero] at h
    linarith

/-- **Exercise 11.31(a)**, lower adjoints of a composition. -/
theorem svLowerAdjoint_svComp_of_intrinsicInterior {H : E → Set F} {K : F → Set G}
    (hH : SvSublinear H) (hK : SvSublinear K)
    (hq : (intrinsicInterior ℝ (svRange H) ∩ intrinsicInterior ℝ (svDom K)).Nonempty) :
    svLowerAdjoint (svComp K H) = svComp (svLowerAdjoint H) (svLowerAdjoint K) := by
  funext z'
  ext v
  rw [svLowerAdjoint_eq_neg_upperAdjoint, Set.mem_neg,
    svUpperAdjoint_svComp_of_intrinsicInterior hH hK hq, mem_svComp, mem_svComp]
  constructor
  · rintro ⟨y, hy, hv⟩
    refine ⟨-y, ?_, ?_⟩
    · rw [svLowerAdjoint_eq_neg_upperAdjoint, Set.mem_neg, neg_neg]
      exact hy
    · rw [svLowerAdjoint_eq_neg_upperAdjoint, Set.mem_neg, neg_neg]
      exact hv
  · rintro ⟨y, hy, hv⟩
    rw [svLowerAdjoint_eq_neg_upperAdjoint, Set.mem_neg] at hy hv
    exact ⟨-y, hy, hv⟩

/-- **Exercise 11.31(b)**, upper adjoints of a sum. -/
theorem svUpperAdjoint_svAdd_of_intrinsicInterior {H K : E → Set F}
    (hH : SvSublinear H) (hK : SvSublinear K)
    (hq : (intrinsicInterior ℝ (svDom H) ∩ intrinsicInterior ℝ (svDom K)).Nonempty) :
    svUpperAdjoint (svAdd H K) = svAdd (svUpperAdjoint H) (svUpperAdjoint K) := by
  refine le_antisymm ?_ (svAdd_upperAdjoints_subset H K)
  intro y' v hv
  obtain ⟨w, hwH, hwK⟩ := hq
  let A₁ : WithLp 2 (WithLp 2 (E × F) × F) →L[ℝ] WithLp 2 (E × F) :=
    WithLp.fstL 2 ℝ (WithLp 2 (E × F)) F
  let C₁ := A₁ ⁻¹' euclideanSvGraph H
  let C₂ := (tripleFirstLast (F := F)) ⁻¹' euclideanSvGraph K
  have hm₁ : ∀ x y z, WithLp.toLp 2 (WithLp.toLp 2 (x, y), z) ∈ C₁ ↔ y ∈ H x :=
    fun _ _ _ ↦ Iff.rfl
  have hm₂ : ∀ x y z, WithLp.toLp 2 (WithLp.toLp 2 (x, y), z) ∈ C₂ ↔ z ∈ K x :=
    fun _ _ _ ↦ Iff.rfl
  have hC₁c : Convex ℝ C₁ := hH.convex_euclideanSvGraph.linear_preimage A₁.toLinearMap
  have hC₂c : Convex ℝ C₂ :=
    hK.convex_euclideanSvGraph.linear_preimage (tripleFirstLast (F := F)).toLinearMap
  have hC₁k : IsCone C₁ := LinearMap.isCone_preimage A₁.toLinearMap hH.isCone_euclideanSvGraph
  have hC₂k : IsCone C₂ :=
    LinearMap.isCone_preimage (tripleFirstLast (F := F)).toLinearMap hK.isCone_euclideanSvGraph
  have hlast : ∀ u ∈ polarCone C₁, u.snd = 0 := by
    intro u hu
    refine eq_zero_of_forall_inner_nonpos fun z ↦ ?_
    have h := hu _ ((hm₁ 0 0 z).mpr hH.1.1)
    simpa [inner_tripleLp_toLp] using h
  have hmid : ∀ u ∈ polarCone C₂, u.fst.snd = 0 := by
    intro u hu
    refine eq_zero_of_forall_inner_nonpos fun y ↦ ?_
    have h := hu _ ((hm₂ 0 y 0).mpr hK.1.1)
    simpa [inner_tripleLp_toLp] using h
  have hann : ∀ u, u ∈ polarCone C₁ → -u ∈ polarCone C₂ → ∀ x ∈ C₁ ∪ C₂, ⟪u, x⟫_ℝ = 0 := by
    intro u hu hu'
    have hz := hlast u hu
    have hy : u.fst.snd = 0 := by simpa using hmid _ hu'
    have hDH : ∀ l ∈ svDom H, ⟪u.fst.fst, l⟫_ℝ ≤ 0 := by
      rintro l ⟨y, hl⟩
      have h := hu _ ((hm₁ l y 0).mpr hl)
      simpa [inner_tripleLp_toLp, hy] using h
    have hDK : ∀ l ∈ svDom K, ⟪-u.fst.fst, l⟫_ℝ ≤ 0 := by
      rintro l ⟨z, hl⟩
      have h := hu' _ ((hm₂ l 0 z).mpr hl)
      simpa [inner_tripleLp_toLp, hz] using h
    have hw0 : ⟪u.fst.fst, w⟫_ℝ = 0 := by
      have h1 := hDH w (intrinsicInterior_subset hwH)
      have h2 := hDK w (intrinsicInterior_subset hwK)
      rw [inner_neg_left] at h2
      linarith
    have hH0 := inner_eq_zero_of_mem_intrinsicInterior hDH hwH hw0
    have hK0 := inner_eq_zero_of_mem_intrinsicInterior hDK hwK
      (by rw [inner_neg_left, hw0, neg_zero])
    rintro p (hp | hp)
    · rw [inner_tripleLp, hy, hz, hH0 p.fst.fst ⟨p.fst.snd, hp⟩]
      simp
    · have h := hK0 p.fst.fst ⟨p.snd, hp⟩
      rw [inner_neg_left, neg_eq_zero] at h
      rw [inner_tripleLp, hy, hz, h]
      simp
  obtain ⟨g₁, hg₁, hg₁w⟩ := exists_mem_intrinsicInterior_of_mem_intrinsicInterior_image
    (WithLp.fstₗ 2 ℝ E F) hH.convex_euclideanSvGraph
    (by rwa [← svDom_eq_image_euclideanSvGraph])
  obtain ⟨g₂, hg₂, hg₂w⟩ := exists_mem_intrinsicInterior_of_mem_intrinsicInterior_image
    (WithLp.fstₗ 2 ℝ E F) hK.convex_euclideanSvGraph
    (by rwa [← svDom_eq_image_euclideanSvGraph])
  have hcl : closure C₁ ∩ closure C₂ ⊆ closure (C₁ ∩ C₂) := by
    refine closure_inter_preimage_subset A₁ (tripleFirstLast (F := F))
      hH.convex_euclideanSvGraph hK.convex_euclideanSvGraph (k := WithLp.toLp 2 (g₁, g₂.snd))
      hg₁ ?_
    have he : (tripleFirstLast (F := F)) (WithLp.toLp 2 (g₁, g₂.snd)) = g₂ := by
      change WithLp.toLp 2 (g₁.fst, g₂.snd) = g₂
      have h1 : g₁.fst = w := hg₁w
      have h2 : g₂.fst = w := hg₂w
      rw [h1, ← h2]
      rfl
    rw [he]
    exact hg₂
  have hpol := polarCone_inter_eq_add_of_annihilating hC₁c hC₁k hC₂c hC₂k hann hcl
  have hu₀ : WithLp.toLp 2 (WithLp.toLp 2 (v, -y'), -y') ∈ polarCone (C₁ ∩ C₂) := by
    rintro p ⟨hp₁, hp₂⟩
    have h := hv p.fst.fst (p.fst.snd + p.snd) (mem_svAdd.mpr ⟨_, hp₁, _, hp₂, rfl⟩)
    rw [real_inner_comm, inner_tripleLp_toLp]
    simp only [inner_neg_right]
    rw [inner_add_right] at h
    linarith [real_inner_comm y' p.fst.snd, real_inner_comm y' p.snd, real_inner_comm v p.fst.fst]
  rw [hpol] at hu₀
  obtain ⟨u₁, hu₁, u₂, hu₂, hsum⟩ := hu₀
  have hz₁ := hlast u₁ hu₁
  have hy₂ := hmid u₂ hu₂
  have hsx : u₁.fst.fst + u₂.fst.fst = v := congrArg (fun p ↦ p.fst.fst) hsum
  have hsy : u₁.fst.snd + u₂.fst.snd = -y' := congrArg (fun p ↦ p.fst.snd) hsum
  have hsz : u₁.snd + u₂.snd = -y' := congrArg (fun p ↦ p.snd) hsum
  rw [hy₂, add_zero] at hsy
  rw [hz₁, zero_add] at hsz
  refine mem_svAdd.mpr ⟨u₁.fst.fst, ?_, u₂.fst.fst, ?_, hsx⟩
  · intro x y hy
    have h := hu₁ _ ((hm₁ x y 0).mpr hy)
    rw [inner_tripleLp_toLp, hsy, inner_neg_left] at h
    simp only [inner_zero_right, add_zero] at h
    linarith
  · intro x z hz
    have h := hu₂ _ ((hm₂ x 0 z).mpr hz)
    rw [inner_tripleLp_toLp, hsz, inner_neg_left] at h
    simp only [inner_zero_right, add_zero] at h
    linarith

/-- **Exercise 11.31(b)**, lower adjoints of a sum. -/
theorem svLowerAdjoint_svAdd_of_intrinsicInterior {H K : E → Set F}
    (hH : SvSublinear H) (hK : SvSublinear K)
    (hq : (intrinsicInterior ℝ (svDom H) ∩ intrinsicInterior ℝ (svDom K)).Nonempty) :
    svLowerAdjoint (svAdd H K) = svAdd (svLowerAdjoint H) (svLowerAdjoint K) := by
  funext y
  ext v
  rw [svLowerAdjoint_eq_neg_upperAdjoint, Set.mem_neg,
    svUpperAdjoint_svAdd_of_intrinsicInterior hH hK hq, mem_svAdd, mem_svAdd]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨-a, ?_, -b, ?_, ?_⟩
    · rw [svLowerAdjoint_eq_neg_upperAdjoint, Set.mem_neg, neg_neg]
      exact ha
    · rw [svLowerAdjoint_eq_neg_upperAdjoint, Set.mem_neg, neg_neg]
      exact hb
    · rw [← neg_add, hab, neg_neg]
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [svLowerAdjoint_eq_neg_upperAdjoint, Set.mem_neg] at ha hb
    exact ⟨-a, ha, -b, hb, by rw [neg_add]⟩

/-- **Exercise 11.31**, all three adjoint rules: composition and addition under
their relative-interior qualifications, and positive scalar multiples. -/
theorem sublinearAdjoint_calculus :
    (∀ (H : E → Set F) (K : F → Set G), SvSublinear H → SvSublinear K →
      (intrinsicInterior ℝ (svRange H) ∩ intrinsicInterior ℝ (svDom K)).Nonempty →
        svUpperAdjoint (svComp K H) = svComp (svUpperAdjoint H) (svUpperAdjoint K) ∧
        svLowerAdjoint (svComp K H) = svComp (svLowerAdjoint H) (svLowerAdjoint K)) ∧
    (∀ H K : E → Set F, SvSublinear H → SvSublinear K →
      (intrinsicInterior ℝ (svDom H) ∩ intrinsicInterior ℝ (svDom K)).Nonempty →
        svUpperAdjoint (svAdd H K) = svAdd (svUpperAdjoint H) (svUpperAdjoint K) ∧
        svLowerAdjoint (svAdd H K) = svAdd (svLowerAdjoint H) (svLowerAdjoint K)) ∧
    (∀ (H : E → Set F) (c : ℝ), 0 < c →
      svUpperAdjoint (fun w ↦ c • H w) = (fun y ↦ c • svUpperAdjoint H y) ∧
      svLowerAdjoint (fun w ↦ c • H w) = (fun y ↦ c • svLowerAdjoint H y)) :=
  ⟨fun _ _ hH hK hq ↦ ⟨svUpperAdjoint_svComp_of_intrinsicInterior hH hK hq,
      svLowerAdjoint_svComp_of_intrinsicInterior hH hK hq⟩,
    fun _ _ hH hK hq ↦ ⟨svUpperAdjoint_svAdd_of_intrinsicInterior hH hK hq,
      svLowerAdjoint_svAdd_of_intrinsicInterior hH hK hq⟩,
    fun H _ hc ↦ ⟨svUpperAdjoint_smul H hc, svLowerAdjoint_smul H hc⟩⟩

end Calculus

end RW
