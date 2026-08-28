/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Images of Converging Sets

Exercise 5.30 pushes a sequence of sets `Cν` forward through a set-valued
mapping `S` and asks when `S(Cν) → S(C)`.  The book's Guide says to extend
the argument for 4.26 using ideas from 5.26; both are used here, but through
a single identity rather than by repeating either proof.

That identity is `S(C) = π₂((gph S) ∩ π₁⁻¹(C))`, the same device by which
5.26 read `S⁻¹(D)` as a projection.  It turns the set-valued image into an
ordinary continuous image of a varying set, so Theorem 4.26 applies verbatim
with `G = π₂` and the sets `(gph S) ∩ π₁⁻¹(Cν)`.  The two inclusions

    lim sup ((gph S) ∩ π₁⁻¹(Cν)) ⊂ gph S,
    lim sup ((gph S) ∩ π₁⁻¹(Cν)) ⊂ π₁⁻¹(lim sup Cν)

are pure monotonicity -- outer limits do not distribute over intersections,
but they do respect inclusion -- and outer semicontinuity of `S` enters only
through `lim sup (gph S) = cl(gph S) = gph S`.

What remains is 4.26's escape condition for `π₂`: a selection of graph points
whose values converge must have bounded arguments.  Each of the book's two
alternatives supplies it.  Local boundedness of `S⁻¹` gives it immediately by
5.15, with no extraction at all, since the arguments lie in `S⁻¹(B)` for a
bounded `B` holding the values.  The horizon alternative is where the
extraction happens: escaping arguments yield a unit direction `w` in
`lim sup∞ Cν`, and rescaling the graph points sends the values to `0`, so
`0 ∈ S∞(w)` and the hypothesis `(S∞)⁻¹(0) ∩ lim sup∞ Cν = {0}` is violated.

Clause (a) is proved directly and is unrelated to all of this: inner limits do
not survive the intersection with `gph S`, but the inner-semicontinuity
argument is two neighborhoods deep and needs no structure on the spaces.

Clause (d) is 4.24 applied to clause (c): the remaining horizon inclusion
`lim sup∞ S(Cν) ⊂ S∞(C∞) ⊂ S(C)∞` is proved by the double rescaling of 4.27.
It uses **no semicontinuity of `S` whatsoever**, so the printed hypothesis of
total continuity is stronger than needed; the theorem is stated under
continuity, with the printed form kept as a corollary.
-/

import RockafellarWets.Chapter4.ImageLimits
import RockafellarWets.Chapter4.TotalLinearImages
import RockafellarWets.Chapter5.HorizonImages
import RockafellarWets.Chapter5.TotalContinuity

open Bornology Filter Metric Set Topology

namespace RW

section InnerLimit

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Exercise 5.30(a)**, in the sharper pointwise form: inner semicontinuity
is only needed at the points of `lim inf Cν`.

The proof is two neighborhoods deep.  Given `u ∈ S(x)` with `x` in the inner
limit and a neighborhood `W` of `u`, inner semicontinuity at `x` makes
`{y | S(y) ∩ W ≠ ∅}` a neighborhood `V` of `x`, and `x ∈ lim inf Cν` makes
`Cν` meet `V` eventually; any hit lies in `Cν` and has a value in `W`. -/
theorem svImage_innerSetLimit_subset {S : E → Set F} {C : ℕ → Set E}
    (hisc : ∀ x ∈ innerSetLimit C, SvIscAt S x) :
    svImage S (innerSetLimit C) ⊆ innerSetLimit (fun n ↦ svImage S (C n)) := by
  intro u hu
  obtain ⟨x, hxC, hux⟩ := mem_svImage.1 hu
  intro W hW
  have hV : ∀ᶠ y in nhds x, (S y ∩ W).Nonempty := hisc x hxC hux W hW
  filter_upwards [hxC _ hV] with n hn
  obtain ⟨y, hyC, v, hvS, hvW⟩ := hn
  exact ⟨v, subset_svImage hyC hvS, hvW⟩

/-- **Exercise 5.30(a)**: an inner semicontinuous mapping carries the inner
limit into the inner limit of the images. -/
theorem SvIsc.svImage_innerSetLimit_subset {S : E → Set F} (hisc : SvIsc S)
    (C : ℕ → Set E) :
    svImage S (innerSetLimit C) ⊆ innerSetLimit (fun n ↦ svImage S (C n)) :=
  _root_.RW.svImage_innerSetLimit_subset fun x _ ↦ hisc x

end InnerLimit

section GraphSlices

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

omit [TopologicalSpace E] [TopologicalSpace F] in
/-- The image `S(C)` is the second projection of the part of `gph S` lying
over `C`.  This is the identity that turns 5.30 into an instance of 4.26. -/
theorem svImage_eq_image_snd (S : E → Set F) (C : Set E) :
    svImage S C = Prod.snd '' (svGraph S ∩ Prod.fst ⁻¹' C) := by
  ext u
  simp only [mem_svImage, mem_image, mem_inter_iff, mem_svGraph, mem_preimage,
    Prod.exists]
  constructor
  · rintro ⟨x, hxC, hux⟩
    exact ⟨x, u, ⟨hux, hxC⟩, rfl⟩
  · rintro ⟨x, v, ⟨hv, hxC⟩, rfl⟩
    exact ⟨x, hxC, hv⟩

/-- Outer limits commute with continuous preimages in the easy direction. -/
theorem outerSetLimit_preimage_subset {P Q : Type*} [TopologicalSpace P]
    [TopologicalSpace Q] {G : P → Q} (hG : Continuous G) (C : ℕ → Set Q) :
    outerSetLimit (fun n ↦ G ⁻¹' C n) ⊆ G ⁻¹' outerSetLimit C := by
  intro p hp W hW
  refine (hp (G ⁻¹' W) (hG.continuousAt hW)).mono ?_
  rintro n ⟨q, hqC, hqW⟩
  exact ⟨G q, hqC, hqW⟩

/-- The outer limit of the graph slices stays inside the graph slice over the
outer limit.  Both halves are monotonicity: the graph is a fixed closed set,
and the cylinder is a continuous preimage. -/
theorem outerSetLimit_graphSlice_subset {S : E → Set F} (C : ℕ → Set E)
    (hS : IsClosed (svGraph S)) :
    outerSetLimit (fun n ↦ svGraph S ∩ Prod.fst ⁻¹' C n) ⊆
      svGraph S ∩ Prod.fst ⁻¹' outerSetLimit C := by
  refine subset_inter ?_ ?_
  · have h1 : outerSetLimit (fun n ↦ svGraph S ∩ Prod.fst ⁻¹' C n) ⊆
        outerSetLimit (fun _ : ℕ ↦ svGraph S) :=
      outerSetLimit_mono fun _ ↦ inter_subset_left
    rwa [outerSetLimit_const, hS.closure_eq] at h1
  · exact (outerSetLimit_mono fun n ↦ inter_subset_right).trans
      (outerSetLimit_preimage_subset continuous_fst C)

end GraphSlices

section NoEscape

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {S : E → Set F} {C : ℕ → Set E}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in
/-- A selection of graph points is bounded as soon as both of its coordinate
sequences are. -/
private theorem isBounded_range_of_isBounded_proj {p : ℕ → E × F}
    (hfst : IsBounded (Set.range (Prod.fst ∘ p)))
    (hsnd : IsBounded (Set.range (Prod.snd ∘ p))) :
    IsBounded (Set.range p) := by
  refine (hfst.prod hsnd).subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨⟨n, rfl⟩, ⟨n, rfl⟩⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The first alternative in **Exercise 5.30(b)**: local boundedness of `S⁻¹`
keeps the arguments of a convergent selection of values in a bounded set.
This is 5.15 applied to `S⁻¹`, with no extraction at all. -/
theorem noConvergentImageEscapeAlong_snd_of_svLocallyBounded_svInv
    (S : E → Set F) (C : ℕ → Set E) (hlb : SvLocallyBounded (svInv S)) :
    NoConvergentImageEscapeAlong (Prod.snd : E × F → F)
      (fun n ↦ svGraph S ∩ Prod.fst ⁻¹' C n) := by
  intro _ p u _ hpG hpu
  have hsnd : IsBounded (Set.range (Prod.snd ∘ p)) :=
    Metric.isBounded_range_of_tendsto _ hpu
  refine isBounded_range_of_isBounded_proj ?_ hsnd
  refine (svLocallyBounded_iff_isBounded_svImage.1 hlb _ hsnd).subset ?_
  rintro _ ⟨n, rfl⟩
  exact mem_svImage.2 ⟨(p n).2, ⟨n, rfl⟩, (hpG n).1⟩

omit [FiniteDimensional ℝ F] in
/-- The second alternative in **Exercise 5.30(b)**: if the arguments escaped,
they would produce a unit horizon direction `w` of the sets `Cν` over which
`S∞` still reaches `0`, since the values stay put. -/
theorem noConvergentImageEscapeAlong_snd_of_svHorizon
    (h : svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E)) :
    NoConvergentImageEscapeAlong (Prod.snd : E × F → F)
      (fun n ↦ svGraph S ∩ Prod.fst ⁻¹' C n) := by
  intro φ p u hφ hpG hpu
  have hsnd : IsBounded (Set.range (Prod.snd ∘ p)) :=
    Metric.isBounded_range_of_tendsto _ hpu
  by_contra hbdd
  have hfst : ¬ IsBounded (Set.range (Prod.fst ∘ p)) := fun hf ↦
    hbdd (isBounded_range_of_isBounded_proj hf hsnd)
  obtain ⟨w, ψ, hψ, hwdir⟩ :=
    exists_cosmicDirection_subsequence_of_not_isBounded hfst
  -- The escaping arguments give a horizon direction of the sets `Cν`.
  have hwC : (w : E) ∈ horizonOuterSetLimit C :=
    mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.2
      ⟨φ ∘ ψ, fun n ↦ (p (ψ n)).1, hφ.comp hψ, fun n ↦ (hpG (ψ n)).2, hwdir⟩
  -- Rescaling the graph points sends the values to `0`, so `0 ∈ S∞(w)`.
  obtain ⟨a, hapos, hazero, hax⟩ := exists_scaling_of_tendsto_cosmicDirection hwdir
  have hay : Tendsto (fun n ↦ a n • (p (ψ n)).2) atTop (nhds 0) := by
    simpa using hazero.smul (hpu.comp hψ.tendsto_atTop)
  have hap : Tendsto (fun n ↦ a n • p (ψ n)) atTop (nhds ((w : E), (0 : F))) :=
    hax.prodMk_nhds hay
  have hatop : Tendsto (fun n ↦ (a n)⁻¹) atTop atTop :=
    Filter.Tendsto.inv_tendsto_nhdsGT_zero
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within a hazero
        (Eventually.of_forall hapos))
  have hgraph : ((w : E), (0 : F)) ∈ horizonCone (svGraph S) :=
    Set.mem_insert_of_mem 0 <| mem_asymptoticCone_of_seq_smul hatop hap
      fun n ↦ by
        rw [inv_smul_smul₀ (hapos n).ne']
        exact (hpG (ψ n)).1
  have hwzero : (w : E) ∈ ({0} : Set E) := by
    rw [← h]
    exact ⟨mem_svHorizon.2 hgraph, hwC⟩
  have hwnorm : ‖(w : E)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  rw [mem_singleton_iff] at hwzero
  simp [hwzero] at hwnorm

end NoEscape

section OuterLimit

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {S : E → Set F} {C : ℕ → Set E}

/-- **Exercise 5.30(b)**, stated against the sequential no-escape condition
of 4.26 for the projection `(x, u) → u`. -/
theorem outerSetLimit_svImage_subset (hosc : SvOsc S)
    (hesc : NoConvergentImageEscapeAlong (Prod.snd : E × F → F)
      (fun n ↦ svGraph S ∩ Prod.fst ⁻¹' C n)) :
    outerSetLimit (fun n ↦ svImage S (C n)) ⊆ svImage S (outerSetLimit C) := by
  have hrew : (fun n ↦ svImage S (C n)) =
      fun n ↦ Prod.snd '' (svGraph S ∩ Prod.fst ⁻¹' C n) :=
    funext fun n ↦ svImage_eq_image_snd S (C n)
  rw [hrew, outerSetLimit_image_eq_image_outerSetLimit continuous_snd hesc,
    svImage_eq_image_snd S (outerSetLimit C)]
  exact image_mono
    (outerSetLimit_graphSlice_subset C (isClosed_svGraph_iff_svOsc.2 hosc))

/-- **Exercise 5.30(b)**, first alternative: `S⁻¹` locally bounded. -/
theorem SvOsc.outerSetLimit_svImage_subset_of_svLocallyBounded_svInv
    (hosc : SvOsc S) (hlb : SvLocallyBounded (svInv S)) (C : ℕ → Set E) :
    outerSetLimit (fun n ↦ svImage S (C n)) ⊆ svImage S (outerSetLimit C) :=
  outerSetLimit_svImage_subset hosc
    (noConvergentImageEscapeAlong_snd_of_svLocallyBounded_svInv S C hlb)

/-- **Exercise 5.30(b)**, second alternative: `(S∞)⁻¹(0) ∩ limsup∞ Cν = {0}`. -/
theorem SvOsc.outerSetLimit_svImage_subset_of_svHorizon (hosc : SvOsc S)
    (h : svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E)) :
    outerSetLimit (fun n ↦ svImage S (C n)) ⊆ svImage S (outerSetLimit C) :=
  outerSetLimit_svImage_subset hosc
    (noConvergentImageEscapeAlong_snd_of_svHorizon h)

end OuterLimit

section Convergence

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {S : E → Set F} {C : ℕ → Set E} {D : Set E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The two inclusions of 5.30(a) and 5.30(b) already pin the limit down:
`S(D)` is squeezed between the inner and the outer limit. -/
theorem pkConverges_svImage_of_subset_of_subset
    (hinner : svImage S D ⊆ innerSetLimit (fun n ↦ svImage S (C n)))
    (houter : outerSetLimit (fun n ↦ svImage S (C n)) ⊆ svImage S D) :
    PKConverges (fun n ↦ svImage S (C n)) (svImage S D) :=
  ⟨Subset.antisymm ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner,
    Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit _))⟩

/-- **Exercise 5.30(c)**, stated against the no-escape condition. -/
theorem PKConverges.svImage_of_noEscape (hC : PKConverges C D)
    (hcont : SvContinuous S)
    (hesc : NoConvergentImageEscapeAlong (Prod.snd : E × F → F)
      (fun n ↦ svGraph S ∩ Prod.fst ⁻¹' C n)) :
    PKConverges (fun n ↦ svImage S (C n)) (svImage S D) := by
  refine pkConverges_svImage_of_subset_of_subset ?_ ?_
  · rw [← hC.inner_eq]
    exact SvIsc.svImage_innerSetLimit_subset (fun x ↦ (hcont x).2) C
  · rw [← hC.outer_eq]
    exact outerSetLimit_svImage_subset (fun x ↦ (hcont x).1) hesc

/-- **Exercise 5.30(c)**, first alternative: `S⁻¹` locally bounded. -/
theorem PKConverges.svImage_of_svLocallyBounded_svInv (hC : PKConverges C D)
    (hcont : SvContinuous S) (hlb : SvLocallyBounded (svInv S)) :
    PKConverges (fun n ↦ svImage S (C n)) (svImage S D) :=
  hC.svImage_of_noEscape hcont
    (noConvergentImageEscapeAlong_snd_of_svLocallyBounded_svInv S C hlb)

omit [FiniteDimensional ℝ F] in
/-- Under total convergence the horizon condition of the limit set implies
the one along the sequence, by 4.24. -/
theorem svHorizon_inter_horizonOuterSetLimit_eq
    (hC : TotalConverges C D)
    (h : svInv (svHorizon S) 0 ∩ horizonCone D = ({0} : Set E)) :
    svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E) := by
  refine Subset.antisymm (fun w hw ↦ ?_) ?_
  · rw [← h]
    exact ⟨hw.1, hC.horizonOuter_subset hw.2⟩
  · rw [singleton_subset_iff]
    exact ⟨mem_svHorizon.2 (zero_mem_horizonCone _),
      (isCone_horizonOuterSetLimit C).1⟩

/-- **Exercise 5.30(c)**, second alternative: `Cν →ᵗ C` together with
`(S∞)⁻¹(0) ∩ C∞ = {0}`. -/
theorem TotalConverges.pkConverges_svImage (hC : TotalConverges C D)
    (hcont : SvContinuous S)
    (h : svInv (svHorizon S) 0 ∩ horizonCone D = ({0} : Set E)) :
    PKConverges (fun n ↦ svImage S (C n)) (svImage S D) :=
  hC.pkConverges.svImage_of_noEscape hcont (noConvergentImageEscapeAlong_snd_of_svHorizon
    (svHorizon_inter_horizonOuterSetLimit_eq hC h))

end Convergence

section TotalConvergence

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {S : E → Set F} {C : ℕ → Set E} {D : Set E}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- `S∞` carries cones to cones, since `gph S∞` is one. -/
theorem isCone_svImage_svHorizon (S : E → Set F) {K : Set E} (hK : IsCone K) :
    IsCone (svImage (svHorizon S) K) := by
  refine ⟨mem_svImage.2 ⟨0, hK.1, zero_mem_svHorizon_zero S⟩, ?_⟩
  rintro w hw c hc
  obtain ⟨q, hqK, hwq⟩ := mem_svImage.1 hw
  refine mem_svImage.2 ⟨c • q, hK.smul_mem hqK hc.le, mem_svHorizon.2 ?_⟩
  simpa only [Prod.smul_mk] using
    (isCone_horizonCone (svGraph S)).smul_mem (mem_svHorizon.1 hwq) hc.le

omit [FiniteDimensional ℝ F] in
/-- The engine of 5.30(d): rescaled arguments cannot escape when the rescaled
values stay bounded.  An escaping direction would be a horizon direction of
the sets `Cν` over which `S∞` reaches `0`. -/
private theorem isBounded_scaled_selection
    (h : svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E))
    {φ : ℕ → ℕ} {x : ℕ → E} {y : ℕ → F} {a : ℕ → ℝ}
    (hφ : StrictMono φ) (hxC : ∀ n, x n ∈ C (φ n)) (hxy : ∀ n, y n ∈ S (x n))
    (hapos : ∀ n, 0 < a n) (hazero : Tendsto a atTop (nhds 0))
    (hay : IsBounded (Set.range fun n ↦ a n • y n)) :
    IsBounded (Set.range fun n ↦ a n • x n) := by
  by_contra hnot
  obtain ⟨v, ψ, hψ, hvdir⟩ :=
    exists_cosmicDirection_subsequence_of_not_isBounded hnot
  obtain ⟨b, hbpos, hbzero, hbv⟩ := exists_scaling_of_tendsto_cosmicDirection hvdir
  have hcpos : ∀ n, 0 < b n * a (ψ n) := fun n ↦ mul_pos (hbpos n) (hapos (ψ n))
  have haψ : Tendsto (fun n ↦ a (ψ n)) atTop (nhds 0) := hazero.comp hψ.tendsto_atTop
  have hczero : Tendsto (fun n ↦ b n * a (ψ n)) atTop (nhds 0) := by
    simpa only [mul_zero] using hbzero.mul haψ
  have hcx : Tendsto (fun n ↦ (b n * a (ψ n)) • x (ψ n)) atTop (nhds (v : E)) := by
    simpa only [mul_smul] using hbv
  have hvC : (v : E) ∈ horizonOuterSetLimit C :=
    mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.2
      ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ, fun n ↦ hxC (ψ n),
        tendsto_cosmicDirection_of_scaling hcpos hczero hcx⟩
  -- The values were already rescaled to a bounded sequence, so the extra
  -- factor `b n → 0` drives them to the origin.
  obtain ⟨R, hR⟩ := hay.exists_norm_le
  have hbound : Tendsto (fun n ↦ |b n| * max R 0) atTop (nhds 0) := by
    simpa only [abs_zero, zero_mul] using hbzero.abs.mul_const (max R 0)
  have hcy : Tendsto (fun n ↦ (b n * a (ψ n)) • y (ψ n)) atTop (nhds 0) :=
    squeeze_zero_norm (fun n ↦ by
      rw [mul_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        ((hR _ ⟨ψ n, rfl⟩).trans (le_max_left _ _)) (abs_nonneg _)) hbound
  have hctop : Tendsto (fun n ↦ (b n * a (ψ n))⁻¹) atTop atTop :=
    Filter.Tendsto.inv_tendsto_nhdsGT_zero
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hczero
        (Eventually.of_forall hcpos))
  have hgraph : ((v : E), (0 : F)) ∈ horizonCone (svGraph S) :=
    Set.mem_insert_of_mem 0 <| mem_asymptoticCone_of_seq_smul hctop
      (hcx.prodMk_nhds hcy) fun n ↦ by
        rw [Prod.smul_mk, inv_smul_smul₀ (hcpos n).ne',
          inv_smul_smul₀ (hcpos n).ne']
        exact hxy (ψ n)
  have hvzero : (v : E) ∈ ({0} : Set E) := by
    rw [← h]
    exact ⟨mem_svHorizon.2 hgraph, hvC⟩
  have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  rw [mem_singleton_iff] at hvzero
  simp [hvzero] at hvnorm

omit [FiniteDimensional ℝ F] in
/-- **Exercise 5.30(d)**, horizon half: every horizon direction of the images
comes from a horizon direction of `S` over a horizon direction of the limit
set.  Nothing here needs semicontinuity of `S`. -/
theorem horizonOuterSetLimit_svImage_subset (hC : TotalConverges C D)
    (h : svInv (svHorizon S) 0 ∩ horizonCone D = ({0} : Set E)) :
    horizonOuterSetLimit (fun n ↦ svImage S (C n)) ⊆
      svImage (svHorizon S) (horizonCone D) := by
  have hseq : svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E) :=
    svHorizon_inter_horizonOuterSetLimit_eq hC h
  intro w hw
  rcases hw with rfl | ⟨u, huOuter, r, hr, rfl⟩
  · exact mem_svImage.2 ⟨0, zero_mem_horizonCone D, zero_mem_svHorizon_zero S⟩
  obtain ⟨φ, y, hφ, hyImage, hydir⟩ :=
    mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.1
      (cosmicDirection_mem_outer_ordinaryCosmicSequence_iff.1 huOuter)
  choose x hxC hxy using fun n ↦ mem_svImage.1 (hyImage n)
  obtain ⟨a, hapos, hazero, hay⟩ := exists_scaling_of_tendsto_cosmicDirection hydir
  have haybdd : IsBounded (Set.range fun n ↦ a n • y n) :=
    Metric.isBounded_range_of_tendsto _ hay
  obtain ⟨q, -, ψ, hψ, hq⟩ :=
    tendsto_subseq_of_bounded
      (isBounded_scaled_selection hseq hφ hxC hxy hapos hazero haybdd)
      (fun n ↦ Set.mem_range_self n)
  have hqx : Tendsto (fun n ↦ a (ψ n) • x (ψ n)) atTop (nhds q) := hq
  have hqy : Tendsto (fun n ↦ a (ψ n) • y (ψ n)) atTop (nhds (u : F)) :=
    hay.comp hψ.tendsto_atTop
  -- The rescaled graph points converge to `(q, u)`, a horizon direction.
  have hatop : Tendsto (fun n ↦ (a (ψ n))⁻¹) atTop atTop :=
    Filter.Tendsto.inv_tendsto_nhdsGT_zero
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hazero.comp hψ.tendsto_atTop) (Eventually.of_forall fun n ↦ hapos (ψ n)))
  have hgraph : (q, (u : F)) ∈ horizonCone (svGraph S) :=
    Set.mem_insert_of_mem 0 <| mem_asymptoticCone_of_seq_smul hatop
      (hqx.prodMk_nhds hqy) fun n ↦ by
        rw [Prod.smul_mk, inv_smul_smul₀ (hapos (ψ n)).ne',
          inv_smul_smul₀ (hapos (ψ n)).ne']
        exact hxy (ψ n)
  -- Its first coordinate is a horizon direction of the limit set.
  have hqD : q ∈ horizonCone D := by
    by_cases hq0 : q = 0
    · rw [hq0]
      exact zero_mem_horizonCone D
    have hqnorm : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
    have hscalepos : ∀ n, 0 < ‖q‖⁻¹ * a (ψ n) := fun n ↦
      mul_pos (inv_pos.mpr hqnorm) (hapos (ψ n))
    have hscalezero : Tendsto (fun n ↦ ‖q‖⁻¹ * a (ψ n)) atTop (nhds 0) := by
      simpa only [mul_zero] using
        tendsto_const_nhds.mul (hazero.comp hψ.tendsto_atTop)
    have hscaled : Tendsto (fun n ↦ (‖q‖⁻¹ * a (ψ n)) • x (ψ n)) atTop
        (nhds ((cosmicDirectionOf q hq0 : CosmicBoundary E) : E)) := by
      simpa only [mul_smul, coe_cosmicDirectionOf, NormedSpace.normalize] using
        tendsto_const_nhds.smul hqx
    have hvOuter : ((cosmicDirectionOf q hq0 : CosmicBoundary E) : E) ∈
        horizonOuterSetLimit C :=
      mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.2
        ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ, fun n ↦ hxC (ψ n),
          tendsto_cosmicDirection_of_scaling hscalepos hscalezero hscaled⟩
    have hscaledMem := (isCone_horizonCone D).smul_mem
      (hC.horizonOuter_subset hvOuter) (norm_nonneg q)
    simpa only [coe_cosmicDirectionOf, NormedSpace.norm_smul_normalize q] using
      hscaledMem
  exact (isCone_svImage_svHorizon S (isCone_horizonCone D)).smul_mem
    (mem_svImage.2 ⟨q, hqD, mem_svHorizon.2 hgraph⟩) hr.le

/-- **Exercise 5.30(d)**.  Total convergence of the images, under the book's
three hypotheses on `Cν`, on `(S∞)⁻¹(0)` and on `S∞(C∞)`.

Only continuity of `S` is used, not total continuity: the horizon half is
carried entirely by the hypotheses on `S∞`, which say nothing about limits of
`S(x)`. -/
theorem TotalConverges.svImage_of_svHorizon (hC : TotalConverges C D)
    (hcont : SvContinuous S)
    (h : svInv (svHorizon S) 0 ∩ horizonCone D = ({0} : Set E))
    (himg : svImage (svHorizon S) (horizonCone D) ⊆ horizonCone (svImage S D)) :
    TotalConverges (fun n ↦ svImage S (C n)) (svImage S D) :=
  totalConverges_iff_pkConverges_and_horizonOuter_subset.2
    ⟨hC.pkConverges_svImage hcont h,
      (horizonOuterSetLimit_svImage_subset hC h).trans himg⟩

/-- **Exercise 5.30(d)** as printed, under total continuity of `S`. -/
theorem TotalConverges.svImage_of_svTotallyContinuous (hC : TotalConverges C D)
    (hcont : SvTotallyContinuous S)
    (h : svInv (svHorizon S) 0 ∩ horizonCone D = ({0} : Set E))
    (himg : svImage (svHorizon S) (horizonCone D) ⊆ horizonCone (svImage S D)) :
    TotalConverges (fun n ↦ svImage S (C n)) (svImage S D) :=
  hC.svImage_of_svHorizon (fun x ↦ (svTotallyContinuousAt_iff.1 (hcont x)).1) h himg

end TotalConvergence

end RW
