/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Images of Converging Mappings

Theorem 5.53, together with the total graph convergence and formula 5(14)
that the book introduces just before it.

Total graph convergence is set convergence of the graphs in the sense of 4.23,
so 5(14) -- that it is graphical convergence together with
`lim sup∞ gph Sν ⊂ gph S∞` -- is 4.24 read through `gph S∞ = (gph S)∞`, with
nothing to prove.

The three inclusions are the moving-mapping counterparts of 5.30(a), (b) and
(d), and they are proved the same way, with `gph Sν` in place of a fixed
`gph S` at exactly one step each: where 5.30 concludes that a limit of graph
points lies in `gph S` because that set is closed, here it lies in
`lim sup gph Sν`, which graphical convergence identifies with `gph S`; and
where 5.30 produces a horizon direction of `gph S`, here it produces one of
`lim sup∞ gph Sν`, which the second half of 5(14) sends into `gph S∞`.
-/

import RockafellarWets.Chapter4.TotalConvergenceAutomatic
import RockafellarWets.Chapter5.ContinuousUniformConvergence
import RockafellarWets.Chapter5.GraphicalLimits
import RockafellarWets.Chapter5.ImageConvergence

open Bornology Filter Metric Set Topology

namespace RW

section Definition

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F}

/-- The paragraph before 5.53: `Sν` converges *totally* to `S` when the graphs
converge totally in the sense of 4.23. -/
def TotalGraphicalConverges (Sseq : ℕ → E → Set F) (S : E → Set F) : Prop :=
  TotalConverges (fun n ↦ svGraph (Sseq n)) (svGraph S)

/-- **Formula 5(14)**: total graph convergence is graphical convergence
together with the horizon inclusion, by 4.24 and `gph S∞ = (gph S)∞`. -/
theorem totalGraphicalConverges_iff :
    TotalGraphicalConverges Sseq S ↔
      GraphicalConverges Sseq S ∧
        horizonOuterSetLimit (fun n ↦ svGraph (Sseq n)) ⊆
          svGraph (svHorizon S) :=
  totalConverges_iff_pkConverges_and_horizonOuter_subset

theorem TotalGraphicalConverges.graphicalConverges
    (h : TotalGraphicalConverges Sseq S) : GraphicalConverges Sseq S :=
  (totalGraphicalConverges_iff.1 h).1

theorem TotalGraphicalConverges.horizonOuter_subset
    (h : TotalGraphicalConverges Sseq S) :
    horizonOuterSetLimit (fun n ↦ svGraph (Sseq n)) ⊆ svGraph (svHorizon S) :=
  (totalGraphicalConverges_iff.1 h).2

end Definition

section Inner

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {C : ℕ → Set E} {D : Set E}

omit [NormedSpace ℝ E] in
/-- **Theorem 5.53(a)**: continuous convergence carries the inner limit of the
argument sets into the inner limit of the images.  Only the `ε`-`ρ` form of
continuous convergence is used, so no sequence of arguments has to be built by
a diagonal choice: a neighborhood of `x̄` is met by `Cν` eventually, and that
is exactly the quantifier the inclusions of 5.41 consume. -/
theorem svImage_subset_innerSetLimit_svImage
    (hcont : SvConvergesContinuously Sseq S) (hD : D ⊆ innerSetLimit C) :
    svImage S D ⊆ innerSetLimit (fun n ↦ svImage (Sseq n) (C n)) := by
  rintro u hu
  obtain ⟨x, hxD, hux⟩ := mem_svImage.1 hu
  have hclosed : IsClosed (S x) :=
    (hcont x (fun _ ↦ x) (fun _ ↦ mem_univ _) tendsto_const_nhds).isClosed
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨W, hW, hn⟩ := (svConvergesContinuouslyAt_iff hclosed).1 (hcont x)
    ε hε (‖u‖ + 1) (by positivity)
  filter_upwards [hn, hD hxD W hW] with n hn' hCn
  obtain ⟨z, hzC, hzW⟩ := hCn
  have huball : u ∈ S x ∩ closedBall 0 (‖u‖ + 1) := by
    refine ⟨hux, ?_⟩
    simp only [mem_closedBall, dist_zero_right]
    linarith
  obtain ⟨w, hw, hd⟩ := Metric.mem_thickening_iff.1 ((hn' z hzW).2 huball)
  exact ⟨w, mem_svImage.2 ⟨z, hzC, hw⟩, hball (by rwa [mem_ball, dist_comm])⟩

end Inner

section HorizonExtraction

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G]

omit [FiniteDimensional ℝ G] in
/-- The moving-set counterpart of `mem_asymptoticCone_of_seq_smul`: a limit of
rescaled points drawn from a subsequence of the family is a horizon direction
of the family.  Normalizing once here is what keeps 5.53(b) and (c) from
repeating the `cosmicDirectionOf` bookkeeping. -/
theorem mem_horizonOuterSetLimit_of_seq_smul {C : ℕ → Set G} {φ : ℕ → ℕ}
    {p : ℕ → G} {a : ℕ → ℝ} {g : G} (hφ : StrictMono φ)
    (hp : ∀ n, p n ∈ C (φ n)) (hapos : ∀ n, 0 < a n)
    (hazero : Tendsto a atTop (nhds 0))
    (hlim : Tendsto (fun n ↦ a n • p n) atTop (nhds g)) :
    g ∈ horizonOuterSetLimit C := by
  by_cases hg0 : g = 0
  · rw [hg0]
    exact (isCone_horizonOuterSetLimit C).1
  have hgnorm : (0 : ℝ) < ‖g‖ := norm_pos_iff.mpr hg0
  have hscalepos : ∀ n, 0 < ‖g‖⁻¹ * a n := fun n ↦
    mul_pos (inv_pos.mpr hgnorm) (hapos n)
  have hscalezero : Tendsto (fun n ↦ ‖g‖⁻¹ * a n) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hazero
  have hscaled : Tendsto (fun n ↦ (‖g‖⁻¹ * a n) • p n) atTop
      (nhds ((cosmicDirectionOf g hg0 : CosmicBoundary G) : G)) := by
    simpa only [mul_smul, coe_cosmicDirectionOf, NormedSpace.normalize] using
      tendsto_const_nhds.smul hlim
  have hdir : ((cosmicDirectionOf g hg0 : CosmicBoundary G) : G) ∈
      horizonOuterSetLimit C :=
    mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.2
      ⟨φ, p, hφ, hp, tendsto_cosmicDirection_of_scaling hscalepos hscalezero hscaled⟩
  have hscaledMem := (isCone_horizonOuterSetLimit C).smul_mem hdir (norm_nonneg g)
  simpa only [coe_cosmicDirectionOf, NormedSpace.norm_smul_normalize g] using
    hscaledMem

end HorizonExtraction

section Outer

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {C : ℕ → Set E} {D : Set E}

/-- **Theorem 5.53(b)**: the outer limit of the images stays inside `S(D)`.
The argument is the book's.  A convergent selection of values comes from
arguments in `Cν`; if those stay bounded, a cluster point of them lies in `D`
and the limiting graph point lies in `lim sup gph Sν = gph S`.  If they
escape, their direction is a horizon direction of `Cν` -- hence of `D` -- over
which `S∞` still reaches `0`, because the values stay bounded while the
arguments are rescaled to zero; the hypothesis excludes that. -/
theorem outerSetLimit_svImage_subset_svImage
    (hS : TotalGraphicalConverges Sseq S) (hC : outerSetLimit C ⊆ D)
    (h : svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E)) :
    outerSetLimit (fun n ↦ svImage (Sseq n) (C n)) ⊆ svImage S D := by
  intro u hu
  obtain ⟨φ, y, hφ, hyImage, hyu⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hu
  choose x hxC hxy using fun n ↦ mem_svImage.1 (hyImage n)
  by_cases hbdd : IsBounded (Set.range x)
  · obtain ⟨q, -, ψ, hψ, hq⟩ :=
      tendsto_subseq_of_bounded hbdd fun n ↦ Set.mem_range_self n
    refine mem_svImage.2 ⟨q, hC (mem_outerSetLimit_iff_exists_subsequence.2
      ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ, fun n ↦ hxC (ψ n), hq⟩), ?_⟩
    have hmem : (q, u) ∈ outerSetLimit (fun n ↦ svGraph (Sseq n)) :=
      mem_outerSetLimit_iff_exists_subsequence.2
        ⟨φ ∘ ψ, fun n ↦ (x (ψ n), y (ψ n)), hφ.comp hψ, fun n ↦ hxy (ψ n),
          hq.prodMk_nhds (hyu.comp hψ.tendsto_atTop)⟩
    rwa [hS.graphicalConverges.outer_eq] at hmem
  · exfalso
    obtain ⟨v, ψ, hψ, hvdir⟩ :=
      exists_cosmicDirection_subsequence_of_not_isBounded hbdd
    obtain ⟨a, hapos, hazero, hav⟩ := exists_scaling_of_tendsto_cosmicDirection hvdir
    have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
    have hvC : (v : E) ∈ horizonOuterSetLimit C :=
      mem_horizonOuterSetLimit_iff_exists_cosmicDirection_subsequence.2
        ⟨φ ∘ ψ, x ∘ ψ, hφ.comp hψ, fun n ↦ hxC (ψ n), hvdir⟩
    -- The values converge, so rescaling by `a n → 0` drives them to the origin.
    have hay : Tendsto (fun n ↦ a n • y (ψ n)) atTop (nhds 0) := by
      simpa only [zero_smul] using hazero.smul (hyu.comp hψ.tendsto_atTop)
    have hgraph : ((v : E), (0 : F)) ∈
        horizonOuterSetLimit (fun n ↦ svGraph (Sseq n)) :=
      mem_horizonOuterSetLimit_of_seq_smul (p := fun n ↦ (x (ψ n), y (ψ n)))
        (hφ.comp hψ) (fun n ↦ hxy (ψ n)) hapos hazero
        (by simpa only [Prod.smul_mk] using hav.prodMk_nhds hay)
    have hvzero : (v : E) ∈ ({0} : Set E) := by
      rw [← h]
      exact ⟨mem_svHorizon.2 (hS.horizonOuter_subset hgraph), hvC⟩
    rw [mem_singleton_iff] at hvzero
    simp [hvzero] at hvnorm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The hypothesis of 5.53(b) in the book's form implies the one used above,
by the horizon half of total convergence of the argument sets. -/
theorem svHorizon_inter_horizonOuterSetLimit_eq_of_subset
    (hCh : horizonOuterSetLimit C ⊆ horizonCone D)
    (h : svInv (svHorizon S) 0 ∩ horizonCone D = ({0} : Set E)) :
    svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E) := by
  refine Subset.antisymm (fun w hw ↦ ?_) ?_
  · rw [← h]
    exact ⟨hw.1, hCh hw.2⟩
  · rw [singleton_subset_iff]
    exact ⟨mem_svHorizon.2 (zero_mem_horizonCone _),
      (isCone_horizonOuterSetLimit C).1⟩

/-- **Theorem 5.53(b)** as printed. -/
theorem outerSetLimit_svImage_subset_svImage_of_horizonCone
    (hS : TotalGraphicalConverges Sseq S) (hC : outerSetLimit C ⊆ D)
    (hCh : horizonOuterSetLimit C ⊆ horizonCone D)
    (h : svInv (svHorizon S) 0 ∩ horizonCone D = ({0} : Set E)) :
    outerSetLimit (fun n ↦ svImage (Sseq n) (C n)) ⊆ svImage S D :=
  outerSetLimit_svImage_subset_svImage hS hC
    (svHorizon_inter_horizonOuterSetLimit_eq_of_subset hCh h)

/-- The engine of 5.53(c), the moving-mapping counterpart of the one in
5.30(d): rescaled arguments cannot escape when the rescaled values stay
bounded, because an escaping direction would be a horizon direction of the
sets `Cν` over which `S∞` reaches `0`. -/
private theorem isBounded_scaled_selection_seq
    (hS : TotalGraphicalConverges Sseq S)
    (h : svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E))
    {φ : ℕ → ℕ} {x : ℕ → E} {y : ℕ → F} {a : ℕ → ℝ}
    (hφ : StrictMono φ) (hxC : ∀ n, x n ∈ C (φ n))
    (hxy : ∀ n, y n ∈ Sseq (φ n) (x n))
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
  obtain ⟨R, hR⟩ := hay.exists_norm_le
  have hbound : Tendsto (fun n ↦ |b n| * max R 0) atTop (nhds 0) := by
    simpa only [abs_zero, zero_mul] using hbzero.abs.mul_const (max R 0)
  have hcy : Tendsto (fun n ↦ (b n * a (ψ n)) • y (ψ n)) atTop (nhds 0) :=
    squeeze_zero_norm (fun n ↦ by
      rw [mul_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        ((hR _ ⟨ψ n, rfl⟩).trans (le_max_left _ _)) (abs_nonneg _)) hbound
  have hgraph : ((v : E), (0 : F)) ∈
      horizonOuterSetLimit (fun n ↦ svGraph (Sseq n)) :=
    mem_horizonOuterSetLimit_of_seq_smul (p := fun n ↦ (x (ψ n), y (ψ n)))
      (hφ.comp hψ) (fun n ↦ hxy (ψ n)) hcpos hczero
      (by simpa only [Prod.smul_mk] using hcx.prodMk_nhds hcy)
  have hvzero : (v : E) ∈ ({0} : Set E) := by
    rw [← h]
    exact ⟨mem_svHorizon.2 (hS.horizonOuter_subset hgraph), hvC⟩
  have hvnorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  rw [mem_singleton_iff] at hvzero
  simp [hvzero] at hvnorm

/-- **Theorem 5.53(c)**, first half: every horizon direction of the images is
`S∞` of a horizon direction of the argument sets. -/
theorem horizonOuterSetLimit_svImage_subset_svImage_svHorizon
    (hS : TotalGraphicalConverges Sseq S)
    (hCh : horizonOuterSetLimit C ⊆ horizonCone D)
    (h : svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E)) :
    horizonOuterSetLimit (fun n ↦ svImage (Sseq n) (C n)) ⊆
      svImage (svHorizon S) (horizonCone D) := by
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
      (isBounded_scaled_selection_seq hS h hφ hxC hxy hapos hazero haybdd)
      fun n ↦ Set.mem_range_self n
  have hqx : Tendsto (fun n ↦ a (ψ n) • x (ψ n)) atTop (nhds q) := hq
  have hqy : Tendsto (fun n ↦ a (ψ n) • y (ψ n)) atTop (nhds (u : F)) :=
    hay.comp hψ.tendsto_atTop
  have hgraph : (q, (u : F)) ∈ svGraph (svHorizon S) :=
    hS.horizonOuter_subset (mem_horizonOuterSetLimit_of_seq_smul
      (p := fun n ↦ (x (ψ n), y (ψ n))) (hφ.comp hψ) (fun n ↦ hxy (ψ n))
      (fun n ↦ hapos (ψ n)) (hazero.comp hψ.tendsto_atTop)
      (by simpa only [Prod.smul_mk] using hqx.prodMk_nhds hqy))
  have hqD : q ∈ horizonCone D :=
    hCh (mem_horizonOuterSetLimit_of_seq_smul (p := fun n ↦ x (ψ n))
      (hφ.comp hψ) (fun n ↦ hxC (ψ n)) (fun n ↦ hapos (ψ n))
      (hazero.comp hψ.tendsto_atTop) hqx)
  exact (isCone_svImage_svHorizon S (isCone_horizonCone D)).smul_mem
    (mem_svImage.2 ⟨q, hqD, hgraph⟩) hr.le

/-- **Theorem 5.53(c)**. -/
theorem horizonOuterSetLimit_svImage_subset_horizonCone
    (hS : TotalGraphicalConverges Sseq S)
    (hCh : horizonOuterSetLimit C ⊆ horizonCone D)
    (h : svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E))
    (himg : svImage (svHorizon S) (horizonCone D) ⊆
      horizonCone (svImage S D)) :
    horizonOuterSetLimit (fun n ↦ svImage (Sseq n) (C n)) ⊆
      horizonCone (svImage S D) :=
  (horizonOuterSetLimit_svImage_subset_svImage_svHorizon hS hCh h).trans himg

end Outer

section Convergence

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {C : ℕ → Set E} {D : Set E}

/-- **Theorem 5.53**, first concluding statement.  The printed version asks
only for continuous convergence of the mappings; see
`not_pkConverges_svImage_of_svConvergesContinuously` for why total graph
convergence has to be added. -/
theorem pkConverges_svImage_of_totalConverges
    (hcont : SvConvergesContinuously Sseq S)
    (hS : TotalGraphicalConverges Sseq S) (hC : TotalConverges C D)
    (h : svInv (svHorizon S) 0 ∩ horizonCone D = ({0} : Set E)) :
    PKConverges (fun n ↦ svImage (Sseq n) (C n)) (svImage S D) := by
  have hinner := svImage_subset_innerSetLimit_svImage hcont
    hC.pkConverges.inner_eq.ge
  have houter := outerSetLimit_svImage_subset_svImage_of_horizonCone hS
    hC.pkConverges.outer_eq.subset hC.horizonOuter_subset h
  exact ⟨Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner,
    Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit _))⟩

/-- **Theorem 5.53**, second concluding statement: with `(S∞)⁻¹(0) = {0}` the
horizon of the argument sets is unconstrained, so ordinary convergence of them
is enough. -/
theorem pkConverges_svImage_of_pkConverges
    (hcont : SvConvergesContinuously Sseq S)
    (hS : TotalGraphicalConverges Sseq S) (hC : PKConverges C D)
    (h : svInv (svHorizon S) 0 = ({0} : Set E)) :
    PKConverges (fun n ↦ svImage (Sseq n) (C n)) (svImage S D) := by
  have hseq : svInv (svHorizon S) 0 ∩ horizonOuterSetLimit C = ({0} : Set E) := by
    rw [h, Set.inter_eq_left, Set.singleton_subset_iff]
    exact (isCone_horizonOuterSetLimit C).1
  have hinner := svImage_subset_innerSetLimit_svImage hcont hC.inner_eq.ge
  have houter := outerSetLimit_svImage_subset_svImage hS hC.outer_eq.subset hseq
  exact ⟨Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit _).trans houter) hinner,
    Subset.antisymm houter
      (hinner.trans (innerSetLimit_subset_outerSetLimit _))⟩

/-- **Theorem 5.53**, total form: clause (c) upgrades the conclusion of the
first concluding statement to total convergence. -/
theorem totalConverges_svImage
    (hcont : SvConvergesContinuously Sseq S)
    (hS : TotalGraphicalConverges Sseq S) (hC : TotalConverges C D)
    (h : svInv (svHorizon S) 0 ∩ horizonCone D = ({0} : Set E))
    (himg : svImage (svHorizon S) (horizonCone D) ⊆
      horizonCone (svImage S D)) :
    TotalConverges (fun n ↦ svImage (Sseq n) (C n)) (svImage S D) :=
  totalConverges_iff_pkConverges_and_horizonOuter_subset.2
    ⟨pkConverges_svImage_of_totalConverges hcont hS hC h,
      horizonOuterSetLimit_svImage_subset_horizonCone hS hC.horizonOuter_subset
        (svHorizon_inter_horizonOuterSetLimit_eq_of_subset hC.horizonOuter_subset h)
        himg⟩

end Convergence

section Necessity

/-- The witness for 5.53's first concluding statement: `Sν` puts a single
value over the *escaping* argument `ν` and nothing anywhere else, so it
converges continuously to the empty-valued mapping while every image
`Sν(IR)` is `{0}`. -/
noncomputable def escapingValueSeq (n : ℕ) (x : ℝ) : Set ℝ :=
  if x = (n : ℝ) then {0} else ∅

theorem svImage_escapingValueSeq_univ (n : ℕ) :
    svImage (escapingValueSeq n) univ = ({0} : Set ℝ) := by
  ext u
  simp only [mem_svImage, mem_univ, true_and, escapingValueSeq]
  constructor
  · rintro ⟨x, hx⟩
    by_cases h : x = (n : ℝ)
    · rwa [if_pos h] at hx
    · rw [if_neg h] at hx
      exact absurd hx (notMem_empty u)
  · intro hu
    exact ⟨(n : ℝ), by rw [if_pos rfl]; exact hu⟩

theorem svConvergesContinuously_escapingValueSeq :
    SvConvergesContinuously escapingValueSeq (fun _ : ℝ ↦ (∅ : Set ℝ)) := by
  intro x y _ hy
  have hbdd : IsBounded (Set.range y) := Metric.isBounded_range_of_tendsto _ hy
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  have hev : ∀ᶠ n in atTop, escapingValueSeq n (y n) = ∅ := by
    filter_upwards [eventually_gt_atTop ⌈R⌉₊] with n hn
    refine if_neg fun heq ↦ ?_
    have h1 : ‖y n‖ ≤ R := hR _ ⟨n, rfl⟩
    rw [heq, Real.norm_natCast] at h1
    have h2 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
    have h3 : ((⌈R⌉₊ : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have houter : outerSetLimit (fun n ↦ escapingValueSeq n (y n)) ⊆ ∅ :=
    outerSetLimitAlong_subset_of_eventually_subset isClosed_empty
      (hev.mono fun n h ↦ h.subset)
  exact ⟨Subset.antisymm
      ((innerSetLimit_subset_outerSetLimit _).trans houter) (empty_subset _),
    Subset.antisymm houter (empty_subset _)⟩

/-- **5.53's first concluding statement is false as printed.**  It asks only
for continuous convergence of the mappings, but the escape case of clause (b)
needs `lim sup∞ gph Sν ⊂ gph S∞`, which continuous convergence does not
supply -- as the book itself observes just before 5.53, with a
counterexample of the same shape.  Here the arguments escape while the values
stay put, so the images do not converge to the image of the limit. -/
theorem not_pkConverges_svImage_of_svConvergesContinuously :
    ∃ (Sseq : ℕ → ℝ → Set ℝ) (S : ℝ → Set ℝ) (C : ℕ → Set ℝ) (D : Set ℝ),
      SvConvergesContinuously Sseq S ∧ TotalConverges C D ∧
        svInv (svHorizon S) 0 ∩ horizonCone D = ({0} : Set ℝ) ∧
        ¬ outerSetLimit (fun n ↦ svImage (Sseq n) (C n)) ⊆ svImage S D := by
  refine ⟨escapingValueSeq, fun _ ↦ ∅, fun _ ↦ univ, univ,
    svConvergesContinuously_escapingValueSeq, ?_, ?_, ?_⟩
  · exact totalConverges_of_isCone (pkConverges_const_of_isClosed isClosed_univ)
      univ_nonempty fun _ ↦ ⟨mem_univ 0, fun _ _ _ _ ↦ mem_univ _⟩
  · have hgraph : svGraph (fun _ : ℝ ↦ (∅ : Set ℝ)) = (∅ : Set (ℝ × ℝ)) := by
      ext p
      simp [svGraph]
    have hinv : svInv (svHorizon (fun _ : ℝ ↦ (∅ : Set ℝ))) 0 = ({0} : Set ℝ) := by
      ext z
      simp [svInv, svHorizon, hgraph, Prod.ext_iff]
    rw [hinv, Set.inter_eq_left, Set.singleton_subset_iff]
    exact zero_mem_horizonCone _
  · intro hcon
    have himg : ∀ n : ℕ, svImage (escapingValueSeq n) univ = ({0} : Set ℝ) :=
      svImage_escapingValueSeq_univ
    have hlim : outerSetLimit (fun n ↦ svImage (escapingValueSeq n) univ)
        = ({0} : Set ℝ) := by
      simp only [himg]
      simp
    rw [hlim] at hcon
    have : (0 : ℝ) ∈ svImage (fun _ : ℝ ↦ (∅ : Set ℝ)) univ := hcon rfl
    simp [svImage] at this

end Necessity

end RW
