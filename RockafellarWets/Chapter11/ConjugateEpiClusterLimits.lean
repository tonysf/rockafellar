/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugation and one-sided epi-limits
-/
import RockafellarWets.Chapter11.ConjugateEpiConvergence
import RockafellarWets.Chapter7.EpiLimitProperties
import RockafellarWets.Chapter7.InfimaAndMinimizers
import RockafellarWets.Chapter4.ClusterLimits

open Bornology Filter Metric Set Topology
namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- All subsequential epi-limits, including improper functions. -/
def epiClusterLimits (f : ℕ → E → EReal) : Set (E → EReal) :=
  {g | ∃ φ : ℕ → ℕ, StrictMono φ ∧ EpiConverges (f ∘ φ) g}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem epigraph_cluster (f : ℕ → E → EReal) {D : Set (E × ℝ)}
    (hD : D ∈ pkClusterLimits (fun n ↦ epigraph (f n))) :
    ∃ g ∈ epiClusterLimits f, epigraph g = D := by
  obtain ⟨φ,hφ,hD⟩ := hD
  have he : epigraph (epiLowerLimit (f ∘ φ)) = D := (epigraph_epiLowerLimit _).trans hD.2
  exact ⟨epiLowerLimit (f ∘ φ),⟨φ,hφ,by unfold EpiConverges; rw [he]; exact hD⟩,he⟩

theorem le_epiLowerLimit_iff_epiClusterLimits {f : ℕ → E → EReal} {g : E → EReal} :
    g ≤ epiLowerLimit f ↔ ∀ h ∈ epiClusterLimits f, g ≤ h := by
  rw [← epigraph_subset_epigraph_iff,epigraph_epiLowerLimit,
    outerSetLimit_eq_sUnion_pkClusterLimits]
  constructor
  · intro hh h hm
    apply epigraph_subset_epigraph_iff.mp
    obtain ⟨φ,hφ,hm⟩ := hm
    exact (subset_sUnion_of_mem (show epigraph h ∈ pkClusterLimits (fun n ↦ epigraph (f n)) from ⟨φ,hφ,hm⟩)).trans hh
  · intro hh p hp
    obtain ⟨D,hD,hp⟩ := hp
    obtain ⟨h,hm,he⟩ := epigraph_cluster f hD
    exact epigraph_subset_epigraph_iff.mpr (hh h hm) (he.symm ▸ hp)

theorem epiUpperLimit_le_iff_epiClusterLimits {f : ℕ → E → EReal} {g : E → EReal} :
    epiUpperLimit f ≤ g ↔ ∀ h ∈ epiClusterLimits f, h ≤ g := by
  rw [← epigraph_subset_epigraph_iff,epigraph_epiUpperLimit,
    innerSetLimit_eq_sInter_pkClusterLimits]
  constructor
  · intro hh h hm
    apply epigraph_subset_epigraph_iff.mp
    obtain ⟨φ,hφ,hm⟩ := hm
    exact hh.trans (sInter_subset_of_mem ⟨φ,hφ,hm⟩)
  · intro hh p hp
    apply mem_sInter.mpr
    intro D hD
    obtain ⟨h,hm,he⟩ := epigraph_cluster f hD
    exact he ▸ epigraph_subset_epigraph_iff.mpr (hh h hm) hp

/-- The bounded-set hypothesis in 11.34 prevents epigraphical escape along
every subsequence. -/
theorem not_epiConverges_top_subsequence_of_bounded_infima {f : ℕ → E → EReal}
    {B : Set E} (hB : IsBounded B)
    (hi : limsup (fun n ↦ infimumOn (f n) B) atTop < ⊤)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ¬ EpiConverges (f ∘ φ) (fun _ ↦ ⊤) := by
  obtain ⟨a,ha,_⟩ := EReal.exists_between_coe_real hi
  have hev : ∀ᶠ n in atTop, infimumOn (f n) B < (a:EReal) :=
    eventually_lt_of_limsup_lt ha (by isBoundedDefault)
  obtain ⟨R,hR⟩ := hB.exists_norm_le
  intro he
  let r := max (max R a) 0 + 1
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨n,hn,hn'⟩ := ((hφ.tendsto_atTop.eventually hev).and
    ((epiConverges_top_iff_eventually_on_closedBall _).mp he r hr)).exists
  obtain ⟨x,hxa⟩ := iInf_lt_iff.mp hn
  obtain ⟨hxB,hxa⟩ := iInf_lt_iff.mp hxa
  have hxball : x ∈ closedBall (0:E) r := by
    rw [mem_closedBall_zero_iff]
    exact (hR x hxB).trans (by dsimp [r]; linarith [le_max_left R a,le_max_left (max R a) 0])
  have har : a ≤ r := by dsimp [r]; linarith [le_max_right R a,le_max_left (max R a) 0]
  exact hxa.not_ge ((EReal.coe_le_coe_iff.mpr har).trans (hn' x hxball))

/-- Under the two nondegeneracy conditions in 11.34, every epi-cluster
function is proper, lower semicontinuous and convex. -/
theorem epiClusterLimits_proper {f : ℕ → E → EReal}
    (hc : ∀ n, Convex ℝ (epigraph (f n)))
    (hbot : ∀ x, ⊥ < epiLowerLimit f x)
    (hne : ∀ φ : ℕ → ℕ, StrictMono φ → ¬ EpiConverges (f ∘ φ) (fun _ ↦ ⊤))
    {g : E → EReal} (hg : g ∈ epiClusterLimits f) :
    IsProper g ∧ LowerSemicontinuous g ∧ Convex ℝ (epigraph g) := by
  obtain ⟨φ,hφ,he⟩ := hg
  have hlow : epiLowerLimit f ≤ g :=
    le_epiLowerLimit_iff_epiClusterLimits.mp le_rfl g ⟨φ,hφ,he⟩
  refine ⟨⟨?_,fun x ↦ (hbot x).trans_le (hlow x)⟩,he.lowerSemicontinuous,
    he.convex_epigraph (fun n ↦ hc (φ n))⟩
  by_contra! ht
  have hgt : g = fun _ ↦ ⊤ := funext fun x ↦ top_unique (ht x)
  exact hne φ hφ (hgt ▸ he)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Epi-convergence is preserved by strictly increasing subsequences. -/
theorem EpiConverges.comp_strictMono {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) {φ : ℕ → ℕ} (hφ : StrictMono φ) : EpiConverges (f ∘ φ) g := by
  have hi : epigraph g ⊆ innerSetLimit (fun n ↦ epigraph (f (φ n))) := by
    rw [← h.1]
    exact innerSetLimit_subset_subsequence (C := fun n ↦ epigraph (f n)) hφ
  have ho : outerSetLimit (fun n ↦ epigraph (f (φ n))) ⊆ epigraph g := by
    rw [← h.2]
    exact outerSetLimit_subsequence_subset (C := fun n ↦ epigraph (f n)) hφ
  exact ⟨((innerSetLimit_subset_outerSetLimit _).trans ho).antisymm hi,
    ho.antisymm (hi.trans (innerSetLimit_subset_outerSetLimit _))⟩

/-- Conjugation bijects the epi-cluster functions under the nondegeneracy
conditions in Theorem 11.34. -/
theorem epiClusterLimits_fenchelConjugate {f : ℕ → E → EReal}
    (hp : ∀ n, IsProper (f n)) (hl : ∀ n, LowerSemicontinuous (f n))
    (hc : ∀ n, Convex ℝ (epigraph (f n)))
    (hbot : ∀ x, ⊥ < epiLowerLimit f x)
    (hne : ∀ φ : ℕ → ℕ, StrictMono φ → ¬ EpiConverges (f ∘ φ) (fun _ ↦ ⊤)) :
    epiClusterLimits (fun n ↦ fenchelConjugate (f n)) = fenchelConjugate '' epiClusterLimits f := by
  apply Subset.antisymm
  · rintro g ⟨φ,hφ,hg⟩
    obtain ⟨ψ,h,hψ,hht,he⟩ := exists_epiConvergent_subsequence_of_not_escape (hne φ hφ)
    have hh : h ∈ epiClusterLimits f := ⟨φ ∘ ψ,hφ.comp hψ,by simpa only [Function.comp_assoc] using he⟩
    obtain ⟨hph,hlh,hch⟩ := epiClusterLimits_proper hc hbot hne hh
    have hdual := he.fenchelConjugate (fun n ↦ hp (φ (ψ n)))
      (fun n ↦ hl (φ (ψ n))) (fun n ↦ hc (φ (ψ n))) hph hlh hch
    have hgsub : EpiConverges ((fun n ↦ fenchelConjugate (f (φ n))) ∘ ψ) g :=
      hg.comp_strictMono hψ
    exact ⟨h,hh,eq_of_epigraph_eq (hdual.unique hgsub)⟩
  · rintro _ ⟨h,hh,rfl⟩
    obtain ⟨hph,hlh,hch⟩ := epiClusterLimits_proper hc hbot hne hh
    obtain ⟨φ,hφ,he⟩ := hh
    exact ⟨φ,hφ,he.fenchelConjugate (fun n ↦ hp (φ n)) (fun n ↦ hl (φ n))
      (fun n ↦ hc (φ n)) hph hlh hch⟩

/-- Order reversal is an equivalence on the proper closed convex functions. -/
theorem fenchelConjugate_le_fenchelConjugate_iff {f g : E → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f))
    (hgp : IsProper g) (hgl : LowerSemicontinuous g) (hgc : Convex ℝ (epigraph g)) :
    fenchelConjugate f ≤ fenchelConjugate g ↔ g ≤ f := by
  refine ⟨fun h ↦ ?_,fun h ↦ fenchelConjugate_antitone h⟩
  have h' := fenchelConjugate_antitone h
  simpa only [fenchelConjugate_fenchelConjugate_eq hp hl hc,
    fenchelConjugate_fenchelConjugate_eq hgp hgl hgc] using h'

/-- The two general one-sided equivalences in **Theorem 11.34**, with the
bounded-set and finite lower epi-limit hypotheses exactly as printed. -/
theorem conjugate_epiLimit_inequalities {f : ℕ → E → EReal} {g : E → EReal}
    (hp : ∀ n, IsProper (f n)) (hl : ∀ n, LowerSemicontinuous (f n))
    (hc : ∀ n, Convex ℝ (epigraph (f n)))
    (hgp : IsProper g) (hgl : LowerSemicontinuous g) (hgc : Convex ℝ (epigraph g))
    (hbot : ∀ x, ⊥ < epiLowerLimit f x) {B : Set E} (hB : IsBounded B)
    (hi : limsup (fun n ↦ infimumOn (f n) B) atTop < ⊤) :
    (g ≤ epiLowerLimit f ↔ epiUpperLimit (fun n ↦ fenchelConjugate (f n)) ≤ fenchelConjugate g) ∧
    (epiUpperLimit f ≤ g ↔ fenchelConjugate g ≤ epiLowerLimit (fun n ↦ fenchelConjugate (f n))) := by
  have hne := fun (φ : ℕ → ℕ) (hφ : StrictMono φ) ↦ not_epiConverges_top_subsequence_of_bounded_infima hB hi hφ
  have he := epiClusterLimits_fenchelConjugate hp hl hc hbot hne
  rw [le_epiLowerLimit_iff_epiClusterLimits,epiUpperLimit_le_iff_epiClusterLimits,
    epiUpperLimit_le_iff_epiClusterLimits,le_epiLowerLimit_iff_epiClusterLimits,he]
  simp only [forall_mem_image]
  constructor
  · apply forall₂_congr
    intro h hh
    obtain ⟨hhp,hhl,hhc⟩ := epiClusterLimits_proper hc hbot hne hh
    exact (fenchelConjugate_le_fenchelConjugate_iff hhp hhl hhc hgp hgl hgc).symm
  · apply forall₂_congr
    intro h hh
    obtain ⟨hhp,hhl,hhc⟩ := epiClusterLimits_proper hc hbot hne hh
    exact (fenchelConjugate_le_fenchelConjugate_iff hgp hgl hgc hhp hhl hhc).symm

end RW
