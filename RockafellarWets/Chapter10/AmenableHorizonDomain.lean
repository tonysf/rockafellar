/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Horizon subgradients are domain normals for amenable functions
-/
import RockafellarWets.Chapter10.NormalMultiplierLimits

open Set Filter Topology

namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A regular domain normal induces a horizontal epigraph normal. -/
theorem regularNormal_domain_subset_horizonSubdifferential {f : E → EReal} {x : E} {c : ℝ}
    (hx : f x = c) (hl : IsLocallyLscAt f x) :
    regularNormalCone (effectiveDomain f) x ⊆ horizonSubdifferential f x := by
  intro v hv
  apply (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hl hx).mpr
  apply regularNormalCone_subset_normalCone
  have hprod : WithLp.toLp 2 (v,(0:ℝ)) ∈
      regularNormalCone (l2ProdSet (effectiveDomain f) univ) (WithLp.toLp 2 (x,c)) := by
    rw [regularNormalCone_l2ProdSet,regularNormalCone_univ]
    exact ⟨hv,rfl⟩
  apply regularNormalCone_mono_local (C := euclideanEpigraph f)
    (D := l2ProdSet (effectiveDomain f) univ) (x := WithLp.toLp 2 (x,c)) hx.le ?_ hprod
  apply Filter.Eventually.of_forall
  intro y hy
  exact ⟨hy.trans_lt (EReal.coe_lt_top _),mem_univ _⟩

/-- The local lower-semicontinuity consequence is available for a model
of any admitted smoothness order. -/
theorem AmenableFunctionModel.isLocallyLscAt {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) : IsLocallyLscAt f x := by
  have h : AmenableAt f x := ⟨{ M with smooth := M.smooth.of_le (by exact_mod_cast hr),plq := by simp }⟩
  exact h.isSubdifferentiallyRegularAt.isLocallyLscAt

/-- **Exercise 10.25(a)**: the general domain-normal identity, without
assuming that the domain is locally closed or that subgradients are nonempty. -/
theorem AmenableFunctionModel.horizon_eq_normal_domain {f : E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : AmenableFunctionModel f x r full) (hr : 1 ≤ r) :
    horizonSubdifferential f x = normalCone (effectiveDomain f) x := by
  apply Subset.antisymm
  · exact (M.horizon_subset_regularNormal_domain hr).trans (regularNormalCone_subset_normalCone _ _)
  · rintro v ⟨_,ys,us,hyDom,hy,huN,hu⟩
    have hnear := (M.qualification_eventually hr).and (M.isOpen.mem_nhds M.mem)
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hy.eventually hnear)
    have hNV (n : ℕ) : ys (n+N) ∈ M.neighborhood := (hN (n+N) (Nat.le_add_left _ _)).2
    have hNQ (n : ℕ) : ∀z ∈ normalCone (closure (effectiveDomain M.outer)) (M.inner (ys (n+N))),
        (fderiv ℝ M.inner (ys (n+N))).adjoint z = 0 → z = 0 := (hN (n+N) (Nat.le_add_left _ _)).1
    have hfin (n : ℕ) : f (ys (n+N)) ≠ ⊥ ∧ f (ys (n+N)) ≠ ⊤ := by
      refine ⟨?_,ne_of_lt (hyDom (n+N))⟩
      rw [M.eqOn _ (hNV n)]
      exact (M.proper.2 _).ne'
    let Ms (n : ℕ) : AmenableFunctionModel f (ys (n+N)) r full :=
      { M with mem := hNV n, finite := hfin n, qualification := hNQ n }
    have hval (n : ℕ) : M.outer (M.inner (ys (n+N))) = ((f (ys (n+N))).toReal:EReal) := by
      rw [← M.eqOn _ (hNV n)]
      exact (EReal.coe_toReal (hfin n).2 (hfin n).1).symm
    have him (n : ℕ) : us (n+N) ∈ (fderiv ℝ M.inner (ys (n+N))).adjoint ''
        normalCone (closure (effectiveDomain M.outer)) (M.inner (ys (n+N))) := by
      have hh := regularNormal_domain_subset_horizonSubdifferential
        (f := f) (x := ys (n+N)) ((EReal.coe_toReal (hfin n).2 (hfin n).1).symm)
        ((Ms n).isLocallyLscAt hr) (huN (n+N))
      rw [((Ms n).derivatives hr).2.1] at hh
      change us (n+N) ∈ (fderiv ℝ M.inner (ys (n+N))).adjoint ''
        horizonSubdifferential M.outer (M.inner (ys (n+N))) at hh
      rwa [horizonSubdifferential_eq_normalCone_closure_domain M.proper M.lsc M.convex (hval n)] at hh
    have hcont := M.smooth.continuousOn.continuousAt (M.isOpen.mem_nhds M.mem)
    have hder := (M.smooth.continuousOn_fderiv_of_isOpen M.isOpen (by exact_mod_cast hr)).continuousAt
      (M.isOpen.mem_nhds M.mem)
    have hh := mem_image_normalCone_of_tendsto isClosed_closure hcont
      (ContinuousLinearMap.adjoint.continuous.continuousAt.comp hder) M.qualification
      (hy.comp (tendsto_add_atTop_nat N)) (hu.comp (tendsto_add_atTop_nat N)) him
    have hxval : M.outer (M.inner x) = ((f x).toReal:EReal) := by
      rw [← M.eqOn x M.mem]
      exact (EReal.coe_toReal M.finite.2 M.finite.1).symm
    rw [(M.derivatives hr).2.1,horizonSubdifferential_eq_normalCone_closure_domain M.proper M.lsc M.convex hxval]
    exact hh

/-- **Exercise 10.25(a)**, the representation-free statement. -/
theorem AmenableAt.horizon_eq_normal_domain {f : E → EReal} {x : E} (h : AmenableAt f x) :
    horizonSubdifferential f x = normalCone (effectiveDomain f) x := by
  obtain ⟨M⟩ := h
  exact M.horizon_eq_normal_domain le_rfl

end RW
