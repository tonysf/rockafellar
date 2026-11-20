/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Extremal principles for images of closed sets
-/

import RockafellarWets.Chapter9.InverseCoderivatives
import RockafellarWets.Chapter9.ConvexMetricRegularity
import RockafellarWets.Chapter9.CoderivativeScalarization
import RockafellarWets.Chapter9.SingleValuedGraphicalDerivatives
import RockafellarWets.Chapter9.SmoothLipschitzModulus
import RockafellarWets.Chapter8.ConstrainedOptimality
import RockafellarWets.Chapter8.SmoothGraphicalDerivatives

open Filter Metric Set Topology
open scoped InnerProductSpace Pointwise

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The coderivative form underlying the image extremal principle. -/
theorem extremal_image_coderivative {f : E → F} {X : Set E} {x : E}
    (hX : IsClosed X) (hx : x ∈ X) (hf : Continuous f) (hs : StrictlyContinuousAt f x)
    (hb : f x ∉ interior (f '' X)) :
    ∃ y : F, y ≠ 0 ∧ ∃ v ∈ normalCone X x, -v ∈ coderivative (svSingleton f) x (f x) y := by
  classical
  let S := svRestrict (svSingleton f) X
  have hmem : f x ∈ S x := ⟨rfl,hx⟩
  have hG : IsClosed (svGraph (svSingleton f)) :=
    isClosed_eq continuous_snd (hf.comp continuous_fst)
  have hSG : svGraph S = svGraph (svSingleton f) ∩ (X ×ˢ univ) := by
    ext p
    change (p.2 = f p.1 ∧ p.1 ∈ X) ↔ (p.2 = f p.1 ∧ p.1 ∈ X ∧ p.2 ∈ univ)
    simp
  have hclosed : IsClosed (svGraph S) := hSG ▸ hG.inter (hX.prod isClosed_univ)
  have hrange : svRange S = f '' X := by
    ext y
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a,ha.2,ha.1.symm⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a,rfl,ha⟩
  have hnot : ¬ HasAubinPropertyAt (svInv S) (f x) x := by
    intro h
    apply hb
    simpa only [svDom_svInv,hrange] using h.interior_domain
  have hfail : ¬ ∀ y, 0 ∈ coderivative S x (f x) y → y = 0 :=
    fun h ↦ hnot ((hasAubinProperty_inverse_iff_coderivative_nonsingular hmem
      (RW.IsClosed.isLocallyClosedAt hclosed _)).mpr h)
  push_neg at hfail
  obtain ⟨y,hy,hy0⟩ := hfail
  let p := WithLp.toLp 2 (x,f x)
  let C := euclideanSvGraph (svSingleton f)
  let D := l2ProdSet X (univ : Set F)
  have hC : IsClosed C := hG.preimage (WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous
  have hD : IsClosed D := isClosed_l2ProdSet hX isClosed_univ
  have hprod : normalCone D p = l2ProdSet (normalCone X x) {(0:F)} := by
    rw [show normalCone D p = _ from normalCone_l2ProdSet X univ x (f x),normalCone_univ]
  have hFzero : coderivative (svSingleton f) x (f x) 0 = {0} :=
    (hasAubinPropertyAt_iff_coderivative_zero (show f x ∈ svSingleton f x from rfl)
      (RW.IsClosed.isLocallyClosedAt hG _)).mp hs.hasAubinProperty_singleton
  have hCQ : ∀ n ∈ normalCone C p, -n ∈ normalCone D p → n = 0 := by
    intro n hn hneg
    obtain ⟨⟨a,b⟩,rfl⟩ := (WithLp.toLp_surjective 2) n
    rw [hprod] at hneg
    have hb0 : b = 0 := neg_eq_zero.mp (show -b = 0 from hneg.2)
    subst b
    have ha : a ∈ coderivative (svSingleton f) x (f x) 0 := by
      change WithLp.toLp 2 (a,-(0:F)) ∈ normalCone C p
      simpa only [neg_zero] using hn
    rw [hFzero,mem_singleton_iff] at ha
    exact ha ▸ rfl
  have hEucl : euclideanSvGraph S = C ∩ D := by
    ext q
    change (q.snd = f q.fst ∧ q.fst ∈ X) ↔ (q.snd = f q.fst ∧ q.fst ∈ X ∧ q.snd ∈ univ)
    simp
  have hnormal : WithLp.toLp 2 ((0:E),-y) ∈ normalCone (C ∩ D) p := by
    change WithLp.toLp 2 ((0:E),-y) ∈ normalCone (euclideanSvGraph S) p at hy
    rwa [hEucl] at hy
  obtain ⟨a,ha,b,hb,hab⟩ := normalCone_inter_subset_add hC hD hCQ hnormal
  rw [hprod] at hb
  obtain ⟨⟨a₁,a₂⟩,rfl⟩ := (WithLp.toLp_surjective 2) a
  obtain ⟨⟨b₁,b₂⟩,rfl⟩ := (WithLp.toLp_surjective 2) b
  have hb₂ : b₂ = 0 := hb.2
  have ha₂ : a₂ = -y := by
    have he := congrArg (fun q : WithLp 2 (E × F) ↦ q.snd) hab
    change a₂+b₂ = -y at he
    simpa only [hb₂,add_zero] using he
  have ha₁ : a₁ = -b₁ := by
    have he := congrArg (fun q : WithLp 2 (E × F) ↦ q.fst) hab
    change a₁+b₁ = 0 at he
    exact eq_neg_of_add_eq_zero_left he
  exact ⟨y,hy0,b₁,hb.1,by simpa only [ha₁,ha₂] using ha⟩

/-- **Proposition 9.69(a).** A boundary image produces a nonzero multiplier
and opposite normal/subgradient vectors. Only continuity away from the base
point is needed; strict continuity is required at that point. -/
theorem extremal_image_subgradient {f : E → F} {X : Set E} {x : E}
    (hX : IsClosed X) (hx : x ∈ X) (hf : Continuous f) (hs : StrictlyContinuousAt f x)
    (hb : f x ∉ interior (f '' X)) :
    ∃ y : F, y ≠ 0 ∧ ∃ v ∈ normalCone X x,
      -v ∈ subdifferential (fun a ↦ ((⟪y,f a⟫_ℝ : ℝ) : EReal)) x := by
  obtain ⟨y,hy,v,hv,hcode⟩ := extremal_image_coderivative hX hx hf hs hb
  rw [coderivative_svSingleton_eq_subdifferential hs] at hcode
  exact ⟨y,hy,v,hv,hcode⟩

/-- **Proposition 9.69(a)** in the printed set-sum form. -/
theorem extremal_principle_image {f : E → F} {X : Set E} {x : E}
    (hX : IsClosed X) (hx : x ∈ X) (hf : ∀ a, StrictlyContinuousAt f a)
    (hb : f x ∉ interior (f '' X)) :
    ∃ y : F, y ≠ 0 ∧ (0:E) ∈ normalCone X x +
      subdifferential (fun a ↦ ((⟪y,f a⟫_ℝ : ℝ) : EReal)) x := by
  obtain ⟨y,hy,v,hv,hs⟩ := extremal_image_subgradient hX hx
    (continuous_iff_continuousAt.mpr fun a ↦ (hf a).continuousAt) (hf x) hb
  exact ⟨y,hy,v,hv,-v,hs,add_neg_cancel v⟩

/-- The linear image specialization used for the set-sum and nonoverlap
principles. -/
theorem extremal_linear_image {X : Set E} {x : E} (A : E →L[ℝ] F)
    (hX : IsClosed X) (hx : x ∈ X) (hb : A x ∉ interior (A '' X)) :
    ∃ y : F, y ≠ 0 ∧ -(A.adjoint y) ∈ normalCone X x := by
  have hs : StrictlyContinuousAt A x :=
    (lipschitzModulus_eq_of_hasStrictFDerivAt A.hasStrictFDerivAt).trans_lt ENNReal.coe_lt_top
  obtain ⟨y,hy,v,hv,hcode⟩ := extremal_image_coderivative hX hx A.continuous hs hb
  have he := (graphicalDerivatives_of_contDiffAt (x := x) A.contDiff.contDiffAt).2.2.2.1
  rw [ContinuousLinearMap.fderiv] at he
  rw [he] at hcode
  have hvA : -v = A.adjoint y := hcode
  exact ⟨y,hy,by simpa only [← hvA,neg_neg] using hv⟩

end RW
