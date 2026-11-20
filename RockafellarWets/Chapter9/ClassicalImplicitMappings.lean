/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Classical strictly differentiable implicit mappings

Theorem 9.56(d), with the corrected derivative `-A⁻¹ B`. The printed
formula omits the minus sign, as the equation `x + p = 0` demonstrates.
-/

import RockafellarWets.Chapter9.InverseLocalizationDerivatives
import RockafellarWets.Chapter9.ImplicitMappingDefinitions
import Mathlib.Analysis.Calculus.Deriv.Add

open Filter Metric Set Topology
open scoped NNReal

namespace RW

section Block

variable {E P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The invertible block derivative of the augmented implicit-equation
mapping `(x,p) ↦ (f(x,p),p)`. -/
def implicitBlockEquiv (A : E ≃L[ℝ] F) (B : P →L[ℝ] F) : (E × P) ≃L[ℝ] (F × P) where
  toFun z := (A z.1 + B z.2,z.2)
  invFun z := (A.symm (z.1 - B z.2),z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z v := by ext <;> simp <;> abel
  map_smul' r z := by ext <;> simp [smul_add]
  continuous_toFun := (A.continuous.comp continuous_fst |>.add
    (B.continuous.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun := (A.symm.continuous.comp
    (continuous_fst.sub (B.continuous.comp continuous_snd))).prodMk continuous_snd

@[simp] theorem implicitBlockEquiv_apply (A : E ≃L[ℝ] F) (B : P →L[ℝ] F) (z : E × P) :
    implicitBlockEquiv A B z = (A z.1 + B z.2,z.2) := rfl

@[simp] theorem implicitBlockEquiv_symm_apply (A : E ≃L[ℝ] F) (B : P →L[ℝ] F) (z : F × P) :
    (implicitBlockEquiv A B).symm z = (A.symm (z.1 - B z.2),z.2) := rfl

end Block

section Implicit

variable {E P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Theorem 9.56(d)**, corrected classical implicit-function formula.
The branch represents all nearby solutions and has derivative `-A⁻¹ B`.
The result also holds in Banach spaces. -/
theorem exists_strict_implicit_localization
    {f : E × P → F} {x : E} {p : P} {A : E ≃L[ℝ] F} {B : P →L[ℝ] F}
    (hf : HasStrictFDerivAt f ((A : E →L[ℝ] F).coprod B) (x,p)) (hzero : f (x,p) = 0) :
    ∃ g : P → E, IsLipschitzSingleValuedLocalization (fun q ↦ {a | f (a,q) = 0}) p x g ∧
      HasStrictFDerivAt g (-((A.symm : F →L[ℝ] E).comp B)) p := by
  let H : E × P → F × P := fun z ↦ (f z,z.2)
  let L := implicitBlockEquiv A B
  have hH : HasStrictFDerivAt H (L : (E × P) →L[ℝ] (F × P)) (x,p) := by
    convert hf.prodMk (ContinuousLinearMap.snd ℝ E P).hasStrictFDerivAt using 1
  have hHp : H (x,p) = (0,p) := by simp [H,hzero]
  obtain ⟨G,r,s,k,hr,hs,hGp,hGL,hfiber,hGd,_⟩ :=
    HasStrictFDerivAt.exists_lipschitz_inverse_branch hH
  rw [hHp] at hGp hGL hfiber hGd
  let g : P → E := fun q ↦ (G (0,q)).1
  have hmem (q : P) (hq : q ∈ ball p r) :
      G (0,q) ∈ svInv (fun z ↦ {H z}) (0,q) ∩ ball (x,p) s := by
    apply (hfiber (0,q) ?_).symm ▸ mem_singleton (G (0,q))
    simpa only [mem_ball,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using hq
  have hsecond (q : P) (hq : q ∈ ball p r) : (G (0,q)).2 = q := by
    have he : (0,q) = H (G (0,q)) := (hmem q hq).1
    exact (congrArg Prod.snd he).symm
  refine ⟨g,?_,?_⟩
  · refine ⟨min r s,s,k,lt_min hr hs,hs,?_,?_,?_⟩
    · exact congrArg Prod.fst hGp
    · apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      have ha' : ((0 : F),a) ∈ ball (0,p) r := by
        simpa only [mem_ball,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using
          (lt_of_lt_of_le ha (min_le_left r s))
      have hb' : ((0 : F),b) ∈ ball (0,p) r := by
        simpa only [mem_ball,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using
          (lt_of_lt_of_le hb (min_le_left r s))
      have hfst : dist (G (0,a)).1 (G (0,b)).1 ≤ dist (G (0,a)) (G (0,b)) := by
        rw [Prod.dist_eq]
        exact le_max_left _ _
      exact hfst.trans
        ((hGL.dist_le_mul (0,a) ha' (0,b) hb').trans_eq (by simp [Prod.dist_eq]))
    · intro q hq
      have hqr : q ∈ ball p r := lt_of_lt_of_le hq (min_le_left r s)
      have hqs : dist q p < s := lt_of_lt_of_le hq (min_le_right r s)
      ext a
      constructor
      · rintro ⟨ha,has⟩
        have hpair : (a,q) ∈ svInv (fun z ↦ {H z}) (0,q) ∩ ball (x,p) s := by
          refine ⟨?_,?_⟩
          · change (0,q) = H (a,q)
            change f (a,q) = 0 at ha
            simp only [H,ha]
          · simpa only [mem_ball,Prod.dist_eq,max_lt_iff] using And.intro has hqs
        have he : (a,q) = G (0,q) := mem_singleton_iff.mp ((hfiber (0,q) (by
          simpa only [mem_ball,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using hqr)) ▸ hpair)
        exact congrArg Prod.fst he
      · intro ha
        have he : a = g q := ha
        subst a
        have hm := hmem q hqr
        have hpair : G (0,q) = (g q,q) := by
          ext
          · rfl
          · exact hsecond q hqr
        rw [hpair] at hm
        refine ⟨?_,?_⟩
        · have he : (0,q) = H (g q,q) := hm.1
          exact (congrArg Prod.fst he).symm
        · have hd : dist (g q,q) (x,p) < s := hm.2
          rw [Prod.dist_eq] at hd
          exact (max_lt_iff.mp hd).1
  · let I : P →L[ℝ] (F × P) := (0 : P →L[ℝ] F).prod (ContinuousLinearMap.id ℝ P)
    have hchain := (ContinuousLinearMap.fst ℝ E P).hasStrictFDerivAt.comp p
      (hGd.comp p I.hasStrictFDerivAt)
    convert hchain using 1
    · ext q
      simp [I,L,ContinuousLinearMap.comp_apply,implicitBlockEquiv_symm_apply]

/-- **Theorem 9.56(d)** in the shared Euclidean-product formulation of the
implicit solution mapping. -/
theorem exists_strict_implicitSolutionMapping_localization
    {f : WithLp 2 (E × P) → F} {x : E} {p : P} {A : E ≃L[ℝ] F} {B : P →L[ℝ] F}
    (hf : HasStrictFDerivAt f (((A : E →L[ℝ] F).coprod B).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ E P).toContinuousLinearMap) (WithLp.toLp 2 (x,p)))
    (hzero : f (WithLp.toLp 2 (x,p)) = 0) :
    ∃ g : P → E, IsLipschitzSingleValuedLocalization (implicitSolutionMapping (svSingleton f)) p x g ∧
      HasStrictFDerivAt g (-((A.symm : F →L[ℝ] E).comp B)) p := by
  have hfc : HasStrictFDerivAt (fun z : E × P ↦ f (WithLp.toLp 2 z))
      ((A : E →L[ℝ] F).coprod B) (x,p) := by
    convert hf.comp (x,p) (WithLp.prodContinuousLinearEquiv 2 ℝ E P).symm.hasStrictFDerivAt using 1
  obtain ⟨g,hg,hgd⟩ := exists_strict_implicit_localization hfc hzero
  have he : (fun q ↦ {a | f (WithLp.toLp 2 (a,q)) = 0}) = implicitSolutionMapping (svSingleton f) := by
    funext q
    ext a
    simp only [implicitSolutionMapping,svSingleton,mem_setOf_eq,mem_singleton_iff,eq_comm]
  exact ⟨g,he ▸ hg,hgd⟩

end Implicit

/-- The printed positive sign in 9.56(d) is false already for `x + p = 0`:
the unique solution is `x = -p`, with derivative `-1`, not `1`. -/
theorem implicit_derivative_sign_counterexample :
    (∀ p : ℝ, {x : ℝ | x + p = 0} = {-p}) ∧
      HasStrictDerivAt (fun p : ℝ ↦ -p) (-1) 0 ∧
      ¬ HasStrictDerivAt (fun p : ℝ ↦ -p) 1 0 := by
  have hd : HasStrictDerivAt (fun p : ℝ ↦ -p) (-1) 0 := (hasStrictDerivAt_id 0).neg
  refine ⟨?_,hd,fun h ↦ ?_⟩
  · intro p
    ext x
    simp only [mem_setOf_eq,mem_singleton_iff]
    constructor <;> intro h <;> linarith
  · have he : (-1 : ℝ) = 1 := hd.hasDerivAt.unique h.hasDerivAt
    norm_num at he

end RW
