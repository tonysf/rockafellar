/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Coderivatives under strictly differentiable addition

The limiting-normal formula needs a closed-graph hypothesis on the
set-valued summand when the perturbation is only strictly differentiable
at the base point.
-/
import RockafellarWets.Chapter10.FiniteSumQualifications
import RockafellarWets.Chapter10.GraphicalAddition
import RockafellarWets.Chapter10.GraphGerms
import RockafellarWets.Chapter9.SingleValuedStrictDifferentiability

open Filter Set Topology
open scoped Pointwise

namespace RW
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {S : E → Set F} {f : E → F} {x : E} {u : F} {A : E →L[ℝ] F}

theorem svFiniteSum_fin_two (S T : E → Set F) : svFiniteSum (![S,T] : Fin 2 → E → Set F) = svAdd S T := by
  funext a
  change finiteSetSum (fun i : Fin 2 ↦ (![S,T] : Fin 2 → E → Set F) i a) = S a+T a
  have he : (fun i : Fin 2 ↦ (![S,T] : Fin 2 → E → Set F) i a) = ![S a,T a] := by
    funext i; fin_cases i <;> rfl
  rw [he,finiteSetSum_fin_two]

theorem svOsc_svAdd_single (hS : SvOsc S) (hf : Continuous f) : SvOsc (svAdd S (svSingleton f)) := by
  apply isClosed_svGraph_iff_svOsc.mp
  have he : svGraph (svAdd S (svSingleton f)) = (fun p : E × F ↦ (p.1,p.2-f p.1)) ⁻¹' svGraph S := by
    ext p
    exact mem_svAdd_single
  rw [he]
  exact (isClosed_svGraph_iff_svOsc.mpr hS).preimage
    (continuous_fst.prodMk (continuous_snd.sub (hf.comp continuous_fst)))

private theorem coderivative_svAdd_single_subset_of_continuous (hS : SvOsc S) (hc : Continuous f)
    (hf : HasStrictFDerivAt f A x) (y : F) :
    coderivative (svAdd S (svSingleton f)) x (u+f x) y ⊆ coderivative S x u y+{A.adjoint y} := by
  let T : Fin 2 → E → Set F := ![S,svSingleton f]
  have hT : ∀ i, SvOsc (T i) := by
    intro i; fin_cases i
    · exact hS
    · exact fun _ ↦ svOscAt_svSingleton_of_continuousAt hc.continuousAt
  have hb : SvLocallyBoundedAt (finiteSumMappingAux T) (x,u+f x) := by
    apply finiteSumMappingAux_locallyBounded_of_all_but_one (0 : Fin 2)
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · exact svLocallyBoundedAt_svSingleton_of_continuousAt hf.continuousAt
  have hQ : ∀ q ∈ finiteSumMappingAux T (x,u+f x), FiniteSumCoderivativeQualification T x q := by
    intro q hq
    apply finiteSumCoderivativeQualification_of_all_but_one_aubin (0 : Fin 2)
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · have he : q 1 = f x := hq.1 1
      change HasAubinPropertyAt (svSingleton f) x (q 1)
      rw [he]
      exact (strictlyContinuousAt_iff.mpr hf.exists_lipschitzOnWith).hasAubinProperty_singleton
  intro v hv
  have he : svFiniteSum T = svAdd S (svSingleton f) := svFiniteSum_fin_two _ _
  rw [← he] at hv
  obtain ⟨q,hq,hv⟩ := mem_iUnion₂.mp (coderivative_svFiniteSum_subset hT hb hQ y hv)
  have hq1 : q 1 = f x := hq.1 1
  have hq0 : q 0 = u := by
    have hh := hq.2
    rw [Fin.sum_univ_two,hq1] at hh
    exact add_right_cancel hh
  have hfun : (fun i ↦ coderivative (T i) x (q i) y) =
      (![coderivative S x u y,{A.adjoint y}] : Fin 2 → Set E) := by
    funext i
    fin_cases i
    · change coderivative S x (q 0) y = coderivative S x u y
      rw [hq0]
    · change coderivative (svSingleton f) x (q 1) y = {A.adjoint y}
      rw [hq1,coderivative_singleton_of_hasStrictFDerivAt hf]
      rfl
  rwa [hfun,finiteSetSum_fin_two] at hv

private theorem coderivative_svAdd_single_of_continuous (hS : SvOsc S) (hc : Continuous f)
    (hf : HasStrictFDerivAt f A x) (y : F) :
    coderivative (svAdd S (svSingleton f)) x (u+f x) y = coderivative S x u y+{A.adjoint y} := by
  apply Subset.antisymm (coderivative_svAdd_single_subset_of_continuous hS hc hf y)
  rintro v ⟨z,hz,b,hb,rfl⟩
  have hb' : b = A.adjoint y := hb
  subst b
  have hcancel : svAdd (svAdd S (svSingleton f)) (svSingleton (fun a ↦ -f a)) = S := by
    funext a
    ext b
    simp only [mem_svAdd_single,sub_neg_eq_add,add_sub_cancel_right]
  have hh := coderivative_svAdd_single_subset_of_continuous (u := u+f x)
    (svOsc_svAdd_single hS hc) hc.neg hf.neg y
  rw [hcancel,add_neg_cancel_right] at hh
  obtain ⟨a,ha,b,hb,he⟩ := hh hz
  have hb' : b = -A.adjoint y := by simpa only [map_neg,ContinuousLinearMap.neg_apply] using hb
  have ha' : a = z+A.adjoint y := by rw [hb'] at he; apply eq_add_of_sub_eq; simpa only [sub_eq_add_neg] using he
  simpa only [ha'] using ha

/-- **Exercise 10.43(b)**, the coderivative identity with a closed graph.
The perturbation needs a strict derivative only at the base point. -/
theorem coderivative_svAdd_single_of_svOsc (hS : SvOsc S)
    (hf : HasStrictFDerivAt f A x) (y : F) :
    coderivative (svAdd S (svSingleton f)) x (u+f x) y = coderivative S x u y+{A.adjoint y} := by
  have hfc : StrictlyContinuousAt f x := strictlyContinuousAt_iff.mpr hf.exists_lipschitzOnWith
  obtain ⟨g,k,hg,he⟩ := hfc.exists_global_lipschitz_germ
  have hgD : HasStrictFDerivAt g A x := hf.congr_of_eventuallyEq he
  have headd : svAdd S (svSingleton f) =ᶠ[𝓝 x] svAdd S (svSingleton g) := by
    filter_upwards [he] with a ha
    simp only [svAdd,svSingleton,ha]
  rw [coderivative_congr_nhds headd,he.eq_of_nhds]
  exact coderivative_svAdd_single_of_continuous hS hg.continuous hgD y

/-- The corrected rule only needs closedness near the graph point. -/
theorem coderivative_svAdd_single_of_locallyClosed
    (hS : IsLocallyClosedAt (svGraph S) (x,u))
    (hf : HasStrictFDerivAt f A x) (y : F) :
    coderivative (svAdd S (svSingleton f)) x (u+f x) y = coderivative S x u y+{A.adjoint y} := by
  obtain ⟨V,hV,_,hc⟩ := hS
  let T : E → Set F := fun a ↦ {b | (a,b) ∈ svGraph S ∩ V}
  have hT : SvOsc T := isClosed_svGraph_iff_svOsc.mp hc
  have he : svGraph S =ᶠ[𝓝 (x,u)] svGraph T := by
    filter_upwards [hV] with p hp
    change (p.2 ∈ S p.1) = (p.2 ∈ S p.1 ∧ p ∈ V)
    simp only [hp,and_true]
  have hψ : ContinuousAt (fun p : E × F ↦ (p.1,p.2-f p.1)) (x,u+f x) :=
    continuous_fst.continuousAt.prodMk
      (continuous_snd.continuousAt.sub (hf.continuousAt.comp continuous_fst.continuousAt))
  have headd : svGraph (svAdd S (svSingleton f)) =ᶠ[𝓝 (x,u+f x)]
      svGraph (svAdd T (svSingleton f)) := by
    have hh : ∀ᶠ p : E × F in 𝓝 (x,u+f x),
        svGraph S (p.1,p.2-f p.1) = svGraph T (p.1,p.2-f p.1) := by
      have ht : Tendsto (fun p : E × F ↦ (p.1,p.2-f p.1)) (𝓝 (x,u+f x)) (𝓝 (x,u)) := by
        simpa only [add_sub_cancel_right] using hψ.tendsto
      exact ht.eventually he
    filter_upwards [hh] with p hp
    change (p.2 ∈ svAdd S (svSingleton f) p.1) = (p.2 ∈ svAdd T (svSingleton f) p.1)
    simp only [mem_svAdd_single]
    exact hp
  rw [coderivative_congr_graph_nhds headd,coderivative_congr_graph_nhds he]
  exact coderivative_svAdd_single_of_svOsc hT hf y

end RW
