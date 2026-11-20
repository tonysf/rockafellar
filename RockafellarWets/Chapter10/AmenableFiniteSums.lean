/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite sums of amenable functions
-/
import RockafellarWets.Chapter10.AmenableHorizonDomain
import RockafellarWets.Chapter10.DependentSeparableSubgradients
import RockafellarWets.Chapter10.PLQFiniteCalculus

open Set Filter Topology Classical
open scoped InnerProductSpace BigOperators

noncomputable section
namespace RW
universe u

section Product
variable {ι : Type u} [Fintype ι] {F : ι → Type u}
  [∀i, NormedAddCommGroup (F i)] [∀i, InnerProductSpace ℝ (F i)]
  [∀i, FiniteDimensional ℝ (F i)]

theorem effectiveDomain_dependentSeparablePi {g : ∀i, F i → EReal} (hp : ∀i, IsProper (g i)) :
    effectiveDomain (dependentSeparablePi g) = l2PiSet (fun i ↦ effectiveDomain (g i)) := by
  ext v
  change (∑i,g i (v i)) < ⊤ ↔ ∀i,g i (v i) < ⊤
  have hbot (s : Finset ι) : ⊥ < ∑i ∈ s,g i (v i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => rw [Finset.sum_insert hi]; exact EReal.bot_lt_add_iff.mpr ⟨(hp i).2 _,ih⟩
  have hsum (s : Finset ι) : (∑i ∈ s,g i (v i)) < ⊤ ↔ ∀i ∈ s,g i (v i) < ⊤ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hb : (∑j ∈ s,g j (v j)) ≠ ⊥ := (hbot s).ne'
      have he : g i (v i)+(∑j ∈ s,g j (v j)) < ⊤ ↔ g i (v i) < ⊤ ∧ (∑j ∈ s,g j (v j)) < ⊤ := by
        constructor
        · intro h
          constructor
          · by_contra hn
            have hz : g i (v i) = ⊤ := top_unique (not_lt.mp hn)
            rw [hz,EReal.top_add_of_ne_bot hb] at h
            exact lt_irrefl _ h
          · by_contra hn
            have hz : (∑j ∈ s,g j (v j)) = ⊤ := top_unique (not_lt.mp hn)
            rw [hz,EReal.add_top_of_ne_bot ((hp i).2 _).ne'] at h
            exact lt_irrefl _ h
        · rintro ⟨h,k⟩; exact EReal.add_lt_top h.ne k.ne
      simpa only [he,ih,Finset.mem_insert,forall_eq_or_imp]
  simpa using hsum Finset.univ

theorem closure_l2PiSet (C : ∀i, Set (F i)) :
    closure (l2PiSet C) = l2PiSet (fun i ↦ closure (C i)) := by
  have he (K : ∀i, Set (F i)) : l2PiSet K =
      (PiLp.continuousLinearEquiv 2 ℝ F).toHomeomorph ⁻¹' (Set.pi univ K) := by
    ext v
    change (∀i,v i ∈ K i) ↔ ∀i ∈ (univ : Set ι),v i ∈ K i
    simp
  rw [he,← Homeomorph.preimage_closure,closure_pi_set,← he]

theorem convex_epigraph_dependentSeparablePi {g : ∀i, F i → EReal}
    (hp : ∀i, IsProper (g i)) (hc : ∀i, Convex ℝ (epigraph (g i))) :
    Convex ℝ (epigraph (dependentSeparablePi g)) := by
  have hb (s : Finset ι) (v : PiLp 2 F) : (∑i ∈ s,g i (v i)) ≠ ⊥ := by
    have hh : ⊥ < ∑i ∈ s,g i (v i) := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih => rw [Finset.sum_insert hi]; exact EReal.bot_lt_add_iff.mpr ⟨(hp i).2 _,ih⟩
    exact hh.ne'
  unfold dependentSeparablePi
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    intro p hp q hq a b ha hb hab
    change (0:EReal) ≤ ((a*p.2+b*q.2:ℝ):EReal)
    have hp0 : (0:ℝ) ≤ p.2 := EReal.coe_le_coe_iff.mp hp
    have hq0 : (0:ℝ) ≤ q.2 := EReal.coe_le_coe_iff.mp hq
    exact EReal.coe_le_coe_iff.mpr (add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hci : Convex ℝ (epigraph (fun v : PiLp 2 F ↦ g i (v i))) := by
      simpa using convex_epigraph_compAffine (hc i) (PiLp.proj (𝕜 := ℝ) 2 F i) 0
    exact convex_epigraph_add_of_ne_bot hci ih (fun v ↦ ((hp i).2 _).ne') (hb s)

end Product

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type u} [Fintype ι]

/-- The product construction for qualified finite sums preserves the
smoothness order and the PLQ outer representation. -/
def AmenableFunctionModel.finiteSum {f : ι → E → EReal} {x : E} {r : ℕ} {full : Bool}
    (M : ∀i,AmenableFunctionModel (f i) x r full) (hr : 1 ≤ r)
    (hQ : ∀v : ι → E, (∀i,v i ∈ normalCone (effectiveDomain (f i)) x) →
      ∑i,v i = 0 → ∀i,v i = 0) : AmenableFunctionModel (fun y ↦ ∑i,f i y) x r full where
  Target := PiLp 2 (fun i ↦ (M i).Target)
  outer := dependentSeparablePi (fun i ↦ (M i).outer)
  inner := fun y ↦ WithLp.toLp 2 (fun i ↦ (M i).inner y)
  neighborhood := ⋂i,(M i).neighborhood
  isOpen := isOpen_iInter_of_finite (fun i ↦ (M i).isOpen)
  mem := mem_iInter.mpr (fun i ↦ (M i).mem)
  finite := by
    have hh : (∑i,f i x) = ((∑i,(f i x).toReal:ℝ):EReal) :=
      dependentSeparablePi_eq_coe (f := f) (x := WithLp.toLp 2 (fun _ ↦ x))
        (fun i ↦ (EReal.coe_toReal (M i).finite.2 (M i).finite.1).symm)
    rw [hh]
    exact ⟨EReal.coe_ne_bot _,EReal.coe_ne_top _⟩
  proper := isProper_dependentSeparablePi (fun i ↦ (M i).proper)
  lsc := lowerSemicontinuous_dependentSeparablePi (fun i ↦ (M i).lsc) (fun i ↦ (M i).proper.2)
  convex := convex_epigraph_dependentSeparablePi (fun i ↦ (M i).proper) (fun i ↦ (M i).convex)
  smooth := (PiLp.continuousLinearEquiv 2 ℝ (fun i ↦ (M i).Target)).symm.contDiff.contDiffOn.comp
    (contDiffOn_pi.mpr (fun i ↦ (M i).smooth.mono (iInter_subset _ i))) (fun _ _ ↦ mem_univ _)
  eqOn := by
    intro y hy
    exact Finset.sum_congr rfl (fun i _ ↦ (M i).eqOn y (mem_iInter.mp hy i))
  qualification := by
    intro v hv hz
    rw [effectiveDomain_dependentSeparablePi (fun i ↦ (M i).proper),closure_l2PiSet,normalCone_l2PiSet] at hv
    have hmd (i : ι) := (((M i).smooth x (M i).mem).contDiffAt ((M i).isOpen.mem_nhds (M i).mem)).differentiableAt
      (by exact_mod_cast (show r ≠ 0 by omega))
    have hd := (PiLp.continuousLinearEquiv 2 ℝ (fun i ↦ (M i).Target)).symm.toContinuousLinearMap.hasFDerivAt.comp x
      (hasFDerivAt_pi.mpr (fun i ↦ (hmd i).hasFDerivAt))
    change HasFDerivAt (fun y ↦ WithLp.toLp 2 (fun i ↦ (M i).inner y)) _ x at hd
    have ha : (fderiv ℝ (fun y ↦ WithLp.toLp 2 (fun i ↦ (M i).inner y)) x).adjoint v =
        ∑i,(fderiv ℝ (M i).inner x).adjoint (v i) := by
      rw [hd.fderiv]
      apply ext_inner_right ℝ
      intro w
      rw [ContinuousLinearMap.adjoint_inner_left]
      simp only [sum_inner,ContinuousLinearMap.adjoint_inner_left]
      change ⟪v,WithLp.toLp 2 (fun i ↦ fderiv ℝ (M i).inner x w)⟫_ℝ = _
      simp [PiLp.inner_apply]
    rw [ha] at hz
    have hn (i : ι) : (fderiv ℝ (M i).inner x).adjoint (v i) ∈ normalCone (effectiveDomain (f i)) x := by
      rw [← (M i).horizon_eq_normal_domain hr,((M i).derivatives hr).2.1]
      refine ⟨v i,?_,rfl⟩
      rw [horizonSubdifferential_eq_normalCone_closure_domain (M i).proper (M i).lsc (M i).convex
        (c := (f i x).toReal) (by rw [← (M i).eqOn x (M i).mem]; exact (EReal.coe_toReal (M i).finite.2 (M i).finite.1).symm)]
      exact hv i
    have hh := hQ (fun i ↦ (fderiv ℝ (M i).inner x).adjoint (v i)) hn hz
    ext i
    exact (M i).qualification (v i) (hv i) (hh i)
  plq := by
    intro hf
    apply IsPiecewiseLinearQuadratic.sum Finset.univ
    intro i _
    simpa using ((M i).plq hf).compAffine (PiLp.proj (𝕜 := ℝ) 2 (fun i ↦ (M i).Target) i) 0

theorem AmenableAt.finiteSum {f : ι → E → EReal} {x : E}
    (hf : ∀i,AmenableAt (f i) x)
    (hQ : ∀v : ι → E, (∀i,v i ∈ normalCone (effectiveDomain (f i)) x) → ∑i,v i = 0 → ∀i,v i = 0) :
    AmenableAt (fun y ↦ ∑i,f i y) x :=
  ⟨AmenableFunctionModel.finiteSum (fun i ↦ Classical.choice (hf i)) le_rfl hQ⟩

theorem StronglyAmenableAt.finiteSum {f : ι → E → EReal} {x : E}
    (hf : ∀i,StronglyAmenableAt (f i) x)
    (hQ : ∀v : ι → E, (∀i,v i ∈ normalCone (effectiveDomain (f i)) x) → ∑i,v i = 0 → ∀i,v i = 0) :
    StronglyAmenableAt (fun y ↦ ∑i,f i y) x :=
  ⟨AmenableFunctionModel.finiteSum (fun i ↦ Classical.choice (hf i)) (by norm_num) hQ⟩

theorem FullyAmenableAt.finiteSum {f : ι → E → EReal} {x : E}
    (hf : ∀i,FullyAmenableAt (f i) x)
    (hQ : ∀v : ι → E, (∀i,v i ∈ normalCone (effectiveDomain (f i)) x) → ∑i,v i = 0 → ∀i,v i = 0) :
    FullyAmenableAt (fun y ↦ ∑i,f i y) x :=
  ⟨AmenableFunctionModel.finiteSum (fun i ↦ Classical.choice (hf i)) (by norm_num) hQ⟩

end RW
end
