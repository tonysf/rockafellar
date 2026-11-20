/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# First derivatives of PLQ functions
-/
import RockafellarWets.Chapter10.PolyhedralPieceDerivatives
import RockafellarWets.Chapter5.HorizonSetLimitsAlong

open Set Filter Topology Classical
open scoped InnerProductSpace

noncomputable section
namespace RW
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Inactive closed pieces can be removed on a neighborhood. -/
theorem plqRepresentation_eventually_min {m : ℕ} {f : E → EReal} {C : Fin m → Set E}
    {q : Fin m → QuadraticPiece E} (hC : ∀ i, IsPolyhedral (C i))
    (hdom : effectiveDomain f = ⋃ i, C i) (hf : ∀ i y, y ∈ C i → f y = (q i).eval y)
    {x : E} (hx : x ∈ effectiveDomain f) :
    ∃ hI : (Finset.univ.filter (fun i ↦ x ∈ C i)).Nonempty,
      f =ᶠ[𝓝 x] (fun y ↦ (Finset.univ.filter (fun i ↦ x ∈ C i)).inf' hI
        (fun i ↦ restrictedQuadratic (C i) (q i) y)) := by
  let I := Finset.univ.filter (fun i ↦ x ∈ C i)
  have hI : I.Nonempty := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hdom ▸ hx)
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  refine ⟨hI,?_⟩
  have he : ∀ᶠ y in 𝓝 x, ∀ i, y ∈ C i → x ∈ C i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x ∈ C i
    · exact .of_forall fun _ _ ↦ hi
    · filter_upwards [(hC i).isClosed.isOpen_compl.mem_nhds hi] with y hy hiy
      exact (hy hiy).elim
  filter_upwards [he] with y hy
  apply le_antisymm
  · apply Finset.le_inf'
    intro i hi
    by_cases hiy : y ∈ C i
    · rw [restrictedQuadratic_of_mem (q i) hiy,hf i y hiy]
    · rw [restrictedQuadratic_of_not_mem (q i) hiy]; exact le_top
  · by_cases hfy : f y = ⊤
    · rw [hfy]; exact le_top
    · obtain ⟨i,hi⟩ := mem_iUnion.mp (hdom ▸ (show y ∈ effectiveDomain f from lt_top_iff_ne_top.mpr hfy))
      have hiI : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy i hi⟩
      exact (Finset.inf'_le (fun i ↦ restrictedQuadratic (C i) (q i) y) hiI).trans_eq
        ((restrictedQuadratic_of_mem (q i) hi).trans (hf i y hi).symm)

/-- **Proposition 10.21**, the fixed-direction limit equals the subderivative. -/
theorem IsPiecewiseLinearQuadratic.hasOneSidedDirDeriv {f : E → EReal}
    (h : IsPiecewiseLinearQuadratic f) {x : E} (hx : x ∈ effectiveDomain f) (w : E) :
    HasOneSidedDirDeriv f x w (subderivative f x w) := by
  have hfin : f x = ((f x).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (h.ne_bot x)).symm
  obtain ⟨m,C,q,hC,hdom,hf⟩ := h
  obtain ⟨hI,he⟩ := plqRepresentation_eventually_min hC hdom hf hx
  have hbase : ∀ i ∈ Finset.univ.filter (fun i ↦ x ∈ C i),
      restrictedQuadratic (C i) (q i) x = ((f x).toReal : EReal) := by
    intro i hi
    rw [restrictedQuadratic_of_mem (q i) (Finset.mem_filter.mp hi).2,
      ← hf i x (Finset.mem_filter.mp hi).2]
    exact hfin
  have hd := HasOneSidedDirDeriv.finset_inf' _ hI hbase (fun i hi ↦
    hasOneSidedDirDeriv_restrictedQuadratic (hC i) (q i) (Finset.mem_filter.mp hi).2 w)
  rw [subderivative_congr_nhds he w,subderivative_finset_inf' _ hI hbase]
  exact hd.congr_nhds he.symm

/-- The subderivative agrees with the differential on each active tangent cone. -/
theorem plqRepresentation_subderivative_on_piece {m : ℕ} {f : E → EReal} {C : Fin m → Set E}
    {q : Fin m → QuadraticPiece E} (hC : ∀ i, IsPolyhedral (C i))
    (hdom : effectiveDomain f = ⋃ i, C i) (hf : ∀ i y, y ∈ C i → f y = (q i).eval y)
    {x w : E} {i : Fin m} (hxi : x ∈ C i) (hwi : w ∈ tangentCone (C i) x) :
    subderivative f x w = (fderiv ℝ (q i).eval x w : EReal) := by
  have hplq : IsPiecewiseLinearQuadratic f := ⟨m,C,q,hC,hdom,hf⟩
  have hxd : x ∈ effectiveDomain f := hdom ▸ mem_iUnion.mpr ⟨i,hxi⟩
  have hlim := ((hasDirectionalSemiderivative_iff.mp
    (((q i).contDiff 1).differentiable (by norm_num) x |>.hasFDerivAt.hasDirectionalSemiderivative w)).hasOneSidedDirDeriv).2.2
  have he : (fun t ↦ differenceQuotient f x t w) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t ↦ differenceQuotient (fun y ↦ ((q i).eval y : EReal)) x t w) := by
    filter_upwards [(hC i).eventually_ray_mem_iff hxi w] with t ht
    unfold differenceQuotient
    rw [hf i _ (ht.mpr hwi),hf i _ hxi]
  exact tendsto_nhds_unique (hplq.hasOneSidedDirDeriv hxd w).2.2 (hlim.congr' he.symm)

/-- A finite union commutes with tangent cones. -/
theorem tangentCone_finite_iUnion {ι : Type*} [Fintype ι] (C : ι → Set E) (x : E) :
    tangentCone (⋃ i, C i) x = ⋃ i, tangentCone (C i) x := by
  have hunion (A B : Set E) : tangentCone (A ∪ B) x = tangentCone A x ∪ tangentCone B x := by
    simp only [tangentCone_eq_outerSetLimitAlong]
    have he : blowUp (A ∪ B) x = fun t ↦ blowUp A x t ∪ blowUp B x t := by
      funext t
      exact image_union _ _ _
    rw [he,outerSetLimitAlong_union]
  have hempty : tangentCone (∅ : Set E) x = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro w ⟨a,t,ha,_⟩
    exact ha 0
  have hfin (s : Finset ι) : tangentCone (⋃ i ∈ s, C i) x = ⋃ i ∈ s, tangentCone (C i) x := by
    induction s using Finset.induction_on with
    | empty => simp [hempty]
    | @insert i s hi ih => simp [hunion,ih]
  simpa using hfin Finset.univ

/-- **Proposition 10.21**: the subderivative is piecewise linear, with
effective domain exactly the tangent cone to the original domain. -/
theorem IsPiecewiseLinearQuadratic.subderivative_piecewiseLinear {f : E → EReal}
    (h : IsPiecewiseLinearQuadratic f) {x : E} (hx : x ∈ effectiveDomain f) :
    IsPiecewiseLinear (subderivative f x) ∧
      effectiveDomain (subderivative f x) = tangentCone (effectiveDomain f) x := by
  have hfin : f x = ((f x).toReal : EReal) := (EReal.coe_toReal (ne_of_lt hx) (h.ne_bot x)).symm
  obtain ⟨m,C,q,hC,hdom,hf⟩ := h
  let K (i : Fin m) : Set E := if x ∈ C i then tangentCone (C i) x else ∅
  have hK (i : Fin m) : IsPolyhedral (K i) := by
    dsimp [K]
    split_ifs with hi
    · exact (hC i).isPolyhedral_tangentCone hi
    · exact IsPolyhedral.empty
  have hvalue (i : Fin m) (w : E) (hw : w ∈ K i) :
      subderivative f x w = (fderiv ℝ (q i).eval x w : EReal) := by
    by_cases hi : x ∈ C i
    · exact plqRepresentation_subderivative_on_piece hC hdom hf hi (by simpa [K,hi] using hw)
    · simp [K,hi] at hw
  have hdomain : effectiveDomain (subderivative f x) = ⋃ i, K i := by
    ext w
    constructor
    · intro hw
      obtain ⟨hI,he⟩ := plqRepresentation_eventually_min hC hdom hf hx
      have hbase : ∀ i ∈ Finset.univ.filter (fun i ↦ x ∈ C i),
          restrictedQuadratic (C i) (q i) x = ((f x).toReal : EReal) := by
        intro i hi
        rw [restrictedQuadratic_of_mem (q i) (Finset.mem_filter.mp hi).2,
          ← hf i x (Finset.mem_filter.mp hi).2]
        exact hfin
      have hsub := (subderivative_congr_nhds he w).trans (subderivative_finset_inf' _ hI hbase)
      obtain ⟨i,hi,heq⟩ := Finset.exists_mem_eq_inf' hI (fun i ↦ subderivative (restrictedQuadratic (C i) (q i)) x w)
      have hxi := (Finset.mem_filter.mp hi).2
      have hwi : w ∈ tangentCone (C i) x := by
        by_contra hn
        have htop : subderivative f x w = ⊤ := by rw [hsub,heq,subderivative_restrictedQuadratic (q i) hxi w,if_neg hn]
        exact (ne_of_lt hw) htop
      exact mem_iUnion.mpr ⟨i,by simpa [K,hxi] using hwi⟩
    · intro hw
      obtain ⟨i,hi⟩ := mem_iUnion.mp hw
      change subderivative f x w < ⊤
      rw [hvalue i w hi]
      exact EReal.coe_lt_top _
  refine ⟨⟨m,K,fun i ↦ gradient (q i).eval x,fun _ ↦ 0,hK,hdomain,?_⟩,?_⟩
  · intro i w hw
    rw [hvalue i w hw,add_zero,
      inner_gradient_left (((q i).contDiff 1).differentiable (by norm_num) x)]
  · rw [hdomain,hdom,tangentCone_finite_iUnion]
    apply iUnion_congr
    intro i
    by_cases hi : x ∈ C i
    · simp [K,hi]
    · simp only [K,if_neg hi]
      symm
      apply eq_empty_iff_forall_notMem.mpr
      rintro w ⟨a,t,ha,hat,_⟩
      exact hi ((hC i).isClosed.mem_of_tendsto hat (.of_forall ha))

end RW
end
