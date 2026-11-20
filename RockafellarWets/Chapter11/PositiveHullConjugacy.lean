/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Positive hulls of conjugates
-/
import RockafellarWets.Chapter11.HorizonConjugacy
import RockafellarWets.Chapter11.SupportConjugates
import RockafellarWets.Chapter3.HomogeneousCompletion

open Set Filter Topology
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem positiveHullFunction_eq_iInf_perspective {g : E → EReal} {v : E} (hv : v ≠ 0) :
    positiveHullFunction g v = ⨅ t : {t : ℝ // 0 < t}, (t:ℝ) * g ((t:ℝ)⁻¹ • v) := by
  refine le_antisymm (le_iInf fun t ↦ ?_) (le_iInf fun a ↦ ?_)
  · have he := (positivelyHomogeneous_positiveHullFunction g).2 (x := (t:ℝ)⁻¹ • v) t.property
    simp only [smul_smul,mul_inv_cancel₀ t.property.ne',one_smul] at he
    rw [he]
    have ht : 0 < (t:ℝ) := t.property
    gcongr
    exact positiveHullFunction_le_apply g _
  · rcases a.property with hzero | ⟨t,ht,p,hp,he⟩
    · exact (hv (congrArg Prod.fst hzero)).elim
    · have hvp : t⁻¹ • v = p.1 := by
        have h := congrArg Prod.fst he
        change v = t • p.1 at h
        rw [h,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
      have hap : (a:ℝ) = t*p.2 := congrArg Prod.snd he
      apply (iInf_le (fun t : {t : ℝ // 0 < t} ↦ (t:ℝ) * g ((t:ℝ)⁻¹ • v)) ⟨t,ht⟩).trans
      rw [hvp,hap,EReal.coe_mul]
      gcongr
      exact hp

theorem linearMinorantSet_positiveHullFunction (g : E → EReal) :
    linearMinorantSet (positiveHullFunction g) = linearMinorantSet g := by
  ext x
  constructor
  · intro h v
    exact (h v).trans (positiveHullFunction_le_apply g v)
  · intro h
    apply le_positiveHullFunction_of_positivelyHomogeneous_of_le _ h
    refine ⟨by simp, ?_⟩
    intro v t ht
    simp [real_inner_smul_right,EReal.coe_mul]

private theorem positiveHull_vertical_lift {g : E → EReal} {x : E} {a b : ℝ}
    (hx : x ≠ 0) (ha : (x,a) ∈ positiveHull (epigraph g)) (hab : a ≤ b) :
    (x,b) ∈ positiveHull (epigraph g) := by
  rcases ha with hzero | ⟨t,ht,p,hp,he⟩
  · exact (hx (congrArg Prod.fst hzero)).elim
  · have ha' : a = t*p.2 := congrArg Prod.snd he
    refine Or.inr ⟨t,ht,(p.1,p.2+(b-a)/t),?_,?_⟩
    · exact hp.trans (EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_right
        (div_nonneg (sub_nonneg.mpr hab) ht.le)))
    · ext
      · have hh := congrArg Prod.fst he
        exact hh
      · change b = t*(p.2+(b-a)/t)
        rw [mul_add,mul_div_cancel₀ _ ht.ne',← ha']
        ring

/-- The positive hull is closed when the only horizon directions are vertical
and a finite linear minorant rules out negative heights at the origin.
Unlike the older Chapter 3 wrapper, this permits `g 0 = +∞`. -/
theorem lowerSemicontinuous_positiveHullFunction_of_vertical_horizon
    [FiniteDimensional ℝ E] {g : E → EReal} (hp : IsProper g)
    (hl : LowerSemicontinuous g) (h0 : (0:EReal) < g 0)
    (hh : horizonFunction g = indicatorVA {0})
    (hm : (linearMinorantSet g).Nonempty) :
    LowerSemicontinuous (positiveHullFunction g) := by
  obtain ⟨x₀,hx₀⟩ := hm
  have hminor : x₀ ∈ linearMinorantSet (positiveHullFunction g) := by
    rwa [linearMinorantSet_positiveHullFunction]
  have hne : (epigraph g).Nonempty := by
    obtain ⟨x,hx⟩ := hp.1
    obtain ⟨a,ha,_⟩ := EReal.exists_between_coe_real hx
    exact ⟨(x,a),ha.le⟩
  have hH : horizonCone (epigraph g) = {p : E × ℝ | p.1 = 0 ∧ 0 ≤ p.2} := by
    rw [← epigraph_horizonFunction_eq_horizonCone_epigraph hne,hh]
    ext p
    by_cases hp0 : p.1 = 0 <;> simp [epigraph,indicatorVA,hp0]
  have hclosure : closure (positiveHull (epigraph g)) =
      positiveHull (epigraph g) ∪ {p : E × ℝ | p.1 = 0 ∧ 0 ≤ p.2} := by
    rw [closure_positiveHull_eq_union_horizonCone (isClosed_epigraph_of_lsc_ereal g hl)
      (by intro hz; exact h0.not_ge hz),hH]
  have he : epigraph (positiveHullFunction g) = closure (positiveHull (epigraph g)) := by
    apply Subset.antisymm
    · rintro ⟨x,a⟩ ha
      by_cases hx : x = 0
      · rw [hclosure]
        refine Or.inr ⟨hx,?_⟩
        have h := (hminor x).trans ha
        simpa [hx] using h
      · have ht : Tendsto (fun n : ℕ ↦ (x,a+((n:ℝ)+1)⁻¹)) atTop (𝓝 (x,a)) := by
          apply tendsto_const_nhds.prodMk_nhds
          simpa only [one_div,add_zero] using (tendsto_const_nhds (x := a)).add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        apply isClosed_closure.mem_of_tendsto ht
        apply Eventually.of_forall
        intro n
        obtain ⟨b,hb,hba⟩ := exists_mem_positiveHull_epigraph_lt
          (ha.trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right a (show 0 < ((n:ℝ)+1)⁻¹ by positivity))))
        exact subset_closure (positiveHull_vertical_lift hx hb (EReal.coe_lt_coe_iff.mp hba).le)
    · rw [hclosure]
      rintro p (hp' | hp')
      · exact positiveHull_epigraph_subset_epigraph_positiveHullFunction g hp'
      · change positiveHullFunction g p.1 ≤ (p.2:EReal)
        rw [hp'.1]
        exact (positiveHullFunction_le_of_mem_positiveHull_epigraph
          (zero_mem_positiveHull (epigraph g))).trans (by exact_mod_cast hp'.2)
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  rw [he]
  exact isClosed_closure

end
end RW
