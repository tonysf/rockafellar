/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General convex hull functions and their closed epigraphs
-/
import RockafellarWets.Chapter3.ConvexHullFunctions
import RockafellarWets.Chapter3.LowerClosureProperness
import RockafellarWets.Chapter7.EpiLimitProperties

open Set Filter Topology
open scoped Pointwise
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strictly above the convex hull function one lies in the convexified epigraph. -/
theorem mem_convexHull_epigraph_of_lt {f : E → EReal} {x : E} {a : ℝ}
    (h : convexHullFunction f x < (a:EReal)) : (x,a) ∈ convexHull ℝ (epigraph f) := by
  obtain ⟨b,hb⟩ := iInf_lt_iff.mp h
  have hab : (b:ℝ) < a := EReal.coe_lt_coe_iff.mp hb
  have hm := add_nonnegative_vertical_mem_convexHull_epigraph
    (f := f) (p := (x,(b:ℝ))) (d := a-(b:ℝ)) b.property (sub_nonneg.mpr hab.le)
  simpa using hm

theorem epigraph_convexHullFunction_subset_closure (f : E → EReal) :
    epigraph (convexHullFunction f) ⊆ closure (convexHull ℝ (epigraph f)) := by
  rintro ⟨x,a⟩ h
  have ht : Tendsto (fun n : ℕ ↦ (x,a+((n:ℝ)+1)⁻¹)) atTop (𝓝 (x,a)) := by
    apply tendsto_const_nhds.prodMk_nhds
    simpa only [one_div,add_zero] using (tendsto_const_nhds (x := a)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply isClosed_closure.mem_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro n
  apply subset_closure
  apply mem_convexHull_epigraph_of_lt
  exact h.trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right a (by positivity)))

theorem closure_epigraph_convexHullFunction (f : E → EReal) :
    closure (epigraph (convexHullFunction f)) = closure (convexHull ℝ (epigraph f)) :=
  Subset.antisymm (closure_minimal (epigraph_convexHullFunction_subset_closure f) isClosed_closure)
    (closure_mono (convexHull_epigraph_subset_epigraph_convexHullFunction f))

/-- Convexification is convex without coercivity or properness assumptions. -/
theorem convex_epigraph_convexHullFunction (f : E → EReal) :
    Convex ℝ (epigraph (convexHullFunction f)) := by
  intro p hp q hq t s ht hs hts
  let r : ℝ := t*p.2+s*q.2
  have hlim : Tendsto (fun n : ℕ ↦ ((r+((n:ℝ)+1)⁻¹:ℝ):EReal)) atTop (𝓝 (r:EReal)) := by
    apply continuous_coe_real_ereal.continuousAt.tendsto.comp
    simpa only [one_div,add_zero] using (tendsto_const_nhds (x := r)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  change convexHullFunction f (t • p.1+s • q.1) ≤ (r:EReal)
  apply ge_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  have hpos : 0 < ((n:ℝ)+1)⁻¹ := by positivity
  have hp' := mem_convexHull_epigraph_of_lt (f := f)
    (hp.trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right p.2 hpos)))
  have hq' := mem_convexHull_epigraph_of_lt (f := f)
    (hq.trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right q.2 hpos)))
  have hh := convex_convexHull ℝ (epigraph f) hp' hq' ht hs hts
  have he : t*(p.2+((n:ℝ)+1)⁻¹)+s*(q.2+((n:ℝ)+1)⁻¹) = r+((n:ℝ)+1)⁻¹ := by
    dsimp [r]
    nlinarith [congrArg (fun z : ℝ ↦ z*((n:ℝ)+1)⁻¹) hts]
  apply convexHullFunction_le_of_mem_convexHull_epigraph
  simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,he] using hh

/-- Convexification is always a minorant, even for improper functions. -/
theorem convexHullFunction_le_all (f : E → EReal) : convexHullFunction f ≤ f :=
  epigraph_subset_epigraph_iff.mp ((subset_convexHull ℝ (epigraph f)).trans
    (convexHull_epigraph_subset_epigraph_convexHullFunction f))

theorem epigraph_epiClosure_convexHullFunction (f : E → EReal) :
    epigraph (epiClosure (convexHullFunction f)) = closure (convexHull ℝ (epigraph f)) := by
  rw [epigraph_epiClosure,closure_epigraph_convexHullFunction]

theorem convex_epigraph_epiClosure_convexHullFunction (f : E → EReal) :
    Convex ℝ (epigraph (epiClosure (convexHullFunction f))) := by
  rw [epigraph_epiClosure_convexHullFunction]
  exact (convex_convexHull ℝ (epigraph f)).closure

theorem isProper_epiClosure_convexHullFunction [FiniteDimensional ℝ E] {f : E → EReal}
    (hp : IsProper (convexHullFunction f)) : IsProper (epiClosure (convexHullFunction f)) :=
  isProper_of_isLowerClosure hp (convex_epigraph_convexHullFunction f) (epigraph_epiClosure _)

end
end RW
