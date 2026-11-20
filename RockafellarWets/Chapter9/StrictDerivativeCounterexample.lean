/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The two-parabola strict derivative example
-/

import RockafellarWets.Chapter9.StrictDerivativeSequences
import RockafellarWets.Chapter5.HorizonSetLimitsAlong

open Filter Metric Set Topology

namespace RW

/-- The mapping in Figure 9–9. -/
def twoParabola (x : ℝ) : Set ℝ := {x^2,-x^2}

private theorem tangentCone_union_realProd (C D : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    tangentCone (C ∪ D) p = tangentCone C p ∪ tangentCone D p := by
  rw [tangentCone_eq_outerSetLimitAlong (C ∪ D) p,
    tangentCone_eq_outerSetLimitAlong C p,tangentCone_eq_outerSetLimitAlong D p]
  have he : blowUp (C ∪ D) p = fun t ↦ blowUp C p t ∪ blowUp D p t := by
    funext t
    exact image_union _ _ _
  rw [he]
  exact outerSetLimitAlong_union (𝓝[>] (0:ℝ)) (blowUp C p) (blowUp D p)

private theorem mem_tangentCone_scaled_parabola {c x u w z : ℝ} :
    (w,z) ∈ tangentCone {p : ℝ × ℝ | p.2 = c*p.1^2} (x,u) ↔
      u = c*x^2 ∧ z = 2*c*x*w := by
  constructor
  · rintro ⟨a,τ,ha,hat,hτ,hτt,hqt⟩
    have hue : u = c*x^2 := tendsto_nhds_unique hat.snd_nhds
      (by simpa only [show ∀ n, (a n).2 = c*(a n).1^2 from ha] using
        (hat.fst_nhds.pow 2).const_mul c)
    have hq1 : Tendsto (fun n ↦ (τ n)⁻¹ * ((a n).1-x)) atTop (𝓝 w) := hqt.fst_nhds
    have he (n : ℕ) : (τ n)⁻¹ * ((a n).2-u) =
        c * ((a n).1+x) * ((τ n)⁻¹*((a n).1-x)) := by
      rw [ha n,hue]
      ring
    refine ⟨hue,tendsto_nhds_unique hqt.snd_nhds ?_⟩
    change Tendsto (fun n ↦ (τ n)⁻¹ * ((a n).2-u)) atTop (𝓝 (2*c*x*w))
    simp only [he]
    convert (((hat.fst_nhds.add_const x).const_mul c).mul hq1) using 1 <;> ring
  · rintro ⟨rfl,rfl⟩
    let τ : ℕ → ℝ := fun n ↦ 1/((n:ℝ)+1)
    have hτ : ∀ n, 0 < τ n := fun n ↦ by dsimp [τ]; positivity
    have hτt : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    apply mem_tangentCone_of_forall
      (xs := fun n ↦ (x+τ n*w,c*(x+τ n*w)^2)) (τs := τ)
      (fun _ ↦ rfl) hτ hτt
    have he (n : ℕ) : (τ n)⁻¹ • ((x+τ n*w,c*(x+τ n*w)^2)-(x,c*x^2)) =
        (w,2*c*x*w+c*τ n*w^2) := by
      ext
      · change (τ n)⁻¹ * ((x+τ n*w)-x) = w
        field_simp [(hτ n).ne']
        <;> ring
      · change (τ n)⁻¹ * (c*(x+τ n*w)^2-c*x^2) = 2*c*x*w+c*τ n*w^2
        field_simp [(hτ n).ne']
        <;> ring
    simp only [he]
    exact tendsto_const_nhds.prodMk_nhds (by
      simpa only [mul_zero,zero_mul,add_zero] using
        ((hτt.const_mul c).mul_const (w^2)).const_add (2*c*x*w))

/-- Every ordinary derivative of the two-parabola mapping is one linear map.
At the shared vertex the two displayed alternatives coincide. -/
theorem mem_graphicalDerivative_twoParabola {x u w z : ℝ} :
    z ∈ graphicalDerivative twoParabola x u w ↔
      (u = x^2 ∧ z = 2*x*w) ∨ (u = -x^2 ∧ z = -(2*x*w)) := by
  change (w,z) ∈ svGraph (graphicalDerivative twoParabola x u) ↔ _
  rw [svGraph_graphicalDerivative]
  have hg : svGraph twoParabola = {p : ℝ × ℝ | p.2 = 1*p.1^2} ∪
      {p : ℝ × ℝ | p.2 = (-1)*p.1^2} := by
    ext p
    simp [svGraph,twoParabola]
  rw [hg,tangentCone_union_realProd,mem_union,mem_tangentCone_scaled_parabola,
    mem_tangentCone_scaled_parabola]
  simp [neg_mul]

/-- The ordinary derivative at the vertex is the zero map. -/
theorem graphicalDerivative_twoParabola_zero (w : ℝ) :
    graphicalDerivative twoParabola 0 0 w = {0} := by
  ext z
  simp [mem_graphicalDerivative_twoParabola]

/-- The nearby ordinary derivatives satisfy a bound tending uniformly to zero
on every bounded set of input directions. -/
theorem norm_graphicalDerivative_twoParabola {x u w z : ℝ}
    (hz : z ∈ graphicalDerivative twoParabola x u w) :
    ‖z‖ = 2*‖x‖*‖w‖ := by
  rcases mem_graphicalDerivative_twoParabola.mp hz with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    simp [norm_mul]

/-- The graphical outer limit of nearby ordinary derivatives is the zero map. -/
theorem outerLimit_graphicalDerivative_twoParabola :
    outerSetLimitAlong (𝓝[svGraph twoParabola] (0,0))
      (fun p : ℝ × ℝ ↦ svGraph (graphicalDerivative twoParabola p.1 p.2)) =
      svGraph (fun _ : ℝ ↦ ({0} : Set ℝ)) := by
  ext ⟨w,z⟩
  constructor
  · intro hz
    obtain ⟨p,q,hpt,hmem,hqt⟩ := mem_outerSetLimitAlong_iff_exists_seq.mp hz
    have hp0 := hpt.mono_right nhdsWithin_le_nhds
    have he (n : ℕ) : ‖(q n).2‖ = 2*‖(p n).1‖*‖(q n).1‖ :=
      norm_graphicalDerivative_twoParabola (hmem n)
    have hnorm : Tendsto (fun n ↦ ‖(q n).2‖) atTop (𝓝 0) := by
      simpa only [he,Prod.fst_zero,norm_zero,mul_zero,zero_mul] using
        ((hp0.fst_nhds.norm.const_mul 2).mul hqt.fst_nhds.norm)
    have : ‖z‖ = 0 := tendsto_nhds_unique hqt.snd_nhds.norm hnorm
    exact norm_eq_zero.mp this
  · intro hz
    have hz0 : z = 0 := hz
    subst z
    apply mem_outerSetLimitAlong_iff_exists_seq.mpr
    exact ⟨fun _ ↦ (0,0),fun _ ↦ (w,0),
      tendsto_nhdsWithin_of_forall_mem (fun _ ↦ by simp [svGraph,twoParabola]) tendsto_const_nhds,
      fun _ ↦ by change 0 ∈ graphicalDerivative twoParabola 0 0 w; simp [graphicalDerivative_twoParabola_zero],
      tendsto_const_nhds⟩

/-- Switching between the branches yields every vertical strict direction,
although the nearby ordinary derivatives tend to the zero map. -/
theorem strictGraphicalDerivative_twoParabola_zero :
    strictGraphicalDerivative twoParabola 0 0 0 = univ := by
  have hunit : (0,1) ∈ strictTangentCone (svGraph twoParabola) (0,0) := by
    change 1 ∈ strictGraphicalDerivative twoParabola 0 0 0
    apply mem_strictGraphicalDerivative_iff_sequences.mpr
    let a : ℕ → ℝ := fun n ↦ 1/((n:ℝ)+1)
    have ha : ∀ n, 0 < a n := fun n ↦ by dsimp [a]; positivity
    have hat : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨fun n ↦ 2*(a n)^2,a,fun n ↦ -(a n)^2,fun _ ↦ 0,fun _ ↦ 1,
      fun n ↦ by positivity,by simpa using (hat.pow 2).const_mul 2,
      fun n ↦ by simp [twoParabola],hat,by simpa using (hat.pow 2).neg,
      tendsto_const_nhds,tendsto_const_nhds,?_⟩
    intro n
    rw [mem_mappingDifferenceQuotient_iff (by positivity)]
    simp only [smul_eq_mul,mul_one,mul_zero,add_zero]
    have he : -(a n)^2+2*(a n)^2 = (a n)^2 := by ring
    rw [he]
    simp [twoParabola]
  have hcone := isCone_strictTangentCone (show (0,0) ∈ svGraph twoParabola by
    simp [svGraph,twoParabola])
  apply eq_univ_of_forall
  intro z
  change (0,z) ∈ strictTangentCone (svGraph twoParabola) (0,0)
  rcases lt_trichotomy 0 z with hz | rfl | hz
  · simpa using hcone.2 hunit hz
  · exact hcone.1
  · have hneg := neg_mem_strictTangentCone (hcone.2 hunit (show 0 < -z by linarith))
    simpa using hneg

end RW
