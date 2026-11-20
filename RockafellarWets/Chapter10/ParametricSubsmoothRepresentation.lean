/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The local representation and active gradients in Theorem 10.58
-/
import RockafellarWets.Chapter10.ParametricMinimizerLocalization
import RockafellarWets.Chapter10.SubsmoothFunctions

open Filter Set Topology InnerProductSpace
open scoped Pointwise

namespace RW
noncomputable section
universe u

variable {P E : Type u} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A compact family which is jointly continuous in value and partial
gradient defines a lower-C¹ representation. No derivative in the index
variable is needed. -/
def LowerRepresentation.ofContinuousPartialGradient {O : Set P} (hO : IsOpen O)
    {p : P → ℝ} (T : Type u) [TopologicalSpace T] [CompactSpace T]
    (F : T → P → ℝ) (G : T × P → P)
    (hc : ContinuousOn (fun q : T × P ↦ F q.1 q.2) (univ ×ˢ O))
    (hG : ContinuousOn G (univ ×ˢ O))
    (hd : ∀ t, ∀ x ∈ O, HasGradientAt (F t) (G (t,x)) x)
    (hle : ∀ t, ∀ x ∈ O, F t x ≤ p x) (heq : ∀ x ∈ O, ∃ t, F t x = p x) :
    LowerRepresentation 1 p O := by
  refine LowerRepresentation.mk T F (fun t ↦ ?_) (fun j hj ↦ ?_) hle heq
  · apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := (0 : WithTop ℕ∞)) hO.uniqueDiffOn).mpr
    refine ⟨by simp,fun x ↦ (toDual ℝ P) (G (t,x)),contDiffOn_zero.mpr ?_,
      fun x hx ↦ (hd t x hx).hasFDerivAt.hasFDerivWithinAt⟩
    exact (toDual ℝ P).continuous.comp_continuousOn (hG.comp
      (continuous_const.prodMk continuous_id).continuousOn (fun x hx ↦ ⟨mem_univ t,hx⟩))
  · have hj' : (j:ℕ∞) ≤ 1 := hj
    norm_cast at hj'
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · apply ((continuousMultilinearCurryFin0 ℝ P ℝ).symm.continuous.comp_continuousOn hc).congr
      intro q _
      ext m
      simp [iteratedFDeriv_zero_apply]
    · apply ((continuousMultilinearCurryFin1 ℝ P ℝ).symm.continuous.comp_continuousOn
        ((toDual ℝ P).continuous.comp_continuousOn hG)).congr
      intro q hq
      change iteratedFDeriv ℝ 1 (F q.1) q.2 = (continuousMultilinearCurryFin1 ℝ P ℝ).symm ((toDual ℝ P) (G (q.1,q.2)))
      rw [← (hd q.1 q.2 hq.2).hasFDerivAt.fderiv]
      ext m
      simp [iteratedFDeriv_one_apply]

/-- **10.58**, on an open neighborhood of the original parameter. The same
compact decision set indexes the representation throughout the neighborhood.
The negatives of its active gradients are exactly the partial gradients of
the original cost at minimizing decisions. -/
theorem exists_upperC_parametric_representation {f : E × P → EReal} {g : E × P → ℝ}
    {G : E × P → P} {V : Set E} {W : Set P} {u₀ : P} (hf : LowerSemicontinuous f)
    (hp : IsProper f) (hb : IsLevelBoundedInXLocallyUniformly f) (hu₀ : valueFunction f u₀ < ⊤)
    (hV : IsOpen V) (hW : IsOpen W) (huW : u₀ ∈ W) (hPV : paramArgmin f u₀ ⊆ V)
    (hfg : ∀ p ∈ V ×ˢ W, f p = (g p : EReal)) (hg : ContinuousOn g (V ×ˢ W))
    (hG : ContinuousOn G (V ×ˢ W))
    (hd : ∀ x ∈ V, ∀ u ∈ W, HasGradientAt (fun v ↦ g (x,v)) (G (x,u)) u) :
    ∃ O : Set P, IsOpen O ∧ u₀ ∈ O ∧ O ⊆ W ∧
      IsUpperCOn 1 (fun u ↦ (valueFunction f u).toReal) O ∧
      ∃ R : LowerRepresentation 1 (fun u ↦ -(valueFunction f u).toReal) O,
        ∀ u ∈ O, R.gradSet u = -((fun x ↦ G (x,u)) '' paramArgmin f u) := by
  obtain ⟨K,hK,hKV,O,hO,huO,hOW,H⟩ := exists_compact_decision_set hf hp hb hu₀ hV hW huW hPV hfg hg
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F (x : K) (u : P) := -g (x,u)
  let D (q : K × P) := -G (q.1,q.2)
  have hm : MapsTo (fun q : K × P ↦ ((q.1:E),q.2)) (univ ×ˢ O) (V ×ˢ W) :=
    fun q hq ↦ ⟨hKV q.1.property,hOW hq.2⟩
  have hc : Continuous (fun q : K × P ↦ ((q.1:E),q.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hd' (x : K) (u : P) (hu : u ∈ O) : HasGradientAt (F x) (D (x,u)) u := by
    change HasFDerivAt _ ((toDual ℝ P) (-G (x,u))) u
    rw [map_neg]
    exact (hd x (hKV x.property) u (hOW hu)).hasFDerivAt.neg
  have hactive (x : K) (u : P) (hu : u ∈ O) :
      F x u = -(valueFunction f u).toReal ↔ (x:E) ∈ paramArgmin f u := by
    rw [mem_paramArgmin_iff,hfg _ ⟨hKV x.property,hOW hu⟩,← (H u hu).2.1]
    simp [F,EReal.coe_lt_top]
  let R := LowerRepresentation.ofContinuousPartialGradient hO K F D
    ((hg.comp hc.continuousOn hm).neg) ((hG.comp hc.continuousOn hm).neg) hd'
    (fun x u hu ↦ by
      apply neg_le_neg
      apply EReal.coe_le_coe_iff.mp
      rw [(H u hu).2.1,← hfg _ ⟨hKV x.property,hOW hu⟩]
      exact iInf_le (fun x ↦ f (x,u)) (x:E))
    (fun u hu ↦ by
      obtain ⟨x,hx⟩ := (H u hu).2.2.1
      exact ⟨⟨x,(H u hu).2.2.2 hx⟩,(hactive _ u hu).mpr hx⟩)
  refine ⟨O,hO,huO,hOW,(fun x hx ↦ ⟨O,hO,hx,Subset.rfl,⟨R⟩⟩),R,?_⟩
  intro u hu
  ext v
  change (∃ x ∈ ({x : K | F x u = -(valueFunction f u).toReal} : Set K), gradient (F x) u = v) ↔
    -v ∈ (fun x ↦ G (x,u)) '' paramArgmin f u
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,(hactive x u hu).mp hx,by rw [(hd' x u hu).gradient]; simp [D]⟩
  · rintro ⟨x,hx,hvx⟩
    let t : K := ⟨x,(H u hu).2.2.2 hx⟩
    exact ⟨t,(hactive t u hu).mpr hx,by rw [(hd' t u hu).gradient]; simpa [D,t] using congrArg Neg.neg hvx⟩

end
end RW
