/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugate pairs are exactly polar epigraph-cone pairs
-/
import RockafellarWets.Chapter11.ConjugacyConePolarity

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Exchange the final two coordinates in the cone representation. -/
def conjugacySwap (p : ConjugacySpace E) : ConjugacySpace E :=
  conjugacyPoint p.fst p.snd.snd p.snd.fst

@[simp] theorem conjugacySwap_involutive (p : ConjugacySpace E) :
    conjugacySwap (conjugacySwap p) = p := rfl

theorem inner_conjugacySwap (p q : ConjugacySpace E) :
    ⟪conjugacySwap p,q⟫_ℝ = ⟪p,conjugacySwap q⟫_ℝ := by
  simp [conjugacySwap,conjugacyPoint,WithLp.prod_inner_apply,add_assoc,add_comm,add_left_comm]

theorem mem_polar_conjugacyDualCone_iff (g : E → EReal) (p : ConjugacySpace E) :
    p ∈ polarCone (conjugacyDualCone g) ↔ conjugacySwap p ∈ polarCone (conjugacyPrimalCone g) := by
  constructor
  · intro h q hq
    rw [inner_conjugacySwap]
    exact h (conjugacySwap q) hq
  · intro h q hq
    have hh := h (conjugacySwap q) hq
    simpa only [inner_conjugacySwap,conjugacySwap_involutive] using hh

theorem polarCone_conjugacyDualCone {g : E → EReal}
    (hp : IsProper g) (hpc : IsProper (fenchelConjugate g)) :
    polarCone (conjugacyDualCone g) = conjugacyPrimalCone (fenchelConjugate g) := by
  ext p
  rw [mem_polar_conjugacyDualCone_iff,polarCone_conjugacyPrimalCone hp hpc]
  rfl

theorem conjugate_eq_of_primalCone_polar_eq_dualCone {f g : E → EReal}
    (h : polarCone (conjugacyPrimalCone f) = conjugacyDualCone g) :
    fenchelConjugate f = g := by
  apply eq_of_epigraph_eq
  ext p
  change fenchelConjugate f p.1 ≤ (p.2:EReal) ↔ g p.1 ≤ (p.2:EReal)
  rw [← mem_polar_conjugacyPrimalCone_dual_slice,h,mem_conjugacyDualCone_neg_one]

theorem conjugate_eq_of_dualCone_polar_eq_primalCone {f g : E → EReal}
    (h : polarCone (conjugacyDualCone g) = conjugacyPrimalCone f) :
    fenchelConjugate g = f := by
  apply conjugate_eq_of_primalCone_polar_eq_dualCone
  ext p
  have hh := congrArg (fun S : Set (ConjugacySpace E) ↦ conjugacySwap p ∈ S) h
  simpa only [mem_polar_conjugacyDualCone_iff,conjugacySwap_involutive] using (iff_of_eq hh)

/-- **Exercise 11.7**, in the Euclidean space with coordinates `(x,α,β)`.
The two stated functions are mutual conjugates exactly when their cones are
mutual polars. No convexity or semicontinuity is added to the hypotheses. -/
theorem conjugate_pair_iff_mutual_polar_cones {f g : E → EReal}
    (hp : IsProper f) (hpg : IsProper g) :
    (fenchelConjugate f = g ∧ fenchelConjugate g = f) ↔
      (polarCone (conjugacyPrimalCone f) = conjugacyDualCone g ∧
       polarCone (conjugacyDualCone g) = conjugacyPrimalCone f) := by
  constructor
  · rintro ⟨hf,hg⟩
    have hpc : IsProper (fenchelConjugate f) := hf.symm ▸ hpg
    have hpgc : IsProper (fenchelConjugate g) := hg.symm ▸ hp
    exact ⟨by rw [polarCone_conjugacyPrimalCone hp hpc,hf],
      by rw [polarCone_conjugacyDualCone hpg hpgc,hg]⟩
  · rintro ⟨hf,hg⟩
    exact ⟨conjugate_eq_of_primalCone_polar_eq_dualCone hf,
      conjugate_eq_of_dualCone_polar_eq_primalCone hg⟩

/-- The properness hypothesis ensures the horizon part of the cone is
exactly the epigraph of the horizon function appearing in the book. -/
theorem mem_conjugacyPrimalCone_iff_raySpace_horizonFunction {f : E → EReal}
    (hp : IsProper f) (p : ConjugacySpace E) :
    p ∈ conjugacyPrimalCone f ↔
      ((p.fst,p.snd.fst),p.snd.snd) ∈ raySpaceCone (epigraph f) (epigraph (horizonFunction f)) := by
  have hne : (epigraph f).Nonempty := by
    obtain ⟨x,hx⟩ := hp.1
    obtain ⟨a,ha,_⟩ := EReal.exists_between_coe_real hx
    exact ⟨(x,a),ha.le⟩
  rw [epigraph_horizonFunction_eq_horizonCone_epigraph hne]
  rfl

/-- The closed-convex cone criterion in the guide to Exercise 11.7. -/
theorem closed_convex_conjugacyPrimalCone_iff {f : E → EReal} (hp : IsProper f) :
    (IsClosed (conjugacyPrimalCone f) ∧ Convex ℝ (conjugacyPrimalCone f)) ↔
      (LowerSemicontinuous f ∧ Convex ℝ (epigraph f)) := by
  constructor
  · rintro ⟨hcl,hcv⟩
    have hslice : epigraph f = (fun p : E × ℝ ↦ conjugacyPoint p.1 p.2 (-1)) ⁻¹' conjugacyPrimalCone f := by
      ext p
      exact (mem_conjugacyPrimalCone_neg_one f p.1 p.2).symm
    have hcont : Continuous (fun p : E × ℝ ↦ conjugacyPoint p.1 p.2 (-1)) := by
      exact (WithLp.prod_continuous_toLp 2 E (WithLp 2 (ℝ × ℝ))).comp
        (continuous_fst.prodMk ((WithLp.prod_continuous_toLp 2 ℝ ℝ).comp
          (continuous_snd.prodMk continuous_const)))
    refine ⟨lowerSemicontinuous_of_isClosed_epigraph_ereal f ?_,?_⟩
    · rw [hslice]
      exact hcl.preimage hcont
    · intro p hp' q hq t s ht hs hts
      have hh := hcv ((mem_conjugacyPrimalCone_neg_one f p.1 p.2).mpr hp')
        ((mem_conjugacyPrimalCone_neg_one f q.1 q.2).mpr hq) ht hs hts
      apply (mem_conjugacyPrimalCone_neg_one f _ _).mp
      have he : t • conjugacyPoint p.1 p.2 (-1)+s • conjugacyPoint q.1 q.2 (-1) =
          conjugacyPoint (t • p.1+s • q.1) (t*p.2+s*q.2) (-1) := by
        apply WithLp.ofLp_injective
        apply Prod.ext
        · rfl
        · apply WithLp.ofLp_injective
          apply Prod.ext
          · rfl
          · change t*(-1)+s*(-1) = -1
            linarith
      simpa only [he] using hh
  · rintro ⟨hl,hc⟩
    have hpc := isProper_fenchelConjugate hp hl hc
    have hpcc : IsProper (fenchelConjugate (fenchelConjugate f)) := by
      rw [fenchelConjugate_fenchelConjugate_eq hp hl hc]
      exact hp
    have he := polarCone_conjugacyDualCone hpc hpcc
    rw [fenchelConjugate_fenchelConjugate_eq hp hl hc] at he
    rw [← he]
    exact ⟨isClosed_polarCone _,convex_polarCone _⟩

end
end RW
