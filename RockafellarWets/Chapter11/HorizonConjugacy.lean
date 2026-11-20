/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Horizon functions and conjugate domains
-/
import RockafellarWets.Chapter11.FenchelMoreau
import RockafellarWets.Chapter3.HorizonFunctionFormulas

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The horizon of a proper conjugate is the support of the original domain.
This direction does not require convexity of the original function. -/
theorem horizon_fenchelConjugate_eq_support_domain_of_proper {f : E → EReal}
    (hp : IsProper f) (hpc : IsProper (fenchelConjugate f)) :
    horizonFunction (fenchelConjugate f) = supportFunction (effectiveDomain f) := by
  obtain ⟨v₀,hv₀⟩ := hpc.1
  let c := (fenchelConjugate f v₀).toReal
  have hc : fenchelConjugate f v₀ = (c:EReal) := (EReal.coe_toReal hv₀.ne (hpc.2 v₀).ne').symm
  apply eq_of_epigraph_eq
  ext p
  change horizonFunction (fenchelConjugate f) p.1 ≤ (p.2:EReal) ↔ _
  rw [horizonFunction_le_coe_iff_forall_ray_le (convex_epigraph_fenchelConjugate f)
    (lowerSemicontinuous_fenchelConjugate f) hpc hv₀]
  change (∀ t : ℝ, 0 < t → fenchelConjugate f (v₀+t • p.1) ≤ fenchelConjugate f v₀+((t*p.2:ℝ):EReal)) ↔
    supportFunction (effectiveDomain f) p.1 ≤ (p.2:EReal)
  rw [supportFunction_le_iff]
  constructor
  · intro hr x hx
    have hx' : f x = ((f x).toReal:EReal) := (EReal.coe_toReal hx.ne (hp.2 x).ne').symm
    apply EReal.coe_le_coe_iff.mpr
    by_contra! hbad
    let d : ℝ := ⟪x,p.1⟫_ℝ-p.2
    let k : ℝ := c-⟪v₀,x⟫_ℝ+(f x).toReal
    have hd : 0 < d := sub_pos.mpr hbad
    let t : ℝ := (|k|+1)/d
    have ht : 0 < t := div_pos (by positivity) hd
    have hh := (le_fenchelConjugate f x (v₀+t • p.1)).trans (hr t ht)
    rw [hx',hc,← EReal.coe_sub,← EReal.coe_add] at hh
    have hh' := EReal.coe_le_coe_iff.mp hh
    simp only [inner_add_left,real_inner_smul_left,real_inner_comm x p.1] at hh'
    have he : t*d = |k|+1 := div_mul_cancel₀ _ hd.ne'
    have hk : k ≤ |k| := le_abs_self k
    dsimp only [d,k] at he hk
    nlinarith
  · intro hs t ht
    apply (fenchelConjugate_le_iff _ _ _).mpr
    intro x
    by_cases htop : f x = ⊤
    · simp [htop]
    have hx : f x = ((f x).toReal:EReal) := (EReal.coe_toReal htop (hp.2 x).ne').symm
    have hm := le_fenchelConjugate f x v₀
    rw [hx,hc,← EReal.coe_sub] at hm
    have hm' := EReal.coe_le_coe_iff.mp hm
    have hs' := EReal.coe_le_coe_iff.mp (hs x (lt_top_iff_ne_top.mpr htop))
    rw [hx,hc,← EReal.coe_sub,← EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    simp only [inner_add_left,real_inner_smul_left,real_inner_comm x p.1]
    nlinarith [mul_le_mul_of_nonneg_left hs' ht.le]

/-- **Theorem 11.5**, both symmetric support-domain identities. -/
theorem horizon_conjugate_support_identities {f : E → EReal} (hp : IsProper f)
    (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    horizonFunction f = supportFunction (effectiveDomain (fenchelConjugate f)) ∧
      horizonFunction (fenchelConjugate f) = supportFunction (effectiveDomain f) := by
  have hpc := isProper_fenchelConjugate hp hl hc
  constructor
  · have hpcc : IsProper (fenchelConjugate (fenchelConjugate f)) := by
      rw [fenchelConjugate_fenchelConjugate_eq hp hl hc]
      exact hp
    have h := horizon_fenchelConjugate_eq_support_domain_of_proper (f := fenchelConjugate f) hpc hpcc
    simpa only [fenchelConjugate_fenchelConjugate_eq hp hl hc] using h
  · exact horizon_fenchelConjugate_eq_support_domain_of_proper hp hpc

end
end RW
