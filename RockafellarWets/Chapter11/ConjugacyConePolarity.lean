/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugacy as cone polarity
-/
import RockafellarWets.Chapter11.ConjugacyConeGeometry

open Set
open scoped InnerProductSpace
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The polar of the homogenized epigraph is the interchanged homogenized
epigraph of its conjugate. Properness of the original and its conjugate is
sufficient here; no closure of the original epigraph is assumed. -/
theorem polarCone_conjugacyPrimalCone {f : E → EReal}
    (hp : IsProper f) (hpc : IsProper (fenchelConjugate f)) :
    polarCone (conjugacyPrimalCone f) = conjugacyDualCone (fenchelConjugate f) := by
  have hne : (epigraph (fenchelConjugate f)).Nonempty := by
    obtain ⟨v,hv⟩ := hpc.1
    obtain ⟨b,hb,_⟩ := EReal.exists_between_coe_real hv
    exact ⟨(v,b),hb.le⟩
  have hH := epigraph_horizonFunction_eq_horizonCone_epigraph hne
  have hhor := horizon_fenchelConjugate_eq_support_domain_of_proper hp hpc
  ext q
  rw [mem_polar_conjugacyPrimalCone_iff]
  constructor
  · intro h
    obtain ⟨x₀,hx₀⟩ := hp.1
    obtain ⟨a₀,ha₀,_⟩ := EReal.exists_between_coe_real hx₀
    have hsign : q.snd.fst ≤ 0 := by
      by_contra! hpos
      let c := ⟪q.fst,x₀⟫_ℝ+q.snd.fst*a₀-q.snd.snd
      let t := (|c|+1)/q.snd.fst
      have ht : 0 < t := div_pos (by positivity) hpos
      have hh := h x₀ (a₀+t) (ha₀.le.trans (EReal.coe_le_coe_iff.mpr (by linarith)))
      have he : q.snd.fst*t = |c|+1 := mul_div_cancel₀ _ hpos.ne'
      have hc : -c ≤ |c| := neg_le_abs c
      dsimp [c] at hc
      nlinarith
    rcases eq_or_lt_of_le hsign with hzero | hneg
    · change ((q.fst,q.snd.snd),q.snd.fst) ∈ raySpaceCone _ _
      rw [hzero,mem_raySpaceCone_zero_iff,← hH]
      change horizonFunction (fenchelConjugate f) q.fst ≤ (q.snd.snd:EReal)
      rw [hhor,supportFunction_le_iff]
      intro x hx
      obtain ⟨a,ha,_⟩ := EReal.exists_between_coe_real hx
      have hh := h x a ha.le
      rw [hzero,zero_mul,add_zero] at hh
      exact EReal.coe_le_coe_iff.mpr (by simpa only [real_inner_comm] using (sub_nonpos.mp hh))
    · let μ : ℝ := -q.snd.fst
      have hμ : 0 < μ := neg_pos.mpr hneg
      have hbound : fenchelConjugate f (μ⁻¹ • q.fst) ≤ ((q.snd.snd/μ:ℝ):EReal) := by
        rw [fenchelConjugate_le_coe_iff_epigraph]
        intro p hp'
        have hh := h p.1 p.2 hp'
        change ⟪μ⁻¹ • q.fst,p.1⟫_ℝ-p.2 ≤ q.snd.snd/μ
        rw [real_inner_smul_left]
        apply (le_div_iff₀ hμ).mpr
        have hrel : q.snd.fst = -μ := by simp [μ]
        rw [hrel] at hh
        have he : (μ⁻¹*⟪q.fst,p.1⟫_ℝ)*μ = ⟪q.fst,p.1⟫_ℝ := by field_simp
        nlinarith
      refine Or.inl ⟨(μ⁻¹ • q.fst,q.snd.snd/μ),hbound,μ,hμ,?_⟩
      apply Prod.ext
      · apply Prod.ext
        · change q.fst = μ • (μ⁻¹ • q.fst)
          simp [smul_smul,hμ.ne']
        · change q.snd.snd = μ*(q.snd.snd/μ)
          rw [mul_div_cancel₀ _ hμ.ne']
      · change q.snd.fst = -μ
        simp [μ]
  · intro h x a ha
    rcases h with ⟨p,hp',μ,hμ,he⟩ | ⟨hq,hzero⟩
    · have hx : ((⟪p.1,x⟫_ℝ-p.2:ℝ):EReal) ≤ f x :=
        (fenchelConjugate_le_coe_iff f p.1 p.2).mp hp' x
      have hh := EReal.coe_le_coe_iff.mp (hx.trans ha)
      have hfst : q.fst = μ • p.1 := congrArg (fun r : (E × ℝ) × ℝ ↦ r.1.1) he
      have hsnd : q.snd.snd = μ*p.2 := congrArg (fun r : (E × ℝ) × ℝ ↦ r.1.2) he
      have hscale : q.snd.fst = -μ := congrArg Prod.snd he
      rw [hfst,hsnd,hscale,real_inner_smul_left]
      nlinarith [mul_nonneg hμ.le (sub_nonneg.mpr hh)]
    · have hzero' : q.snd.fst = 0 := hzero
      rw [← hH] at hq
      change horizonFunction (fenchelConjugate f) q.fst ≤ (q.snd.snd:EReal) at hq
      rw [hhor,supportFunction_le_iff] at hq
      have hh := EReal.coe_le_coe_iff.mp (hq x (ha.trans_lt (EReal.coe_lt_top a)))
      rw [hzero',zero_mul,add_zero]
      simpa only [real_inner_comm] using sub_nonpos.mpr hh

end
end RW
