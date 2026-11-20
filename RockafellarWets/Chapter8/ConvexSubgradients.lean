/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subgradients of convex functions

At a finite point of a proper convex function, the regular and limiting
subgradients are precisely the slopes of its affine supports at that point.
-/

import RockafellarWets.Chapter8.HorizontalEpigraphNormals
import RockafellarWets.Chapter7.ConvexEpiConvergence

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → EReal} {x v : E} {c : ℝ}

/-- **Proposition 8.12**, the convex support inequality at a finite point. -/
theorem mem_regularSubdifferential_iff_of_convex (hc : Convex ℝ (epigraph f)) (hp : IsProper f)
    (hx : f x = c) : v ∈ regularSubdifferential f x ↔
      ∀ z, ((c + ⟪v,z-x⟫_ℝ : ℝ) : EReal) ≤ f z := by
  rw [mem_regularSubdifferential_iff_epigraph_normal hx]
  have hcp : Convex ℝ (euclideanEpigraph f) := convex_preimage_continuousLinearEquiv
    (l2ProdEquiv E) hc
  rw [regularNormalCone_eq_of_convex hcp (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le)]
  constructor
  · intro hn z
    by_cases hzt : f z = ⊤
    · simp [hzt]
    have hzr := EReal.coe_toReal hzt (hp.2 z).ne'
    have h := hn (WithLp.toLp 2 (z,(f z).toReal)) (show f z ≤ _ from hzr.ge)
    change ⟪v,z-x⟫_ℝ + ((f z).toReal-c) * (-1) ≤ 0 at h
    rw [← hzr]
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  · intro h p hp'
    obtain ⟨⟨z,r⟩, rfl⟩ := (WithLp.toLp_surjective 2) p
    change f z ≤ (r : EReal) at hp'
    change ⟪v,z-x⟫_ℝ + (r-c) * (-1) ≤ 0
    linarith [EReal.coe_le_coe_iff.mp ((h z).trans hp')]

/-- **Proposition 8.12**, attentive limits of supporting slopes still satisfy
the global support inequality. -/
theorem mem_subdifferential_iff_of_convex (hc : Convex ℝ (epigraph f)) (hp : IsProper f)
    (hx : f x = c) : v ∈ subdifferential f x ↔
      ∀ z, ((c + ⟪v,z-x⟫_ℝ : ℝ) : EReal) ≤ f z := by
  constructor
  · intro hv z
    obtain ⟨_, y, w, hy, hfy, hw, hwv⟩ := mem_subdifferential_iff_exists_seq.mp hv
    have hfy' : Tendsto (fun n ↦ (f (y n)).toReal) atTop (𝓝 c) := by
      rw [hx] at hfy
      simpa using (EReal.tendsto_toReal (EReal.coe_ne_top c) (EReal.coe_ne_bot c)).comp hfy
    apply le_of_tendsto ((continuous_coe_real_ereal.tendsto _).comp
      (hfy'.add (hwv.inner (tendsto_const_nhds.sub hy))))
    filter_upwards with n
    obtain ⟨a, ha⟩ : ∃ a : ℝ, f (y n) = a :=
      ⟨(hw n).choose, (hw n).choose_spec.1⟩
    have hn := (mem_regularSubdifferential_iff_of_convex hc hp ha).mp (hw n) z
    simpa [ha] using hn
  · exact fun h ↦ regularSubdifferential_subset_subdifferential f x
      ((mem_regularSubdifferential_iff_of_convex hc hp hx).mpr h)

/-- For a proper convex function the regular and limiting subgradients agree
even when the epigraph is not closed. -/
theorem subdifferential_eq_regularSubdifferential_of_convex (hc : Convex ℝ (epigraph f))
    (hp : IsProper f) (hx : f x = c) : subdifferential f x = regularSubdifferential f x := by
  ext v
  rw [mem_subdifferential_iff_of_convex hc hp hx, mem_regularSubdifferential_iff_of_convex hc hp hx]

omit [FiniteDimensional ℝ E] in
/-- Horizontal normals to a convex epigraph are exactly normals to its
effective domain, including when the domain is relatively open. -/
theorem horizontal_normal_iff_normalCone_domain (hc : Convex ℝ (epigraph f)) (hp : IsProper f)
    (hx : f x = c) : WithLp.toLp 2 (v,(0:ℝ)) ∈ normalCone (euclideanEpigraph f)
      (WithLp.toLp 2 (x,c)) ↔ v ∈ normalCone (effectiveDomain f) x := by
  have hcp : Convex ℝ (euclideanEpigraph f) := convex_preimage_continuousLinearEquiv
    (l2ProdEquiv E) hc
  have hxd : x ∈ effectiveDomain f := hx.trans_lt (EReal.coe_lt_top c)
  rw [normalCone_eq_of_convex hcp (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hx.le),
    normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph hc) hxd]
  constructor
  · intro h z hz
    have he : ((f z).toReal : EReal) = f z :=
      EReal.coe_toReal (show z ∈ effectiveDomain f from hz).ne (hp.2 z).ne'
    have hn := h (WithLp.toLp 2 (z,(f z).toReal)) (show f z ≤ _ from he.ge)
    change ⟪v,z-x⟫_ℝ + _ * 0 ≤ 0 at hn
    simpa using hn
  · intro h p hpe
    obtain ⟨⟨z,r⟩, rfl⟩ := (WithLp.toLp_surjective 2) p
    have hzr : f z ≤ (r : EReal) := hpe
    change ⟪v,z-x⟫_ℝ + _ * 0 ≤ 0
    simpa using h z (hzr.trans_lt (EReal.coe_lt_top r))

/-- **Proposition 8.12**, unconditional horizon inclusion. -/
theorem horizonSubdifferential_subset_normalCone_domain (hc : Convex ℝ (epigraph f))
    (hp : IsProper f) (hx : f x = c) :
    horizonSubdifferential f x ⊆ normalCone (effectiveDomain f) x := fun _ hv ↦
  (horizontal_normal_iff_normalCone_domain hc hp hx).mp (horizontal_normal_of_mem_horizonSubdifferential hx hv)

/-- **Proposition 8.12**, if there is one affine support at the point then its
whole subdifferential has recession cone equal to the horizon subdifferential
and to the normal cone of the domain. -/
theorem horizonSubdifferential_eq_normalCone_of_subdifferential_nonempty
    (hc : Convex ℝ (epigraph f)) (hp : IsProper f) (hx : f x = c)
    (hne : (subdifferential f x).Nonempty) :
    horizonSubdifferential f x = normalCone (effectiveDomain f) x ∧
    horizonSubdifferential f x = horizonCone (subdifferential f x) := by
  obtain ⟨u, hu⟩ := hne
  have hrad : normalCone (effectiveDomain f) x ⊆ horizonCone (subdifferential f x) := by
    intro w hw
    rw [normalCone_eq_of_convex (convex_effectiveDomain_of_convex_epigraph hc)
      (show x ∈ effectiveDomain f from hx.trans_lt (EReal.coe_lt_top c))] at hw
    apply mem_horizonCone_of_forall_smul_add_mem (x := u)
    intro t ht
    rw [mem_subdifferential_iff_of_convex hc hp hx]
    intro z
    by_cases hzt : f z = ⊤
    · simp [hzt]
    have hwz := hw z (lt_top_iff_ne_top.mpr hzt)
    refine (EReal.coe_le_coe_iff.mpr ?_).trans
      ((mem_subdifferential_iff_of_convex hc hp hx).mp hu z)
    rw [inner_add_left, real_inner_smul_left]
    linarith [mul_nonpos_of_nonneg_of_nonpos ht hwz]
  have hsub : horizonCone (subdifferential f x) ⊆ horizonSubdifferential f x := by
    rw [subdifferential_eq_regularSubdifferential_of_convex hc hp hx]
    exact horizonCone_regularSubdifferential_subset hx
  have hn := horizonSubdifferential_subset_normalCone_domain hc hp hx
  exact ⟨hn.antisymm (hrad.trans hsub), (hn.trans hrad).antisymm hsub⟩

/-- **Proposition 8.12.** Local lower semicontinuity suffices for equality of
the horizon subdifferential and the normal cone to the domain. -/
theorem horizonSubdifferential_eq_normalCone_domain_of_locallyLsc
    (hc : Convex ℝ (epigraph f)) (hp : IsProper f) (hl : IsLocallyLscAt f x) (hx : f x = c) :
    horizonSubdifferential f x = normalCone (effectiveDomain f) x := by
  ext v
  exact (mem_horizonSubdifferential_iff_epigraph_normal_of_locallyLsc hl hx).trans
    (horizontal_normal_iff_normalCone_domain hc hp hx)

end RW
