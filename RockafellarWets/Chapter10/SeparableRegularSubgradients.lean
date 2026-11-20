/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 10: Regular subgradients of separable functions
-/

import RockafellarWets.Chapter10.EpigraphChainMaps

open Filter Set Topology
open scoped InnerProductSpace

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A sum whose two terms depend on separate Euclidean coordinates. -/
def separableSum (f : E → EReal) (g : F → EReal) (p : WithLp 2 (E × F)) : EReal :=
  f p.fst + g p.snd

variable {f : E → EReal} {g : F → EReal} {x : E} {y : F} {c d : ℝ}

/-- **Proposition 10.5**, the binary regular-subgradient product formula. -/
theorem mem_regularSubdifferential_separableSum_iff (hx : f x = c) (hy : g y = d)
    (v : WithLp 2 (E × F)) :
    v ∈ regularSubdifferential (separableSum f g) (WithLp.toLp 2 (x,y)) ↔
      v.fst ∈ regularSubdifferential f x ∧ v.snd ∈ regularSubdifferential g y := by
  have hxy : separableSum f g (WithLp.toLp 2 (x,y)) = ((c+d:ℝ):EReal) := by
    simp only [separableSum,WithLp.toLp_fst,WithLp.toLp_snd,hx,hy,EReal.coe_add]
  constructor
  · rintro ⟨a,ha,hv⟩
    have ha' : a = c+d := EReal.coe_injective (ha.symm.trans hxy)
    subst a
    constructor
    · refine ⟨c,hx,fun ε hε ↦ ?_⟩
      have hm : Tendsto (fun z : E ↦ WithLp.toLp 2 (z,y)) (𝓝 x) (𝓝 (WithLp.toLp 2 (x,y))) :=
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.continuous.tendsto _).comp
          (tendsto_id.prodMk_nhds tendsto_const_nhds)
      filter_upwards [hm.eventually (hv ε hε)] with z hz
      have hn : ‖WithLp.toLp 2 (z,y)-WithLp.toLp 2 (x,y)‖ = ‖z-x‖ := by
        rw [← WithLp.toLp_sub,Prod.mk_sub_mk,sub_self]
        exact WithLp.norm_toLp_fst 2 E F _
      have hi : ⟪v,WithLp.toLp 2 (z,y)-WithLp.toLp 2 (x,y)⟫_ℝ = ⟪v.fst,z-x⟫_ℝ := by
        change ⟪v.fst,z-x⟫_ℝ + ⟪v.snd,y-y⟫_ℝ = _
        simp
      change ((c+d+⟪v,WithLp.toLp 2 (z,y)-WithLp.toLp 2 (x,y)⟫_ℝ-
        ε*‖WithLp.toLp 2 (z,y)-WithLp.toLp 2 (x,y)‖:ℝ):EReal) ≤ f z+g y at hz
      rw [hn,hi,hy,show c+d+⟪v.fst,z-x⟫_ℝ-ε*‖z-x‖ = (c+⟪v.fst,z-x⟫_ℝ-ε*‖z-x‖)+d by ring,
        EReal.coe_add] at hz
      exact (EReal.addLECancellable_coe d).add_le_add_iff_right.mp hz
    · refine ⟨d,hy,fun ε hε ↦ ?_⟩
      have hm : Tendsto (fun z : F ↦ WithLp.toLp 2 (x,z)) (𝓝 y) (𝓝 (WithLp.toLp 2 (x,y))) :=
        ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.continuous.tendsto _).comp
          (tendsto_const_nhds.prodMk_nhds tendsto_id)
      filter_upwards [hm.eventually (hv ε hε)] with z hz
      have hn : ‖WithLp.toLp 2 (x,z)-WithLp.toLp 2 (x,y)‖ = ‖z-y‖ := by
        rw [← WithLp.toLp_sub,Prod.mk_sub_mk,sub_self]
        exact WithLp.norm_toLp_snd 2 E F _
      have hi : ⟪v,WithLp.toLp 2 (x,z)-WithLp.toLp 2 (x,y)⟫_ℝ = ⟪v.snd,z-y⟫_ℝ := by
        change ⟪v.fst,x-x⟫_ℝ + ⟪v.snd,z-y⟫_ℝ = _
        simp
      change ((c+d+⟪v,WithLp.toLp 2 (x,z)-WithLp.toLp 2 (x,y)⟫_ℝ-
        ε*‖WithLp.toLp 2 (x,z)-WithLp.toLp 2 (x,y)‖:ℝ):EReal) ≤ f x+g z at hz
      rw [hn,hi,hx,show c+d+⟪v.snd,z-y⟫_ℝ-ε*‖z-y‖ = (d+⟪v.snd,z-y⟫_ℝ-ε*‖z-y‖)+c by ring,
        EReal.coe_add,add_comm (c:EReal)] at hz
      exact (EReal.addLECancellable_coe c).add_le_add_iff_right.mp hz
  · rintro ⟨⟨a,ha,hv⟩,⟨b,hb,hw⟩⟩
    have ha' : a = c := EReal.coe_injective (ha.symm.trans hx)
    have hb' : b = d := EReal.coe_injective (hb.symm.trans hy)
    subst a; subst b
    refine ⟨c+d,hxy,fun ε hε ↦ ?_⟩
    have hfst := ((WithLp.fstL 2 ℝ E F).continuous.tendsto (WithLp.toLp 2 (x,y))).eventually (hv (ε/2) (by positivity))
    have hsnd := ((WithLp.sndL 2 ℝ E F).continuous.tendsto (WithLp.toLp 2 (x,y))).eventually (hw (ε/2) (by positivity))
    filter_upwards [hfst,hsnd] with q hqf hqg
    have hh := add_le_add hqf hqg
    rw [← EReal.coe_add] at hh
    apply (EReal.coe_le_coe_iff.mpr ?_).trans hh
    have hnf := WithLp.norm_fst_le E (q-WithLp.toLp 2 (x,y))
    have hng := WithLp.norm_snd_le E (q-WithLp.toLp 2 (x,y))
    change c+d+(⟪v.fst,q.fst-x⟫_ℝ+⟪v.snd,q.snd-y⟫_ℝ)-ε*‖q-WithLp.toLp 2 (x,y)‖ ≤
      (c+⟪v.fst,q.fst-x⟫_ℝ-ε/2*‖q.fst-x‖)+(d+⟪v.snd,q.snd-y⟫_ℝ-ε/2*‖q.snd-y‖)
    change ‖q.fst-x‖ ≤ ‖q-WithLp.toLp 2 (x,y)‖ at hnf
    change ‖q.snd-y‖ ≤ ‖q-WithLp.toLp 2 (x,y)‖ at hng
    nlinarith

end RW
