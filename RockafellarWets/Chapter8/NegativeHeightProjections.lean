/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Approximating horizontal proximal normals

Move a point with a unique horizontal projection slightly downward. If every
projection at every intermediate height still had horizontal displacement,
then the squared distance could increase by at most the square of each
height increment. On subdividing the interval its total increase would be
zero. At the endpoint equality would give a second projection at the
original height, or a point strictly below the finite graph.
-/

import RockafellarWets.Chapter8.EpigraphNormals
import RockafellarWets.Chapter5.ProjectionGraphicalConvergence
import RockafellarWets.Chapter6.ProximalNormals

open Filter Metric Set Topology
open scoped InnerProductSpace

namespace RW

private theorem le_at_zero_of_quadratic_increments {D : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hq : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, D t ≤ D s + (t-s)^2) :
    D b ≤ D 0 := by
  have mesh (n : ℕ) (hn : 0 < n) : D b ≤ D 0 + b^2 / n := by
    let δ := b/n
    have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
    have hδ : (n:ℝ)*δ = b := by dsimp [δ]; field_simp
    have hin (k : ℕ) (hk : k ≤ n) : (k:ℝ)*δ ∈ Icc 0 b := by
      have hpos : 0 ≤ δ := div_nonneg hb.le hn'.le
      exact ⟨mul_nonneg (Nat.cast_nonneg _) hpos, hδ ▸ mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hk) hpos⟩
    have hstep (k : ℕ) (hk : k ≤ n) : D ((k:ℝ)*δ) ≤ D 0 + k*δ^2 := by
      induction k with
      | zero => simp
      | succ k ih =>
        have hk' := Nat.le_of_succ_le hk
        have hi := hq _ (hin k hk') _ (hin (k+1) hk)
        have h := ih hk'
        rw [Nat.cast_add_one, show ((k:ℝ)+1)*δ - k*δ = δ by ring] at hi
        rw [Nat.cast_add_one]
        nlinarith
    have h := hstep n le_rfl
    rw [hδ] at h
    convert h using 1
    dsimp [δ]
    field_simp
  have hlim : Tendsto (fun n : ℕ ↦ D 0 + b^2 / n) atTop (𝓝 (D 0)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (b^2))
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨1,fun n hn ↦ mesh n hn⟩)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem dist_sq_l2 (p q : WithLp 2 (E × ℝ)) :
    dist p q ^ 2 = ‖p.ofLp.1 - q.ofLp.1‖^2 + (p.ofLp.2 - q.ofLp.2)^2 := by
  rw [dist_eq_norm, WithLp.prod_norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

/-- At a center with a unique projection onto a closed nonempty set, every
selection of projections tends to that projection as its centers approach. -/
theorem tendsto_projections_of_unique {P : Type*} [NormedAddCommGroup P] [ProperSpace P]
    {C : Set P} (hC : IsClosed C) (hne : C.Nonempty) {a p : P}
    (hu : projMapping C a = {p}) {a' p' : ℕ → P} (ha : Tendsto a' atTop (𝓝 a))
    (hp : ∀ n, p' n ∈ projMapping C (a' n)) : Tendsto p' atTop (𝓝 p) := by
  apply _root_.tendsto_nhds.mpr
  intro O hO hpO
  obtain ⟨V,hV,hs⟩ := SvOscAt.exists_nhds_svImage_subset
    (svLocallyBounded_projMapping hne a) (svOsc_projMapping hC a) hO (by simpa [hu] using hpO)
  exact (ha.eventually_mem hV).mono fun n hn ↦ hs (mem_svImage.mpr ⟨_,hn,hp n⟩)

/-- Some arbitrarily small downward change in height has a projection with
strictly negative vertical displacement. -/
private theorem exists_negative_projection_below {f : E → EReal} {x a : E} {c : ℝ}
    (hf : IsClosed (euclideanEpigraph f)) (hx : f x = c)
    (hu : projMapping (euclideanEpigraph f) (WithLp.toLp 2 (a,c)) = {WithLp.toLp 2 (x,c)})
    {b : ℝ} (hb : 0 < b) :
    ∃ s ∈ Icc 0 b, ∃ p ∈ projMapping (euclideanEpigraph f) (WithLp.toLp 2 (a,c-s)),
      c-s < p.ofLp.2 := by
  let C := euclideanEpigraph f
  let q := fun s : ℝ ↦ WithLp.toLp 2 (a,c-s)
  let D := fun s ↦ infDist (q s) C ^ 2
  have hne : C.Nonempty := ⟨WithLp.toLp 2 (x,c),hx.le⟩
  have h0 (p : WithLp 2 (E × ℝ)) (hp : p ∈ C) : dist (q 0) (WithLp.toLp 2 (x,c)) ≤
      dist (q 0) p := by
    have hxP : WithLp.toLp 2 (x,c) ∈ projMapping C (q 0) := by simp [q,C,hu]
    rw [(mem_projMapping_iff_dist.mp hxP).2]
    exact infDist_le_dist_of_mem hp
  have hdist0 : dist (q 0) (WithLp.toLp 2 (x,c)) = infDist (q 0) C :=
    (mem_projMapping_iff_dist.mp (show WithLp.toLp 2 (x,c) ∈ projMapping C (q 0) by
      simp [q,C,hu])).2
  have hinc : D 0 < D b := by
    obtain ⟨p,hp⟩ := projMapping_nonempty hf hne (q b)
    let z := WithLp.toLp 2 (p.ofLp.1, p.ofLp.2+b)
    have hz : z ∈ C := (show f p.ofLp.1 ≤ (p.ofLp.2 : EReal) from hp.1).trans
      (EReal.coe_le_coe_iff.mpr (by linarith))
    have hdist : dist (q 0) z = dist (q b) p := by
      apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
      rw [dist_sq_l2,dist_sq_l2]
      simp [q,z]
      ring
    have hle := h0 z hz
    rw [hdist, hdist0, (mem_projMapping_iff_dist.mp hp).2] at hle
    apply (sq_lt_sq₀ infDist_nonneg infDist_nonneg).mpr
    apply lt_of_le_of_ne hle
    intro he
    have hzP : z ∈ projMapping C (q 0) :=
      mem_projMapping_iff_dist.mpr ⟨hz, hdist.trans ((mem_projMapping_iff_dist.mp hp).2.trans he.symm)⟩
    have hez : z = WithLp.toLp 2 (x,c) := by simpa [C,q,hu] using hzP
    have hzx : p.ofLp.1 = x := congrArg (fun k : WithLp 2 (E × ℝ) ↦ k.ofLp.1) hez
    have hzc : p.ofLp.2+b = c := congrArg (fun k : WithLp 2 (E × ℝ) ↦ k.ofLp.2) hez
    have hzlow : f p.ofLp.1 ≤ (p.ofLp.2 : EReal) := hp.1
    rw [hzx,hx] at hzlow
    linarith [EReal.coe_le_coe_iff.mp hzlow]
  by_contra! hn
  apply hinc.not_ge (le_at_zero_of_quadratic_increments hb ?_)
  intro s hs t _
  obtain ⟨p,hp⟩ := projMapping_nonempty hf hne (q s)
  have hle : p.ofLp.2 ≤ c-s := hn s hs p hp
  let z := WithLp.toLp 2 (p.ofLp.1,c-s)
  have hz : z ∈ C := (show f p.ofLp.1 ≤ (p.ofLp.2 : EReal) from hp.1).trans
    (EReal.coe_le_coe_iff.mpr hle)
  have hpdist := (mem_projMapping_iff_dist.mp hp).2
  have hmin := sq_le_sq₀ dist_nonneg dist_nonneg |>.mpr (hpdist.trans_le (infDist_le_dist_of_mem hz))
  rw [dist_sq_l2,dist_sq_l2] at hmin
  simp only [q,z,sub_self,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
    add_zero,add_le_iff_nonpos_right] at hmin
  have hheight : p.ofLp.2 = c-s := by nlinarith [sq_nonneg (c-s-p.ofLp.2)]
  have hcmp := (sq_le_sq₀ infDist_nonneg dist_nonneg).mpr
    (infDist_le_dist_of_mem (x := q t) (s := C) hp.1)
  change infDist (q t) C ^ 2 ≤ infDist (q s) C ^ 2 + _
  rw [← hpdist,dist_sq_l2]
  rw [dist_sq_l2] at hcmp
  simp only [q,hheight] at hcmp ⊢
  nlinarith

/-- Graph of the regular epigraph normals of strictly negative height. -/
def negativeEpigraphNormalGraph (f : E → EReal) :
    Set (WithLp 2 (E × ℝ) × WithLp 2 (E × ℝ)) :=
  {q | q.2 ∈ regularNormalCone (euclideanEpigraph f) q.1 ∧ q.2.ofLp.2 < 0}

/-- At a finite graph point of a closed epigraph, every horizontal proximal
normal is approximable by regular normals of strictly negative height. -/
theorem horizontal_proximal_mem_closure_negativeNormalGraph {f : E → EReal} {x v : E} {c : ℝ}
    (hf : IsClosed (euclideanEpigraph f)) (hx : f x = c)
    (hv : WithLp.toLp 2 (v,(0:ℝ)) ∈ proximalNormalCone (euclideanEpigraph f)
      (WithLp.toLp 2 (x,c))) :
    (WithLp.toLp 2 (x,c), WithLp.toLp 2 (v,(0:ℝ))) ∈ closure (negativeEpigraphNormalGraph f) := by
  let p := WithLp.toLp 2 (x,c)
  let d := WithLp.toLp 2 (v,(0:ℝ))
  obtain ⟨t, ht, hp⟩ := hv
  let r := t/2
  have hr : 0 < r := half_pos ht
  let a := x + r • v
  have hu : projMapping (euclideanEpigraph f) (WithLp.toLp 2 (a,c)) = {p} := by
    convert projMapping_add_smul_eq_singleton_of_lt hp hr (half_lt_self ht) using 2
    apply WithLp.ofLp_injective
    ext <;> simp [a]
  have hex (n : ℕ) := exists_negative_projection_below hf hx hu
    (b := 1/((n:ℝ)+1)) (by positivity)
  choose s hs z hz hneg using hex
  let q := fun n ↦ WithLp.toLp 2 (a,c-s n)
  have hs0 : Tendsto s atTop (𝓝 0) := squeeze_zero (fun n ↦ (hs n).1) (fun n ↦ (hs n).2)
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hq : Tendsto q atTop (𝓝 (WithLp.toLp 2 (a,c))) :=
    ((l2ProdEquiv E).symm.continuous.tendsto _).comp (tendsto_const_nhds.prodMk_nhds
      (show Tendsto (fun n ↦ c-s n) atTop (𝓝 c) by simpa using tendsto_const_nhds.sub hs0))
  have hzp := tendsto_projections_of_unique hf ⟨p,hx.le⟩ hu hq hz
  let w := fun n ↦ r⁻¹ • (q n-z n)
  have hw (n : ℕ) : w n ∈ regularNormalCone (euclideanEpigraph f) (z n) :=
    nonneg_smul_sub_mem_regularNormalCone_of_mem_projMapping (hz n) (inv_nonneg.mpr hr.le)
  have hd : r⁻¹ • (WithLp.toLp 2 (a,c) - p) = d := by
    apply WithLp.ofLp_injective
    ext <;> simp [a,p,d,hr.ne']
  have hwlim : Tendsto w atTop (𝓝 d) := hd ▸ (hq.sub hzp).const_smul _
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨fun n ↦ (z n,w n), fun n ↦ ⟨hw n, ?_⟩, hzp.prodMk_nhds hwlim⟩
  change r⁻¹ * ((c-s n)-(z n).ofLp.2) < 0
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hr) (sub_neg.mpr (hneg n))

end RW
