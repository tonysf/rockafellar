/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Subgradient recovery for uniformly Lipschitz limits
-/

import RockafellarWets.Chapter9.LipschitzLimits
import RockafellarWets.Chapter9.LipschitzExtension
import RockafellarWets.Chapter9.SubgradientModulus
import RockafellarWets.Chapter8.ProximalSubgradientLimits

open Filter Metric Set Topology
open scoped NNReal

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem subdifferential_congr_nhds_of_finite {f g : E → EReal} {x : E} {c : ℝ}
    (hf : f x = (c:EReal)) (he : f =ᶠ[𝓝 x] g) : subdifferential f x = subdifferential g x := by
  have hx : g x = (c:EReal) := (mem_of_mem_nhds he).symm.trans hf
  have hepi : euclideanEpigraph f =ᶠ[𝓝 (WithLp.toLp 2 (x,c))] euclideanEpigraph g := by
    filter_upwards [((WithLp.continuous_fst 2 E ℝ).tendsto (WithLp.toLp 2 (x,c))).eventually he] with p hp
    change (f p.fst ≤ (p.snd:EReal)) = (g p.fst ≤ (p.snd:EReal))
    rw [hp]
  ext v
  rw [mem_subdifferential_iff_epigraph_normal hf,mem_subdifferential_iff_epigraph_normal hx,
    normalCone_congr_nhds hepi]

theorem lowerSemicontinuous_restrictedRealFunction {f : E → ℝ} (hf : Continuous f)
    {B : Set E} (hB : IsClosed B) : LowerSemicontinuous (restrictedRealFunction f B) := by
  apply lowerSemicontinuous_of_isClosed_epigraph_ereal
  have he : epigraph (restrictedRealFunction f B) = epigraph (fun x ↦ (f x:EReal)) ∩ (B ×ˢ univ) := by
    ext ⟨x,r⟩
    by_cases hx : x ∈ B <;> simp [epigraph,restrictedRealFunction,hx]
  rw [he]
  exact (isClosed_epigraph_of_lsc_ereal _ (continuous_coe_real_ereal.comp hf).lowerSemicontinuous).inter
    (hB.prod isClosed_univ)

theorem epiConverges_restricted_lipschitz {f : ℕ → E → ℝ} {g : E → ℝ} {k : ℝ≥0}
    (hf : ∀ n, LipschitzWith k (f n)) {B : Set E} (hB : IsClosed B)
    (hlim : ∀ x ∈ B, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    EpiConverges (fun n ↦ restrictedRealFunction (f n) B) (restrictedRealFunction g B) := by
  apply epiConverges_iff_liminf_limsup.mpr
  intro x
  by_cases hx : x ∈ B
  · simp only [restrictedRealFunction,if_pos hx]
    constructor
    · intro y hy
      have ht := EReal.tendsto_coe.mpr (tendsto_lipschitz_values_of_tendsto hf (hlim x hx) hy)
      apply ht.liminf_eq.symm.le.trans
      apply liminf_le_liminf
      filter_upwards with n
      split_ifs <;> simp
      all_goals isBoundedDefault
    · refine ⟨fun _ ↦ x,tendsto_const_nhds,?_⟩
      simpa only [if_pos hx] using (EReal.tendsto_coe.mpr (hlim x hx)).limsup_eq.le
  · have he : restrictedRealFunction g B x = ⊤ := by simp [restrictedRealFunction,hx]
    rw [he]
    refine ⟨fun y hy ↦ ?_,⟨fun _ ↦ x,tendsto_const_nhds,le_top⟩⟩
    have hev := hy.eventually (hB.isOpen_compl.mem_nhds hx)
    have ht : Tendsto (fun n ↦ restrictedRealFunction (f n) B (y n)) atTop (𝓝 (⊤:EReal)) :=
      tendsto_const_nhds.congr' (hev.mono fun n hn ↦ by simp [restrictedRealFunction,hn])
    exact ht.liminf_eq.symm.le

theorem erealStrictlyContinuousAt_coe_of_lipschitzOnWith {f : E → ℝ} {X : Set E} {x : E}
    {k : ℝ≥0} (hf : LipschitzOnWith k f X) (hX : X ∈ 𝓝 x) :
    ERealStrictlyContinuousAt (fun y ↦ (f y:EReal)) x := by
  refine ⟨Eventually.of_forall fun y ↦ by simp,?_⟩
  simpa only [EReal.toReal_coe] using strictlyContinuousAt_iff.mpr ⟨k,X,hX,hf⟩

/-- **Proposition 9.59(a)**, recovery with every index and the original
functions. The chosen points remain in the original domain. -/
theorem exists_subgradient_recovery_of_lipschitz_limit {f : ℕ → E → ℝ} {g : E → ℝ}
    {X : Set E} {k : ℝ≥0} (hf : ∀ n, LipschitzOnWith k (f n) X)
    (hlim : ∀ x ∈ X, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)))
    {x v : E} (hx : x ∈ interior X) (hv : v ∈ subdifferential (fun y ↦ (g y:EReal)) x) :
    ∃ y w : ℕ → E, Tendsto y atTop (𝓝 x) ∧ Tendsto w atTop (𝓝 v) ∧
      ∀ n, y n ∈ interior X ∧ w n ∈ subdifferential (fun z ↦ (f n z:EReal)) (y n) := by
  classical
  have hX : X ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hX
  let B := closedBall x r
  choose F hF heF using fun n ↦ exists_lipschitz_extension_same_constant (hf n)
  obtain ⟨G,hG,heG⟩ := exists_lipschitz_extension_same_constant (lipschitzOnWith_of_pointwise_limit hf hlim)
  have hpoint (z : E) (hz : z ∈ B) : Tendsto (fun n ↦ F n z) atTop (𝓝 (G z)) := by
    rw [← heG (hball hz)]
    exact (hlim z (hball hz)).congr fun n ↦ heF n (hball hz)
  have heq (z : E) (hz : z ∈ ball x r) :
      restrictedRealFunction G B =ᶠ[𝓝 z] (fun a ↦ (g a:EReal)) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with a ha
    simp only [restrictedRealFunction,B,if_pos (ball_subset_closedBall ha),← heG (hball (ball_subset_closedBall ha))]
  have hgx : restrictedRealFunction G B x = (g x:EReal) := by
    simp only [restrictedRealFunction,B,if_pos (mem_closedBall_self hr.le),← heG (interior_subset hx)]
  have hv' : v ∈ subdifferential (restrictedRealFunction G B) x := by
    rw [subdifferential_congr_nhds_of_finite hgx (heq x (mem_ball_self hr))]
    exact hv
  obtain ⟨y,w,c,hy,hc,hw,hm⟩ := proximalSubgradientRecovery_of_epiConverges
    (fun n ↦ lowerSemicontinuous_restrictedRealFunction (hF n).continuous isClosed_closedBall)
    (epiConverges_restricted_lipschitz hF isClosed_closedBall hpoint) hgx hv'
  have hgood : ∀ᶠ n in atTop, y n ∈ interior X ∧ w n ∈ subdifferential (fun z ↦ (f n z:EReal)) (y n) := by
    filter_upwards [hm,hy.eventually (ball_mem_nhds x hr)] with n hn hyn
    have hlocal : restrictedRealFunction (F n) B =ᶠ[𝓝 (y n)] (fun z ↦ (f n z:EReal)) := by
      filter_upwards [isOpen_ball.mem_nhds hyn] with z hz
      simp only [restrictedRealFunction,B,if_pos (ball_subset_closedBall hz),← heF n (hball (ball_subset_closedBall hz))]
    have hs := regularSubdifferential_subset_subdifferential _ _
      (proximalSubdifferential_subset_regularSubdifferential _ _ hn.2)
    rw [subdifferential_congr_nhds_of_finite hn.1 hlocal] at hs
    exact ⟨mem_interior_iff_mem_nhds.mpr
      (mem_of_superset (isOpen_ball.mem_nhds hyn) (ball_subset_closedBall.trans hball)),hs⟩
  choose z hz using fun n ↦
    (erealStrictlyContinuousAt_coe_of_lipschitzOnWith (hf n) hX).subdifferential_nonempty_compact.1
  let good n := y n ∈ interior X ∧ w n ∈ subdifferential (fun z ↦ (f n z:EReal)) (y n)
  let yy n := if good n then y n else x
  let ww n := if good n then w n else z n
  refine ⟨yy,ww,hy.congr' ?_,hw.congr' ?_,fun n ↦ ?_⟩
  · exact hgood.mono fun n hn ↦ by simp [yy,good,hn]
  · exact hgood.mono fun n hn ↦ by simp [ww,good,hn]
  · by_cases hn : good n
    · simpa only [yy,ww,if_pos hn] using hn
    · simpa only [yy,ww,if_neg hn] using And.intro hx (hz n)

/-- **Proposition 9.59(a)**, the limit and the subgradient approximation
assertions with their common dense-set convergence hypotheses. -/
theorem exists_lipschitz_limit_and_subgradient_recovery {f : ℕ → E → ℝ} {X D : Set E}
    {k : ℝ≥0} (hf : ∀ n, LipschitzOnWith k (f n) X) (hDX : D ⊆ X) (hXD : X ⊆ closure D)
    (hlim : ∀ x ∈ D, ∃ v : ℝ, Tendsto (fun n ↦ f n x) atTop (𝓝 v)) :
    ∃ g : E → ℝ, LipschitzWith k g ∧
      (∀ B ⊆ X, Bornology.IsBounded B → TendstoUniformlyOn f g atTop B) ∧
      ∀ x ∈ interior X, ∀ v ∈ subdifferential (fun a ↦ (g a:EReal)) x,
        ∃ y w : ℕ → E, Tendsto y atTop (𝓝 x) ∧ Tendsto w atTop (𝓝 v) ∧
          ∀ n, y n ∈ interior X ∧ w n ∈ subdifferential (fun a ↦ (f n a:EReal)) (y n) := by
  obtain ⟨g,hg,hpoint,hu⟩ := exists_lipschitz_limit_of_convergent_dense hf hDX hXD hlim
  exact ⟨g,hg,hu,fun x hx v hv ↦ exists_subgradient_recovery_of_lipschitz_limit hf hpoint hx hv⟩

end RW
