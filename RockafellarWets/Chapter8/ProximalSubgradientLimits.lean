/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Approximation by proximal subgradients of varying functions

Apply the moving-set normal approximation to strictly negative regular normals
first. These form a dense set at every finite epigraph point, including for
horizontal limiting normals. This order ensures that all approximating normals
have strictly positive rescaling parameters.
-/

import RockafellarWets.Chapter8.HorizontalEpigraphNormals
import RockafellarWets.Chapter8.ProximalApproximation
import RockafellarWets.Chapter7.EpiDistances

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal} {F : ℕ → E → EReal} {x v : E} {c : ℝ}

private abbrev EP (E : Type*) := WithLp 2 (E × ℝ)

/-- Graph coordinates of a positively scaled proximal subgradient. The second
height records the negative of the scale. -/
def scaledProximalSubgradientGraph (f : E → EReal) : Set (EP E × EP E) :=
  {z | f z.1.fst = (z.1.snd : EReal) ∧ z.2.snd < 0 ∧
    (-z.2.snd)⁻¹ • z.2.fst ∈ proximalSubdifferential f z.1.fst}

omit [FiniteDimensional ℝ E] in
private theorem mem_scaledProximal_of_negative_normal {z : EP E × EP E}
    (hz : z.2 ∈ proximalNormalCone (euclideanEpigraph f) z.1) (hb : z.2.snd < 0) :
    z ∈ scaledProximalSubgradientGraph f := by
  obtain ⟨⟨x,c⟩,hp⟩ := (WithLp.toLp_surjective 2) z.1
  obtain ⟨⟨u,b⟩,hq⟩ := (WithLp.toLp_surjective 2) z.2
  have hpos : 0 < -b := neg_pos.mpr (by simpa only [← hq] using hb)
  have hn : WithLp.toLp 2 (u,b) ∈ proximalNormalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c)) := by
    rwa [hq,hp]
  have hfin := value_eq_of_mem_regularNormalCone_epigraph_of_neg (proximalNormalCone_subset_regularNormalCone hn)
    (neg_pos.mp hpos)
  have hscale : (-b)⁻¹ • WithLp.toLp 2 (u,b) = WithLp.toLp 2 ((-b)⁻¹ • u,(-1:ℝ)) := by
    apply WithLp.ofLp_injective
    ext <;> simp [(neg_pos.mp hpos).ne,smul_eq_mul]
  have hcone := (isCone_proximalNormalCone (show WithLp.toLp 2 (x,c) ∈ euclideanEpigraph f from hfin.le)).smul_mem hn
    (inv_nonneg.mpr hpos.le)
  rw [hscale] at hcone
  change f z.1.fst = _ ∧ _ ∧ _ ∈ _
  rw [← hp,← hq]
  exact ⟨hfin,neg_pos.mp hpos,(mem_proximalSubdifferential_iff_mem_proximalNormalCone_l2Epigraph hfin).mpr hcone⟩

/-- **8.47(b)** in graph coordinates, valid for ordinary and horizontal
normals, when only the lower epi-limit is prescribed. -/
theorem mem_outerSetLimit_scaledProximalSubgradientGraph
    (hF : ∀ n, LowerSemicontinuous (F n)) (hlim : epiLowerLimit F = f)
    (hx : f x = c) {q : EP E} (hn : q ∈ normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c))) :
    (WithLp.toLp 2 (x,c), q) ∈ outerSetLimit (fun n ↦ scaledProximalSubgradientGraph (F n)) := by
  have hl : LowerSemicontinuous f := hlim ▸ lowerSemicontinuous_epiLowerLimit _
  have hout : outerSetLimit (fun n ↦ euclideanEpigraph (F n)) = euclideanEpigraph f := by
    change outerSetLimit (fun n ↦ (WithLp.homeomorphProd 2 E ℝ) ⁻¹' epigraph (F n)) = _
    rw [outerSetLimit_preimage_homeomorph,← epigraph_epiLowerLimit,hlim]
    rfl
  apply closure_minimal _ (isClosed_outerSetLimit _) (mem_closure_negativeNormalGraph_of_normal_of_lsc hl hx hn)
  intro z hz V hV
  let B : Set (EP E × EP E) := {a | a.2.snd < 0}
  have hB : B ∈ 𝓝 z := (isOpen_lt ((WithLp.continuous_snd 2 E ℝ).comp continuous_snd) continuous_const).mem_nhds hz.2
  have h := mem_graphicalOuterLimit_proximalNormalCone_of_mem_normalCone (isClosed_euclideanEpigraph hl)
    (fun n ↦ isClosed_euclideanEpigraph (hF n)) hout (regularNormalCone_subset_normalCone _ _ hz.1)
  exact (h (V ∩ B) (inter_mem hV hB)).mono fun n ⟨a,ha,hav,hab⟩ ↦
    ⟨a,mem_scaledProximal_of_negative_normal ha hab,hav⟩

/-- Under epi-convergence every neighborhood is hit eventually, so a
cofinite set of indices suffices. -/
theorem mem_innerSetLimit_scaledProximalSubgradientGraph
    (hF : ∀ n, LowerSemicontinuous (F n)) (hlim : EpiConverges F f)
    (hx : f x = c) {q : EP E} (hn : q ∈ normalCone (euclideanEpigraph f) (WithLp.toLp 2 (x,c))) :
    (WithLp.toLp 2 (x,c), q) ∈ innerSetLimit (fun n ↦ scaledProximalSubgradientGraph (F n)) := by
  have hconv := epiConverges_iff_pkConverges_euclideanEpigraph.mp hlim
  have hl : LowerSemicontinuous f := by
    rw [← (epiConverges_iff_epiLimits_eq.mp hlim).1]
    exact lowerSemicontinuous_epiLowerLimit _
  apply closure_minimal _ (isClosed_innerSetLimit _) (mem_closure_negativeNormalGraph_of_normal_of_lsc hl hx hn)
  intro z hz V hV
  let B : Set (EP E × EP E) := {a | a.2.snd < 0}
  have hB : B ∈ 𝓝 z := (isOpen_lt ((WithLp.continuous_snd 2 E ℝ).comp continuous_snd) continuous_const).mem_nhds hz.2
  have h := mem_graphicalInnerLimit_proximalNormalCone_of_mem_normalCone
    (fun n ↦ isClosed_euclideanEpigraph (hF n)) hconv (regularNormalCone_subset_normalCone _ _ hz.1)
  exact (h (V ∩ B) (inter_mem hV hB)).mono fun n ⟨a,ha,hav,hab⟩ ↦
    ⟨a,mem_scaledProximal_of_negative_normal ha hab,hav⟩

/-- Recovery at a finite graph point by proximal subgradients of a family of
functions, using all sufficiently large indices. -/
def ProximalSubgradientRecovery (F : ℕ → E → EReal) (x : E) (c : ℝ) (v : E) : Prop :=
  ∃ (y u : ℕ → E) (r : ℕ → ℝ), Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 c) ∧
    Tendsto u atTop (𝓝 v) ∧ ∀ᶠ n in atTop, F n (y n) = (r n : EReal) ∧ u n ∈ proximalSubdifferential (F n) (y n)

/-- Recovery of a horizon subgradient, with positive scales tending to zero. -/
def HorizonProximalSubgradientRecovery (F : ℕ → E → EReal) (x : E) (c : ℝ) (v : E) : Prop :=
  ∃ (y u : ℕ → E) (r t : ℕ → ℝ), Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 c) ∧
    Tendsto t atTop (𝓝 0) ∧ Tendsto (fun n ↦ t n • u n) atTop (𝓝 v) ∧
    ∀ᶠ n in atTop, 0 < t n ∧ F n (y n) = (r n : EReal) ∧ u n ∈ proximalSubdifferential (F n) (y n)

omit [FiniteDimensional ℝ E] in
private theorem recovery_of_negative_unit_limit {z : ℕ → EP E × EP E}
    (hz : ∀ᶠ n in atTop, z n ∈ scaledProximalSubgradientGraph (F n))
    (hlim : Tendsto z atTop (𝓝 (WithLp.toLp 2 (x,c),WithLp.toLp 2 (v,(-1:ℝ))))) :
    ProximalSubgradientRecovery F x c v := by
  let t := fun n ↦ -(z n).2.snd
  have hp := (continuous_fst.tendsto _).comp hlim
  have hq := (continuous_snd.tendsto _).comp hlim
  have ht : Tendsto t atTop (𝓝 (1:ℝ)) := by
    simpa [t,Function.comp_def] using (((WithLp.continuous_snd 2 E ℝ).tendsto _).comp hq).neg
  have hu := (ht.inv₀ one_ne_zero).smul (((WithLp.continuous_fst 2 E ℝ).tendsto _).comp hq)
  exact ⟨_,fun n ↦ (t n)⁻¹ • (z n).2.fst,_, ((WithLp.continuous_fst 2 E ℝ).tendsto _).comp hp,
    ((WithLp.continuous_snd 2 E ℝ).tendsto _).comp hp,by simpa using hu,
    hz.mono fun n h ↦ ⟨h.1,h.2.2⟩⟩

omit [FiniteDimensional ℝ E] in
private theorem recovery_of_horizontal_limit {z : ℕ → EP E × EP E}
    (hz : ∀ᶠ n in atTop, z n ∈ scaledProximalSubgradientGraph (F n))
    (hlim : Tendsto z atTop (𝓝 (WithLp.toLp 2 (x,c),WithLp.toLp 2 (v,(0:ℝ))))) :
    HorizonProximalSubgradientRecovery F x c v := by
  let t := fun n ↦ -(z n).2.snd
  have hp := (continuous_fst.tendsto _).comp hlim
  have hq := (continuous_snd.tendsto _).comp hlim
  refine ⟨_,fun n ↦ (t n)⁻¹ • (z n).2.fst,_,t,((WithLp.continuous_fst 2 E ℝ).tendsto _).comp hp,
    ((WithLp.continuous_snd 2 E ℝ).tendsto _).comp hp,?_,?_,hz.mono fun n h ↦ ⟨neg_pos.mpr h.2.1,h.1,h.2.2⟩⟩
  · simpa [t,Function.comp_def] using (((WithLp.continuous_snd 2 E ℝ).tendsto _).comp hq).neg
  · apply Tendsto.congr' _ (((WithLp.continuous_fst 2 E ℝ).tendsto _).comp hq)
    filter_upwards [hz] with n hn
    simp [t,smul_smul,hn.2.1.ne]

/-- **8.47(b)**, the subsequence for an ordinary subgradient. -/
theorem exists_subsequence_proximalSubgradientRecovery (hF : ∀ n, LowerSemicontinuous (F n))
    (hlim : epiLowerLimit F = f) (hx : f x = c) (hv : v ∈ subdifferential f x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ProximalSubgradientRecovery (F ∘ φ) x c v := by
  obtain ⟨φ,z,hφ,hz,hzlim⟩ := mem_outerSetLimit_iff_exists_subsequence.mp
    (mem_outerSetLimit_scaledProximalSubgradientGraph hF hlim hx ((mem_subdifferential_iff_epigraph_normal hx).mp hv))
  exact ⟨φ,hφ,recovery_of_negative_unit_limit (Eventually.of_forall hz) hzlim⟩

/-- **8.47(b)**, the subsequence for a horizon subgradient. -/
theorem exists_subsequence_horizonProximalSubgradientRecovery (hF : ∀ n, LowerSemicontinuous (F n))
    (hlim : epiLowerLimit F = f) (hx : f x = c) (hv : v ∈ horizonSubdifferential f x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ HorizonProximalSubgradientRecovery (F ∘ φ) x c v := by
  obtain ⟨φ,z,hφ,hz,hzlim⟩ := mem_outerSetLimit_iff_exists_subsequence.mp
    (mem_outerSetLimit_scaledProximalSubgradientGraph hF hlim hx (horizontal_normal_of_mem_horizonSubdifferential hx hv))
  exact ⟨φ,hφ,recovery_of_horizontal_limit (Eventually.of_forall hz) hzlim⟩

/-- **8.47(b)**, the cofinite recovery of an ordinary subgradient. -/
theorem proximalSubgradientRecovery_of_epiConverges (hF : ∀ n, LowerSemicontinuous (F n))
    (hlim : EpiConverges F f) (hx : f x = c) (hv : v ∈ subdifferential f x) :
    ProximalSubgradientRecovery F x c v := by
  obtain ⟨z,hz,hzlim⟩ := mem_innerSetLimit_iff_exists_seq.mp
    (mem_innerSetLimit_scaledProximalSubgradientGraph hF hlim hx ((mem_subdifferential_iff_epigraph_normal hx).mp hv))
  exact recovery_of_negative_unit_limit hz hzlim

/-- **8.47(b)**, the cofinite recovery of a horizon subgradient. -/
theorem horizonProximalSubgradientRecovery_of_epiConverges (hF : ∀ n, LowerSemicontinuous (F n))
    (hlim : EpiConverges F f) (hx : f x = c) (hv : v ∈ horizonSubdifferential f x) :
    HorizonProximalSubgradientRecovery F x c v := by
  obtain ⟨z,hz,hzlim⟩ := mem_innerSetLimit_iff_exists_seq.mp
    (mem_innerSetLimit_scaledProximalSubgradientGraph hF hlim hx (horizontal_normal_of_mem_horizonSubdifferential hx hv))
  exact recovery_of_horizontal_limit hz hzlim

/-- **8.47(a)**, approximation of a horizon subgradient at prescribed accuracy. -/
theorem exists_scaled_proximalSubgradient_close (hl : LowerSemicontinuous f) (hx : f x = c)
    (hv : v ∈ horizonSubdifferential f x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (y u : E) (r t : ℝ), f y = r ∧ dist y x < δ ∧ |r-c| < δ ∧ u ∈ proximalSubdifferential f y ∧
      0 < t ∧ t < δ ∧ dist (t • u) v < δ := by
  have hconv : EpiConverges (fun _ : ℕ ↦ f) f := pkConverges_const_of_isClosed (isClosed_epigraph_of_lsc_ereal f hl)
  obtain ⟨y,u,r,t,hy,hr,ht,hu,hm⟩ := horizonProximalSubgradientRecovery_of_epiConverges (fun _ ↦ hl) hconv hx hv
  obtain ⟨n,hn,hy',hr',ht',hu'⟩ := (hm.and ((hy.eventually (ball_mem_nhds x hδ)).and
    ((hr.eventually (ball_mem_nhds c hδ)).and ((ht.eventually_lt_const hδ).and
      (hu.eventually (ball_mem_nhds v hδ)))))).exists
  exact ⟨y n,u n,r n,t n,hn.2.1,hy',by simpa [Real.dist_eq] using hr',hn.2.2,hn.1,ht',hu'⟩

end RW
