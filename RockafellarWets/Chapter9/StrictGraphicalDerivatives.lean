/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strict graphical derivatives
-/

import RockafellarWets.Chapter9.StrictTangents
import RockafellarWets.Chapter8.ProtoDifferentiability
import RockafellarWets.Chapter8.HomogeneousMappings

open Filter Metric Set Topology

namespace RW

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Definition 9.53.** The graph is the outer limit of the moving-base
difference quotients as the base approaches through the original graph. -/
def strictGraphicalDerivative (S : E → Set F) (x : E) (u : F) : E → Set F :=
  fun w ↦ {z | (w,z) ∈ strictTangentCone (svGraph S) (x,u)}

theorem svGraph_strictGraphicalDerivative (S : E → Set F) (x : E) (u : F) :
    svGraph (strictGraphicalDerivative S x u) = strictTangentCone (svGraph S) (x,u) := rfl

/-- The graphical outer-limit formula following (9.27). -/
theorem svGraph_strictGraphicalDerivative_eq_outerLimit (S : E → Set F) (x : E) (u : F) :
    svGraph (strictGraphicalDerivative S x u) =
      outerSetLimitAlong ((𝓝[svGraph S] (x,u)) ×ˢ (𝓝[>] (0:ℝ)))
        (fun p : (E × F) × ℝ ↦ svGraph (mappingDifferenceQuotient S p.1.1 p.1.2 p.2)) := by
  change outerSetLimitAlong _ _ = _
  apply outerSetLimitAlong_congr
  have hpos : ∀ᶠ p in ((𝓝[svGraph S] (x,u)) ×ˢ (𝓝[>] (0:ℝ))), 0 < p.2 :=
    Filter.tendsto_snd self_mem_nhdsWithin
  filter_upwards [hpos] with p hp
  exact (svGraph_mappingDifferenceQuotient hp.ne').symm

/-- The sequence formulation (9.27), including moving input directions. -/
theorem mem_strictGraphicalDerivative_iff_sequences {S : E → Set F} {x w : E} {u z : F} :
    z ∈ strictGraphicalDerivative S x u w ↔
      ∃ (τ : ℕ → ℝ) (a : ℕ → E) (b : ℕ → F) (v : ℕ → E) (q : ℕ → F),
        (∀ n, 0 < τ n) ∧ Tendsto τ atTop (𝓝 0) ∧
        (∀ n, b n ∈ S (a n)) ∧ Tendsto a atTop (𝓝 x) ∧ Tendsto b atTop (𝓝 u) ∧
        Tendsto v atTop (𝓝 w) ∧ Tendsto q atTop (𝓝 z) ∧
        ∀ n, q n ∈ mappingDifferenceQuotient S (a n) (b n) (τ n) (v n) := by
  change (w,z) ∈ strictTangentCone (svGraph S) (x,u) ↔ _
  rw [mem_strictTangentCone_iff_exists_sequences]
  constructor
  · rintro ⟨a,b,τ,ha,hb,hat,hτ,hτt,hq⟩
    change Tendsto (fun n ↦ ((τ n)⁻¹ • ((b n).1-(a n).1),(τ n)⁻¹ • ((b n).2-(a n).2)))
      atTop (𝓝 (w,z)) at hq
    refine ⟨τ,fun n ↦ (a n).1,fun n ↦ (a n).2,
      fun n ↦ (τ n)⁻¹ • ((b n).1-(a n).1),fun n ↦ (τ n)⁻¹ • ((b n).2-(a n).2),
      hτ,hτt,ha,hat.fst_nhds,hat.snd_nhds,hq.fst_nhds,hq.snd_nhds,?_⟩
    intro n
    rw [mem_mappingDifferenceQuotient_iff (hτ n).ne']
    simpa only [smul_smul,mul_inv_cancel₀ (hτ n).ne',one_smul,add_sub_cancel] using hb n
  · rintro ⟨τ,a,b,v,q,hτ,hτt,hab,hat,hbt,hvt,hqt,hmem⟩
    refine ⟨fun n ↦ (a n,b n),fun n ↦ (a n + τ n • v n,b n + τ n • q n),τ,
      hab,fun n ↦ (mem_mappingDifferenceQuotient_iff (hτ n).ne').mp (hmem n),
      hat.prodMk_nhds hbt,hτ,hτt,?_⟩
    have he (n : ℕ) : (τ n)⁻¹ • ((a n + τ n • v n,b n + τ n • q n)-(a n,b n)) = (v n,q n) := by
      ext <;> simp [smul_smul,(hτ n).ne']
    simpa only [he] using hvt.prodMk_nhds hqt

theorem svOsc_strictGraphicalDerivative (S : E → Set F) (x : E) (u : F) :
    SvOsc (strictGraphicalDerivative S x u) :=
  isClosed_svGraph_iff_svOsc.mp (isClosed_strictTangentCone _ _)

theorem svPositivelyHomogeneous_strictGraphicalDerivative {S : E → Set F} {x : E} {u : F}
    (hu : u ∈ S x) : SvPositivelyHomogeneous (strictGraphicalDerivative S x u) :=
  svPositivelyHomogeneous_iff_isCone_svGraph.mpr (isCone_strictTangentCone hu)

theorem graphicalDerivative_subset_strictGraphicalDerivative {S : E → Set F} {x : E} {u : F}
    (hu : u ∈ S x) (w : E) : graphicalDerivative S x u w ⊆ strictGraphicalDerivative S x u w := by
  intro z hz
  apply tangentCone_subset_strictTangentCone (show (x,u) ∈ svGraph S from hu)
  change (w,z) ∈ svGraph (graphicalDerivative S x u) at hz
  rwa [svGraph_graphicalDerivative] at hz

/-- The strict derivative contains the graphical outer limit of nearby derivatives. -/
theorem outerLimit_graphicalDerivative_subset_strictGraphicalDerivative (S : E → Set F) (x : E) (u : F) :
    outerSetLimitAlong (𝓝[svGraph S] (x,u))
      (fun p : E × F ↦ svGraph (graphicalDerivative S p.1 p.2)) ⊆
      svGraph (strictGraphicalDerivative S x u) := by
  simpa only [svGraph_graphicalDerivative,svGraph_strictGraphicalDerivative] using
    outerLimit_tangentCone_subset_strictTangentCone (svGraph S) (x,u)

theorem strictGraphicalDerivative_svInv (S : E → Set F) (x : E) (u : F) :
    strictGraphicalDerivative (svInv S) u x = svInv (strictGraphicalDerivative S x u) := by
  ext z w
  change (z,w) ∈ strictTangentCone (svGraph (svInv S)) (u,x) ↔ _
  have he : svGraph (svInv S) = (ContinuousLinearEquiv.prodComm ℝ F E) ⁻¹' svGraph S := rfl
  rw [he,strictTangentCone_preimage_continuousLinearEquiv]
  rfl

/-- A continuous linear mapping agrees with its strict graphical derivative. -/
theorem strictGraphicalDerivative_singleton_continuousLinearMap (L : E →L[ℝ] F) (x w : E) :
    strictGraphicalDerivative (fun a ↦ {L a}) x (L x) w = {L w} := by
  ext z
  constructor
  · intro hz
    obtain ⟨τ,a,b,v,q,hτ,hτt,hab,hat,hbt,hvt,hqt,hmem⟩ :=
      mem_strictGraphicalDerivative_iff_sequences.mp hz
    have he (n : ℕ) : q n = L (v n) := by
      obtain ⟨y,hy,hyq⟩ := hmem n
      have hbn := mem_singleton_iff.mp (hab n)
      have hyn := mem_singleton_iff.mp hy
      simpa only [hyn,hbn,map_add,map_smul,add_sub_cancel_left,smul_smul,
        inv_mul_cancel₀ (hτ n).ne',one_smul] using hyq.symm
    apply mem_singleton_iff.mpr
    have hfun : q = L ∘ v := funext he
    exact tendsto_nhds_unique hqt (hfun ▸ L.continuous.continuousAt.tendsto.comp hvt)
  · rintro rfl
    apply mem_strictGraphicalDerivative_iff_sequences.mpr
    refine ⟨fun n ↦ 1/((n:ℝ)+1),fun _ ↦ x,fun _ ↦ L x,fun _ ↦ w,fun _ ↦ L w,
      fun _ ↦ by positivity,tendsto_one_div_add_atTop_nhds_zero_nat,
      fun _ ↦ mem_singleton _,tendsto_const_nhds,tendsto_const_nhds,
      tendsto_const_nhds,tendsto_const_nhds,?_⟩
    intro n
    rw [mem_mappingDifferenceQuotient_iff (by positivity)]
    simp only [mem_singleton_iff,map_add,map_smul]

end RW
