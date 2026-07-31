/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 3D: Horizon Functions in Pointwise Addition

This file formalizes the general horizon inequality, the convex equality, and
the coercivity consequences from Exercise 3.29.  The nonconvex inequality is
proved directly from asymptotic epigraph sequences, using affine minorants to
control the two normalized summands.
-/

import RockafellarWets.Chapter3.Coercivity
import RockafellarWets.Chapter3.EpiAddition

open Set EReal Topology Filter Bornology

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Affine lower bounds under pointwise addition -/

omit [NormedSpace ℝ E] in
/-- Affine norm minorants add under pointwise addition. -/
theorem HasAffineNormLowerBound.add
    {f g : E → EReal} {γ₁ γ₂ β₁ β₂ : ℝ}
    (hf : HasAffineNormLowerBound f γ₁ β₁)
    (hg : HasAffineNormLowerBound g γ₂ β₂) :
    HasAffineNormLowerBound (fun x => f x + g x) (γ₁ + γ₂) (β₁ + β₂) := by
  intro x
  calc
    ((((γ₁ + γ₂) * ‖x‖ + (β₁ + β₂) : ℝ)) : EReal) =
        ((γ₁ * ‖x‖ + β₁ : ℝ) : EReal) +
          ((γ₂ * ‖x‖ + β₂ : ℝ) : EReal) := by
            rw [← EReal.coe_add]
            congr 1
            ring
    _ ≤ f x + g x := add_le_add (hf x) (hg x)

omit [NormedSpace ℝ E] in
/-- An affine norm minorant remains valid after decreasing its slope. -/
theorem HasAffineNormLowerBound.mono_slope
    {f : E → EReal} {γ δ β : ℝ}
    (hf : HasAffineNormLowerBound f δ β) (hγδ : γ ≤ δ) :
    HasAffineNormLowerBound f γ β := by
  intro x
  have hreal : γ * ‖x‖ + β ≤ δ * ‖x‖ + β :=
    by
      simpa [add_comm] using
        add_le_add_right (mul_le_mul_of_nonneg_right hγδ (norm_nonneg x)) β
  exact le_trans (by exact_mod_cast hreal) (hf x)

/-- An affine norm minorant bounds the horizon function without any convexity
assumption.  This is the sequential form of the easy half of formula 3(3). -/
theorem HasAffineNormLowerBound.le_horizonFunction
    [FiniteDimensional ℝ E]
    {f : E → EReal} {γ β : ℝ} (hf : HasAffineNormLowerBound f γ β) (w : E) :
    ((γ * ‖w‖ : ℝ) : EReal) ≤ horizonFunction f w := by
  refine le_iInf ?_
  intro a
  have ha :
      (w, (a : ℝ)) = 0 ∨
        (w, (a : ℝ)) ∈ asymptoticCone ℝ (epigraph f) := by
    simpa [horizonCone] using a.property
  rcases ha with ha0 | ha
  · have hw : w = 0 := congrArg Prod.fst ha0
    have haa : (a : ℝ) = 0 := congrArg Prod.snd ha0
    simp [hw, haa]
  · rcases exists_seq_pos_smul_of_mem_asymptoticCone ha with
      ⟨c, u, hc, hu, hcpos, hmem⟩
    have hineq : ∀ n, γ * ‖(u n).1‖ + β / c n ≤ (u n).2 := by
      intro n
      have hepi := hmem n
      rw [mem_epigraph_iff] at hepi
      have hlower := hf (c n • (u n).1)
      have hreal :
          γ * ‖c n • (u n).1‖ + β ≤ c n * (u n).2 := by
        exact_mod_cast hlower.trans hepi
      have hcn : 0 < c n := hcpos n
      rw [norm_smul, Real.norm_of_nonneg hcn.le] at hreal
      have heq :
          γ * ‖(u n).1‖ + β / c n =
            (γ * (c n * ‖(u n).1‖) + β) / c n := by
        field_simp [hcn.ne']
      rw [heq, div_le_iff₀ hcn]
      linarith
    have hcInv : Tendsto (fun n => (c n)⁻¹) atTop (𝓝 0) :=
      hc.inv_tendsto_atTop
    have hlowerTendsto :
        Tendsto (fun n => γ * ‖(u n).1‖ + β / c n) atTop
          (𝓝 (γ * ‖w‖)) := by
      have huFst : Tendsto (fun n => (u n).1) atTop (𝓝 w) :=
        continuous_fst.continuousAt.tendsto.comp hu
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul (tendsto_norm.comp huFst)).add
          (tendsto_const_nhds.mul hcInv)
    have huSnd : Tendsto (fun n => (u n).2) atTop (𝓝 (a : ℝ)) :=
      continuous_snd.continuousAt.tendsto.comp hu
    exact_mod_cast
      le_of_tendsto_of_tendsto hlowerTendsto huSnd
        (Eventually.of_forall hineq)

omit [NormedSpace ℝ E] in
/-- Exercise 3.29(a), affine-minorant form: adding a function with a real
global lower bound preserves level coercivity. -/
theorem IsLevelCoercive.add_of_hasRealLowerBound
    {f g : E → EReal} (hf : IsLevelCoercive f)
    {β : ℝ} (hg : ∀ x, (β : EReal) ≤ g x) :
    IsLevelCoercive (fun x => f x + g x) := by
  rcases hf with ⟨γ, hγ, α, hf⟩
  refine ⟨γ, hγ, α + β, ?_⟩
  have hg' : HasAffineNormLowerBound g 0 β := by
    intro x
    simpa using hg x
  simpa using hf.add hg'

omit [NormedSpace ℝ E] in
/-- Symmetric form of Exercise 3.29(a). -/
theorem IsLevelCoercive.add_left_of_hasRealLowerBound
    {f g : E → EReal} (hg : IsLevelCoercive g)
    {β : ℝ} (hf : ∀ x, (β : EReal) ≤ f x) :
    IsLevelCoercive (fun x => f x + g x) := by
  rcases hg with ⟨γ, hγ, α, hg⟩
  refine ⟨γ, hγ, β + α, ?_⟩
  have hf' : HasAffineNormLowerBound f 0 β := by
    intro x
    simpa using hf x
  simpa using hf'.add hg

omit [NormedSpace ℝ E] in
/-- The sum of two level-coercive functions is level-coercive. -/
theorem IsLevelCoercive.add
    {f g : E → EReal} (hf : IsLevelCoercive f) (hg : IsLevelCoercive g) :
    IsLevelCoercive (fun x => f x + g x) := by
  rcases hf with ⟨γ₁, hγ₁, β₁, hf⟩
  rcases hg with ⟨γ₂, hγ₂, β₂, hg⟩
  exact ⟨γ₁ + γ₂, add_pos hγ₁ hγ₂, β₁ + β₂, hf.add hg⟩

/-- Exercise 3.29(b): adding a non-counter-coercive function to a coercive
function preserves coercivity. -/
theorem IsCoercive.add_of_not_isCounterCoercive
    {f g : E → EReal} (hf : IsCoercive f) (hg : ¬ IsCounterCoercive g) :
    IsCoercive (fun x => f x + g x) := by
  rcases exists_affineNormLowerBound_of_not_isCounterCoercive hg with
    ⟨δ, βg, hg⟩
  intro γ hγ
  let η : ℝ := γ + |δ| + 1
  have hη : 0 < η := by
    dsimp [η]
    positivity
  rcases hf η hη with ⟨βf, hf⟩
  refine ⟨βf + βg, ?_⟩
  apply (hf.add hg).mono_slope
  dsimp [η]
  have hδ : 0 ≤ |δ| + δ := by
    exact neg_le_iff_add_nonneg.mp (neg_le_abs δ)
  linarith

/-- Symmetric form of Exercise 3.29(b). -/
theorem IsCoercive.add_left_of_not_isCounterCoercive
    {f g : E → EReal} (hg : IsCoercive g) (hf : ¬ IsCounterCoercive f) :
    IsCoercive (fun x => f x + g x) := by
  have h := hg.add_of_not_isCounterCoercive hf
  simpa [add_comm] using h

/-- The sum of two coercive functions is coercive. -/
theorem IsCoercive.add
    {f g : E → EReal} (hf : IsCoercive f) (hg : IsCoercive g) :
    IsCoercive (fun x => f x + g x) :=
  hf.add_of_not_isCounterCoercive
    (not_isCounterCoercive_of_isLevelCoercive
      (isLevelCoercive_of_isCoercive hg))

/-! ## Exercise 3.29: the general horizon inequality -/

/-- Exercise 3.29, general case: for proper functions which are not
counter-coercive, the horizon function of their pointwise sum dominates the
sum of their horizon functions.  The lower-semicontinuity assumptions are
included exactly as in the statement in the book; the asymptotic-sequence
argument itself only needs properness and affine minorants. -/
theorem add_horizonFunction_le_horizonFunction_pointwiseAdd
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (_hflsc : LowerSemicontinuous f) (_hglsc : LowerSemicontinuous g)
    (hfproper : IsProper f) (hgproper : IsProper g)
    (hfnot : ¬ IsCounterCoercive f) (hgnot : ¬ IsCounterCoercive g) :
    (fun w => horizonFunction f w + horizonFunction g w) ≤
      horizonFunction (fun x => f x + g x) := by
  rcases exists_affineNormLowerBound_of_not_isCounterCoercive hfnot with
    ⟨γf, βf, hfminor⟩
  rcases exists_affineNormLowerBound_of_not_isCounterCoercive hgnot with
    ⟨γg, βg, hgminor⟩
  intro w
  refine le_iInf ?_
  intro a
  have ha :
      (w, (a : ℝ)) = 0 ∨
        (w, (a : ℝ)) ∈
          asymptoticCone ℝ (epigraph (fun x => f x + g x)) := by
    simpa [horizonCone] using a.property
  rcases ha with ha0 | ha
  · have hw : w = 0 := congrArg Prod.fst ha0
    have haa : (a : ℝ) = 0 := congrArg Prod.snd ha0
    have hfzero : horizonFunction f (0 : E) = 0 := by
      apply le_antisymm
      · exact horizonFunction_le_of_mem_horizonCone_epigraph
          (zero_mem_horizonCone (epigraph f))
      · simpa using hfminor.le_horizonFunction (0 : E)
    have hgzero : horizonFunction g (0 : E) = 0 := by
      apply le_antisymm
      · exact horizonFunction_le_of_mem_horizonCone_epigraph
          (zero_mem_horizonCone (epigraph g))
      · simpa using hgminor.le_horizonFunction (0 : E)
    simp [hw, haa, hfzero, hgzero]
  · rcases exists_seq_pos_smul_of_mem_asymptoticCone ha with
      ⟨c, u, hc, hu, hcpos, hmem⟩
    let x : ℕ → E := fun n => (u n).1
    let b : ℕ → ℝ := fun n => (u n).2
    let r : ℕ → ℝ := fun n => (f (c n • x n)).toReal / c n
    let s : ℕ → ℝ := fun n => (g (c n • x n)).toReal / c n
    have hx : Tendsto x atTop (𝓝 w) :=
      continuous_fst.continuousAt.tendsto.comp hu
    have hb : Tendsto b atTop (𝓝 (a : ℝ)) :=
      continuous_snd.continuousAt.tendsto.comp hu
    have hfinite :
        ∀ n,
          f (c n • x n) ≠ ⊤ ∧ g (c n • x n) ≠ ⊤ := by
      intro n
      have hepi := hmem n
      rw [mem_epigraph_iff] at hepi
      have hepi' :
          f (c n • x n) + g (c n • x n) ≤
            ((c n * b n : ℝ) : EReal) := by
        simpa [x, b, Prod.smul_mk, smul_eq_mul] using hepi
      have hsumtop :
          f (c n • x n) + g (c n • x n) ≠ ⊤ :=
        ne_of_lt (hepi'.trans_lt (EReal.coe_lt_top _))
      exact
        (EReal.add_ne_top_iff_ne_top₂
          (ne_of_gt (hfproper.2 _)) (ne_of_gt (hgproper.2 _))).mp hsumtop
    have hsum : ∀ n, r n + s n ≤ b n := by
      intro n
      have hepi := hmem n
      rw [mem_epigraph_iff] at hepi
      have hepi' :
          f (c n • x n) + g (c n • x n) ≤
            ((c n * b n : ℝ) : EReal) := by
        simpa [x, b, Prod.smul_mk, smul_eq_mul] using hepi
      have hbotf : f (c n • x n) ≠ ⊥ := ne_of_gt (hfproper.2 _)
      have hbotg : g (c n • x n) ≠ ⊥ := ne_of_gt (hgproper.2 _)
      have hreal :
          (f (c n • x n)).toReal + (g (c n • x n)).toReal ≤
            c n * b n := by
        rw [← EReal.coe_toReal (hfinite n).1 hbotf,
          ← EReal.coe_toReal (hfinite n).2 hbotg, ← EReal.coe_add] at hepi'
        exact_mod_cast hepi'
      dsimp [r, s]
      rw [← add_div]
      exact (div_le_iff₀ (hcpos n)).2 (by simpa [mul_comm] using hreal)
    have hrlower : ∀ n, γf * ‖x n‖ + βf / c n ≤ r n := by
      intro n
      have hminor := hfminor (c n • x n)
      have hreal :
          γf * ‖c n • x n‖ + βf ≤
            (f (c n • x n)).toReal := by
        exact_mod_cast (show
          ((γf * ‖c n • x n‖ + βf : ℝ) : EReal) ≤
            (((f (c n • x n)).toReal : ℝ) : EReal) by
              simpa [EReal.coe_toReal (hfinite n).1
                (ne_of_gt (hfproper.2 _))] using hminor)
      rw [norm_smul, Real.norm_of_nonneg (hcpos n).le] at hreal
      dsimp [r]
      apply (le_div_iff₀ (hcpos n)).2
      field_simp [ne_of_gt (hcpos n)]
      nlinarith
    have hslower : ∀ n, γg * ‖x n‖ + βg / c n ≤ s n := by
      intro n
      have hminor := hgminor (c n • x n)
      have hreal :
          γg * ‖c n • x n‖ + βg ≤
            (g (c n • x n)).toReal := by
        exact_mod_cast (show
          ((γg * ‖c n • x n‖ + βg : ℝ) : EReal) ≤
            (((g (c n • x n)).toReal : ℝ) : EReal) by
              simpa [EReal.coe_toReal (hfinite n).2
                (ne_of_gt (hgproper.2 _))] using hminor)
      rw [norm_smul, Real.norm_of_nonneg (hcpos n).le] at hreal
      dsimp [s]
      apply (le_div_iff₀ (hcpos n)).2
      field_simp [ne_of_gt (hcpos n)]
      nlinarith
    have hcinv : Tendsto (fun n => (c n)⁻¹) atTop (𝓝 0) :=
      hc.inv_tendsto_atTop
    obtain ⟨X, hX⟩ :=
      (Metric.isBounded_range_of_tendsto x hx).exists_norm_le
    obtain ⟨B, hB⟩ :=
      (Metric.isBounded_range_of_tendsto b hb).exists_norm_le
    obtain ⟨D, hD⟩ :=
      (Metric.isBounded_range_of_tendsto (fun n => (c n)⁻¹) hcinv).exists_norm_le
    let Kf : ℝ := |γf| * X + |βf| * D
    let Kg : ℝ := |γg| * X + |βg| * D
    have hflow : ∀ n, -Kf ≤ r n := by
      intro n
      have hxnorm : ‖x n‖ ≤ X := hX _ ⟨n, rfl⟩
      have hdinv : |(c n)⁻¹| ≤ D := by
        simpa [Real.norm_eq_abs] using hD _ ⟨n, rfl⟩
      have hγ :
          |γf * ‖x n‖| ≤ |γf| * X := by
        rw [_root_.abs_mul, abs_norm]
        exact mul_le_mul_of_nonneg_left hxnorm (abs_nonneg γf)
      have hβ :
          |βf / c n| ≤ |βf| * D := by
        rw [div_eq_mul_inv, _root_.abs_mul]
        exact mul_le_mul_of_nonneg_left hdinv (abs_nonneg βf)
      have hminor :
          -(Kf) ≤ γf * ‖x n‖ + βf / c n := by
        dsimp [Kf]
        nlinarith [neg_abs_le (γf * ‖x n‖), neg_abs_le (βf / c n)]
      exact hminor.trans (hrlower n)
    have hglow : ∀ n, -Kg ≤ s n := by
      intro n
      have hxnorm : ‖x n‖ ≤ X := hX _ ⟨n, rfl⟩
      have hdinv : |(c n)⁻¹| ≤ D := by
        simpa [Real.norm_eq_abs] using hD _ ⟨n, rfl⟩
      have hγ :
          |γg * ‖x n‖| ≤ |γg| * X := by
        rw [_root_.abs_mul, abs_norm]
        exact mul_le_mul_of_nonneg_left hxnorm (abs_nonneg γg)
      have hβ :
          |βg / c n| ≤ |βg| * D := by
        rw [div_eq_mul_inv, _root_.abs_mul]
        exact mul_le_mul_of_nonneg_left hdinv (abs_nonneg βg)
      have hminor :
          -(Kg) ≤ γg * ‖x n‖ + βg / c n := by
        dsimp [Kg]
        nlinarith [neg_abs_le (γg * ‖x n‖), neg_abs_le (βg / c n)]
      exact hminor.trans (hslower n)
    have hrupper : ∀ n, r n ≤ B + Kg := by
      intro n
      have hbupper : b n ≤ B := by
        exact le_trans (le_abs_self (b n)) (by
          simpa [Real.norm_eq_abs] using hB _ ⟨n, rfl⟩)
      linarith [hsum n, hglow n]
    have hsupper : ∀ n, s n ≤ B + Kf := by
      intro n
      have hbupper : b n ≤ B := by
        exact le_trans (le_abs_self (b n)) (by
          simpa [Real.norm_eq_abs] using hB _ ⟨n, rfl⟩)
      linarith [hsum n, hflow n]
    have hrbounded : IsBounded (Set.range r) :=
      Metric.isBounded_of_bddAbove_of_bddBelow
        ⟨B + Kg, by rintro _ ⟨n, rfl⟩; exact hrupper n⟩
        ⟨-Kf, by rintro _ ⟨n, rfl⟩; exact hflow n⟩
    have hsbounded : IsBounded (Set.range s) :=
      Metric.isBounded_of_bddAbove_of_bddBelow
        ⟨B + Kf, by rintro _ ⟨n, rfl⟩; exact hsupper n⟩
        ⟨-Kg, by rintro _ ⟨n, rfl⟩; exact hglow n⟩
    rcases tendsto_subseq_of_bounded hrbounded (fun n => ⟨n, rfl⟩) with
      ⟨r₀, _hr₀, φ, hφ, hrφ⟩
    have hsφbounded : IsBounded (Set.range (s ∘ φ)) :=
      hsbounded.subset <| by
        rintro _ ⟨n, rfl⟩
        exact ⟨φ n, rfl⟩
    rcases tendsto_subseq_of_bounded hsφbounded (fun n => ⟨n, rfl⟩) with
      ⟨s₀, _hs₀, ψ, hψ, hsφψ⟩
    let θ : ℕ → ℕ := φ ∘ ψ
    have hθ : StrictMono θ := hφ.comp hψ
    have hθtop : Tendsto θ atTop atTop := hθ.tendsto_atTop
    have hrθ : Tendsto (r ∘ θ) atTop (𝓝 r₀) := hrφ.comp hψ.tendsto_atTop
    have hsθ : Tendsto (s ∘ θ) atTop (𝓝 s₀) := by
      simpa [θ, Function.comp_def] using hsφψ
    have hxθ : Tendsto (x ∘ θ) atTop (𝓝 w) := hx.comp hθtop
    have hbθ : Tendsto (b ∘ θ) atTop (𝓝 (a : ℝ)) := hb.comp hθtop
    have hcθ : Tendsto (c ∘ θ) atTop atTop := hc.comp hθtop
    have hfr :
        horizonFunction f w ≤ (r₀ : EReal) := by
      apply horizonFunction_le_of_mem_horizonCone_epigraph
      apply Set.mem_insert_of_mem 0
      apply mem_asymptoticCone_of_seq_smul hcθ
        (hxθ.prodMk_nhds hrθ)
      intro n
      rw [mem_epigraph_iff]
      have htop := (hfinite (θ n)).1
      have hbot : f (c (θ n) • x (θ n)) ≠ ⊥ :=
        ne_of_gt (hfproper.2 _)
      rw [Prod.smul_mk, smul_eq_mul]
      change
        f (c (θ n) • x (θ n)) ≤
          ((c (θ n) * r (θ n) : ℝ) : EReal)
      rw [← EReal.coe_toReal htop hbot]
      exact_mod_cast (by
        dsimp [r]
        field_simp [ne_of_gt (hcpos (θ n))]
        exact le_rfl)
    have hgs :
        horizonFunction g w ≤ (s₀ : EReal) := by
      apply horizonFunction_le_of_mem_horizonCone_epigraph
      apply Set.mem_insert_of_mem 0
      apply mem_asymptoticCone_of_seq_smul hcθ
        (hxθ.prodMk_nhds hsθ)
      intro n
      rw [mem_epigraph_iff]
      have htop := (hfinite (θ n)).2
      have hbot : g (c (θ n) • x (θ n)) ≠ ⊥ :=
        ne_of_gt (hgproper.2 _)
      rw [Prod.smul_mk, smul_eq_mul]
      change
        g (c (θ n) • x (θ n)) ≤
          ((c (θ n) * s (θ n) : ℝ) : EReal)
      rw [← EReal.coe_toReal htop hbot]
      exact_mod_cast (by
        dsimp [s]
        field_simp [ne_of_gt (hcpos (θ n))]
        exact le_rfl)
    have hrs : r₀ + s₀ ≤ (a : ℝ) := by
      exact le_of_tendsto_of_tendsto (hrθ.add hsθ) hbθ
        (Eventually.of_forall fun n => hsum (θ n))
    calc
      horizonFunction f w + horizonFunction g w ≤
          (r₀ : EReal) + (s₀ : EReal) :=
        add_le_add hfr hgs
      _ = ((r₀ + s₀ : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ ≤ (a : EReal) := by exact_mod_cast hrs

/-! ## Closed-convex linear preimages -/

/-- For a nonempty linear preimage of a closed convex set, taking the horizon
cone commutes with taking that preimage. -/
theorem horizonCone_preimage_linearMap_eq
    {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →ₗ[ℝ] G) {C : Set G}
    (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (hne : (L ⁻¹' C).Nonempty) :
    horizonCone (L ⁻¹' C) = L ⁻¹' horizonCone C := by
  apply Set.Subset.antisymm
  · intro w hw
    change L w ∈ horizonCone C
    rcases hne with ⟨x, hx⟩
    apply mem_horizonCone_of_forall_smul_add_mem (x := L x)
    intro τ hτ
    simpa using
      smul_add_mem_of_mem_horizonCone
        (hconv.linear_preimage L)
        (hclosed.preimage L.continuous_of_finiteDimensional)
        hx hw hτ
  · intro w hw
    change L w ∈ horizonCone C at hw
    rcases hne with ⟨x, hx⟩
    apply mem_horizonCone_of_forall_smul_add_mem (x := x)
    intro τ hτ
    change L (τ • w + x) ∈ C
    simpa using
      smul_add_mem_of_mem_horizonCone hconv hclosed hx hw hτ

/-- The linear map on epigraph ambient spaces induced by precomposition. -/
private def epigraphPrecomposeLinearMap
    {F G : Type*} [AddCommMonoid F] [Module ℝ F]
    [AddCommMonoid G] [Module ℝ G]
    (L : F →ₗ[ℝ] G) : (F × ℝ) →ₗ[ℝ] (G × ℝ) :=
  (L.comp (LinearMap.fst ℝ F ℝ)).prod (LinearMap.snd ℝ F ℝ)

@[simp] private theorem epigraphPrecomposeLinearMap_apply
    {F G : Type*} [AddCommMonoid F] [Module ℝ F]
    [AddCommMonoid G] [Module ℝ G]
    (L : F →ₗ[ℝ] G) (p : F × ℝ) :
    epigraphPrecomposeLinearMap L p = (L p.1, p.2) :=
  rfl

/-- Horizon functions commute with linear precomposition when the original
epigraph is closed and convex and the precomposed epigraph is nonempty. -/
theorem horizonFunction_precompose_linearMap_eq
    {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → EReal} (L : F →ₗ[ℝ] G)
    (hconv : Convex ℝ (epigraph f)) (hclosed : IsClosed (epigraph f))
    (hne : (epigraph (fun x : F => f (L x))).Nonempty) :
    horizonFunction (fun x : F => f (L x)) =
      fun w : F => horizonFunction f (L w) := by
  let M : (F × ℝ) →ₗ[ℝ] (G × ℝ) := epigraphPrecomposeLinearMap L
  have hpre :
      M ⁻¹' epigraph f = epigraph (fun x : F => f (L x)) := by
    ext p
    change f (L p.1) ≤ (p.2 : EReal) ↔
      p ∈ epigraph (fun x : F => f (L x))
    rw [mem_epigraph_iff]
  have hnepre : (M ⁻¹' epigraph f).Nonempty := by
    simpa [hpre] using hne
  have hnef : (epigraph f).Nonempty := by
    rcases hnepre with ⟨p, hp⟩
    exact ⟨M p, hp⟩
  apply eq_of_epigraph_eq
  calc
    epigraph (horizonFunction (fun x : F => f (L x))) =
        horizonCone (epigraph (fun x : F => f (L x))) :=
      epigraph_horizonFunction_eq_horizonCone_epigraph hne
    _ = horizonCone (M ⁻¹' epigraph f) := by rw [hpre]
    _ = M ⁻¹' horizonCone (epigraph f) :=
      horizonCone_preimage_linearMap_eq M hconv hclosed hnepre
    _ = M ⁻¹' epigraph (horizonFunction f) := by
      rw [epigraph_horizonFunction_eq_horizonCone_epigraph hnef]
    _ = epigraph (fun w : F => horizonFunction f (L w)) := by
      ext p
      change horizonFunction f (L p.1) ≤ (p.2 : EReal) ↔
        p ∈ epigraph (fun w : F => horizonFunction f (L w))
      rw [mem_epigraph_iff]

/-! ## Exercise 3.29: convex horizon equality -/

/-- The diagonal embedding used to view pointwise addition as a restriction of
the epi-sum integrand: `(x, 2x)` is sent to `f x + g x`. -/
private def pointwiseAddEmbedding :
    E →ₗ[ℝ] E × E :=
  (LinearMap.id : E →ₗ[ℝ] E).prod
    ((LinearMap.id : E →ₗ[ℝ] E) + LinearMap.id)

@[simp] private theorem pointwiseAddEmbedding_apply (x : E) :
    pointwiseAddEmbedding x = (x, x + x) := by
  simp [pointwiseAddEmbedding]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Proper functions with a common finite-domain point have a proper pointwise
sum. -/
theorem isProper_pointwiseAdd_of_nonempty_effectiveDomain_inter
    {f g : E → EReal} (hf : IsProper f) (hg : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    IsProper (fun x => f x + g x) := by
  refine ⟨?_, ?_⟩
  · rcases hdom with ⟨x, hxf, hxg⟩
    refine ⟨x, EReal.add_lt_top ?_ ?_⟩
    · exact ne_of_lt ((mem_effectiveDomain_iff f x).1 hxf)
    · exact ne_of_lt ((mem_effectiveDomain_iff g x).1 hxg)
  · intro x
    exact EReal.bot_lt_add_iff.mpr ⟨hf.2 x, hg.2 x⟩

/-- Exercise 3.29, convex case: for proper lsc convex functions with a common
finite-domain point, the horizon function of their pointwise sum is the sum of
their horizon functions. -/
theorem horizonFunction_pointwiseAdd_eq_add
    [FiniteDimensional ℝ E]
    {f g : E → EReal}
    (hfconv : Convex ℝ (epigraph f)) (hgconv : Convex ℝ (epigraph g))
    (hflsc : LowerSemicontinuous f) (hglsc : LowerSemicontinuous g)
    (hfproper : IsProper f) (hgproper : IsProper g)
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty) :
    horizonFunction (fun x => f x + g x) =
      fun w => horizonFunction f w + horizonFunction g w := by
  let L : E →ₗ[ℝ] E × E := pointwiseAddEmbedding
  have hfun :
      (fun x : E => epiSumIntegrand f g (L x)) =
        fun x => f x + g x := by
    funext x
    simp [L, epiSumIntegrand, sub_eq_add_neg, add_assoc]
  have hconvIntegrand :
      Convex ℝ (epigraph (epiSumIntegrand f g)) := by
    rw [show epigraph (epiSumIntegrand f g) =
        epiSumLinearMap '' (epigraph f ×ˢ epigraph g) by
      simpa [epiSumIntegrand] using
        (image_epiSumLinearMap_eq_epigraph hfproper.2 hgproper.2).symm]
    exact (hfconv.prod hgconv).linear_image epiSumLinearMap
  have hclosedIntegrand :
      IsClosed (epigraph (epiSumIntegrand f g)) :=
    isClosed_epigraph_of_lsc_ereal _
      (lowerSemicontinuous_epiSumIntegrand
        hflsc hglsc hfproper hgproper)
  have hne :
      (epigraph (fun x : E => epiSumIntegrand f g (L x))).Nonempty := by
    rw [hfun]
    exact epigraph_nonempty_of_isProper
      (isProper_pointwiseAdd_of_nonempty_effectiveDomain_inter
        hfproper hgproper hdom)
  have hprecompose :=
    horizonFunction_precompose_linearMap_eq
      L hconvIntegrand hclosedIntegrand hne
  have hintegrand :=
    horizonFunction_epiSumIntegrand_eq_add
      hfconv hgconv hflsc hglsc hfproper hgproper
  rw [← hfun]
  funext w
  calc
    horizonFunction (fun x : E => epiSumIntegrand f g (L x)) w =
        horizonFunction (epiSumIntegrand f g) (L w) :=
      congrFun hprecompose w
    _ = horizonFunction f w + horizonFunction g w := by
      rw [hintegrand]
      simp [L, sub_eq_add_neg, add_assoc]

end RW
