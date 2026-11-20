/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Fenchel-type duality scheme

Example 11.41.
-/
import RockafellarWets.Chapter11.MinimaxRelations
import RockafellarWets.Chapter11.PrimalDualBestCase
import RockafellarWets.Chapter10.PLQCalculus

open Set Filter Topology
open scoped InnerProductSpace Pointwise
namespace RW
noncomputable section

/-- Splitting a finite difference against a sum of two values other than `-∞`. -/
theorem ereal_coe_sub_split {r m n t s : ℝ} {a d : EReal} (ha : a ≠ ⊥) (hd : d ≠ ⊥)
    (hr : r = n + t + s + m) :
    (r : EReal) - ((m : EReal) + a + d) = ((n : EReal) + ((t : EReal) - d)) + ((s : EReal) - a) := by
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | top =>
    induction d using EReal.rec with
    | bot => exact absurd rfl hd
    | top => simp
    | coe d => simp
  | coe a =>
    induction d using EReal.rec with
    | bot => exact absurd rfl hd
    | top => simp
    | coe d =>
      norm_cast
      rw [hr]
      ring

theorem ereal_neg_neg_coe_add_add {β : ℝ} {H K : EReal} (hH : H ≠ ⊥) (hK : K ≠ ⊥) :
    -(-(β : EReal) + H + K) = (β : EReal) - H - K := by
  induction H using EReal.rec with
  | bot => exact absurd rfl hH
  | top =>
    induction K using EReal.rec with
    | bot => exact absurd rfl hK
    | top => simp
    | coe K => simp
  | coe H =>
    induction K using EReal.rec with
    | bot => exact absurd rfl hK
    | top => simp
    | coe K =>
      norm_cast
      ring

theorem ereal_coe_sub_sub_ne_top {β : ℝ} {H K : EReal} (hH : H ≠ ⊥) (hK : K ≠ ⊥) :
    (β : EReal) - H - K ≠ ⊤ := by
  induction H using EReal.rec with
  | bot => exact absurd rfl hH
  | top => simp
  | coe H =>
    induction K using EReal.rec with
    | bot => exact absurd rfl hK
    | top => simp
    | coe K => exact_mod_cast EReal.coe_ne_top _

theorem ne_top_of_ereal_coe_sub_sub_ne_bot {β : ℝ} {H K : EReal}
    (h : (β : EReal) - H - K ≠ ⊥) : H ≠ ⊤ ∧ K ≠ ⊤ := by
  constructor
  · rintro rfl
    simp at h
  · rintro rfl
    simp at h

private theorem fenchelConjugate_ne_bot_of_isProper {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {g : F → EReal} (hg : IsProper g) (v : F) :
    fenchelConjugate g v ≠ ⊥ := by
  obtain ⟨z, hz⟩ := hg.1
  exact (bot_lt_fenchelConjugate_of_finite (EReal.coe_toReal hz.ne (hg.2 z).ne').symm v).ne'

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

/-- The perturbation integrand `f(x,u) = ⟨c,x⟩ + k(x) + h(b - Ax + u)` of **11.41**. -/
def fenchelIntegrand (k : E → EReal) (h : P → EReal) (A : E →L[ℝ] P) (b : P) (c : E) :
    WithLp 2 (E × P) → EReal :=
  fun q ↦ (⟪c, q.fst⟫_ℝ : EReal) + k q.fst + h (b - A q.fst + q.snd)

/-- The primal objective `φ(x) = ⟨c,x⟩ + k(x) + h(b - Ax)` of **11.41**. -/
def fenchelPrimal (k : E → EReal) (h : P → EReal) (A : E →L[ℝ] P) (b : P) (c : E) (x : E) :
    EReal :=
  (⟪c, x⟫_ℝ : EReal) + k x + h (b - A x)

/-- The dual objective `ψ(y) = ⟨b,y⟩ - h*(y) - k*(A*y - c)` of **11.41**. -/
def fenchelDual (k : E → EReal) (h : P → EReal) (A : E →L[ℝ] P) (b : P) (c : E) (y : P) :
    EReal :=
  (⟪b, y⟫_ℝ : EReal) - fenchelConjugate h y - fenchelConjugate k (A.adjoint y - c)

variable {k : E → EReal} {h : P → EReal} (A : E →L[ℝ] P) (b : P) (c : E)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem primalObjective_fenchelIntegrand :
    primalObjective (fenchelIntegrand k h A b c) = fenchelPrimal k h A b c := by
  funext x
  change (⟪c, x⟫_ℝ : EReal) + k x + h (b - A x + 0) = _
  rw [add_zero]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem fenchelIntegrand_ne_bot (hkb : ∀ x, k x ≠ ⊥) (hhb : ∀ w, h w ≠ ⊥)
    (q : WithLp 2 (E × P)) : fenchelIntegrand k h A b c q ≠ ⊥ := by
  simp only [fenchelIntegrand, ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, hkb, hhb,
    or_self, not_false_eq_true]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem fenchelIntegrand_lt_top_iff (hkb : ∀ x, k x ≠ ⊥) (hhb : ∀ w, h w ≠ ⊥) (x : E) (u : P) :
    fenchelIntegrand k h A b c (WithLp.toLp 2 (x, u)) < ⊤ ↔ k x < ⊤ ∧ h (b - A x + u) < ⊤ := by
  change (⟪c, x⟫_ℝ : EReal) + k x + h (b - A x + u) < ⊤ ↔ _
  simp only [lt_top_iff_ne_top]
  rw [EReal.add_ne_top_iff_ne_top₂ (by simp [hkb]) (hhb _),
    EReal.add_ne_top_iff_ne_top₂ (EReal.coe_ne_bot _) (hkb x)]
  simp

/-- The conjugate formula in **11.41**: `f*(v,y) = -⟨b,y⟩ + h*(y) + k*(A*y - c + v)`. -/
theorem fenchelConjugate_fenchelIntegrand (hkb : ∀ x, k x ≠ ⊥) (hhb : ∀ w, h w ≠ ⊥)
    (v : E) (y : P) :
    fenchelConjugate (fenchelIntegrand k h A b c) (WithLp.toLp 2 (v, y)) =
      -(⟪b, y⟫_ℝ : EReal) + fenchelConjugate h y + fenchelConjugate k (A.adjoint y - c + v) := by
  have hshift (x : E) : (⨆ u : P, (⟪WithLp.toLp 2 (v, y), WithLp.toLp 2 (x, u)⟫_ℝ : EReal) -
        fenchelIntegrand k h A b c (WithLp.toLp 2 (x, u))) =
      ⨆ w : P, ((((-⟪b, y⟫_ℝ : ℝ) : EReal) + ((⟪y, w⟫_ℝ : EReal) - h w)) +
        ((⟪A.adjoint y - c + v, x⟫_ℝ : EReal) - k x)) := by
    refine (Equiv.subRight (b - A x)).iSup_comp.symm.trans (iSup_congr fun w ↦ ?_)
    have hw : b - A x + (w - (b - A x)) = w := by abel
    have h₁ : ⟪WithLp.toLp 2 (v, y), WithLp.toLp 2 (x, w - (b - A x))⟫_ℝ =
        ⟪v, x⟫_ℝ + ⟪y, w - (b - A x)⟫_ℝ := by
      rw [WithLp.prod_inner_apply]
    have hi : ⟪WithLp.toLp 2 (v, y), WithLp.toLp 2 (x, w - (b - A x))⟫_ℝ =
        -⟪b, y⟫_ℝ + ⟪y, w⟫_ℝ + ⟪A.adjoint y - c + v, x⟫_ℝ + ⟪c, x⟫_ℝ := by
      rw [h₁, inner_add_left, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
        inner_sub_right, inner_sub_right, real_inner_comm b y]
      ring
    change (⟪WithLp.toLp 2 (v, y), WithLp.toLp 2 (x, w - (b - A x))⟫_ℝ : EReal) -
      ((⟪c, x⟫_ℝ : EReal) + k x + h (b - A x + (w - (b - A x)))) = _
    rw [hw]
    exact ereal_coe_sub_split (hkb x) (hhb w) hi
  calc fenchelConjugate (fenchelIntegrand k h A b c) (WithLp.toLp 2 (v, y))
      = ⨆ x : E, ⨆ u : P, (⟪WithLp.toLp 2 (v, y), WithLp.toLp 2 (x, u)⟫_ℝ : EReal) -
          fenchelIntegrand k h A b c (WithLp.toLp 2 (x, u)) := by
        rw [fenchelConjugate, ← (WithLp.toLp_surjective 2).iSup_comp, iSup_prod]
    _ = ⨆ x : E, ⨆ w : P, ((((-⟪b, y⟫_ℝ : ℝ) : EReal) + ((⟪y, w⟫_ℝ : EReal) - h w)) +
          ((⟪A.adjoint y - c + v, x⟫_ℝ : EReal) - k x)) := iSup_congr hshift
    _ = ⨆ x : E, ((((-⟪b, y⟫_ℝ : ℝ) : EReal) + fenchelConjugate h y) +
          ((⟪A.adjoint y - c + v, x⟫_ℝ : EReal) - k x)) := by
        refine iSup_congr fun x ↦ ?_
        rw [← ereal_iSup_add, ← ereal_add_iSup]
        rfl
    _ = _ := by
        rw [← ereal_add_iSup, EReal.coe_neg]
        rfl

/-- The dual problem of **11.41**: `-f*(0,y) = ⟨b,y⟩ - h*(y) - k*(A*y - c)`. -/
theorem dualObjective_fenchelIntegrand (hk : IsProper k) (hh : IsProper h) :
    dualObjective (fenchelIntegrand k h A b c) = fenchelDual k h A b c := by
  funext y
  rw [dualObjective, fenchelConjugate_fenchelIntegrand A b c (fun x ↦ (hk.2 x).ne')
    (fun w ↦ (hh.2 w).ne'), add_zero]
  exact ereal_neg_neg_coe_add_add (fenchelConjugate_ne_bot_of_isProper hh y)
    (fenchelConjugate_ne_bot_of_isProper hk _)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem isProper_fenchelIntegrand (hk : IsProper k) (hh : IsProper h) :
    IsProper (fenchelIntegrand k h A b c) := by
  obtain ⟨x₀, hx₀⟩ := hk.1
  obtain ⟨w₀, hw₀⟩ := hh.1
  refine ⟨⟨WithLp.toLp 2 (x₀, w₀ - (b - A x₀)), ?_⟩, fun q ↦ ?_⟩
  · rw [fenchelIntegrand_lt_top_iff A b c (fun x ↦ (hk.2 x).ne') (fun w ↦ (hh.2 w).ne')]
    refine ⟨hx₀, ?_⟩
    rwa [show b - A x₀ + (w₀ - (b - A x₀)) = w₀ by abel]
  · exact bot_lt_iff_ne_bot.mpr
      (fenchelIntegrand_ne_bot A b c (fun x ↦ (hk.2 x).ne') (fun w ↦ (hh.2 w).ne') q)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem lowerSemicontinuous_fenchelIntegrand (hkb : ∀ x, k x ≠ ⊥) (hhb : ∀ w, h w ≠ ⊥)
    (hkl : LowerSemicontinuous k) (hhl : LowerSemicontinuous h) :
    LowerSemicontinuous (fenchelIntegrand k h A b c) := by
  have hfst : Continuous (fun q : WithLp 2 (E × P) ↦ q.fst) := (WithLp.fstL 2 ℝ E P).continuous
  have hsnd : Continuous (fun q : WithLp 2 (E × P) ↦ q.snd) := (WithLp.sndL 2 ℝ E P).continuous
  have h₁ : LowerSemicontinuous (fun q : WithLp 2 (E × P) ↦ (⟪c, q.fst⟫_ℝ : EReal) + k q.fst) := by
    have := lowerSemicontinuous_add_coe (g := fun q : WithLp 2 (E × P) ↦ ⟪c, q.fst⟫_ℝ)
      (hkl.comp hfst) ((continuous_const : Continuous fun _ : WithLp 2 (E × P) ↦ c).inner hfst)
    simpa only [Function.comp_apply, add_comm] using this
  have h₂ : LowerSemicontinuous (fun q : WithLp 2 (E × P) ↦ h (b - A q.fst + q.snd)) :=
    hhl.comp ((continuous_const.sub (A.continuous.comp hfst)).add hsnd)
  exact h₁.add' h₂ fun q ↦ EReal.continuousAt_add (.inr (hhb _))
    (.inl (by simp [EReal.add_eq_bot_iff, hkb]))

theorem convex_epigraph_fenchelIntegrand (hkb : ∀ x, k x ≠ ⊥) (hhb : ∀ w, h w ≠ ⊥)
    (hkc : Convex ℝ (epigraph k)) (hhc : Convex ℝ (epigraph h)) :
    Convex ℝ (epigraph (fenchelIntegrand k h A b c)) := by
  have hlin : Convex ℝ (epigraph (fun q : WithLp 2 (E × P) ↦ (⟪c, q.fst⟫_ℝ : EReal))) := by
    rintro ⟨q₁, a₁⟩ h₁ ⟨q₂, a₂⟩ h₂ t s ht hs hts
    change ((⟪c, q₁.fst⟫_ℝ : ℝ) : EReal) ≤ (a₁ : EReal) at h₁
    change ((⟪c, q₂.fst⟫_ℝ : ℝ) : EReal) ≤ (a₂ : EReal) at h₂
    change ((⟪c, (t • q₁ + s • q₂).fst⟫_ℝ : ℝ) : EReal) ≤ ((t * a₁ + s * a₂ : ℝ) : EReal)
    rw [EReal.coe_le_coe_iff] at h₁ h₂ ⊢
    simp only [WithLp.add_fst, WithLp.smul_fst, inner_add_right, inner_smul_right]
    nlinarith
  have hk' : Convex ℝ (epigraph (fun q : WithLp 2 (E × P) ↦ k q.fst)) := by
    have := convex_epigraph_compAffine hkc (WithLp.fstL 2 ℝ E P) 0
    simpa using this
  have hh' : Convex ℝ (epigraph (fun q : WithLp 2 (E × P) ↦ h (b - A q.fst + q.snd))) := by
    have he : (fun q : WithLp 2 (E × P) ↦ h (b - A q.fst + q.snd)) =
        fun q ↦ h (((WithLp.sndL 2 ℝ E P) - A.comp (WithLp.fstL 2 ℝ E P)) q + b) := by
      funext q
      congr 1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
      change b - A q.fst + q.snd = q.snd - A q.fst + b
      abel
    rw [he]
    exact convex_epigraph_compAffine hhc _ b
  exact convex_epigraph_add_of_ne_bot
    (convex_epigraph_add_of_ne_bot hlin hk' (fun _ ↦ EReal.coe_ne_bot _) (fun q ↦ hkb _)) hh'
    (fun q ↦ by simp [EReal.add_eq_bot_iff, hkb]) (fun q ↦ hhb _)

/-- The domain `U = A dom k + dom h - b` in **11.41**. -/
theorem effectiveDomain_parametricValue_fenchelIntegrand (hkb : ∀ x, k x ≠ ⊥)
    (hhb : ∀ w, h w ≠ ⊥) :
    effectiveDomain (parametricValue (fenchelIntegrand k h A b c)) =
      (fun u ↦ u + b) ⁻¹' (A '' effectiveDomain k + effectiveDomain h) := by
  rw [effectiveDomain_parametricValue]
  ext u
  simp only [mem_image, mem_preimage, Set.mem_add]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨⟨x, u'⟩, rfl⟩ := (WithLp.toLp_surjective 2) q
    have hq' := (fenchelIntegrand_lt_top_iff A b c hkb hhb x u').mp hq
    refine ⟨A x, ⟨x, hq'.1, rfl⟩, b - A x + u', hq'.2, ?_⟩
    change A x + (b - A x + u') = u' + b
    abel
  · rintro ⟨_, ⟨x, hx, rfl⟩, w, hw, hsum⟩
    refine ⟨WithLp.toLp 2 (x, u), (fenchelIntegrand_lt_top_iff A b c hkb hhb x u).mpr
      ⟨hx, ?_⟩, rfl⟩
    have hw' : b - A x + u = w := by rw [← sub_eq_zero]; rw [← sub_eq_zero] at hsum; rw [← neg_eq_zero, ← hsum]; abel
    rw [hw']
    exact hw

/-- The domain `V = dom k* - A* dom h* + c` in **11.41**. -/
theorem effectiveDomain_dualParametricValue_fenchelIntegrand (hk : IsProper k)
    (hh : IsProper h) :
    effectiveDomain (dualParametricValue (fenchelIntegrand k h A b c)) =
      (fun v ↦ v - c) ⁻¹' (effectiveDomain (fenchelConjugate k) -
        A.adjoint '' effectiveDomain (fenchelConjugate h)) := by
  have hHb := fenchelConjugate_ne_bot_of_isProper hh
  have hKb := fenchelConjugate_ne_bot_of_isProper hk
  rw [effectiveDomain_dualParametricValue]
  ext v
  simp only [mem_image, mem_preimage, Set.mem_sub]
  have hlt (y : P) : fenchelConjugate (fenchelIntegrand k h A b c) (WithLp.toLp 2 (v, y)) < ⊤ ↔
      fenchelConjugate h y < ⊤ ∧ fenchelConjugate k (A.adjoint y - c + v) < ⊤ := by
    rw [fenchelConjugate_fenchelIntegrand A b c (fun x ↦ (hk.2 x).ne') (fun w ↦ (hh.2 w).ne')]
    simp only [lt_top_iff_ne_top]
    rw [EReal.add_ne_top_iff_ne_top₂ (by simp [hHb]) (hKb _),
      EReal.add_ne_top_iff_ne_top₂ (by simp) (hHb y)]
    simp
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨⟨v', y⟩, rfl⟩ := (WithLp.toLp_surjective 2) q
    have hq' := (hlt y).mp hq
    refine ⟨A.adjoint y - c + v', hq'.2, A.adjoint y, ⟨y, hq'.1, rfl⟩, ?_⟩
    change A.adjoint y - c + v' - A.adjoint y = v' - c
    abel
  · rintro ⟨z, hz, _, ⟨y, hy, rfl⟩, hsum⟩
    refine ⟨WithLp.toLp 2 (v, y), (hlt y).mpr ⟨hy, ?_⟩, rfl⟩
    have hz' : A.adjoint y - c + v = z := by
      have : z = v - c + A.adjoint y := by rw [← hsum]; abel
      rw [this]; abel
    rw [hz']
    exact hz

/-- **11.41**: `0 ∈ int U ⟺ b ∈ int (A dom k + dom h)`. -/
theorem zero_mem_interior_fenchel_U_iff (hkb : ∀ x, k x ≠ ⊥) (hhb : ∀ w, h w ≠ ⊥) :
    (0 : P) ∈ interior (effectiveDomain (parametricValue (fenchelIntegrand k h A b c))) ↔
      b ∈ interior (A '' effectiveDomain k + effectiveDomain h) := by
  rw [effectiveDomain_parametricValue_fenchelIntegrand A b c hkb hhb]
  change (0 : P) ∈ interior (⇑(Homeomorph.addRight b) ⁻¹' _) ↔ _
  rw [← Homeomorph.preimage_interior]
  simp

/-- **11.41**: `0 ∈ int V ⟺ c ∈ int (A* dom h* - dom k*)`. -/
theorem zero_mem_interior_fenchel_V_iff (hk : IsProper k) (hh : IsProper h) :
    (0 : E) ∈ interior (effectiveDomain (dualParametricValue (fenchelIntegrand k h A b c))) ↔
      c ∈ interior (A.adjoint '' effectiveDomain (fenchelConjugate h) -
        effectiveDomain (fenchelConjugate k)) := by
  rw [effectiveDomain_dualParametricValue_fenchelIntegrand A b c hk hh]
  set S := effectiveDomain (fenchelConjugate k) - A.adjoint '' effectiveDomain (fenchelConjugate h)
  have hT : A.adjoint '' effectiveDomain (fenchelConjugate h) - effectiveDomain (fenchelConjugate k) =
      (fun v : E ↦ -v) ⁻¹' S := by
    ext v
    simp only [mem_preimage, S, Set.mem_sub]
    constructor
    · rintro ⟨a, ha, z, hz, rfl⟩
      exact ⟨z, hz, a, ha, by abel⟩
    · rintro ⟨z, hz, a, ha, he⟩
      refine ⟨a, ha, z, hz, ?_⟩
      rw [← neg_neg v, ← he]
      abel
  rw [hT]
  change (0 : E) ∈ interior (⇑(Homeomorph.subRight c) ⁻¹' S) ↔
    c ∈ interior (⇑(Homeomorph.neg E) ⁻¹' S)
  rw [← Homeomorph.preimage_interior, ← Homeomorph.preimage_interior]
  simp only [mem_preimage]
  change (0 : E) - c ∈ interior S ↔ -c ∈ interior S
  rw [zero_sub]

/-- The value equation behind the optimality conditions of **11.41**: equality
of the primal and dual objectives is equality in both Fenchel inequalities. -/
theorem fenchelPrimal_eq_fenchelDual_iff (hk : IsProper k) (hh : IsProper h) (x₀ : E) (y₀ : P) :
    fenchelPrimal k h A b c x₀ = fenchelDual k h A b c y₀ ↔
      (h (b - A x₀) + fenchelConjugate h y₀ = (⟪y₀, b - A x₀⟫_ℝ : EReal) ∧
        k x₀ + fenchelConjugate k (A.adjoint y₀ - c) = (⟪A.adjoint y₀ - c, x₀⟫_ℝ : EReal)) := by
  have hid : ⟪y₀, b - A x₀⟫_ℝ + ⟪A.adjoint y₀ - c, x₀⟫_ℝ = ⟪b, y₀⟫_ℝ - ⟪c, x₀⟫_ℝ := by
    rw [inner_sub_right, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
      real_inner_comm b y₀]
    ring
  have hHb := fenchelConjugate_ne_bot_of_isProper hh y₀
  have hKb := fenchelConjugate_ne_bot_of_isProper hk (A.adjoint y₀ - c)
  have hYh := fenchel_young hh (b - A x₀) y₀
  have hYk := fenchel_young hk x₀ (A.adjoint y₀ - c)
  constructor
  · intro he
    have hψt : fenchelDual k h A b c y₀ ≠ ⊤ := ereal_coe_sub_sub_ne_top hHb hKb
    have hφb : fenchelPrimal k h A b c x₀ ≠ ⊥ := by
      simp only [fenchelPrimal, ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot,
        (hk.2 x₀).ne', (hh.2 _).ne', or_self, not_false_eq_true]
    have hφt : fenchelPrimal k h A b c x₀ ≠ ⊤ := he ▸ hψt
    have hψb : fenchelDual k h A b c y₀ ≠ ⊥ := he ▸ hφb
    simp only [fenchelPrimal] at hφt
    rw [EReal.add_ne_top_iff_ne_top₂ (by simp [(hk.2 x₀).ne']) (hh.2 _).ne',
      EReal.add_ne_top_iff_ne_top₂ (EReal.coe_ne_bot _) (hk.2 x₀).ne'] at hφt
    replace hψb := ne_top_of_ereal_coe_sub_sub_ne_bot hψb
    obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, k x₀ = κ := ⟨_, (EReal.coe_toReal hφt.1.2 (hk.2 x₀).ne').symm⟩
    obtain ⟨η, hη⟩ : ∃ η : ℝ, h (b - A x₀) = η :=
      ⟨_, (EReal.coe_toReal hφt.2 (hh.2 _).ne').symm⟩
    obtain ⟨η', hη'⟩ : ∃ η' : ℝ, fenchelConjugate h y₀ = η' :=
      ⟨_, (EReal.coe_toReal hψb.1 hHb).symm⟩
    obtain ⟨κ', hκ'⟩ : ∃ κ' : ℝ, fenchelConjugate k (A.adjoint y₀ - c) = κ' :=
      ⟨_, (EReal.coe_toReal hψb.2 hKb).symm⟩
    simp only [fenchelPrimal, fenchelDual, hκ, hη, hη', hκ'] at he
    rw [hη, hη'] at hYh
    rw [hκ, hκ'] at hYk
    rw [hη, hη', hκ, hκ']
    norm_cast at he hYh hYk ⊢
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    obtain ⟨η, η', hη, hη'⟩ := exists_coe_components_of_add_eq_coe h₁
    obtain ⟨κ, κ', hκ, hκ'⟩ := exists_coe_components_of_add_eq_coe h₂
    rw [hη, hη'] at h₁
    rw [hκ, hκ'] at h₂
    simp only [fenchelPrimal, fenchelDual, hκ, hη, hη', hκ']
    norm_cast at h₁ h₂ ⊢
    linarith

/-- **Example 11.41**, optimality: joint optimality with equal values holds iff
`ȳ ∈ ∂h(b - Ax̄)` and `A*ȳ - c ∈ ∂k(x̄)`, iff `x̄ ∈ ∂k*(A*ȳ - c)` and
`b - Ax̄ ∈ ∂h*(ȳ)`. -/
theorem fenchel_optimality (hk : IsProper k) (hkl : LowerSemicontinuous k)
    (hkc : Convex ℝ (epigraph k)) (hh : IsProper h) (hhl : LowerSemicontinuous h)
    (hhc : Convex ℝ (epigraph h)) (x₀ : E) (y₀ : P) :
    ((x₀ ∈ argmin (fenchelPrimal k h A b c) ∧ y₀ ∈ argmax (fenchelDual k h A b c) ∧
        (⨅ x, fenchelPrimal k h A b c x) = ⨆ y, fenchelDual k h A b c y) ↔
      (y₀ ∈ subdifferential h (b - A x₀) ∧ A.adjoint y₀ - c ∈ subdifferential k x₀)) ∧
    ((y₀ ∈ subdifferential h (b - A x₀) ∧ A.adjoint y₀ - c ∈ subdifferential k x₀) ↔
      (x₀ ∈ subdifferential (fenchelConjugate k) (A.adjoint y₀ - c) ∧
        b - A x₀ ∈ subdifferential (fenchelConjugate h) y₀)) := by
  refine ⟨?_, ?_⟩
  · rw [← primalObjective_fenchelIntegrand, ← dualObjective_fenchelIntegrand A b c hk hh,
      primal_dual_optimality_iff_values_equal_of_isProper (isProper_fenchelIntegrand A b c hk hh),
      primalObjective_fenchelIntegrand, dualObjective_fenchelIntegrand A b c hk hh,
      mem_subdifferential_iff_fenchel_equality hh hhc, mem_subdifferential_iff_fenchel_equality hk hkc]
    exact fenchelPrimal_eq_fenchelDual_iff A b c hk hh x₀ y₀
  · rw [mem_subdifferential_fenchelConjugate_iff hk hkl hkc,
      mem_subdifferential_fenchelConjugate_iff hh hhl hhc]
    exact and_comm

/-- **Example 11.41** in the format of **11.39**: the integrand is proper, lsc and
convex, its primal and dual problems are the Fenchel pair, and the interior
criteria for `U` and `V` take the stated form. -/
theorem fenchel_scheme_fits_duality (hk : IsProper k) (hkl : LowerSemicontinuous k)
    (hkc : Convex ℝ (epigraph k)) (hh : IsProper h) (hhl : LowerSemicontinuous h)
    (hhc : Convex ℝ (epigraph h)) :
    IsProper (fenchelIntegrand k h A b c) ∧ LowerSemicontinuous (fenchelIntegrand k h A b c) ∧
      Convex ℝ (epigraph (fenchelIntegrand k h A b c)) ∧
      primalObjective (fenchelIntegrand k h A b c) = fenchelPrimal k h A b c ∧
      dualObjective (fenchelIntegrand k h A b c) = fenchelDual k h A b c ∧
      ((0 : P) ∈ interior (effectiveDomain (parametricValue (fenchelIntegrand k h A b c))) ↔
        b ∈ interior (A '' effectiveDomain k + effectiveDomain h)) ∧
      ((0 : E) ∈ interior (effectiveDomain (dualParametricValue (fenchelIntegrand k h A b c))) ↔
        c ∈ interior (A.adjoint '' effectiveDomain (fenchelConjugate h) -
          effectiveDomain (fenchelConjugate k))) := by
  have hkb : ∀ x, k x ≠ ⊥ := fun x ↦ (hk.2 x).ne'
  have hhb : ∀ w, h w ≠ ⊥ := fun w ↦ (hh.2 w).ne'
  exact ⟨isProper_fenchelIntegrand A b c hk hh,
    lowerSemicontinuous_fenchelIntegrand A b c hkb hhb hkl hhl,
    convex_epigraph_fenchelIntegrand A b c hkb hhb hkc hhc, primalObjective_fenchelIntegrand A b c,
    dualObjective_fenchelIntegrand A b c hk hh, zero_mem_interior_fenchel_U_iff A b c hkb hhb,
    zero_mem_interior_fenchel_V_iff A b c hk hh⟩

/-- **11.41** with **11.39(a)**: either interior criterion gives `inf φ = sup ψ`. -/
theorem fenchel_strong_duality (hk : IsProper k) (hkl : LowerSemicontinuous k)
    (hkc : Convex ℝ (epigraph k)) (hh : IsProper h) (hhl : LowerSemicontinuous h)
    (hhc : Convex ℝ (epigraph h))
    (hint : b ∈ interior (A '' effectiveDomain k + effectiveDomain h) ∨
      c ∈ interior (A.adjoint '' effectiveDomain (fenchelConjugate h) -
        effectiveDomain (fenchelConjugate k))) :
    (⨅ x, fenchelPrimal k h A b c x) = ⨆ y, fenchelDual k h A b c y := by
  obtain ⟨hfp, hfl, hfc, hφ, hψ, hU, hV⟩ := fenchel_scheme_fits_duality A b c hk hkl hkc hh hhl hhc
  rw [← hφ, ← hψ]
  rcases hint with hb | hc'
  · exact primal_dual_strong_duality_of_primal_interior hfp hfl hfc (hU.mpr hb)
  · exact primal_dual_strong_duality_of_dual_interior hfp hfl hfc (hV.mpr hc')

/-- **11.41** with **11.40(a)**: under both interior criteria the common optimal
value is finite and attained in both problems. -/
theorem fenchel_best_case (hk : IsProper k) (hkl : LowerSemicontinuous k)
    (hkc : Convex ℝ (epigraph k)) (hh : IsProper h) (hhl : LowerSemicontinuous h)
    (hhc : Convex ℝ (epigraph h)) (hb : b ∈ interior (A '' effectiveDomain k + effectiveDomain h))
    (hc' : c ∈ interior (A.adjoint '' effectiveDomain (fenchelConjugate h) -
        effectiveDomain (fenchelConjugate k))) :
    ∃ (a : ℝ) (x₀ : E) (y₀ : P), x₀ ∈ argmin (fenchelPrimal k h A b c) ∧
      y₀ ∈ argmax (fenchelDual k h A b c) ∧ (⨅ x, fenchelPrimal k h A b c x) = (a : EReal) ∧
      (⨆ y, fenchelDual k h A b c y) = (a : EReal) := by
  obtain ⟨hfp, hfl, hfc, hφ, hψ, hU, hV⟩ := fenchel_scheme_fits_duality A b c hk hkl hkc hh hhl hhc
  rw [← hφ, ← hψ]
  exact primal_dual_best_case_attainment hfp hfl hfc (hU.mpr hb) (hV.mpr hc')

end
end RW
