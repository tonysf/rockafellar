/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2H: Closures of convex functions through relative interiors

This file formalizes Exercise 2.46 of Rockafellar–Wets in finite-dimensional
real normed spaces, with `cl f = epiClosure f` and `rint = intrinsicInterior ℝ`.

The relative versions of 2.34 and of the closure formula 2(11) come first:
`(x, α) ∈ rint(epi f)` iff `x ∈ rint(dom f)` and `f(x) < α` (from 2.43), and
`(cl f)(x) = lim_{τ ↗ 1} f((1 - τ)x₀ + τx)` for `x₀ ∈ rint(dom f)`.

* (a) `cl f₁ = cl f₂` when `f₁`, `f₂` agree on `rint(dom f₁) = rint(dom f₂)`.
* (b) `cl(f₁ + f₂) = cl f₁ + cl f₂` (sums by inf-addition) when
  `rint(dom f₁) ∩ rint(dom f₂) ≠ ∅`, for proper `f₁`, `f₂`.  Properness is
  needed: `closure_sum_counterexample` gives improper `f₁ ≡ -∞` on `[0,1]` and
  `f₂ = 1/x` on `(0,1]` with `cl(f₁ + f₂)(0) = -∞` but `cl f₁(0) + cl f₂(0) = ∞`.
* (c) for `f = g ∘ L`, `rint(dom f) = L⁻¹(rint(dom g))` and `cl f = (cl g) ∘ L`.
-/

import RockafellarWets.Chapter2.RelativeInteriorCalculus
import RockafellarWets.Chapter2.ClosuresContinuity
import RockafellarWets.Chapter2.ConvexOperations
import Mathlib.Analysis.Convex.Mul

open Set Filter Topology Metric

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Relative interiors of epigraphs and the relative closure formula -/

theorem intrinsicInterior_Ici (c : ℝ) : intrinsicInterior ℝ (Ici c) = Ioi c := by
  have htop : affineSpan ℝ (Ici c) = ⊤ := by
    rw [← (convex_Ici c).interior_nonempty_iff_affineSpan_eq_top, interior_Ici]
    exact ⟨c + 1, by simp⟩
  rw [intrinsicInterior_eq_interior_of_affineSpan_eq_top htop, interior_Ici]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem productFiber_epigraph (f : E → EReal) (x : E) :
    productFiber (epigraph f) x = {α : ℝ | f x ≤ (α : EReal)} := by
  ext α
  simp [productFiber, mem_epigraph_iff]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem intrinsicInterior_productFiber_epigraph {f : E → EReal} {x : E} (hx : f x < ⊤) :
    intrinsicInterior ℝ (productFiber (epigraph f) x) = {α : ℝ | f x < (α : EReal)} := by
  rw [productFiber_epigraph]
  induction hfx : f x using EReal.rec with
  | bot =>
    have h1 : {α : ℝ | (⊥ : EReal) ≤ (α : EReal)} = univ := by ext; simp
    have h2 : {α : ℝ | (⊥ : EReal) < (α : EReal)} = univ := by ext; simp [EReal.bot_lt_coe]
    rw [h1, h2, intrinsicInterior_eq_interior_of_affineSpan_eq_top (by simp), interior_univ]
  | coe c =>
    have h1 : {α : ℝ | (c : EReal) ≤ (α : EReal)} = Ici c := by ext; simp
    have h2 : {α : ℝ | (c : EReal) < (α : EReal)} = Ioi c := by ext; simp
    rw [h1, h2, intrinsicInterior_Ici]
  | top => rw [hfx] at hx; exact absurd hx (lt_irrefl _)

/-- Relative form of **Proposition 2.34**: `(x, α) ∈ rint(epi f)` if and only if
`x ∈ rint(dom f)` and `f(x) < α`. -/
theorem mem_intrinsicInterior_epigraph_iff {f : E → EReal} (hf : IsConvexRelative univ f)
    {x : E} {α : ℝ} :
    (x, α) ∈ intrinsicInterior ℝ (epigraph f) ↔
      x ∈ intrinsicInterior ℝ (effectiveDomain f) ∧ f x < (α : EReal) := by
  have hc := (isConvexRelative_univ_iff f).mp hf
  rw [mem_intrinsicInterior_prod_iff hc, epigraph_proj_eq_effectiveDomain]
  constructor
  · rintro ⟨hx, hα⟩
    have hxd : x ∈ effectiveDomain f := intrinsicInterior_subset hx
    rw [intrinsicInterior_productFiber_epigraph hxd] at hα
    exact ⟨hx, hα⟩
  · rintro ⟨hx, hα⟩
    have hxd : x ∈ effectiveDomain f := intrinsicInterior_subset hx
    refine ⟨hx, ?_⟩
    rw [intrinsicInterior_productFiber_epigraph hxd]
    exact hα

/-- Relative form of the closure formula 2(11): for `x₀ ∈ rint(dom f)`,
`(cl f)(x) = lim_{τ ↗ 1} f((1 - τ)x₀ + τx)` for every `x`. -/
theorem tendsto_epiClosure_of_mem_intrinsicInterior {f : E → EReal}
    (hf : IsConvexRelative univ f) {x₀ : E} (hx₀ : x₀ ∈ intrinsicInterior ℝ (effectiveDomain f))
    (x : E) :
    Tendsto (fun τ : ℝ ↦ f ((1 - τ) • x₀ + τ • x)) (𝓝[<] 1) (𝓝 (epiClosure f x)) := by
  have hc := (isConvexRelative_univ_iff f).mp hf
  have hcont : Continuous (fun τ : ℝ ↦ (1 - τ) • x₀ + τ • x) := by fun_prop
  have htend : Tendsto (fun τ : ℝ ↦ (1 - τ) • x₀ + τ • x) (𝓝[<] 1) (𝓝 x) := by
    have := hcont.tendsto 1
    simp only [sub_self, zero_smul, one_smul, zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_order]
  constructor
  · intro a ha
    have hlsc := lowerSemicontinuous_epiLowerLimit (fun _ : ℕ ↦ f)
    have hev : ∀ᶠ y in 𝓝 x, a < epiClosure f y := hlsc x a ha
    exact (htend.eventually hev).mono fun τ hτ ↦ hτ.trans_le (epiClosure_le_self f _)
  · intro b hb
    obtain ⟨α, hα, hαb⟩ := EReal.lt_iff_exists_real_btwn.mp hb
    have hxα : (x, α) ∈ closure (epigraph f) := by
      rw [← epigraph_epiClosure]
      exact (mem_epigraph_iff _ x α).mpr hα.le
    have hx₀d : x₀ ∈ effectiveDomain f := intrinsicInterior_subset hx₀
    obtain ⟨α₀, hα₀, -⟩ := EReal.lt_iff_exists_real_btwn.mp hx₀d
    have hint : (x₀, α₀) ∈ intrinsicInterior ℝ (epigraph f) :=
      (mem_intrinsicInterior_epigraph_iff hf).mpr ⟨hx₀, hα₀⟩
    have hseg : ∀ τ : ℝ, 0 ≤ τ → τ < 1 →
        f ((1 - τ) • x₀ + τ • x) ≤ (((1 - τ) * α₀ + τ * α : ℝ) : EReal) := by
      intro τ hτ0 hτ1
      have hm := Convex.add_smul_sub_mem_intrinsicInterior_normed hc hxα hint
        (t := 1 - τ) (by linarith) (by linarith)
      have hmem := intrinsicInterior_subset hm
      have he : (x, α) + (1 - τ) • ((x₀, α₀) - (x, α)) =
          ((1 - τ) • x₀ + τ • x, (1 - τ) * α₀ + τ * α) := by
        simp only [Prod.smul_mk, Prod.mk_sub_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
        constructor
        · module
        · ring
      rw [he] at hmem
      exact (mem_epigraph_iff _ _ _).mp hmem
    have hlim : Tendsto (fun τ : ℝ ↦ (1 - τ) * α₀ + τ * α) (𝓝[<] 1) (𝓝 α) := by
      have : Continuous (fun τ : ℝ ↦ (1 - τ) * α₀ + τ * α) := by fun_prop
      have h := this.tendsto 1
      simp only [sub_self, zero_mul, one_mul, zero_add] at h
      exact h.mono_left nhdsWithin_le_nhds
    by_cases hbt : b = ⊤
    · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with τ hτ
      rw [hbt]
      exact (hseg τ hτ.1.le hτ.2).trans_lt (EReal.coe_lt_top _)
    · have hbb : b ≠ ⊥ := (hb.trans_le' bot_le).ne'
      have hbr : α < b.toReal := by
        have := EReal.coe_toReal hbt hbb
        rw [← this] at hαb
        exact_mod_cast hαb
      filter_upwards [hlim.eventually (gt_mem_nhds hbr), Ioo_mem_nhdsLT zero_lt_one] with τ hτb hτ
      refine (hseg τ hτ.1.le hτ.2).trans_lt ?_
      rw [← EReal.coe_toReal hbt hbb]
      exact_mod_cast hτb

/-! ## Exercise 2.46 -/

/-- **Exercise 2.46(a)**: convex functions agreeing on a common
`rint(dom f₁) = rint(dom f₂)` have the same closure. -/
theorem epiClosure_eq_of_eqOn_intrinsicInterior {f₁ f₂ : E → EReal}
    (h₁ : IsConvexRelative univ f₁) (h₂ : IsConvexRelative univ f₂)
    (hrint : intrinsicInterior ℝ (effectiveDomain f₁) = intrinsicInterior ℝ (effectiveDomain f₂))
    (hagree : ∀ x ∈ intrinsicInterior ℝ (effectiveDomain f₁), f₁ x = f₂ x) :
    epiClosure f₁ = epiClosure f₂ := by
  have hd₁ := h₁.convex_effectiveDomain
  have hd₂ := h₂.convex_effectiveDomain
  rcases (intrinsicInterior ℝ (effectiveDomain f₁)).eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
  · have he₁ : effectiveDomain f₁ = ∅ := by
      by_contra hne
      exact (Set.Nonempty.intrinsicInterior hd₁ (nonempty_iff_ne_empty.mpr hne)).ne_empty hempty
    have he₂ : effectiveDomain f₂ = ∅ := by
      by_contra hne
      rw [hrint] at hempty
      exact (Set.Nonempty.intrinsicInterior hd₂ (nonempty_iff_ne_empty.mpr hne)).ne_empty hempty
    have htop : ∀ g : E → EReal, effectiveDomain g = ∅ → epiClosure g = fun _ ↦ ⊤ := by
      intro g hg
      funext x
      by_contra hne
      have := effectiveDomain_epiClosure_subset_closure g (lt_top_iff_ne_top.mpr hne)
      rw [hg, closure_empty] at this
      exact this
    rw [htop f₁ he₁, htop f₂ he₂]
  funext x
  have hx₀' : x₀ ∈ intrinsicInterior ℝ (effectiveDomain f₂) := hrint ▸ hx₀
  have hl₁ := tendsto_epiClosure_of_mem_intrinsicInterior h₁ hx₀ x
  have hl₂ := tendsto_epiClosure_of_mem_intrinsicInterior h₂ hx₀' x
  by_cases hxc : x ∈ closure (effectiveDomain f₁)
  · have heq : ∀ᶠ τ in 𝓝[<] (1 : ℝ), f₁ ((1 - τ) • x₀ + τ • x) = f₂ ((1 - τ) • x₀ + τ • x) := by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with τ hτ
      apply hagree
      have h := Convex.add_smul_sub_mem_intrinsicInterior_normed hd₁ hxc hx₀ (t := 1 - τ)
        (by linarith [hτ.2]) (by linarith [hτ.1])
      convert h using 1
      module
    exact tendsto_nhds_unique hl₁ (hl₂.congr' (heq.mono fun τ hτ ↦ hτ.symm))
  · have hcl₂ : closure (effectiveDomain f₂) = closure (effectiveDomain f₁) := by
      rw [← (intrinsicInterior_properties hd₁ ⟨x₀, intrinsicInterior_subset hx₀⟩).2.2.1,
        ← (intrinsicInterior_properties hd₂ ⟨x₀, intrinsicInterior_subset hx₀'⟩).2.2.1, hrint]
    have ht : ∀ g : E → EReal, x ∉ closure (effectiveDomain g) → epiClosure g x = ⊤ := by
      intro g hg
      by_contra hne
      exact hg (effectiveDomain_epiClosure_subset_closure g (lt_top_iff_ne_top.mpr hne))
    rw [ht f₁ hxc, ht f₂ (hcl₂ ▸ hxc)]

theorem infAddition_lt_top_iff {a b : EReal} : infAddition a b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by
  unfold infAddition
  split_ifs with h
  · simp only [lt_self_iff_false, false_iff, not_and]
    rcases h with h | h <;> simp [h]
  · push_neg at h
    exact ⟨fun _ ↦ ⟨lt_top_iff_ne_top.mpr h.1, lt_top_iff_ne_top.mpr h.2⟩,
      fun hab ↦ EReal.add_lt_top hab.1.ne hab.2.ne⟩

/-- **Exercise 2.46(b)**, for proper functions: if
`rint(dom f₁) ∩ rint(dom f₂) ≠ ∅`, then `cl(f₁ + f₂) = cl f₁ + cl f₂`, with sums
formed by inf-addition. -/
theorem epiClosure_infAddition_eq {f₁ f₂ : E → EReal} (h₁ : IsConvexRelative univ f₁)
    (h₂ : IsConvexRelative univ f₂) (hp₁ : IsProper f₁) (hp₂ : IsProper f₂)
    (hmeet : (intrinsicInterior ℝ (effectiveDomain f₁) ∩
      intrinsicInterior ℝ (effectiveDomain f₂)).Nonempty) :
    epiClosure (fun x ↦ infAddition (f₁ x) (f₂ x)) =
      fun x ↦ infAddition (epiClosure f₁ x) (epiClosure f₂ x) := by
  set g : E → EReal := fun x ↦ infAddition (f₁ x) (f₂ x) with hgdef
  have hg : IsConvexRelative univ g := by
    have h := isConvexRelative_finiteInfAddition (g := ![f₁, f₂])
      (fun i ↦ by fin_cases i <;> assumption)
    refine h.congr convex_univ fun x _ ↦ ?_
    change _ = infAddition (f₁ x) (f₂ x)
    rw [← finiteInfAddition_fin_two]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hdom : effectiveDomain g = effectiveDomain f₁ ∩ effectiveDomain f₂ := by
    ext x
    exact infAddition_lt_top_iff
  obtain ⟨x₀, hx₀₁, hx₀₂⟩ := hmeet
  have hx₀ : x₀ ∈ intrinsicInterior ℝ (effectiveDomain g) := by
    rw [hdom]
    have hC : ∀ i : Fin 2, Convex ℝ (![effectiveDomain f₁, effectiveDomain f₂] i) := by
      intro i; fin_cases i
      · exact h₁.convex_effectiveDomain
      · exact h₂.convex_effectiveDomain
    have hne : (⋂ i, intrinsicInterior ℝ (![effectiveDomain f₁, effectiveDomain f₂] i)).Nonempty :=
      ⟨x₀, mem_iInter.mpr fun i ↦ by fin_cases i <;> assumption⟩
    have h := intrinsicInterior_iInter_eq hC hne
    have hinter : (⋂ i, ![effectiveDomain f₁, effectiveDomain f₂] i) =
        effectiveDomain f₁ ∩ effectiveDomain f₂ := by
      ext x; simp [Fin.forall_fin_two]
    rw [hinter] at h
    rw [h]
    exact mem_iInter.mpr fun i ↦ by fin_cases i <;> assumption
  have hcp : ∀ f : E → EReal, IsConvexRelative univ f → IsProper f → ∀ x, epiClosure f x ≠ ⊥ :=
    fun f hf hp x ↦ (isProper_of_isLowerClosure hp ((isConvexRelative_univ_iff f).mp hf)
      (epigraph_epiClosure f)).2 x |>.ne'
  funext x
  have hlg := tendsto_epiClosure_of_mem_intrinsicInterior hg hx₀ x
  have hl₁ := tendsto_epiClosure_of_mem_intrinsicInterior h₁ hx₀₁ x
  have hl₂ := tendsto_epiClosure_of_mem_intrinsicInterior h₂ hx₀₂ x
  have hsum := ((EReal.continuousAt_add (p := (epiClosure f₁ x, epiClosure f₂ x))
    (Or.inr (hcp f₂ h₂ hp₂ x)) (Or.inl (hcp f₁ h₁ hp₁ x))).tendsto).comp (hl₁.prodMk_nhds hl₂)
  have heq : ∀ τ : ℝ, g ((1 - τ) • x₀ + τ • x) =
      f₁ ((1 - τ) • x₀ + τ • x) + f₂ ((1 - τ) • x₀ + τ • x) := fun τ ↦
    infAddition_eq_add_of_ne_bot (hp₁.2 _).ne' (hp₂.2 _).ne'
  have hlg' : Tendsto (fun τ : ℝ ↦ f₁ ((1 - τ) • x₀ + τ • x) + f₂ ((1 - τ) • x₀ + τ • x))
      (𝓝[<] 1) (𝓝 (epiClosure g x)) := hlg.congr heq
  rw [tendsto_nhds_unique hlg' hsum,
    infAddition_eq_add_of_ne_bot (hcp f₁ h₁ hp₁ x) (hcp f₂ h₂ hp₂ x)]

/-- **Exercise 2.46(c)**: for convex `g` and linear `L` with `rint(dom g)` meeting
the range of `L`, `rint(dom(g ∘ L)) = L⁻¹(rint(dom g))` and
`cl(g ∘ L) = (cl g) ∘ L`. -/
theorem epiClosure_comp_linear {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {g : F → EReal} (hg : IsConvexRelative univ g) (L : E →ₗ[ℝ] F)
    (hmeet : (intrinsicInterior ℝ (effectiveDomain g) ∩ range L).Nonempty) :
    intrinsicInterior ℝ (effectiveDomain (g ∘ L)) = L ⁻¹' intrinsicInterior ℝ (effectiveDomain g) ∧
      epiClosure (g ∘ L) = epiClosure g ∘ L := by
  have hdom : effectiveDomain (g ∘ L) = L ⁻¹' effectiveDomain g := rfl
  refine ⟨by rw [hdom]; exact (intrinsicInterior_linear_preimage L hg.convex_effectiveDomain
    hmeet).1, ?_⟩
  set L₀ : E × ℝ →ₗ[ℝ] F × ℝ := L.prodMap LinearMap.id with hL₀
  have hepi : epigraph (g ∘ L) = L₀ ⁻¹' epigraph g := by
    ext ⟨x, α⟩
    simp [hL₀, mem_epigraph_iff]
  obtain ⟨_, hy, xb, rfl⟩ := hmeet
  have hyd : L xb ∈ effectiveDomain g := intrinsicInterior_subset hy
  obtain ⟨α, hα, -⟩ := EReal.lt_iff_exists_real_btwn.mp hyd
  have hmeet₀ : (intrinsicInterior ℝ (epigraph g) ∩ range L₀).Nonempty :=
    ⟨(L xb, α), (mem_intrinsicInterior_epigraph_iff hg).mpr ⟨hy, hα⟩, (xb, α), by simp [hL₀]⟩
  have hcl := (intrinsicInterior_linear_preimage L₀ ((isConvexRelative_univ_iff g).mp hg)
    hmeet₀).2
  apply eq_of_epigraph_eq
  rw [epigraph_epiClosure, hepi, hcl, ← epigraph_epiClosure]
  ext ⟨x, β⟩
  simp [hL₀, mem_epigraph_iff]

/-! ## The properness hypothesis in Exercise 2.46(b) -/

open Classical in
/-- The improper convex function `-∞` on `[0,1]`, `∞` elsewhere. -/
def closureSumLeft (x : ℝ) : EReal := if x ∈ Icc (0 : ℝ) 1 then ⊥ else ⊤

open Classical in
/-- The proper convex function `1/x` on `(0,1]`, `∞` elsewhere. -/
def closureSumRight (x : ℝ) : EReal := if x ∈ Ioc (0 : ℝ) 1 then ((x⁻¹ : ℝ) : EReal) else ⊤

/-- Exercise 2.46(b) needs properness: for `f₁ = closureSumLeft` (improper) and
`f₂ = closureSumRight`, both convex with `1/2 ∈ rint(dom f₁) ∩ rint(dom f₂)`,
`cl(f₁ + f₂)(0) = -∞` while `cl f₁(0) + cl f₂(0) = -∞ + ∞ = ∞` under inf-addition. -/
theorem closure_sum_counterexample :
    IsConvexRelative univ closureSumLeft ∧ IsConvexRelative univ closureSumRight ∧
      (1 / 2 : ℝ) ∈ intrinsicInterior ℝ (effectiveDomain closureSumLeft) ∩
        intrinsicInterior ℝ (effectiveDomain closureSumRight) ∧
      epiClosure (fun x ↦ infAddition (closureSumLeft x) (closureSumRight x)) 0 = ⊥ ∧
      infAddition (epiClosure closureSumLeft 0) (epiClosure closureSumRight 0) = ⊤ := by
  classical
  have hdom₁ : effectiveDomain closureSumLeft = Icc 0 1 := by
    ext x
    simp only [effectiveDomain, mem_setOf_eq, closureSumLeft]
    split_ifs with hx <;> simp [hx]
  have hdom₂ : effectiveDomain closureSumRight = Ioc 0 1 := by
    ext x
    simp only [effectiveDomain, mem_setOf_eq, closureSumRight]
    split_ifs with hx <;> simp [hx]
  have hc₁ : IsConvexRelative univ closureSumLeft := by
    have h0 : IsConvexRelative (Icc (0 : ℝ) 1) (fun _ ↦ (⊥ : EReal)) :=
      fun _ _ _ _ _ _ _ ↦ bot_le
    refine ((isConvexRelative_iff_extension (convex_Icc 0 1) _).mp h0).congr convex_univ
      fun x _ ↦ ?_
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [closureSumLeft, hx]
  have hc₂ : IsConvexRelative univ closureSumRight := by
    have hinv : ConvexOn ℝ (Ioc (0 : ℝ) 1) (fun x : ℝ ↦ x⁻¹) := by
      have := (convexOn_zpow (𝕜 := ℝ) (-1)).subset Ioc_subset_Ioi_self (convex_Ioc 0 1)
      simpa using this
    refine ((isConvexRelative_iff_extension (convex_Ioc 0 1) _).mp
      ((isConvexRelative_coe_iff (convex_Ioc 0 1) _).mpr hinv)).congr convex_univ fun x _ ↦ ?_
    by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;> simp [closureSumRight, hx]
  refine ⟨hc₁, hc₂, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hdom₁]
    exact interior_subset_intrinsicInterior (by rw [interior_Icc]; norm_num)
  · rw [hdom₂]
    exact interior_subset_intrinsicInterior (by rw [interior_Ioc]; norm_num)
  · refine (EReal.eq_bot_iff_forall_lt _).mpr fun a ↦ ?_
    refine lt_of_le_of_lt ?_ (EReal.coe_lt_coe_iff.mpr (sub_one_lt a))
    rw [← mem_epigraph_iff, epigraph_epiClosure, Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(min (ε / 2) 1, a - 1), ?_, ?_⟩
    · have hx : min (ε / 2) 1 ∈ Ioc (0 : ℝ) 1 :=
        ⟨lt_min (by linarith) one_pos, min_le_right _ _⟩
      have hx' : min (ε / 2) 1 ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hx
      rw [mem_epigraph_iff]
      simp [closureSumLeft, closureSumRight, hx, hx', infAddition]
    · rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq, zero_sub, abs_neg,
        abs_of_pos (lt_min (by linarith) one_pos)]
      exact (min_le_left _ _).trans_lt (by linarith)
  · have h₁ : epiClosure closureSumLeft 0 = ⊥ :=
      le_bot_iff.mp ((epiClosure_le_self _ 0).trans (by simp [closureSumLeft]))
    have h₂ : epiClosure closureSumRight 0 = ⊤ := by
      refine (EReal.eq_top_iff_forall_lt _).mpr fun a ↦ ?_
      by_contra hle
      push_neg at hle
      rw [← mem_epigraph_iff, epigraph_epiClosure, Metric.mem_closure_iff] at hle
      obtain ⟨⟨x, β⟩, hxβ, hdist⟩ := hle (1 / (|a| + 2)) (by positivity)
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, zero_sub, abs_neg] at hdist
      have hx1 := (le_max_left _ _).trans_lt hdist
      have hβ1 := (le_max_right _ _).trans_lt hdist
      rw [mem_epigraph_iff] at hxβ
      by_cases hx : x ∈ Ioc (0 : ℝ) 1
      · simp only [closureSumRight, hx, if_true, EReal.coe_le_coe_iff] at hxβ
        have hxpos : 0 < x := hx.1
        rw [abs_of_pos hxpos] at hx1
        have hr : 1 / (|a| + 2) ≤ 1 / 2 := by
          apply div_le_div_of_nonneg_left zero_le_one (by norm_num); linarith [abs_nonneg a]
        have hinv : |a| + 2 < x⁻¹ := by
          rw [lt_inv_comm₀ (by positivity) hxpos]
          simpa using hx1
        have hβ1' : |a - β| < 1 / (|a| + 2) := hβ1
        have hβ : β < a + 1 := by
          have := (abs_lt.mp hβ1').1
          linarith
        linarith [le_abs_self a]
      · simp [closureSumRight, hx] at hxβ
    rw [h₁, h₂]
    simp [infAddition]

end RW
