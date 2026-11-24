/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 2F: Closures and continuity of convex functions

This file formalizes Section F of Chapter 2 of Rockafellar–Wets on a
finite-dimensional Euclidean space, with `cl f = epiClosure f` (Chapter 7).

* Proposition 2.32: closures of convex sets and functions; `cl f` is proper
  exactly when `f` is (Chapter 3 `isProper_of_isLowerClosure`).
* Theorem 2.33: the line segment principle.
* Proposition 2.34: interiors of epigraphs (Chapter 8) and of level sets.
* Theorem 2.35: continuity on `int(dom f)`, agreement with `cl f` there
  (Chapters 8 and 11), and the closure formula 2(11).
* Corollary 2.36: finite convex functions on open convex sets and their unique
  proper lsc convex extensions.
* Corollary 2.37: lsc convex functions of one real variable are continuous
  relative to `cl(dom f)`.
-/

import RockafellarWets.Chapter2.ConvexFunctions
import RockafellarWets.Chapter7.EpiLimitProperties
import RockafellarWets.Chapter7.ConvexEpiConvergence
import RockafellarWets.Chapter8.ConvexSubderivativeInteriors
import RockafellarWets.Chapter11.ConvexMarginalGeometry
import RockafellarWets.Chapter3.LowerClosureProperness

open Set Filter Topology

noncomputable section

namespace RW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Proposition 2.32 -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem epiClosure_le_self (f : E → EReal) : epiClosure f ≤ f :=
  epigraph_subset_epigraph_iff.mp (epigraph_epiClosure f ▸ subset_closure)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem effectiveDomain_epiClosure_subset_closure (f : E → EReal) :
    effectiveDomain (epiClosure f) ⊆ closure (effectiveDomain f) := by
  intro x hx
  obtain ⟨a, ha, _⟩ := EReal.exists_between_coe_real hx
  have he : (x, a) ∈ closure (epigraph f) := by
    rw [← epigraph_epiClosure]
    exact ha.le
  have h := mem_closure_image continuous_fst.continuousAt he
  rwa [epigraph_proj_eq_effectiveDomain] at h

omit [FiniteDimensional ℝ E] in
/-- **Proposition 2.32**: the closure of a convex set is convex, and the closure
`cl f` of a convex function is convex. -/
theorem convex_closure_and_isConvexRelative_epiClosure :
    (∀ C : Set E, Convex ℝ C → Convex ℝ (closure C)) ∧
      ∀ f : E → EReal, IsConvexRelative univ f → IsConvexRelative univ (epiClosure f) := by
  refine ⟨fun C hC ↦ hC.closure, fun f hf ↦ ?_⟩
  rw [isConvexRelative_univ_iff, epigraph_epiClosure]
  exact ((isConvexRelative_univ_iff f).mp hf).closure

/-- **Proposition 2.32**: for convex `f`, `cl f` is proper if and only if `f` is
proper. -/
theorem isProper_epiClosure_iff {f : E → EReal} (hf : IsConvexRelative univ f) :
    IsProper (epiClosure f) ↔ IsProper f := by
  constructor
  · rintro ⟨⟨x, hx⟩, hbot⟩
    refine ⟨?_, fun y ↦ (hbot y).trans_le (epiClosure_le_self f y)⟩
    obtain ⟨y, hy⟩ := closure_nonempty_iff.mp
      ⟨x, effectiveDomain_epiClosure_subset_closure f hx⟩
    exact ⟨y, hy⟩
  · intro hp
    exact isProper_of_isLowerClosure hp ((isConvexRelative_univ_iff f).mp hf)
      (epigraph_epiClosure f)

/-! ## Theorem 2.33 -/

/-- **Theorem 2.33 (line segment principle)**: for convex `C`,
`int C ≠ ∅ ↔ int(cl C) ≠ ∅`; if `x₀ ∈ int C` and `x₁ ∈ cl C` then the points
`(1 - τ)x₀ + τx₁`, `τ ∈ (0,1)`, lie in `int C`; `int C` is convex; and when
`int C ≠ ∅`, `cl C = cl(int C)` and `int C = int(cl C)`. -/
theorem line_segment_principle {C : Set E} (hC : Convex ℝ C) :
    ((interior C).Nonempty ↔ (interior (closure C)).Nonempty) ∧
      (∀ x₀ ∈ interior C, ∀ x₁ ∈ closure C, ∀ τ : ℝ, 0 < τ → τ < 1 →
        (1 - τ) • x₀ + τ • x₁ ∈ interior C) ∧
      Convex ℝ (interior C) ∧
      ((interior C).Nonempty → closure C = closure (interior C) ∧
        interior C = interior (closure C)) := by
  refine ⟨by rw [Convex.interior_closure_eq hC], fun x₀ hx₀ x₁ hx₁ τ hτ0 hτ1 ↦ ?_, hC.interior,
    fun hne ↦ ⟨(hC.closure_interior_eq_closure_of_nonempty_interior hne).symm,
      (hC.interior_closure_eq_interior_of_nonempty_interior hne).symm⟩⟩
  exact hC.combo_interior_closure_mem_interior hx₀ hx₁ (by linarith) hτ0.le (by ring)

/-! ## Proposition 2.34 -/

/-- **Proposition 2.34**: `int(epi f) = {(x, α) | x ∈ int(dom f), f(x) < α}`. -/
theorem interior_epigraph_eq {f : E → EReal} (hf : IsConvexRelative univ f) :
    interior (epigraph f) =
      {p : E × ℝ | p.1 ∈ interior (effectiveDomain f) ∧ f p.1 < (p.2 : EReal)} := by
  ext ⟨x, a⟩
  exact mem_interior_epigraph_iff_of_convex ((isConvexRelative_univ_iff f).mp hf)

/-- **Proposition 2.34**: `int(lev≤α f) = {x ∈ int(dom f) | f(x) < α}` for
`α ∈ (inf f, ∞)`. -/
theorem interior_levelSet_eq {f : E → EReal} (hf : IsConvexRelative univ f) {α : ℝ}
    (hα : (⨅ x, f x) < (α : EReal)) :
    interior (levelSet f α) = {x | x ∈ interior (effectiveDomain f) ∧ f x < (α : EReal)} := by
  have hc := (isConvexRelative_univ_iff f).mp hf
  ext x
  constructor
  · intro hx
    have hsub : levelSet f α ⊆ effectiveDomain f := fun y hy ↦
      lt_of_le_of_lt (show f y ≤ (α : EReal) from hy) (EReal.coe_lt_top α)
    refine ⟨interior_mono hsub hx, ?_⟩
    obtain ⟨x₀, hx₀⟩ := iInf_lt_iff.mp hα
    obtain ⟨r, hr, hrα⟩ := EReal.lt_iff_exists_real_btwn.mp hx₀
    have hrα' : r < α := by exact_mod_cast hrα
    have hcont : Continuous (fun ε : ℝ ↦ x + ε • (x - x₀)) := by fun_prop
    have htend : Tendsto (fun ε : ℝ ↦ x + ε • (x - x₀)) (𝓝[>] 0) (𝓝 x) := by
      have := hcont.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hε, hεpos⟩ :=
      ((htend.eventually (mem_interior_iff_mem_nhds.mp hx)).and self_mem_nhdsWithin).exists
    have hεpos' : (0 : ℝ) < ε := hεpos
    set τ : ℝ := 1 / (1 + ε) with hτ
    have hτ0 : 0 < τ := by positivity
    have hτ1 : τ < 1 := by
      rw [hτ, div_lt_one (by linarith)]
      linarith
    have hkey : τ * (1 + ε) = 1 := by
      rw [hτ]
      field_simp
    have hx_eq : (1 - τ) • x₀ + τ • (x + ε • (x - x₀)) = x := by
      calc (1 - τ) • x₀ + τ • (x + ε • (x - x₀))
          = (1 - τ * (1 + ε)) • x₀ + (τ * (1 + ε)) • x := by module
        _ = x := by rw [hkey]; simp
    have h := hf.le_of_le hr.le (show f (x + ε • (x - x₀)) ≤ (α : EReal) from hε) hτ0.le hτ1.le
    rw [hx_eq] at h
    refine h.trans_lt (EReal.coe_lt_coe_iff.mpr ?_)
    nlinarith
  · rintro ⟨hx, hfx⟩
    have hint := mem_interior_epigraph_of_mem_interior_effectiveDomain hc hx hfx
    rw [mem_interior_iff_mem_nhds] at hint ⊢
    have hcont : Continuous (fun y : E ↦ (y, α)) := by fun_prop
    exact (hcont.tendsto x).eventually hint |>.mono fun y hy ↦ (mem_epigraph_iff f y α).mp hy

/-! ## Theorem 2.35 -/

/-- **Theorem 2.35**: a convex function is continuous on `int(dom f)`. -/
theorem IsConvexRelative.continuousOn_interior_effectiveDomain {f : E → EReal}
    (hf : IsConvexRelative univ f) : ContinuousOn f (interior (effectiveDomain f)) := by
  set U := interior (effectiveDomain f) with hU
  by_cases hp : IsProper f
  · have hfin : ∀ x ∈ U, f x = ((f x).toReal : EReal) := by
      intro x hx
      have hxd : x ∈ effectiveDomain f := interior_subset hx
      exact (EReal.coe_toReal (ne_of_lt hxd) (hp.2 x).ne').symm
    have hconvU : Convex ℝ U := hf.convex_effectiveDomain.interior
    have hg : ConvexOn ℝ U (fun x ↦ (f x).toReal) := by
      rw [← isConvexRelative_coe_iff hconvU]
      exact (hf.mono (subset_univ U)).congr hconvU hfin
    have hcont := (continuous_coe_real_ereal.comp_continuousOn (hg.continuousOn isOpen_interior))
    exact hcont.congr fun x hx ↦ hfin x hx
  · have hbot : ∀ x ∈ U, f x = ⊥ := fun x hx ↦ hf.eq_bot_of_mem_interior_of_not_isProper hp hx
    exact continuousOn_const.congr hbot

/-- **Theorem 2.35**: `f` agrees with `cl f` on `int(dom f)`, which is also
`int(dom(cl f))`; outside `dom(cl f) ⊆ cl(dom f)` both equal `∞`. -/
theorem epiClosure_agrees {f : E → EReal} (hf : IsConvexRelative univ f) :
    (∀ x ∈ interior (effectiveDomain f), epiClosure f x = f x) ∧
      interior (effectiveDomain (epiClosure f)) = interior (effectiveDomain f) ∧
      effectiveDomain (epiClosure f) ⊆ closure (effectiveDomain f) ∧
      ∀ x ∉ effectiveDomain (epiClosure f), epiClosure f x = ⊤ ∧ f x = ⊤ := by
  have hc := (isConvexRelative_univ_iff f).mp hf
  refine ⟨fun x hx ↦ epiClosure_eq_of_mem_interior_convex hc hx, interior_domain_epiClosure hc,
    effectiveDomain_epiClosure_subset_closure f, fun x hx ↦ ?_⟩
  have h1 : epiClosure f x = ⊤ := by simpa [effectiveDomain] using hx
  exact ⟨h1, top_le_iff.mp (h1 ▸ epiClosure_le_self f x)⟩

/-- **Theorem 2.35**, closure formula 2(11): for `x₀ ∈ int(dom f)`,
`(cl f)(x) = lim_{τ ↗ 1} f((1 - τ)x₀ + τx)` for every `x`. -/
theorem tendsto_epiClosure_of_mem_interior {f : E → EReal} (hf : IsConvexRelative univ f)
    {x₀ : E} (hx₀ : x₀ ∈ interior (effectiveDomain f)) (x : E) :
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
    have hx₀d : x₀ ∈ effectiveDomain f := interior_subset hx₀
    obtain ⟨α₀, hα₀, -⟩ := EReal.lt_iff_exists_real_btwn.mp hx₀d
    have hint := mem_interior_epigraph_of_mem_interior_effectiveDomain hc hx₀ hα₀
    have hseg : ∀ τ : ℝ, 0 ≤ τ → τ < 1 →
        f ((1 - τ) • x₀ + τ • x) ≤ (((1 - τ) * α₀ + τ * α : ℝ) : EReal) := by
      intro τ hτ0 hτ1
      have hm := hc.combo_interior_closure_mem_interior hint hxα (by linarith : (0 : ℝ) < 1 - τ)
        hτ0 (by ring)
      have := interior_subset hm
      simpa [mem_epigraph_iff] using this
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

/-! ## Corollary 2.36 -/

/-- **Corollary 2.36**: a finite convex function on an open convex set is
continuous there. -/
theorem continuousOn_of_convexOn_isOpen {O : Set E} (hO : IsOpen O) {f : E → ℝ}
    (hf : ConvexOn ℝ O f) : ContinuousOn f O :=
  hf.continuousOn hO

open Classical in
/-- **Corollary 2.36**: a finite convex function on a nonempty open convex set
has a unique extension to a proper lsc convex function with domain inside
`cl O`. -/
theorem existsUnique_lsc_extension {O : Set E} (hO : IsOpen O) (hOc : Convex ℝ O)
    (hne : O.Nonempty) {f : E → ℝ} (hf : ConvexOn ℝ O f) :
    ∃! g : E → EReal, IsProper g ∧ LowerSemicontinuous g ∧ IsConvexRelative univ g ∧
      (∀ x ∈ O, g x = f x) ∧ effectiveDomain g ⊆ closure O := by
  set h : E → EReal := fun x ↦ if x ∈ O then (f x : EReal) else ⊤ with hh
  have hhconv : IsConvexRelative univ h :=
    (isConvexRelative_iff_extension hOc _).mp ((isConvexRelative_coe_iff hOc f).mpr hf)
  have hdom : effectiveDomain h = O := by
    ext x
    by_cases hx : x ∈ O <;> simp [effectiveDomain, hh, hx]
  have hhp : IsProper h := by
    refine ⟨?_, fun x ↦ ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨x, by simp [hh, hx]⟩
    · by_cases hx : x ∈ O <;> simp [hh, hx]
  have hint : interior (effectiveDomain h) = O := by rw [hdom, hO.interior_eq]
  have hagree := epiClosure_agrees hhconv
  have hgO : ∀ x ∈ O, epiClosure h x = f x := by
    intro x hx
    rw [hagree.1 x (hint ▸ hx)]
    simp [hh, hx]
  refine ⟨epiClosure h, ⟨(isProper_epiClosure_iff hhconv).mpr hhp,
    lowerSemicontinuous_epiLowerLimit _, convex_closure_and_isConvexRelative_epiClosure.2 h hhconv,
    hgO, hdom ▸ hagree.2.2.1⟩, ?_⟩
  rintro g ⟨hgp, hgl, hgc, hgO', hgdom⟩
  funext x
  obtain ⟨x₀, hx₀⟩ := hne
  by_cases hxc : x ∈ closure O
  · have hOsub : O ⊆ interior (effectiveDomain g) := by
      refine interior_maximal (fun y hy ↦ ?_) hO
      change g y < ⊤
      rw [hgO' y hy]
      exact EReal.coe_lt_top _
    have hl1 := tendsto_epiClosure_of_mem_interior hgc (hOsub hx₀) x
    have hl2 := tendsto_epiClosure_of_mem_interior hhconv (hint.symm ▸ hx₀) x
    rw [epiClosure_eq_of_lowerSemicontinuous hgl] at hl1
    have hseg : ∀ τ : ℝ, 0 < τ → τ < 1 → (1 - τ) • x₀ + τ • x ∈ O := by
      intro τ hτ0 hτ1
      have := (line_segment_principle hOc).2.1 x₀ (hO.interior_eq.symm ▸ hx₀) x hxc τ
        (by linarith) (by linarith)
      rwa [hO.interior_eq] at this
    have heq : ∀ᶠ τ in 𝓝[<] (1 : ℝ),
        g ((1 - τ) • x₀ + τ • x) = h ((1 - τ) • x₀ + τ • x) := by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with τ hτ
      have hmem := hseg τ hτ.1 hτ.2
      rw [hgO' _ hmem]
      simp [hh, hmem]
    exact tendsto_nhds_unique hl1 ((hl2.congr' (heq.mono fun τ hτ ↦ hτ.symm)))
  · have h1 : g x = ⊤ := by
      by_contra hne'
      exact hxc (hgdom (lt_top_iff_ne_top.mpr hne'))
    have h2 : epiClosure h x = ⊤ := by
      by_contra hne'
      exact hxc (hdom ▸ effectiveDomain_epiClosure_subset_closure h (lt_top_iff_ne_top.mpr hne'))
    rw [h1, h2]

/-! ## Corollary 2.37 -/

/-- The reparametrization `y = (1 - φ(y))x₀ + φ(y)x` of a line in `ℝ`. -/
theorem closure_formula_reparam {x₀ x : ℝ} (hxx₀ : x ≠ x₀) (y : ℝ) :
    (1 - (x₀ - y) / (x₀ - x)) • x₀ + ((x₀ - y) / (x₀ - x)) • x = y := by
  have hden : x₀ - x ≠ 0 := sub_ne_zero.mpr hxx₀.symm
  simp only [smul_eq_mul]
  field_simp
  ring

/-- One-sided form of the closure formula 2(11) on the real line. -/
theorem tendsto_of_closure_formula_real {f : ℝ → EReal} {x₀ x : ℝ} {L : EReal}
    (hlim : Tendsto (fun τ : ℝ ↦ f ((1 - τ) • x₀ + τ • x)) (𝓝[<] 1) (𝓝 L)) :
    (x < x₀ → Tendsto f (𝓝[>] x) (𝓝 L)) ∧ (x₀ < x → Tendsto f (𝓝[<] x) (𝓝 L)) := by
  have hφc : Continuous (fun y : ℝ ↦ (x₀ - y) / (x₀ - x)) := by fun_prop
  have key : ∀ l : Filter ℝ, l ≤ 𝓝 x → (∀ᶠ y in l, (x₀ - y) / (x₀ - x) < 1) → x ≠ x₀ →
      Tendsto f l (𝓝 L) := by
    intro l hl hev hxx₀
    have hφx : (x₀ - x) / (x₀ - x) = 1 := div_self (sub_ne_zero.mpr hxx₀.symm)
    have hφt : Tendsto (fun y : ℝ ↦ (x₀ - y) / (x₀ - x)) l (𝓝[<] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, hev⟩
      have := hφc.tendsto x
      rw [hφx] at this
      exact this.mono_left hl
    exact (hlim.comp hφt).congr fun y ↦ by
      simp only [Function.comp_apply, closure_formula_reparam hxx₀ y]
  refine ⟨fun hlt ↦ key _ nhdsWithin_le_nhds ?_ hlt.ne, fun hgt ↦ key _ nhdsWithin_le_nhds ?_
    hgt.ne'⟩
  · filter_upwards [self_mem_nhdsWithin] with y hy
    rw [div_lt_one (sub_pos.mpr hlt)]
    linarith [show x < y from hy]
  · filter_upwards [self_mem_nhdsWithin] with y hy
    rw [div_lt_one_of_neg (sub_neg.mpr hgt)]
    linarith [show y < x from hy]

/-- **Corollary 2.37**: a lower semicontinuous convex function `f : ℝ → ℝ̄` is
continuous relative to `cl(dom f)`. -/
theorem continuousOn_closure_effectiveDomain_real {f : ℝ → EReal}
    (hf : IsConvexRelative univ f) (hl : LowerSemicontinuous f) :
    ContinuousOn f (closure (effectiveDomain f)) := by
  set D := effectiveDomain f with hDdef
  have hD : Convex ℝ D := hf.convex_effectiveDomain
  by_cases hint : (interior D).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hint
    intro x hx
    by_cases hxi : x ∈ interior D
    · exact (hf.continuousOn_interior_effectiveDomain.continuousAt
        (isOpen_interior.mem_nhds hxi)).continuousWithinAt
    have hlim := tendsto_epiClosure_of_mem_interior hf hx₀ x
    rw [epiClosure_eq_of_lowerSemicontinuous hl] at hlim
    have hseg := (line_segment_principle hD).2.1
    have hone := tendsto_of_closure_formula_real hlim
    rcases lt_or_gt_of_ne (fun h : x = x₀ ↦ hxi (h ▸ hx₀)) with hlt | hgt
    · have hside : closure D ⊆ Ici x := by
        intro y hy
        by_contra hyx
        simp only [mem_Ici, not_le] at hyx
        apply hxi
        have hτ := hseg x₀ hx₀ y hy ((x₀ - x) / (x₀ - y)) (div_pos (by linarith) (by linarith))
          ((div_lt_one (by linarith)).mpr (by linarith))
        have hne : x₀ - y ≠ 0 := ne_of_gt (by linarith)
        convert hτ using 1
        simp only [smul_eq_mul]
        field_simp
        ring
      exact (continuousWithinAt_Ioi_iff_Ici.mp (hone.1 hlt)).mono hside
    · have hside : closure D ⊆ Iic x := by
        intro y hy
        by_contra hyx
        simp only [mem_Iic, not_le] at hyx
        apply hxi
        have hτ := hseg x₀ hx₀ y hy ((x - x₀) / (y - x₀)) (div_pos (by linarith) (by linarith))
          ((div_lt_one (by linarith)).mpr (by linarith))
        have hne : y - x₀ ≠ 0 := ne_of_gt (by linarith)
        convert hτ using 1
        simp only [smul_eq_mul]
        field_simp
        ring
      exact (continuousWithinAt_Iio_iff_Iic.mp (hone.2 hgt)).mono hside
  · have hsub : D.Subsingleton := by
      intro a ha b hb
      by_contra hab
      apply hint
      rcases lt_or_gt_of_ne hab with h | h
      · refine ⟨(a + b) / 2, mem_interior_iff_mem_nhds.mpr (mem_of_superset
          (Ioo_mem_nhds (show a < (a + b) / 2 by linarith) (show (a + b) / 2 < b by linarith))
          ?_)⟩
        exact Ioo_subset_Icc_self.trans (hD.ordConnected.out ha hb)
      · refine ⟨(a + b) / 2, mem_interior_iff_mem_nhds.mpr (mem_of_superset
          (Ioo_mem_nhds (show b < (a + b) / 2 by linarith) (show (a + b) / 2 < a by linarith))
          ?_)⟩
        exact Ioo_subset_Icc_self.trans (hD.ordConnected.out hb ha)
    exact hsub.closure.continuousOn f

/-! ## Theorem 2.35: continuity relative to convex hulls of finite sets -/

section FiniteHulls

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Theorem 2.35** (last assertion): an lsc convex function is continuous
relative to the convex hull of any finite subset of its effective domain.

The hull is parametrized by the standard simplex through the quotient map
`w ↦ ∑ w_c c`.  Near a weight vector `wb`, every weight vector is
`(1 - s) wb + s μ` with `μ` in the standard simplex for a fixed small `s`, so
convexity bounds `f` above by `(1 - s) r + s M` for any real `r > f(x̄)`,
where `M` bounds `f` on the hull; lower semicontinuity gives the lower
bound. -/
theorem IsConvexRelative.continuousOn_convexHull_of_finite {f : F → EReal}
    (hf : IsConvexRelative univ f) (hlsc : LowerSemicontinuous f) {C : Set F}
    (hC : C.Finite) (hCdom : ∀ x ∈ C, f x < ⊤) : ContinuousOn f (convexHull ℝ C) := by
  classical
  letI := hC.fintype
  -- a real upper bound for `f` on `con C`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ C, f x ≤ (M : EReal) := by
    refine ⟨∑ c : C, |(f c).toReal|, fun x hx ↦ ?_⟩
    calc f x ≤ ((f x).toReal : EReal) := EReal.le_coe_toReal (hCdom x hx).ne
      _ ≤ _ := EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans
          (Finset.single_le_sum (f := fun c : C ↦ |(f c).toReal|) (fun _ _ ↦ abs_nonneg _)
            (Finset.mem_univ ⟨x, hx⟩)))
  have hMS : ∀ y ∈ convexHull ℝ C, f y ≤ (M : EReal) := fun y hy ↦
    convexHull_min (fun x hx ↦ hM x hx) (hf.convex_levelSet (M : EReal)) hy
  -- the parametrization by the standard simplex
  let Φ : (C → ℝ) → F := fun w ↦ ∑ c : C, w c • (c : F)
  have hΦcont : Continuous Φ := continuous_finset_sum _ fun c _ ↦
    (continuous_apply c).smul continuous_const
  have hΦmem : ∀ w ∈ stdSimplex ℝ C, Φ w ∈ convexHull ℝ C := fun w hw ↦
    (convex_convexHull ℝ C).sum_mem (fun c _ ↦ hw.1 c) hw.2
      (fun c _ ↦ subset_convexHull ℝ C c.2)
  have hΦsurj : ∀ x ∈ convexHull ℝ C, ∃ w ∈ stdSimplex ℝ C, Φ w = x := by
    intro x hx
    rw [hC.convexHull_eq_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w, hw, by simp [Φ]⟩
  -- continuity of `f ∘ Φ` on the standard simplex
  have hg : Continuous fun w : stdSimplex ℝ C ↦ f (Φ w) := by
    refine continuous_iff_continuousAt.mpr fun wb ↦ tendsto_order.mpr ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
    · exact ((hΦcont.comp continuous_subtype_val).tendsto wb).eventually (hlsc (Φ wb) b hb)
    rcases eq_or_ne b ⊤ with rfl | hbtop
    · exact Eventually.of_forall fun w ↦ (hMS _ (hΦmem w w.2)).trans_lt (EReal.coe_lt_top M)
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hb
    have hbr : b = ((b.toReal : ℝ) : EReal) := (EReal.coe_toReal hbtop (ne_bot_of_gt hr2)).symm
    have hrb : r < b.toReal := by
      rw [hbr] at hr2
      exact_mod_cast hr2
    set s₀ : ℝ := min 1 ((b.toReal - r) / (2 * (|M - r| + 1))) with hs₀
    have hs₀pos : 0 < s₀ := lt_min one_pos (div_pos (sub_pos.mpr hrb) (by positivity))
    have hs₀1 : s₀ ≤ 1 := min_le_left _ _
    have hbound : (1 - s₀) * r + s₀ * M < b.toReal := by
      have h1 : s₀ * (M - r) ≤ s₀ * |M - r| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hs₀pos.le
      have h2 : s₀ * |M - r| < b.toReal - r := by
        have hle : s₀ ≤ (b.toReal - r) / (2 * (|M - r| + 1)) := min_le_right _ _
        have hpos : 0 < 2 * (|M - r| + 1) := by positivity
        calc s₀ * |M - r| ≤ (b.toReal - r) / (2 * (|M - r| + 1)) * |M - r| :=
              mul_le_mul_of_nonneg_right hle (abs_nonneg _)
          _ < b.toReal - r := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
              nlinarith [abs_nonneg (M - r), sub_pos.mpr hrb]
      nlinarith
    have hev : ∀ᶠ w : stdSimplex ℝ C in 𝓝 wb,
        ∀ c, (1 - s₀) * (wb : C → ℝ) c ≤ (w : C → ℝ) c := by
      rw [eventually_all]
      intro c
      by_cases hc : (wb : C → ℝ) c = 0
      · exact Eventually.of_forall fun w ↦ by
          rw [hc, mul_zero]
          exact w.2.1 c
      · have hpos : 0 < (wb : C → ℝ) c := lt_of_le_of_ne (wb.2.1 c) (Ne.symm hc)
        have hlt : (1 - s₀) * (wb : C → ℝ) c < (wb : C → ℝ) c := by nlinarith
        exact (((continuous_apply c).comp continuous_subtype_val).continuousAt.eventually
          (lt_mem_nhds hlt)).mono fun w hw ↦ hw.le
    filter_upwards [hev] with w hw
    let μ : C → ℝ := fun c ↦ ((w : C → ℝ) c - (1 - s₀) * (wb : C → ℝ) c) / s₀
    have hw1 : ∑ c, (w : C → ℝ) c = 1 := w.2.2
    have hwb1 : ∑ c, (wb : C → ℝ) c = 1 := wb.2.2
    have hμ : μ ∈ stdSimplex ℝ C := by
      refine ⟨fun c ↦ div_nonneg (sub_nonneg.mpr (hw c)) hs₀pos.le, ?_⟩
      simp only [μ, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hw1, hwb1]
      field_simp
      ring
    have hrep : Φ w = (1 - s₀) • Φ wb + s₀ • Φ μ := by
      simp only [Φ, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul, ← add_smul]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      congr 1
      simp only [μ]
      field_simp
      ring
    have hle := hf.le_of_le (x₀ := Φ wb) (x₁ := Φ μ) hr1.le (hMS _ (hΦmem μ hμ)) hs₀pos.le hs₀1
    rw [← hrep] at hle
    rw [hbr]
    exact hle.trans_lt (EReal.coe_lt_coe_iff.mpr hbound)
  -- transfer through the quotient map onto `con C`
  let Ψ : stdSimplex ℝ C → convexHull ℝ C := fun w ↦ ⟨Φ w, hΦmem w w.2⟩
  have hΨcont : Continuous Ψ := (hΦcont.comp continuous_subtype_val).subtype_mk _
  haveI : CompactSpace (stdSimplex ℝ C) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex _)
  have hΨq : Topology.IsQuotientMap Ψ := hΨcont.isClosedMap.isQuotientMap hΨcont fun x ↦ by
    obtain ⟨w, hw, hwx⟩ := hΦsurj x x.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwx⟩
  rw [continuousOn_iff_continuous_restrict, hΨq.continuous_iff]
  exact hg

/-- **Theorem 2.35**: in particular, an lsc convex function is continuous
relative to any line segment in its effective domain. -/
theorem IsConvexRelative.continuousOn_segment {f : F → EReal} (hf : IsConvexRelative univ f)
    (hlsc : LowerSemicontinuous f) {a b : F} (ha : f a < ⊤) (hb : f b < ⊤) :
    ContinuousOn f (segment ℝ a b) := by
  rw [← convexHull_pair]
  refine hf.continuousOn_convexHull_of_finite hlsc (toFinite _) fun x hx ↦ ?_
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

end FiniteHulls

end RW
