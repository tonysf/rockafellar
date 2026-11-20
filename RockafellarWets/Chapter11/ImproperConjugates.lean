/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Improper conjugates and improper closed convex hulls
-/
import RockafellarWets.Chapter11.ConjugateInvariance

open Set Filter Topology
open scoped InnerProductSpace Classical
namespace RW
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp] theorem fenchelConjugate_top : fenchelConjugate (fun _ : E ↦ (⊤:EReal)) = fun _ ↦ ⊥ := by
  funext v
  simp [fenchelConjugate]

@[simp] theorem fenchelConjugate_bot : fenchelConjugate (fun _ : E ↦ (⊥:EReal)) = fun _ ↦ ⊤ := by
  funext v
  simp [fenchelConjugate]

theorem fenchelConjugate_eq_top_of_bot {f : E → EReal} {x : E} (hx : f x = ⊥) :
    fenchelConjugate f = fun _ ↦ ⊤ := by
  funext v
  apply top_unique
  simpa [hx] using le_fenchelConjugate f x v

/-- **Theorem 11.2**, a `-∞` value of the convex hull makes the conjugate
identically `+∞` and the biconjugate identically `-∞`. -/
theorem improper_convexHull_conjugates {f : E → EReal} {x : E}
    (hx : convexHullFunction f x = ⊥) :
    fenchelConjugate f = (fun _ ↦ ⊤) ∧
    fenchelConjugate (fenchelConjugate f) = (fun _ ↦ ⊥) := by
  have he : fenchelConjugate f = fun _ ↦ ⊤ := by
    rw [← fenchelConjugate_convexHullFunction f]
    exact fenchelConjugate_eq_top_of_bot hx
  exact ⟨he,by rw [he,fenchelConjugate_top]⟩

/-- A convex epigraph with a full vertical fiber has a full vertical fiber
above every point in the closure of its effective domain after closure. -/
theorem closure_epigraph_of_bot {f : E → EReal} (hc : Convex ℝ (epigraph f))
    {x₀ : E} (hx₀ : f x₀ = ⊥) :
    closure (epigraph f) = {p : E × ℝ | p.1 ∈ closure (effectiveDomain f)} := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro p hp
      exact subset_closure (hp.trans_lt (EReal.coe_lt_top p.2))
    · exact isClosed_closure.preimage continuous_fst
  · rintro ⟨x,a⟩ hx
    have hdom : ∀ y ∈ effectiveDomain f, (y,a) ∈ closure (epigraph f) := by
      intro y hy
      obtain ⟨b,hb⟩ := EReal.exists_between_coe_real hy
      have hyb : (y,b) ∈ epigraph f := hb.1.le
      let t : ℕ → ℝ := fun n ↦ ((n:ℝ)+1)⁻¹
      have ht0 (n : ℕ) : 0 < t n := by dsimp [t]; positivity
      have ht1 (n : ℕ) : t n ≤ 1 := by
        dsimp [t]
        exact inv_le_one_of_one_le₀ (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
      have ht : Tendsto t atTop (𝓝 0) := by
        simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hp : ∀ n, (t n • x₀+(1-t n) • y,a) ∈ epigraph f := by
        intro n
        have hbase : (x₀,(a-(1-t n)*b)/t n) ∈ epigraph f := by
          change f x₀ ≤ _
          rw [hx₀]
          exact bot_le
        have hmem := hc hbase hyb (ht0 n).le (sub_nonneg.mpr (ht1 n)) (by ring)
        have he : t n*((a-(1-t n)*b)/t n)+(1-t n)*b = a := by
          field_simp [(ht0 n).ne']
          <;> ring
        simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul,he] using hmem
      have hlim : Tendsto (fun n ↦ (t n • x₀+(1-t n) • y,a)) atTop (𝓝 (y,a)) := by
        simpa only [zero_smul,sub_zero,one_smul,zero_add] using
          ((ht.smul (tendsto_const_nhds (x := x₀))).add
          (((tendsto_const_nhds (x := (1:ℝ))).sub ht).smul (tendsto_const_nhds (x := y)))).prodMk_nhds
            (tendsto_const_nhds (x := a))
      exact isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ subset_closure (hp n))
    exact closure_minimal hdom
      (isClosed_closure.preimage (continuous_id.prodMk continuous_const)) hx

/-- The closed hull of an improper convex function is `-∞` on the closure
of its effective domain and `+∞` elsewhere. -/
theorem epiClosure_of_convex_bot {f : E → EReal} (hc : Convex ℝ (epigraph f))
    {x₀ : E} (hx₀ : f x₀ = ⊥) :
    epiClosure f = fun x ↦ if x ∈ closure (effectiveDomain f) then ⊥ else ⊤ := by
  apply eq_of_epigraph_eq
  rw [epigraph_epiClosure,closure_epigraph_of_bot hc hx₀]
  ext p
  by_cases h : p.1 ∈ closure (effectiveDomain f) <;> simp [epigraph,h]

/-- **Theorem 11.2**, the complete improper closed-convex-hull formula. -/
theorem epiClosure_convexHull_of_bot {f : E → EReal} {x₀ : E}
    (hx₀ : convexHullFunction f x₀ = ⊥) :
    epiClosure (convexHullFunction f) =
      fun x ↦ if x ∈ closure (effectiveDomain (convexHullFunction f)) then ⊥ else ⊤ :=
  epiClosure_of_convex_bot (convex_epigraph_convexHullFunction f) hx₀

/-- The remaining improper case in 11.2: the identically infinite function. -/
theorem identically_top_conjugates :
    fenchelConjugate (fun _ : E ↦ (⊤:EReal)) = (fun _ ↦ ⊥) ∧
    fenchelConjugate (fenchelConjugate (fun _ : E ↦ (⊤:EReal))) = (fun _ ↦ ⊤) := by
  simp

end
end RW
