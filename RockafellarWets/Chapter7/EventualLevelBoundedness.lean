/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eventual level boundedness of function sequences

Exercise 7.32. The connected-sublevel criterion allows empty sublevels. A
single point of the effective domain of the limit supplies the eventual hits
at every sufficiently high level.
-/

import RockafellarWets.Chapter7.EpiLimits
import RockafellarWets.Chapter4.EventuallyBounded
import RockafellarWets.Chapter4.ConnectedLimits
import RockafellarWets.Chapter3.Coercivity

open Filter Metric Set Topology

namespace RW

variable {E : Type*} [NormedAddCommGroup E]

/-- Eventual level boundedness just before Exercise 7.32. The common bound and
the index beyond which it holds may depend on the real level. -/
def IsEventuallyLevelBounded (f : ℕ → E → EReal) : Prop :=
  ∀ a : ℝ, EventuallyBounded (fun n ↦ levelSet (f n) a)

/-- **Exercise 7.32(a)**, a common level-bounded lower bound. -/
theorem isEventuallyLevelBounded_of_eventually_ge {f : ℕ → E → EReal} {g : E → EReal}
    (hg : IsLevelBounded g) (h : ∀ᶠ n in atTop, g ≤ f n) : IsEventuallyLevelBounded f := by
  intro a
  obtain ⟨r, hr⟩ := (hg a).subset_closedBall (0 : E)
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  exact ⟨r, N, fun n hn x hx ↦ hr ((hN n hn x).trans hx)⟩

/-- **Exercise 7.32(a)**, a common eventual bound on the effective domains. -/
theorem isEventuallyLevelBounded_of_effectiveDomain {f : ℕ → E → EReal}
    (h : EventuallyBounded (fun n ↦ effectiveDomain (f n))) : IsEventuallyLevelBounded f := by
  obtain ⟨r, N, hN⟩ := h
  exact fun a ↦ ⟨r, N, fun n hn x hx ↦ hN n hn (lt_of_le_of_lt hx (EReal.coe_lt_top a))⟩

private theorem mem_innerSetLimit_levelSet_of_lt {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) {x : E} {a : ℝ} (hxa : g x < a) :
    x ∈ innerSetLimit (fun n ↦ levelSet (f n) a) := by
  obtain ⟨b, hxb, hba⟩ := EReal.exists_between_coe_real hxa
  have hx : (x, b) ∈ innerSetLimit (fun n ↦ epigraph (f n)) := h.inner_eq.symm ▸ hxb.le
  intro V hV
  filter_upwards [hx (V ×ˢ Iio a) (prod_mem_nhds hV
    (Iio_mem_nhds (EReal.coe_lt_coe_iff.1 hba)))] with n hn
  obtain ⟨p, hp, hpV, hpa⟩ := hn
  exact ⟨p.1, le_trans hp (EReal.coe_le_coe_iff.2 (le_of_lt hpa)), hpV⟩

private theorem outer_levelSet_subset_of_epiConverges {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (a : ℝ) :
    outerSetLimit (fun n ↦ levelSet (f n) a) ⊆ levelSet g a := by
  intro x hx
  obtain ⟨φ, ys, hφ, hys, hto⟩ := mem_outerSetLimit_iff_exists_subsequence.1 hx
  have hp : (x, a) ∈ outerSetLimit (fun n ↦ epigraph (f n)) :=
    mem_outerSetLimit_iff_exists_subsequence.2 ⟨φ, fun k ↦ (ys k, a), hφ, hys,
      hto.prodMk_nhds tendsto_const_nhds⟩
  rw [h.outer_eq] at hp
  exact hp

/-- **Exercise 7.32(b)**, the epi-limit is level bounded. -/
theorem isLevelBounded_of_isEventuallyLevelBounded {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hb : IsEventuallyLevelBounded f) : IsLevelBounded g := by
  intro a
  obtain ⟨r, N, hN⟩ := hb (a + 1)
  apply (isBounded_closedBall (x := (0 : E)) (r := r)).subset
  intro x hx
  by_contra hxout
  have hin := mem_innerSetLimit_levelSet_of_lt h (lt_of_le_of_lt hx
    (EReal.coe_lt_coe_iff.2 (lt_add_one a)))
  have hnh : (closedBall (0 : E) r)ᶜ ∈ 𝓝 x := isClosed_closedBall.isOpen_compl.mem_nhds hxout
  obtain ⟨n, ⟨y, hy, hyout⟩, hn⟩ := ((hin _ hnh).and (eventually_ge_atTop N)).exists
  exact hyout (hN n hn hy)

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exercise 7.32(b)**, the epi-limit is inf-compact. -/
theorem isInfCompact_of_isEventuallyLevelBounded {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hb : IsEventuallyLevelBounded f) : IsInfCompact g :=
  isInfCompact_of_isLevelBounded_of_lsc (lowerSemicontinuous_of_isClosed_epigraph_ereal g
    (PKConverges.isClosed h)) (isLevelBounded_of_isEventuallyLevelBounded h hb)

/-- **Exercise 7.32(c)**, connected sublevels and a level-bounded epi-limit
with nonempty effective domain force eventual level boundedness. -/
theorem isEventuallyLevelBounded_of_preconnected_levelSet {f : ℕ → E → EReal} {g : E → EReal}
    (h : EpiConverges f g) (hb : IsLevelBounded g) (hne : (effectiveDomain g).Nonempty)
    (hc : ∀ n (a : ℝ), IsPreconnected (levelSet (f n) a)) : IsEventuallyLevelBounded f := by
  intro a
  obtain ⟨x, hx⟩ := hne
  obtain ⟨b, hxb, _⟩ := EReal.exists_between_coe_real hx
  let A := max a b
  have hin := mem_innerSetLimit_levelSet_of_lt h (hxb.trans_le
    (EReal.coe_le_coe_iff.2 (le_max_right a b)))
  have hnevent : ∀ᶠ n in atTop, (levelSet (f n) A).Nonempty :=
    (hin univ univ_mem).mono fun _ ⟨y, hy, _⟩ ↦ ⟨y, hy⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnevent
  let φ : ℕ → ℕ := fun k ↦ k + N
  have hφ : StrictMono φ := fun _ _ hlt ↦ Nat.add_lt_add_right hlt N
  let S : ℕ → Set E := fun n ↦ levelSet (f n) A
  have hconn : ∀ k, IsConnected ((S ∘ φ) k) := fun k ↦
    ⟨hN (k + N) (Nat.le_add_left _ _), hc _ _⟩
  have houter : Bornology.IsBounded (outerSetLimit (S ∘ φ)) :=
    (hb A).subset ((outerSetLimit_subsequence_subset hφ).trans (outer_levelSet_subset_of_epiConverges h A))
  have hno : NoSubsequenceEscapesToHorizon (S ∘ φ) := by
    intro ψ hψ
    exact ⟨x, innerSetLimit_subset_outerSetLimit _ (innerSetLimit_subset_subsequence hψ
      (innerSetLimit_subset_subsequence hφ hin))⟩
  obtain ⟨r, hr⟩ := eventually_subset_closedBall_of_connected_of_bounded_outerSetLimit hconn houter hno
  obtain ⟨M, hM⟩ := eventually_atTop.1 hr
  refine ⟨r, M + N, fun n hn y hy ↦ ?_⟩
  have hidx : n - N + N = n := by omega
  apply hM (n - N) (by omega)
  change f (n - N + N) y ≤ (A : EReal)
  rw [hidx]
  exact le_trans hy (EReal.coe_le_coe_iff.2 (le_max_left _ _))

end RW
