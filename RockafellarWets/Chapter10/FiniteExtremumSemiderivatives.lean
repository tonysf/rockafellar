/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Semiderivatives of finite maxima and minima
-/
import RockafellarWets.Chapter10.SemiderivativeCalculus
import RockafellarWets.Chapter7.SemidifferentiabilityCharacterizations

open Set Filter Topology Classical
open scoped BigOperators

noncomputable section
namespace RW
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite directional semidifferentiability gives continuity along every
moving ray at that direction. -/
theorem HasDirectionalSemiderivative.path_tendsto {f : E → F} {x w : E} {u : F}
    (hf : HasDirectionalSemiderivative f x w u) :
    Tendsto (fun p : ℝ × E ↦ f (x + p.1 • p.2)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 (f x)) := by
  have ht : Tendsto (Prod.fst : ℝ × E → ℝ) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) (𝓝 0) :=
    tendsto_fst.mono_right nhdsWithin_le_nhds
  have h := (ht.smul hf).add_const (f x)
  simp only [zero_smul,zero_add] at h
  apply h.congr'
  filter_upwards [tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p ht
  simp [smul_smul,mul_inv_cancel₀ (ne_of_gt ht)]

def finiteMaximum {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → E → ℝ) (x : E) : ℝ :=
  s.sup' hs (fun i ↦ f i x)

def activeMaximum {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → E → ℝ) (x : E) : Finset ι :=
  s.filter (fun i ↦ f i x = RW.finiteMaximum s hs f x)

theorem activeMaximum_nonempty {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → E → ℝ) (x : E) : (activeMaximum s hs f x).Nonempty := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' hs (fun i ↦ f i x)
  exact ⟨i,Finset.mem_filter.mpr ⟨hi,he.symm⟩⟩

/-- **Exercise 10.27(c)**: only the active indices enter the directional
semiderivative of a finite maximum. -/
theorem HasDirectionalSemiderivative.finiteMaximum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → E → ℝ} {x w : E} {d : ι → ℝ}
    (hf : ∀ i ∈ s, HasDirectionalSemiderivative (f i) x w (d i)) :
    HasDirectionalSemiderivative (RW.finiteMaximum s hs f) x w
      ((activeMaximum s hs f x).sup' (activeMaximum_nonempty s hs f x) d) := by
  let I := activeMaximum s hs f x
  have hI := activeMaximum_nonempty s hs f x
  obtain ⟨i₀,hi₀⟩ := activeMaximum_nonempty s hs f x
  have hi₀s := (Finset.mem_filter.mp hi₀).1
  have hi₀eq := (Finset.mem_filter.mp hi₀).2
  have hevent : ∀ᶠ p : ℝ × E in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      ∀ i ∈ s, i ∉ I → f i (x + p.1 • p.2) < f i₀ (x + p.1 • p.2) := by
    apply (Filter.eventually_all_finset s).mpr
    intro i hi
    by_cases hia : i ∈ I
    · exact .of_forall fun _ hn ↦ (hn hia).elim
    · have hlt : f i x < f i₀ x := by
        rw [hi₀eq]
        apply lt_of_le_of_ne (Finset.le_sup' (fun j ↦ f j x) hi)
        intro he
        exact hia (Finset.mem_filter.mpr ⟨hi,he⟩)
      filter_upwards [((hf i hi).path_tendsto).eventually_lt ((hf i₀ hi₀s).path_tendsto) hlt] with p hp _
      exact hp
  have hmax : ∀ᶠ p : ℝ × E in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w,
      RW.finiteMaximum s hs f (x + p.1 • p.2) = I.sup' hI (fun i ↦ f i (x + p.1 • p.2)) := by
    filter_upwards [hevent] with p hp
    unfold RW.finiteMaximum
    apply le_antisymm
    · apply Finset.sup'_le
      intro i hi
      by_cases hia : i ∈ I
      · exact Finset.le_sup' (fun j ↦ f j (x + p.1 • p.2)) hia
      · exact (hp i hi hia).le.trans (Finset.le_sup' (fun j ↦ f j (x + p.1 • p.2)) hi₀)
    · exact Finset.sup'_le hI _ fun i hi ↦ Finset.le_sup' (fun j ↦ f j (x + p.1 • p.2)) (Finset.mem_filter.mp hi).1
  have hlim := Filter.Tendsto.finset_sup'_nhds_apply hI
    (fun i hi ↦ hf i (Finset.mem_filter.mp hi).1)
  apply hlim.congr'
  filter_upwards [hmax,tendsto_fst.eventually (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with p hp ht
  change I.sup' hI (fun i ↦ p.1⁻¹ * (f i (x + p.1 • p.2) - f i x)) = _
  simp only [smul_eq_mul]
  rw [hp]
  have hmono : Monotone (fun a : ℝ ↦ p.1⁻¹ * (a - RW.finiteMaximum s hs f x)) :=
    fun a b hab ↦ mul_le_mul_of_nonneg_left (sub_le_sub_right hab _) (inv_nonneg.mpr ht.le)
  rw [Finset.comp_sup'_eq_sup'_comp hI (f := fun i ↦ f i (x + p.1 • p.2))
    (fun a : ℝ ↦ p.1⁻¹ * (a - RW.finiteMaximum s hs f x)) (fun a b ↦ hmono.map_sup a b)]
  apply Finset.sup'_congr hI rfl
  intro i hi
  simp only [Function.comp_def,smul_eq_mul]
  rw [(Finset.mem_filter.mp hi).2]

/-- The original scalar predicate from Definition 7.20 is equivalent to
existence of a finite vector semiderivative in every direction. -/
theorem semidifferentiableAt_coe_iff {f : E → ℝ} {x : E} :
    SemidifferentiableAt (fun y ↦ (f y : EReal)) x ↔
      ∀ w, ∃ d : ℝ, HasDirectionalSemiderivative f x w d := by
  constructor
  · intro h
    obtain ⟨d,_,_,hd⟩ := h.exists_semiderivative
    exact fun w ↦ ⟨d w,hasDirectionalSemiderivative_iff.mpr (hd w).1⟩
  · intro h w
    obtain ⟨d,hd⟩ := h w
    exact ⟨d,hasDirectionalSemiderivative_iff.mp hd⟩

/-- **Exercise 10.27(a)**, arbitrary finite real linear combinations. -/
theorem SemidifferentiableAt.linearCombination {ι : Type*} (s : Finset ι)
    {f : ι → E → ℝ} {x : E} (a : ι → ℝ)
    (hf : ∀ i ∈ s, SemidifferentiableAt (fun y ↦ (f i y : EReal)) x) :
    SemidifferentiableAt (fun y ↦ ((∑ i ∈ s, a i * f i y : ℝ) : EReal)) x := by
  classical
  apply semidifferentiableAt_coe_iff.mpr
  intro w
  have hd : ∀ i ∈ s, ∃ d : ℝ, HasDirectionalSemiderivative (f i) x w d :=
    fun i hi ↦ semidifferentiableAt_coe_iff.mp (hf i hi) w
  choose d hd using hd
  let ds (i : ι) : ℝ := if hi : i ∈ s then d i hi else 0
  refine ⟨∑ i ∈ s, a i * ds i,?_⟩
  exact HasDirectionalSemiderivative.sum s fun i hi ↦ by simpa [ds,hi] using (hd i hi).const_smul (a i)

/-- **Exercise 10.27(c)**, semidifferentiability of a finite maximum. -/
theorem SemidifferentiableAt.finiteMaximum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → E → ℝ} {x : E}
    (hf : ∀ i ∈ s, SemidifferentiableAt (fun y ↦ (f i y : EReal)) x) :
    SemidifferentiableAt (fun y ↦ (RW.finiteMaximum s hs f y : EReal)) x := by
  apply semidifferentiableAt_coe_iff.mpr
  intro w
  have hd : ∀ i ∈ s, ∃ d : ℝ, HasDirectionalSemiderivative (f i) x w d :=
    fun i hi ↦ semidifferentiableAt_coe_iff.mp (hf i hi) w
  choose d hd using hd
  let ds (i : ι) : ℝ := if hi : i ∈ s then d i hi else 0
  exact ⟨_,HasDirectionalSemiderivative.finiteMaximum s hs (d := ds) (fun i hi ↦ by simpa [ds,hi] using hd i hi)⟩

/-- The finite minimum, written in its equivalent negated-maximum form. -/
def finiteMinimum {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → E → ℝ) (x : E) : ℝ :=
  -RW.finiteMaximum s hs (fun i y ↦ -f i y) x

theorem finiteMinimum_eq_inf' {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → E → ℝ) (x : E) : finiteMinimum s hs f x = s.inf' hs (fun i ↦ f i x) := by
  simpa [finiteMinimum,RW.finiteMaximum,Function.comp_def] using
    (Finset.comp_sup'_eq_sup'_comp (γ := OrderDual ℝ) hs (f := fun i ↦ -f i x)
      (fun a : ℝ ↦ -a) (fun a b ↦ by
        change -(max a b) = min (-a) (-b)
        rcases le_total a b with h | h
        · rw [max_eq_right h,min_eq_right (neg_le_neg h)]
        · rw [max_eq_left h,min_eq_left (neg_le_neg h)]))

/-- **Exercise 10.27(c)**, the exact minimum rule. The displayed active set
consists precisely of the indices attaining the minimum at the base point. -/
theorem HasDirectionalSemiderivative.finiteMinimum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → E → ℝ} {x w : E} {d : ι → ℝ}
    (hf : ∀ i ∈ s, HasDirectionalSemiderivative (f i) x w (d i)) :
    HasDirectionalSemiderivative (RW.finiteMinimum s hs f) x w
      (-((activeMaximum s hs (fun i y ↦ -f i y) x).sup'
        (activeMaximum_nonempty s hs (fun i y ↦ -f i y) x) (fun i ↦ -d i))) := by
  have hn : ∀ i ∈ s, HasDirectionalSemiderivative (fun y ↦ -f i y) x w (-d i) :=
    fun i hi ↦ by simpa using (hf i hi).const_smul (-1)
  simpa [RW.finiteMinimum] using
    (HasDirectionalSemiderivative.finiteMaximum s hs hn).const_smul (-1)

theorem SemidifferentiableAt.finiteMinimum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {f : ι → E → ℝ} {x : E}
    (hf : ∀ i ∈ s, SemidifferentiableAt (fun y ↦ (f i y : EReal)) x) :
    SemidifferentiableAt (fun y ↦ (RW.finiteMinimum s hs f y : EReal)) x := by
  apply semidifferentiableAt_coe_iff.mpr
  intro w
  have hd : ∀ i ∈ s, ∃ d : ℝ, HasDirectionalSemiderivative (f i) x w d :=
    fun i hi ↦ semidifferentiableAt_coe_iff.mp (hf i hi) w
  choose d hd using hd
  let ds (i : ι) : ℝ := if hi : i ∈ s then d i hi else 0
  exact ⟨_,HasDirectionalSemiderivative.finiteMinimum s hs (d := ds)
    (fun i hi ↦ by simpa [ds,hi] using hd i hi)⟩

/-- **Exercise 10.27(b)** in the original scalar semidifferentiability predicate. -/
theorem SemidifferentiableAt.comp_hasFDerivAt {g : F → ℝ} {f : E → F} {x : E}
    {A : E →L[ℝ] F} (hg : SemidifferentiableAt (fun y ↦ (g y : EReal)) (f x))
    (hf : HasFDerivAt f A x) :
    SemidifferentiableAt (fun y ↦ (g (f y) : EReal)) x := by
  apply semidifferentiableAt_coe_iff.mpr
  intro w
  obtain ⟨d,hd⟩ := semidifferentiableAt_coe_iff.mp hg (A w)
  exact ⟨d,hd.comp (hf.hasDirectionalSemiderivative w)⟩

/-- A semidifferentiable scalar function has its finite directional
semiderivative given by `df(x)(w).toReal`. -/
theorem SemidifferentiableAt.hasDirectionalSemiderivative {f : E → ℝ} {x : E}
    (hf : SemidifferentiableAt (fun y ↦ (f y : EReal)) x) (w : E) :
    HasDirectionalSemiderivative f x w (subderivative (fun y ↦ (f y : EReal)) x w).toReal := by
  obtain ⟨d,hd⟩ := semidifferentiableAt_coe_iff.mp hf w
  simpa [hd.subderivative_eq] using hd

/-- **Exercise 10.27(b)**, the printed equality of subderivatives. -/
theorem subderivative_comp_of_semidifferentiable {g : F → ℝ} {f : E → F} {x w : E}
    {A : E →L[ℝ] F} (hg : SemidifferentiableAt (fun y ↦ (g y : EReal)) (f x))
    (hf : HasFDerivAt f A x) :
    subderivative (fun y ↦ (g (f y) : EReal)) x w =
      subderivative (fun y ↦ (g y : EReal)) (f x) (A w) := by
  obtain ⟨d,hd⟩ := semidifferentiableAt_coe_iff.mp hg (A w)
  exact (hd.comp (hf.hasDirectionalSemiderivative w)).subderivative_eq.trans hd.subderivative_eq.symm

/-- **Exercise 10.27(a)**, the exact finite linear-combination formula. -/
theorem subderivative_linearCombination {ι : Type*} (s : Finset ι)
    {f : ι → E → ℝ} {x w : E} (a : ι → ℝ)
    (hf : ∀ i ∈ s, SemidifferentiableAt (fun y ↦ (f i y : EReal)) x) :
    subderivative (fun y ↦ ((∑ i ∈ s, a i * f i y : ℝ) : EReal)) x w =
      ((∑ i ∈ s, a i * (subderivative (fun y ↦ (f i y : EReal)) x w).toReal : ℝ) : EReal) := by
  exact (HasDirectionalSemiderivative.sum s fun i hi ↦
    (hf i hi).hasDirectionalSemiderivative w |>.const_smul (a i)).subderivative_eq

end RW
end
