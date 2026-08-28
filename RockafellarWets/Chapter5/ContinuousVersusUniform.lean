/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 5: Continuous versus Uniform Convergence

Theorem 5.43: continuous convergence relative to `X` is the pointwise
localization of uniform convergence.

The book proves this by translating everything, through 5.42, into statements
about the scalar functions `hν(x) = min(d(u, Sν(x)), η)` and then quoting the
classical relationship between continuous and uniform convergence of
functions.  That route is not taken here.  Every notion involved already has
an `ε`-`ρ` *inclusion* form in this development --

* uniform convergence on `X` is Definition 5.41 itself;
* continuous convergence at `x̄` is `svConvergesContinuouslyWithinAt_iff`;
* continuity of `S` relative to `X` is 5.12 --

so the whole theorem is a matter of composing inclusions through a third set,
by `inter_closedBall_subset_thickening_trans`.  Each composition costs `ε/2`
on each side and `ε/2` of extra radius in the middle, which is why every
statement below is applied at radius `ρ + ε` before being used at radius `ρ`.
Nothing here needs 5.42.

Two of the three passages are pure composition.  The third, uniform
convergence on a compact `B ⊂ X`, is where compactness enters: continuous
convergence supplies a neighborhood at each point of `B` separately, and a
finite subcover turns those into one index beyond which the inclusions hold
at *every* point of `B` at once.  The book argues that step by contradiction
through a cluster point of escaping arguments; the subcover replaces it.

The last assertion of (b) -- that continuity of `S` is automatic when the `Sν`
are continuous relative to `X` and `X` is locally compact relative to itself --
is the same composition run three times instead of twice, `Sν(z)` and `Sν(x̄)`
being interposed between `S(z)` and `S(x̄)`.
-/

import RockafellarWets.Chapter5.GraphicalContinuousConvergence
import RockafellarWets.Chapter5.PerturbedMappings
import RockafellarWets.Chapter5.UniformSemicontinuity

open Filter Metric Set Topology

namespace RW

section Continuity

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E} {x : E}

/-- **Theorem 5.43**, the general assertion recorded after the statement:
continuous convergence to `S` at `x̄` relative to `X`, together with pointwise
convergence at the nearby points of `X`, forces `S` to be continuous at `x̄`
relative to `X`.

Both semicontinuity clauses are the same composition through `Sν(z)`: what
continuous convergence knows about `Sν(z)` and `S(x̄)` combines with what
pointwise convergence at `z` knows about `Sν(z)` and `S(z)`. -/
theorem svContinuousWithinAt_of_svConvergesContinuouslyWithinAt (hx : x ∈ X)
    (hc : SvConvergesContinuouslyWithinAt Sseq S X x)
    (hp : ∃ V ∈ nhds x, ∀ y ∈ X ∩ V, PointwiseConvergesAt Sseq S y) :
    SvContinuousWithinAt S X x := by
  obtain ⟨V₀, hV₀, hpw⟩ := hp
  have hclx : IsClosed (S x) := hc.isClosed_apply hx
  have hub := (svConvergesContinuouslyWithinAt_iff hx hclx).1 hc
  have hcl : ∀ y ∈ X ∩ V₀, IsClosed (S y) := by
    intro y hy
    rw [← (hpw y hy).2]
    exact isClosed_outerSetLimit _
  constructor
  · refine (svOscWithinAt_iff_exists_nhds_inter_closedBall_subset hclx).2
      fun ρ hρ ε hε ↦ ?_
    obtain ⟨V, hV, hN⟩ := hub (ε / 2) (by linarith) (ρ + ε) (by linarith)
    refine ⟨V ∩ V₀, inter_mem hV hV₀, fun z hz ↦ ?_⟩
    obtain ⟨n, hn, hnpw⟩ := (hN.and
      ((pkConverges_apply_iff (hcl z ⟨hz.1, hz.2.2⟩)).1 (hpw z ⟨hz.1, hz.2.2⟩)
        (ε / 2) (by linarith) ρ hρ)).exists
    have hstep := inter_closedBall_subset_thickening_trans
      (by linarith : ρ + ε / 2 ≤ ρ + ε) hnpw.2 (hn z ⟨hz.2.1, hz.1⟩).1
    rwa [add_halves] at hstep
  · refine (svIscWithinAt_iff_exists_nhds_inter_closedBall_subset hclx).2
      fun ρ hρ ε hε ↦ ?_
    obtain ⟨V, hV, hN⟩ := hub (ε / 2) (by linarith) ρ hρ
    refine ⟨V ∩ V₀, inter_mem hV hV₀, fun z hz ↦ ?_⟩
    obtain ⟨n, hn, hnpw⟩ := (hN.and
      ((pkConverges_apply_iff (hcl z ⟨hz.1, hz.2.2⟩)).1 (hpw z ⟨hz.1, hz.2.2⟩)
        (ε / 2) (by linarith) (ρ + ε) (by linarith))).exists
    have hstep := inter_closedBall_subset_thickening_trans
      (by linarith : ρ + ε / 2 ≤ ρ + ε) (hn z ⟨hz.2.1, hz.1⟩).2 hnpw.1
    rwa [add_halves] at hstep

/-- **Theorem 5.43**, (a) ⟹ the continuity half of (b).  Continuous
convergence relative to `X` contains pointwise convergence on `X`, taken along
constant sequences. -/
theorem SvConvergesContinuouslyOn.svContinuousOn
    (hc : SvConvergesContinuouslyOn Sseq S X) : SvContinuousOn S X := fun x hx ↦
  svContinuousWithinAt_of_svConvergesContinuouslyWithinAt hx (hc x hx)
    ⟨univ, univ_mem, fun y hy ↦ (hc y hy.1).pointwiseConvergesAt hy.1⟩

/-- **Theorem 5.43**, (a) ⟹ the uniform-convergence half of (b).

Continuous convergence supplies, at each point `z` of a compact `B ⊂ X`, a
neighborhood and an index beyond which `Sν(y)` and `S(z)` approximate each
other for `y ∈ X` in that neighborhood; the continuity of `S` just established
supplies a neighborhood on which `S(y)` and `S(z)` do the same.  A finite
subcover of `B` collapses those local data into one index beyond which the
composed inclusions hold at every point of `B` at once -- which is where
compactness of `B` is used, and it replaces the book's argument by
contradiction through a cluster point of escaping arguments. -/
theorem SvConvergesContinuouslyOn.svConvergesUniformlyOn
    (hc : SvConvergesContinuouslyOn Sseq S X) {B : Set E} (hBX : B ⊆ X)
    (hB : IsCompact B) : SvConvergesUniformlyOn Sseq S B := by
  classical
  have hcont := hc.svContinuousOn
  intro ε hε ρ hρ
  have hpick : ∀ z ∈ B, ∃ U ∈ nhds z,
      (∀ᶠ n in atTop, ∀ y ∈ U ∩ X,
        Sseq n y ∩ closedBall 0 (ρ + ε) ⊆ thickening (ε / 2) (S z) ∧
          S z ∩ closedBall 0 (ρ + ε) ⊆ thickening (ε / 2) (Sseq n y)) ∧
      (∀ y ∈ X ∩ U,
        S y ∩ closedBall 0 (ρ + ε) ⊆ thickening (ε / 2) (S z) ∧
          S z ∩ closedBall 0 (ρ + ε) ⊆ thickening (ε / 2) (S y)) := by
    intro z hz
    have hzX := hBX hz
    have hclz : IsClosed (S z) := (hc z hzX).isClosed_apply hzX
    obtain ⟨V, hV, hN⟩ :=
      (svConvergesContinuouslyWithinAt_iff hzX hclz).1 (hc z hzX)
        (ε / 2) (by linarith) (ρ + ε) (by linarith)
    obtain ⟨W₁, hW₁, hosc⟩ :=
      (svOscWithinAt_iff_exists_nhds_inter_closedBall_subset hclz).1
        (hcont z hzX).1 (ρ + ε) (by linarith) (ε / 2) (by linarith)
    obtain ⟨W₂, hW₂, hisc⟩ :=
      (svIscWithinAt_iff_exists_nhds_inter_closedBall_subset hclz).1
        (hcont z hzX).2 (ρ + ε) (by linarith) (ε / 2) (by linarith)
    exact ⟨V ∩ (W₁ ∩ W₂), inter_mem hV (inter_mem hW₁ hW₂),
      hN.mono fun n hn y hy ↦ hn y ⟨hy.1.1, hy.2⟩,
      fun y hy ↦ ⟨hosc y ⟨hy.1, hy.2.2.1⟩, hisc y ⟨hy.1, hy.2.2.2⟩⟩⟩
  choose! U hU hUn hUS using hpick
  obtain ⟨t, htB, htcover⟩ := hB.elim_nhds_subcover U hU
  have hall : ∀ᶠ n in atTop, ∀ z ∈ t, ∀ y ∈ U z ∩ X,
      Sseq n y ∩ closedBall 0 (ρ + ε) ⊆ thickening (ε / 2) (S z) ∧
        S z ∩ closedBall 0 (ρ + ε) ⊆ thickening (ε / 2) (Sseq n y) :=
    (eventually_all_finset t).2 fun z hz ↦ hUn z (htB z hz)
  filter_upwards [hall] with n hn y hy
  obtain ⟨z, hz, hyU⟩ := mem_iUnion₂.1 (htcover hy)
  have hmem : y ∈ U z ∩ X := ⟨hyU, hBX hy⟩
  have hzB : z ∈ B := htB z hz
  have hosc := inter_closedBall_subset_thickening_trans
    (by linarith : ρ + ε / 2 ≤ ρ + ε)
    (inter_closedBall_subset_of_le (by linarith) (hn z hz y hmem).1)
    (hUS z hzB y ⟨hBX hy, hyU⟩).2
  have hisc := inter_closedBall_subset_thickening_trans
    (by linarith : ρ + ε / 2 ≤ ρ + ε)
    (inter_closedBall_subset_of_le (by linarith) (hUS z hzB y ⟨hBX hy, hyU⟩).1)
    (hn z hz y hmem).2
  rw [add_halves] at hosc hisc
  exact ⟨hosc, hisc⟩

/-- **Theorem 5.43**, (b) ⟹ (a).

The compact set is the book's: an approaching sequence together with its
limit.  On it the convergence is uniform, and composing that with the
continuity of `S` at `x̄` -- through the intermediate set `S(xν)` -- gives the
two inclusions between `Sν(xν)` and `S(x̄)` that 4.10 asks for. -/
theorem svConvergesContinuouslyOn_of_svConvergesUniformlyOn
    (hu : ∀ B ⊆ X, IsCompact B → SvConvergesUniformlyOn Sseq S B)
    (hcont : SvContinuousOn S X) : SvConvergesContinuouslyOn Sseq S X := by
  intro x hx y hyX hy
  have hclx : IsClosed (S x) := (hcont x hx).1.isClosed hx
  refine (pkConverges_iff_eventually_inclusions hclx).2 fun ε hε ρ hρ ↦ ?_
  have hBX : insert x (range y) ⊆ X := by
    rintro z hz
    rcases hz with rfl | ⟨n, rfl⟩
    · exact hx
    · exact hyX n
  obtain ⟨W₁, hW₁, hosc⟩ :=
    (svOscWithinAt_iff_exists_nhds_inter_closedBall_subset hclx).1
      (hcont x hx).1 (ρ + ε) (by linarith) (ε / 2) (by linarith)
  obtain ⟨W₂, hW₂, hisc⟩ :=
    (svIscWithinAt_iff_exists_nhds_inter_closedBall_subset hclx).1
      (hcont x hx).2 (ρ + ε) (by linarith) (ε / 2) (by linarith)
  filter_upwards [hu _ hBX hy.isCompact_insert_range (ε / 2) (by linarith)
      (ρ + ε) (by linarith),
    hy.eventually_mem (inter_mem hW₁ hW₂)] with n hn hyn
  have hmem : y n ∈ insert x (range y) := mem_insert_of_mem _ ⟨n, rfl⟩
  have h₁ := inter_closedBall_subset_thickening_trans
    (by linarith : ρ + ε / 2 ≤ ρ + ε)
    (inter_closedBall_subset_of_le (by linarith) (hn (y n) hmem).1)
    (hosc (y n) ⟨hyX n, hyn.1⟩)
  have h₂ := inter_closedBall_subset_thickening_trans
    (by linarith : ρ + ε / 2 ≤ ρ + ε)
    (inter_closedBall_subset_of_le (by linarith) (hisc (y n) ⟨hyX n, hyn.2⟩))
    (hn (y n) hmem).2
  rw [add_halves] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- **Theorem 5.43**: continuous convergence relative to `X` is uniform
convergence on all compact subsets of `X` together with continuity of the
limit relative to `X`. -/
theorem svConvergesContinuouslyOn_iff :
    SvConvergesContinuouslyOn Sseq S X ↔
      (∀ B ⊆ X, IsCompact B → SvConvergesUniformlyOn Sseq S B) ∧
        SvContinuousOn S X :=
  ⟨fun h ↦ ⟨fun _ hBX hB ↦ h.svConvergesUniformlyOn hBX hB, h.svContinuousOn⟩,
    fun h ↦ svConvergesContinuouslyOn_of_svConvergesUniformlyOn h.1 h.2⟩

end Continuity

section AutomaticContinuity

variable {E F : Type*} [PseudoMetricSpace E]
variable [NormedAddCommGroup F] [ProperSpace F]
variable {Sseq : ℕ → E → Set F} {S : E → Set F} {X : Set E}

/-- **Theorem 5.43**, last sentence of (b): continuity of the limit is
automatic when the `Sν` are continuous relative to `X` and every point of `X`
has a compact neighborhood relative to `X`.

This is the same composition, run three times: `S(z)` reaches `Sν(z)` by the
uniform convergence on the compact neighborhood, `Sν(z)` reaches `Sν(x̄)` by
the continuity of that one `Sν`, and `Sν(x̄)` reaches `S(x̄)` by the uniform
convergence again -- so a single index chosen once serves the whole argument.

The printed statement omits the closed-valuedness of `S`, which is the
standing assumption of 5.42 and is genuinely needed:
`svOscOn_not_automatic_without_closedValued` is a *constant* sequence
`Sν ≡ [0, 1]`, continuous relative to `IR`, converging uniformly on all of
`IR` to the constant mapping `S ≡ (0, 1)`, which is not outer semicontinuous.
The `ε`-inclusions of Definition 5.41 cannot see the difference between a set
and its closure, so no argument from them alone can produce closed values. -/
theorem svContinuousOn_of_svConvergesUniformlyOn
    (hSn : ∀ n, SvContinuousOn (Sseq n) X)
    (hu : ∀ B ⊆ X, IsCompact B → SvConvergesUniformlyOn Sseq S B)
    (hloc : ∀ z ∈ X, ∃ B ⊆ X, IsCompact B ∧ B ∈ nhdsWithin z X)
    (hclosed : ∀ z ∈ X, IsClosed (S z)) : SvContinuousOn S X := by
  intro x hx
  obtain ⟨B, hBX, hBc, hBnhds⟩ := hloc x hx
  obtain ⟨V₀, hV₀, hV₀sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hBnhds
  have hxB : x ∈ B := mem_of_mem_nhdsWithin hx hBnhds
  constructor
  · refine (svOscWithinAt_iff_exists_nhds_inter_closedBall_subset (hclosed x hx)).2
      fun ρ hρ ε hε ↦ ?_
    obtain ⟨n, hn⟩ :=
      (hu B hBX hBc (ε / 3) (by linarith) (ρ + ε) (by linarith)).exists
    obtain ⟨V, hV, hoscn⟩ :=
      (svOscWithinAt_iff_exists_nhds_inter_closedBall_subset
        ((hSn n x hx).1.isClosed hx)).1 (hSn n x hx).1
        (ρ + ε / 3) (by linarith) (ε / 3) (by linarith)
    refine ⟨V ∩ V₀, inter_mem hV hV₀, fun z hz ↦ ?_⟩
    have hzB : z ∈ B := hV₀sub ⟨hz.2.2, hz.1⟩
    have hstep := inter_closedBall_subset_thickening_trans
      (le_refl (ρ + ε / 3))
      (inter_closedBall_subset_of_le (by linarith) (hn z hzB).2)
      (hoscn z ⟨hz.1, hz.2.1⟩)
    have hstep' := inter_closedBall_subset_thickening_trans
      (by linarith : ρ + (ε / 3 + ε / 3) ≤ ρ + ε / 3 + ε / 3) hstep
      (inter_closedBall_subset_of_le (by linarith) (hn x hxB).1)
    have hsum : ε / 3 + ε / 3 + ε / 3 = ε := by ring
    rwa [hsum] at hstep'
  · refine (svIscWithinAt_iff_exists_nhds_inter_closedBall_subset (hclosed x hx)).2
      fun ρ hρ ε hε ↦ ?_
    obtain ⟨n, hn⟩ :=
      (hu B hBX hBc (ε / 3) (by linarith) (ρ + ε) (by linarith)).exists
    obtain ⟨V, hV, hiscn⟩ :=
      (svIscWithinAt_iff_exists_nhds_inter_closedBall_subset
        ((hSn n x hx).1.isClosed hx)).1 (hSn n x hx).2
        (ρ + ε / 3) (by linarith) (ε / 3) (by linarith)
    refine ⟨V ∩ V₀, inter_mem hV hV₀, fun z hz ↦ ?_⟩
    have hzB : z ∈ B := hV₀sub ⟨hz.2.2, hz.1⟩
    have hstep := inter_closedBall_subset_thickening_trans
      (le_refl (ρ + ε / 3))
      (inter_closedBall_subset_of_le (by linarith) (hn x hxB).2)
      (hiscn z ⟨hz.1, hz.2.1⟩)
    have hstep' := inter_closedBall_subset_thickening_trans
      (by linarith : ρ + (ε / 3 + ε / 3) ≤ ρ + ε / 3 + ε / 3) hstep
      (inter_closedBall_subset_of_le (by linarith) (hn z hzB).1)
    have hsum : ε / 3 + ε / 3 + ε / 3 = ε := by ring
    rwa [hsum] at hstep'

end AutomaticContinuity

section ClosedValuedNeeded

/-- The two constant mappings behind the witness below converge uniformly on
every set: each inclusion of Definition 5.41 relates a set to an
`ε`-thickening, and a thickening does not distinguish `(0, 1)` from its
closure `[0, 1]`. -/
theorem svConvergesUniformlyOn_icc_ioo (B : Set ℝ) :
    SvConvergesUniformlyOn (fun (_ : ℕ) (_ : ℝ) ↦ Icc (0 : ℝ) 1)
      (fun _ ↦ Ioo (0 : ℝ) 1) B := by
  intro ε hε ρ _
  filter_upwards with n z _
  refine ⟨fun v hv ↦ closure_subset_thickening hε _ ?_, fun v hv ↦
    self_subset_thickening hε _ (Ioo_subset_Icc_self hv.1)⟩
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  exact hv.1

/-- The closed-valuedness dropped from the last sentence of 5.43(b), and from
both clauses of 5.46, is genuinely needed.

Take the *constant* sequence `Sν ≡ [0, 1]` on `IR`, which is continuous and in
particular outer semicontinuous, and the constant mapping `S ≡ (0, 1)`.  Every
point of `IR` has a compact neighborhood, and the convergence is uniform on
all of `IR`, hence on every compact subset.  Yet `S` is not outer
semicontinuous anywhere, its values not being closed -- so it is not
continuous either, and `Sν` does not converge graphically to it, the graphical
outer limit of the constant graphs being their closure.

The reason is structural: the `ε`-inclusions of Definition 5.41 cannot
distinguish a set from its closure, so no argument from them alone can produce
closed values.  The book's own proof of 5.46(a) uses closed-valuedness at its
last step, concluding `ū ∈ S(x̄)` from `d(ū, S(x̄)) ≤ 2ε` for all `ε > 0`. -/
theorem svOscOn_not_automatic_without_closedValued :
    (∀ _ : ℕ, SvContinuousOn (fun _ : ℝ ↦ Icc (0 : ℝ) 1) univ) ∧
      SvConvergesUniformlyOn (fun (_ : ℕ) (_ : ℝ) ↦ Icc (0 : ℝ) 1)
        (fun _ ↦ Ioo (0 : ℝ) 1) univ ∧
      (∀ B ⊆ (univ : Set ℝ), IsCompact B →
        SvConvergesUniformlyOn (fun (_ : ℕ) (_ : ℝ) ↦ Icc (0 : ℝ) 1)
          (fun _ ↦ Ioo (0 : ℝ) 1) B) ∧
      (∀ z ∈ (univ : Set ℝ), ∃ B ⊆ (univ : Set ℝ), IsCompact B ∧
        B ∈ nhdsWithin z (univ : Set ℝ)) ∧
      ¬ SvOscOn (fun _ : ℝ ↦ Ioo (0 : ℝ) 1) univ := by
  refine ⟨fun _ x _ ↦ svContinuousWithinAt_univ.2
      ⟨svOscAt_const isClosed_Icc x, svIscAt_const _ x⟩,
    svConvergesUniformlyOn_icc_ioo _, fun B _ _ ↦ svConvergesUniformlyOn_icc_ioo B,
    fun z _ ↦ ⟨Icc (z - 1) (z + 1), subset_univ _, isCompact_Icc, by
      rw [nhdsWithin_univ]
      exact Icc_mem_nhds (by linarith) (by linarith)⟩, ?_⟩
  intro h
  have hcl : IsClosed (Ioo (0 : ℝ) 1) :=
    SvOscWithinAt.isClosed (S := fun _ : ℝ ↦ Ioo (0 : ℝ) 1) (x := (0 : ℝ))
      (mem_univ 0) (h 0 (mem_univ 0))
  have h0 : (0 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    rw [← hcl.closure_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_refl 0, by norm_num⟩
  exact absurd h0.1 (lt_irrefl 0)

end ClosedValuedNeeded

end RW
