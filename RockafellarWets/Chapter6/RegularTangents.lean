/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chapter 6: Regular Tangent Cones

Definition 6.25 and Theorem 6.26.  The regular tangent cone is kept in the
filter-native form of formula 6(15): a simultaneous inner limit as both the
base point approaches through the set and the positive scale tends to zero.
-/

import RockafellarWets.Chapter6.ChangeOfCoordinates
import RockafellarWets.Chapter6.NormalCones

open Filter Metric Set Topology

namespace RW

section RegularTangents

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Definition 6.25**, formula 6(15): the regular tangent cone is the joint
inner limit of the magnified difference sets as the base point approaches
through `C` and the positive scale tends to zero. -/
def regularTangentCone (C : Set E) (x : E) : Set E :=
  innerSetLimitAlong
    ((nhdsWithin x C) ×ˢ (nhdsWithin 0 (Ioi (0 : ℝ))))
    (fun p : E × ℝ ↦ blowUp C p.1 p.2)

/-- The neighborhood/filter reading of Definition 6.25. -/
theorem mem_regularTangentCone {C : Set E} {x w : E} :
    w ∈ regularTangentCone C x ↔
      ∀ V ∈ nhds w,
        ∀ᶠ p in (nhdsWithin x C) ×ˢ (nhdsWithin 0 (Ioi (0 : ℝ))),
          (blowUp C p.1 p.2 ∩ V).Nonempty :=
  Iff.rfl

/-- The exact sequential reading printed in Definition 6.25.  Thus the
filter-native joint inner limit really says that for every positive scale
sequence tending to zero and every base sequence approaching through `C`, one
can select points of `C` whose corresponding difference quotients tend to
`w`. -/
theorem mem_regularTangentCone_iff_forall_sequences {C : Set E} {x w : E}
    (hx : x ∈ C) :
    w ∈ regularTangentCone C x ↔
      ∀ (τs : ℕ → ℝ) (xbars : ℕ → E),
        (∀ n, 0 < τs n) → Tendsto τs atTop (nhds 0) →
        (∀ n, xbars n ∈ C) → Tendsto xbars atTop (nhds x) →
        ∃ xs : ℕ → E, (∀ n, xs n ∈ C) ∧ Tendsto xs atTop (nhds x) ∧
          Tendsto (fun n ↦ (τs n)⁻¹ • (xs n - xbars n)) atTop (nhds w) := by
  classical
  constructor
  · intro hw τs xbars hτpos hτ0 hxbarC hxbarto
    have hp : Tendsto (fun n ↦ (xbars n, τs n)) atTop
        ((nhdsWithin x C) ×ˢ (nhdsWithin 0 (Ioi (0 : ℝ)))) :=
      (tendsto_nhdsWithin_of_forall_mem hxbarC hxbarto).prodMk
        (tendsto_nhdsWithin_of_forall_mem hτpos hτ0)
    have hinner : w ∈ innerSetLimit
        (fun n ↦ blowUp C (xbars n) (τs n)) :=
      innerSetLimitAlong_subset_innerSetLimit_comp hp hw
    obtain ⟨us, hus, husto⟩ := mem_innerSetLimit_iff_exists_seq.1 hinner
    let us' : ℕ → E := fun n ↦
      if us n ∈ blowUp C (xbars n) (τs n) then us n
      else (τs n)⁻¹ • (x - xbars n)
    have hus'all : ∀ n, us' n ∈ blowUp C (xbars n) (τs n) := by
      intro n
      by_cases hn : us n ∈ blowUp C (xbars n) (τs n)
      · change (if us n ∈ blowUp C (xbars n) (τs n) then us n
            else (τs n)⁻¹ • (x - xbars n)) ∈ blowUp C (xbars n) (τs n)
        rw [if_pos hn]
        exact hn
      · change (if us n ∈ blowUp C (xbars n) (τs n) then us n
            else (τs n)⁻¹ • (x - xbars n)) ∈ blowUp C (xbars n) (τs n)
        rw [if_neg hn]
        exact ⟨x, hx, rfl⟩
    have husevent : us' =ᶠ[atTop] us := hus.mono fun n hn ↦ by
      change (if us n ∈ blowUp C (xbars n) (τs n) then us n
        else (τs n)⁻¹ • (x - xbars n)) = us n
      rw [if_pos hn]
    have hus'to : Tendsto us' atTop (nhds w) := husto.congr' husevent.symm
    choose xs hxsC hxsquot using fun n ↦ (mem_blowUp.1 (hus'all n))
    have hquot : Tendsto (fun n ↦ (τs n)⁻¹ • (xs n - xbars n))
        atTop (nhds w) := by
      simpa only [hxsquot] using hus'to
    have hdiff : Tendsto (fun n ↦ xs n - xbars n) atTop (nhds (0 : E)) := by
      have h := hτ0.smul hquot
      rw [zero_smul] at h
      have heq : ∀ n, τs n • ((τs n)⁻¹ • (xs n - xbars n)) =
          xs n - xbars n := fun n ↦ by
        rw [smul_smul, mul_inv_cancel₀ (hτpos n).ne', one_smul]
      simpa only [heq] using h
    have hxsto : Tendsto xs atTop (nhds x) := by
      have h := hdiff.add hxbarto
      simpa only [sub_add_cancel, zero_add] using h
    exact ⟨xs, hxsC, hxsto, hquot⟩
  · intro hseq
    by_contra hw
    obtain ⟨p, hpto, hnot⟩ := exists_seq_not_mem_outerSetLimit hw
    obtain ⟨xbars, hxbarC, hxbarto, hxbareq⟩ :=
      exists_seq_mem_of_tendsto_nhdsWithin hx hpto.fst
    have hτwithin := tendsto_nhdsWithin_iff.1 hpto.snd
    let τs : ℕ → ℝ := fun n ↦ if 0 < (p n).2 then (p n).2 else 1
    have hτpos : ∀ n, 0 < τs n := by
      intro n
      by_cases hn : 0 < (p n).2
      · simp [τs, hn]
      · simp [τs, hn]
    have hτeq : τs =ᶠ[atTop] fun n ↦ (p n).2 := by
      filter_upwards [hτwithin.2] with n hn
      have hn' : 0 < (p n).2 := hn
      change (if 0 < (p n).2 then (p n).2 else 1) = (p n).2
      rw [if_pos hn']
    have hτto : Tendsto τs atTop (nhds 0) :=
      hτwithin.1.congr' hτeq.symm
    obtain ⟨xs, hxsC, -, hq⟩ :=
      hseq τs xbars hτpos hτto hxbarC hxbarto
    apply hnot
    apply innerSetLimit_subset_outerSetLimit _
    refine mem_innerSetLimit_iff_exists_seq.2 ⟨
      fun n ↦ (τs n)⁻¹ • (xs n - xbars n), ?_, hq⟩
    filter_upwards [hxbareq, hτeq] with n hxn hτn
    rw [hxn, hτn]
    exact ⟨xs n, hxsC n, rfl⟩

/-- The regular tangent cone is closed, since it is an inner set limit. -/
theorem isClosed_regularTangentCone (C : Set E) (x : E) :
    IsClosed (regularTangentCone C x) :=
  isClosed_innerSetLimitAlong _ _

/-- The zero vector is a regular tangent at every point of `C`. -/
theorem zero_mem_regularTangentCone {C : Set E} {x : E} (hx : x ∈ C) :
    (0 : E) ∈ regularTangentCone C x := by
  rw [mem_regularTangentCone_iff_forall_sequences hx]
  intro τs xbars _ _ hxbarC hxbarto
  refine ⟨xbars, hxbarC, hxbarto, ?_⟩
  simp

/-- The regular tangent cone is a cone. -/
theorem isCone_regularTangentCone {C : Set E} {x : E} (hx : x ∈ C) :
    IsCone (regularTangentCone C x) := by
  refine ⟨zero_mem_regularTangentCone hx, ?_⟩
  intro w hw c hc
  rw [mem_regularTangentCone_iff_forall_sequences hx] at hw ⊢
  intro τs xbars hτpos hτ0 hxbarC hxbarto
  have hcτto : Tendsto (fun n ↦ c * τs n) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hτ0
  obtain ⟨xs, hxsC, hxsto, hq⟩ :=
    hw (fun n ↦ c * τs n) xbars (fun n ↦ mul_pos hc (hτpos n))
      hcτto hxbarC hxbarto
  refine ⟨xs, hxsC, hxsto, ?_⟩
  have heq : ∀ n, (τs n)⁻¹ • (xs n - xbars n) =
      c • ((c * τs n)⁻¹ • (xs n - xbars n)) := fun n ↦ by
    rw [mul_inv, smul_smul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  simpa only [heq] using hq.const_smul c

/-- Closure of the regular tangent cone under nonnegative scaling. -/
theorem smul_mem_regularTangentCone {C : Set E} {x w : E} (hx : x ∈ C)
    (hw : w ∈ regularTangentCone C x) {c : ℝ} (hc : 0 ≤ c) :
    c • w ∈ regularTangentCone C x :=
  (isCone_regularTangentCone hx).smul_mem hw hc

/-- Every regular tangent vector is derivable.  This is the constant-base
specialization of the joint inner limit in Definition 6.25. -/
theorem regularTangentCone_subset_derivableCone {C : Set E} {x : E}
    (hx : x ∈ C) : regularTangentCone C x ⊆ derivableCone C x := by
  rw [derivableCone_eq_innerSetLimitAlong hx]
  intro w hw
  let l := nhdsWithin 0 (Ioi (0 : ℝ))
  have hbase : Tendsto (fun _ : ℝ ↦ x) l (nhdsWithin x C) :=
    tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds.mono_left inf_le_left, Eventually.of_forall fun _ ↦ hx⟩
  have hp : Tendsto (fun τ : ℝ ↦ (x, τ)) l
      ((nhdsWithin x C) ×ˢ l) := hbase.prodMk tendsto_id
  have hmono := innerSetLimitAlong_mono_filter hp
      (fun p : E × ℝ ↦ blowUp C p.1 p.2) hw
  simpa [l, innerSetLimitAlong_comp, Function.comp_def] using hmono

/-- Every regular tangent vector is a tangent vector. -/
theorem regularTangentCone_subset_tangentCone {C : Set E} {x : E}
    (hx : x ∈ C) : regularTangentCone C x ⊆ tangentCone C x :=
  (regularTangentCone_subset_derivableCone hx).trans
    (derivableCone_subset_tangentCone hx)

/-- The regular tangent cone is closed under addition.  The proof is the
two-stage selection in Theorem 6.26: realize the first vector relative to the
arbitrary base sequence, then realize the second relative to the selected
intermediate sequence. -/
theorem add_mem_regularTangentCone {C : Set E} {x w₀ w₁ : E} (hx : x ∈ C)
    (hw₀ : w₀ ∈ regularTangentCone C x) (hw₁ : w₁ ∈ regularTangentCone C x) :
    w₀ + w₁ ∈ regularTangentCone C x := by
  rw [mem_regularTangentCone_iff_forall_sequences hx] at hw₀ hw₁ ⊢
  intro τs xbars hτpos hτ0 hxbarC hxbarto
  obtain ⟨xtildes, hxtildeC, hxtildeto, hq₀⟩ :=
    hw₀ τs xbars hτpos hτ0 hxbarC hxbarto
  obtain ⟨xs, hxsC, hxsto, hq₁⟩ :=
    hw₁ τs xtildes hτpos hτ0 hxtildeC hxtildeto
  refine ⟨xs, hxsC, hxsto, ?_⟩
  have heq : ∀ n, (τs n)⁻¹ • (xs n - xbars n) =
      (τs n)⁻¹ • (xtildes n - xbars n) +
        (τs n)⁻¹ • (xs n - xtildes n) := fun n ↦ by
    rw [← smul_add]
    congr 1
    abel_nf
  simpa only [heq] using hq₀.add hq₁

/-- **Theorem 6.26**: the regular tangent cone is convex. -/
theorem convex_regularTangentCone {C : Set E} {x : E} (hx : x ∈ C) :
    Convex ℝ (regularTangentCone C x) :=
  ((isCone_regularTangentCone hx).convex_iff_add_mem).2
    (fun _ _ ↦ add_mem_regularTangentCone hx)

section FiniteDimensional

/-- Formula 6(18): failure of regular tangency is witnessed by approaching
base points and positive scales at which one fixed ball of quotients is
missed. -/
theorem not_mem_regularTangentCone_iff_exists_sequences {C : Set E} {x w : E}
    (hx : x ∈ C) :
    w ∉ regularTangentCone C x ↔
      ∃ ε > 0, ∃ (xbars : ℕ → E) (τs : ℕ → ℝ),
        (∀ n, xbars n ∈ C) ∧ Tendsto xbars atTop (nhds x) ∧
        (∀ n, 0 < τs n) ∧ Tendsto τs atTop (nhds 0) ∧
        ∀ n, blowUp C (xbars n) (τs n) ∩ ball w ε = ∅ := by
  classical
  constructor
  · intro hw
    rw [mem_regularTangentCone] at hw
    simp only [not_forall] at hw
    obtain ⟨V, hV, hnot⟩ := hw
    obtain ⟨ε, hε, hballV⟩ := Metric.mem_nhds_iff.1 hV
    obtain ⟨p, hpto, hpbad⟩ :=
      Filter.exists_seq_forall_of_frequently (Filter.not_eventually.1 hnot)
    have hfst := tendsto_nhdsWithin_iff.1 hpto.fst
    have hsnd := tendsto_nhdsWithin_iff.1 hpto.snd
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hfst.2.and hsnd.2)
    refine ⟨ε, hε, (fun n ↦ (p (n + N)).1), (fun n ↦ (p (n + N)).2),
      fun n ↦ (hN _ (Nat.le_add_left N n)).1,
      hfst.1.comp (tendsto_add_atTop_nat N),
      fun n ↦ (hN _ (Nat.le_add_left N n)).2,
      hsnd.1.comp (tendsto_add_atTop_nat N), ?_⟩
    intro n
    apply eq_empty_of_forall_notMem
    intro z hz
    exact hpbad (n + N) ⟨z, hz.1, hballV hz.2⟩
  · rintro ⟨ε, hε, xbars, τs, hxbarC, hxbarto, hτpos, hτ0, hempty⟩ hw
    obtain ⟨xs, hxsC, -, hq⟩ :=
      (mem_regularTangentCone_iff_forall_sequences hx).1 hw
        τs xbars hτpos hτ0 hxbarC hxbarto
    have hevent : ∀ᶠ n in atTop,
        (τs n)⁻¹ • (xs n - xbars n) ∈ ball w ε :=
      hq.eventually (ball_mem_nhds w hε)
    obtain ⟨n, hn⟩ := hevent.exists
    have hmem : (τs n)⁻¹ • (xs n - xbars n) ∈
        blowUp C (xbars n) (τs n) ∩ ball w ε :=
      ⟨⟨xs n, hxsC n, rfl⟩, hn⟩
    rw [hempty n] at hmem
    exact hmem

/-- Failure of the right-hand side of 6(16), in the sequential form 6(17). -/
theorem not_mem_svInnerLimitWithin_tangentCone_iff_exists_sequences
    {C : Set E} {x w : E} :
    w ∉ svInnerLimitWithin (tangentCone C) C x ↔
      ∃ ε > 0, ∃ xbars : ℕ → E,
        (∀ n, xbars n ∈ C) ∧ Tendsto xbars atTop (nhds x) ∧
        ∀ n, tangentCone C (xbars n) ∩ ball w ε = ∅ := by
  classical
  constructor
  · intro hw
    rw [svInnerLimitWithin, mem_innerSetLimitAlong] at hw
    simp only [not_forall] at hw
    obtain ⟨V, hV, hnot⟩ := hw
    obtain ⟨ε, hε, hballV⟩ := Metric.mem_nhds_iff.1 hV
    obtain ⟨y, hyto, hybad⟩ :=
      Filter.exists_seq_forall_of_frequently (Filter.not_eventually.1 hnot)
    have hywithin := tendsto_nhdsWithin_iff.1 hyto
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hywithin.2
    refine ⟨ε, hε, (fun n ↦ y (n + N)), fun n ↦ hN _ (Nat.le_add_left N n),
      hywithin.1.comp (tendsto_add_atTop_nat N), ?_⟩
    intro n
    apply eq_empty_of_forall_notMem
    intro z hz
    exact hybad (n + N) ⟨z, hz.1, hballV hz.2⟩
  · rintro ⟨ε, hε, xbars, hxbarC, hxbarto, hempty⟩ hw
    have hinner : w ∈ innerSetLimit (fun n ↦ tangentCone C (xbars n)) :=
      innerSetLimitAlong_subset_innerSetLimit_comp
        (tendsto_nhdsWithin_of_forall_mem hxbarC hxbarto) hw
    have hevent := hinner (ball w ε) (ball_mem_nhds w hε)
    obtain ⟨n, z, hzTan, hzBall⟩ := hevent.exists
    have hz : z ∈ tangentCone C (xbars n) ∩ ball w ε := ⟨hzTan, hzBall⟩
    rw [hempty n] at hz
    exact hz

/-- The sequential reading of the inner limit of tangent cones in 6(16). -/
theorem mem_svInnerLimitWithin_tangentCone_iff_forall_sequences
    {C : Set E} {x w : E} (hx : x ∈ C) :
    w ∈ svInnerLimitWithin (tangentCone C) C x ↔
      ∀ xbars : ℕ → E, (∀ n, xbars n ∈ C) →
        Tendsto xbars atTop (nhds x) →
        ∃ ws : ℕ → E, (∀ n, ws n ∈ tangentCone C (xbars n)) ∧
          Tendsto ws atTop (nhds w) := by
  classical
  rw [svInnerLimitWithin_eq_iInter (tangentCone C) hx]
  constructor
  · intro hw xbars hxbarC hxbarto
    have hinner : w ∈ innerSetLimit (fun n ↦ tangentCone C (xbars n)) :=
      mem_iInter₂.1 hw xbars ⟨hxbarC, hxbarto⟩
    obtain ⟨ws, hwsevent, hwsto⟩ := mem_innerSetLimit_iff_exists_seq.1 hinner
    let ws' : ℕ → E := fun n ↦
      if ws n ∈ tangentCone C (xbars n) then ws n else 0
    have hws'all : ∀ n, ws' n ∈ tangentCone C (xbars n) := by
      intro n
      by_cases hn : ws n ∈ tangentCone C (xbars n)
      · change (if ws n ∈ tangentCone C (xbars n) then ws n else 0) ∈
          tangentCone C (xbars n)
        rw [if_pos hn]
        exact hn
      · change (if ws n ∈ tangentCone C (xbars n) then ws n else 0) ∈
          tangentCone C (xbars n)
        rw [if_neg hn]
        exact (isCone_tangentCone (hxbarC n)).1
    have hwseq : ws' =ᶠ[atTop] ws := hwsevent.mono fun n hn ↦ by
      change (if ws n ∈ tangentCone C (xbars n) then ws n else 0) = ws n
      rw [if_pos hn]
    exact ⟨ws', hws'all, hwsto.congr' hwseq.symm⟩
  · intro hseq
    apply mem_iInter₂.2
    intro xbars hxbars
    obtain ⟨ws, hwsTan, hwsto⟩ := hseq xbars hxbars.1 hxbars.2
    exact mem_innerSetLimit_iff_exists_seq.2
      ⟨ws, Eventually.of_forall hwsTan, hwsto⟩

variable [FiniteDimensional ℝ E]

/-- The compact last-contact argument at the heart of Theorem 6.26.  If a
closed ball of difference quotients is missed at one positive scale, a nearby
point of the closed set has a tangent cone missing the corresponding open
ball. -/
private theorem exists_tangentCone_avoids_ball_of_blowUp_avoids_closedBall
    {C : Set E} (hC : IsClosed C) {xhat w : E} (hxhat : xhat ∈ C)
    {r τbar : ℝ} (hr : 0 < r) (hτbar : 0 < τbar)
    (hmiss : blowUp C xhat τbar ∩ closedBall w r = ∅) :
    ∃ xtilde ∈ C, dist xtilde xhat ≤ τbar * (‖w‖ + r) ∧
      tangentCone C xtilde ∩ ball w r = ∅ := by
  let f : ℝ × E → E := fun p ↦ xhat + p.1 • p.2
  let K : Set (ℝ × E) :=
    (Icc (0 : ℝ) τbar ×ˢ closedBall w r) ∩ f ⁻¹' C
  let A : Set ℝ := Prod.fst '' K
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hKcompact : IsCompact K := by
    exact (isCompact_Icc.prod (isCompact_closedBall w r)).inter_right (hC.preimage hf)
  have hAcompact : IsCompact A := hKcompact.image continuous_fst
  have hwball : w ∈ closedBall w r := by simp [hr.le]
  have hAne : A.Nonempty := by
    refine ⟨0, ⟨(0, w), ?_, rfl⟩⟩
    refine ⟨⟨⟨le_rfl, hτbar.le⟩, hwball⟩, ?_⟩
    simpa [f] using hxhat
  obtain ⟨τhat, hτhatA, hτhatmax⟩ := hAcompact.exists_isGreatest hAne
  obtain ⟨p, hpK, hpτ⟩ := hτhatA
  have hpIcc : p.1 ∈ Icc (0 : ℝ) τbar := hpK.1.1
  have hpu : p.2 ∈ closedBall w r := hpK.1.2
  have hpC : f p ∈ C := hpK.2
  have hτhat0 : 0 ≤ τhat := by simpa [hpτ] using hpIcc.1
  have hτhatle : τhat ≤ τbar := by simpa [hpτ] using hpIcc.2
  have hτhatlt : τhat < τbar := by
    refine lt_of_le_of_ne hτhatle ?_
    intro heq
    have hpτbar : p.1 = τbar := hpτ.trans heq
    have huBlow : p.2 ∈ blowUp C xhat τbar := by
      refine ⟨f p, hpC, ?_⟩
      dsimp [f]
      rw [hpτbar, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ hτbar.ne', one_smul]
    have : p.2 ∈ blowUp C xhat τbar ∩ closedBall w r := ⟨huBlow, hpu⟩
    rw [hmiss] at this
    exact this
  let xtilde : E := f p
  refine ⟨xtilde, hpC, ?_, ?_⟩
  · have hpunorm : ‖p.2‖ ≤ ‖w‖ + r := by
      calc
        ‖p.2‖ = ‖(p.2 - w) + w‖ := by abel_nf
        _ ≤ ‖p.2 - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ r + ‖w‖ := by
          gcongr
          simpa [dist_eq_norm] using hpu
        _ = ‖w‖ + r := add_comm _ _
    change dist (f p) xhat ≤ τbar * (‖w‖ + r)
    rw [dist_eq_norm]
    dsimp [f]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hpIcc.1]
    exact (mul_le_mul_of_nonneg_left hpunorm hpIcc.1).trans
      (mul_le_mul_of_nonneg_right hpIcc.2 (by positivity))
  · rw [eq_empty_iff_forall_notMem]
    rintro v ⟨hvTan, hvBall⟩
    obtain ⟨ys, ts, hysC, -, htspos, hts0, hqto⟩ := hvTan
    have hgap : 0 < τbar - τhat := sub_pos.2 hτhatlt
    have hsmall : ∀ᶠ n in atTop, ts n < τbar - τhat :=
      hts0.eventually_lt_const hgap
    have hqball : ∀ᶠ n in atTop,
        (ts n)⁻¹ • (ys n - xtilde) ∈ ball w r :=
      hqto.eventually (isOpen_ball.mem_nhds hvBall)
    obtain ⟨n, hnsmall, hnball⟩ := (hsmall.and hqball).exists
    let t := ts n
    let q := (ts n)⁻¹ • (ys n - xtilde)
    have htpos : 0 < t := htspos n
    have htsumpos : 0 < τhat + t := add_pos_of_nonneg_of_pos hτhat0 htpos
    let u' : E := (τhat / (τhat + t)) • p.2 +
      (t / (τhat + t)) • q
    have hcoef0 : 0 ≤ τhat / (τhat + t) := div_nonneg hτhat0 htsumpos.le
    have hcoef1 : 0 ≤ t / (τhat + t) := div_nonneg htpos.le htsumpos.le
    have hcoefsum : τhat / (τhat + t) + t / (τhat + t) = 1 := by
      field_simp
    have hu'ball : u' ∈ closedBall w r := by
      exact (convex_closedBall w r) hpu (ball_subset_closedBall hnball)
        hcoef0 hcoef1 hcoefsum
    have hyformula : ys n = xtilde + t • q := by
      dsimp [q, t]
      rw [smul_smul, mul_inv_cancel₀ (htspos n).ne', one_smul, add_sub_cancel]
    have hcontact : xhat + (τhat + t) • u' = ys n := by
      have hcoefτ : (τhat + t) * (τhat / (τhat + t)) = τhat := by
        field_simp
      have hcoeft : (τhat + t) * (t / (τhat + t)) = t := by
        field_simp
      dsimp [u', xtilde, f] at hyformula ⊢
      rw [hpτ] at hyformula
      rw [smul_add, smul_smul, smul_smul, hcoefτ, hcoeft]
      simpa only [add_assoc] using hyformula.symm
    have hsumIcc : τhat + t ∈ Icc (0 : ℝ) τbar := by
      exact ⟨htsumpos.le, by dsimp [t] at hnsmall ⊢; linarith⟩
    have hsumA : τhat + t ∈ A := by
      refine ⟨(τhat + t, u'), ?_, rfl⟩
      refine ⟨⟨hsumIcc, hu'ball⟩, ?_⟩
      change xhat + (τhat + t) • u' ∈ C
      rw [hcontact]
      exact hysC n
    have := hτhatmax hsumA
    linarith

/-- Formula 6(16) for a closed set.  Local closedness is reduced to this
case below. -/
private theorem regularTangentCone_eq_svInnerLimitWithin_tangentCone_of_isClosed
    {C : Set E} (hC : IsClosed C) {x : E} (hx : x ∈ C) :
    regularTangentCone C x = svInnerLimitWithin (tangentCone C) C x := by
  ext w
  constructor
  · intro hw
    by_contra hinner
    obtain ⟨ε, hε, xbars, hxbarC, hxbarto, hTanEmpty⟩ :=
      not_mem_svInnerLimitWithin_tangentCone_iff_exists_sequences.1 hinner
    have havoid : ∀ n, ∀ᶠ τ in nhdsWithin 0 (Ioi (0 : ℝ)),
        blowUp C (xbars n) τ ∩ closedBall w (ε / 2) = ∅ := by
      intro n
      have hnotfreq : ¬ ∃ᶠ τ in nhdsWithin 0 (Ioi (0 : ℝ)),
          (blowUp C (xbars n) τ ∩ closedBall w (ε / 2)).Nonempty := by
        intro hfreq
        have hlim := outerSetLimitAlong_inter_nonempty_of_frequently
          (isCompact_closedBall w (ε / 2)) hfreq
        rw [← tangentCone_eq_outerSetLimitAlong] at hlim
        obtain ⟨v, hvTan, hvBall⟩ := hlim
        have hvOpen : v ∈ ball w ε := by
          exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hvBall) (by linarith))
        have hv : v ∈ tangentCone C (xbars n) ∩ ball w ε := ⟨hvTan, hvOpen⟩
        rw [hTanEmpty n] at hv
        exact hv
      filter_upwards [Filter.not_frequently.1 hnotfreq] with τ hτ
      exact not_nonempty_iff_eq_empty.1 hτ
    have hpick : ∀ n : ℕ, ∃ τ : ℝ,
        0 < τ ∧ τ < 1 / ((n : ℝ) + 1) ∧
          blowUp C (xbars n) τ ∩ ball w (ε / 2) = ∅ := by
      intro n
      have hbound : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨τ, hτavoid, hτIoo⟩ :=
        ((havoid n).and (Ioo_mem_nhdsGT hbound)).exists
      refine ⟨τ, hτIoo.1, hτIoo.2, ?_⟩
      apply eq_empty_of_forall_notMem
      intro v hv
      have hv' : v ∈ blowUp C (xbars n) τ ∩ closedBall w (ε / 2) :=
        ⟨hv.1, ball_subset_closedBall hv.2⟩
      rw [hτavoid] at hv'
      exact hv'
    choose τs hτpos hτbound hBlowEmpty using hpick
    have hτ0 : Tendsto τs atTop (nhds 0) :=
      squeeze_zero (fun n ↦ (hτpos n).le) (fun n ↦ (hτbound n).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hnreg : w ∉ regularTangentCone C x :=
      (not_mem_regularTangentCone_iff_exists_sequences hx).2
        ⟨ε / 2, by linarith, xbars, τs, hxbarC, hxbarto,
          hτpos, hτ0, hBlowEmpty⟩
    exact hnreg hw
  · intro hinner
    by_contra hnreg
    obtain ⟨ε, hε, xbars, τs, hxbarC, hxbarto, hτpos, hτ0, hBlowEmpty⟩ :=
      (not_mem_regularTangentCone_iff_exists_sequences hx).1 hnreg
    have hpick : ∀ n, ∃ xtilde ∈ C,
        dist xtilde (xbars n) ≤ τs n * (‖w‖ + ε / 2) ∧
          tangentCone C xtilde ∩ ball w (ε / 2) = ∅ := by
      intro n
      apply exists_tangentCone_avoids_ball_of_blowUp_avoids_closedBall
        hC (hxbarC n) (by linarith) (hτpos n)
      apply eq_empty_of_forall_notMem
      intro v hv
      have hv' : v ∈ blowUp C (xbars n) (τs n) ∩ ball w ε :=
        ⟨hv.1, mem_ball.2
          (lt_of_le_of_lt (mem_closedBall.1 hv.2) (by linarith))⟩
      rw [hBlowEmpty n] at hv'
      exact hv'
    choose xtildes hxtildeC hdist hTanEmpty using hpick
    have hboundto : Tendsto (fun n ↦ τs n * (‖w‖ + ε / 2))
        atTop (nhds 0) := by
      simpa using hτ0.mul_const (‖w‖ + ε / 2)
    have hxtildeto : Tendsto xtildes atTop (nhds x) := by
      rw [Metric.tendsto_nhds]
      intro δ hδ
      have hnear : ∀ᶠ n in atTop, τs n * (‖w‖ + ε / 2) < δ / 2 :=
        hboundto.eventually_lt_const (by linarith)
      have hbase : ∀ᶠ n in atTop, dist (xbars n) x < δ / 2 :=
        (Metric.tendsto_nhds.1 hxbarto) (δ / 2) (by linarith)
      filter_upwards [hnear, hbase] with n hnclose hnbase
      calc
        dist (xtildes n) x ≤ dist (xtildes n) (xbars n) + dist (xbars n) x :=
          dist_triangle _ _ _
        _ < δ := by linarith [hdist n]
    have hnotinner : w ∉ svInnerLimitWithin (tangentCone C) C x :=
      not_mem_svInnerLimitWithin_tangentCone_iff_exists_sequences.2
        ⟨ε / 2, by linarith, xtildes, hxtildeC, hxtildeto, hTanEmpty⟩
    exact hnotinner hinner

omit [FiniteDimensional ℝ E] in
/-- The regular tangent cone is local: intersecting the set with a
neighborhood of the base point does not change it. -/
theorem regularTangentCone_inter_nhds {C V : Set E} {x : E} (hx : x ∈ C)
    (hV : V ∈ nhds x) :
    regularTangentCone (C ∩ V) x = regularTangentCone C x := by
  classical
  have hxV : x ∈ V := mem_of_mem_nhds hV
  have hxCV : x ∈ C ∩ V := ⟨hx, hxV⟩
  ext w
  rw [mem_regularTangentCone_iff_forall_sequences hxCV,
    mem_regularTangentCone_iff_forall_sequences hx]
  constructor
  · intro hw τs xbars hτpos hτ0 hxbarC hxbarto
    let xbars' : ℕ → E := fun n ↦ if xbars n ∈ V then xbars n else x
    have hxbar'CV : ∀ n, xbars' n ∈ C ∩ V := by
      intro n
      by_cases hn : xbars n ∈ V
      · change (if xbars n ∈ V then xbars n else x) ∈ C ∩ V
        rw [if_pos hn]
        exact ⟨hxbarC n, hn⟩
      · change (if xbars n ∈ V then xbars n else x) ∈ C ∩ V
        rw [if_neg hn]
        exact hxCV
    have hxbarevent : xbars' =ᶠ[atTop] xbars :=
      (hxbarto.eventually hV).mono fun n hn ↦ by
        change (if xbars n ∈ V then xbars n else x) = xbars n
        exact if_pos hn
    have hxbar'to : Tendsto xbars' atTop (nhds x) :=
      hxbarto.congr' hxbarevent.symm
    obtain ⟨xs, hxsCV, hxsto, hq⟩ :=
      hw τs xbars' hτpos hτ0 hxbar'CV hxbar'to
    refine ⟨xs, fun n ↦ (hxsCV n).1, hxsto, ?_⟩
    apply hq.congr'
    filter_upwards [hxbarevent] with n hn
    rw [hn]
  · intro hw τs xbars hτpos hτ0 hxbarCV hxbarto
    obtain ⟨xs, hxsC, hxsto, hq⟩ :=
      hw τs xbars hτpos hτ0 (fun n ↦ (hxbarCV n).1) hxbarto
    let xs' : ℕ → E := fun n ↦ if xs n ∈ V then xs n else x
    have hxs'CV : ∀ n, xs' n ∈ C ∩ V := by
      intro n
      by_cases hn : xs n ∈ V
      · change (if xs n ∈ V then xs n else x) ∈ C ∩ V
        rw [if_pos hn]
        exact ⟨hxsC n, hn⟩
      · change (if xs n ∈ V then xs n else x) ∈ C ∩ V
        rw [if_neg hn]
        exact hxCV
    have hxsevent : xs' =ᶠ[atTop] xs :=
      (hxsto.eventually hV).mono fun n hn ↦ by
        change (if xs n ∈ V then xs n else x) = xs n
        exact if_pos hn
    have hxs'to : Tendsto xs' atTop (nhds x) := hxsto.congr' hxsevent.symm
    refine ⟨xs', hxs'CV, hxs'to, ?_⟩
    apply hq.congr'
    filter_upwards [hxsevent] with n hn
    rw [hn]

omit [FiniteDimensional ℝ E] in
/-- Both the approaching-base filter and the tangent-cone mapping in 6(16)
are local. -/
private theorem svInnerLimitWithin_tangentCone_inter_nhds
    {C V : Set E} {x : E} (hV : V ∈ nhds x) :
    svInnerLimitWithin (tangentCone (C ∩ V)) (C ∩ V) x =
      svInnerLimitWithin (tangentCone C) C x := by
  have hxint : x ∈ interior V := mem_interior_iff_mem_nhds.2 hV
  have hint : interior V ∈ nhds x := isOpen_interior.mem_nhds hxint
  have heq : tangentCone (C ∩ V) =ᶠ[nhdsWithin x C] tangentCone C := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hint] with y hy
    exact tangentCone_inter_nhds (mem_interior_iff_mem_nhds.1 hy)
  rw [svInnerLimitWithin, svInnerLimitWithin, ← nhdsWithin_restrict' C hV]
  exact innerSetLimitAlong_congr heq

/-- **Theorem 6.26**, formula 6(16). -/
theorem regularTangentCone_eq_svInnerLimitWithin_tangentCone
    {C : Set E} {x : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    regularTangentCone C x =
      svInnerLimitWithin (tangentCone C) C x := by
  obtain ⟨V, hV, -, hCVclosed⟩ := hlc
  have hxCV : x ∈ C ∩ V := ⟨hx, mem_of_mem_nhds hV⟩
  calc
    regularTangentCone C x = regularTangentCone (C ∩ V) x :=
      (regularTangentCone_inter_nhds hx hV).symm
    _ = svInnerLimitWithin (tangentCone (C ∩ V)) (C ∩ V) x :=
      regularTangentCone_eq_svInnerLimitWithin_tangentCone_of_isClosed
        hCVclosed hxCV
    _ = svInnerLimitWithin (tangentCone C) C x :=
      svInnerLimitWithin_tangentCone_inter_nhds hV

/-- **Theorem 6.26**, sequential locally closed characterization: a vector is
regular tangent exactly when every approaching base sequence admits tangent
vectors converging to it. -/
theorem mem_regularTangentCone_iff_forall_tangent_sequences
    {C : Set E} {x w : E} (hx : x ∈ C) (hlc : IsLocallyClosedAt C x) :
    w ∈ regularTangentCone C x ↔
      ∀ xbars : ℕ → E, (∀ n, xbars n ∈ C) →
        Tendsto xbars atTop (nhds x) →
        ∃ ws : ℕ → E, (∀ n, ws n ∈ tangentCone C (xbars n)) ∧
          Tendsto ws atTop (nhds w) := by
  rw [regularTangentCone_eq_svInnerLimitWithin_tangentCone hx hlc,
    mem_svInnerLimitWithin_tangentCone_iff_forall_sequences hx]

end FiniteDimensional

end RegularTangents

end RW
