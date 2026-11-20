/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lagrangians of dualizing parameterizations

Definition 11.45 with formula 11(17), and Proposition 11.48.
-/
import RockafellarWets.Chapter11.PrimalDualSolutions
import RockafellarWets.Chapter3.Pointwise
import RockafellarWets.Chapter3.ERealInfimum

open Set Filter Topology
open scoped InnerProductSpace
namespace RW
noncomputable section

section ConvexSubgradients
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {g : F → EReal} {z v : F} {c : ℝ}

/-- A regular subgradient of a function with convex epigraph at a finite point
is the slope of a global affine minorant. Properness is not assumed: a value
`-∞` anywhere would violate the normal-cone inequality. -/
theorem forall_le_of_mem_regularSubdifferential_of_convex (hc : Convex ℝ (epigraph g))
    (hz : g z = c) (hv : v ∈ regularSubdifferential g z) :
    ∀ w, ((c + ⟪v, w - z⟫_ℝ : ℝ) : EReal) ≤ g w := by
  rw [mem_regularSubdifferential_iff_epigraph_normal hz] at hv
  have hcp : Convex ℝ (euclideanEpigraph g) :=
    convex_preimage_continuousLinearEquiv (l2ProdEquiv F) hc
  rw [regularNormalCone_eq_of_convex hcp
    (show WithLp.toLp 2 (z, c) ∈ euclideanEpigraph g from hz.le)] at hv
  intro w
  by_cases hwt : g w = ⊤
  · simp [hwt]
  by_cases hwb : g w = ⊥
  · exfalso
    have h := hv (WithLp.toLp 2 (w, c + ⟪v, w - z⟫_ℝ - 1))
      (show g w ≤ _ by rw [hwb]; exact bot_le)
    change ⟪v, w - z⟫_ℝ + ((c + ⟪v, w - z⟫_ℝ - 1) - c) * (-1) ≤ 0 at h
    linarith
  have hwr := EReal.coe_toReal hwt hwb
  have h := hv (WithLp.toLp 2 (w, (g w).toReal)) (show g w ≤ _ from hwr.ge)
  change ⟪v, w - z⟫_ℝ + ((g w).toReal - c) * (-1) ≤ 0 at h
  rw [← hwr]
  exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- Attentive limits of convex regular subgradients keep the global support
inequality, again without a properness hypothesis. -/
theorem forall_le_of_mem_subdifferential_of_convex (hc : Convex ℝ (epigraph g))
    (hz : g z = c) (hv : v ∈ subdifferential g z) :
    ∀ w, ((c + ⟪v, w - z⟫_ℝ : ℝ) : EReal) ≤ g w := by
  intro w
  obtain ⟨_, y, u, hy, hgy, hu, huv⟩ := mem_subdifferential_iff_exists_seq.mp hv
  have hgy' : Tendsto (fun n ↦ (g (y n)).toReal) atTop (𝓝 c) := by
    rw [hz] at hgy
    simpa using (EReal.tendsto_toReal (EReal.coe_ne_top c) (EReal.coe_ne_bot c)).comp hgy
  apply le_of_tendsto ((continuous_coe_real_ereal.tendsto _).comp
    (hgy'.add (huv.inner (tendsto_const_nhds.sub hy))))
  filter_upwards with n
  obtain ⟨a, ha⟩ : ∃ a : ℝ, g (y n) = a := ⟨(hu n).choose, (hu n).choose_spec.1⟩
  have hn := forall_le_of_mem_regularSubdifferential_of_convex hc ha (hu n) w
  simpa [ha] using hn

/-- **Proposition 8.12** at a finite point of a function with convex epigraph,
with properness derived from the subgradient inequality instead of assumed. -/
theorem mem_subdifferential_iff_of_convex_of_eq_coe (hc : Convex ℝ (epigraph g))
    (hz : g z = c) : v ∈ subdifferential g z ↔ ∀ w, ((c + ⟪v, w - z⟫_ℝ : ℝ) : EReal) ≤ g w := by
  refine ⟨forall_le_of_mem_subdifferential_of_convex hc hz, fun h ↦ ?_⟩
  have hp : IsProper g :=
    ⟨⟨z, hz ▸ EReal.coe_lt_top c⟩, fun w ↦ (EReal.bot_lt_coe _).trans_le (h w)⟩
  exact (mem_subdifferential_iff_of_convex hc hp hz).mpr h

end ConvexSubgradients

/-- Moving a finite summand across an extended-real inequality. -/
theorem ereal_add_coe_le_coe_iff (a : EReal) (r b : ℝ) :
    a + (r : EReal) ≤ (b : EReal) ↔ a ≤ ((b - r : ℝ) : EReal) := by
  cases a with
  | bot => simp
  | top => simp only [EReal.top_add_coe, top_le_iff, EReal.coe_ne_top]
  | coe a =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

/-- Moving a finite subtrahend across an extended-real inequality. -/
theorem ereal_coe_le_sub_coe_iff (a : EReal) (r s : ℝ) :
    (r : EReal) ≤ a - (s : EReal) ↔ ((r + s : ℝ) : EReal) ≤ a := by
  cases a with
  | bot => simp
  | top => simp
  | coe a =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem inner_toLp_sub_toLp (v x' x : E) (y u' u : P) :
    ⟪WithLp.toLp 2 (v, y), WithLp.toLp 2 (x', u') - WithLp.toLp 2 (x, u)⟫_ℝ =
      ⟪v, x' - x⟫_ℝ + ⟪y, u' - u⟫_ℝ := by
  rw [← WithLp.toLp_sub, WithLp.prod_inner_apply]
  rfl

/-- The parameter slice `u ↦ f(x,u)`. -/
def parameterSlice (f : WithLp 2 (E × P) → EReal) (x : E) (u : P) : EReal :=
  f (WithLp.toLp 2 (x, u))

/-- **Definition 11.45**. The representation `φ = f(·,0)` of the problem of
minimizing `φ` is a dualizing parameterization when `f` is proper and `f(x,u)`
is lsc and convex in `u` for every `x`. -/
structure IsDualizingParameterization (φ : E → EReal) (f : WithLp 2 (E × P) → EReal) :
    Prop where
  eq_primalObjective : φ = primalObjective f
  isProper : IsProper f
  lowerSemicontinuous_slice : ∀ x : E, LowerSemicontinuous (parameterSlice f x)
  convex_slice : ∀ x : E, Convex ℝ (epigraph (parameterSlice f x))

/-- The Lagrangian **11(16)**, `l(x,y) = inf_u {f(x,u) - ⟨y,u⟩}`. -/
def lagrangian (f : WithLp 2 (E × P) → EReal) (x : E) (y : P) : EReal :=
  ⨅ u : P, f (WithLp.toLp 2 (x, u)) - (⟪y, u⟫_ℝ : EReal)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P] in
theorem lagrangian_eq_neg_fenchelConjugate (f : WithLp 2 (E × P) → EReal) (x : E) (y : P) :
    lagrangian f x y = -fenchelConjugate (parameterSlice f x) y :=
  iInf_sub_inner_eq_neg_fenchelConjugate (parameterSlice f x) y

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P] in
/-- For each `x`, `-l(x,·)` is conjugate to `f(x,·)` (Definition 11.45). -/
theorem neg_lagrangian_eq_fenchelConjugate (f : WithLp 2 (E × P) → EReal) (x : E) :
    (fun y ↦ -lagrangian f x y) = fenchelConjugate (parameterSlice f x) := by
  funext y
  rw [lagrangian_eq_neg_fenchelConjugate, neg_neg]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P] in
/-- Under a dualizing parameterization each slice `f(x,·)` is proper, lsc and
convex unless it is identically `∞`. -/
theorem IsDualizingParameterization.slice_cases {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) (x : E) :
    (IsProper (parameterSlice f x) ∧ LowerSemicontinuous (parameterSlice f x) ∧
      Convex ℝ (epigraph (parameterSlice f x))) ∨ parameterSlice f x = fun _ ↦ ⊤ := by
  by_cases h : ∃ u, parameterSlice f x u < ⊤
  · exact .inl ⟨⟨h, fun u ↦ hf.isProper.2 _⟩, hf.lowerSemicontinuous_slice x, hf.convex_slice x⟩
  · push_neg at h
    exact .inr (funext fun u ↦ top_le_iff.mp (h u))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Each slice coincides with its biconjugate, by 11.1 and 11.2. -/
theorem IsDualizingParameterization.biconjugate_slice {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) (x : E) :
    fenchelConjugate (fenchelConjugate (parameterSlice f x)) = parameterSlice f x := by
  rcases hf.slice_cases x with ⟨hp, hl, hc⟩ | ht
  · exact fenchelConjugate_fenchelConjugate_eq hp hl hc
  · rw [ht]
    exact identically_top_conjugates.2

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Formula **11(17)**: `f(x,u) = sup_y {l(x,y) + ⟨y,u⟩}`. -/
theorem IsDualizingParameterization.eq_iSup_lagrangian {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) (x : E) (u : P) :
    f (WithLp.toLp 2 (x, u)) = ⨆ y, lagrangian f x y + (⟪y, u⟫_ℝ : EReal) := by
  have h := congrFun (hf.biconjugate_slice x) u
  rw [← neg_lagrangian_eq_fenchelConjugate] at h
  refine h.symm.trans (iSup_congr fun y ↦ ?_)
  change (⟪u, y⟫_ℝ : EReal) - -lagrangian f x y = _
  rw [sub_eq_add_neg, neg_neg, add_comm, real_inner_comm]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- The parameterizations of **11.39** are dualizing (as remarked after 11.45). -/
theorem isDualizingParameterization_of_convex {f : WithLp 2 (E × P) → EReal}
    (hp : IsProper f) (hl : LowerSemicontinuous f) (hc : Convex ℝ (epigraph f)) :
    IsDualizingParameterization (primalObjective f) f := by
  refine ⟨rfl, hp, fun x ↦ hl.comp (by fun_prop), fun x ↦ ?_⟩
  rintro ⟨u₁, a₁⟩ h₁ ⟨u₂, a₂⟩ h₂ t s ht hs hts
  have hh := hc (show (WithLp.toLp 2 (x, u₁), a₁) ∈ epigraph f from h₁)
    (show (WithLp.toLp 2 (x, u₂), a₂) ∈ epigraph f from h₂) ht hs hts
  change f (t • WithLp.toLp 2 (x, u₁) + s • WithLp.toLp 2 (x, u₂)) ≤ ((t * a₁ + s * a₂ : ℝ) : EReal)
    at hh
  change f (WithLp.toLp 2 (x, t • u₁ + s • u₂)) ≤ ((t * a₁ + s * a₂ : ℝ) : EReal)
  rwa [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add, Prod.smul_mk, Prod.smul_mk,
    Prod.mk_add_mk, Convex.combo_self hts] at hh

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P] in
/-- **Proposition 11.48**, first assertion: `l(x,y)` is usc and concave in `y`. -/
theorem lagrangian_usc_concave (f : WithLp 2 (E × P) → EReal) (x : E) :
    UpperSemicontinuous (lagrangian f x) ∧ Convex ℝ (epigraph (fun y ↦ -lagrangian f x y)) := by
  refine ⟨?_, (neg_lagrangian_eq_fenchelConjugate f x) ▸ convex_epigraph_fenchelConjugate _⟩
  have he : lagrangian f x = fun y ↦ -fenchelConjugate (parameterSlice f x) y :=
    funext (lagrangian_eq_neg_fenchelConjugate f x)
  rw [he]
  exact continuous_neg.comp_lowerSemicontinuous_antitone (lowerSemicontinuous_fenchelConjugate _)
    EReal.neg_strictAnti.antitone

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
theorem lagrangian_eq_fiberInfimum (f : WithLp 2 (E × P) → EReal) (y : P) :
    (fun x ↦ lagrangian f x y) = fiberInfimum (WithLp.fstL 2 ℝ E P)
      (fun q ↦ f q - (⟪WithLp.toLp 2 ((0 : E), y), q⟫_ℝ : EReal)) := by
  funext x
  apply le_antisymm (le_iInf fun q ↦ iInf_le_of_le q.val.snd ?_) (le_iInf fun u ↦ ?_)
  · obtain ⟨q, hq⟩ := q
    change q.fst = x at hq
    subst x
    have hi : ⟪WithLp.toLp 2 ((0 : E), y), q⟫_ℝ = ⟪y, q.snd⟫_ℝ := by simp [WithLp.prod_inner_apply]
    change f q - (⟪y, q.snd⟫_ℝ : EReal) ≤ f q - (⟪WithLp.toLp 2 ((0 : E), y), q⟫_ℝ : EReal)
    rw [hi]
  · refine iInf_le_of_le ⟨WithLp.toLp 2 (x, u), rfl⟩ ?_
    simp [WithLp.prod_inner_apply]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
/-- Joint convexity of `f` makes the Lagrangian convex in `x` (inf-projection). -/
theorem convex_epigraph_lagrangian_of_convex {f : WithLp 2 (E × P) → EReal}
    (hc : Convex ℝ (epigraph f)) (y : P) : Convex ℝ (epigraph (fun x ↦ lagrangian f x y)) := by
  rw [lagrangian_eq_fiberInfimum]
  exact convex_epigraph_fiberInfimum _ (convex_epigraph_sub_inner hc _)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ P] in
private theorem convex_epigraph_fst_add_inner {g : E → EReal} (hg : Convex ℝ (epigraph g))
    (y : P) : Convex ℝ (epigraph (fun q : WithLp 2 (E × P) ↦ g q.fst + (⟪y, q.snd⟫_ℝ : EReal))) := by
  rintro ⟨q₁, a₁⟩ h₁ ⟨q₂, a₂⟩ h₂ t s ht hs hts
  change g q₁.fst + (⟪y, q₁.snd⟫_ℝ : EReal) ≤ (a₁ : EReal) at h₁
  change g q₂.fst + (⟪y, q₂.snd⟫_ℝ : EReal) ≤ (a₂ : EReal) at h₂
  rw [ereal_add_coe_le_coe_iff] at h₁ h₂
  have hh := hg (show (q₁.fst, a₁ - ⟪y, q₁.snd⟫_ℝ) ∈ epigraph g from h₁)
    (show (q₂.fst, a₂ - ⟪y, q₂.snd⟫_ℝ) ∈ epigraph g from h₂) ht hs hts
  change g (t • q₁.fst + s • q₂.fst) ≤
    ((t * (a₁ - ⟪y, q₁.snd⟫_ℝ) + s * (a₂ - ⟪y, q₂.snd⟫_ℝ) : ℝ) : EReal) at hh
  change g (t • q₁ + s • q₂).fst + (⟪y, (t • q₁ + s • q₂).snd⟫_ℝ : EReal) ≤
    ((t * a₁ + s * a₂ : ℝ) : EReal)
  rw [ereal_add_coe_le_coe_iff]
  simp only [WithLp.add_fst, WithLp.smul_fst, WithLp.add_snd, WithLp.smul_snd, inner_add_right,
    inner_smul_right]
  convert hh using 2
  ring

omit [FiniteDimensional ℝ E] in
/-- **Proposition 11.48**, second assertion: the Lagrangian of a dualizing
parameterization is convex in `x` exactly when `f(x,u)` is convex in `(x,u)`. -/
theorem IsDualizingParameterization.convex_lagrangian_iff {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f) :
    (∀ y, Convex ℝ (epigraph (fun x ↦ lagrangian f x y))) ↔ Convex ℝ (epigraph f) := by
  refine ⟨fun hl ↦ ?_, fun hc y ↦ convex_epigraph_lagrangian_of_convex hc y⟩
  have he : f = fun q ↦ ⨆ y, lagrangian f q.fst y + (⟪y, q.snd⟫_ℝ : EReal) :=
    funext fun q ↦ hf.eq_iSup_lagrangian q.fst q.snd
  rw [he]
  exact convex_epigraph_iSup fun y ↦ convex_epigraph_fst_add_inner (hl y) y

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ P] in
/-- The value identity in **11.48**: at a subgradient pair the slice value is
finite and `l(x,y) = f(x,u) - ⟨y,u⟩`. -/
private theorem lagrangian_eq_of_slice_support {f : WithLp 2 (E × P) → EReal} {x : E} {u y : P}
    {c : ℝ} (hfc : f (WithLp.toLp 2 (x, u)) = c)
    (hs : ∀ u', ((c + ⟪y, u' - u⟫_ℝ : ℝ) : EReal) ≤ f (WithLp.toLp 2 (x, u'))) :
    lagrangian f x y = ((c - ⟪y, u⟫_ℝ : ℝ) : EReal) := by
  apply le_antisymm
  · refine (iInf_le _ u).trans ?_
    rw [hfc, EReal.coe_sub]
  · refine le_iInf fun u' ↦ (ereal_coe_le_sub_coe_iff _ _ _).mpr ?_
    convert hs u' using 2
    rw [inner_sub_right]
    ring

/-- **Proposition 11.48**, the subgradient correspondence for convex `f`:
`(v,y) ∈ ∂f(x,u)` iff `v ∈ ∂ₓl(x,y)` and `u ∈ ∂_y[-l](x,y)`. -/
theorem IsDualizingParameterization.mem_subdifferential_iff_lagrangian {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f)
    (hc : Convex ℝ (epigraph f)) (x v : E) (u y : P) :
    WithLp.toLp 2 (v, y) ∈ subdifferential f (WithLp.toLp 2 (x, u)) ↔
      v ∈ subdifferential (fun z ↦ lagrangian f z y) x ∧
        u ∈ subdifferential (fun w ↦ -lagrangian f x w) y := by
  have hp := hf.isProper
  rw [neg_lagrangian_eq_fenchelConjugate]
  constructor
  · intro h
    obtain ⟨c, hfc⟩ := h.1
    have hall := (mem_subdifferential_iff_of_convex hc hp hfc).mp h
    have hall' (x' : E) (u' : P) :
        ((c + ⟪v, x' - x⟫_ℝ + ⟪y, u' - u⟫_ℝ : ℝ) : EReal) ≤ f (WithLp.toLp 2 (x', u')) := by
      have h' := hall (WithLp.toLp 2 (x', u'))
      rwa [inner_toLp_sub_toLp, ← add_assoc] at h'
    have hgp : IsProper (parameterSlice f x) :=
      ⟨⟨u, show f _ < ⊤ by rw [hfc]; exact EReal.coe_lt_top c⟩, fun w ↦ hp.2 _⟩
    have hs (u' : P) : ((c + ⟪y, u' - u⟫_ℝ : ℝ) : EReal) ≤ f (WithLp.toLp 2 (x, u')) := by
      simpa using hall' x u'
    have hyg : y ∈ subdifferential (parameterSlice f x) u :=
      (mem_subdifferential_iff_of_convex (hf.convex_slice x) hgp hfc).mpr hs
    have hlx := lagrangian_eq_of_slice_support hfc hs
    refine ⟨(mem_subdifferential_iff_of_convex_of_eq_coe
      (convex_epigraph_lagrangian_of_convex hc y) hlx).mpr fun x' ↦ ?_,
      (mem_subdifferential_fenchelConjugate_iff hgp (hf.lowerSemicontinuous_slice x)
        (hf.convex_slice x) u y).mpr hyg⟩
    refine le_iInf fun u' ↦ (ereal_coe_le_sub_coe_iff _ _ _).mpr ?_
    convert hall' x' u' using 2
    simp only [inner_sub_right]
    ring
  · rintro ⟨hv, hu⟩
    have hgp : IsProper (parameterSlice f x) := by
      rcases hf.slice_cases x with ⟨hgp, -, -⟩ | ht
      · exact hgp
      · exfalso
        obtain ⟨e, he⟩ := hu.1
        rw [ht, identically_top_conjugates.1] at he
        exact EReal.bot_ne_coe e he
    have hyg := (mem_subdifferential_fenchelConjugate_iff hgp (hf.lowerSemicontinuous_slice x)
      (hf.convex_slice x) u y).mp hu
    obtain ⟨c, hfc⟩ := hyg.1
    have hs := (mem_subdifferential_iff_of_convex (hf.convex_slice x) hgp hfc).mp hyg
    have hlx := lagrangian_eq_of_slice_support (show f (WithLp.toLp 2 (x, u)) = c from hfc) hs
    have hlin := (mem_subdifferential_iff_of_convex_of_eq_coe
      (convex_epigraph_lagrangian_of_convex hc y) hlx).mp hv
    apply (mem_subdifferential_iff_of_convex hc hp (show f (WithLp.toLp 2 (x, u)) = c from hfc)).mpr
    intro q
    obtain ⟨⟨x', u'⟩, rfl⟩ := (WithLp.toLp_surjective 2) q
    rw [inner_toLp_sub_toLp]
    have h₁ := (hlin x').trans (iInf_le _ u')
    rw [ereal_coe_le_sub_coe_iff] at h₁
    convert h₁ using 2
    simp only [inner_sub_right]
    ring

/-- **Proposition 11.48**, the value statement: at a subgradient pair the
Lagrangian is finite and equals `f(x,u) - ⟨y,u⟩`. -/
theorem IsDualizingParameterization.lagrangian_eq_of_mem_subdifferential {φ : E → EReal}
    {f : WithLp 2 (E × P) → EReal} (hf : IsDualizingParameterization φ f)
    (hc : Convex ℝ (epigraph f)) {x v : E} {u y : P}
    (h : WithLp.toLp 2 (v, y) ∈ subdifferential f (WithLp.toLp 2 (x, u))) :
    (∃ a : ℝ, lagrangian f x y = a) ∧
      lagrangian f x y = f (WithLp.toLp 2 (x, u)) - (⟪y, u⟫_ℝ : EReal) := by
  obtain ⟨c, hfc⟩ := h.1
  have hall := (mem_subdifferential_iff_of_convex hc hf.isProper hfc).mp h
  have hs (u' : P) : ((c + ⟪y, u' - u⟫_ℝ : ℝ) : EReal) ≤ f (WithLp.toLp 2 (x, u')) := by
    have h' := hall (WithLp.toLp 2 (x, u'))
    simpa [inner_toLp_sub_toLp] using h'
  have hlx := lagrangian_eq_of_slice_support hfc hs
  exact ⟨⟨_, hlx⟩, by rw [hlx, hfc, EReal.coe_sub]⟩

end
end RW
