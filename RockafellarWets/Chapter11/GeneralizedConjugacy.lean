/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Conjugacy for an arbitrary real-valued pairing
-/

import RockafellarWets.Chapter11.FenchelConjugate

open Set

namespace RW

variable {X Y : Type*}

/-- The generalized conjugate with respect to a finite-valued coupling. -/
noncomputable def pairingConjugate (Φ : X → Y → ℝ) (f : X → EReal) (y : Y) : EReal :=
  ⨆ x : X, (Φ x y : EReal) - f x

/-- A pairing envelope is an arbitrary supremum of finite translates of sections of the coupling. -/
def IsPairingEnvelope (Φ : X → Y → ℝ) (f : X → EReal) : Prop :=
  ∃ S : Set (Y × ℝ), ∀ x, f x = ⨆ p : S, ((Φ x p.val.1 + p.val.2 : ℝ) : EReal)

private theorem pairing_sub_le_iff (r : ℝ) (a b : EReal) :
    (r : EReal) - a ≤ b ↔ (r : EReal) - b ≤ a := by
  cases a <;> cases b <;> simp [← EReal.coe_sub]
  constructor <;> intro <;> linarith

/-- The two generalized conjugate operators form an antitone Galois connection. -/
theorem pairingConjugate_le_iff (Φ : X → Y → ℝ) (f : X → EReal) (g : Y → EReal) :
    pairingConjugate Φ f ≤ g ↔ pairingConjugate (Function.swap Φ) g ≤ f := by
  constructor
  · intro h x
    exact iSup_le fun y ↦ (pairing_sub_le_iff _ _ _).mp ((le_iSup _ x).trans (h y))
  · intro h y
    exact iSup_le fun x ↦ (pairing_sub_le_iff _ _ _).mp ((le_iSup _ y).trans (h x))

theorem pairingConjugate_antitone (Φ : X → Y → ℝ) : Antitone (pairingConjugate Φ) :=
  fun _ _ h _ ↦ iSup_mono fun x ↦ EReal.sub_le_sub le_rfl (h x)

/-- Every generalized biconjugate minorizes its primal function. -/
theorem pairingBiconjugate_le (Φ : X → Y → ℝ) (f : X → EReal) :
    pairingConjugate (Function.swap Φ) (pairingConjugate Φ f) ≤ f :=
  (pairingConjugate_le_iff Φ f _).mp le_rfl

/-- **11.63**. Every generalized conjugate is an envelope, even for a function
taking either infinite value. -/
theorem isPairingEnvelope_conjugate (Φ : X → Y → ℝ) (f : X → EReal) :
    IsPairingEnvelope (Function.swap Φ) (pairingConjugate Φ f) := by
  let S := {p : X × ℝ | (p.2 : EReal) ≤ -f p.1}
  refine ⟨S,fun y ↦ le_antisymm (iSup_le fun x ↦ ?_) (iSup_le fun p ↦ ?_)⟩
  · by_contra! h
    obtain ⟨b,hb,hb'⟩ := EReal.exists_between_coe_real h
    let a := b - Φ x y
    have ha : (a : EReal) ≤ -f x := by
      cases he : f x with
      | bot => simp
      | top => simp [he] at hb'
      | coe u =>
        rw [he,← EReal.coe_sub,EReal.coe_lt_coe_iff] at hb'
        rw [← EReal.coe_neg,EReal.coe_le_coe_iff]
        dsimp [a]
        linarith
    have hle := le_iSup (fun p : S ↦ ((Φ p.val.1 y + p.val.2 : ℝ) : EReal)) (⟨(x,a),ha⟩ : S)
    exact (not_le_of_gt hb) (by simpa [a] using hle)
  · have hp : (p.val.2 : EReal) ≤ -f p.val.1 := p.property
    exact (show ((Φ p.val.1 y + p.val.2 : ℝ) : EReal) ≤ (Φ p.val.1 y : EReal) - f p.val.1 by
      rw [EReal.coe_add, sub_eq_add_neg]; exact add_le_add_right hp _).trans
      (le_iSup (fun x : X ↦ (Φ x y : EReal) - f x) p.val.1)

/-- The pairing envelopes are exactly the fixed points of biconjugation. -/
theorem isPairingEnvelope_iff_biconjugate (Φ : X → Y → ℝ) (f : X → EReal) :
    IsPairingEnvelope Φ f ↔ pairingConjugate (Function.swap Φ) (pairingConjugate Φ f) = f := by
  constructor
  · rintro ⟨S,hS⟩
    apply le_antisymm (pairingBiconjugate_le Φ f)
    intro x
    rw [hS x]
    apply iSup_le
    intro p
    have hminor (z : X) : ((Φ z p.val.1 + p.val.2 : ℝ) : EReal) ≤ f z := by
      rw [hS z]
      exact le_iSup (fun q : S ↦ ((Φ z q.val.1 + q.val.2 : ℝ) : EReal)) p
    have hd : pairingConjugate Φ f p.val.1 ≤ ((-p.val.2 : ℝ) : EReal) := by
      apply iSup_le
      intro z
      apply (pairing_sub_le_iff _ _ _).mpr
      simpa only [← EReal.coe_sub,sub_neg_eq_add] using hminor z
    apply le_iSup_of_le p.val.1
    have ha := EReal.sub_le_sub (le_refl (Φ x p.val.1 : EReal)) hd
    simpa only [Function.swap,← EReal.coe_sub,sub_neg_eq_add] using ha
  · intro h
    rw [← h]
    exact isPairingEnvelope_conjugate (Function.swap Φ) _

/-- **11.63**. The biconjugate is the greatest pairing envelope below the given function. -/
theorem pairingBiconjugate_isGreatest (Φ : X → Y → ℝ) (f : X → EReal) :
    IsGreatest {h | IsPairingEnvelope Φ h ∧ h ≤ f}
      (pairingConjugate (Function.swap Φ) (pairingConjugate Φ f)) := by
  refine ⟨⟨isPairingEnvelope_conjugate (Function.swap Φ) _,pairingBiconjugate_le _ _⟩,?_⟩
  rintro h ⟨he,hf⟩
  have hmono := pairingConjugate_antitone (Function.swap Φ) (pairingConjugate_antitone Φ hf)
  rwa [(isPairingEnvelope_iff_biconjugate Φ h).mp he] at hmono

/-- **11.63**, the same two facts for a function on the second space: its
conjugate is a pairing envelope on the first space. -/
theorem isPairingEnvelope_conjugate_swap (Φ : X → Y → ℝ) (g : Y → EReal) :
    IsPairingEnvelope Φ (pairingConjugate (Function.swap Φ) g) :=
  isPairingEnvelope_conjugate (Function.swap Φ) g

/-- **11.63**, the biconjugate of a function on the second space is the
greatest envelope on that space below it. -/
theorem pairingBiconjugate_isGreatest_swap (Φ : X → Y → ℝ) (g : Y → EReal) :
    IsGreatest {h | IsPairingEnvelope (Function.swap Φ) h ∧ h ≤ g}
      (pairingConjugate Φ (pairingConjugate (Function.swap Φ) g)) :=
  pairingBiconjugate_isGreatest (Function.swap Φ) g

/-- The order-reversing bijection between the envelope functions on each side of the pairing. -/
noncomputable def pairingEnvelopeEquiv (Φ : X → Y → ℝ) :
    {f // IsPairingEnvelope Φ f} ≃ {g // IsPairingEnvelope (Function.swap Φ) g} where
  toFun f := ⟨pairingConjugate Φ f.val,isPairingEnvelope_conjugate Φ _⟩
  invFun g := ⟨pairingConjugate (Function.swap Φ) g.val,isPairingEnvelope_conjugate (Function.swap Φ) _⟩
  left_inv f := Subtype.ext ((isPairingEnvelope_iff_biconjugate Φ _).mp f.property)
  right_inv g := Subtype.ext ((isPairingEnvelope_iff_biconjugate (Function.swap Φ) _).mp g.property)

/-- Both directions of the correspondence are given by the two conjugacy formulas. -/
theorem pairingEnvelopeEquiv_formulas (Φ : X → Y → ℝ) (f : {f // IsPairingEnvelope Φ f}) :
    (∀ y, (pairingEnvelopeEquiv Φ f).val y = ⨆ x, (Φ x y : EReal) - f.val x) ∧
      ∀ x, f.val x = ⨆ y, (Φ x y : EReal) - (pairingEnvelopeEquiv Φ f).val y := by
  refine ⟨fun y ↦ rfl,fun x ↦ ?_⟩
  exact (congrFun ((isPairingEnvelope_iff_biconjugate Φ _).mp f.property) x).symm

end RW
