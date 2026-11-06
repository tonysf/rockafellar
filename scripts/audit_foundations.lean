/-
Focused foundation audit. Run only after rebuilding the changed modules and the
named Chapter 3 consumers. This script intentionally excludes Chapters 6 and 7.
It fails on missing declarations or axioms beyond the three standard axioms.
-/

import RockafellarWets.Chapter1.Defs
import RockafellarWets.Chapter1.Proximal
import RockafellarWets.Chapter3.ExtendedCancellationCompletion
import RockafellarWets.Chapter3.ExtendedProximalCancellationCompletion
import RockafellarWets.Chapter5.ProximalMappings
import RockafellarWets.Chapter3.EpiCancellation
import RockafellarWets.Chapter3.ERealFunctionShift
import RockafellarWets.Chapter3.ExtendedProximalCancellationExact
import Lean.Elab.Command
import Lean.Util.CollectAxioms

example : RW.IsProxBounded (fun _ : ℝ ↦ ((-1 : ℝ) : EReal)) :=
  RW.isProxBounded_const (-1)

example : 0 < RW.proxThreshold (fun _ : ℝ ↦ ((-1 : ℝ) : EReal)) :=
  (RW.isProxBounded_iff_pos_proxThreshold _).1 (RW.isProxBounded_const (-1))

example (lam : ℝ) (x : ℝ) :
    RW.proximalMappingEReal (fun _ : ℝ ↦ ⊤) lam x = ∅ := by
  change RW.argmin (RW.proximalObjectiveEReal (fun _ : ℝ ↦ ⊤) lam x) = ∅
  have hobj : RW.proximalObjectiveEReal (fun _ : ℝ ↦ ⊤) lam x =
      (fun _ : ℝ ↦ (⊤ : EReal)) := by
    funext w
    exact EReal.top_add_coe _
  rw [hobj, RW.argmin_const_top]

example (lam : ℝ) (x : ℝ) :
    RW.proximalMappingEReal (fun _ : ℝ ↦ ⊥) lam x = Set.univ := by
  simp [RW.proximalMappingEReal, RW.proximalObjectiveEReal, RW.argmin]

example (f : ℝ → EReal) (lam : ℝ) :
    RW.proxMappingEReal f lam = RW.proximalMappingEReal f lam := rfl

example (f : ℝ → EReal) (lam : ℝ) :
    RW.proxMappingEReal f lam = RW.paramArgmin (RW.proxIntegrand f lam) := rfl

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let audited : Array Lean.Name := #[
    ``RW.IsProxBounded,
    ``RW.proxThreshold,
    ``RW.isProxBounded_iff_pos_proxThreshold,
    ``RW.isProxBounded_of_bddBelow,
    ``RW.isProxBounded_const,
    ``RW.proximalObjectiveEReal,
    ``RW.moreauEnvelopeEReal,
    ``RW.moreauEnvelopeEReal_eq_iInf_proximalObjectiveEReal,
    ``RW.isProxBounded_iff_exists_moreauEnvelopeEReal,
    ``RW.proximalMappingEReal,
    ``RW.mem_proximalMappingEReal_iff,
    ``RW.exists_affine_minorant_gt_of_lt_of_convex_lsc_ereal,
    ``RW.corollary336_eq_of_moreauEnvelopeEReal_eq,
    ``RW.isProper_proximalObjectiveEReal,
    ``RW.lowerSemicontinuous_proximalObjectiveEReal,
    ``RW.isLevelCoercive_proximalObjectiveEReal_of_affineMinorant,
    ``RW.isLevelCoercive_proximalObjectiveEReal,
    ``RW.proximalMappingEReal_nonempty,
    ``RW.moreauEnvelopeEReal_finite,
    ``RW.mem_effectiveDomain_of_mem_proximalMappingEReal,
    ``RW.norm_sub_proximalEReal_le_two_mul,
    ``RW.HasLipschitzProximalSelectionEReal,
    ``RW.hasLipschitzProximalSelectionEReal,
    ``RW.exists_lt_add_coe,
    ``RW.continuousAt_ereal_const_add,
    ``RW.continuous_ereal_const_add,
    ``RW.lowerSemicontinuousAt_add_coe,
    ``RW.lowerSemicontinuous_add_coe,
    ``RW.upperSemicontinuous_valueFunction,
    ``RW.proxIntegrand,
    ``RW.proxIntegrand_apply,
    ``RW.moreauEnvelopeEReal_eq_valueFunction,
    ``RW.proxMappingEReal,
    ``RW.proxMappingEReal_eq_proximalMappingEReal,
    ``RW.proxMappingEReal_eq_paramArgmin,
    ``RW.mem_proxMappingEReal,
    ``RW.lowerSemicontinuous_proxIntegrand,
    ``RW.isProper_proxIntegrand,
    ``RW.valueFunction_proxIntegrand_lt_top,
    ``RW.exists_eventually_valueFunction_proxIntegrand_le,
    ``RW.upperSemicontinuous_valueFunction_proxIntegrand,
    ``RW.isLevelBoundedInXLocallyUniformly_proxIntegrand,
    ``RW.svLocallyBoundedAt_of_within_univ,
    ``RW.svLocallyBounded_proxMappingEReal,
    ``RW.svOsc_proxMappingEReal,
    ``RW.svOsc_and_svLocallyBounded_proxMappingEReal,
    ``RW.theorem334_eq_of_epiSum_eq,
    ``RW.moreauEnvelopeEReal_add_const,
    ``RW.proximalMappingEReal_add_const,
    ``RW.corollary337_eq_add_const_of_proximalMappingEReal_eq,
    ``RW.corollary337_proximalMappingEReal_eq_iff_eq_add_const]
  for name in audited do
    unless (← Lean.getEnv).contains name do
      throwError "Missing audited declaration: {name}"
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun ax ↦ !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "Unexpected axioms for {name}: {unexpected.toList}"
    Lean.logInfo m!"AXIOM-AUDIT {name}: {axioms.toList}"
  Lean.logInfo m!"Audited {audited.size} declarations; only propext, Classical.choice, and Quot.sound allowed."
