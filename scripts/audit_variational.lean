/-
Audit every kernel declaration defined by Chapters 1–14, including private
helpers and generated declarations, and all of their transitive dependencies.

Run after rebuilding the project:
  lake build
  lake env lean scripts/audit_variational.lean

Only the three standard Lean axioms are permitted. In particular, a proof
depending on sorryAx, an additional axiom, or native_decide fails this audit.
-/

import RockafellarWets.Chapter1
import RockafellarWets.Chapter2
import RockafellarWets.Chapter3
import RockafellarWets.Chapter4
import RockafellarWets.Chapter5
import RockafellarWets.Chapter6
import RockafellarWets.Chapter7
import RockafellarWets.Chapter8
import RockafellarWets.Chapter9
import RockafellarWets.Chapter10
import RockafellarWets.Chapter11
import RockafellarWets.Chapter12
import RockafellarWets.Chapter13
import RockafellarWets.Chapter14
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let roots := #[`RockafellarWets.Chapter1, `RockafellarWets.Chapter2,
    `RockafellarWets.Chapter3, `RockafellarWets.Chapter4, `RockafellarWets.Chapter5,
    `RockafellarWets.Chapter6, `RockafellarWets.Chapter7,
    `RockafellarWets.Chapter8, `RockafellarWets.Chapter9, `RockafellarWets.Chapter10,
    `RockafellarWets.Chapter11, `RockafellarWets.Chapter12,
    `RockafellarWets.Chapter13, `RockafellarWets.Chapter14]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  let mut modules : NameSet := {}
  for root in roots do
    let mut count := 0
    for (name, idx) in env.const2ModIdx do
      let mod := env.header.moduleNames[idx.toNat]!
      if root.isPrefixOf mod then
        names := names.push name
        modules := modules.insert mod
        count := count + 1
    unless count > 0 do
      throwError "No kernel declarations found for {root}"
    logInfo m!"{root}: {count} kernel declarations"
  let (_, result) := (names.forM CollectAxioms.collect |>.run env).run {}
  let unexpected := result.axioms.filter fun ax ↦ !allowed.contains ax
  unless unexpected.isEmpty do
    throwError "Unexpected axiom dependencies: {unexpected.toList}"
  logInfo m!"Audited {names.size} kernel declarations in {modules.size} modules. Axioms: {result.axioms.toList}."
