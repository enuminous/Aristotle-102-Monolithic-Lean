import Lean
import RequestProject.Coherence
import RequestProject.Dynamics
import RequestProject.Fields
import RequestProject.Golden
import RequestProject.Main
import RequestProject.Metrics

/-! Audit every safe declaration defined in the listed project modules. -/

open Lean in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`RequestProject.Coherence, `RequestProject.Dynamics, `RequestProject.Fields, `RequestProject.Golden, `RequestProject.Main, `RequestProject.Metrics]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut theoremCount := 0
  for (name, info) in env.constants.toList do
    let isProject := match env.getModuleIdxFor? name with
      | some idx => modules.contains env.header.moduleNames[idx.toNat]!
      | none => (`AuditProbe).isPrefixOf (privateToUserName name)
    if isProject && !info.isUnsafe then
      count := count + 1
      if info matches .thmInfo _ then
        theoremCount := theoremCount + 1
      for ax in (← collectAxioms name) do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} used by {name}"
  if count == 0 then
    throwError "Audit matched no project declarations"
  logInfo m!"Axiom audit passed: {count} safe declarations, {theoremCount} theorem declarations (including generated lemmas)."
