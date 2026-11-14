import CHS
import Lean.Util.CollectAxioms

/-!
# Exhaustive transitive axiom audit of public CHS declarations

The audit enumerates the imported environment, so newly exported source
declarations cannot be omitted accidentally from a hand-maintained list.
Each declaration is checked against the same three-axiom allow-list as the
accepted baseline.  This file introduces no mathematical declarations.
-/

set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, _) in env.constants do
    if name.toString.startsWith "CHS." && !name.isInternalDetail then
      names := names.push name
  names := names.qsort Name.lt
  for name in names do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless axiomName == ``propext || axiomName == ``Classical.choice ||
          axiomName == ``Quot.sound do
        throwError "Disallowed transitive axiom {axiomName} in {name}"
    let axiomText := String.intercalate "," ((axioms.qsort Name.lt).toList.map toString)
    logInfo m!"CHS_AXIOMS|{name}|{axiomText}"
  logInfo m!"CHS_AXIOMS_TOTAL|{names.size}"
