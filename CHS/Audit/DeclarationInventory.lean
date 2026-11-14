import CHS

/-! Public declaration names and their actual imported source modules. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let mut names : Array Name := #[]
  for (name, _) in env.constants do
    if !name.isInternalDetail then
      if let some index := env.getModuleIdxFor? name then
        if (`CHS).isPrefixOf modules[index.toNat]! then
          names := names.push name
  names := names.qsort Name.lt
  for name in names do
    let some index := env.getModuleIdxFor? name | throwError "Missing module for {name}"
    logInfo m!"CHS_DECL|{name}|{modules[index.toNat]!}"
  logInfo m!"CHS_DECL_TOTAL|{names.size}"
