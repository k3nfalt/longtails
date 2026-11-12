import Lean

open Lean Meta

namespace ConvergenceMetadata

structure Entry where
  moduleName : Name
  theoremName : Name
  setupName : Name
  budgetName : Name
  online : Bool
  lower : Bool

def inspect (includeLowerBounds : Bool := false) : MetaM (Array Entry) := do
  let env ← getEnv
  let mut entries := #[]
  for moduleName in env.header.moduleNames, moduleData in env.header.moduleData do
    let lower := (`LongTails.LowerBounds).isPrefixOf moduleName
    unless (`LongTails.Theorems).isPrefixOf moduleName || (includeLowerBounds && lower) do
      continue
    let mut found := #[]
    for info in moduleData.constants do
      let .thmInfo theoremInfo := info | continue
      unless (env.getModuleIdxFor? info.name).any
          (fun idx => env.header.moduleNames[idx.toNat]! == moduleName) do continue
      let isConvergence ← forallTelescope theoremInfo.type fun _ body =>
        pure (body.isAppOfArity `OracleTemplate.Convergence 2 ||
          body.isAppOfArity `OracleTemplate.OnlineConvergence 2 ||
          body.isAppOfArity `OracleTemplate.NonConvergence 2)
      if isConvergence then found := found.push theoremInfo
    unless found.size == 1 do
      throwError "{moduleName}: expected exactly one convergence theorem, found {found.size}"
    let theoremInfo := found[0]!
    unless theoremInfo.name.getString! == "result" do
      throwError "{moduleName}: convergence theorem must be named result"
    let online := theoremInfo.type.isAppOfArity `OracleTemplate.OnlineConvergence 2
    let nonconvergence := theoremInfo.type.isAppOfArity `OracleTemplate.NonConvergence 2
    unless nonconvergence || online || theoremInfo.type.isAppOfArity `OracleTemplate.Convergence 2 do
      throwError "{moduleName}: result must have type Convergence setup budget or OnlineConvergence setup bound or NonConvergence setup budget without extra hypotheses"
    unless lower == nonconvergence do
      throwError "{moduleName}: NonConvergence results belong in LowerBounds; convergence results belong in Theorems"
    let args := theoremInfo.type.getAppArgs
    let .const setupName _ := args[0]! |
      throwError "{moduleName}: expected a named setup spec"
    let some setupIdx := env.getModuleIdxFor? setupName |
      throwError "{moduleName}: setup must come from an imported module"
    let setupModule := env.header.moduleNames[setupIdx.toNat]!
    unless (`LongTails.Setups).isPrefixOf setupModule &&
        setupName == setupModule ++ `spec do
      throwError "{moduleName}: setup must be <LongTails.Setups.Module>.spec"
    let .const budgetName _ := args[1]! |
      throwError "{moduleName}: expected a named budget definition"
    let parameterName := if online then `bound else `budget
    unless budgetName == theoremInfo.name.getPrefix ++ parameterName do
      throwError "{moduleName}: expected {parameterName} in the result namespace"
    let .defnInfo _ ← getConstInfo budgetName |
      throwError "{moduleName}: budget must be a definition"
    entries := entries.push ⟨moduleName, theoremInfo.name, setupName, budgetName, online, lower⟩
  return entries

end ConvergenceMetadata
