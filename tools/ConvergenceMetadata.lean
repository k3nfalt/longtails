import Lean

open Lean Meta

namespace ConvergenceMetadata

structure Entry where
  moduleName : Name
  theoremName : Name
  setupName : Name
  budgetName : Name
  online : Bool
  indexed : Bool

def inspect : MetaM (Array Entry) := do
  let env ← getEnv
  let mut entries := #[]
  for moduleName in env.header.moduleNames, moduleData in env.header.moduleData do
    unless (`LongTails.Theorems).isPrefixOf moduleName do continue
    let mut found := #[]
    for info in moduleData.constants do
      let .thmInfo theoremInfo := info | continue
      unless (env.getModuleIdxFor? info.name).any
          (fun idx => env.header.moduleNames[idx.toNat]! == moduleName) do continue
      let isConvergence ← forallTelescope theoremInfo.type fun _ body =>
        pure (body.isAppOfArity `OracleTemplate.Convergence 2 ||
          body.isAppOfArity `OracleTemplate.OnlineConvergence 2)
      if isConvergence then found := found.push theoremInfo
    unless found.size == 1 do
      throwError "{moduleName}: expected exactly one convergence theorem, found {found.size}"
    let theoremInfo := found[0]!
    unless theoremInfo.name.getString! == "result" do
      throwError "{moduleName}: convergence theorem must be named result"
    let entry ← forallTelescope theoremInfo.type fun indices body => do
      for index in indices do
        unless (← isDefEq (← inferType index) (mkConst ``Nat)) do
          throwError "{moduleName}: result must be without extra hypotheses; indices must be natural numbers"
      let online := body.isAppOfArity `OracleTemplate.OnlineConvergence 2
      if online && !indices.isEmpty then
        throwError "{moduleName}: indexed OnlineConvergence families are not supported"
      unless online || body.isAppOfArity `OracleTemplate.Convergence 2 do
        throwError "{moduleName}: expected Convergence setup budget or OnlineConvergence setup bound"
      let args := body.getAppArgs
      unless args[0]!.getAppArgs == indices && args[1]!.getAppArgs == indices do
        throwError "{moduleName}: setup and budget must use exactly the result indices in order"
      let .const setupName _ := args[0]!.getAppFn |
        throwError "{moduleName}: expected a named setup spec"
      let .const budgetName _ := args[1]!.getAppFn |
        throwError "{moduleName}: expected a named budget definition"
      pure (setupName, budgetName, online, !indices.isEmpty)
    let (setupName, budgetName, online, indexed) := entry
    let some setupIdx := env.getModuleIdxFor? setupName |
      throwError "{moduleName}: setup must come from an imported module"
    let setupModule := env.header.moduleNames[setupIdx.toNat]!
    unless (`LongTails.Setups).isPrefixOf setupModule &&
        setupName == setupModule ++ `spec do
      throwError "{moduleName}: setup must be <LongTails.Setups.Module>.spec"
    let parameterName := if online then `bound else `budget
    unless budgetName == theoremInfo.name.getPrefix ++ parameterName do
      throwError "{moduleName}: expected {parameterName} in the result namespace"
    let .defnInfo _ ← getConstInfo budgetName |
      throwError "{moduleName}: budget must be a definition"
    entries := entries.push ⟨moduleName, theoremInfo.name, setupName, budgetName, online, indexed⟩
  return entries

end ConvergenceMetadata
