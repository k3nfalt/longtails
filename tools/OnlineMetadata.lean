import Lean

open Lean Meta

namespace OnlineMetadata

structure Entry where
  moduleName : Name
  theoremName : Name
  setupName : Name
  boundName : Name
  methodName : Option Name

def inspect : MetaM (Array Entry) := do
  let env ← getEnv
  let mut entries := #[]
  for moduleName in env.header.moduleNames, moduleData in env.header.moduleData do
    unless (`LongTailsOnline.Theorems).isPrefixOf moduleName do continue
    let mut found := #[]
    for info in moduleData.constants do
      let .thmInfo theoremInfo := info | continue
      unless (env.getModuleIdxFor? info.name).any
          (fun idx => env.header.moduleNames[idx.toNat]! == moduleName) do continue
      let isOnline ← forallTelescope theoremInfo.type fun _ body =>
        pure (body.isAppOfArity `OnlineTemplate.Guarantee 3 ||
          body.isAppOfArity `OnlineTemplate.Achievable 2)
      if isOnline then found := found.push theoremInfo
    unless found.size == 1 do
      throwError "{moduleName}: expected exactly one online theorem, found {found.size}"
    let theoremInfo := found[0]!
    unless theoremInfo.name.getString! == "result" do
      throwError "{moduleName}: online theorem must be named result"
    let isGuarantee := theoremInfo.type.isAppOfArity `OnlineTemplate.Guarantee 3
    unless isGuarantee || theoremInfo.type.isAppOfArity `OnlineTemplate.Achievable 2 do
      throwError "{moduleName}: result must have type Guarantee or Achievable without extra hypotheses"
    let args := theoremInfo.type.getAppArgs
    let .const setupName _ := args[0]! |
      throwError "{moduleName}: expected a named setup spec"
    let some setupIdx := env.getModuleIdxFor? setupName |
      throwError "{moduleName}: setup must come from an imported module"
    let setupModule := env.header.moduleNames[setupIdx.toNat]!
    unless (`LongTailsOnline.Setups).isPrefixOf setupModule &&
        setupName == setupModule ++ `spec do
      throwError "{moduleName}: setup must be <LongTailsOnline.Setups.Module>.spec"
    let .const boundName _ := args[if isGuarantee then 2 else 1]! |
      throwError "{moduleName}: expected a named bound definition"
    unless boundName == theoremInfo.name.getPrefix ++ `bound do
      throwError "{moduleName}: expected bound in the result namespace"
    let .defnInfo _ ← getConstInfo boundName |
      throwError "{moduleName}: bound must be a definition"
    let methodName ← if isGuarantee then do
        let .const methodName _ := args[1]! |
          throwError "{moduleName}: expected a named method definition"
        unless methodName == theoremInfo.name.getPrefix ++ `method do
          throwError "{moduleName}: expected method in the result namespace"
        let .defnInfo _ ← getConstInfo methodName |
          throwError "{moduleName}: method must be a definition"
        pure (some methodName)
      else pure none
    entries := entries.push ⟨moduleName, theoremInfo.name, setupName, boundName, methodName⟩
  return entries

end OnlineMetadata
