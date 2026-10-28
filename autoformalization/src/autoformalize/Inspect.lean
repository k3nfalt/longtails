import Lean
open Lean Elab Command

def afRangeJson (r : DeclarationRange) : Json := Json.mkObj [
  ("start_line", toJson r.pos.line), ("start_column", toJson r.pos.column),
  ("end_line", toJson r.endPos.line), ("end_column", toJson r.endPos.column)]

partial def afExprTree (e : Expr) : Json :=
  let node (kind : String) (fields : List (String × Json)) := Json.mkObj (("kind", toJson kind) :: fields)
  match e with
  | .bvar i => node "bvar" [("index", toJson i)]
  | .fvar i => node "fvar" [("name", toJson i.name.toString)]
  | .mvar i => node "mvar" [("name", toJson i.name.toString)]
  | .sort u => node "sort" [("level", toJson (repr u).pretty)]
  | .const n us => node "const" [("name", toJson n.toString), ("levels", toJson (us.map fun u => (repr u).pretty))]
  | .app f a => node "app" [("function", afExprTree f), ("argument", afExprTree a)]
  | .lam n t b bi => node "lambda" [("name", toJson n.toString), ("binder", toJson (repr bi).pretty), ("type", afExprTree t), ("body", afExprTree b)]
  | .forallE n t b bi => node "forall" [("name", toJson n.toString), ("binder", toJson (repr bi).pretty), ("type", afExprTree t), ("body", afExprTree b)]
  | .letE n t v b nd => node "let" [("name", toJson n.toString), ("type", afExprTree t), ("value", afExprTree v), ("body", afExprTree b), ("nondependent", toJson nd)]
  | .lit v => node "literal" [("value", toJson (repr v).pretty)]
  | .mdata _ b => node "metadata" [("body", afExprTree b)]
  | .proj n i b => node "projection" [("name", toJson n.toString), ("index", toJson i), ("body", afExprTree b)]

def afKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def afValue (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .thmInfo _ => none
  | _ => ci.value? (allowOpaque := true)

def afUsed (ci : ConstantInfo) : Array Name := Id.run do
  let mut names := ci.type.getUsedConstants
  if let some value := afValue ci then
    for n in value.getUsedConstants do
      if !names.contains n then names := names.push n
  return names.qsort (fun a b => a.toString < b.toString)

def afRecord (name : Name) (trees : Bool) : CommandElabM Json := do
  let env ← getEnv
  let some ci := env.find? name | throwError "Unknown requested declaration {name}"
  let owner := (env.getModuleIdxFor? name).map (fun i => env.header.moduleNames[i.toNat]!)
  let ranges ← findDeclarationRanges? name
  let axioms ← collectAxioms name
  let displayed ← liftTermElabM (Lean.Meta.ppExpr ci.type)
  let value := afValue ci
  let mut fields := [
    ("name", toJson name.toString),
    ("module", toJson (owner.getD env.mainModule).toString),
    ("kind", toJson (afKind ci)),
    ("type_text", toJson displayed.pretty),
    ("type_repr", toJson (repr ci.type).pretty),
    ("value_repr", value.map (fun e => toJson (repr e).pretty) |>.getD Json.null),
    ("used", toJson ((afUsed ci).map Name.toString)),
    ("proof_used", toJson (((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]).qsort (fun a b => a.toString < b.toString) |>.map Name.toString)),
    ("axioms", toJson ((axioms.qsort (fun a b => a.toString < b.toString)).map Name.toString)),
    ("range", ranges.map (afRangeJson ·.range) |>.getD Json.null),
    ("selection", ranges.map (afRangeJson ·.selectionRange) |>.getD Json.null)]
  if (getStructureInfo? env name).isSome then
    fields := fields ++ [("structure_fields", toJson ((getStructureFieldsFlattened env name false).map Name.toString))]
  if trees then
    fields := fields ++ [("type_tree", afExprTree ci.type), ("value_tree", value.map afExprTree |>.getD Json.null)]
  return Json.mkObj fields

def afInspect (names : Array Name) (modules : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut selected := names
  for n in names do
    unless env.contains n do throwError "Unknown requested declaration {n}"
  for (n, _) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if modules.contains env.header.moduleNames[i.toNat]! && !selected.contains n then
        selected := selected.push n
  selected := selected.qsort (fun a b => a.toString < b.toString)
  let mut providers : Array Name := #[]
  for n in selected do
    for p in afUsed (env.find? n).get! do
      if !selected.contains p && !providers.contains p then providers := providers.push p
  providers := providers.qsort (fun a b => a.toString < b.toString)
  let mut deeper : Array Name := #[]
  for p in providers do
    for n in afUsed (env.find? p).get! do
      if !selected.contains n && !providers.contains n && !deeper.contains n then deeper := deeper.push n
  let decls ← selected.mapM (afRecord · true)
  let providerRecords ← providers.mapM (afRecord · false)
  let record := Json.mkObj [("declarations", toJson decls), ("providers", toJson providerRecords),
    ("unexpanded_dependencies", toJson ((deeper.qsort (fun a b => a.toString < b.toString)).map Name.toString))]
  logInfo m!"AF_INVENTORY {record.compress}"

def afParseProof (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `term text with
  | .error msg => throwError "Invalid proof term: {msg}"
  | .ok stx =>
    unless stx.getKind == `Lean.Parser.Term.byTactic do throwError "Proof body must be a by tactic term"
    logInfo "AF_PROOF_PARSED"
