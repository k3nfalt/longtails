import LeanTeX.Basic
import LeanTeX.LatexChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

open Lean Meta LeanTeX

namespace TheoremDescriptions

private def symbol (s : String) : String :=
  (String.join (s.toList.map fun c =>
    let latex := c.toLatex
    if latex.startsWith "\\" then latex ++ " " else latex)).trimAscii.toString

@[latex_pp fvar] def variablePrinter : LatexPrinter
  | .fvar id => return .atomString (symbol (← id.getDecl).userName.toString)
  | _ => failure

@[latex_pp lit] def literalPrinter : LatexPrinter
  | .lit (.natVal n) => return .atomString (toString n)
  | _ => failure

@[latex_pp mdata] def metadataPrinter : LatexPrinter
  | .mdata _ e => latexPP e
  | _ => failure

@[latex_pp letE] def letPrinter : LatexPrinter
  | .letE _ _ value body _ => latexPP (body.instantiate1 value)
  | _ => failure

private def sized (data : LatexData) : LatexData :=
  match data with
  | .Atom latex bigness sup sub => .Atom latex (max 1 bigness) sup sub
  | .Row latex lbp rbp bigness => .Row latex lbp rbp (max 1 bigness)

private def binary (args : Array Expr) (op : String) (bp : Nat)
    (assoc : Associativity) : LatexPrinterM LatexData := do
  let a ← latexPP args[args.size - 2]!
  let b ← latexPP args.back!
  return (sized a).protectRight bp ++ LatexData.binOp op assoc bp ++ (sized b).protectLeft bp

@[latex_pp app] def applicationPrinter : LatexPrinter := fun e => do
  let name := e.getAppFn.constName!
  let args := e.getAppArgs
  match name with
  | ``ite =>
    return .ofString ("\\begin{cases} " ++ (← latexPP args[3]!).latex.1 ++
      " & " ++ (← latexPP args[1]!).latex.1 ++ " \\\\ " ++
      (← latexPP args[4]!).latex.1 ++ " & \\mathrm{otherwise} \\end{cases}")
  | ``OfNat.ofNat => latexPP args[1]!
  | ``Nat.cast | ``NatCast.natCast | ``PNat.val => latexPP args.back!
  | ``LE.le => binary args " \\leq " 50 .none
  | ``HAdd.hAdd => binary args " + " 65 .left
  | ``HSub.hSub => binary args " - " 65 .left
  | ``Neg.neg => return .ofString ("-" ++ ((sized (← latexPP args.back!)).protectLeft 75).latex.1)
  | ``Inv.inv => return .frac (.atomString "1") (← latexPP args.back!)
  | ``HMul.hMul => binary args " \\cdot " 70 .left
  | ``HDiv.hDiv => return .frac (← latexPP args[args.size - 2]!) (← latexPP args.back!)
  | ``HPow.hPow => return (sized (← latexPP args[args.size - 2]!)).sup (← latexPP args.back!)
  | ``Norm.norm => return .atomString ("\\left\\lVert " ++
      (← latexPP args.back!).latex.1 ++ " \\right\\rVert")
  | ``Real.sqrt => return .ofString ("\\sqrt{" ++ (← latexPP args.back!).latex.1 ++ "}")
  | ``Real.log => return .ofString ("\\log\\left(" ++
      (← latexPP args.back!).latex.1 ++ "\\right)")
  | ``Real.logb => return .ofString ("\\log_{" ++
      (← latexPP args[0]!).latex.1 ++ "}\\left(" ++
      (← latexPP args[1]!).latex.1 ++ "\\right)")
  | ``Real.exp => return .ofString ("\\exp\\left(" ++
      (← latexPP args.back!).latex.1 ++ "\\right)")
  | ``Nat.sqrt => return .ofString ("\\left\\lfloor\\sqrt{" ++
      (← latexPP args.back!).latex.1 ++ "}\\right\\rfloor")
  | ``Nat.log2 => return .ofString ("\\operatorname{log2}\\left(" ++
      (← latexPP args.back!).latex.1 ++ "\\right)")
  | ``Finset.sum =>
    guard (args[args.size - 2]!.getAppFn.constName! == ``Finset.univ)
    let fn ← ensureLam args.back! none
    guard (fn.bindingDomain!.isAppOfArity ``Fin 1)
    let bound ← latexPP fn.bindingDomain!.getAppArgs.back!
    withBindingBodyUnusedName fn fun index body => do
      return .ofString ("\\left(\\sum_{" ++ symbol index.toString ++ "=0}^{" ++
        bound.latex.1 ++ "-1} " ++ (← latexPP body).latex.1 ++ "\\right)")
  | ``Nat.ceil => return .ofString ("\\left\\lceil " ++ (← latexPP args.back!).latex.1 ++ " \\right\\rceil_{+}")
  | ``Nat.clog =>
    return .ofString ("\\operatorname{clog}_{" ++ (← latexPP args[0]!).latex.1 ++
      "}\\left(" ++ (← latexPP args[1]!).latex.1 ++ "\\right)")
  | ``Module.finrank =>
    guard (args[0]!.isConstOf ``Real)
    return .ofString ("\\dim_{\\mathbb{R}}\\left(" ++
      (← latexPP args[1]!).latex.1 ++ "\\right)")
  | ``min | ``max =>
    let op := if name == ``min then "\\min" else "\\max"
    return .ofString (op ++ "\\left\\{ " ++ (← latexPP args[args.size - 2]!).latex.1 ++
      ", " ++ (← latexPP args.back!).latex.1 ++ " \\right\\}")
  | _ =>
    let some projection ← getProjectionFnInfo? name | failure
    let structName := projection.ctorName.getPrefix
    guard (structName.getString! == "Params" || structName.getString! == "Public")
    let mut parameter := args[projection.numParams]!
    while !parameter.isFVar do
      let parentName := parameter.getAppFn.constName!
      let some parent ← getProjectionFnInfo? parentName | failure
      guard ((getStructureParentInfo (← getEnv) parent.ctorName.getPrefix).any
        (fun info => info.projFn == parentName) ||
        (parent.ctorName.getPrefix.getString! == "Params" &&
          (← inferType parameter).getAppFn.constName! == structName))
      parameter := parameter.getAppArgs[parent.numParams]!
    let mut result := symbol name.getString!
    for arg in args.toList.drop (projection.numParams + 1) do
      result := result ++ "\\left(" ++ (← latexPP arg).latex.1 ++ "\\right)"
    return .atomString result

def budgetLatex (value : Expr) : MetaM String := do
  lambdaTelescope value fun _ body => do
    let result ← run_latexPP body {}
    if (result.splitOn "\\text").length > 1 || (result.splitOn "\\operatorname{Lean}").length > 1 then
      throwError "Unsupported budget notation in LeanTeX: {result}"
    return result

end TheoremDescriptions
