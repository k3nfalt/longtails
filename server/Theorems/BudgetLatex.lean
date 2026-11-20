import LeanTeX.Basic
import LeanTeX.LatexChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Finset.Lattice.Fold
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

@[latex_pp const] def clockBitsPrinter : LatexPrinter
  | e@(.const `DistributedTemplate.clockBits _) => do latexPP (← whnf e)
  | _ => failure

@[latex_pp mdata] def metadataPrinter : LatexPrinter
  | .mdata _ e => latexPP e
  | _ => failure

private partial def definitionLatex (lhs : String) (value : Expr) : LatexPrinterM String := do
  if value.isLambda then
    withBindingBodyUnusedName value fun arg body =>
      definitionLatex (lhs ++ "\\left(" ++ symbol arg.toString ++ "\\right)") body
  else
    return lhs ++ " = " ++ (← latexPP value).latex.1

private partial def letBlock (e : Expr) (defs : Array String) : LatexPrinterM LatexData := do
  match e.consumeMData with
  | .letE name type value body _ =>
    let name ← withReader (fun cfg => { cfg with allowShadowing := false }) (getUnusedName name body)
    let definition ← definitionLatex (symbol name.toString) value
    withLetDecl name type value fun x => letBlock (body.instantiate1 x) (defs.push definition)
  | _ =>
    let main ← latexPP e
    return .ofString ("\\begin{aligned} &" ++ main.latex.1 ++
      " \\\\ &\\text{where}\\quad " ++ String.intercalate " \\\\ &\\phantom{\\text{where}\\quad} " defs.toList ++
      "\\end{aligned}")

@[latex_pp letE] def letPrinter : LatexPrinter := fun e => letBlock e #[]

private def sized (data : LatexData) : LatexData :=
  match data with
  | .Atom latex bigness sup sub => .Atom latex (max 1 bigness) sup sub
  | .Row latex lbp rbp bigness => .Row latex lbp rbp (max 1 bigness)

private def binary (args : Array Expr) (op : String) (bp : Nat)
    (assoc : Associativity) : LatexPrinterM LatexData := do
  let a ← latexPP args[args.size - 2]!
  let b ← latexPP args.back!
  return (sized a).protectRight bp ++ LatexData.binOp op assoc bp ++ (sized b).protectLeft bp

private def namedApplication (e : Expr) : LatexPrinterM LatexData := do
  let name := e.getAppFn.constName!
  guard ((`LongTails.Theorems).isPrefixOf name)
  let kinds ← getParamKinds e
  let mut arguments := #[]
  for arg in e.getAppArgs, kind in kinds do
    if kind.isRegularExplicit && !(← isProof arg) then
      arguments := arguments.push (← latexPP arg).latex.1
  return .atomString ("\\operatorname{" ++ name.getString! ++ "}" ++
    (if arguments.isEmpty then "" else "\\left(" ++ String.intercalate ", " arguments.toList ++ "\\right)"))

@[latex_pp const] def namedConstantPrinter : LatexPrinter := namedApplication

@[latex_pp app] def applicationPrinter : LatexPrinter := fun e => do
  if e.getAppFn.isFVar then
    let mut result := (← latexPP e.getAppFn).latex.1
    for arg in e.getAppArgs do
      result := result ++ "\\left(" ++ (← latexPP arg).latex.1 ++ "\\right)"
    return .atomString result
  if e.getAppFn.isLambda then return ← latexPP e.headBeta
  let .const name _ := e.getAppFn | failure
  let args := e.getAppArgs
  match name with
  | ``Exists =>
    withBindingBodyUnusedName' args.back! none fun n body => do
      let domain ← if args[0]!.isConstOf ``Real then pure "\\mathbb{R}" else pure (← latexPP args[0]!).latex.1
      return .ofString ("\\exists " ++ symbol n.toString ++ "\\in " ++ domain ++ ",\\;" ++ (← latexPP body).latex.1)
  | ``Iff => binary args " \\leftrightarrow " 20 .none
  | ``LT.lt => binary args " < " 50 .none
  | ``And => binary args " \\land " 35 .right
  | ``Exists.choose =>
    return .atomString ("\\operatorname{choose}\\left(" ++ (← latexPP args.back!).latex.1 ++ "\\right)")
  | ``dite =>
    let cond := (← latexPP args[1]!).latex.1
    withBindingBodyUnusedName args[3]! fun h yes => do
      withBindingBodyUnusedName args[4]! fun hn no => do
        let otherwise := if args[4]!.bindingBody!.hasLooseBVar 0 then
            symbol hn.toString ++ " : \\neg\\left(" ++ cond ++ "\\right)"
          else "\\mathrm{otherwise}"
        return .ofString ("\\begin{cases} " ++ (← latexPP yes).latex.1 ++ " & " ++
          symbol h.toString ++ " : " ++ cond ++ " \\\\ " ++ (← latexPP no).latex.1 ++
          " & " ++ otherwise ++ " \\end{cases}")
  | ``ite =>
    return .ofString ("\\begin{cases} " ++ (← latexPP args[3]!).latex.1 ++
      " & " ++ (← latexPP args[1]!).latex.1 ++ " \\\\ " ++
      (← latexPP args[4]!).latex.1 ++ " & \\mathrm{otherwise} \\end{cases}")
  | ``iInf =>
    let fn ← ensureLam args.back! none
    let domain := fn.bindingDomain!
    guard (domain.isAppOfArity ``Subtype 2)
    let predicate := domain.getAppArgs.back!
    let index ← getUnusedName fn.bindingName! fn.bindingBody!
    withLocalDeclD index domain fun x => do
      let body := fn.bindingBody!.instantiate1 x
      let value ← mkAppM ``Subtype.val #[x]
      let condition ← latexPP (mkApp predicate value).headBeta
      let base ← latexPP domain.getAppArgs[0]!
      return .ofString ("\\inf_{\\substack{" ++ symbol index.toString ++ "\\in " ++
        base.latex.1 ++ "\\\\ " ++ condition.latex.1 ++ "}}\\left(" ++
        (← latexPP body).latex.1 ++ "\\right)")
  | ``Subtype.val => latexPP args.back!
  | ``Fin => return .ofString ("\\{0,\\ldots," ++
      (← latexPP args.back!).latex.1 ++ "-1\\}")
  | ``Finset => return .ofString ("\\mathcal{P}\\left(" ++
      (← latexPP args.back!).latex.1 ++ "\\right)")
  | ``Prod => binary args " \\times " 70 .none
  | ``Prod.fst | ``Prod.snd =>
    return .atomString ((← latexPP args.back!).latex.1 ++
      (if name == ``Prod.fst then "_{1}" else "_{2}"))
  | ``Membership.mem =>
    binary #[args.back!, args[args.size - 2]!] " \\in " 50 .none
  | ``Inter.inter => binary args " \\cap " 70 .left
  | ``SDiff.sdiff => binary args " \\setminus " 70 .left
  | ``Finset.Nonempty =>
    return .ofString ((← latexPP args.back!).latex.1 ++ " \\ne \\varnothing")
  | ``Fintype.card => return .ofString ("\\left|" ++
      (← latexPP args[0]!).latex.1 ++ "\\right|")
  | `LongTails.Algorithms.GraceGraph.Link => latexPP (← whnf e)
  | ``Subtype =>
    let predicate ← ensureLam args.back! none
    withBindingBodyUnusedName predicate fun index body => do
      return .ofString ("\\left\\{ " ++ symbol index.toString ++ "\\in " ++
        (← latexPP args[0]!).latex.1 ++ " \\mid " ++
        (← latexPP body).latex.1 ++ " \\right\\}")
  | `SimpleGraph.Adj =>
    return .ofString ((← latexPP args[args.size - 3]!).latex.1 ++ "\\left(" ++
      (← latexPP args[args.size - 2]!).latex.1 ++ ", " ++
      (← latexPP args.back!).latex.1 ++ "\\right)")
  | ``OfNat.ofNat => latexPP args[1]!
  | ``Nat.cast | ``NatCast.natCast | ``PNat.val => latexPP args.back!
  | ``NNReal.toReal => latexPP args.back!
  | ``Real.toNNReal =>
    return .ofString ("\\max\\left\\{ " ++ (← latexPP args.back!).latex.1 ++ ", 0 \\right\\}")
  | ``Eq => binary args " = " 50 .none
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
  | ``Nat.log2 => return .ofString ("\\log_{2}\\left(" ++
      (← latexPP args.back!).latex.1 ++ "\\right)")
  | ``Nat.size => return .ofString ("\\left\\lceil\\log_{2}\\left(" ++
      (← latexPP args.back!).latex.1 ++ " + 1\\right)\\right\\rceil_{+}")
  | ``Finset.sup | ``Finset.sup' | ``Finset.inf' =>
    let offset := if name == ``Finset.sup then 2 else 3
    let set := args[args.size - offset]!
    let isRange := set.isAppOfArity ``Finset.range 1
    guard (isRange || set.getAppFn.isConstOf ``Finset.univ)
    let fn ← ensureLam args.back! none
    let domain := fn.bindingDomain!
    let op := if name == ``Finset.inf' then "\\min" else "\\max"
    let bound ← if isRange then pure (some (← latexPP set.appArg!).latex.1)
      else if domain.isAppOfArity ``Fin 1 then
        pure (some (← latexPP domain.getAppArgs.back!).latex.1)
      else pure none
    let domainLatex ← if bound.isNone then pure (← latexPP domain).latex.1 else pure ""
    withBindingBodyUnusedName fn fun index body => do
      let index := symbol index.toString
      let range := match bound with
        | some n => "0\\le " ++ index ++ "<" ++ n
        | none => index ++ "\\in " ++ domainLatex
      return .ofString ("\\left(" ++ op ++ "_{" ++ range ++ "} " ++
        (← latexPP body).latex.1 ++ "\\right)")
  | ``sInf =>
    let range := args.back!
    guard (range.isAppOfArity ``Set.range 3)
    let fn ← ensureLam range.getAppArgs.back! none
    guard (fn.bindingDomain!.isAppOfArity ``Fin 1)
    let bound ← latexPP fn.bindingDomain!.getAppArgs.back!
    withBindingBodyUnusedName fn fun index body => do
      return .ofString ("\\inf_{0\\le " ++ symbol index.toString ++ "<" ++
        bound.latex.1 ++ "}\\left(" ++ (← latexPP body).latex.1 ++ "\\right)")
  | ``Finset.sum | ``Finset.prod =>
    let set := args[args.size - 2]!
    let fn ← ensureLam args.back! none
    if !set.getAppFn.isConstOf ``Finset.univ || !(fn.bindingDomain!.isAppOfArity ``Fin 1) then
      let domain ← if set.getAppFn.isConstOf ``Finset.univ then
          latexPP fn.bindingDomain!
        else latexPP set
      return ← withBindingBodyUnusedName fn fun index body => do
        let op := if name == ``Finset.sum then "\\sum" else "\\prod"
        return .ofString ("\\left(" ++ op ++ "_{" ++ symbol index.toString ++ "\\in " ++
          domain.latex.1 ++ "} " ++ (← latexPP body).latex.1 ++ "\\right)")
    let bound ← latexPP fn.bindingDomain!.getAppArgs.back!
    withBindingBodyUnusedName fn fun index body => do
      let op := if name == ``Finset.sum then "\\sum" else "\\prod"
      return .ofString ("\\left(" ++ op ++ "_{" ++ symbol index.toString ++ "=0}^{" ++
        bound.latex.1 ++ "-1} " ++ (← latexPP body).latex.1 ++ "\\right)")
  | ``Finset.card => return .ofString ("\\left|" ++
      (← latexPP args.back!).latex.1 ++ "\\right|")
  | `LongTails.Setups.HiddenMixedIntegerLinear.goodPoints =>
    return .ofString ("\\operatorname{goodPoints}\\left(" ++
      (← latexPP args.back!).latex.1 ++ "\\right)")
  | ``Int.toNat => return .ofString ("\\max\\left\\{ " ++
      (← latexPP args.back!).latex.1 ++ ", 0 \\right\\}")
  | ``Nat.ceil => return .ofString ("\\left\\lceil " ++ (← latexPP args.back!).latex.1 ++ " \\right\\rceil_{+}")
  | ``Nat.floor => return .ofString ("\\left\\lfloor " ++ (← latexPP args.back!).latex.1 ++ " \\right\\rfloor_{+}")
  | ``Nat.log =>
    return .ofString ("\\operatorname{Nat.log}_{" ++ (← latexPP args[0]!).latex.1 ++
      "}\\left(" ++ (← latexPP args[1]!).latex.1 ++ "\\right)")
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
    if (`LongTails.Theorems).isPrefixOf name then return ← namedApplication e
    let some projection ← getProjectionFnInfo? name | failure
    let structName := projection.ctorName.getPrefix
    guard (structName.getString!.endsWith "Params" || structName.getString! == "Public")
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
    if result.contains "\\operatorname{Lean}" then
      throwError "Unsupported budget notation in LeanTeX: {result}"
    return result

end TheoremDescriptions
