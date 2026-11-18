import BudgetLatex
import LongTails.TemplateDistributed

open Lean Elab Command Term

run_cmd liftTermElabM do
  let value ← elabTerm (← `(DistributedTemplate.clockBits)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "64" do
    throwError "Unexpected clock width: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (x : ℝ) => Nat.floor (x / 3) + 1)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\left\\lfloor \\frac{x}{3} \\right\\rfloor_{+} + 1" do
    throwError "Unexpected natural floor budget: {result}"

namespace BudgetLatexTests
structure Public where
  L : ℝ
  start : ℝ
structure Params where
  data : Public
  dimension : ℕ+
  hi : Fin dimension → ℤ
  lo : Fin dimension → ℤ
structure LowerParams where
  L : ℝ

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (q : Params) => q.data.L)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "L" do
    throwError "Unexpected bundled public parameter: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (p : Params) => (p.dimension : ℝ))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "dimension" do
    throwError "Unexpected positive natural parameter: {result}"
end BudgetLatexTests

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (p : BudgetLatexTests.LowerParams) => p.L)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "L" do
    throwError "Unexpected lower-bound parameter: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (x : ℝ) => (Real.toNNReal x : ℝ))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\max\\left\\{ x, 0 \\right\\}" do
    throwError "Unexpected nonnegative real conversion: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (n : ℕ) => Nat.size n)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\left\\lceil\\log_{2}\\left(n + 1\\right)\\right\\rceil_{+}" do
    throwError "Unexpected bit length: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (n : ℕ) => if n = 1 then (0 : ℕ) else 2)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\begin{cases} 0 & n = 1 \\\\ 2 & \\mathrm{otherwise} \\end{cases}" do
    throwError "Unexpected equality condition: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (n : ℕ) (h : Fin n → NNReal) => Finset.univ.sup h)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\left(\\max_{0\\le a<n} h\\left(a\\right)\\right)" do
    throwError "Unexpected finite maximum: {result}"

namespace LongTails.Theorems.BudgetLatexTests
abbrev SearchSpace (n : ℕ) := Fin (n + 1)
def count (n : ℕ) (c : SearchSpace n) : ℕ := n + c.val
end LongTails.Theorems.BudgetLatexTests

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (n : ℕ) => Finset.univ.inf' Finset.univ_nonempty
    (fun c : LongTails.Theorems.BudgetLatexTests.SearchSpace n =>
      LongTails.Theorems.BudgetLatexTests.count n c))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\left(\\min_{c\\in \\operatorname{SearchSpace}\\left(n\\right)} \\operatorname{count}\\left(n, c\\right)\\right)" do
    throwError "Unexpected finite search budget: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (p : BudgetLatexTests.Params) => ‖p.data.start‖ ^ 2)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\left\\lVert start \\right\\rVert^{2}" do
    throwError "Unexpected squared norm budget: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (m : ℕ) => Nat.log2 (m ^ 3 + 4))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\log_{2}\\left(m^{3} + 4\\right)" do
    throwError "Unexpected natural logarithm base two: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (β : ℝ) => β⁻¹)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\frac{1}{\\beta}" do
    throwError "Unexpected inverse budget: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (μx μy : ℝ) => μx * μy)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\mu x \\cdot \\mu y" do
    throwError "Unexpected compound Greek identifiers: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (a b : ℝ) => Real.exp (-28 * (a + b)))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\exp\\left(-28 \\cdot \\left(a + b\\right)\\right)" do
    throwError "Unexpected negative budget: {result}"
  let value ← elabTerm (← `(fun (a b : ℝ) => -(a + b))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "-\\left(a + b\\right)" do
    throwError "Unexpected negative sum: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (a b c : ℝ) => (a + b) * (b + c) ^ (2 : ℕ))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\left(a + b\\right) \\cdot \\left(b + c\\right)^{2}" do
    throwError "Unexpected bracket sizing: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (Δ ε : ℝ) => if Δ ≤ ε then (0 : ℕ) else 2)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\begin{cases} 0 & \\Delta \\leq \\varepsilon \\\\ 2 & \\mathrm{otherwise} \\end{cases}" do
    throwError "Unexpected conditional budget: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (a b c : ℝ) => min (a + b) (max b c))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\min\\left\\{ a + b, \\max\\left\\{ b, c \\right\\} \\right\\}" do
    throwError "Unexpected min/max budget: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (δ : ℝ) => Real.log (Real.exp 1 / δ))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\log\\left(\\frac{\\exp\\left(1\\right)}{\\delta}\\right)" do
    throwError "Unexpected exponential budget: {result}"
  let value ← elabTerm (← `(fun (a b : ℝ) => Real.exp (a + b))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\exp\\left(a + b\\right)" do
    throwError "Unexpected exponential argument: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (R r0 : ℝ) => Real.logb 2 (R / r0))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\log_{2}\\left(\\frac{R}{r0}\\right)" do
    throwError "Unexpected logarithm base: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (p : BudgetLatexTests.Params) =>
    2 * (∏ j, (p.hi j - p.lo j + 1).toNat) - 1)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "2 \\cdot \\left(\\prod_{j=0}^{dimension-1} \\max\\left\\{ hi\\left(j\\right) - lo\\left(j\\right) + 1, 0 \\right\\}\\right) - 1" do
    throwError "Unexpected finite product budget: {result}"

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (s : Finset ℕ) => s.card)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\left|s\\right|" do
    throwError "Unexpected cardinality budget: {result}"
