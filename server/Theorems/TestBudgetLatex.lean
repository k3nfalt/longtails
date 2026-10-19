import BudgetLatex

open Lean Elab Command Term

namespace BudgetLatexTests
structure Public where
  L : ℝ
structure Params where
  data : Public

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (q : Params) => q.data.L)) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "L" do
    throwError "Unexpected bundled public parameter: {result}"
end BudgetLatexTests

set_option hygiene false in
run_cmd liftTermElabM do
  let value ← elabTerm (← `(fun (m : ℕ) => Nat.log2 (m ^ 3 + 4))) none
  let result ← TheoremDescriptions.budgetLatex (← instantiateMVars value)
  unless result == "\\operatorname{log2}\\left(m^{3} + 4\\right)" do
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
