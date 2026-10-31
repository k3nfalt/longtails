import LongTails.Template

namespace OracleTemplate.BoundedScalarConvex

def project (lower upper x : ℝ) : ℝ := max lower (min upper x)

noncomputable def scalarSgd (lower upper η x0 : ℝ) : Algorithm ℝ ℝ ℝ where
  Seed := Unit
  State := ℝ
  initial _ := x0
  query x := (0, x)
  update x g := project lower upper (x-η*g)
  output x := x

noncomputable def scalarRun (O : Oracle ℝ ℝ) (lower upper η x0 : ℝ) :
    ℕ → ((k : ℕ) → O.Seed k) → ℝ × List ((Fin 1 × ℝ) × ℝ)
  | 0, _ => (x0, [])
  | n+1, ξ =>
      let (x, history) := scalarRun O lower upper η x0 n ξ
      let query := (0, x)
      let reply := O.answer history query (ξ history.length)
      (project lower upper (x-η*reply), history ++ [(query, reply)])

noncomputable def scalarIterate (O : Oracle ℝ ℝ) (lower upper η x0 : ℝ)
    (n : ℕ) (ξ : (k : ℕ) → O.Seed k) : ℝ :=
  (scalarRun O lower upper η x0 n ξ).1

noncomputable def scalarHistory (O : Oracle ℝ ℝ) (lower upper η x0 : ℝ)
    (n : ℕ) (ξ : (k : ℕ) → O.Seed k) : List ((Fin 1 × ℝ) × ℝ) :=
  (scalarRun O lower upper η x0 n ξ).2

end OracleTemplate.BoundedScalarConvex
