import LongTails.Template

namespace OracleTemplate.BoundedScalarConvex

def project (lower upper x : ℝ) : ℝ := max lower (min upper x)

noncomputable def scalarSgd (lower upper η x0 : ℝ) : Algorithm ℝ ℝ ℝ where
  State := ℝ
  initial _ := x0
  query x := (0, x)
  update x g := project lower upper (x-η*g)
  output x := x

noncomputable def scalarIterate (O : Oracle ℝ ℝ) (lower upper η x0 : ℝ) :
    ℕ → ((k : ℕ) → O.Seed k) → ℝ
  | 0, _ => x0
  | n+1, ξ =>
      project lower upper (scalarIterate O lower upper η x0 n ξ-
        η*O.answer n (0, (scalarIterate O lower upper η x0 n ξ)) (ξ n))

end OracleTemplate.BoundedScalarConvex
