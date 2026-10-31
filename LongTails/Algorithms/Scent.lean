import LongTails.Setups.CompositionalEntropicRisk

namespace OracleTemplate.Scent

open LongTails.Setups.CompositionalEntropicRisk

noncomputable def spmd (α ν s : ℝ) : ℝ :=
  ν + Real.log (1 + α * Real.exp s) - Real.log (1 + α * Real.exp ν)

structure State (q : Params) where
  t : ℕ
  j : ℕ
  w : q.E
  ν : Fin q.n → ℝ
  acc : q.E
  sum : q.E
  pending : Bool
  proposal : q.E

noncomputable def sampleUpdate (q : Params) (η α : ℝ) (s : State q) (i : Fin q.n)
    (r1 r2 : ℝ × q.E) : State q :=
  let ν' := Function.update s.ν i (spmd α (s.ν i) r1.1)
  let acc' := s.acc + Real.exp (r2.1 - ν' i) • r2.2
  if s.j + 1 = q.B then
    ⟨s.t, s.j + 1, s.w, ν', acc', s.sum, true, s.w - (η / q.B) • acc'⟩
  else
    ⟨s.t, s.j + 1, s.w, ν', acc', s.sum, false, s.proposal⟩

noncomputable def projectionUpdate (q : Params) (s : State q) (x : q.E) : State q :=
  ⟨s.t + 1, 0, x, s.ν, 0, s.sum + s.w, false, x⟩

noncomputable def scent (q : Params) (η α : ℝ) (T : ℕ) :
    Algorithm (Query q) (Reply q) q.E where
  State := State q
  initial _ := ⟨0, 0, q.w0, fun _ => q.c1, 0, 0, false, q.w0⟩
  query s := (0, if s.pending then .projection s.proposal else .sample s.w)
  update s r := match r with
    | .sample i r1 r2 => sampleUpdate q η α s i r1 r2
    | .projection x => projectionUpdate q s x
  output s := if T = 0 then q.w0 else (T : ℝ)⁻¹ • s.sum

end OracleTemplate.Scent
