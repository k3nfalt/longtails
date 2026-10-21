import LongTails.Setups.LocalSmoothStronglyConvexLora
import LongTails.Proofs.LoraSilverConvergence

namespace LongTails.Theorems.SilverLoraLocalConvergence

open OracleTemplate LongTails.Setups.LocalSmoothStronglyConvexLora
open LongTails.Algorithms.LoraGd LongTails.Proofs.LoraModel
open LongTails.Proofs.LoraExecution LongTails.Proofs.LoraSilverConvergence

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 128 * ⌈64 * p.ρ * p.R ^ 2 / (p.μ * p.s ^ 2)⌉₊ * (⌈Real.log (1 + 512 * p.ρ * p.R ^ 2 / (p.μ * p.s ^ 2)) / Real.log (1 + Real.sqrt 2)⌉₊ + 1) + (2 ^ ⌈Real.log (1 + 512 * p.ρ * p.R ^ 2 / (p.μ * p.s ^ 2)) / Real.log (1 + Real.sqrt 2)⌉₊ - 1) * ⌈Real.log (1 + 32 * p.ρ * p.R ^ 4 / p.ε) / Real.log 4⌉₊

theorem result : Convergence LongTails.Setups.LocalSmoothStronglyConvexLora.spec budget := by
  refine ⟨LongTails.Algorithms.LoraSilver.method, ?_, allowed⟩
  intro p hp f O hO
  change Params at p
  change (MatrixSpace p.m p.n → ℝ) at f
  change Oracle (MatrixSpace p.m p.n) (MatrixSpace p.m p.n) 1 at O
  obtain ⟨_, _, _, hμ, hμρ, hs, hsR, hε⟩ := hp
  obtain ⟨hg, hstrong, hlip, hanswer, c, hmin, href, hB, hA, hinit⟩ := hO
  let H : Model p f c := ⟨hμ, hμρ, hs, hsR, hg, hstrong, hlip, hmin, href, hB, hA⟩
  have hb : budget p = fun _ => (LongTails.Algorithms.LoraSilver.schedule p).length := by
    funext i
    rw [schedule_length]
    rfl
  refine ⟨product c, hmin, Filter.Eventually.of_forall ?_⟩
  intro ω
  change Unit × ((k : ℕ) → O.Seed k) at ω
  change f (product (execute O (LongTails.Algorithms.LoraSilver.method p) (budget p) ω.1 ω.2)) -
    f (product c) ≤ p.ε
  rw [hb]
  erw [execute_eq_of_answer_eq O (gradient f) hanswer]
  have he := execute_schedule (gradient f) (LongTails.Algorithms.LoraSilver.schedule p)
    (smoothness p) p.x₀
  change f (product (execute { answer := fun _ query _ => gradient f query.2 }
    (LongTails.Algorithms.LoraSilver.method p)
    (fun _ => (LongTails.Algorithms.LoraSilver.schedule p).length) ω.1)) - f (product c) ≤ p.ε
  cases ω.1
  erw [he]
  exact schedule_accuracy H hε hinit

end LongTails.Theorems.SilverLoraLocalConvergence
