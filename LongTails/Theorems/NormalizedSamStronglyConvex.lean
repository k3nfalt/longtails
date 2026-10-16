import LongTails.Setups.NormalizedSamStronglyConvex
import LongTails.Proofs.NormalizedSamRun
import LongTails.Proofs.SamTuning
import LongTails.Proofs.SamCycleScaling

namespace LongTails.Theorems.NormalizedSamStronglyConvex

open OracleTemplate LongTails.Setups.NormalizedSamStronglyConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 2 * ⌈(2*p.L/p.μ + 2*p.L^2*p.ρ/(p.μ*Real.sqrt (p.μ*p.ε)))*Real.log (1+p.Δ/p.ε)⌉₊

theorem result : Convergence LongTails.Setups.NormalizedSamStronglyConvex.spec budget := by
  refine ⟨fun p => LongTails.Algorithms.NormalizedSam.method
    (1/(2*p.L+2*p.L^2*p.ρ/Real.sqrt (p.μ*p.ε))) p.ρ p.x0, ?_, ?_⟩
  · intro p hp I oracle h
    rcases hp with ⟨hμ, hμL, hρ, hΔ, hε⟩
    rcases h with ⟨hg, hl, hs, _, hx, ho⟩
    have hL : 0 < p.L := hμ.trans_le hμL
    let η := 1/(2*p.L+2*p.L^2*p.ρ/Real.sqrt (p.μ*p.ε))
    let K := ⌈(2*p.L/p.μ+2*p.L^2*p.ρ/(p.μ*Real.sqrt (p.μ*p.ε)))*Real.log (1+p.Δ/p.ε)⌉₊
    have ha := LongTails.Proofs.SamStrongConvex.tuned_accuracy hL hρ hμ hμL hΔ hε
      hs hg hl p.x0 I.2 hx
    refine Filter.Eventually.of_forall ?_
    rintro ⟨⟨⟩, seed⟩
    change I.1 (execute oracle (LongTails.Algorithms.NormalizedSam.method η p.ρ p.x0)
      (fun _ => 2*K) () seed)-I.1 I.2 ≤ p.ε
    erw [execute_eq_of_answer_eq oracle (gradient I.1) ho]
    erw [LongTails.Proofs.NormalizedSamRun.execute_method]
    exact ha
  · intro p hp
    rcases hp with ⟨hμ, hμL, hρ, _, hε⟩
    refine ⟨_, ?_, rfl⟩
    exact (LongTails.Proofs.SamStrongConvex.tuning (hμ.trans_le hμL) hμ hμL hρ hε).1

end LongTails.Theorems.NormalizedSamStronglyConvex
