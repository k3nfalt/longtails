import LongTails.Setups.HeavyTailedNcsc
import LongTails.Proofs.HeavyTailSaddleOuter
import LongTails.Proofs.HeavyTailSaddleOuterCost

namespace OracleTemplate.HeavyTailedNcscAccelerated

open LongTails.Setups.HeavyTailedNcsc
open LongTails.Algorithms.HeavyTailSaddleEstimator
open LongTails.Proofs.HeavyTailSaddleOuter LongTails.Proofs.HeavyTailSaddleOuterCost

noncomputable def budget : (let S := LongTails.Setups.HeavyTailedNcsc.spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈((2:ℝ)^80*(q.p/(q.p-1)))^(q.p/(q.p-1)+2)*(1+Real.log (2+q.L/q.μ+1/q.δ+q.L*q.Δ/q.ε^2+((q.L/q.μ)*(q.σ/q.ε))^(q.p/(q.p-1))+Real.log (2+(q.L/q.μ)^3*q.L*(q.Δ+q.G^2/q.μ)/q.ε^2)))^(2*(q.p/(q.p-1))+3)*(Real.sqrt (q.L/q.μ)*(1+q.L*q.Δ/q.ε^2+Real.log (2+(q.L/q.μ)^3*q.L*(q.Δ+q.G^2/q.μ)/q.ε^2))+(q.L*q.Δ/q.ε^2*(q.L/q.μ)^((q.p/(q.p-1))/2)+(q.L/q.μ)^(q.p/(q.p-1)))*(q.σ/q.ε)^(q.p/(q.p-1)))⌉₊

theorem result : Convergence LongTails.Setups.HeavyTailedNcsc.spec budget := by
  refine ⟨fun q => saddleAlgorithm q.p q.σ q.L q.μ q.Δ q.G q.ε q.δ (q.x0,q.y0),?_,fun _ _ => trivial⟩
  intro q hv f O hadm
  have hvalid := hv
  obtain ⟨hm,hmL,hp,hp2,hσ,hΔ,_,he,hd,hdhalf⟩ := hv
  have hc := actual_saddle_cost (G:=q.G) hp hp2 hσ hm hmL hΔ he hd (by linarith : q.δ ≤ 1)
  have hcalls : saddleCalls q.p q.σ q.L q.μ q.Δ q.G q.ε q.δ ≤ budget q 0 := by
    apply (Nat.cast_le (α:=ℝ)).mp
    unfold budget
    exact hc.trans (Nat.le_ceil _)
  exact setup_success q hvalid f O hadm (budget q 0) hcalls

end OracleTemplate.HeavyTailedNcscAccelerated
