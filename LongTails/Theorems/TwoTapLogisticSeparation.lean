import LongTails.Setups.TwoTapLogisticSeparation
import LongTails.Proofs.TwoTapLogisticBudget

namespace OracleTemplate.TwoTapLogisticSeparation

open LongTails.Setups.TwoTapLogisticSeparation
open LongTails.Algorithms.TwoTapLogisticGd
open LongTails.Proofs.TwoTapLogisticDescent
open LongTails.Proofs.TwoTapLogisticBudget

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  let U := p.a^2+p.b^2
  let V := ‖p.v‖^2
  let s := U-V
  let D := max s (-s)+2
  let u := if p.δ ≤ s then p.δ/2 else min 1 (p.δ^2/(p.R^2*(1+D)))
  let K := 5*(2+(D+2)/u)
  let A := U+V+2
  let B := 4*Real.sqrt K/p.γ
  let Z := A+B*Real.sqrt ((Real.log (8*p.n))^3)
  let L := 1+8*p.R+32*p.R^2*(A+4*B)+(if p.δ ≤ s then 4/p.δ else 0)
  ⌈(1+80*p.n*(2+p.R)*K*L/p.γ^2)*Real.log (1+4*((2+p.R)*(1+Z)))⌉₊

theorem result : Convergence LongTails.Setups.TwoTapLogisticSeparation.spec budget := by
  refine ⟨fun p => algorithm p (stepSize p), ?_, fun p hp => family_compliance p _ (tuning_limits p hp).1⟩
  rintro p hp X O ⟨hX,S,hF,hO⟩
  dsimp only
  rintro ⟨ω,ξ⟩
  change Separates p X (execute O (algorithm p (stepSize p)) (fun _ => budget p (0 : Fin 1)) ω ξ)
  erw [valid_execution p X (stepSize p) O hO (budget p (0 : Fin 1)) ω ξ]
  apply iterate_separates p X hp hX S hF
  apply le_trans _ (Nat.le_ceil _)
  erw [tuning_eq p]
  rw [div_mul_eq_mul_div,one_mul,div_div_eq_mul_div]
  have hD : max (p.a^2+p.b^2-‖p.v‖^2) (-(p.a^2+p.b^2-‖p.v‖^2)) =
      |‖p.v‖^2-(p.a^2+p.b^2)| := by rw [← abs_eq_max_neg, abs_sub_comm]
  have hu (D : ℝ) : p.δ^2/(p.R^2*(1+D)) = (p.δ/p.R)^2/(1+D) := by
    rw [div_pow, div_div]
  simp only [hD, hu]
  exact le_rfl

end OracleTemplate.TwoTapLogisticSeparation
