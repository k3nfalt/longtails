import LongTails.Proofs.UscgSharpLowerFrontier
import LongTails.Proofs.UscgSharpLowerExecution

namespace LongTails.Proofs.UscgSharpLowerResult

open MeasureTheory OracleTemplate
open LongTails.Setups.UscgHighProbability
open LongTails.Setups.UscgConstant (Space IsBallLMO)
open LongTails.Algorithms.UscgSharpConfidence
open UscgSharpLowerWitness UscgSharpLowerExecution UscgSharpScalar UscgSharpExecution

noncomputable def realized {L σ Δ ε δ α η : ℝ} {T : ℕ} {lmo : Space 1 → Space 1}
    (W : Witness L σ Δ ε δ α η T lmo) : Prop :=
  spec.valid (params W) ∧
  spec.admissible (params W) (lift W.f)
    (canonicalOracle (publicParams L σ Δ ε δ) (oracle W.f' W.noise) lmo (stream W)) ∧
  spec.allowedAlgorithm (publicParams L σ Δ ε δ) (algorithm (publicParams L σ Δ ε δ) α η) ∧
  ¬ spec.successful (params W) (lift W.f)
    (fun seed : Unit × (ℕ → W.Ω) => execute
      (canonicalOracle (publicParams L σ Δ ε δ) (oracle W.f' W.noise) lmo (stream W))
      (algorithm (publicParams L σ Δ ε δ) α η) (fun _ => T) seed.1 seed.2)
    ⟨(Measure.dirac ()).prod (stream W : Measure (ℕ → W.Ω)), inferInstance⟩

theorem execution_frontier {L σ Δ ε ell α η : ℝ} {T : ℕ} (lmo : Space 1 → Space 1)
    (hL : 0 < L) (he : 0 < ε) (hσ : 0 ≤ σ) (ha : 0 < α) (ha1 : α < 1)
    (hη : 0 < η) (hT : 0 < T)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo)
    (hA : 8192 ≤ σ ^ 2 / ε ^ 2) (hD : 256 ≤ L * Δ / ε ^ 2)
    (hell : 256 * (1 + Real.log (σ ^ 2 / ε ^ 2) + Real.log (L * Δ / ε ^ 2)) ≤ ell)
    (horizon : (T : ℝ) ≤ (σ ^ 2 / ε ^ 2) * Real.sqrt (L * Δ / ε ^ 2) * ell / 262144) :
    ∃ W : Witness L σ Δ ε (Real.exp (-ell)) α η T lmo, realized W := by
  obtain ⟨W⟩ := UscgSharpLowerFrontier.confidence_lower lmo hL he hσ ha ha1 hη hT hlmo hA hD hell horizon
  have hΔ : 0 ≤ Δ := by
    have hh := (le_div_iff₀ (sq_pos_of_pos he)).mp hD
    nlinarith [sq_pos_of_pos he]
  have hla := Real.log_nonneg (show 1 ≤ σ ^ 2 / ε ^ 2 by linarith)
  have hld := Real.log_nonneg (show 1 ≤ L * Δ / ε ^ 2 by linarith)
  have hell256 : 256 ≤ ell := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hδ : Real.exp (-ell) < 1 / 2 := by
    calc
      _ < Real.exp (-Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  exact ⟨W, valid W hL hσ hΔ he (Real.exp_pos _) hδ, admissible W hlmo,
    UscgSharpSchedule.algorithm_allowed _ ha ha1 hη,
    not_successful W hT (Real.exp_pos _).le hlmo⟩

end LongTails.Proofs.UscgSharpLowerResult
