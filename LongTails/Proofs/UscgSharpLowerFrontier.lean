import LongTails.Proofs.UscgSharpMixingWitness
import LongTails.Proofs.UscgSharpDeterministicWitness

namespace LongTails.Proofs.UscgSharpLowerFrontier

open LongTails.Setups.UscgConstant (Space IsBallLMO)
open UscgSharpLowerWitness

theorem confidence_lower {L σ Δ ε ell α η : ℝ} {T : ℕ} (lmo : Space 1 → Space 1)
    (hL : 0 < L) (he : 0 < ε) (hσ : 0 ≤ σ) (ha : 0 < α) (ha1 : α < 1)
    (hη : 0 < η) (hT : 0 < T)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo)
    (hA : 8192 ≤ σ ^ 2 / ε ^ 2) (hD : 256 ≤ L * Δ / ε ^ 2)
    (hell : 256 * (1 + Real.log (σ ^ 2 / ε ^ 2) + Real.log (L * Δ / ε ^ 2)) ≤ ell)
    (horizon : (T : ℝ) ≤ (σ ^ 2 / ε ^ 2) * Real.sqrt (L * Δ / ε ^ 2) * ell / 262144) :
    Nonempty (Witness L σ Δ ε (Real.exp (-ell)) α η T lmo) := by
  let A := σ ^ 2 / ε ^ 2
  let D := L * Δ / ε ^ 2
  have hA1 : 1 ≤ A := by dsimp [A]; linarith
  have hD1 : 1 ≤ D := by dsimp [D]; linarith
  have hla := Real.log_nonneg hA1
  have hld := Real.log_nonneg hD1
  have hell256 : 256 ≤ ell := by change 256 * (1 + Real.log A + Real.log D) ≤ ell at hell; linarith
  have hellp : 0 < ell := by linarith
  have hprod : 0 ≤ A * Real.sqrt D * ell := by positivity
  have hhor : (T : ℝ) ≤ A * Real.sqrt D * ell := by
    change (T : ℝ) ≤ A * Real.sqrt D * ell / 262144 at horizon
    linarith
  have htlog := (UscgSharpLowerTuning.horizon_log hA1 hD1 hT hell hhor).2
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hδ : Real.exp (-ell) < 1 / 2 := by
    calc
      _ < Real.exp (-Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  by_cases hT3 : T ≤ 3
  · exact UscgSharpDeterministicWitness.small_horizon_witness lmo hL he (by linarith) hT hT3 hD
  have hT4 : 4 ≤ T := by omega
  by_cases hmemory : 4096 / (A + 16) ≤ α
  · exact UscgSharpMixingWitness.mixing_witness lmo hL he ha ha1 hη hT hδ hA hD hmemory hlmo
  have hα : α < 4096 / (A + 16) := lt_of_not_ge hmemory
  have hAp : 0 < A + 16 := by linarith
  have hαmul := (lt_div_iff₀ hAp).mp hα
  have hαhalf : α ≤ 1 / 2 := by
    have hh : 4096 / (A + 16) ≤ 1 / 2 := (div_le_iff₀ hAp).mpr (by change 8192 ≤ A at hA; linarith)
    exact hα.le.trans hh
  have hαA : α * A ≤ 4096 := by nlinarith
  have hfront : 64 * α * T ≤ Real.sqrt D * ell := by
    have hh := (le_div_iff₀ (by norm_num : (0 : ℝ) < 262144)).mp horizon
    have hm := mul_le_mul_of_nonneg_left hh ha.le
    have hs := mul_le_mul_of_nonneg_right hαA (show 0 ≤ Real.sqrt D * ell by positivity)
    change (T : ℝ) * 262144 ≤ A * Real.sqrt D * ell at hh
    nlinarith
  have hsig : ε ≤ σ := by
    have hh := (le_div_iff₀ (sq_pos_of_pos he)).mp hA
    nlinarith [sq_pos_of_pos he]
  have hΔ : 0 ≤ Δ := by
    have hh := (le_div_iff₀ (sq_pos_of_pos he)).mp hD
    nlinarith [sq_pos_of_pos he]
  by_cases hprogress : 4 * ε * η * T < Δ
  · exact UscgSharpDeterministicWitness.slow_step_witness lmo hL he (by linarith) hη.le hT hlmo hD hprogress
  · exact quadratic_witness lmo hL he hsig hΔ ha hαhalf hη hT4 hlmo hell256 htlog hD hfront (le_of_not_gt hprogress)

end LongTails.Proofs.UscgSharpLowerFrontier
