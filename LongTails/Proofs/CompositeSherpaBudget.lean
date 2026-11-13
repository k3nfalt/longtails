import LongTails.Proofs.CompositeSherpaRun
import LongTails.Proofs.RadiusFreeSherpaBudget
import LongTails.Proofs.BacktrackingCompositeBudget
import LongTails.Proofs.Execution

open Set

namespace OracleTemplate.CompositeSherpa

open LongTails.Setups.LipschitzCompositeGeneralizedSmooth
open RadiusFreeSherpa (theta theta_pos theta_sq theta_le log_two_lower one_le_log2q log2q_pos
  log_le_two_sqrt log_pow_bound logb_le)

lemma execute_algorithm (p : Public) (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E)
    (ψ : p.E → ℝ) (N : ℕ) :
    execute { answer := fun _ (_, q) _ => answerOf p grad prox ψ q } (algorithm p) (fun _ => N) =
      stateOutput ((T p grad prox ψ)^[N] (initState p.x0)) := by
  erw [execute_iterate]
  rfl

lemma sqrt_prod_le {q : ℝ} (hq : 0 ≤ q) : Real.sqrt (1 + q) * Real.log (2 + q) ≤ 4 * (1 + q) := by
  have h1 := log_le_two_sqrt (x := 2 + q) (by linarith)
  have h2 : Real.sqrt (1 + q) * Real.sqrt (2 + q) ≤ 2 * (1 + q) := by
    rw [← Real.sqrt_mul (by linarith)]
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have h0 : 0 ≤ Real.sqrt (1 + q) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 h0]

lemma bigB_le {q : ℝ} (hq : 0 ≤ q) : bigB q ≤ 1300 * (1 + q) := by
  unfold bigB
  have hθ := theta_le hq
  have hθ0 : 0 ≤ theta q := (theta_pos hq).le
  have hθsq := theta_sq hq
  have h24 : Real.sqrt 24 * Real.sqrt 12 ≤ 17 := by
    rw [← Real.sqrt_mul (by norm_num)]
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hlog : Real.log (216 * (1 + q) ^ 2) ≤ 10 * Real.log (2 + q) := by
    have := log_pow_bound (c := 216) hq (by norm_num) (a := 8) (k := 2) (by norm_num)
    push_cast at this
    linarith
  have hprod := sqrt_prod_le hq
  have hlogpos := log2q_pos hq
  have hθlog : theta q * Real.log (216 * (1 + q) ^ 2) ≤ 40 * (1 + q) := by
    calc theta q * Real.log (216 * (1 + q) ^ 2) ≤ theta q * (10 * Real.log (2 + q)) :=
          mul_le_mul_of_nonneg_left hlog hθ0
      _ = 10 * (Real.sqrt (1 + q) * Real.log (2 + q)) := by unfold theta; ring
      _ ≤ 10 * (4 * (1 + q)) := by gcongr
      _ = 40 * (1 + q) := by ring
  have hθθ : theta q * (5 / 2 * theta q) = 5 / 2 * (1 + q) := by
    rw [← hθsq]; ring
  nlinarith [mul_le_mul_of_nonneg_right h24 hq]

lemma probeCap_le {q : ℝ} (hq : 0 ≤ q) : (probeCap q : ℝ) ≤ 25 * Real.log (2 + q) := by
  unfold probeCap
  have hpos : (0 : ℝ) < 2304 * (1 + 2 * q) ^ 2 := by positivity
  have hle : 2304 * (1 + 2 * q) ^ 2 ≤ 16384 * (1 + q) ^ 2 := by nlinarith
  have hlog : Real.log (2304 * (1 + 2 * q) ^ 2) ≤ 16 * Real.log (2 + q) := by
    have := log_pow_bound (c := 16384) hq (by norm_num) (a := 14) (k := 2) (by norm_num)
    push_cast at this
    exact (Real.log_le_log hpos hle).trans (by linarith)
  have hlognn : 0 ≤ Real.log (2304 * (1 + 2 * q) ^ 2) := Real.log_nonneg (by nlinarith)
  have hlb := logb_le hlognn
  have hceil := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    (by nlinarith : (1:ℝ) ≤ 2304 * (1 + 2 * q) ^ 2))
  have h1 := one_le_log2q hq
  linarith

lemma phaseSteps_le {q : ℝ} (hq : 0 ≤ q) : phaseSteps q ≤ 75000 * (1 + q) * Real.log (2 + q) := by
  unfold phaseSteps
  have hB := bigB_le hq
  have hpc := probeCap_le hq
  have hpc0 : (0 : ℝ) ≤ probeCap q := by positivity
  have hl := log2q_pos hq
  have h1 := one_le_log2q hq
  have hB0 : 0 ≤ bigB q + 1 := by
    have : 0 ≤ bigB q := by
      unfold bigB
      have := theta_pos hq
      have : 0 ≤ Real.log (216 * (1 + q) ^ 2) := Real.log_nonneg (by nlinarith)
      positivity
    linarith
  have h2 : 5 + 2 * (probeCap q : ℝ) ≤ 58 * Real.log (2 + q) := by linarith
  have h3 : (bigB q + 1) * (5 + 2 * probeCap q) ≤ (1300 * (1 + q) + 1) * (58 * Real.log (2 + q)) := by
    apply mul_le_mul (by linarith) h2 (by positivity) (by positivity)
  have h4 : (1300 * (1 + q) + 1) * (58 * Real.log (2 + q)) ≤ 1301 * (1 + q) * (58 * Real.log (2 + q)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  nlinarith [mul_nonneg hq hl.le]

lemma phase2_bound_le {q A : ℝ} (hq : 0 ≤ q) :
    4 + 61 * Real.sqrt A +
      (35 + 1067 * q) * Real.log (1 + (12 + 400 * q) * (1 + 1 + Real.sqrt (6 * q))) +
      4 * Real.log (5 / 2 + 1 / 16 + 132 * q) +
      2 * Real.log (2 * ((1 + (40 + 2400 * q)) * (8 * (1 + 32 * q) ^ 2 + 200 * q ^ 2))) ≤
    61 * Real.sqrt A + 15100 * (1 + q) * Real.log (2 + q) := by
  have hl := log2q_pos hq
  have h1 := one_le_log2q hq
  have hs6 : Real.sqrt (6 * q) ≤ 3 * (1 + q) := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs0 : 0 ≤ Real.sqrt (6 * q) := Real.sqrt_nonneg _
  have hinner1 : 1 + (12 + 400 * q) * (1 + 1 + Real.sqrt (6 * q)) ≤ 4096 * (1 + q) ^ 2 := by
    have : (12 + 400 * q) * (1 + 1 + Real.sqrt (6 * q)) ≤ 412 * (1 + q) * (5 * (1 + q)) := by
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    nlinarith
  have hlog1 : Real.log (1 + (12 + 400 * q) * (1 + 1 + Real.sqrt (6 * q))) ≤ 14 * Real.log (2 + q) := by
    have := log_pow_bound (c := 4096) hq (by norm_num) (a := 12) (k := 2) (by norm_num)
    push_cast at this
    exact (Real.log_le_log (by positivity) hinner1).trans (by linarith)
  have hterm1 : (35 + 1067 * q) * Real.log (1 + (12 + 400 * q) * (1 + 1 + Real.sqrt (6 * q))) ≤
      1067 * (1 + q) * (14 * Real.log (2 + q)) := by
    apply mul_le_mul (by linarith) hlog1 (Real.log_nonneg (by nlinarith)) (by positivity)
  have hinner2 : 5 / 2 + 1 / 16 + 132 * q ≤ 256 * (1 + q) ^ 1 := by nlinarith
  have hlog2 : Real.log (5 / 2 + 1 / 16 + 132 * q) ≤ 9 * Real.log (2 + q) := by
    have := log_pow_bound (c := 256) hq (by norm_num) (a := 8) (k := 1) (by norm_num)
    push_cast at this
    exact (Real.log_le_log (by positivity) hinner2).trans (by linarith)
  have hinner3 : 2 * ((1 + (40 + 2400 * q)) * (8 * (1 + 32 * q) ^ 2 + 200 * q ^ 2)) ≤
      67108864 * (1 + q) ^ 3 := by
    have ha : 1 + (40 + 2400 * q) ≤ 2441 * (1 + q) := by linarith
    have hb : 8 * (1 + 32 * q) ^ 2 + 200 * q ^ 2 ≤ 8392 * (1 + q) ^ 2 := by nlinarith
    have hc : (1 + (40 + 2400 * q)) * (8 * (1 + 32 * q) ^ 2 + 200 * q ^ 2) ≤
        2441 * (1 + q) * (8392 * (1 + q) ^ 2) :=
      mul_le_mul ha hb (by positivity) (by positivity)
    nlinarith
  have hlog3 : Real.log (2 * ((1 + (40 + 2400 * q)) * (8 * (1 + 32 * q) ^ 2 + 200 * q ^ 2))) ≤
      29 * Real.log (2 + q) := by
    have := log_pow_bound (c := 67108864) hq (by norm_num) (a := 26) (k := 3) (by norm_num)
    push_cast at this
    exact (Real.log_le_log (by positivity) hinner3).trans (by linarith)
  have hL : (1 : ℝ) / 2 ≤ Real.log (2 + q) := by
    have h2 := Real.log_two_gt_d9
    have h3 := Real.log_le_log (by norm_num : (0:ℝ) < 2) (by linarith : (2:ℝ) ≤ 2 + q)
    linarith
  have hqL : 0 ≤ q * Real.log (2 + q) := mul_nonneg hq hl.le
  have e1 : 1067 * (1 + q) * (14 * Real.log (2 + q)) =
      14938 * Real.log (2 + q) + 14938 * (q * Real.log (2 + q)) := by ring
  have e2 : 15100 * (1 + q) * Real.log (2 + q) =
      15100 * Real.log (2 + q) + 15100 * (q * Real.log (2 + q)) := by ring
  rw [e1] at hterm1
  rw [e2]
  clear e1 e2 hinner1 hinner2 hinner3 hlog1 hs6 hs0 h1
  generalize hX : Real.log (1 + (12 + 400 * q) * (1 + 1 + Real.sqrt (6 * q))) = X at hterm1 ⊢
  generalize hY : Real.log (5 / 2 + 1 / 16 + 132 * q) = Y at hlog2 ⊢
  generalize hZ : Real.log (2 * ((1 + (40 + 2400 * q)) * (8 * (1 + 32 * q) ^ 2 + 200 * q ^ 2))) = Z
    at hlog3 ⊢
  generalize hLg : Real.log (2 + q) = L at hterm1 hlog2 hlog3 hL hqL hl ⊢
  generalize hS : Real.sqrt A = S
  nlinarith [hterm1, hlog2, hlog3, hL, hqL]

end OracleTemplate.CompositeSherpa
