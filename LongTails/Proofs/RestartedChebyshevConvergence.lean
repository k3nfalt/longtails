import LongTails.Proofs.RestartedChebyshevCount
import LongTails.Proofs.RestartedChebyshevNumeric
import LongTails.Proofs.FractalChebyshevParams
import LongTails.Proofs.Execution
import LongTails.Algorithms.RestartedChebyshevGd
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.RestartedScheduleGD

open OracleTemplate.FractalChebyshev OracleTemplate.ScheduleBlock

section Schedule

variable {L : ℝ} {k : ℕ}

lemma schedule_pos (hL : 0 < L) (hk : 2 ≤ k) : ∀ h ∈ schedule L (muOf L k) k, 0 < h := by
  intro h hh
  obtain ⟨hμ, hμL⟩ := muOf_bounds hL hk
  unfold schedule at hh
  obtain ⟨θ, -, rfl⟩ := List.mem_map.mp hh
  exact lt_of_lt_of_le (one_div_pos.mpr hL) (stepOf_bounds hμ hμL θ).1

lemma runS_schedule (L μ : ℝ) (k : ℕ) :
    runS (schedule L μ k) = ssum (etaOf L μ k) (2 ^ k) := by
  unfold runS
  rw [schedule_length]
  rfl

lemma runS_eq_sum (l : List ℝ) : runS l = l.sum := by
  unfold runS ssum
  exact sum_range_getD l

lemma schedule_facts (hL : 0 < L) (hk : 2 ≤ k) :
    ScheduleFacts (fun j => (schedule L (muOf L k) k).getD j 0) (schedule L (muOf L k) k).length L
      (L / muOf L k) := by
  obtain ⟨hμ, hμL⟩ := muOf_bounds hL hk
  rw [schedule_length]
  exact {
    hL := hL
    hK := one_le_kappa hL hk
    eta_nonneg := fun j => etaOf_nonneg hμ hμL k j
    eta_pos := fun j hj => lt_of_lt_of_le (one_div_pos.mpr hL) (etaOf_bounds hμ hμL hj).1
    eta_le := fun j hj => by
      have := (etaOf_bounds hμ hμL hj).2
      have e : L / muOf L k / L = 1 / muOf L k := by field_simp
      rw [e]; exact this
    win_le := fun lam h0 hl s t hst ht => window_bound hμ hμL k h0 hl hst ht
    pre_le := fun lam h0 hl t ht => prefix_bound hμ hμL k h0 hl ht
    fin := fun lam h0 hl => final_relation hμ hμL k (final_hyp hL hk) h0 hl }

end Schedule

lemma num_hyp_of_depth {L ρ ε : ℝ} {k : ℕ} (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) (hk : 2 ≤ k)
    (hdep : ((2:ℝ) ^ k) ^ 9 ≤ L ^ 2 / (2 ^ 22 * ρ * ε)) :
    NumHyp (ssum (etaOf L (muOf L k) k) (2 ^ k)) ε (2 ^ k) (L / muOf L k) L ρ := by
  set S := ssum (etaOf L (muOf L k) k) (2 ^ k)
  set n : ℝ := 2 ^ k
  have hlo := ssum_lower hL hk
  have hup := ssum_upper hL hk
  have hκ := kappa_le hL hk
  have hκ1 := one_le_kappa hL hk
  have hm4 : (4:ℝ) ≤ (k : ℝ) + 2 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hmn : (k : ℝ) + 2 ≤ n := by
    have h := (Nat.cast_le (α := ℝ)).mpr (nat_add_two_le_pow hk)
    push_cast at h
    exact h
  have hn4 : (4:ℝ) ≤ n := le_trans hm4 hmn
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hlo
  set m : ℝ := (k : ℝ) + 2
  have hm0 : 0 < m := by linarith
  have hLS : L * S ≤ n ^ 2 := by
    have h1 : L * S ≤ L * (3 * n ^ 2 / (m * L)) := mul_le_mul_of_nonneg_left hup hL.le
    have h2 : L * (3 * n ^ 2 / (m * L)) = 3 * n ^ 2 / m := by field_simp
    rw [h2] at h1
    have h3 : 3 * n ^ 2 / m ≤ n ^ 2 := by
      rw [div_le_iff₀ hm0]; nlinarith
    linarith
  have hSL : n ≤ 16 * L * S := by
    have h1 : 16 * L * (n ^ 2 / (16 * m * L)) ≤ 16 * L * S :=
      mul_le_mul_of_nonneg_left hlo (by positivity)
    have h2 : 16 * L * (n ^ 2 / (16 * m * L)) = n ^ 2 / m := by field_simp
    rw [h2] at h1
    have h3 : n ≤ n ^ 2 / m := by
      rw [le_div_iff₀ hm0]; nlinarith
    linarith
  have hS2 : S ^ 2 ≤ 9 * n ^ 4 / (16 * L ^ 2) := by
    have h1 : S ≤ 3 * n ^ 2 / (4 * L) := by
      refine hup.trans ?_
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have h2 := pow_le_pow_left₀ hS.le h1 2
    have e : (3 * n ^ 2 / (4 * L)) ^ 2 = 9 * n ^ 4 / (16 * L ^ 2) := by ring
    linarith
  have hK : L / muOf L k ≤ 3 * n ^ 2 / 16 := by
    refine hκ.trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    nlinarith
  have hn9 : ρ * ε * n ^ 9 ≤ L ^ 2 / 2 ^ 22 := by
    have e : L ^ 2 / (2 ^ 22 * ρ * ε) = L ^ 2 / 2 ^ 22 / (ρ * ε) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)] at hdep
    linarith
  have hΘ : ρ * S ^ 2 * n * ε ≤ 9 * ρ * ε * n ^ 5 / (16 * L ^ 2) := by
    have := mul_le_mul_of_nonneg_left hS2 (by positivity : 0 ≤ ρ * n * ε)
    have e : ρ * n * ε * (9 * n ^ 4 / (16 * L ^ 2)) = 9 * ρ * ε * n ^ 5 / (16 * L ^ 2) := by ring
    nlinarith
  have hΘ0 : 0 ≤ ρ * S ^ 2 * n * ε := by positivity
  have hL2 : 0 < L ^ 2 := by positivity
  refine ⟨hS, hε, hn4, hκ1, hL, hρ, hLS, hSL, ?_, ?_⟩
  · have h1 : L / muOf L k * (ρ * S ^ 2 * n * ε) * n ^ 2 ≤
        3 * n ^ 2 / 16 * (9 * ρ * ε * n ^ 5 / (16 * L ^ 2)) * n ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hK hΘ hΘ0 (by positivity)
    have e : 3 * n ^ 2 / 16 * (9 * ρ * ε * n ^ 5 / (16 * L ^ 2)) * n ^ 2 =
        27 / 256 * (ρ * ε * n ^ 9) / L ^ 2 := by field_simp; ring
    rw [e] at h1
    have h2 : 27 / 256 * (ρ * ε * n ^ 9) / L ^ 2 ≤ 27 / 256 * (L ^ 2 / 2 ^ 22) / L ^ 2 := by
      apply div_le_div_of_nonneg_right _ hL2.le
      linarith
    have h3 : 27 / 256 * (L ^ 2 / 2 ^ 22) / L ^ 2 = 27 / 256 / 2 ^ 22 := by field_simp
    rw [h3] at h2
    have h4 : (27:ℝ) / 256 / 2 ^ 22 ≤ 1 / 10 ^ 7 := by norm_num
    linarith
  · have h1 : (ρ * S ^ 2 * n * ε) * n ^ 3 ≤ 9 * ρ * ε * n ^ 5 / (16 * L ^ 2) * n ^ 3 :=
      mul_le_mul_of_nonneg_right hΘ (by positivity)
    have e : 9 * ρ * ε * n ^ 5 / (16 * L ^ 2) * n ^ 3 = 9 / 16 * (ρ * ε * n ^ 8) / L ^ 2 := by
      field_simp
    rw [e] at h1
    have hn8 : ρ * ε * n ^ 8 ≤ ρ * ε * n ^ 9 / 4 := by
      have : 0 ≤ ρ * ε * n ^ 8 := by positivity
      have e2 : ρ * ε * n ^ 9 = ρ * ε * n ^ 8 * n := by ring
      rw [e2]; nlinarith
    have h2 : 9 / 16 * (ρ * ε * n ^ 8) / L ^ 2 ≤ 9 / 64 * (L ^ 2 / 2 ^ 22) / L ^ 2 := by
      apply div_le_div_of_nonneg_right _ hL2.le
      linarith
    have h3 : 9 / 64 * (L ^ 2 / 2 ^ 22) / L ^ 2 = 9 / 64 / 2 ^ 22 := by field_simp
    rw [h3] at h2
    have h4 : (9:ℝ) / 64 / 2 ^ 22 ≤ 1 / 10 ^ 7 := by norm_num
    linarith

lemma depth_large {L ρ ε : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) (hk : 2 ≤ depth L ρ ε) :
    ((2:ℝ) ^ depth L ρ ε) ^ 9 ≤ L ^ 2 / (2 ^ 22 * ρ * ε) ∧
      L ^ 2 / (2 ^ 22 * ρ * ε) < ((2:ℝ) ^ depth L ρ ε) ^ 9 * 512 := by
  set M := L ^ 2 / (2 ^ 22 * ρ * ε)
  have hM : 0 ≤ M := by positivity
  set lg := Nat.log 2 ⌊M⌋₊
  have hdk : depth L ρ ε = lg / 9 := rfl
  have hlg : 18 ≤ lg := by omega
  have hfl : ⌊M⌋₊ ≠ 0 := by
    intro h0
    have : lg = 0 := by simp [lg, h0]
    omega
  constructor
  · have h1 : 2 ^ (9 * depth L ρ ε) ≤ 2 ^ lg := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := Nat.pow_log_le_self 2 hfl
    have h3 : ((2 ^ (9 * depth L ρ ε) : ℕ) : ℝ) ≤ (⌊M⌋₊ : ℝ) := by exact_mod_cast h1.trans h2
    have h4 := Nat.floor_le hM
    push_cast at h3
    rw [← pow_mul, mul_comm]
    linarith
  · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊M⌋₊
    have h2 : 2 ^ (lg.succ) ≤ 2 ^ (9 * depth L ρ ε + 9) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [hdk]; omega)
    have h3 : (⌊M⌋₊ : ℝ) + 1 ≤ ((2 ^ (9 * depth L ρ ε + 9) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (h1.trans_le h2))
    have h4 := Nat.lt_floor_add_one M
    push_cast at h3
    have e : ((2:ℝ) ^ depth L ρ ε) ^ 9 * 512 = 2 ^ (9 * depth L ρ ε + 9) := by
      rw [← pow_mul, pow_add]; norm_num; ring
    rw [e]
    linarith

lemma depth_small {L ρ ε : ℝ} (hk : ¬ 2 ≤ depth L ρ ε) :
    L ^ 2 / (2 ^ 22 * ρ * ε) < 2 ^ 18 := by
  set M := L ^ 2 / (2 ^ 22 * ρ * ε)
  have hdk : depth L ρ ε = Nat.log 2 ⌊M⌋₊ / 9 := rfl
  have hlg : Nat.log 2 ⌊M⌋₊ < 18 := by omega
  have h1 := Nat.lt_pow_of_log_lt (by norm_num : 1 < 2) hlg
  have h2 : (⌊M⌋₊ : ℝ) + 1 ≤ ((2 ^ 18 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h1
  have h3 := Nat.lt_floor_add_one M
  push_cast at h2
  linarith

theorem run_hyp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {L ρ ε : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hk : 2 ≤ depth L ρ ε) :
    RunHyp f L ρ ε (chebyshevThreshold L ρ ε) (chebyshevRadius L ρ ε)
      (L / muOf L (depth L ρ ε)) (chebyshevSteps L ρ ε) := by
  set k := depth L ρ ε
  have hsteps : chebyshevSteps L ρ ε = schedule L (muOf L k) k := ite_eq_left hk
  have hthr : chebyshevThreshold L ρ ε = 2 ^ k * ε := ite_eq_left hk
  have hrad : chebyshevRadius L ρ ε =
      8 * ssum (etaOf L (muOf L k) k) (2 ^ k) * ((2:ℝ) ^ k * ε) := by
    unfold chebyshevRadius
    rw [hsteps, hthr, ← runS_eq_sum, runS_schedule]
  have hN := num_hyp_of_depth hL hρ hε hk (depth_large hL hρ hε hk).1
  rw [hsteps, hthr, hrad]
  have hlen : ((schedule L (muOf L k) k).length : ℝ) = 2 ^ k := by
    rw [schedule_length]; push_cast; ring
  have hS := hN.hS
  refine ⟨hf, hρ.le, hH, hlip, schedule_facts hL hk, ?_, ?_, ?_, hε, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [schedule_length]; exact Nat.one_le_two_pow
  · positivity
  · positivity
  · unfold runA runQ
    rw [runS_schedule, hlen]
    exact num_plain hN
  · rw [runS_schedule, hlen]
    unfold runQ
    rw [runS_schedule]
    exact num_completed hN
  · rw [runS_schedule]
    unfold runQ
    rw [runS_schedule]
    exact num_pred hN
  · rw [runS_schedule]
    exact num_exit1 hN
  · rw [runS_schedule]
    unfold runQ
    rw [runS_schedule]
    exact num_exit2 hN
  · exact num_err hN

lemma rpow_ninth {X : ℝ} (hX : 0 < X) : (X ^ (1 / 9 : ℝ)) ^ 9 = X := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]; norm_num

lemma budget_large {L ρ ε Δ : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) (hΔ0 : 0 ≤ Δ)
    (hk : 2 ≤ depth L ρ ε) :
    (Δ + runQ (chebyshevSteps L ρ ε) ε) / runA (chebyshevSteps L ρ ε) ε +
        (chebyshevSteps L ρ ε).length ≤
      1000 * Real.logb 2 (2 + L ^ 2 / (ρ * ε)) * (ρ * ε / L ^ 2) ^ (1 / 9 : ℝ) * L * Δ / ε ^ 2 +
        (L ^ 2 / (ρ * ε)) ^ (1 / 9 : ℝ) + 2 := by
  set k := depth L ρ ε
  have hsteps : chebyshevSteps L ρ ε = schedule L (muOf L k) k := ite_eq_left hk
  rw [hsteps]
  unfold runA runQ
  rw [runS_schedule, schedule_length]
  push_cast
  set S := ssum (etaOf L (muOf L k) k) (2 ^ k)
  set n : ℝ := 2 ^ k
  set X := L ^ 2 / (ρ * ε)
  have hX : 0 < X := by positivity
  set t := X ^ (1 / 9 : ℝ)
  have ht : 0 < t := Real.rpow_pos_of_pos hX _
  have ht9 : t ^ 9 = X := rpow_ninth hX
  have hinv : (ρ * ε / L ^ 2) ^ (1 / 9 : ℝ) = 1 / t := by
    have : ρ * ε / L ^ 2 = X⁻¹ := by simp only [X]; field_simp
    rw [this, Real.inv_rpow hX.le]
    exact (one_div t).symm
  rw [hinv]
  obtain ⟨hlo9, hhi9⟩ := depth_large hL hρ hε hk
  have hM : L ^ 2 / (2 ^ 22 * ρ * ε) = X / 2 ^ 22 := by simp only [X]; field_simp
  rw [hM] at hlo9 hhi9
  have hlo := ssum_lower hL hk
  have hS : 0 < S := lt_of_lt_of_le (by positivity) hlo
  have hn : (4:ℝ) ≤ n := by
    have : (2:ℝ) ^ 2 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    simp only [n]; linarith
  have hm4 : (4:ℝ) ≤ (k : ℝ) + 2 := by
    have : (2:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h3n : 3 * n ≤ t := by
    have h1 : (3 * n) ^ 9 ≤ t ^ 9 := by
      rw [ht9, mul_pow]
      have : (3:ℝ) ^ 9 ≤ 2 ^ 22 := by norm_num
      have hn9 : 0 ≤ n ^ 9 := by positivity
      have := mul_le_mul_of_nonneg_left hlo9 (by norm_num : (0:ℝ) ≤ 3 ^ 9)
      have e : (3:ℝ) ^ 9 * (X / 2 ^ 22) ≤ X := by
        rw [mul_div_assoc', div_le_iff₀ (by norm_num)]; nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) ht.le (by norm_num)).mp h1
  have htn : t < 11 * n := by
    have h1 : t ^ 9 < (11 * n) ^ 9 := by
      rw [ht9, mul_pow]
      have h2 : X < n ^ 9 * 512 * 2 ^ 22 := by
        have := hhi9
        rw [div_lt_iff₀ (by norm_num)] at this; linarith
      have : (512:ℝ) * 2 ^ 22 ≤ 11 ^ 9 := by norm_num
      have hn9 : 0 ≤ n ^ 9 := by positivity
      nlinarith
    exact (pow_lt_pow_iff_left₀ ht.le (by positivity) (by norm_num)).mp h1
  set ℓ := Real.logb 2 (2 + X)
  have hℓk : 9 * ((k : ℝ) + 2) ≤ ℓ := by
    have h1 : (2:ℝ) ^ (9 * (k : ℝ) + 22) ≤ X := by
      rw [show (9 * (k : ℝ) + 22) = ((9 * k + 22 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      have : (2:ℝ) ^ (9 * k + 22) = n ^ 9 * 2 ^ 22 := by
        simp only [n]; rw [← pow_mul, ← pow_add]; ring_nf
      rw [this]
      rw [le_div_iff₀ (by norm_num)] at hlo9
      linarith
    have h2 : 9 * (k : ℝ) + 22 ≤ Real.logb 2 X := (Real.le_logb_iff_rpow_le (by norm_num) hX).mpr h1
    have h3 : Real.logb 2 X ≤ ℓ := Real.logb_le_logb_of_le (by norm_num) hX (by linarith)
    linarith
  have hfirst : 2 * n * (Δ + S * ε ^ 2 / 16) / (S * ε ^ 2 / 16) + n =
      32 * n * Δ / (S * ε ^ 2) + 3 * n := by
    field_simp; ring
  have key1 : 32 * n * Δ / (S * ε ^ 2) ≤ 512 * ((k : ℝ) + 2) * L * Δ / (n * ε ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : n ^ 2 ≤ 16 * ((k : ℝ) + 2) * L * S := by
      rw [div_le_iff₀ (by positivity)] at hlo; linarith
    have : 0 ≤ 32 * Δ * ε ^ 2 := by positivity
    nlinarith
  have key2 : 512 * ((k : ℝ) + 2) * L * Δ / (n * ε ^ 2) ≤ 1000 * ℓ * (1 / t) * L * Δ / ε ^ 2 := by
    have hLΔ : 0 ≤ L * Δ / ε ^ 2 := by positivity
    have e1 : 512 * ((k : ℝ) + 2) * L * Δ / (n * ε ^ 2) =
        512 * ((k : ℝ) + 2) / n * (L * Δ / ε ^ 2) := by
      field_simp
    have e2 : 1000 * ℓ * (1 / t) * L * Δ / ε ^ 2 = 1000 * ℓ / t * (L * Δ / ε ^ 2) := by
      field_simp
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_right _ hLΔ
    rw [div_le_div_iff₀ (by positivity) ht]
    have hk0 : 0 ≤ (k : ℝ) + 2 := by positivity
    have p1 : ((k : ℝ) + 2) * t ≤ ((k : ℝ) + 2) * (11 * n) :=
      mul_le_mul_of_nonneg_left htn.le hk0
    have p2 : 9 * ((k : ℝ) + 2) * n ≤ ℓ * n :=
      mul_le_mul_of_nonneg_right hℓk (by positivity)
    have p3 : 0 ≤ ℓ * n := by nlinarith
    nlinarith
  have e0 : (Δ + S * ε ^ 2 / 16) / (S * ε ^ 2 / 16 / (2 * n)) + n =
      2 * n * (Δ + S * ε ^ 2 / 16) / (S * ε ^ 2 / 16) + n := by
    field_simp
  rw [e0, hfirst]
  linarith

lemma budget_small {L ρ ε Δ : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hε : 0 < ε) (hΔ0 : 0 ≤ Δ)
    (hk : ¬ 2 ≤ depth L ρ ε) :
    2 * L * Δ / ε ^ 2 <
      1000 * Real.logb 2 (2 + L ^ 2 / (ρ * ε)) * (ρ * ε / L ^ 2) ^ (1 / 9 : ℝ) * L * Δ / ε ^ 2 +
        (L ^ 2 / (ρ * ε)) ^ (1 / 9 : ℝ) + 2 := by
  set X := L ^ 2 / (ρ * ε)
  have hX : 0 < X := by positivity
  set t := X ^ (1 / 9 : ℝ)
  have ht : 0 < t := Real.rpow_pos_of_pos hX _
  have ht9 : t ^ 9 = X := rpow_ninth hX
  have hinv : (ρ * ε / L ^ 2) ^ (1 / 9 : ℝ) = 1 / t := by
    have : ρ * ε / L ^ 2 = X⁻¹ := by simp only [X]; field_simp
    rw [this, Real.inv_rpow hX.le]
    exact (one_div t).symm
  rw [hinv]
  have hsm := depth_small hk
  have hM : L ^ 2 / (2 ^ 22 * ρ * ε) = X / 2 ^ 22 := by simp only [X]; field_simp
  rw [hM, div_lt_iff₀ (by norm_num)] at hsm
  have ht32 : t < 32 := by
    have h1 : t ^ 9 < 32 ^ 9 := by rw [ht9]; norm_num at hsm ⊢; linarith
    exact (pow_lt_pow_iff_left₀ ht.le (by norm_num) (by norm_num)).mp h1
  have hℓ : 1 ≤ Real.logb 2 (2 + X) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    norm_num; linarith
  have hLΔ : 0 ≤ L * Δ / ε ^ 2 := by positivity
  have e2 : 1000 * Real.logb 2 (2 + X) * (1 / t) * L * Δ / ε ^ 2 =
      1000 * Real.logb 2 (2 + X) / t * (L * Δ / ε ^ 2) := by field_simp
  have h1 : 2 ≤ 1000 * Real.logb 2 (2 + X) / t := by
    rw [le_div_iff₀ ht]; nlinarith
  have e3 : 2 * L * Δ / ε ^ 2 = 2 * (L * Δ / ε ^ 2) := by ring
  rw [e2, e3]
  have := mul_le_mul_of_nonneg_right h1 hLΔ
  linarith

theorem chebyshev_output {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {L ρ Δ ε : ℝ} {x0 : E} (hL : 0 < L) (hρ : 0 < ρ)
    (hΔ0 : 0 ≤ Δ) (hε : 0 < ε) (hf : ContDiff ℝ 2 f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hΔ : ∀ x, f x0 - f x ≤ Δ) (N : ℕ)
    (hN : 1000 * Real.logb 2 (2 + L ^ 2 / (ρ * ε)) * (ρ * ε / L ^ 2) ^ (1 / 9 : ℝ) * L * Δ /
        ε ^ 2 + (L ^ 2 / (ρ * ε)) ^ (1 / 9 : ℝ) + 2 ≤ N) :
    ‖gradient f ((stepS f L ε (chebyshevThreshold L ρ ε) (chebyshevRadius L ρ ε)
      (chebyshevSteps L ρ ε) x0)^[N] ⟨x0, x0, 0, false⟩).point‖ ≤ ε := by
  set T := stepS f L ε (chebyshevThreshold L ρ ε) (chebyshevRadius L ρ ε) (chebyshevSteps L ρ ε) x0
  by_cases hall : ∀ t < N, ε < ‖gradient f (T^[t] ⟨x0, x0, 0, false⟩).point‖
  · exfalso
    by_cases hk : 2 ≤ depth L ρ ε
    · have H := run_hyp hL hρ hε hf hH hlip hk
      have hc := count_bound H hΔ N hall
      have hb := budget_large hL hρ hε hΔ0 hk (Δ := Δ)
      linarith
    · have hsteps : chebyshevSteps L ρ ε = [] := ite_eq_right hk
      have hthr : chebyshevThreshold L ρ ε = 0 := ite_eq_right hk
      have hall' := hall
      simp only [T, hsteps, hthr] at hall'
      have hg := gd_bound hf hL hε hlip hΔ N hall'
      have hb := budget_small hL hρ hε hΔ0 hk
      have h1 : 2 * L * Δ / ε ^ 2 < N := by linarith
      rw [div_lt_iff₀ (by positivity)] at h1
      linarith
  · push Not at hall
    obtain ⟨t, htN, ht⟩ := hall
    have hsplit : T^[N] ⟨x0, x0, 0, false⟩ = T^[N - t] (T^[t] ⟨x0, x0, 0, false⟩) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [hsplit, iterate_stop _ (Or.inr ht)]
    exact ht

end OracleTemplate.RestartedScheduleGD
