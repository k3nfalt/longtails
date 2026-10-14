import LongTails.Proofs.StochasticGeneralizedRateTuning
import LongTails.Proofs.StochasticGeneralizedBudget

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate tentativeWeight coupling)

lemma initial_up_prefix_raw (p : Params) (hp : spec.valid p) (hL1 : 0 < p.L1)
    (hεΔ : p.ε < p.Δ) (v h : ℕ → p.E → p.E) (N m : ℕ) (hm : m ≤ N)
    (hu : ∀ i < m, runUp p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) i = true)
    (hD : (∑ i ∈ Finset.range N, dissipation p.L0 p.L1 (v i)
      (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) i)) ≤ 3*p.R^2) :
    (m : ℝ) ≤ 10+3/2*(p.L1*p.R)^(2/3 : ℝ)+1/2*Real.log (p.Δ/p.ε) := by
  let s := initialIterate p.L0 p.R p.Δ p.ε p.x0
  have hL0 := hp.1
  have hR := hp.2.2.1
  have hΔ := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.1
  have ha : 0 < p.L1*p.R := mul_pos hL1 hR
  have hr : 1 ≤ p.Δ/p.ε := (one_le_div hε).mpr hεΔ.le
  have ht := ratio_tuning ha hr
  by_cases hm3 : m < 3
  · have hmr : (m : ℝ) ≤ 3 := by exact_mod_cast hm3.le
    have hlog : 0 ≤ Real.log (p.Δ/p.ε) := Real.log_nonneg hr
    have ht0 : 0 ≤ (p.L1*p.R)^(2/3 : ℝ) := Real.rpow_nonneg ha.le _
    nlinarith
  · let i := m-1
    have hi2 : 2 ≤ i := by dsimp [i]; omega
    have him : i < m := by dsimp [i]; omega
    have hiN : i < N := lt_of_lt_of_le him hm
    have hv := initial_valid p hp
    have hA0 : 0 < s.A := by dsimp [s, initialIterate]; positivity
    have hgi := run_up_guess p.L0 p.L1 v h s i (fun j hj => hu j (lt_trans hj him))
    have hp16 : (256 : ℝ) ≤ 16^i := by
      calc
        _ = (16 : ℝ)^2 := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hi2
    have hGi : 256*p.L0 ≤ (run p.L0 p.L1 v h s i).guess := by
      rw [hgi]
      exact (mul_le_mul_of_nonneg_right hp16 hL0.le).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
    have hiup : (run p.L0 p.L1 v h s i).guess <
        16*(p.L0+p.L1*‖v i (coupling (run p.L0 p.L1 v h s i))‖) := of_decide_eq_true (hu i him)
    have hh := run_high_point_le hL0 hL1 v h s hA0.le hv.2 N i hiN hD hiup.le (by linarith)
    rw [hgi] at hh
    have hG0 : 1/target p.R p.ε ≤ s.guess := le_max_right _ _
    have hprod := mul_le_mul_of_nonneg_left hG0 hA0.le
    have he : s.A*(1/target p.R p.ε) = p.ε/(32*p.Δ) := by
      dsimp [s, initialIterate, target]
      field_simp; ring
    rw [he] at hprod
    have hlo := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (16 : ℝ)^i by positivity)
    have hscaled : p.ε*(16 : ℝ)^i/(32*p.Δ) ≤ 8192*(p.L1*p.R)^2 := by
      calc
        _ = (16 : ℝ)^i*(p.ε/(32*p.Δ)) := by ring
        _ ≤ (16 : ℝ)^i*(s.A*s.guess) := hlo
        _ ≤ _ := by nlinarith only [hh]
    have hpower : (16 : ℝ)^i ≤ 262144*(p.L1*p.R)^2*(p.Δ/p.ε) := by
      have hs := (div_le_iff₀ (show 0 < 32*p.Δ by positivity)).mp hscaled
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hε).mpr
      nlinarith only [hs]
    have hc := up_power_count_raw ha hr i hpower
    have heq : i+1=m := by dsimp [i]; omega
    rw [heq] at hc
    simpa only [mul_div_assoc] using hc

lemma initial_up_prefix_bound (p : Params) (hp : spec.valid p) (hL1 : 0 < p.L1)
    (hεΔ : p.ε < p.Δ) (v h : ℕ → p.E → p.E) (N m : ℕ) (hm : m ≤ N)
    (hu : ∀ i < m, runUp p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) i = true)
    (hD : (∑ i ∈ Finset.range N, dissipation p.L0 p.L1 (v i)
      (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) i)) ≤ 3*p.R^2) :
    (m : ℝ) ≤ 16*(⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε) := by
  have hε := hp.2.2.2.2.2.1
  have hr : 1 ≤ p.Δ/p.ε := (one_le_div hε).mpr hεΔ.le
  have hh := startup_count_simplify (mul_pos hL1 hp.2.2.1) hr
    (initial_up_prefix_raw p hp hL1 hεΔ v h N m hm hu hD)
  simpa only [mul_div_assoc] using hh

lemma initial_up_guess_bound (p : Params) (hp : spec.valid p) (hL1 : 0 < p.L1)
    (v h : ℕ → p.E → p.E) (N m : ℕ) (hm : m ≤ N)
    (hu : ∀ i < m, runUp p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) i = true)
    (hD : (∑ i ∈ Finset.range N, dissipation p.L0 p.L1 (v i)
      (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) i)) ≤ 3*p.R^2) :
    (run p.L0 p.L1 v h (initialIterate p.L0 p.R p.Δ p.ε p.x0) m).guess*target p.R p.ε ≤
      1+8192*(Real.sqrt (p.L0*p.R^2/p.ε))^2+4194304*(p.L1*p.R)^2*(p.Δ/p.ε) := by
  let s := initialIterate p.L0 p.R p.Δ p.ε p.x0
  have hL0 := hp.1
  have hR := hp.2.2.1
  have hΔ := hp.2.2.2.1
  have hε := hp.2.2.2.2.2.1
  have hT : 0 < target p.R p.ε := by dsimp [target]; positivity
  have hS : (Real.sqrt (p.L0*p.R^2/p.ε))^2 = p.L0*p.R^2/p.ε := Real.sq_sqrt (by positivity)
  have hnoise : 0 ≤ 4194304*(p.L1*p.R)^2*(p.Δ/p.ε) := by positivity
  cases m with
  | zero =>
    change s.guess*target p.R p.ε ≤ _
    have hguess : s.guess ≤ p.L0+1/target p.R p.ε :=
      max_le (by linarith [one_div_pos.mpr hT]) (by linarith)
    have hh := mul_le_mul_of_nonneg_right hguess hT.le
    rw [add_mul, one_div_mul_cancel hT.ne'] at hh
    rw [hS]
    dsimp [target] at *
    have hx : 0 ≤ p.L0*p.R^2/p.ε := by positivity
    simp only [div_eq_mul_inv] at hh hnoise hx ⊢
    nlinarith only [hh, hnoise, hx]
  | succ j =>
    have hiN : j < N := by omega
    have hiup : (run p.L0 p.L1 v h s j).guess <
        16*(p.L0+p.L1*‖v j (coupling (run p.L0 p.L1 v h s j))‖) := of_decide_eq_true (hu j (by omega))
    have heG : (run p.L0 p.L1 v h s (j+1)).guess = 16*(run p.L0 p.L1 v h s j).guess := by
      change (step p.L0 p.L1 (v j) (h j) (run p.L0 p.L1 v h s j)).guess = _
      rw [step_guess, ite_eq_right (not_le.mpr hiup)]
    change (run p.L0 p.L1 v h s (j+1)).guess*target p.R p.ε ≤ _
    rw [heG]
    by_cases hj : (run p.L0 p.L1 v h s j).guess ≤ 32*p.L0
    · have hh := mul_le_mul_of_nonneg_right hj (show 0 ≤ 16*target p.R p.ε by positivity)
      rw [hS]
      dsimp [target] at *
      simp only [div_eq_mul_inv] at hh hnoise ⊢
      nlinarith only [hh, hnoise]
    · have hv := initial_valid p hp
      have hA0 : 0 < s.A := by dsimp [s, initialIterate]; positivity
      have hh := run_high_point_le hL0 hL1 v h s hA0.le hv.2 N j hiN hD hiup.le (by linarith)
      have hb : (run p.L0 p.L1 v h s j).guess ≤ 8192*(p.L1*p.R)^2/s.A :=
        (le_div_iff₀ hA0).mpr (by nlinarith only [hh])
      have hm' := mul_le_mul_of_nonneg_right hb (show 0 ≤ 16*target p.R p.ε by positivity)
      have he : (8192*(p.L1*p.R)^2/s.A)*(16*target p.R p.ε) =
          4194304*(p.L1*p.R)^2*(p.Δ/p.ε) := by
        dsimp [s, initialIterate, target]
        field_simp; ring
      rw [he] at hm'
      nlinarith only [hm', sq_nonneg (Real.sqrt (p.L0*p.R^2/p.ε))]

end OracleTemplate.StochasticGeneralized
