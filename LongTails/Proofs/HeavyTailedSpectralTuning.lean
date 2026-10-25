import LongTails.Proofs.HeavyTailedSpectralMoments
import Mathlib.Algebra.Order.Floor.Semiring

namespace LongTails.Proofs.HeavyTailedSpectralTuning

lemma probe_step_bounds {M γ σ p c D : ℝ} (hM : 0 < M) (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hp : 1 < p) (hc : 0 < c) (hD : 0 < D) (hγM : γ ≤ M) :
    let η := 1 / (M + (256 * D * σ ^ p / (c * γ)) ^ (1 / (p - 1)))
    0 < η ∧ η * M ≤ 1 ∧ η * γ ≤ 1 ∧ η ^ (p - 1) * σ ^ p ≤ c * γ / (256 * D) := by
  let K := 256 * D * σ ^ p / (c * γ)
  let a := K ^ (1 / (p - 1))
  intro η
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have ha : 0 ≤ a := Real.rpow_nonneg hK _
  have hden : 0 < M + a := by positivity
  have hη : 0 < η := one_div_pos.mpr hden
  have heq : η * (M + a) = 1 := one_div_mul_cancel hden.ne'
  have hηM : η * M ≤ 1 := by nlinarith [mul_nonneg hη.le ha]
  have hηγ : η * γ ≤ 1 := (mul_le_mul_of_nonneg_left hγM hη.le).trans hηM
  refine ⟨hη, hηM, hηγ, ?_⟩
  have hηa : η * a ≤ 1 := by nlinarith [mul_nonneg hη.le hM.le]
  have hpow := Real.rpow_le_rpow (mul_nonneg hη.le ha) hηa (by linarith : 0 ≤ p - 1)
  rw [Real.mul_rpow hη.le ha, Real.one_rpow] at hpow
  have haeq : a ^ (p - 1) = K := by
    dsimp only [a]
    rw [← Real.rpow_mul hK, one_div_mul_cancel (by linarith : p - 1 ≠ 0), Real.rpow_one]
  rw [haeq] at hpow
  dsimp only [K] at hpow
  have hh : η ^ (p - 1) * (256 * D * σ ^ p) ≤ c * γ := by
    have hh := (div_le_iff₀ (mul_pos hc hγ)).mp
      (show η ^ (p - 1) * (256 * D * σ ^ p) / (c * γ) ≤ 1 from by
        convert hpow using 1
        ring)
    simpa using hh
  apply (le_div_iff₀ (by positivity : 0 < 256 * D)).mpr
  nlinarith

lemma probe_count_bounds {D η γ σ p c : ℝ} (hD : 1 ≤ D) (hη : 0 < η)
    (hγ : 0 < γ) (hσ : 0 ≤ σ) (hηγ : η * γ ≤ 1)
    (heff : η ^ (p - 1) * σ ^ p ≤ c * γ / (256 * D)) :
    let n := ⌈2 * D / (η * γ)⌉₊
    0 < n ∧ 2 * D ≤ η * n * γ ∧ n * (η ^ p * σ ^ p) ≤ 3 * c / 256 := by
  intro n
  have hD0 : 0 < D := by linarith
  have hηγ0 := mul_pos hη hγ
  have hn0 : 0 < n := Nat.one_le_ceil_iff.mpr (by positivity)
  have hlo := Nat.le_ceil (2 * D / (η * γ))
  have hlo' := mul_le_mul_of_nonneg_right hlo hηγ0.le
  rw [div_mul_cancel₀ _ hηγ0.ne'] at hlo'
  have hhi := (Nat.ceil_lt_add_one (show 0 ≤ 2 * D / (η * γ) by positivity)).le
  have hhi' := mul_le_mul_of_nonneg_right hhi hηγ0.le
  rw [add_mul, div_mul_cancel₀ _ hηγ0.ne', one_mul] at hhi'
  have hnhi : (n : ℝ) * (η * γ) ≤ 3 * D := by linarith
  refine ⟨hn0, by nlinarith [hlo'], ?_⟩
  have hpow : η ^ p = η ^ (p - 1) * η := by
    have hh := Real.rpow_add_one hη.ne' (p - 1)
    simpa using hh
  have hz : (n * (η ^ p * σ ^ p)) * γ ≤ (3 * c / 256) * γ := by
    calc
      _ = ((n : ℝ) * (η * γ)) * (η ^ (p - 1) * σ ^ p) := by rw [hpow]; ring
      _ ≤ (3 * D) * (η ^ (p - 1) * σ ^ p) :=
        mul_le_mul_of_nonneg_right hnhi (by positivity)
      _ ≤ (3 * D) * (c * γ / (256 * D)) := mul_le_mul_of_nonneg_left heff (by positivity)
      _ = _ := by field_simp
  exact (mul_le_mul_iff_left₀ hγ).mp hz

lemma dimension_log_scale_ge {d : ℕ} (hd : 0 < d) :
    1 ≤ 4 * (Real.log (2 * Real.sqrt (2 * d)) + 2) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 * (d : ℝ) by positivity)
  have hs : 1 ≤ Real.sqrt (2 * d) := by nlinarith [Real.sqrt_nonneg (2 * (d : ℝ))]
  have hl := Real.log_nonneg (show 1 ≤ 2 * Real.sqrt (2 * d) by linarith)
  linarith

lemma probe_tuning {d : ℕ} {M γ σ p q : ℝ} (hd : 0 < d) (hM : 0 < M)
    (hγ : 0 < γ) (hσ : 0 ≤ σ) (hpq : p.HolderConjugate q) (hγM : γ ≤ M) :
    let c := (1 / 4 : ℝ) ^ q / 16
    let D := 4 * (Real.log (2 * Real.sqrt (2 * d)) + 2)
    let η := 1 / (M + (256 * D * σ ^ p / (c * γ)) ^ (1 / (p - 1)))
    let n := ⌈2 * D / (η * γ)⌉₊
    0 < η ∧ η * M ≤ 1 ∧ 0 < n ∧
      8 * (Real.log (2 * Real.sqrt (2 * d)) + 2) ≤ η * n * γ ∧
      n * (η ^ p * σ ^ p) ≤ (1 / 4 : ℝ) ^ q / 256 ∧
      ∀ ell, 0 ≤ ell → ell ≤ M →
        ((1 + η * ell) ^ p + 6 * η ^ p * σ ^ p) ^ n ≤ (2 * (1 + η * ell) ^ n) ^ p := by
  intro c D η n
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcmax : c ≤ 1 / 16 := by
    have hh := Real.rpow_le_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1) hpq.symm.nonneg
    dsimp only [c]
    linarith
  have hD : 1 ≤ D := dimension_log_scale_ge hd
  have hstep := probe_step_bounds hM hγ hσ hpq.lt hc (by linarith : 0 < D) hγM
  have hcount := probe_count_bounds hD hstep.1 hγ hσ hstep.2.2.1 hstep.2.2.2
  change 0 < n ∧ 2 * D ≤ η * n * γ ∧ n * (η ^ p * σ ^ p) ≤ 3 * c / 256 at hcount
  refine ⟨hstep.1, hstep.2.1, hcount.1, ?_, ?_, ?_⟩
  · convert hcount.2.1 using 1
    ring
  · have hh := hcount.2.2
    dsimp only [c] at hh hc
    linarith
  · intro ell hell _
    apply HeavyTailedSpectralMoments.small_inflation_power
      (show 1 ≤ 1 + η * ell by nlinarith [mul_nonneg hstep.1.le hell])
      (show 0 ≤ 6 * η ^ p * σ ^ p by positivity) hpq.lt.le n
    nlinarith [hcount.2.2]

end LongTails.Proofs.HeavyTailedSpectralTuning
