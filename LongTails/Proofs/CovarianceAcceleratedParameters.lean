import LongTails.Proofs.CovarianceAcceleratedRun

open LongTails.Algorithms.CovarianceAccelerated
open LongTails.Proofs.CovarianceAcceleratedRun

namespace LongTails.Proofs.CovarianceAcceleratedParameters

lemma squared_weights_sum_le (η : ℝ) (T : ℕ) :
    (∑ t ∈ Finset.range T, weight η t ^ 2) ≤ η ^ 2 * (T : ℝ) ^ 3 := by
  calc
    _ ≤ ∑ _ ∈ Finset.range T, η ^ 2 * (T : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' : (t : ℝ) + 1 ≤ T := by exact_mod_cast (show t + 1 ≤ T by have := Finset.mem_range.mp ht; omega)
      unfold weight
      rw [mul_pow]
      gcongr
    _ = η ^ 2 * (T : ℝ) ^ 3 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

lemma cumulative_lower {η : ℝ} (hη : 0 ≤ η) (T : ℕ) :
    η * (T : ℝ) ^ 2 / 2 ≤ cumulative η T := by
  unfold cumulative
  nlinarith [mul_nonneg hη (Nat.cast_nonneg (α := ℝ) T)]

lemma weighted_residual_le {η σ L R : ℝ} (hη : 0 ≤ η) (hσ : 0 ≤ σ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (k T t : ℕ) (ht : t < T) :
    weight η t * (48 * σ + 96 * L * R * k / ((t : ℝ) + 1)) ≤
      η * (100 * (σ * T + L * R * k)) := by
  have hp : (t : ℝ) + 1 ≠ 0 := by positivity
  have he : weight η t * (48 * σ + 96 * L * R * k / ((t : ℝ) + 1)) =
      η * (48 * σ * ((t : ℝ) + 1) + 96 * L * R * k) := by
    unfold weight
    field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hη
  have ht' : (t : ℝ) + 1 ≤ T := by exact_mod_cast (show t + 1 ≤ T by omega)
  have hs := mul_le_mul_of_nonneg_left ht' hσ
  have hn : 0 ≤ L * R * k := by positivity
  have hst : 0 ≤ σ * T := by positivity
  nlinarith

lemma moment_cost_sum_le (η R s a σ e : ℝ) (T : ℕ) :
    (∑ t ∈ Finset.range T,
      (320 * weight η t ^ 2 * R ^ 2 * s ^ 2 + 80 * weight η t ^ 2 * a ^ 2 * σ ^ 2 + 18 * e)) ≤
      320 * η ^ 2 * R ^ 2 * s ^ 2 * (T : ℝ) ^ 3 +
        80 * η ^ 2 * a ^ 2 * σ ^ 2 * (T : ℝ) ^ 3 + 18 * T * e := by
  have he (t : ℕ) : 320 * weight η t ^ 2 * R ^ 2 * s ^ 2 +
      80 * weight η t ^ 2 * a ^ 2 * σ ^ 2 + 18 * e =
      (320 * R ^ 2 * s ^ 2 + 80 * a ^ 2 * σ ^ 2) * weight η t ^ 2 + 18 * e := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (squared_weights_sum_le η T)
    (show 0 ≤ 320 * R ^ 2 * s ^ 2 + 80 * a ^ 2 * σ ^ 2 by positivity)
  nlinarith

lemma tuning_variance_pos {σ M j ell T : ℝ} (hM : 0 < M) (hj : 0 < j)
    (hell : 0 < ell) (hT : 0 < T) :
    0 < σ ^ 2 * T + j * M ^ 2 * ell / T ^ 2 := by
  have : 0 < j * M ^ 2 * ell / T ^ 2 := by positivity
  positivity

lemma reciprocal_step_bounds {R s T ell M b j : ℝ} (hR : 0 < R) (hs : 0 ≤ s)
    (hT : 0 < T) (hell : 0 < ell) (hM : 0 < M) (hb : 0 < b) (hj : 0 < j) :
    let η := 1 / (16 * R * s * T * Real.sqrt T / Real.sqrt ell +
      64 * R * M + 64 * b * j * M ^ 2)
    0 < η ∧ 2 * η * R * M ≤ 1 / 32 ∧ η * b * M ^ 2 ≤ 1 / (64 * j) := by
  intro η
  let D := 16 * R * s * T * Real.sqrt T / Real.sqrt ell +
    64 * R * M + 64 * b * j * M ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hfirst : 0 ≤ 16 * R * s * T * Real.sqrt T / Real.sqrt ell := by positivity
  have hsecond : 0 < 64 * R * M := by positivity
  have hthird : 0 < 64 * b * j * M ^ 2 := by positivity
  have hη : 0 < η := one_div_pos.mpr hD
  have hηD : η * D = 1 := by dsimp [η, D]; exact one_div_mul_cancel hD.ne'
  have hcap1 : η * (64 * R * M) ≤ 1 := by
    calc
      _ ≤ η * D := mul_le_mul_of_nonneg_left (by dsimp [D]; linarith) hη.le
      _ = 1 := hηD
  have hcap2 : η * (64 * b * j * M ^ 2) ≤ 1 := by
    calc
      _ ≤ η * D := mul_le_mul_of_nonneg_left (by dsimp [D]; linarith) hη.le
      _ = 1 := hηD
  refine ⟨hη, by nlinarith, ?_⟩
  apply (le_div_iff₀ (show 0 < 64 * j by positivity)).mpr
  nlinarith

lemma mixture_balance {R σ M j ell T : ℝ} (hR : 0 < R) (hT : 0 < T)
    (hj : 0 < j) (hell : 0 < ell) (hM : 0 < M) :
    let ν := σ ^ 2 * T + j * M ^ 2 * ell / T ^ 2
    let b := R / (32 * T * Real.sqrt ν)
    0 < b ∧ R ^ 2 / (b * T ^ 2) +
      (320 * σ ^ 2 * T + 512 * j * M ^ 2 * ell / T ^ 2) * b ≤
        48 * R * Real.sqrt ν / T := by
  intro ν b
  have hν : 0 < ν := tuning_variance_pos hM hj hell hT
  have hsqrt : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hb : 0 < b := by dsimp [b]; positivity
  have hv : (Real.sqrt ν) ^ 2 = ν := Real.sq_sqrt hν.le
  have he1 : R ^ 2 / (b * T ^ 2) = 32 * R * Real.sqrt ν / T := by
    dsimp [b]
    field_simp
  have he2 : 512 * ν * b = 16 * R * Real.sqrt ν / T := by
    dsimp [b]
    apply (eq_div_iff hT.ne').mpr
    field_simp
    nlinarith [hv]
  refine ⟨hb, ?_⟩
  have hcoeff : 320 * σ ^ 2 * T + 512 * j * M ^ 2 * ell / T ^ 2 ≤ 512 * ν := by
    dsimp [ν]
    have hn : 0 ≤ σ ^ 2 * T := by positivity
    ring_nf
    nlinarith
  have hterm := mul_le_mul_of_nonneg_right hcoeff hb.le
  rw [he2] at hterm
  rw [he1]
  calc
    _ ≤ 32 * R * Real.sqrt ν / T + 16 * R * Real.sqrt ν / T := add_le_add le_rfl hterm
    _ = _ := by ring

lemma sqrt_sum_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

lemma tuning_sqrt_bound {σ M j ell T : ℝ} (hσ : 0 ≤ σ) (hM : 0 ≤ M)
    (hj : 0 ≤ j) (hell : 0 ≤ ell) (hT : 0 < T) :
    Real.sqrt (σ ^ 2 * T + j * M ^ 2 * ell / T ^ 2) / T ≤
      σ / Real.sqrt T + M * Real.sqrt (j * ell) / T ^ 2 := by
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have h1 : Real.sqrt (σ ^ 2 * T) = σ * Real.sqrt T := by
    rw [Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ]
  have h2 : Real.sqrt (j * M ^ 2 * ell / T ^ 2) = M * Real.sqrt (j * ell) / T := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hT.le]
    have he : j * M ^ 2 * ell = M ^ 2 * (j * ell) := by ring
    rw [he, Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
  have h := div_le_div_of_nonneg_right (sqrt_sum_bound
    (show 0 ≤ σ ^ 2 * T by positivity) (show 0 ≤ j * M ^ 2 * ell / T ^ 2 by positivity)) hT.le
  rw [h1, h2] at h
  have he : (σ * Real.sqrt T + M * Real.sqrt (j * ell) / T) / T =
      σ / Real.sqrt T + M * Real.sqrt (j * ell) / T ^ 2 := by
    field_simp
    linear_combination σ * T * (Real.sq_sqrt hT.le)
  exact h.trans_eq he

lemma directional_noise_balance {η R s T ell : ℝ} (hR : 0 ≤ R) (hs : 0 ≤ s)
    (hT : 0 < T) (hell : 0 < ell)
    (hcap : η * (16 * R * s * T * Real.sqrt T / Real.sqrt ell) ≤ 1) :
    1280 * η * R ^ 2 * s ^ 2 * T ≤ 80 * R * s * Real.sqrt ell / Real.sqrt T := by
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsell : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hell
  have h := mul_le_mul_of_nonneg_right hcap
    (show 0 ≤ 80 * R * s * Real.sqrt ell / Real.sqrt T by positivity)
  have he : η * (16 * R * s * T * Real.sqrt T / Real.sqrt ell) *
      (80 * R * s * Real.sqrt ell / Real.sqrt T) = 1280 * η * R ^ 2 * s ^ 2 * T := by
    field_simp
    ring
  simpa only [he, one_mul] using h

lemma reciprocal_confidence {R s T ell M b j : ℝ} (hR : 0 < R) (hs : 0 ≤ s)
    (hT : 0 < T) (hell : 0 < ell) (hM : 0 < M) (hb : 0 < b) (hj : 0 < j) :
    let η := 1 / (16 * R * s * T * Real.sqrt T / Real.sqrt ell +
      64 * R * M + 64 * b * j * M ^ 2)
    8 * ell / (η * T ^ 2) = 128 * R * s * Real.sqrt ell / Real.sqrt T +
      512 * R * M * ell / T ^ 2 + 512 * b * j * M ^ 2 * ell / T ^ 2 := by
  intro η
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsell : 0 < Real.sqrt ell := Real.sqrt_pos.mpr hell
  have hD : 0 < 16 * R * s * T * Real.sqrt T / Real.sqrt ell +
      64 * R * M + 64 * b * j * M ^ 2 := by positivity
  dsimp [η]
  field_simp
  linear_combination 128 * R * s * T * ell * (Real.sq_sqrt hT.le) -
    128 * R * s * T ^ 2 * (Real.sq_sqrt hell.le)

end LongTails.Proofs.CovarianceAcceleratedParameters
