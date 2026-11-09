import LongTails.Proofs.CovarianceAcceleratedTuning
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxRecDepth 2000

namespace LongTails.Proofs.CovarianceAcceleratedBudget

lemma confidence_log_bounds {A S δ : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    let J := Real.log ((2 : ℝ) ^ 56 * (1 + A + S) / δ ^ 2)
    1 ≤ J ∧ 0 < Real.log (3 / δ) ∧ Real.log (3 / δ) ≤ J := by
  intro J
  have hB : 1 ≤ 1 + A + S := by linarith
  have hδsq : 0 < δ ^ 2 := by positivity
  have hδsq1 : δ ^ 2 < 1 := by nlinarith
  have harg : 3 < (2 : ℝ) ^ 56 * (1 + A + S) / δ ^ 2 := by
    apply (lt_div_iff₀ hδsq).mpr
    nlinarith
  have hJ : 1 ≤ J := by
    apply (Real.exp_le_exp).mp
    rw [Real.exp_log (by linarith : 0 < (2 : ℝ) ^ 56 * (1 + A + S) / δ ^ 2)]
    exact Real.exp_one_lt_three.le.trans harg.le
  have hell : 0 < Real.log (3 / δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  refine ⟨hJ, hell, ?_⟩
  apply Real.log_le_log (by positivity)
  apply (div_le_div_iff₀ hδ hδsq).mpr
  nlinarith

lemma log_horizon_bound {A S δ J N : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hJ : 1 ≤ J) (hN : 0 < N)
    (hJdef : J = Real.log ((2 : ℝ) ^ 56 * (1 + A + S) / δ ^ 2))
    (hNupper : N ≤ 5 * (2 : ℝ) ^ 40 * (1 + A + S) * J ^ 2) :
    Real.log (54 * N / δ) ≤ 3 * J := by
  have hJpos : 0 < J := by linarith
  have hBpos : 0 < 1 + A + S := by positivity
  have harg : 54 * N / δ ≤ ((2 : ℝ) ^ 56 * (1 + A + S) / δ ^ 2) * J ^ 2 := by
    apply (div_le_iff₀ hδ).mpr
    have hδle : δ ≤ 1 := hδ1.le
    have hconst : (270 : ℝ) * 2 ^ 40 ≤ 2 ^ 56 := by norm_num
    have hbase : 54 * N ≤ (2 : ℝ) ^ 56 * (1 + A + S) * J ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hconst (show 0 ≤ (1 + A + S) * J ^ 2 by positivity)]
    have hdiv : 1 ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa using hδle)
    have hmul := mul_le_mul_of_nonneg_left hdiv
      (show 0 ≤ (2 : ℝ) ^ 56 * (1 + A + S) * J ^ 2 by positivity)
    have he : ((2 : ℝ) ^ 56 * (1 + A + S) / δ ^ 2) * J ^ 2 * δ =
        ((2 : ℝ) ^ 56 * (1 + A + S) * J ^ 2) * (1 / δ) := by field_simp
    rw [he]
    have hmul' : (2 : ℝ) ^ 56 * (1 + A + S) * J ^ 2 ≤
        ((2 : ℝ) ^ 56 * (1 + A + S) * J ^ 2) * (1 / δ) := by
      simpa only [mul_one] using hmul
    exact hbase.trans hmul'
  have hlog := Real.log_le_log (show 0 < 54 * N / δ by positivity) harg
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, ← hJdef] at hlog
  have hl : Real.log J ≤ J := (Real.log_le_sub_one_of_pos hJpos).trans (by linarith)
  linarith

lemma horizon_ceiling_upper {A S J ell Q : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hJ : 1 ≤ J) (heJ : ell ≤ J) (hQ : 0 ≤ Q) (hQS : Q ≤ S * (1 + ell)) :
    (⌈(2 : ℝ) ^ 40 * (J ^ 2 + Real.sqrt A * J + Q)⌉₊ : ℝ) ≤
      5 * (2 : ℝ) ^ 40 * (1 + A + S) * J ^ 2 := by
  let B := 1 + A + S
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hJ2 : J ≤ J ^ 2 := by nlinarith
  have hJ21 : 1 ≤ J ^ 2 := by nlinarith
  have hsqrt : Real.sqrt A ≤ B := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hB0, ?_⟩
    dsimp [B]
    nlinarith [sq_nonneg A, sq_nonneg S, mul_nonneg hA hS]
  have hfirst : J ^ 2 ≤ B * J ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sq_nonneg J)]
  have hsecond : Real.sqrt A * J ≤ B * J ^ 2 :=
    (mul_le_mul_of_nonneg_right hsqrt hJ0).trans (mul_le_mul_of_nonneg_left hJ2 hB0)
  have hthird : Q ≤ 2 * B * J ^ 2 := by
    calc
      _ ≤ S * (1 + ell) := hQS
      _ ≤ S * (2 * J ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) hS
      _ ≤ B * (2 * J ^ 2) := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (by positivity)
      _ = _ := by ring
  have hsum : J ^ 2 + Real.sqrt A * J + Q ≤ 4 * B * J ^ 2 := by linarith
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ (2 : ℝ) ^ 40 * (J ^ 2 + Real.sqrt A * J + Q) by positivity)
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (2 : ℝ) ^ 40 by positivity)
  have hunit : 1 ≤ (2 : ℝ) ^ 40 * B * J ^ 2 := by
    have hh : 1 ≤ B * J ^ 2 := hJ21.trans hfirst
    nlinarith
  change _ ≤ 5 * (2 : ℝ) ^ 40 * B * J ^ 2
  linarith

lemma warmup_length_bounds {N : ℕ} {J j : ℝ} (hJ : 1 ≤ J) (hj : 1 ≤ j)
    (hjJ : j ≤ 3 * J) (hN : (2 : ℝ) ^ 40 * J ^ 2 ≤ N) :
    let k := ⌈16 * j⌉₊
    1 ≤ k ∧ (k : ℝ) ≤ 51 * J ∧ k ≤ N ∧
      (N : ℝ) / 2 ≤ (N - k : ℕ) ∧ (k : ℝ) ^ 2 ≤ (N - k : ℕ) ∧ 1 ≤ N - k := by
  intro k
  have hj0 : 0 ≤ j := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hJ2 : J ≤ J ^ 2 := by nlinarith
  have hklower : 16 * j ≤ (k : ℝ) := Nat.le_ceil _
  have hkupper : (k : ℝ) < 16 * j + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk49 : (k : ℝ) ≤ 49 * J := by linarith
  have hk1 : (1 : ℝ) ≤ k := by linarith
  have hk1nat : 1 ≤ k := by exact_mod_cast hk1
  have hdouble : 2 * (k : ℝ) ≤ N := by nlinarith
  have hkN : k ≤ N := by
    apply (Nat.cast_le (α := ℝ)).mp
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - k := Nat.cast_sub hkN
  have hhalf : (N : ℝ) / 2 ≤ (N - k : ℕ) := by rw [hcast]; linarith
  have hsq : (k : ℝ) ^ 2 ≤ (49 * J) ^ 2 := by gcongr
  have hkT : (k : ℝ) ^ 2 ≤ (N - k : ℕ) := by nlinarith
  have hT : 1 ≤ N - k := by
    have hTr : (1 : ℝ) ≤ (N - k : ℕ) := by nlinarith
    exact_mod_cast hTr
  exact ⟨hk1nat, by linarith, hkN, hhalf, hkT, hT⟩

lemma confidence_log_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) : 1 ≤ Real.log (3 / δ) := by
  apply (Real.exp_le_exp).mp
  rw [Real.exp_log (by positivity : 0 < 3 / δ)]
  apply Real.exp_one_lt_three.le.trans
  apply (le_div_iff₀ hδ).mpr
  linarith

lemma exponential_confidence {δ : ℝ} (hδ : 0 < δ) :
    Real.exp (-Real.log (3 / δ)) = δ / 3 := by
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

lemma exponential_horizon {δ : ℝ} {N : ℕ} (hδ : 0 < δ) (hN : 0 < N) :
    Real.exp (-Real.log (54 * (N : ℝ) / δ)) = δ / (54 * N) := by
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

lemma tail_allocation {δ : ℝ} {N k T : ℕ} (hδ : 0 < δ) (hδ1 : δ < 1) (hN : 0 < N)
    (hT : T ≤ N) (hk : 16 * Real.log (54 * (N : ℝ) / δ) ≤ k) :
    (T : ℝ) * Real.exp (-7 * k / 32) ≤ δ / 54 ∧
      18 * (T : ℝ) * Real.exp (-Real.log (54 * (N : ℝ) / δ)) ≤ Real.log (3 / δ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNr0 : (0 : ℝ) < N := by positivity
  have hTr : (T : ℝ) ≤ N := by exact_mod_cast hT
  have hj : 0 ≤ Real.log (54 * (N : ℝ) / δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by nlinarith))
  have he : Real.exp (-7 * (k : ℝ) / 32) ≤ Real.exp (-Real.log (54 * (N : ℝ) / δ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hprod : (T : ℝ) * Real.exp (-Real.log (54 * (N : ℝ) / δ)) ≤ δ / 54 := by
    rw [exponential_horizon hδ hN]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 54)).mpr
    field_simp
    nlinarith
  refine ⟨(mul_le_mul_of_nonneg_left he (Nat.cast_nonneg T)).trans hprod, ?_⟩
  have hell := confidence_log_one hδ hδ1
  nlinarith

lemma accuracy_from_horizon {L R σ s k T ell ε : ℝ} (hR : 0 ≤ R)
    (hσ : 0 ≤ σ) (hs : 0 ≤ s) (hT : 0 < T) (hell : 0 ≤ ell) (hε : 0 < ε)
    (hdet : 131072 * (L * R ^ 2 / ε) * k ^ 2 ≤ T ^ 2)
    (hstat : 34359738368 * R ^ 2 * (σ ^ 2 + s ^ 2 * ell) / ε ^ 2 ≤ T) :
    65536 * (L * R ^ 2 * k ^ 2 / T ^ 2 + R * (σ + s * Real.sqrt ell) / Real.sqrt T) ≤ ε := by
  have hdet' : 65536 * L * R ^ 2 * k ^ 2 / T ^ 2 ≤ ε / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hT)).mpr
    have hh := mul_le_mul_of_nonneg_right hdet hε.le
    have he : (131072 * (L * R ^ 2 / ε) * k ^ 2) * ε = 131072 * L * R ^ 2 * k ^ 2 := by field_simp
    rw [he] at hh
    nlinarith
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsum : (σ + s * Real.sqrt ell) ^ 2 ≤ 2 * (σ ^ 2 + s ^ 2 * ell) := by
    have he : s ^ 2 * (Real.sqrt ell) ^ 2 = s ^ 2 * ell := by rw [Real.sq_sqrt hell]
    nlinarith [sq_nonneg (σ - s * Real.sqrt ell)]
  have hnoise : 65536 * R * (σ + s * Real.sqrt ell) / Real.sqrt T ≤ ε / 2 := by
    apply (div_le_iff₀ hsT).mpr
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have hh := (div_le_iff₀ (sq_pos_of_pos hε)).mp hstat
    have hscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (65536 : ℝ) ^ 2 * R ^ 2 by positivity)
    have he : (ε / 2 * Real.sqrt T) ^ 2 = ε ^ 2 * T / 4 := by
      rw [mul_pow, Real.sq_sqrt hT.le]
      ring
    rw [he]
    nlinarith
  have hh := add_le_add hdet' hnoise
  convert hh using 1 <;> ring

lemma horizon_accuracy_conditions {A Q J k T : ℝ} (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (hJ : 1 ≤ J) (hk : 0 ≤ k) (hkJ : k ≤ 51 * J)
    (hT : (2 : ℝ) ^ 39 * (J ^ 2 + Real.sqrt A * J + Q) ≤ T) :
    131072 * A * k ^ 2 ≤ T ^ 2 ∧ 34359738368 * Q ≤ T := by
  have hJ0 : 0 ≤ J := by linarith
  have hJ2 : 0 ≤ J ^ 2 := sq_nonneg J
  have hroot : 0 ≤ Real.sqrt A * J := by positivity
  have hT0 : 0 ≤ T := (show 0 ≤ (2 : ℝ) ^ 39 * (J ^ 2 + Real.sqrt A * J + Q) by positivity).trans hT
  have hscaled : 18464 * Real.sqrt A * J ≤ T := by nlinarith
  have hsqk : k ^ 2 ≤ (51 * J) ^ 2 := by gcongr
  have hsqT : (18464 * Real.sqrt A * J) ^ 2 ≤ T ^ 2 := by gcongr
  have he : (18464 * Real.sqrt A * J) ^ 2 = 340919296 * A * J ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hA]
    ring
  rw [he] at hsqT
  have hm := mul_le_mul_of_nonneg_left hsqk (show 0 ≤ 131072 * A by positivity)
  have hn : 0 ≤ A * J ^ 2 := by positivity
  constructor <;> nlinarith

lemma budget_calibration {A S Q δ : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hQS : Q ≤ S * (1 + Real.log (3 / δ))) :
    let J := Real.log ((2 : ℝ) ^ 56 * (1 + A + S) / δ ^ 2)
    let N := ⌈(2 : ℝ) ^ 40 * (J ^ 2 + Real.sqrt A * J + Q)⌉₊
    let j := Real.log (54 * (N : ℝ) / δ)
    let k := ⌈16 * j⌉₊
    let T := N - k
    1 ≤ j ∧ Real.log (3 / δ) ≤ j ∧ j ≤ k ∧ 1 ≤ k ∧ 1 ≤ T ∧
      (k : ℝ) ^ 2 ≤ T ∧ (2 : ℝ) ^ 39 * (J ^ 2 + Real.sqrt A * J + Q) ≤ T ∧
      (k : ℝ) ≤ 51 * J ∧ k + T = N := by
  intro J N j k T
  have hlogs := confidence_log_bounds hA hS hδ hδ1
  have hJ : 1 ≤ J := hlogs.1
  have hJ0 : 0 ≤ J := by linarith
  have hlower : (2 : ℝ) ^ 40 * (J ^ 2 + Real.sqrt A * J + Q) ≤ N := Nat.le_ceil _
  have hNJ : (2 : ℝ) ^ 40 * J ^ 2 ≤ N := by
    have hr : 0 ≤ Real.sqrt A * J := by positivity
    nlinarith
  have hNr : (1 : ℝ) ≤ N := by nlinarith [sq_nonneg (J - 1)]
  have hN : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  have hupper : (N : ℝ) ≤ 5 * (2 : ℝ) ^ 40 * (1 + A + S) * J ^ 2 :=
    horizon_ceiling_upper hA hS hJ hlogs.2.2 hQ hQS
  have hjJ : j ≤ 3 * J := log_horizon_bound hA hS hδ hδ1 hJ (by positivity) rfl hupper
  have hej : Real.log (3 / δ) ≤ j := by
    apply Real.log_le_log (by positivity)
    apply (div_le_div_iff₀ hδ hδ).mpr
    nlinarith
  have hj : 1 ≤ j := (confidence_log_one hδ hδ1).trans hej
  have hlength := warmup_length_bounds hJ hj hjJ hNJ
  have hk : 1 ≤ k := hlength.1
  have hkN : k ≤ N := hlength.2.2.1
  have hhalf : (N : ℝ) / 2 ≤ T := hlength.2.2.2.1
  have hkT : (k : ℝ) ^ 2 ≤ T := hlength.2.2.2.2.1
  have hT : 1 ≤ T := hlength.2.2.2.2.2
  have hjk : j ≤ k := by
    have hh : 16 * j ≤ (k : ℝ) := Nat.le_ceil _
    linarith
  have hTscale : (2 : ℝ) ^ 39 * (J ^ 2 + Real.sqrt A * J + Q) ≤ T := by nlinarith
  exact ⟨hj, hej, hjk, hk, hT, hkT, hTscale, hlength.2.1, Nat.add_sub_of_le hkN⟩

end LongTails.Proofs.CovarianceAcceleratedBudget
