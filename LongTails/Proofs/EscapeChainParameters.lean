import LongTails.Proofs.EscapeChainProbability
import LongTails.Setups.HighDimensionalVarianceOnlySecondOrder
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory OracleTemplate

set_option exponentiation.threshold 1024

namespace LongTails.Proofs.EscapeChainParameters

open LongTails.Setups.HighDimensionalVarianceOnlySecondOrder

noncomputable def D (q : Params) : ℝ := Real.sqrt q.ρ * q.Δ / (q.ε * Real.sqrt q.ε)

noncomputable def r0 (q : Params) : ℝ := 2 ^ 133 * Real.sqrt (q.ε / q.ρ) / 10

noncomputable def δ0 (q : Params) : ℝ := 2 ^ 133 * q.ε * r0 q

noncomputable def Kq (q : Params) : ℕ := ⌊q.Δ / (2 ^ 122 * δ0 q)⌋₊

noncomputable def σh (q : Params) : ℝ := q.σ / (2 ^ 133 * q.ε)

noncomputable def Aq (q : Params) : ℝ := σh q ^ 2 / 2025

noncomputable def bq (q : Params) (N : ℕ) : ℕ :=
  ⌈2 ^ 277 * ((Kq q : ℝ) + 1) * Real.log (32 * Kq q * (Kq q + 1) * (N + 1))⌉₊ + 1

noncomputable def nq (q : Params) (N : ℕ) : ℕ := q.d / bq q N

noncomputable def mq (q : Params) (N : ℕ) : ℕ := 2 * N / Kq q

noncomputable def budgetFormula (q : Params) : ℕ :=
  ⌊q.d * (q.σ / q.ε) ^ 2 * D q / 2 ^ 703⌋₊

section facts

variable {q : Params} (hv : spec.valid q)
include hv

lemma pos_facts : 0 < q.L ∧ 0 < q.ρ ∧ 0 < q.ε ∧ 0 < q.δ ∧ q.δ ≤ 1 / 2 ∧ 0 < q.σ ∧
    2 ^ 130 * Real.sqrt (q.ρ * q.ε) ≤ q.L ∧ 2 ^ 200 * q.ε ≤ q.σ ∧ 2 ^ 390 ≤ D q ∧
    D q ^ 2 * Real.log (q.d * q.σ * D q / q.ε) ≤ 2 ^ 480 * q.d := by
  obtain ⟨hg, hδ, hL, hσ, hD, hd⟩ := hv
  obtain ⟨h1, h2, -, -, h5, h6, -, -, -⟩ := hg
  refine ⟨h1, h2, h5, h6, hδ, ?_, hL, hσ, hD, hd⟩
  have : 0 < 2 ^ 200 * q.ε := by positivity
  linarith

lemma r0_pos : 0 < r0 q := by
  obtain ⟨-, hρ, hε, -⟩ := pos_facts hv
  unfold r0; have : 0 < Real.sqrt (q.ε / q.ρ) := Real.sqrt_pos.2 (div_pos hε hρ); positivity

lemma δ0_pos : 0 < δ0 q := by
  obtain ⟨-, -, hε, -⟩ := pos_facts hv
  unfold δ0; have := r0_pos hv; positivity

lemma ratio_one : q.ε * r0 q / δ0 q = 1 / 2 ^ 133 := by
  obtain ⟨-, -, hε, -⟩ := pos_facts hv
  have := r0_pos hv
  unfold δ0; field_simp

lemma sqrt_div_sq : Real.sqrt (q.ε / q.ρ) ^ 2 = q.ε / q.ρ := by
  obtain ⟨-, hρ, hε, -⟩ := pos_facts hv
  exact Real.sq_sqrt (div_pos hε hρ).le

lemma ratio_curv : Real.sqrt (q.ρ * q.ε) * r0 q ^ 2 / δ0 q = 1 / 10 := by
  obtain ⟨-, hρ, hε, -⟩ := pos_facts hv
  have hs : Real.sqrt (q.ρ * q.ε) * Real.sqrt (q.ε / q.ρ) = q.ε := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show q.ρ * q.ε * (q.ε / q.ρ) = q.ε ^ 2 by field_simp]
    exact Real.sqrt_sq hε.le
  rw [div_eq_iff (δ0_pos hv).ne']
  have h1 : Real.sqrt (q.ρ * q.ε) * r0 q ^ 2 =
      (Real.sqrt (q.ρ * q.ε) * Real.sqrt (q.ε / q.ρ)) * r0 q * (2 ^ 133 / 10) := by
    unfold r0; ring
  rw [h1, hs]
  unfold δ0
  ring

lemma hess_const : δ0 q * 2 ^ 126 / r0 q ^ 3 ≤ q.ρ := by
  obtain ⟨-, hρ, hε, -⟩ := pos_facts hv
  have hr := r0_pos hv
  have hs := sqrt_div_sq hv
  have hr2 : r0 q ^ 2 = 2 ^ 266 * (q.ε / q.ρ) / 100 := by
    unfold r0; rw [div_pow, mul_pow, hs]; ring
  have ht : q.ρ * (q.ε / q.ρ) = q.ε := mul_div_cancel₀ _ hρ.ne'
  have key : δ0 q * 2 ^ 126 = (25 / 32 * q.ρ) * r0 q ^ 3 := by
    rw [show r0 q ^ 3 = r0 q * r0 q ^ 2 by ring, hr2]
    unfold δ0
    linear_combination (-(2 : ℝ) ^ 259 * r0 q) * ht
  rw [div_le_iff₀ (by positivity), key]
  have : 0 < r0 q ^ 3 := by positivity
  nlinarith

lemma grad_const : δ0 q * 2 ^ 126 / r0 q ^ 2 ≤ q.L := by
  obtain ⟨-, hρ, hε, -, -, -, hL, -⟩ := pos_facts hv
  have hr := r0_pos hv
  have hrat := ratio_curv hv
  have hsq : 0 < Real.sqrt (q.ρ * q.ε) := Real.sqrt_pos.2 (by positivity)
  have hδ := δ0_pos hv
  have h1 : δ0 q / r0 q ^ 2 = 10 * Real.sqrt (q.ρ * q.ε) := by
    field_simp at hrat ⊢; linarith
  rw [show δ0 q * 2 ^ 126 / r0 q ^ 2 = δ0 q / r0 q ^ 2 * 2 ^ 126 by ring, h1]
  nlinarith

end facts

section facts2

variable {q : Params} (hv : spec.valid q)
include hv

lemma K_formula : q.Δ / (2 ^ 122 * δ0 q) = 10 * D q / 2 ^ 388 := by
  obtain ⟨-, hρ, hε, -⟩ := pos_facts hv
  have hsε : 0 < Real.sqrt q.ε := Real.sqrt_pos.2 hε
  have hsρ : 0 < Real.sqrt q.ρ := Real.sqrt_pos.2 hρ
  unfold δ0 r0 D
  rw [Real.sqrt_div hε.le]
  field_simp

lemma K_bounds : 5 * D q / 2 ^ 388 ≤ Kq q ∧ (Kq q : ℝ) ≤ 10 * D q / 2 ^ 388 ∧ 40 ≤ Kq q := by
  obtain ⟨-, -, -, -, -, -, -, -, hD, -⟩ := pos_facts hv
  have hz : 40 ≤ 10 * D q / 2 ^ 388 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hnn : 0 ≤ 10 * D q / 2 ^ 388 := by linarith
  have hfl : (Kq q : ℝ) ≤ 10 * D q / 2 ^ 388 := by
    unfold Kq; rw [K_formula hv]; exact Nat.floor_le hnn
  have hfl2 : 10 * D q / 2 ^ 388 < Kq q + 1 := by
    unfold Kq; rw [K_formula hv]; exact Nat.lt_floor_add_one _
  have h39 : (39 : ℝ) < Kq q := by linarith
  have h40 : 40 ≤ Kq q := by
    have : 39 < Kq q := by exact_mod_cast h39
    omega
  refine ⟨?_, hfl, h40⟩
  have : 5 * D q / 2 ^ 388 + 1 ≤ 10 * D q / 2 ^ 388 := by
    rw [div_add_one (by positivity), div_le_div_iff_of_pos_right (by positivity)]
    linarith
  linarith

lemma depth : δ0 q * (2 ^ 121 * (Kq q + 1)) ≤ q.Δ := by
  obtain ⟨-, -, hK3⟩ := K_bounds hv
  obtain ⟨-, -, -, -, -, -, -, -, hD, -⟩ := pos_facts hv
  have hδ := δ0_pos hv
  have hnn : 0 ≤ q.Δ / (2 ^ 122 * δ0 q) := by rw [K_formula hv]; linarith
  have hfl : (Kq q : ℝ) ≤ q.Δ / (2 ^ 122 * δ0 q) := Nat.floor_le hnn
  rw [le_div_iff₀ (by positivity)] at hfl
  have hK40 : (40 : ℝ) ≤ Kq q := by exact_mod_cast hK3
  have h2 : δ0 q * (2 ^ 121 * ((Kq q : ℝ) + 1)) ≤ δ0 q * (2 ^ 121 * (2 * Kq q)) :=
    mul_le_mul_of_nonneg_left (by linarith) hδ.le
  linarith

lemma σh_large : 2 ^ 67 ≤ σh q := by
  obtain ⟨-, -, hε, -, -, -, -, hσ, -⟩ := pos_facts hv
  unfold σh
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma A_large : 45 * 2 ^ 102 ≤ Aq q := by
  have h := σh_large hv
  unfold Aq
  rw [le_div_iff₀ (by norm_num)]
  have : (2 : ℝ) ^ 134 ≤ σh q ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h 2; norm_num at this ⊢; linarith
  nlinarith

end facts2

section facts3

variable {q : Params} (hv : spec.valid q)
include hv

lemma d_one : (1 : ℝ) ≤ q.d := by
  have h : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin q.d)) := hv.1.2.2.2.2.2.2.2.2
  rw [finrank_euclideanSpace_fin] at h
  exact Nat.one_le_cast.mpr h

lemma D_pos : 0 < D q := lt_of_lt_of_le (by positivity) (pos_facts hv).2.2.2.2.2.2.2.2.1

lemma ratio_big : 2 ^ 200 ≤ q.σ / q.ε := by
  obtain ⟨-, -, hε, -, -, -, -, hσ, -⟩ := pos_facts hv
  rw [le_div_iff₀ hε]; linarith

lemma X_big : 2 ^ 590 ≤ q.d * q.σ * D q / q.ε := by
  have h1 := d_one hv
  have h2 := ratio_big hv
  have h3 := (pos_facts hv).2.2.2.2.2.2.2.2.1
  have e : q.d * q.σ * D q / q.ε = q.d * (q.σ / q.ε) * D q := by ring
  have m1 := mul_le_mul h1 h2 (by norm_num) (by linarith)
  have m2 := mul_le_mul m1 h3 (by norm_num) (mul_nonneg (by linarith) (by linarith))
  rw [e]
  calc (2 : ℝ) ^ 590 = 1 * 2 ^ 200 * 2 ^ 390 := by norm_num
    _ ≤ _ := m2

lemma logX_one : 1 ≤ Real.log (q.d * q.σ * D q / q.ε) := by
  have h := X_big hv
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (by positivity) h)]
  have h1 := Real.exp_one_lt_d9
  have h2 : (3 : ℝ) ≤ 2 ^ 590 := by norm_num
  linarith

lemma D_sq_le : D q ^ 2 ≤ 2 ^ 480 * q.d := by
  have h := (pos_facts hv).2.2.2.2.2.2.2.2.2
  have hl := logX_one hv
  have : D q ^ 2 ≤ D q ^ 2 * Real.log (q.d * q.σ * D q / q.ε) := le_mul_of_one_le_right (sq_nonneg _) hl
  linarith

lemma D_le_d : D q ≤ 2 ^ 90 * q.d := by
  have h1 := D_sq_le hv
  have hD := (pos_facts hv).2.2.2.2.2.2.2.2.1
  have hDp := D_pos hv
  have : D q * 2 ^ 390 ≤ D q * D q := mul_le_mul_of_nonneg_left hD hDp.le
  nlinarith

lemma d_ratio : 2 ^ 110 * D q ≤ q.d * (q.σ / q.ε) := by
  have h1 := D_le_d hv
  have h2 := ratio_big hv
  have hd := d_one hv
  have : q.d * 2 ^ 200 ≤ q.d * (q.σ / q.ε) := mul_le_mul_of_nonneg_left h2 (by linarith)
  linarith

lemma prod_one (N : ℕ) : (1 : ℝ) ≤ 32 * Kq q * (Kq q + 1) * (N + 1) := by
  obtain ⟨-, -, hK3⟩ := K_bounds hv
  have hK40 : (40 : ℝ) ≤ Kq q := by exact_mod_cast hK3
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith))
    (by linarith)

end facts3

section dims

variable {q : Params} (hv : spec.valid q) {N : ℕ} (hN : N ≤ budgetFormula q)
include hv hN

lemma budget_le : (N : ℝ) ≤ q.d * q.σ ^ 2 * D q / (2 ^ 703 * q.ε ^ 2) := by
  obtain ⟨-, -, hε, -, -, -, -, -, hD, -⟩ := pos_facts hv
  have hDp : 0 < D q := lt_of_lt_of_le (by positivity) hD
  have hb : (budgetFormula q : ℝ) ≤ q.d * (q.σ / q.ε) ^ 2 * D q / 2 ^ 703 := by
    unfold budgetFormula
    exact Nat.floor_le (by positivity)
  have he : q.d * (q.σ / q.ε) ^ 2 * D q / 2 ^ 703 = q.d * q.σ ^ 2 * D q / (2 ^ 703 * q.ε ^ 2) := by
    field_simp
  have : (N : ℝ) ≤ budgetFormula q := by exact_mod_cast hN
  linarith

lemma log_bound :
    Real.log (32 * Kq q * (Kq q + 1) * (N + 1)) ≤ 3 * Real.log (q.d * q.σ * D q / q.ε) := by
  obtain ⟨hK1, hK2, hK3⟩ := K_bounds hv
  obtain ⟨-, -, hε, -, -, -, -, -, hD, -⟩ := pos_facts hv
  have hNb := budget_le hv hN
  have hd1 := d_one hv
  have hr := ratio_big hv
  have hDp := D_pos hv
  have hdr := d_ratio hv
  have hK0 : (0 : ℝ) ≤ Kq q := Nat.cast_nonneg _
  have hKD : (Kq q : ℝ) + 1 ≤ D q := by
    have : 10 * D q / 2 ^ 388 + 1 ≤ D q := by
      rw [div_add_one (by positivity), div_le_iff₀ (by positivity)]; linarith
    linarith
  set X := q.d * q.σ * D q / q.ε with hX
  have hX1 : X = q.d * (q.σ / q.ε) * D q := by rw [hX]; ring
  set Y := q.d * (q.σ / q.ε) ^ 2 * D q with hYd
  have hY0 : 0 ≤ Y := mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) hDp.le
  have hNY : (N : ℝ) ≤ Y := by
    have e : q.d * q.σ ^ 2 * D q / (2 ^ 703 * q.ε ^ 2) = Y / 2 ^ 703 := by
      rw [hYd, div_pow]; ring
    have : Y / 2 ^ 703 ≤ Y := div_le_self hY0 (by norm_num)
    linarith
  have hY1 : 1 ≤ Y := by
    have hr2 : (1 : ℝ) ≤ (q.σ / q.ε) ^ 2 := one_le_pow₀ (by linarith)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd1 hr2) (by linarith)
  have hdD : 2 ^ 390 ≤ q.d * D q := by
    calc (2 : ℝ) ^ 390 = 1 * 2 ^ 390 := by ring
      _ ≤ q.d * D q := mul_le_mul hd1 hD (by norm_num) (by linarith)
  have hXY : X ^ 2 = Y * (q.d * D q) := by rw [hX1, hYd]; ring
  have hN1 : (N : ℝ) + 1 ≤ X ^ 2 := by
    have : Y * 2 ^ 390 ≤ Y * (q.d * D q) := mul_le_mul_of_nonneg_left hdD hY0
    rw [hXY]; linarith
  have h32 : 32 * D q * D q ≤ X := by
    rw [hX1]
    have : 32 * D q ≤ q.d * (q.σ / q.ε) := by linarith
    exact mul_le_mul_of_nonneg_right this hDp.le
  have hprod : 32 * (Kq q : ℝ) * (Kq q + 1) * (N + 1) ≤ X ^ 3 := by
    have hK : (Kq q : ℝ) ≤ D q := by linarith
    calc 32 * (Kq q : ℝ) * (Kq q + 1) * (N + 1) ≤ 32 * D q * D q * X ^ 2 := by gcongr
      _ ≤ X * X ^ 2 := by gcongr
      _ = X ^ 3 := by ring
  have hpos : 0 < 32 * (Kq q : ℝ) * (Kq q + 1) * (N + 1) := by
    have : (0 : ℝ) < Kq q := by linarith [show (40 : ℝ) ≤ Kq q by exact_mod_cast hK3]
    positivity
  calc Real.log (32 * Kq q * (Kq q + 1) * (N + 1)) ≤ Real.log (X ^ 3) :=
        Real.log_le_log hpos hprod
    _ = 3 * Real.log X := by rw [Real.log_pow]; norm_num

lemma b_le : (bq q N : ℝ) ≤ 2 ^ 281 * Kq q * Real.log (q.d * q.σ * D q / q.ε) := by
  obtain ⟨-, -, hK3⟩ := K_bounds hv
  have hlog := log_bound hv hN
  have hΛ1 := logX_one hv
  have hK40 : (40 : ℝ) ≤ Kq q := by exact_mod_cast hK3
  have hL0 : 0 ≤ Real.log (32 * Kq q * (Kq q + 1) * (N + 1)) := Real.log_nonneg (prod_one hv N)
  have hy : 0 ≤ 2 ^ 277 * ((Kq q : ℝ) + 1) * Real.log (32 * Kq q * (Kq q + 1) * (N + 1)) := by
    positivity
  have hc := Nat.ceil_lt_add_one hy
  have hb : (bq q N : ℝ) <
      2 ^ 277 * ((Kq q : ℝ) + 1) * Real.log (32 * Kq q * (Kq q + 1) * (N + 1)) + 2 := by
    unfold bq; push_cast; linarith
  have h1 := mul_le_mul (mul_le_mul_of_nonneg_left (show (Kq q : ℝ) + 1 ≤ 2 * Kq q by linarith)
    (by positivity : (0 : ℝ) ≤ 2 ^ 277)) hlog hL0 (by positivity)
  have hKΛ : 40 ≤ (Kq q : ℝ) * Real.log (q.d * q.σ * D q / q.ε) := by
    have := mul_le_mul hK40 hΛ1 (by norm_num) (by linarith)
    linarith
  linarith

lemma dim_room : (4 * Kq q + 2) * bq q N ≤ q.d := by
  obtain ⟨-, hK2, hK3⟩ := K_bounds hv
  obtain ⟨-, -, -, -, -, -, -, -, hD, hdim⟩ := pos_facts hv
  have hb := b_le hv hN
  have hΛ := logX_one hv
  set Λ := Real.log (q.d * q.σ * D q / q.ε) with hΛd
  have hK40 : (40 : ℝ) ≤ Kq q := by exact_mod_cast hK3
  have hDp := D_pos hv
  have hKD : (Kq q : ℝ) ≤ D q / 2 ^ 384 := by
    calc (Kq q : ℝ) ≤ 10 * D q / 2 ^ 388 := hK2
      _ ≤ D q / 2 ^ 384 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hb0 : (0 : ℝ) ≤ bq q N := Nat.cast_nonneg _
  have e1 : (4 * (Kq q : ℝ) + 2) * bq q N ≤ (5 * Kq q) * (2 ^ 281 * Kq q * Λ) :=
    mul_le_mul (by linarith) hb hb0 (by positivity)
  have e2 : (Kq q : ℝ) * Kq q ≤ (D q / 2 ^ 384) * (D q / 2 ^ 384) :=
    mul_le_mul hKD hKD (by positivity) (by positivity)
  have e3 : 5 * 2 ^ 281 * ((Kq q : ℝ) * Kq q) * Λ ≤ 5 * 2 ^ 281 * ((D q / 2 ^ 384) * (D q / 2 ^ 384)) * Λ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 (by norm_num)) (by linarith)
  have e4 : 5 * 2 ^ 281 * ((D q / 2 ^ 384) * (D q / 2 ^ 384)) * Λ = 5 * 2 ^ 281 / 2 ^ 768 * (D q ^ 2 * Λ) := by
    ring
  have e5 : 5 * 2 ^ 281 / 2 ^ 768 * (D q ^ 2 * Λ) ≤ 1 / 2 ^ 480 * (D q ^ 2 * Λ) :=
    mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg (sq_nonneg _) (by linarith))
  have e6 : 1 / 2 ^ 480 * (D q ^ 2 * Λ) ≤ q.d := by
    rw [one_div, inv_mul_le_iff₀ (by positivity)]; linarith
  have hreal : (4 * (Kq q : ℝ) + 2) * bq q N ≤ q.d := by
    have : (5 * Kq q) * (2 ^ 281 * Kq q * Λ) = 5 * 2 ^ 281 * ((Kq q : ℝ) * Kq q) * Λ := by ring
    linarith
  exact_mod_cast hreal

lemma n_large : 4 * Kq q + 2 ≤ nq q N := by
  unfold nq
  rw [Nat.le_div_iff_mul_le (by unfold bq; omega)]
  exact dim_room hv hN

end dims

section bad

open EscapeChainCertificate

variable {q : Params} (hv : spec.valid q)
include hv

lemma bad_small (N : ℕ) : ((Kq q : ℝ) + 1) * (N + 1) * Kq q * 2 *
    (2 * Real.exp (-(bq q N / (2 ^ 17 * radius (Kq q) ^ 2)))) ≤ 1 / 8 := by
  obtain ⟨-, -, hK3⟩ := K_bounds hv
  have hK0 : (0 : ℝ) < Kq q := by
    have : (40 : ℝ) ≤ Kq q := by exact_mod_cast hK3
    linarith
  have hP : (0 : ℝ) < 32 * Kq q * (Kq q + 1) * (N + 1) := by positivity
  have hR : radius (Kq q) ^ 2 = 2 ^ 260 * ((Kq q : ℝ) + 1) := by
    unfold radius; rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have hb : 2 ^ 277 * ((Kq q : ℝ) + 1) * Real.log (32 * Kq q * (Kq q + 1) * (N + 1)) ≤ bq q N := by
    unfold bq; push_cast
    have := Nat.le_ceil (2 ^ 277 * ((Kq q : ℝ) + 1) * Real.log (32 * Kq q * (Kq q + 1) * (N + 1)))
    linarith
  have hexp : Real.log (32 * Kq q * (Kq q + 1) * (N + 1)) ≤ bq q N / (2 ^ 17 * radius (Kq q) ^ 2) := by
    rw [hR, le_div_iff₀ (by positivity)]
    linarith
  have hE : Real.exp (-(bq q N / (2 ^ 17 * radius (Kq q) ^ 2))) ≤
      1 / (32 * Kq q * (Kq q + 1) * (N + 1)) := by
    calc Real.exp (-(bq q N / (2 ^ 17 * radius (Kq q) ^ 2)))
        ≤ Real.exp (-Real.log (32 * Kq q * (Kq q + 1) * (N + 1))) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / (32 * Kq q * (Kq q + 1) * (N + 1)) := by
          rw [Real.exp_neg, Real.exp_log hP, one_div]
  have hne : (32 * (Kq q : ℝ) * (Kq q + 1) * (N + 1)) ≠ 0 := hP.ne'
  calc ((Kq q : ℝ) + 1) * (N + 1) * Kq q * 2 * (2 * Real.exp (-(bq q N / (2 ^ 17 * radius (Kq q) ^ 2))))
      ≤ ((Kq q : ℝ) + 1) * (N + 1) * Kq q * 2 * (2 * (1 / (32 * Kq q * (Kq q + 1) * (N + 1)))) := by
        gcongr
    _ = 1 / 8 * ((32 * Kq q * (Kq q + 1) * (N + 1)) * (1 / (32 * Kq q * (Kq q + 1) * (N + 1)))) := by
        ring
    _ = 1 / 8 := by rw [mul_one_div, div_self hne, mul_one]

end bad

section eta

open EscapeChainCertificate

variable {q : Params} (hv : spec.valid q) {N : ℕ} (hN : N ≤ budgetFormula q)
include hv hN

lemma reveal_small :
    2 * (2 ^ 30 / (Aq q * bq q N * (nq q N - (2 * Kq q + 1))) * (mq q N + 1)) ≤ 1 / 8 := by
  obtain ⟨-, -, hε, -, -, -, -, -, hD, -⟩ := pos_facts hv
  obtain ⟨hK1, -, hK3⟩ := K_bounds hv
  have hK0 : (0 : ℝ) < Kq q := by
    have : (40 : ℝ) ≤ Kq q := by exact_mod_cast hK3
    linarith
  have hd1 := d_one hv
  have hDp := D_pos hv
  have hroom := dim_room hv hN
  have hn := n_large hv hN
  have hbpos : 0 < bq q N := by unfold bq; omega
  have hb0 : (0 : ℝ) < bq q N := by exact_mod_cast hbpos
  have hd : (4 * (Kq q : ℝ) + 2) * bq q N ≤ q.d := by exact_mod_cast hroom
  have hnb : (q.d : ℝ) < (nq q N + 1) * bq q N := by
    have h1 : q.d < (q.d / bq q N + 1) * bq q N := by
      rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hbpos
    unfold nq; exact_mod_cast h1
  have hn' : (4 * (Kq q : ℝ) + 2) ≤ nq q N := by exact_mod_cast hn
  have hKb : 0 ≤ (Kq q : ℝ) * bq q N := by positivity
  have hbd : 2 * (bq q N : ℝ) ≤ q.d := by linarith
  have hgap0 : (0 : ℝ) < nq q N - (2 * Kq q + 1) := by linarith
  have hd4 : (q.d : ℝ) / 4 ≤ bq q N * (nq q N - (2 * Kq q + 1)) := by
    have h3 : bq q N * ((nq q N : ℝ) / 2) ≤ bq q N * (nq q N - (2 * Kq q + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hb0.le
    linarith
  have hσh2 : (2 : ℝ) ^ 134 ≤ σh q ^ 2 := by
    have h := σh_large hv
    calc (2 : ℝ) ^ 134 = (2 ^ 67) ^ 2 := by norm_num
      _ ≤ σh q ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  have hσp : 0 < σh q ^ 2 := lt_of_lt_of_le (by positivity) hσh2
  have hNb := budget_le hv hN
  have hNσ : (N : ℝ) ≤ q.d * σh q ^ 2 * D q / 2 ^ 437 := by
    have e : q.d * q.σ ^ 2 * D q / (2 ^ 703 * q.ε ^ 2) = q.d * σh q ^ 2 * D q / 2 ^ 437 := by
      unfold σh; rw [div_pow, mul_pow]; ring
    linarith
  have hm : (mq q N : ℝ) * Kq q ≤ 2 * N := by
    unfold mq; exact_mod_cast Nat.div_mul_le_self (2 * N) (Kq q)
  have hKD : 5 * D q ≤ 2 ^ 388 * Kq q := by
    have := hK1; rw [div_le_iff₀ (by positivity)] at this; linarith
  have hY0 : 0 ≤ q.d * σh q ^ 2 := by positivity
  have hratio : (mq q N : ℝ) ≤ q.d * σh q ^ 2 / 2 ^ 48 := by
    have h2 : q.d * σh q ^ 2 * D q ≤ q.d * σh q ^ 2 * (2 ^ 388 * Kq q / 5) :=
      mul_le_mul_of_nonneg_left (by linarith) hY0
    have hYK : 0 ≤ q.d * σh q ^ 2 * Kq q := mul_nonneg hY0 hK0.le
    have h1 : (mq q N : ℝ) * Kq q ≤ q.d * σh q ^ 2 / 2 ^ 48 * Kq q := by linarith
    exact le_of_mul_le_mul_right h1 hK0
  have hq' : 2 ^ 30 / (Aq q * bq q N * (nq q N - (2 * Kq q + 1))) ≤
      2 ^ 32 * 2025 / (σh q ^ 2 * q.d) := by
    rw [div_le_div_iff₀ (by unfold Aq; positivity) (by positivity)]
    unfold Aq
    have := mul_le_mul_of_nonneg_left hd4 hσp.le
    linarith
  have hm1 : (mq q N : ℝ) + 1 ≤ q.d * σh q ^ 2 / 2 ^ 48 + 1 := by linarith
  have hfin : 2 * (2 ^ 32 * 2025 / (σh q ^ 2 * q.d) * (q.d * σh q ^ 2 / 2 ^ 48 + 1)) ≤ 1 / 8 := by
    have hpos : 0 < σh q ^ 2 * q.d := by positivity
    have hne : σh q ^ 2 * q.d ≠ 0 := hpos.ne'
    have hσ0 : σh q ≠ 0 := (lt_of_lt_of_le (by positivity) (σh_large hv)).ne'
    have e : 2 ^ 32 * 2025 / (σh q ^ 2 * q.d) * (q.d * σh q ^ 2 / 2 ^ 48 + 1) =
        2 ^ 32 * 2025 / 2 ^ 48 + 2 ^ 32 * 2025 / (σh q ^ 2 * q.d) := by
      rw [mul_add, mul_one, show q.d * σh q ^ 2 = σh q ^ 2 * q.d by ring]
      congr 1
      field_simp
    rw [e]
    have h1 : 2 ^ 32 * 2025 / (σh q ^ 2 * q.d) ≤ 2 ^ 32 * 2025 / 2 ^ 134 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      calc (2 : ℝ) ^ 134 = 2 ^ 134 * 1 := by ring
        _ ≤ σh q ^ 2 * q.d := mul_le_mul hσh2 hd1 (by norm_num) hσp.le
    have : (2 : ℝ) ^ 32 * 2025 / 2 ^ 48 + 2 ^ 32 * 2025 / 2 ^ 134 ≤ 1 / 16 := by norm_num
    linarith
  calc 2 * (2 ^ 30 / (Aq q * bq q N * (nq q N - (2 * Kq q + 1))) * (mq q N + 1))
      ≤ 2 * (2 ^ 32 * 2025 / (σh q ^ 2 * q.d) * (q.d * σh q ^ 2 / 2 ^ 48 + 1)) := by
        gcongr
    _ ≤ 1 / 8 := hfin

end eta

end LongTails.Proofs.EscapeChainParameters
