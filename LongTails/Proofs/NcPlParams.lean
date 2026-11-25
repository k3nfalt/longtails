import LongTails.Setups.HighDimensionalStochasticNonconvexPL
import LongTails.Proofs.NcPlHiding

open scoped BigOperators

namespace LongTails.Proofs.NcPlParams

open LongTails.Setups.HighDimensionalStochasticNonconvexPL
open LongTails.Proofs.NcPlBlock LongTails.Proofs.NcPlBlockSmooth LongTails.Proofs.NcPlChainPL
open LongTails.Proofs.NcPlInstance LongTails.Proofs.NcPlHiding

noncomputable def kx (q : Params) : ℕ := ⌊q.L / (2 ^ 46 * q.μ)⌋₊

noncomputable def n1 (q : Params) : ℕ := max 1 (Nat.sqrt (kx q))

noncomputable def nn (q : Params) : ℕ := n1 q * n1 q - 1

noncomputable def mm (q : Params) : ℕ := ⌊q.L * q.Δ / (2 ^ 40 * q.ε ^ 2)⌋₊ - 1

noncomputable def ee (q : Params) : ℝ := 2 ^ 36 * q.ε ^ 2 / q.L

noncomputable def ss (q : Params) : ℝ := 2 ^ 31 * q.ε / q.L

noncomputable def th (q : Params) : ℝ := 1 / ((n1 q : ℝ) * 2 ^ 25)

noncomputable def qq (q : Params) : ℝ :=
  1 / (1 + q.σ ^ 2 * (n1 q : ℝ) ^ 2 / (1024 * q.ε ^ 2))

noncomputable def lowerBudget (q : Params) : ℕ :=
  ⌊q.L ^ 2 * q.Δ / (2 ^ 94 * q.μ * q.ε ^ 2) *
    (1 + q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2))⌋₊

lemma n1_pos (q : Params) : 1 ≤ n1 q := le_max_left _ _

lemma n1_real_pos (q : Params) : (0 : ℝ) < n1 q := by
  have := n1_pos q
  exact_mod_cast this

lemma nn_succ (q : Params) : nn q + 1 = n1 q * n1 q := by
  unfold nn
  have := Nat.mul_pos (n1_pos q) (n1_pos q)
  omega

lemma nn_real (q : Params) : (nn q : ℝ) + 1 = (n1 q : ℝ) ^ 2 := by
  have h := nn_succ q
  have h2 : ((nn q + 1 : ℕ) : ℝ) = ((n1 q * n1 q : ℕ) : ℝ) := by rw [h]
  push_cast at h2
  rw [h2]
  ring

lemma th_pos (q : Params) : 0 < th q := by
  have hn := n1_real_pos q
  unfold th
  positivity

lemma th_le_rho (q : Params) : th q ≤ 1 / (n1 q : ℝ) := by
  have hn := n1_real_pos q
  unfold th
  apply one_div_le_one_div_of_le hn
  nlinarith

lemma th_le_quarter (q : Params) : th q ≤ 1 / 4 := by
  have hn : (1 : ℝ) ≤ n1 q := by exact_mod_cast n1_pos q
  unfold th
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma mask_width (q : Params) :
    2 ^ 23 * th q + 1 / (3 * ((nn q : ℝ) + 1) * (1 / (n1 q : ℝ))) ≤ 1 / (n1 q : ℝ) := by
  have hn := n1_real_pos q
  rw [nn_real]
  unfold th
  have e : 2 ^ 23 * (1 / ((n1 q : ℝ) * 2 ^ 25)) + 1 / (3 * (n1 q : ℝ) ^ 2 * (1 / (n1 q : ℝ))) =
      7 / 12 * (1 / (n1 q : ℝ)) := by
    field_simp
    ring
  rw [e]
  have : 0 < 1 / (n1 q : ℝ) := by positivity
  linarith

lemma nm_cast (n : ℕ) : ((n : ℝ) + 1) / 2 ≤ ((n / 2 + 1 : ℕ) : ℝ) := by
  have h : n + 1 ≤ 2 * (n / 2 + 1) := by omega
  have h2 : ((n + 1 : ℕ) : ℝ) ≤ ((2 * (n / 2 + 1) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h2 ⊢
  linarith

section Valid

variable {q : Params} (hv : spec.valid q)

include hv

lemma pos_μ : 0 < q.μ := hv.1.1

lemma pos_ε : 0 < q.ε := hv.1.2.2.2.2

lemma nonneg_σ : 0 ≤ q.σ := hv.1.2.2.1

lemma nonneg_Δ : 0 ≤ q.Δ := hv.1.2.2.2.1

lemma pos_L : 0 < q.L := by
  have h := hv.2.1
  have := pos_μ hv
  nlinarith

lemma kappa_ge : 2 ≤ q.L / (2 ^ 46 * q.μ) := by
  have h := hv.2.1
  have hμ := pos_μ hv
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma kx_ge : 2 ≤ kx q := by
  unfold kx
  exact Nat.le_floor (by exact_mod_cast kappa_ge hv)

lemma n1_eq : n1 q = Nat.sqrt (kx q) := by
  unfold n1
  apply max_eq_right
  have h := kx_ge hv
  have h1 : Nat.sqrt 1 ≤ Nat.sqrt (kx q) := Nat.sqrt_le_sqrt (by omega)
  simpa using h1

lemma n1_sq_le : (n1 q : ℝ) ^ 2 ≤ q.L / (2 ^ 46 * q.μ) := by
  have h1 : n1 q * n1 q ≤ kx q := by
    rw [n1_eq hv]
    exact Nat.sqrt_le (kx q)
  have h2 : (kx q : ℝ) ≤ q.L / (2 ^ 46 * q.μ) :=
    Nat.floor_le (le_trans (by norm_num) (kappa_ge hv))
  have h3 : ((n1 q * n1 q : ℕ) : ℝ) ≤ (kx q : ℝ) := by exact_mod_cast h1
  push_cast at h3
  nlinarith

lemma n1_sq_ge : q.L / (2 ^ 49 * q.μ) ≤ (n1 q : ℝ) ^ 2 := by
  have hμ := pos_μ hv
  have h1 : kx q < (n1 q + 1) * (n1 q + 1) := by
    rw [n1_eq hv]
    exact Nat.lt_succ_sqrt (kx q)
  have h2 : q.L / (2 ^ 46 * q.μ) < (kx q : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : ((kx q : ℕ) : ℝ) < (((n1 q + 1) * (n1 q + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  have h4 := n1_real_pos q
  have h5 : (1 : ℝ) ≤ n1 q := by exact_mod_cast n1_pos q
  have h6 := kappa_ge hv
  have e : q.L / (2 ^ 49 * q.μ) = q.L / (2 ^ 46 * q.μ) / 8 := by
    field_simp
    ring
  rw [e]
  have h7 : (n1 q : ℝ) ≤ (n1 q : ℝ) ^ 2 := by nlinarith
  have h8 : (1 : ℝ) ≤ (n1 q : ℝ) ^ 2 := by nlinarith
  nlinarith

lemma mfloor_ge : (128 : ℝ) ≤ q.L * q.Δ / (2 ^ 40 * q.ε ^ 2) := by
  have h := hv.2.2.1
  have hε := pos_ε hv
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma mm_succ : (mm q : ℝ) + 1 = (⌊q.L * q.Δ / (2 ^ 40 * q.ε ^ 2)⌋₊ : ℝ) := by
  have h : 1 ≤ ⌊q.L * q.Δ / (2 ^ 40 * q.ε ^ 2)⌋₊ :=
    Nat.le_floor (by
      rw [Nat.cast_one]
      exact le_trans (by norm_num) (mfloor_ge hv))
  unfold mm
  have h2 : ((⌊q.L * q.Δ / (2 ^ 40 * q.ε ^ 2)⌋₊ - 1 + 1 : ℕ) : ℝ) =
      (⌊q.L * q.Δ / (2 ^ 40 * q.ε ^ 2)⌋₊ : ℝ) := by
    rw [Nat.sub_add_cancel h]
  push_cast at h2
  exact h2

lemma mm_le : (mm q : ℝ) + 1 ≤ q.L * q.Δ / (2 ^ 40 * q.ε ^ 2) := by
  rw [mm_succ hv]
  exact Nat.floor_le (le_trans (by norm_num) (mfloor_ge hv))

lemma mm_ge : q.L * q.Δ / (2 ^ 41 * q.ε ^ 2) ≤ (mm q : ℝ) + 1 := by
  have hε := pos_ε hv
  rw [mm_succ hv]
  have h2 : q.L * q.Δ / (2 ^ 40 * q.ε ^ 2) < (⌊q.L * q.Δ / (2 ^ 40 * q.ε ^ 2)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h3 := mfloor_ge hv
  have e : q.L * q.Δ / (2 ^ 41 * q.ε ^ 2) = q.L * q.Δ / (2 ^ 40 * q.ε ^ 2) / 2 := by
    rw [div_div]
    congr 1
    ring
  rw [e]
  linarith

lemma ee_pos : 0 < ee q := by
  have := pos_ε hv
  have := pos_L hv
  unfold ee
  positivity

lemma ss_pos : 0 < ss q := by
  have := pos_ε hv
  have := pos_L hv
  unfold ss
  positivity

lemma ee_div_ss : ee q / ss q = 32 * q.ε := by
  have hε := pos_ε hv
  have hL := pos_L hv
  unfold ee ss
  field_simp
  ring

lemma ee_div_ss_sq : ee q / ss q ^ 2 = q.L / 2 ^ 26 := by
  have hε := pos_ε hv
  have hL := pos_L hv
  unfold ee ss
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp

lemma qq_pos : 0 < qq q := by
  have hε := pos_ε hv
  unfold qq
  positivity

lemma qq_le_one : qq q ≤ 1 := by
  have hε := pos_ε hv
  unfold qq
  rw [div_le_one (by positivity)]
  have : 0 ≤ q.σ ^ 2 * (n1 q : ℝ) ^ 2 / (1024 * q.ε ^ 2) := by positivity
  linarith

lemma qq_var : (1 / qq q - 1) * (1 / (n1 q : ℝ)) ^ 2 = q.σ ^ 2 / (1024 * q.ε ^ 2) := by
  have hε := pos_ε hv
  have hn := n1_real_pos q
  unfold qq
  rw [one_div_one_div]
  field_simp
  ring

lemma pl_const : 2 * q.μ * (147 / lamOf (nn q)) ≤ q.L / 2 ^ 26 := by
  have hμ := pos_μ hv
  have h := n1_sq_le hv
  rw [le_div_iff₀ (by positivity)] at h
  unfold lamOf
  rw [nn_real]
  have hn := n1_real_pos q
  have e : 2 * q.μ * (147 / (1 / (2048 * (n1 q : ℝ) ^ 2))) =
      294 * 2048 * ((n1 q : ℝ) ^ 2 * q.μ) := by
    rw [div_div_eq_mul_div, div_one]
    ring
  rw [e, le_div_iff₀ (by norm_num)]
  nlinarith [mul_nonneg (sq_nonneg (n1 q : ℝ)) hμ.le]

lemma delta_room : 13 * ee q * ((mm q : ℝ) + 1) ≤ q.Δ := by
  have hε := pos_ε hv
  have hL := pos_L hv
  have h := mm_le hv
  have he := ee_pos hv
  have h2 : ee q * ((mm q : ℝ) + 1) ≤ ee q * (q.L * q.Δ / (2 ^ 40 * q.ε ^ 2)) :=
    mul_le_mul_of_nonneg_left h he.le
  have e : ee q * (q.L * q.Δ / (2 ^ 40 * q.ε ^ 2)) = q.Δ / 16 := by
    unfold ee
    field_simp
    ring
  have hΔ := nonneg_Δ hv
  linarith

lemma budget_real {N : ℕ} (hN : N ≤ lowerBudget q) :
    (N : ℝ) ≤ q.L ^ 2 * q.Δ / (2 ^ 94 * q.μ * q.ε ^ 2) *
      (1 + q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2)) := by
  have hμ := pos_μ hv
  have hε := pos_ε hv
  have hL := pos_L hv
  have hΔ := nonneg_Δ hv
  have h0 : 0 ≤ q.L ^ 2 * q.Δ / (2 ^ 94 * q.μ * q.ε ^ 2) *
      (1 + q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2)) := by positivity
  have h1 : (N : ℝ) ≤ (lowerBudget q : ℝ) := by exact_mod_cast hN
  exact h1.trans (Nat.floor_le h0)

lemma budget_count {N : ℕ} (hN : N ≤ lowerBudget q) :
    8 * ((N : ℝ) * qq q) ≤ ((mm q : ℝ) + 1) * (((nn q) / 2 + 1 : ℕ) : ℝ) := by
  have hμ := pos_μ hv
  have hε := pos_ε hv
  have hL := pos_L hv
  have hΔ := nonneg_Δ hv
  have hb := budget_real hv hN
  have hm := mm_ge hv
  have hn := n1_sq_ge hv
  have hnm := nm_cast (nn q)
  rw [nn_real] at hnm
  obtain ⟨S, hS⟩ : ∃ S, S = 1 + q.σ ^ 2 * (n1 q : ℝ) ^ 2 / (1024 * q.ε ^ 2) := ⟨_, rfl⟩
  have hS1 : 1 + q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2) ≤ S := by
    rw [hS]
    have e : q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2) =
        q.σ ^ 2 * (q.L / (2 ^ 49 * q.μ)) / (1024 * q.ε ^ 2) := by
      field_simp
      ring
    rw [e]
    have : q.σ ^ 2 * (q.L / (2 ^ 49 * q.μ)) / (1024 * q.ε ^ 2) ≤
        q.σ ^ 2 * (n1 q : ℝ) ^ 2 / (1024 * q.ε ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (sq_nonneg _)) (by positivity)
    linarith
  have hSpos : 0 < S := by
    rw [hS]
    positivity
  have hq : qq q = 1 / S := by
    unfold qq
    rw [hS]
  rw [hq]
  have e1 : 8 * ((N : ℝ) * (1 / S)) = 8 * (N : ℝ) / S := by ring
  rw [e1, div_le_iff₀ hSpos]
  have hA : 0 ≤ q.L * q.Δ / (2 ^ 41 * q.ε ^ 2) := by positivity
  have hB : 0 ≤ q.L / (2 ^ 49 * q.μ) := by positivity
  have hprod : q.L * q.Δ / (2 ^ 41 * q.ε ^ 2) * (q.L / (2 ^ 49 * q.μ) / 2) *
      (1 + q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2)) ≤
      ((mm q : ℝ) + 1) * (((nn q) / 2 + 1 : ℕ) : ℝ) * S := by
    have hC : 0 ≤ 1 + q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2) := by positivity
    have h1 : q.L / (2 ^ 49 * q.μ) / 2 ≤ (((nn q) / 2 + 1 : ℕ) : ℝ) := by linarith
    exact mul_le_mul (mul_le_mul hm h1 (by positivity) (by positivity)) hS1 hC
      (by positivity)
  have e2 : q.L * q.Δ / (2 ^ 41 * q.ε ^ 2) * (q.L / (2 ^ 49 * q.μ) / 2) *
      (1 + q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2)) =
      8 * (q.L ^ 2 * q.Δ / (2 ^ 94 * q.μ * q.ε ^ 2) *
        (1 + q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2))) := by
    field_simp
    ring
  rw [e2] at hprod
  linarith

end Valid

noncomputable def geo (q : Params) : Geo where
  m := mm q
  n := nn q
  k := (mm q + 1) * (nn q + 2) - 1
  r := rs (n1 q) (nn q + 1)
  ρ := 1 / (n1 q : ℝ)
  Bx := 2 ^ 20 * Real.sqrt ((mm q : ℝ) + 1)
  By := 2 ^ 10 * Real.sqrt (((mm q : ℝ) + 1) * ((nn q : ℝ) + 1))
  hk := Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
  scales := ⟨one_div_pos.mpr (n1_real_pos q), fun k _ => rs_ge _ _ _,
    fun k hk => rs_sq (nn_succ q) (by omega)⟩
  hBx := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  hBy := mul_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  hBxM := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  hByM := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have : (0 : ℝ) ≤ ((mm q : ℝ) + 1) * ((nn q : ℝ) + 1) := by positivity
    nlinarith

lemma geo_k (q : Params) : ((geo q).k : ℝ) + 1 = ((mm q : ℝ) + 1) * ((nn q : ℝ) + 2) := by
  have h := (geo q).hk
  have h2 : (((geo q).k + 1 : ℕ) : ℝ) = ((((geo q).m + 1) * ((geo q).n + 2) : ℕ) : ℝ) := by
    rw [h]
  push_cast at h2
  exact h2

lemma geo_B_sq (q : Params) :
    (2 * (geo q).Bx + 2 * (geo q).By) ^ 2 ≤
      2 ^ 44 * (((mm q : ℝ) + 1) * ((nn q : ℝ) + 1)) := by
  have hx : (geo q).Bx ^ 2 = 2 ^ 40 * ((mm q : ℝ) + 1) := by
    change (2 ^ 20 * Real.sqrt ((mm q : ℝ) + 1)) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hy : (geo q).By ^ 2 = 2 ^ 20 * (((mm q : ℝ) + 1) * ((nn q : ℝ) + 1)) := by
    change (2 ^ 10 * Real.sqrt (((mm q : ℝ) + 1) * ((nn q : ℝ) + 1))) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have h0 : (0 : ℝ) ≤ (mm q : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) ≤ (nn q : ℝ) := Nat.cast_nonneg _
  have hmn := mul_nonneg h0 hn0
  nlinarith [sq_nonneg ((geo q).Bx - (geo q).By)]

section Dimension

noncomputable def xi (q : Params) : ℝ :=
  q.L ^ 2 * q.Δ / (q.μ * q.ε ^ 2) * (1 + q.L * q.σ ^ 2 / (q.μ * q.ε ^ 2))

lemma dim_arith {T K BT Ξ M Nn : ℝ} (hTΞ : T ≤ Ξ + 1) (hK0 : 0 ≤ K) (hK : K ≤ 2 * (M * Nn))
    (hBT0 : 0 ≤ BT) (hBT : BT ≤ 2 ^ 94 * (M * Nn ^ 2)) (hM1 : 1 ≤ M) (hN1 : 1 ≤ Nn)
    (hΞ0 : 0 ≤ Ξ) : 8 * (T * K * BT) + K ≤ 2 ^ 99 * ((Ξ + 1) * M ^ 2 * Nn ^ 3) := by
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ Nn := by linarith
  have hΞ1 : 0 ≤ Ξ + 1 := by linarith
  have a1 : T * K ≤ (Ξ + 1) * (2 * (M * Nn)) := mul_le_mul hTΞ hK hK0 hΞ1
  have a2 : T * K * BT ≤ (Ξ + 1) * (2 * (M * Nn)) * (2 ^ 94 * (M * Nn ^ 2)) :=
    mul_le_mul a1 hBT hBT0 (mul_nonneg hΞ1 (mul_nonneg (by norm_num) (mul_nonneg hM0 hN0)))
  have e : (Ξ + 1) * (2 * (M * Nn)) * (2 ^ 94 * (M * Nn ^ 2)) =
      2 ^ 95 * ((Ξ + 1) * M ^ 2 * Nn ^ 3) := by ring
  rw [e] at a2
  have h2 : M ≤ M ^ 2 := by nlinarith
  have hN2 : 1 ≤ Nn ^ 2 := by nlinarith
  have h3 : Nn ≤ Nn ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hN2 hN0]
  have hP0 : 0 ≤ M ^ 2 * Nn ^ 3 := by positivity
  have hx : M * Nn ≤ M ^ 2 * Nn ^ 3 := mul_le_mul h2 h3 hN0 (sq_nonneg M)
  have hy : M ^ 2 * Nn ^ 3 ≤ (Ξ + 1) * (M ^ 2 * Nn ^ 3) := le_mul_of_one_le_left hP0 (by linarith)
  have e2 : (Ξ + 1) * (M ^ 2 * Nn ^ 3) = (Ξ + 1) * M ^ 2 * Nn ^ 3 := by ring
  rw [e2] at hy
  linarith

lemma dim_K (q : Params) :
    (((geo q).k + 1 : ℕ) : ℝ) ≤ 2 * (((mm q : ℝ) + 1) * ((nn q : ℝ) + 1)) := by
  have hk := geo_k q
  have hm0 : (0 : ℝ) ≤ (mm q : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (nn q : ℝ) := Nat.cast_nonneg _
  push_cast
  rw [hk]
  nlinarith [mul_nonneg hm0 hn0]

lemma th_sq_inv (q : Params) : 1 / th q ^ 2 = 2 ^ 50 * ((nn q : ℝ) + 1) := by
  have hn := n1_real_pos q
  have e : th q ^ 2 = 1 / ((n1 q : ℝ) * 2 ^ 25) ^ 2 := by
    unfold th
    rw [one_div_pow]
  rw [e, one_div_one_div, nn_real]
  ring

lemma dim_BT (q : Params) :
    (2 * (geo q).Bx + 2 * (geo q).By) ^ 2 / th q ^ 2 ≤
      2 ^ 94 * (((mm q : ℝ) + 1) * ((nn q : ℝ) + 1) ^ 2) := by
  have hB := geo_B_sq q
  have hm0 : (0 : ℝ) ≤ (mm q : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (nn q : ℝ) := Nat.cast_nonneg _
  have hNn0 : (0 : ℝ) ≤ 2 ^ 50 * ((nn q : ℝ) + 1) := by positivity
  rw [div_eq_mul_one_div, th_sq_inv]
  have h := mul_le_mul_of_nonneg_right hB hNn0
  have e : 2 ^ 44 * (((mm q : ℝ) + 1) * ((nn q : ℝ) + 1)) * (2 ^ 50 * ((nn q : ℝ) + 1)) =
      2 ^ 94 * (((mm q : ℝ) + 1) * ((nn q : ℝ) + 1) ^ 2) := by ring
  rw [e] at h
  exact h

variable {q : Params} (hv : spec.valid q)

include hv

lemma xi_nonneg : 0 ≤ xi q := by
  have hμ := pos_μ hv
  have hε := pos_ε hv
  have hL := pos_L hv
  have hΔ := nonneg_Δ hv
  unfold xi
  positivity

lemma dim_T {N : ℕ} (hN : N ≤ lowerBudget q) : ((N + 1 : ℕ) : ℝ) ≤ xi q + 1 := by
  have hμ := pos_μ hv
  have hε := pos_ε hv
  have hL := pos_L hv
  have hΔ := nonneg_Δ hv
  have hb := budget_real hv hN
  have hc : 0 < q.μ * q.ε ^ 2 := by positivity
  have hle94 : q.μ * q.ε ^ 2 ≤ 2 ^ 94 * q.μ * q.ε ^ 2 := by nlinarith
  have hle59 : q.μ * q.ε ^ 2 ≤ 2 ^ 59 * q.μ * q.ε ^ 2 := by nlinarith
  have h1 : q.L ^ 2 * q.Δ / (2 ^ 94 * q.μ * q.ε ^ 2) ≤ q.L ^ 2 * q.Δ / (q.μ * q.ε ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) hc hle94
  have h2 : q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2) ≤ q.L * q.σ ^ 2 / (q.μ * q.ε ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) hc hle59
  have h3 : 0 ≤ q.L ^ 2 * q.Δ / (2 ^ 94 * q.μ * q.ε ^ 2) := by positivity
  have h4 : 0 ≤ 1 + q.L * q.σ ^ 2 / (q.μ * q.ε ^ 2) := by positivity
  have h5 : q.L ^ 2 * q.Δ / (2 ^ 94 * q.μ * q.ε ^ 2) *
      (1 + q.L * q.σ ^ 2 / (2 ^ 59 * q.μ * q.ε ^ 2)) ≤ xi q := by
    unfold xi
    exact mul_le_mul h1 (by linarith) (by positivity) (by positivity)
  push_cast
  linarith

lemma dim_final :
    2 ^ 99 * ((xi q + 1) * ((mm q : ℝ) + 1) ^ 2 * ((nn q : ℝ) + 1) ^ 3) ≤ q.d := by
  have hμ := pos_μ hv
  have hε := pos_ε hv
  have hL := pos_L hv
  have hΔ := nonneg_Δ hv
  have hd := hv.2.2.2
  have hm := mm_le hv
  have hn := n1_sq_le hv
  have hξ := xi_nonneg hv
  have hm0 : (0 : ℝ) ≤ (mm q : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) ≤ (nn q : ℝ) + 1 := by positivity
  have hε2 : 0 < q.ε ^ 2 := by positivity
  have hMle : (mm q : ℝ) + 1 ≤ q.L * q.Δ / q.ε ^ 2 := by
    refine hm.trans ?_
    apply div_le_div_of_nonneg_left (by positivity) hε2
    nlinarith
  have hNle : (nn q : ℝ) + 1 ≤ q.L / q.μ := by
    rw [nn_real]
    refine hn.trans ?_
    apply div_le_div_of_nonneg_left hL.le hμ
    nlinarith
  have b1 : ((mm q : ℝ) + 1) ^ 2 ≤ (q.L * q.Δ / q.ε ^ 2) ^ 2 := pow_le_pow_left₀ hm0 hMle 2
  have b2 : ((nn q : ℝ) + 1) ^ 3 ≤ (q.L / q.μ) ^ 3 := pow_le_pow_left₀ hn0 hNle 3
  have hξ1 : 0 ≤ xi q + 1 := by linarith
  have step : (xi q + 1) * ((mm q : ℝ) + 1) ^ 2 * ((nn q : ℝ) + 1) ^ 3 ≤
      (xi q + 1) * (q.L * q.Δ / q.ε ^ 2) ^ 2 * (q.L / q.μ) ^ 3 :=
    mul_le_mul (mul_le_mul_of_nonneg_left b1 hξ1) b2 (by positivity)
      (mul_nonneg hξ1 (sq_nonneg _))
  have e2 : 2 ^ 99 * (xi q + 1) * (q.L * q.Δ / q.ε ^ 2) ^ 2 * (q.L / q.μ) ^ 3 =
      2 ^ 99 * ((xi q + 1) * (q.L * q.Δ / q.ε ^ 2) ^ 2 * (q.L / q.μ) ^ 3) := by ring
  have hd' : 2 ^ 99 * (xi q + 1) * (q.L * q.Δ / q.ε ^ 2) ^ 2 * (q.L / q.μ) ^ 3 ≤ q.d := hd
  rw [e2] at hd'
  linarith

theorem dimension_room {N : ℕ} (hN : N ≤ lowerBudget q) :
    8 * (((N + 1 : ℕ) : ℝ) * (((geo q).k + 1 : ℕ) : ℝ) *
      ((2 * (geo q).Bx + 2 * (geo q).By) ^ 2 / th q ^ 2)) + (((geo q).k + 1 : ℕ) : ℝ) ≤ q.d := by
  have h1 := dim_T hv hN
  have h2 := dim_K q
  have h3 := dim_BT q
  have h4 := dim_final hv
  have hth := th_pos q
  have hBT0 : 0 ≤ (2 * (geo q).Bx + 2 * (geo q).By) ^ 2 / th q ^ 2 := by positivity
  have hm0 : (0 : ℝ) ≤ (mm q : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (nn q : ℝ) := Nat.cast_nonneg _
  have h5 := dim_arith h1 (Nat.cast_nonneg _) h2 hBT0 h3 (by linarith) (by linarith)
    (xi_nonneg hv)
  linarith

end Dimension

end LongTails.Proofs.NcPlParams
