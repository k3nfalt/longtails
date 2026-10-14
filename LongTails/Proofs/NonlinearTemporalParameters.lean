import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OracleTemplate.NonlinearTemporalDiscrepancy

lemma geometric_log_decay {q c X : ℝ} (hq : 0 ≤ q) (hc : 0 < c)
    (hqc : q ≤ 1 - c) (hX : 0 < X) (m n : ℕ)
    (hn : (m : ℝ) / c * Real.log X ≤ n) :
    q ^ n ≤ (X ^ m)⁻¹ := by
  have hbase : q ≤ Real.exp (-c) := by linarith [Real.add_one_le_exp (-c)]
  have hp := pow_le_pow_left₀ hq hbase n
  rw [← Real.exp_nat_mul] at hp
  have hh := mul_le_mul_of_nonneg_left hn hc.le
  have hid : c * ((m : ℝ) / c * Real.log X) = m * Real.log X := by field_simp
  rw [hid] at hh
  have he : Real.exp ((n : ℝ) * -c) ≤ Real.exp (-Real.log (X ^ m)) := by
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    nlinarith
  rw [Real.exp_neg, Real.exp_log (pow_pos hX m)] at he
  exact hp.trans he

lemma reciprocal_momentum_bounds {κ a b : ℝ} (hκ : 1 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let θ := 1 / (4096 * (1 + κ + a + b))
    0 < θ ∧ θ ≤ 1 ∧ θ * κ ≤ 1 ∧ θ * a ≤ 1 / 4096 ∧ θ * b ≤ 1 / 4096 := by
  have hd : 0 < 4096 * (1 + κ + a + b) := by positivity
  dsimp only
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mpr
    nlinarith
  · rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hd).mpr
    linarith

  · rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hd).mpr
    linarith

lemma log_half_lower {X : ℝ} (hX : 2 ≤ X) : (1 : ℝ) / 2 ≤ Real.log X := by
  have hXp : 0 < X := by linarith
  have hi : X⁻¹ ≤ (1 : ℝ) / 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hXp).mpr (by linarith)
  linarith [Real.one_sub_inv_le_log_of_pos hXp]

lemma averaged_root_contraction {θ : ℝ} (hθ1 : θ ≤ 1) :
    0 ≤ (1 + Real.sqrt (1 - θ)) / 2 ∧
      (1 + Real.sqrt (1 - θ)) / 2 ≤ 1 - θ / 4 := by
  have hs := Real.sq_sqrt (sub_nonneg.mpr hθ1)
  have hs0 := Real.sqrt_nonneg (1 - θ)
  constructor
  · positivity
  · nlinarith [sq_nonneg (Real.sqrt (1 - θ) - 1)]

lemma tail_length_decay {θ r : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 1 ≤ r) :
    let n := ⌈64 / θ * Real.log (2 + r)⌉₊
    0 < n ∧ 1 / θ ≤ (n : ℝ) ∧
      ((1 + Real.sqrt (1 - θ)) / 2) ^ n ≤ ((2 + r) ^ (16 : ℕ))⁻¹ := by
  let n := ⌈64 / θ * Real.log (2 + r)⌉₊
  have hc : 64 / θ * Real.log (2 + r) ≤ (n : ℝ) := Nat.le_ceil _
  have hl := log_half_lower (show 2 ≤ 2 + r by linarith)
  have hmul := mul_le_mul_of_nonneg_left hl (show 0 ≤ 64 / θ by positivity)
  have hn : 1 / θ ≤ (n : ℝ) := by
    have he : 64 / θ * (1 / 2) = 32 / θ := by ring
    rw [he] at hmul
    have hh : 1 / θ ≤ 32 / θ := div_le_div_of_nonneg_right (by norm_num) hθ.le
    exact hh.trans (hmul.trans hc)
  have hnp : 0 < n := by
    have hh : (0 : ℝ) < n := (by positivity : (0 : ℝ) < 1 / θ).trans_le hn
    exact_mod_cast hh
  obtain ⟨hq0, hqc⟩ := averaged_root_contraction hθ1
  refine ⟨hnp, hn, ?_⟩
  apply geometric_log_decay hq0 (by positivity : 0 < θ / 4) hqc (by linarith) 16 n
  convert hc using 1; push_cast; ring
lemma warmup_length_decay {θ t : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ht : 0 ≤ t) :
    (1 - 3 * θ / 4) ^ ⌈16 / θ * Real.log (2 + 4096 * t)⌉₊ ≤
      ((2 + 4096 * t) ^ (2 : ℕ))⁻¹ := by
  apply geometric_log_decay (by linarith) (by positivity : 0 < θ / 8)
    (by linarith) (by positivity) 2
  convert Nat.le_ceil (16 / θ * Real.log (2 + 4096 * t)) using 1; push_cast; ring

lemma warmup_scalar_finish {μ M Δ s F E₁ : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hΔ : 0 ≤ Δ) (hs : 0 ≤ s)
    (hentry : μ ^ 3 < 4096 * M ^ 2 * Δ)
    (hsbound : s ≤ ((2 + 4096 * M ^ 2 * Δ / μ ^ 3) ^ (2 : ℕ))⁻¹)
    (hfloor : M ^ 2 * F ≤ μ ^ 3 / 4096)
    (hE : E₁ ≤ 2 * Δ * s + F) :
    E₁ ≤ 2 * Δ ∧ M ^ 2 * E₁ ≤ μ ^ 3 / 1024 := by
  let t := M ^ 2 * Δ / μ ^ 3
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hden : 0 < (2 + 4096 * t) ^ 2 := by positivity
  have hs' : s * (2 + 4096 * t) ^ 2 ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [one_div, t, mul_div_assoc, mul_assoc] using hsbound
  have hp : 4096 * t ≤ (2 + 4096 * t) ^ 2 := by nlinarith [sq_nonneg (4096 * t)]
  have hs2 : s ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ (2 + 4096 * t) ^ 2 by
      nlinarith [sq_nonneg (4096 * t)]) hs
    nlinarith
  have hts : 4096 * t * s ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hp hs
    nlinarith
  have hts' : M ^ 2 * Δ * s ≤ μ ^ 3 / 4096 := by
    have hh := mul_le_mul_of_nonneg_left hts (show 0 ≤ μ ^ 3 by positivity)
    have hid : μ ^ 3 * (4096 * t * s) = 4096 * M ^ 2 * Δ * s := by dsimp [t]; field_simp
    rw [hid] at hh
    linarith
  have hF : F ≤ Δ := by
    exact le_of_mul_le_mul_left (show M ^ 2 * F ≤ M ^ 2 * Δ by linarith)
      (sq_pos_of_pos hM)
  constructor
  · have hh := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ 2 * Δ by positivity)
    linarith
  · have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg M)
    nlinarith

lemma warmup_floor_bound {μ M D B : ℝ} (hμ : 0 < μ) (hB : 0 < B)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hb : 65536 * (1 + M * D / μ ^ 2) ≤ B) :
    M ^ 2 * (4 * (2 * D / B) ^ 2 / μ) ≤ μ ^ 3 / 4096 := by
  have ha : 0 ≤ M * D / μ ^ 2 := by positivity
  have hba : 256 * (M * D / μ ^ 2) ≤ B := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hba (sq_nonneg μ)
  have hid : (256 * (M * D / μ ^ 2)) * μ ^ 2 = 256 * M * D := by field_simp
  rw [hid] at hh
  have hratio : M * D / B ≤ μ ^ 2 / 256 := by
    apply (div_le_iff₀ hB).mpr
    nlinarith
  have hsq := pow_le_pow_left₀ (show 0 ≤ M * D / B by positivity) hratio 2
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 16 / μ by positivity)
  have he₁ : 16 / μ * (M * D / B) ^ 2 = M ^ 2 * (4 * (2 * D / B) ^ 2 / μ) := by ring
  have he₂ : 16 / μ * (μ ^ 2 / 256) ^ 2 = μ ^ 3 / 4096 := by field_simp; ring
  rwa [he₁, he₂] at hm

lemma tail_transient_bound {r ε P s : ℝ} (hr : 1 ≤ r) (hε : 0 ≤ ε)
     (hP2 : P ^ 2 ≤ 6 * ε * r) (hs : 0 ≤ s)
    (hsbound : s ≤ ((2 + r) ^ (16 : ℕ))⁻¹) : P * s ≤ Real.sqrt ε / 8 := by
  have hfour : 64 * r ≤ (2 + r) ^ 4 := by
    nlinarith [pow_nonneg (show 0 ≤ r - 1 by linarith) 4,
      pow_nonneg (show 0 ≤ r - 1 by linarith) 3, sq_nonneg (r - 1)]
  have hp : (2 + r) ^ 4 ≤ (2 + r) ^ 16 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 2 + r) (by norm_num)
  have hden : 0 < (2 + r) ^ (16 : ℕ) := by positivity
  have hsb : s * (2 + r) ^ (16 : ℕ) ≤ 1 :=
    (le_div_iff₀ hden).mp (by simpa only [one_div] using hsbound)
  have hrs : 64 * r * s ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hfour.trans hp) hs
    nlinarith
  have hs64 : 64 * s ≤ 1 := by nlinarith
  have hss := mul_le_mul_of_nonneg_right hrs hs
  have hrs2 : r * s ^ 2 ≤ 1 / 4096 := by nlinarith
  have hpp := mul_le_mul_of_nonneg_right hP2 (sq_nonneg s)
  have hh := mul_le_mul_of_nonneg_left hrs2 (show 0 ≤ 6 * ε by positivity)
  have hsqrt := Real.sq_sqrt hε
  have hroot := Real.sqrt_nonneg ε
  nlinarith [sq_nonneg (P * s - Real.sqrt ε / 8)]

lemma averaged_noise_constant {χ θ ρ D : ℝ} (hχ : 0 < χ) (hθ : 0 < θ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hθρ : θ = 1 - ρ ^ 2) (hD : 0 ≤ D)
    (n : ℕ) (hn : 0 < n) (hbudget : 1 / θ ≤ (n : ℝ)) :
    2 * (θ * Real.sqrt 2 / χ) * D / ((1 - ρ) * n) ≤ 8 * θ * D / χ := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < 1 - ρ := by linarith
  have hs : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hid : 2 * (θ * Real.sqrt 2 / χ) * D / ((1 - ρ) * n) =
      2 * Real.sqrt 2 * (1 + ρ) * D / (χ * n) := by
    rw [hθρ]
    field_simp
    ring
  rw [hid]
  have hc : 2 * Real.sqrt 2 * (1 + ρ) ≤ 8 := by nlinarith [Real.sqrt_nonneg 2]
  have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ D / (χ * n) by positivity)
  have hnθ : 1 ≤ θ * n := by
    have hh := (div_le_iff₀ hθ).mp hbudget
    nlinarith
  have hlast : 8 * D / (χ * n) ≤ 8 * θ * D / χ := by
    apply (div_le_iff₀ (show 0 < χ * n by positivity)).mpr
    have he : 8 * θ * D / χ * (χ * n) = 8 * D * (θ * n) := by field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hnθ (show 0 ≤ 8 * D by positivity)]
  exact (show 2 * Real.sqrt 2 * (1 + ρ) * D / (χ * n) ≤ 8 * D / (χ * n) by
    convert hh using 1 <;> ring).trans hlast

lemma local_response_constants {χ μ θ ρ a b M : ℝ}
    (hχ : 0 < χ) (hχ2 : χ ^ 2 = μ) (hθ : 0 < θ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hθρ : θ = 1 - ρ ^ 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (haM : M * a ≤ μ / 16) (hbM : M * b ≤ μ / 32) :
    let β := θ * Real.sqrt 2 / χ
    let q := (1 + ρ) / 2
    (β * M / χ) * (a + 2 * b) ≤ (1 - ρ) / 2 ∧
      χ * a + 2 * β * M * a ^ 2 / (q - ρ) ≤ 2 * (χ * a) ∧
      8 * β * M * b ^ 2 / (1 - ρ) ≤ χ * b := by
  have hμ : 0 < μ := by nlinarith
  have hd : 0 < 1 - ρ := by linarith
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs : Real.sqrt 2 ≤ 2 := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have ht : θ / (1 - ρ) = 1 + ρ := (div_eq_iff hd.ne').mpr (by rw [hθρ]; ring)
  have ht2 : θ ≤ 2 * (1 - ρ) := by nlinarith [sq_nonneg (1 - ρ)]
  have hsum : M * (a + 2 * b) ≤ μ / 8 := by nlinarith
  dsimp only
  constructor
  · have hprod := mul_le_mul_of_nonneg_left hsum (show 0 ≤ θ * Real.sqrt 2 by positivity)
    have hs' := mul_le_mul_of_nonneg_left hs (show 0 ≤ θ * μ / 8 by positivity)
    have ht' := mul_le_mul_of_nonneg_right ht2 (show 0 ≤ μ / 4 by positivity)
    have he : (θ * Real.sqrt 2 / χ * M / χ) * (a + 2 * b) =
        (θ * Real.sqrt 2 * (M * (a + 2 * b))) / μ := by
      rw [← hχ2]
      ring
    rw [he]
    apply (div_le_iff₀ hμ).mpr
    nlinarith
  · constructor
    · have hid : 2 * (θ * Real.sqrt 2 / χ) * M * a ^ 2 / ((1 + ρ) / 2 - ρ) =
          (4 * Real.sqrt 2 * (1 + ρ) / χ) * (M * a) * a := by
        have hq : (1 + ρ) / 2 - ρ = (1 - ρ) / 2 := by ring
        rw [hq]
        have he : θ = (1 - ρ) * (1 + ρ) := by rw [hθρ]; ring
        rw [he]
        field_simp [hχ.ne', hd.ne']
        ring
      rw [hid]
      have hc : 4 * Real.sqrt 2 * (1 + ρ) ≤ 16 := by nlinarith
      have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ (M * a) * a / χ by positivity)
      have hm := mul_le_mul_of_nonneg_right haM (show 0 ≤ 16 * a / χ by positivity)
      have he : μ * a / χ = χ * a := by rw [← hχ2]; field_simp
      have hbound : (4 * Real.sqrt 2 * (1 + ρ) / χ) * (M * a) * a ≤ χ * a := by
        calc
          _ = (4 * Real.sqrt 2 * (1 + ρ)) * ((M * a) * a / χ) := by ring
          _ ≤ 16 * ((M * a) * a / χ) := hh
          _ ≤ μ * a / χ := by convert hm using 1 <;> ring
          _ = _ := he
      linarith
    · have hid : 8 * (θ * Real.sqrt 2 / χ) * M * b ^ 2 / (1 - ρ) =
          (8 * Real.sqrt 2 * (1 + ρ) / χ) * (M * b) * b := by
        have he : θ = (1 - ρ) * (1 + ρ) := by rw [hθρ]; ring
        rw [he]
        field_simp [hχ.ne', hd.ne']
      rw [hid]
      have hc : 8 * Real.sqrt 2 * (1 + ρ) ≤ 32 := by nlinarith
      have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ (M * b) * b / χ by positivity)
      have hm := mul_le_mul_of_nonneg_right hbM (show 0 ≤ 32 * b / χ by positivity)
      have he : μ * b / χ = χ * b := by rw [← hχ2]; field_simp
      calc
        _ = (8 * Real.sqrt 2 * (1 + ρ)) * ((M * b) * b / χ) := by ring
        _ ≤ 32 * ((M * b) * b / χ) := hh
        _ ≤ μ * b / χ := by convert hm using 1 <;> ring
        _ = _ := he

end OracleTemplate.NonlinearTemporalDiscrepancy
