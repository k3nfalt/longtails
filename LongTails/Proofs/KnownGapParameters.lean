import LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension
import LongTails.Proofs.GeneralizedSmoothTransientParameters
import LongTails.Proofs.AdaptiveTransientParameters
import LongTails.Proofs.KnownGapChainWeights
import LongTails.Proofs.KnownGapSmoothedChain
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.KnownGapParameters

open LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension
open GeneralizedSmoothTransientParameters AdaptiveTransientParameters

noncomputable def q (p : Params) : ℝ := p.L1 * p.R

noncomputable def ℓ (p : Params) : ℝ := Real.log (2 + q p)

noncomputable def Λ (p : Params) : ℝ := Real.log (p.Δ / p.ε)

noncomputable def Λ' (p : Params) : ℝ := min (Λ p / 4) (Real.sqrt (q p) / 8)

noncomputable def X (p : Params) : ℝ := min ((q p * Λ p) ^ (2 / 3 : ℝ)) (q p) / (2048 * ℓ p)

noncomputable def links (p : Params) : ℕ := ⌊X p⌋₊ + 1

noncomputable def ratio (p : Params) (m : ℕ) : ℝ := Λ' p / m

noncomputable def degree (p : Params) : ℕ := ⌈16 * Real.sqrt (q p)⌉₊

noncomputable def width (p : Params) : ℝ := 131072 * p.R

section

variable (p : Params) (hp : spec.valid p)

include hp

lemma L0_pos : 0 < p.L0 := hp.1
lemma L1_pos : 0 < p.L1 := hp.2.1
lemma R_pos : 0 < p.R := hp.2.2.1
lemma ε_pos : 0 < p.ε := hp.2.2.2.1
lemma accuracy_le : 16 * p.ε ≤ p.L0 * p.R ^ 2 := hp.2.2.2.2.1
lemma q_ge : 1048576 ≤ q p := hp.2.2.2.2.2.1
lemma gap_ge : p.ε * (2 + q p) ^ 2 ≤ p.Δ := hp.2.2.2.2.2.2.1
lemma accuracy_gap_ge : p.ε * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) ≤ p.Δ := hp.2.2.2.2.2.2.2.1
lemma full_dim_ge : ⌈70368744177664 * (1 + q p + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) ^ 6⌉₊ ≤ p.d :=
  hp.2.2.2.2.2.2.2.2

lemma dim_ge : ⌈70368744177664 * (1 + q p) ^ 6⌉₊ ≤ p.d := by
  refine le_trans (Nat.ceil_mono ?_) (full_dim_ge p hp)
  have hq : 0 ≤ q p := by have := q_ge p hp; linarith
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)]) 6

lemma q_pos : 0 < q p := by have := q_ge p hp; linarith

lemma Δ_pos : 0 < p.Δ := by
  have h1 := gap_ge p hp
  have h2 : 0 < p.ε * (2 + q p) ^ 2 := by
    have := ε_pos p hp; have := q_pos p hp
    positivity
  linarith

lemma ℓ_pos : 0 < ℓ p := log_pos _ (q_ge p hp)
lemma ℓ_ge_one : 1 ≤ ℓ p := log_one_le _ (q_ge p hp)
lemma ℓ_le : ℓ p ≤ q p / 32768 := log_upper_linear _ (q_ge p hp)

lemma ℓ_ge_four : 4 ≤ ℓ p := by
  unfold ℓ
  have hq := q_ge p hp
  have h1 : Real.exp 4 ≤ 2 + q p := by
    have he : Real.exp 4 ≤ 55 := by
      have h3 := Real.exp_one_lt_d9
      have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h4]
      have : Real.exp 1 ≤ 2.7182818286 := h3.le
      have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := by gcongr
        _ ≤ 55 := by norm_num
    linarith
  have := Real.log_le_log (Real.exp_pos 4) h1
  rwa [Real.log_exp] at this

lemma Λ_ge : 2 * ℓ p ≤ Λ p := by
  have hε := ε_pos p hp
  have hg := gap_ge p hp
  have hq := q_pos p hp
  have h1 : (2 + q p) ^ 2 ≤ p.Δ / p.ε := by
    rw [le_div_iff₀ hε, mul_comm]
    exact hg
  have h2 := Real.log_le_log (by positivity) h1
  unfold Λ ℓ
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

lemma Λ_pos : 0 < Λ p := by have := Λ_ge p hp; have := ℓ_pos p hp; linarith

lemma sqrt_q_ge : 1024 ≤ Real.sqrt (q p) := by
  have hq := q_ge p hp
  have : Real.sqrt (1048576 : ℝ) = 1024 := by
    rw [show (1048576 : ℝ) = 1024 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← this]
  exact Real.sqrt_le_sqrt hq

lemma Λ'_ge_one : 1 ≤ Λ' p := by
  unfold Λ'
  have h1 := Λ_ge p hp
  have h2 := ℓ_ge_four p hp
  have h3 := sqrt_q_ge p hp
  apply le_min <;> linarith

lemma Λ'_pos : 0 < Λ' p := by have := Λ'_ge_one p hp; linarith

omit hp in
lemma Λ'_le_Λ : Λ' p ≤ Λ p / 4 := min_le_left _ _

omit hp in
lemma Λ'_le_sqrt : Λ' p ≤ Real.sqrt (q p) / 8 := min_le_right _ _

lemma X_nonneg : 0 ≤ X p := by
  unfold X
  have := ℓ_pos p hp
  have := q_pos p hp
  have := Λ_pos p hp
  have : 0 ≤ (q p * Λ p) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by positivity) _
  positivity

lemma X_le_q : X p ≤ q p / 2048 := by
  unfold X
  have hl := ℓ_ge_one p hp
  have hq := q_pos p hp
  calc min ((q p * Λ p) ^ (2 / 3 : ℝ)) (q p) / (2048 * ℓ p) ≤ q p / (2048 * ℓ p) := by
        gcongr; exact min_le_right _ _
    _ ≤ q p / 2048 := by
        apply div_le_div_of_nonneg_left hq.le (by norm_num)
        nlinarith

lemma links_le_q : (links p : ℝ) ≤ q p := by
  unfold links
  push_cast
  have h1 := Nat.floor_le (X_nonneg p hp)
  have h2 := X_le_q p hp
  have hq := q_ge p hp
  linarith

omit hp in
lemma links_pos : 0 < links p := by unfold links; omega

lemma links_real : (links p : ℝ) ≤ X p + 1 := by
  unfold links
  push_cast
  linarith [Nat.floor_le (X_nonneg p hp)]

lemma degree_valid : 2 ≤ degree p :=
  degree_ge_two _ (by have := q_ge p hp; linarith)

lemma width_pos : 0 < width p := by
  have := R_pos p hp
  unfold width
  positivity

lemma width_radius : p.R ≤ width p := by
  have := R_pos p hp
  unfold width
  linarith

lemma width_valid : 256 * ((degree p : ℝ) * (degree p + 1 : ℕ)) ≤ p.L1 * width p := by
  have hq : 1 ≤ q p := by have := q_ge p hp; linarith
  have hh := degree_product _ hq
  change (degree p : ℝ) * (degree p + 1 : ℕ) ≤ 306 * q p at hh
  unfold q at hh
  unfold width
  nlinarith only [hh, hq]

end

lemma rpow_two_thirds_cube (x : ℝ) (hx : 0 ≤ x) : ((x ^ (2 / 3 : ℝ)) ^ 3) = x ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

section

variable (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m) (hmM : m ≤ links p)

include hp hm hmM

omit hm in
lemma m_le_q : (m : ℝ) ≤ q p :=
  (show (m : ℝ) ≤ links p by exact_mod_cast hmM).trans (links_le_q p hp)

omit hm in
lemma m_le_X : (m : ℝ) ≤ X p + 1 :=
  (show (m : ℝ) ≤ links p by exact_mod_cast hmM).trans (links_real p hp)

omit hmM in
lemma ratio_pos : 0 < ratio p m := by
  unfold ratio
  have := Λ'_pos p hp
  have : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

omit hp hmM in
lemma total_ratio : (m : ℝ) * ratio p m = Λ' p := by
  unfold ratio
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp

omit hmM in
lemma total_ratio_pred : ((m : ℝ) - 1) * ratio p m ≤ Λ' p := by
  rw [← total_ratio p m hm]
  have := ratio_pos p hp m hm
  nlinarith

omit hmM in
lemma inv_ratio : 1 / ratio p m = (m : ℝ) / Λ' p := by
  unfold ratio
  have := Λ'_pos p hp
  have : (0 : ℝ) < m := by exact_mod_cast hm
  field_simp

omit hm in
lemma log_sqrt_le : Real.log (1 + Real.sqrt m) ≤ ℓ p :=
  sqrt_links_log_bound m _ (q_ge p hp) (m_le_q p hp m hmM)

omit hm hmM in
lemma scaled_log_le : Real.log (1 + 2 * p.ε * (p.L1 / 4) ^ 2 / (p.L0 / 4)) ≤ 2 * ℓ p :=
  scaled_accuracy_log_bound p.L0 p.L1 p.R p.ε (L0_pos p hp) (L1_pos p hp) (R_pos p hp)
    (ε_pos p hp) (by have := accuracy_le p hp; linarith)

lemma m_le_X_twice : (m : ℝ) ≤ 2 * X p ∨ m = 1 := by
  by_cases hX : 1 ≤ X p
  · left; linarith [m_le_X p hp m hmM]
  · right
    have h1 : (m : ℝ) ≤ X p + 1 := m_le_X p hp m hmM
    have h2 : (m : ℝ) < 2 := by linarith
    have h3 : m < 2 := by exact_mod_cast h2
    omega

omit hm in
lemma sqrt_m_bound : Real.sqrt m ≤ Real.sqrt (q p / (1024 * ℓ p)) := by
  apply Real.sqrt_le_sqrt
  have h1 := m_le_X p hp m hmM
  have h2 := X_le_q p hp
  have hl := ℓ_ge_one p hp
  have hlq := ℓ_le p hp
  have hq := q_pos p hp
  have hX : X p ≤ q p / (2048 * ℓ p) := by
    unfold X
    gcongr
    exact min_le_right _ _
  have hone : (1 : ℝ) ≤ q p / (2048 * ℓ p) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have : q p / (1024 * ℓ p) = 2 * (q p / (2048 * ℓ p)) := by ring
  linarith

-- Term A: √m * (8ℓ + 2) ≤ q / 64
omit hm in
lemma termA : Real.sqrt m * (8 * ℓ p + 2) ≤ q p / 64 := by
  have hl := ℓ_ge_one p hp
  have hlq := ℓ_le p hp
  have hq := q_pos p hp
  have hs := sqrt_m_bound p hp m hmM
  have hpos : 0 ≤ Real.sqrt (q p / (1024 * ℓ p)) := Real.sqrt_nonneg _
  have h1 : Real.sqrt m * (8 * ℓ p + 2) ≤ Real.sqrt (q p / (1024 * ℓ p)) * (10 * ℓ p) :=
    mul_le_mul hs (by linarith) (by positivity) hpos
  apply h1.trans
  -- (√(q/(1024ℓ)) * 10ℓ)^2 = q*100ℓ/1024 ≤ (q/64)^2 ⇔ 100ℓ·4096 ≤ 1024 q ⇔ 400ℓ ≤ q
  have hsq : (Real.sqrt (q p / (1024 * ℓ p)) * (10 * ℓ p)) ^ 2 ≤ (q p / 64) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have : q p / (1024 * ℓ p) * (10 * ℓ p) ^ 2 = q p * ℓ p * (100 / 1024) := by
      field_simp; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hlq hq.le]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq

omit hm in
lemma termB : 2 * Real.sqrt m * Λ' p ≤ q p / 64 := by
  have hl := ℓ_ge_one p hp
  have hq := q_pos p hp
  have hs := sqrt_m_bound p hp m hmM
  have hs2 : Real.sqrt (q p / (1024 * ℓ p)) ≤ Real.sqrt (q p) / 32 := by
    rw [show Real.sqrt (q p) / 32 = Real.sqrt (q p / 1024) by
      rw [Real.sqrt_div hq.le, show (1024 : ℝ) = 32 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left hq.le (by norm_num)
    nlinarith
  have hΛ := Λ'_le_sqrt p
  have hΛ0 := (Λ'_pos p hp).le
  have hsq := Real.sq_sqrt hq.le
  have hsn := Real.sqrt_nonneg (q p)
  calc 2 * Real.sqrt m * Λ' p ≤ 2 * (Real.sqrt (q p) / 32) * (Real.sqrt (q p) / 8) := by
        gcongr
        exact hs.trans hs2
    _ = q p / 128 := by
        have : 2 * (Real.sqrt (q p) / 32) * (Real.sqrt (q p) / 8) = Real.sqrt (q p) ^ 2 / 128 := by ring
        rw [this, hsq]
    _ ≤ q p / 64 := by linarith

lemma termC : 4 * ℓ p * ((m : ℝ) * Real.sqrt m) / Λ' p ≤ q p / 32 := by
  have hl := ℓ_ge_one p hp
  have hlq := ℓ_le p hp
  have hq := q_pos p hp
  have hΛ' := Λ'_pos p hp
  have hΛ'1 := Λ'_ge_one p hp
  have hΛ := Λ_pos p hp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- reduce to the squared inequality 16384 ℓ² m³ ≤ q² Λ'²
  have key : 16384 * ℓ p ^ 2 * (m : ℝ) ^ 3 ≤ q p ^ 2 * Λ' p ^ 2 := by
    rcases m_le_X_twice p hp m hm hmM with hX | hone
    · have hX0 := X_nonneg p hp
      have hm3 : (m : ℝ) ^ 3 ≤ 8 * X p ^ 3 := by
        have : (m : ℝ) ^ 3 ≤ (2 * X p) ^ 3 := pow_le_pow_left₀ hm0.le hX 3
        linarith
      rcases le_total (Λ p / 4) (Real.sqrt (q p) / 8) with hcase | hcase
      · have hΛ'eq : Λ' p = Λ p / 4 := min_eq_left hcase
        have hXle : X p ≤ (q p * Λ p) ^ (2 / 3 : ℝ) / (2048 * ℓ p) := by
          unfold X; gcongr; exact min_le_left _ _
        have hX3 : X p ^ 3 ≤ (q p * Λ p) ^ 2 / (2048 * ℓ p) ^ 3 := by
          have := pow_le_pow_left₀ hX0 hXle 3
          rwa [div_pow, rpow_two_thirds_cube _ (by positivity)] at this
        rw [hΛ'eq]
        have hm3' : (m : ℝ) ^ 3 ≤ 8 * ((q p * Λ p) ^ 2 / (2048 * ℓ p) ^ 3) :=
          hm3.trans (mul_le_mul_of_nonneg_left hX3 (by norm_num))
        have h1 : 16384 * ℓ p ^ 2 * (m : ℝ) ^ 3 ≤
            16384 * ℓ p ^ 2 * (8 * ((q p * Λ p) ^ 2 / (2048 * ℓ p) ^ 3)) :=
          mul_le_mul_of_nonneg_left hm3' (by positivity)
        apply h1.trans
        rw [show (2048 * ℓ p) ^ 3 = 2048 ^ 3 * ℓ p ^ 3 by ring]
        rw [show 16384 * ℓ p ^ 2 * (8 * ((q p * Λ p) ^ 2 / (2048 ^ 3 * ℓ p ^ 3))) =
          (q p * Λ p) ^ 2 * (131072 / (2048 ^ 3 * ℓ p)) by field_simp; ring]
        have : (131072 : ℝ) / (2048 ^ 3 * ℓ p) ≤ 1 / 16 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        calc (q p * Λ p) ^ 2 * (131072 / (2048 ^ 3 * ℓ p)) ≤ (q p * Λ p) ^ 2 * (1 / 16) := by
              gcongr
          _ = q p ^ 2 * (Λ p / 4) ^ 2 := by ring
      · have hΛ'eq : Λ' p = Real.sqrt (q p) / 8 := min_eq_right hcase
        have hXle : X p ≤ q p / (2048 * ℓ p) := by
          unfold X; gcongr; exact min_le_right _ _
        have hX3 : X p ^ 3 ≤ q p ^ 3 / (2048 * ℓ p) ^ 3 := by
          have := pow_le_pow_left₀ hX0 hXle 3
          rwa [div_pow] at this
        rw [hΛ'eq]
        have hm3' : (m : ℝ) ^ 3 ≤ 8 * (q p ^ 3 / (2048 * ℓ p) ^ 3) :=
          hm3.trans (mul_le_mul_of_nonneg_left hX3 (by norm_num))
        have h1 : 16384 * ℓ p ^ 2 * (m : ℝ) ^ 3 ≤
            16384 * ℓ p ^ 2 * (8 * (q p ^ 3 / (2048 * ℓ p) ^ 3)) :=
          mul_le_mul_of_nonneg_left hm3' (by positivity)
        apply h1.trans
        rw [show (2048 * ℓ p) ^ 3 = 2048 ^ 3 * ℓ p ^ 3 by ring]
        rw [show 16384 * ℓ p ^ 2 * (8 * (q p ^ 3 / (2048 ^ 3 * ℓ p ^ 3))) =
          q p ^ 3 * (131072 / (2048 ^ 3 * ℓ p)) by field_simp; ring]
        have hsq := Real.sq_sqrt hq.le
        have : (131072 : ℝ) / (2048 ^ 3 * ℓ p) ≤ 1 / 64 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        calc q p ^ 3 * (131072 / (2048 ^ 3 * ℓ p)) ≤ q p ^ 3 * (1 / 64) := by gcongr
          _ = q p ^ 2 * (Real.sqrt (q p) / 8) ^ 2 := by rw [div_pow, hsq]; ring
    · subst hone
      simp only [Nat.cast_one, one_pow, mul_one]
      have h1 : 16384 * ℓ p ^ 2 ≤ q p ^ 2 := by
        have : ℓ p ^ 2 ≤ (q p / 32768) ^ 2 := pow_le_pow_left₀ (by linarith) hlq 2
        nlinarith
      have h2 : q p ^ 2 ≤ q p ^ 2 * Λ' p ^ 2 := by
        have : 1 ≤ Λ' p ^ 2 := by nlinarith
        nlinarith
      linarith
  have hsqrt := Real.sq_sqrt hm0.le
  have hlhs0 : 0 ≤ 4 * ℓ p * ((m : ℝ) * Real.sqrt m) / Λ' p := by positivity
  have hsq : (4 * ℓ p * ((m : ℝ) * Real.sqrt m) / Λ' p) ^ 2 ≤ (q p / 32) ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have : (4 * ℓ p * ((m : ℝ) * Real.sqrt m)) ^ 2 = 16 * ℓ p ^ 2 * (m : ℝ) ^ 3 := by
      rw [mul_pow, mul_pow, mul_pow, hsqrt]
      ring
    rw [this]
    have he : (q p / 32) ^ 2 * Λ' p ^ 2 = q p ^ 2 * Λ' p ^ 2 / 1024 := by ring
    rw [he]
    linarith
  exact (pow_le_pow_iff_left₀ hlhs0 (by positivity) two_ne_zero).mp hsq

noncomputable def bracket (p : Params) (m : ℕ) : ℝ :=
  2 * (Real.log (1 + p.L1 / 4 * KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio p m) /
    (p.L0 / 4)) / (p.L1 / 4)) + 2 / (p.L1 / 4) +
    (4 / (p.L1 / 4) * Real.log (1 + Real.sqrt m)) * (1 + 1 / ratio p m)

lemma bracket_bound : Real.sqrt m * (p.L1 / 4 * bracket p m) ≤ q p / 16 := by
  have hL1 := L1_pos p hp
  have hl := ℓ_ge_one p hp
  have hlog := KnownGapChainWeights.peak_log_bound hm (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
    (by have := L0_pos p hp; positivity) (by positivity) (ε_pos p hp) (ratio_pos p hp m hm).le
  have hsl := scaled_log_le p hp
  have htot := total_ratio_pred p hp m hm
  have hls := log_sqrt_le p hp m hmM
  have hinv := inv_ratio p hp m hm
  have hA := termA p hp m hmM
  have hB := termB p hp m hmM
  have hC := termC p hp m hm hmM
  have hsm : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hΛ' := Λ'_pos p hp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hbr : p.L1 / 4 * bracket p m ≤ 8 * ℓ p + 2 + 2 * Λ' p + 4 * ℓ p * ((m : ℝ) / Λ' p) := by
    unfold bracket
    rw [hinv]
    have hlogle : Real.log (1 + p.L1 / 4 * KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio p m) /
        (p.L0 / 4)) ≤ 2 * ℓ p + Λ' p := by linarith
    have hl0 : 0 ≤ Real.log (1 + Real.sqrt m) :=
      Real.log_nonneg (by linarith [Real.sqrt_nonneg (m : ℝ)])
    have hmΛ : 0 ≤ (m : ℝ) / Λ' p := by positivity
    have he : p.L1 / 4 * (2 * (Real.log (1 + p.L1 / 4 * KnownGapChainWeights.peak m (p.L1 / 4) p.ε
        (ratio p m) / (p.L0 / 4)) / (p.L1 / 4)) + 2 / (p.L1 / 4) +
        4 / (p.L1 / 4) * Real.log (1 + Real.sqrt m) * (1 + (m : ℝ) / Λ' p)) =
        2 * Real.log (1 + p.L1 / 4 * KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio p m) /
          (p.L0 / 4)) + 2 + 4 * Real.log (1 + Real.sqrt m) * (1 + (m : ℝ) / Λ' p) := by
      field_simp
    rw [he]
    have h3 : 4 * Real.log (1 + Real.sqrt m) * (1 + (m : ℝ) / Λ' p) ≤
        4 * ℓ p * (1 + (m : ℝ) / Λ' p) := by gcongr
    nlinarith
  have hfin : Real.sqrt m * (8 * ℓ p + 2 + 2 * Λ' p + 4 * ℓ p * ((m : ℝ) / Λ' p)) ≤ q p / 16 := by
    have he : Real.sqrt m * (8 * ℓ p + 2 + 2 * Λ' p + 4 * ℓ p * ((m : ℝ) / Λ' p)) =
        Real.sqrt m * (8 * ℓ p + 2) + 2 * Real.sqrt m * Λ' p +
          4 * ℓ p * ((m : ℝ) * Real.sqrt m) / Λ' p := by
      field_simp
    rw [he]
    linarith
  calc Real.sqrt m * (p.L1 / 4 * bracket p m) ≤
      Real.sqrt m * (8 * ℓ p + 2 + 2 * Λ' p + 4 * ℓ p * ((m : ℝ) / Λ' p)) := by gcongr
    _ ≤ q p / 16 := hfin

lemma bracket_single : p.L1 / 4 * bracket p m ≤ q p / 16 := by
  have h := bracket_bound p hp m hm hmM
  have hs : 1 ≤ Real.sqrt m := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ m by exact_mod_cast hm)
    simpa using this
  have hbr0 : 0 ≤ p.L1 / 4 * bracket p m := by
    have hL1 := L1_pos p hp
    have := KnownGapChainWeights.shiftCoordinate_bounds (m := m) (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
      (by have := L0_pos p hp; positivity) (by positivity) (ε_pos p hp) (ratio_pos p hp m hm)
      ⟨0, hm⟩
    have hb : 0 ≤ bracket p m := (this.1).trans this.2
    positivity
  nlinarith

lemma shift_norm_le :
    ‖GeneralizedSmoothHardTransfer.shift (p.L0 / 4) (p.L1 / 4)
      (KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio p m))
      (KnownGapChainWeights.weight m (p.L1 / 4) p.ε (ratio p m))‖ ≤ p.R / 4 := by
  have hL1 := L1_pos p hp
  have h := KnownGapChainWeights.shift_norm_bound hm (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
    (by have := L0_pos p hp; positivity) (by positivity) (ε_pos p hp) (ratio_pos p hp m hm)
  have hb := bracket_bound p hp m hm hmM
  change _ ≤ Real.sqrt m * bracket p m at h
  have hq : q p = p.L1 * p.R := rfl
  apply h.trans
  have : Real.sqrt m * bracket p m = (Real.sqrt m * (p.L1 / 4 * bracket p m)) / (p.L1 / 4) := by
    field_simp
  rw [this, div_le_iff₀ (by positivity)]
  rw [hq] at hb
  nlinarith

lemma shiftCoordinate_le (i : Fin m) :
    GeneralizedSmoothHardTransfer.shiftCoordinate (p.L0 / 4) (p.L1 / 4)
      (KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio p m))
      (KnownGapChainWeights.weight m (p.L1 / 4) p.ε (ratio p m)) i ≤ q p / (4 * p.L1) := by
  have hL1 := L1_pos p hp
  have h := (KnownGapChainWeights.shiftCoordinate_bounds (m := m) (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
    (by have := L0_pos p hp; positivity) (by positivity) (ε_pos p hp) (ratio_pos p hp m hm) i).2
  have hb := bracket_single p hp m hm hmM
  change _ ≤ bracket p m at h
  apply h.trans
  rw [le_div_iff₀ (by positivity)]
  nlinarith

omit hmM in
lemma peak_small :
    KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio p m) * (1 / 2 : ℝ) ^ degree p * p.L1 ≤ p.L0 := by
  have hL0 := L0_pos p hp
  have hL1 := L1_pos p hp
  have hε := ε_pos p hp
  have hR := R_pos p hp
  have hq1 : 1 ≤ q p := by have := q_ge p hp; linarith
  have hexp : Real.exp (((m : ℝ) - 1) * ratio p m) ≤ Real.exp (Real.sqrt (q p)) := by
    apply Real.exp_le_exp.mpr
    have h1 := total_ratio_pred p hp m hm
    have h2 := Λ'_le_sqrt p
    have h3 := Real.sqrt_nonneg (q p)
    linarith
  have hcoef : p.ε * p.L1 ^ 2 / 2 ≤ p.L0 * q p ^ 2 / 32 := by
    have hh := mul_le_mul_of_nonneg_right (accuracy_le p hp) (sq_nonneg p.L1)
    unfold q
    nlinarith
  have hsup := exponential_suppression (q p) hq1
  unfold KnownGapChainWeights.peak degree
  have he : 2 * p.ε * (p.L1 / 4) * Real.exp (((m : ℝ) - 1) * ratio p m) * (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ * p.L1 =
      (p.ε * p.L1 ^ 2 / 2) * Real.exp (((m : ℝ) - 1) * ratio p m) * (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ := by ring
  rw [he]
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ := by positivity
  have h1 : (p.ε * p.L1 ^ 2 / 2) * Real.exp (((m : ℝ) - 1) * ratio p m) ≤
      p.L0 * q p ^ 2 / 32 * Real.exp (Real.sqrt (q p)) :=
    mul_le_mul hcoef hexp (Real.exp_pos _).le (by positivity)
  have h2 : p.L0 * q p ^ 2 / 32 * Real.exp (Real.sqrt (q p)) * (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ ≤
      p.L0 / 32 := by
    have hh := mul_le_mul_of_nonneg_left hsup (show 0 ≤ p.L0 / 32 by positivity)
    have hinv : (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ = 1 / (2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ := by
      rw [one_div_pow]
    rw [hinv, mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc (p.ε * p.L1 ^ 2 / 2) * Real.exp (((m : ℝ) - 1) * ratio p m) * (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊
      ≤ p.L0 * q p ^ 2 / 32 * Real.exp (Real.sqrt (q p)) * (1 / 2 : ℝ) ^ ⌈16 * Real.sqrt (q p)⌉₊ := by
        gcongr
    _ ≤ p.L0 / 32 := h2
    _ ≤ p.L0 := by linarith

omit hmM in
lemma gap_bound :
    KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio p m) * ((q p + 1) / (4 * p.L1)) ≤ p.Δ := by
  have hL1 := L1_pos p hp
  have hε := ε_pos p hp
  have hq := q_pos p hp
  have hΔ := Δ_pos p hp
  set y := p.Δ / p.ε with hy
  have hy1 : (2 + q p) ^ 2 ≤ y := by
    have hg := gap_ge p hp
    rw [hy, le_div_iff₀ hε, mul_comm]
    exact hg
  have hypos : 0 < y := by rw [hy]; positivity
  have hexp : Real.exp (((m : ℝ) - 1) * ratio p m) ≤ y ^ (1 / 4 : ℝ) := by
    have h1 := total_ratio_pred p hp m hm
    have h2 := Λ'_le_Λ p
    have h3 : Real.exp (Λ p / 4) = y ^ (1 / 4 : ℝ) := by
      rw [Real.rpow_def_of_pos hypos]
      unfold Λ
      congr 1
      ring
    rw [← h3]
    exact Real.exp_le_exp.mpr (by linarith)
  have hthree : q p + 1 ≤ y ^ (3 / 4 : ℝ) := by
    have h1 : ((2 + q p) ^ 2) ^ (3 / 4 : ℝ) ≤ y ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hy1 (by norm_num)
    have h2 : ((2 + q p) ^ 2) ^ (3 / 4 : ℝ) = (2 + q p) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have h3 : (2 + q p) ^ (1 : ℝ) ≤ (2 + q p) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_one] at h3
    rw [h2] at h1
    linarith
  have hprod : y ^ (1 / 4 : ℝ) * y ^ (3 / 4 : ℝ) = y := by
    rw [← Real.rpow_add hypos]; norm_num
  have hpk : KnownGapChainWeights.peak m (p.L1 / 4) p.ε (ratio p m) * ((q p + 1) / (4 * p.L1)) =
      p.ε / 8 * (Real.exp (((m : ℝ) - 1) * ratio p m) * (q p + 1)) := by
    unfold KnownGapChainWeights.peak
    field_simp
    ring
  rw [hpk]
  have hy14 : 0 ≤ y ^ (1 / 4 : ℝ) := by positivity
  have hq1 : 0 ≤ q p + 1 := by linarith
  calc p.ε / 8 * (Real.exp (((m : ℝ) - 1) * ratio p m) * (q p + 1))
      ≤ p.ε / 8 * (y ^ (1 / 4 : ℝ) * y ^ (3 / 4 : ℝ)) := by
        gcongr
    _ = p.ε / 8 * y := by rw [hprod]
    _ = p.Δ / 8 := by
        have hy' : y * p.ε = p.Δ := by rw [hy]; exact div_mul_cancel₀ _ hε.ne'
        linear_combination (1 / 8 : ℝ) * hy'
    _ ≤ p.Δ := by linarith

omit hp hm hmM in
lemma threshold_eq : KnownGapSmoothedChain.threshold (p.L1 / 4) (ratio p m) =
    min (ratio p m) 1 / (4 * p.L1) := by
  unfold KnownGapSmoothedChain.threshold KnownGapChainWeights.margin
  rw [div_div]
  congr 1
  ring

omit hmM in
lemma threshold_lower : 1 / (4 * p.L1 * m) ≤ KnownGapSmoothedChain.threshold (p.L1 / 4) (ratio p m) := by
  rw [threshold_eq p m]
  have hL1 := L1_pos p hp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : 1 / (m : ℝ) ≤ ratio p m := by
    unfold ratio
    rw [div_le_div_iff_of_pos_right hm0]
    exact Λ'_ge_one p hp
  have hmin : 1 / (m : ℝ) ≤ min (ratio p m) 1 := by
    apply le_min hr
    rw [div_le_one hm0]; exact hm1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 4 * p.L1 by positivity)
  have he : 1 * (4 * p.L1) = 4 * p.L1 * m * (1 / (m : ℝ)) := by field_simp
  rw [he]
  nlinarith

lemma dimension_sufficient :
    (m : ℝ) + 2 * (m : ℝ) ^ 2 * ((4 * width p) ^ 2 /
      KnownGapSmoothedChain.threshold (p.L1 / 4) (ratio p m) ^ 2) ≤ p.d := by
  have hL1 := L1_pos p hp
  have hR := R_pos p hp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hθ := threshold_lower p hp m hm
  have hθ0 : 0 < 1 / (4 * p.L1 * m) := by positivity
  have hmq := m_le_q p hp m hmM
  have hq1 : 1 ≤ q p := by have := q_ge p hp; linarith
  have hratio : (4 * width p) ^ 2 / KnownGapSmoothedChain.threshold (p.L1 / 4) (ratio p m) ^ 2 ≤
      (4 * width p) ^ 2 / (1 / (4 * p.L1 * m)) ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hθ0.le hθ 2
  have hval : (4 * width p) ^ 2 / (1 / (4 * p.L1 * m)) ^ 2 = 4398046511104 * q p ^ 2 * (m : ℝ) ^ 2 := by
    unfold width q
    field_simp
    ring
  rw [hval] at hratio
  have hd : (⌈70368744177664 * (1 + q p) ^ 6⌉₊ : ℝ) ≤ p.d := by exact_mod_cast dim_ge p hp
  have hceil := Nat.le_ceil (70368744177664 * (1 + q p) ^ 6)
  have hm4 : (m : ℝ) ^ 4 ≤ q p ^ 4 := pow_le_pow_left₀ hm0.le hmq 4
  have hq6 : q p ^ 6 ≤ (1 + q p) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
  have hq0 : q p ≤ (1 + q p) ^ 6 := by
    calc q p ≤ 1 + q p := by linarith
      _ ≤ (1 + q p) ^ 6 := by
        simpa using pow_le_pow_right₀ (show 1 ≤ 1 + q p by linarith) (show 1 ≤ 6 by norm_num)
  have h1 : 2 * (m : ℝ) ^ 2 * (4398046511104 * q p ^ 2 * (m : ℝ) ^ 2) ≤
      8796093022208 * q p ^ 6 := by
    have : (m : ℝ) ^ 2 * (m : ℝ) ^ 2 = (m : ℝ) ^ 4 := by ring
    nlinarith [pow_nonneg hm0.le 2, pow_nonneg (q_pos p hp).le 2]
  have h2 : 2 * (m : ℝ) ^ 2 * ((4 * width p) ^ 2 /
      KnownGapSmoothedChain.threshold (p.L1 / 4) (ratio p m) ^ 2) ≤
      2 * (m : ℝ) ^ 2 * (4398046511104 * q p ^ 2 * (m : ℝ) ^ 2) := by gcongr
  have h3 : (m : ℝ) + 8796093022208 * q p ^ 6 ≤ 70368744177664 * (1 + q p) ^ 6 := by
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 + q p by linarith) 6]
  linarith

end

noncomputable def witness : Params :=
  { d := ⌈70368744177664 * (1 + (2 : ℝ) ^ 30 + 2 ^ 30) ^ 6⌉₊, L0 := 1, L1 := 1, x0 := 0, R := 2 ^ 30,
    Δ := Real.exp 4096, ε := 1 }

lemma witness_sqrt : Real.sqrt (1 * ((2 : ℝ) ^ 30) ^ 2 / 1) = 2 ^ 30 := by
  rw [one_mul, div_one, Real.sqrt_sq (by positivity)]

lemma witness_exp : (2 : ℝ) ^ 122 ≤ Real.exp 4096 := by
  have hl : Real.log ((2 : ℝ) ^ 122) ≤ 4096 := by
    rw [Real.log_pow]
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have := Real.exp_le_exp.mpr hl
  rwa [Real.exp_log (by positivity)] at this

lemma witness_valid : spec.valid witness := by
  refine ⟨by norm_num [witness], by norm_num [witness], by norm_num [witness], by norm_num [witness],
    by norm_num [witness], by norm_num [witness], ?_, ?_, ?_⟩
  · show (1 : ℝ) * (2 + 1 * 2 ^ 30) ^ 2 ≤ Real.exp 4096
    have h1 : (1 : ℝ) * (2 + 1 * 2 ^ 30) ^ 2 ≤ (2 : ℝ) ^ 122 := by norm_num
    linarith [witness_exp]
  · show (1 : ℝ) * Real.sqrt (1 * ((2 : ℝ) ^ 30) ^ 2 / 1) ≤ Real.exp 4096
    rw [witness_sqrt]
    have h1 : (1 : ℝ) * 2 ^ 30 ≤ (2 : ℝ) ^ 122 := by norm_num
    linarith [witness_exp]
  · show ⌈70368744177664 * (1 + 1 * (2 : ℝ) ^ 30 + Real.sqrt (1 * ((2 : ℝ) ^ 30) ^ 2 / 1)) ^ 6⌉₊ ≤
      ⌈70368744177664 * (1 + (2 : ℝ) ^ 30 + 2 ^ 30) ^ 6⌉₊
    rw [witness_sqrt, one_mul]

lemma valid_nonempty : ∃ p : Params, spec.valid p := ⟨witness, witness_valid⟩

lemma witness_interpolation : Λ witness / 4 ≤ Real.sqrt (q witness) / 8 := by
  simp only [Λ, q, witness, div_one, Real.log_exp, one_mul]
  have : Real.sqrt ((2 : ℝ) ^ 30) = 2 ^ 15 := by
    rw [show ((2 : ℝ) ^ 30) = (2 ^ 15) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]
  rw [this]
  norm_num

lemma witness_budget : 4096 ≤ X witness := by
  simp only [X, ℓ, Λ, q, witness, div_one, Real.log_exp, one_mul]
  have hpow : ((2 : ℝ) ^ 30 * 4096) ^ (2 / 3 : ℝ) = 2 ^ 28 := by
    rw [show (2 : ℝ) ^ 30 * 4096 = (2 : ℝ) ^ (42 : ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [hpow, min_eq_left (by norm_num)]
  have hlog : Real.log (2 + (2 : ℝ) ^ 30) ≤ 32 := by
    have h1 : (2 : ℝ) + 2 ^ 30 ≤ 2 ^ 31 := by norm_num
    have h2 := Real.log_le_log (by norm_num) h1
    rw [Real.log_pow] at h2
    have := Real.log_two_lt_d9
    norm_num at this h2 ⊢
    linarith
  have hlogpos : 0 < Real.log (2 + (2 : ℝ) ^ 30) := Real.log_pos (by norm_num)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

end LongTails.Proofs.KnownGapParameters
