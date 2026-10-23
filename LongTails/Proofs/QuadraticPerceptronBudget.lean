import LongTails.Proofs.QuadraticPerceptronStopping
import Mathlib.Analysis.SpecialFunctions.Exp

namespace LongTails.Proofs.QuadraticPerceptronCone

lemma log_one_add_ge {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1) : m / 2 ≤ Real.log (1 + m) := by
  have hl := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + m by linarith)
  have he : 1 - (1 + m)⁻¹ = m / (1 + m) := by field_simp; ring
  have : m / 2 ≤ m / (1 + m) := div_le_div_of_nonneg_left h0 (by linarith) (by linarith)
  linarith

lemma exp_le_one_add_pow {m : ℝ} (h0 : 0 ≤ m) (h1 : m ≤ 1) (n : ℕ) :
    Real.exp (n * (m / 2)) ≤ (1 + m) ^ n := by
  rw [← Real.exp_log (show 0 < 1 + m by linarith), ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (log_one_add_ge h0 h1) (Nat.cast_nonneg n))

lemma one_add_pow_le_exp {e : ℝ} (he : 0 ≤ e) (n : ℕ) : (1 + e) ^ n ≤ Real.exp (n * e) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp e]) n

lemma one_sub_pow_le_exp {x : ℝ} (h : x ≤ 1) (n : ℕ) : (1 - x) ^ n ≤ Real.exp (-(n * x)) := by
  rw [show -(n * x) = n * (-x) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-x)]) n

lemma le_of_mul_le_mul_pos {R x y : ℝ} (hR : 0 < R) (h : R * x ≤ R * y) : x ≤ y :=
  le_of_mul_le_mul_left h hR

namespace Gains

variable {g : Gains}

theorem stops_within (hg : g.Standing) {x0 : State} (ha0 : 0 < x0.a) (hb0 : 0 ≤ x0.b)
    (hZ0 : 0 < x0.Z) (hn0 : x0.n = 0) {R gain βLo βHi μ ρ aLo zLo S : ℝ}
    (hR : 0 < R) (hgain : 0 < gain) (hβLo : 0 < βLo) (hμ : 0 < μ) (hρ : 1 ≤ ρ) (haLo : 0 < aLo)
    (hzLo : 0 < zLo) (hc1 : gain / (2 * R) ≤ g.c1) (hc2 : gain / (2 * R) ≤ g.c2)
    (heLo : βLo / (2 * R) ≤ g.e) (heHi : g.e ≤ βHi / (2 * R)) (he1 : g.e ≤ 1)
    (hβR : βLo ≤ 2 * R) (hslow : (x0.A = 0 ∧ x0.B = 0) ∨ μ / (2 * R) ≤ g.m)
    (hratio : |x0.B| ≤ ρ * |x0.A|) (haL : aLo ≤ x0.a) (hzL : zLo ≤ x0.Z)
    (hS : x0.a + x0.b + 2 * x0.Z ≤ S) :
    g.Stopped (g.traj x0 ⌈24 * (R * Real.log ρ / μ + 1) * (R / gain + 1) ^ 2 *
      (3 + 2 * βHi * Real.log ρ / μ +
        Real.log (S * (1 / aLo + 8 * R ^ 3 / (βLo ^ 3 * zLo))))⌉₊) := by
  have hm0 := hg.m_nonneg
  have hm1 := hg.m_le
  have he0 := hg.e_pos
  have hcm1 : g.cm ≤ 1 := (cm_le_c1 (g := g)).trans hg.c1_le
  have hcm : gain / (2 * R) ≤ g.cm := le_min hc1 hc2
  have hcm' : gain ≤ 2 * R * g.cm := by rwa [div_le_iff₀' (by positivity)] at hcm
  have hcm0 : 0 < g.cm := lt_of_lt_of_le (by positivity) hcm
  have heHi' : 2 * R * g.e ≤ βHi := by rwa [le_div_iff₀' (by positivity)] at heHi
  have hβHi : 0 ≤ βHi := le_trans (by positivity) heHi'
  set X := Real.log ρ / μ with hXdef
  have hX : 0 ≤ X := div_nonneg (Real.log_nonneg hρ) hμ.le
  set t := βLo / (2 * R) with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by rw [div_le_one (by positivity)]; exact hβR
  set w := t ^ 3 * zLo with hwdef
  have hw0 : 0 < w := by positivity
  have hW : 8 * R ^ 3 / (βLo ^ 3 * zLo) = 1 / w := by
    rw [hwdef, htdef]; field_simp; ring
  set W := 1 / aLo + 1 / w with hWdef
  have hW0 : 0 < W := by positivity
  have hSa : aLo ≤ S := by linarith
  have hS0 : 0 < S := by linarith
  have hSW : 1 ≤ S * W := by
    have : 1 ≤ S * (1 / aLo) := by rw [mul_one_div, le_div_iff₀ haLo]; linarith
    have : 0 ≤ S * (1 / w) := by positivity
    rw [hWdef, mul_add]; linarith
  set L := Real.log (S * W) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hSW
  have hexpL : Real.exp L = S * W := Real.exp_log (by positivity)
  set Λ := 3 + 2 * βHi * X + L with hΛdef
  have hΛ : 3 ≤ Λ := by
    have : 0 ≤ 2 * βHi * X := by positivity
    linarith
  have hew : w ≤ g.e * x0.Z := by
    have h1 : t ^ 3 ≤ t := by
      calc t ^ 3 = t * t ^ 2 := by ring
        _ ≤ t * 1 := by gcongr; exact pow_le_one₀ ht0.le ht1
        _ = t := mul_one t
    exact mul_le_mul (h1.trans heLo) hzL hzLo.le he0.le
  have hew3 : w ≤ g.e ^ 3 * x0.Z :=
    mul_le_mul (pow_le_pow_left₀ ht0.le heLo 3) hzL hzLo.le (by positivity)
  set N := ⌈4 * R * X⌉₊ with hNdef
  set K := ⌈4 * (R / gain) * Λ⌉₊ with hKdef
  set J := ⌈4 * (R / gain) ^ 2 * Λ⌉₊ with hJdef
  have hN1 : (N : ℝ) < 4 * R * X + 1 := Nat.ceil_lt_add_one (by positivity)
  have hK1 : (K : ℝ) < 4 * (R / gain) * Λ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hJ1 : (J : ℝ) < 4 * (R / gain) ^ 2 * Λ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hN0 : 4 * R * X ≤ N := Nat.le_ceil _
  have hK0 : 4 * (R / gain) * Λ ≤ K := Nat.le_ceil _
  have hJ0 : 4 * (R / gain) ^ 2 * Λ ≤ J := Nat.le_ceil _
  have hg0 : gain ≠ 0 := hgain.ne'
  have hμ0 : μ ≠ 0 := hμ.ne'
  have hKcm : Λ ≤ K * (g.cm / 2) := by
    apply le_of_mul_le_mul_pos (show 0 < 4 * R by positivity)
    have h1 : 4 * R * Λ = gain * (4 * (R / gain) * Λ) := by field_simp
    have h2 : gain * (4 * (R / gain) * Λ) ≤ gain * K := mul_le_mul_of_nonneg_left hK0 hgain.le
    have h3 : gain * (K : ℝ) ≤ 2 * R * g.cm * K := mul_le_mul_of_nonneg_right hcm' (by positivity)
    linarith
  have hJcm : Λ ≤ J * g.cm ^ 2 := by
    apply le_of_mul_le_mul_pos (show 0 < 4 * R ^ 2 by positivity)
    have h1 : 4 * R ^ 2 * Λ = gain ^ 2 * (4 * (R / gain) ^ 2 * Λ) := by
      field_simp
    have h2 : gain ^ 2 * (4 * (R / gain) ^ 2 * Λ) ≤ gain ^ 2 * J :=
      mul_le_mul_of_nonneg_left hJ0 (by positivity)
    have h3 : gain ^ 2 * (J : ℝ) ≤ (2 * R * g.cm) ^ 2 * J :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hgain.le hcm' 2) (by positivity)
    linarith
  have hNe : N * g.e ≤ 2 * βHi * X + 1 := by
    have h1 : (N : ℝ) * g.e ≤ (4 * R * X + 1) * g.e := mul_le_mul_of_nonneg_right hN1.le he0.le
    have h2 : (4 * R * X + 1) * g.e = 2 * X * (2 * R * g.e) + g.e := by ring
    have h3 : 2 * X * (2 * R * g.e) ≤ 2 * X * βHi := mul_le_mul_of_nonneg_left heHi' (by positivity)
    linarith
  have hpowe : (1 + g.e) ^ N ≤ Real.exp (N * g.e) := one_add_pow_le_exp he0.le N
  have hSmax : (1 + g.e) ^ N * S ≤ Real.exp (N * g.e + L) * (1 / W) := by
    rw [Real.exp_add, hexpL]
    have hW1 : W ≠ 0 := hW0.ne'
    calc (1 + g.e) ^ N * S ≤ Real.exp (N * g.e) * S := mul_le_mul_of_nonneg_right hpowe hS0.le
      _ = Real.exp (N * g.e) * (S * W) * (1 / W) := by field_simp
  have hNeL : N * g.e + L ≤ Λ - 2 := by rw [hΛdef]; linarith
  have hN : x0.B ^ 2 ≤ (1 + g.m) ^ (2 * N) * x0.A ^ 2 := by
    rcases hslow with ⟨hA, hB⟩ | hm
    · rw [hA, hB]; simp
    · have hB2 : x0.B ^ 2 ≤ ρ ^ 2 * x0.A ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hratio 2
        rw [sq_abs, mul_pow, sq_abs] at this; exact this
      have hm' : μ ≤ 2 * R * g.m := by rwa [div_le_iff₀' (by positivity)] at hm
      have hlog : Real.log ρ ≤ N * (g.m / 2) := by
        apply le_of_mul_le_mul_pos (show 0 < 4 * R by positivity)
        have h1 : 4 * R * Real.log ρ = μ * (4 * R * X) := by rw [hXdef]; field_simp
        have h2 : μ * (4 * R * X) ≤ μ * N := mul_le_mul_of_nonneg_left hN0 hμ.le
        have h3 : μ * (N : ℝ) ≤ 2 * R * g.m * N := mul_le_mul_of_nonneg_right hm' (by positivity)
        linarith
      have hρm : ρ ≤ (1 + g.m) ^ N := by
        calc ρ = Real.exp (Real.log ρ) := (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp (N * (g.m / 2)) := Real.exp_le_exp.mpr hlog
          _ ≤ (1 + g.m) ^ N := exp_le_one_add_pow hm0 hm1 N
      have : ρ ^ 2 ≤ (1 + g.m) ^ (2 * N) := by
        rw [pow_mul', ]
        exact pow_le_pow_left₀ (by linarith) hρm 2
      exact hB2.trans (mul_le_mul_of_nonneg_right this (sq_nonneg _))
  have hα : 1 ≤ min x0.a (g.e * x0.Z) * W := by
    rcases min_cases x0.a (g.e * x0.Z) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, hWdef, mul_add]
    · have : 1 ≤ x0.a * (1 / aLo) := by rw [mul_one_div, le_div_iff₀ haLo]; linarith
      have : 0 ≤ x0.a * (1 / w) := by positivity
      linarith
    · have : 1 ≤ g.e * x0.Z * (1 / w) := by rw [mul_one_div, le_div_iff₀ hw0]; linarith
      have : 0 ≤ g.e * x0.Z * (1 / aLo) := by positivity
      linarith
  have hK : (1 + g.e) ^ N * S < min x0.a (g.e * x0.Z) * (1 + g.cm) ^ K := by
    have hαW : 1 / W ≤ min x0.a (g.e * x0.Z) := by rw [div_le_iff₀ hW0]; linarith
    have hα0 : 0 < min x0.a (g.e * x0.Z) := lt_min ha0 (by positivity)
    calc (1 + g.e) ^ N * S ≤ Real.exp (N * g.e + L) * (1 / W) := hSmax
      _ < Real.exp (K * (g.cm / 2)) * (1 / W) := by
          gcongr
          linarith
      _ ≤ (1 + g.cm) ^ K * min x0.a (g.e * x0.Z) := by
          gcongr; exact exp_le_one_add_pow hcm0.le hcm1 K
      _ = min x0.a (g.e * x0.Z) * (1 + g.cm) ^ K := mul_comm _ _
  have hJ : (1 - g.cm ^ 2) ^ J * ((1 + g.e) ^ N * S) ≤ g.e ^ 3 * x0.Z := by
    have hq : 0 ≤ 1 - g.cm ^ 2 := by linarith [pow_le_one₀ hcm0.le hcm1 (n := 2)]
    have hpow : (1 - g.cm ^ 2) ^ J ≤ Real.exp (-(J * g.cm ^ 2)) :=
      one_sub_pow_le_exp (pow_le_one₀ hcm0.le hcm1) J
    have hWw : 1 / W ≤ w := by
      rw [div_le_iff₀ hW0, hWdef, mul_add]
      have : w * (1 / w) = 1 := by field_simp
      have : 0 ≤ w * (1 / aLo) := by positivity
      linarith
    calc (1 - g.cm ^ 2) ^ J * ((1 + g.e) ^ N * S)
        ≤ Real.exp (-(J * g.cm ^ 2)) * (Real.exp (N * g.e + L) * (1 / W)) := by
          gcongr
      _ = Real.exp (-(J * g.cm ^ 2) + (N * g.e + L)) * (1 / W) := by
          rw [Real.exp_add (-(J * g.cm ^ 2))]; ring
      _ ≤ Real.exp 0 * w := by
          gcongr
          linarith
      _ = w := by rw [Real.exp_zero, one_mul]
      _ ≤ g.e ^ 3 * x0.Z := hew3
  have hst := stops hg ha0 hb0 hZ0 hn0 hN hS hK hJ
  refine stopped_mono hst ?_
  have hT : ((N * (K + 1) + 2 * J + 3 * K + 3 : ℕ) : ℝ) ≤
      24 * (R * Real.log ρ / μ + 1) * (R / gain + 1) ^ 2 *
        (3 + 2 * βHi * Real.log ρ / μ +
          Real.log (S * (1 / aLo + 8 * R ^ 3 / (βLo ^ 3 * zLo)))) := by
    rw [hW, ← hWdef, ← hLdef, show R * Real.log ρ / μ = R * X by rw [hXdef]; ring,
      show 2 * βHi * Real.log ρ / μ = 2 * βHi * X by rw [hXdef]; ring, ← hΛdef]
    push_cast
    set r := R / gain
    have hr : 0 ≤ r := by positivity
    set P := R * X + 1
    have hP : 1 ≤ P := by
      have : 0 ≤ R * X := by positivity
      linarith
    have hNP : (N : ℝ) + 3 ≤ 4 * P := by linarith
    have hKr : (K : ℝ) + 1 ≤ 4 * r * Λ + 2 := by linarith
    have hJr : (J : ℝ) ≤ 4 * r ^ 2 * Λ + 1 := by linarith
    have hprod : ((N : ℝ) + 3) * (K + 1) ≤ 4 * P * (4 * r * Λ + 2) :=
      mul_le_mul hNP hKr (by positivity) (by positivity)
    have e1 : (N : ℝ) * (K + 1) + 2 * J + 3 * K + 3 = ((N : ℝ) + 3) * (K + 1) + 2 * J := by ring
    rw [e1]
    have hPΛ : 0 ≤ P * Λ := by positivity
    have hr2 : 0 ≤ r ^ 2 * Λ * (P - 1) := by
      have : 0 ≤ P - 1 := by linarith
      positivity
    have hrP : 0 ≤ r * P * Λ := by positivity
    have hr2' : 0 ≤ r ^ 2 * Λ := by positivity
    have hPL : 0 ≤ P * (Λ - 3) := mul_nonneg (by linarith) (by linarith)
    linarith
  exact_mod_cast hT.trans (Nat.le_ceil _)

end Gains

end LongTails.Proofs.QuadraticPerceptronCone
