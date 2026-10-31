import LongTails.Proofs.SpsaStep

namespace LongTails.Proofs.SpsaTuning

open LongTails.Proofs.SpsaStep

noncomputable def smoothing (L ε : ℝ) (d : ℕ) : ℝ := ε / (28 * L * d)

noncomputable def scaleS (σ ε : ℝ) : ℝ := 2 * (σ + ε / 56)

noncomputable def clipLevel (σ p ε : ℝ) : ℝ :=
  256 * scaleS σ ε + 64 * ε + 2 * scaleS σ ε * (33 * scaleS σ ε / ε) ^ (1 / (p - 1))

noncomputable def stepSize (L σ p ε : ℝ) (d : ℕ) : ℝ :=
  min (1 / (8192 * L * d)) (ε ^ 2 / (96 * L * d * (clipLevel σ p ε ^ (2 - p) * scaleS σ ε ^ p)))

noncomputable def horizon (L Δ σ p ε : ℝ) (d : ℕ) : ℕ :=
  ⌈2 ^ 20 * 132 ^ (p / (p - 1)) * L * d * Δ / ε ^ 2 * (1 + (σ / ε) ^ (p / (p - 1)))⌉₊

variable {L Δ σ p ε : ℝ} {d : ℕ}

section Basic

variable (hd : 0 < d) (hL : 0 < L) (hσ : 0 ≤ σ) (hp1 : 1 < p) (hp2 : p ≤ 2) (hε : 0 < ε)
include hd hL hε

lemma rho_eq : L * smoothing L ε d * d / 2 = ε / 56 := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  unfold smoothing; field_simp; ring

lemma S_eq : 2 * (σ + L * smoothing L ε d * d / 2) = scaleS σ ε := by
  rw [rho_eq hd hL hε]; rfl

lemma smoothing_pos : 0 < smoothing L ε d := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  unfold smoothing; positivity

omit hd hL in
lemma scaleS_pos (hσ : 0 ≤ σ) : 0 < scaleS σ ε := by unfold scaleS; positivity

omit hd hL in
lemma clip_ge_S (hσ : 0 ≤ σ) : 256 * scaleS σ ε ≤ clipLevel σ p ε := by
  have := scaleS_pos (ε := ε) hε hσ
  unfold clipLevel
  have : 0 ≤ 2 * scaleS σ ε * (33 * scaleS σ ε / ε) ^ (1 / (p - 1)) := by positivity
  linarith

omit hd hL in
lemma clip_ge_eps (hσ : 0 ≤ σ) : 64 * ε ≤ clipLevel σ p ε := by
  have := scaleS_pos (ε := ε) hε hσ
  unfold clipLevel
  have : 0 ≤ 2 * scaleS σ ε * (33 * scaleS σ ε / ε) ^ (1 / (p - 1)) := by positivity
  linarith

omit hd hL in
lemma clip_pos (hσ : 0 ≤ σ) : 0 < clipLevel σ p ε := by
  have := clip_ge_eps (p := p) hε hσ; linarith

lemma bias_le (hσ : 0 ≤ σ) (hp1 : 1 < p) :
    biasLevel L σ p (smoothing L ε d) (clipLevel σ p ε) d ≤ ε / 14 := by
  unfold biasLevel
  rw [rho_eq hd hL hε]
  change ε / 56 + Real.sqrt 3 * scaleS σ ε * (2 * scaleS σ ε / clipLevel σ p ε) ^ (p - 1) ≤ ε / 14
  set S := scaleS σ ε
  set c := clipLevel σ p ε
  have hS := scaleS_pos (ε := ε) hε hσ
  have hc := clip_pos (p := p) hε hσ
  have hp0 : 0 < p - 1 := by linarith
  set k := (33 * S / ε) ^ (1 / (p - 1)) with hk
  have hk0 : 0 < k := by positivity
  have hck : 2 * S * k ≤ c := by
    simp only [c, clipLevel]
    have : 0 ≤ 256 * S + 64 * ε := by positivity
    linarith
  have hratio : 2 * S / c ≤ 1 / k := by
    rw [div_le_div_iff₀ hc hk0]; linarith
  have hpow : (2 * S / c) ^ (p - 1) ≤ ε / (33 * S) := by
    calc (2 * S / c) ^ (p - 1) ≤ (1 / k) ^ (p - 1) :=
          Real.rpow_le_rpow (by positivity) hratio hp0.le
      _ = ε / (33 * S) := by
          rw [one_div, Real.inv_rpow hk0.le, hk, ← Real.rpow_mul (by positivity),
            one_div_mul_cancel hp0.ne', Real.rpow_one, inv_div]
  have hs3 : Real.sqrt 3 ≤ 1.7321 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have : Real.sqrt 3 * S * (2 * S / c) ^ (p - 1) ≤ Real.sqrt 3 * S * (ε / (33 * S)) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have e : Real.sqrt 3 * S * (ε / (33 * S)) = Real.sqrt 3 * ε / 33 := by
    rw [show Real.sqrt 3 * S * (ε / (33 * S)) = Real.sqrt 3 * ε / 33 * (S / S) by ring,
      div_self hS.ne', mul_one]
  rw [e] at this
  have h2 : Real.sqrt 3 * ε / 33 ≤ 1.7321 * ε / 33 := by
    have := mul_le_mul_of_nonneg_right hs3 hε.le; linarith
  linarith

lemma bias_mul_le (hσ : 0 ≤ σ) (hp1 : 1 < p) :
    512 * biasLevel L σ p (smoothing L ε d) (clipLevel σ p ε) d ≤ clipLevel σ p ε := by
  have h1 := bias_le hd hL hε hσ hp1
  have h2 := clip_ge_eps (p := p) hε hσ
  linarith

omit hε in
lemma step_le : stepSize L σ p ε d * (8192 * L * d) ≤ 1 := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have h := min_le_left (1 / (8192 * L * d))
    (ε ^ 2 / (96 * L * d * (clipLevel σ p ε ^ (2 - p) * scaleS σ ε ^ p)))
  calc stepSize L σ p ε d * (8192 * L * d) ≤ 1 / (8192 * L * d) * (8192 * L * d) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = 1 := by field_simp

lemma step_pos (hσ : 0 ≤ σ) : 0 < stepSize L σ p ε d := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have hc := clip_pos (p := p) hε hσ
  have hS := scaleS_pos (ε := ε) hε hσ
  unfold stepSize
  exact lt_min (by positivity) (by positivity)

lemma step_var (hσ : 0 ≤ σ) :
    4 * L * stepSize L σ p ε d * d * (clipLevel σ p ε ^ (2 - p) * scaleS σ ε ^ p) ≤ ε ^ 2 / 24 := by
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have hc := clip_pos (p := p) hε hσ
  have hS := scaleS_pos (ε := ε) hε hσ
  set W := clipLevel σ p ε ^ (2 - p) * scaleS σ ε ^ p
  have hW : 0 < W := by positivity
  have h := min_le_right (1 / (8192 * L * d)) (ε ^ 2 / (96 * L * d * W))
  have : 4 * L * stepSize L σ p ε d * d * W ≤ 4 * L * (ε ^ 2 / (96 * L * d * W)) * d * W := by
    have hh : stepSize L σ p ε d ≤ ε ^ 2 / (96 * L * d * W) := h
    have := mul_le_mul_of_nonneg_left hh (by positivity : (0 : ℝ) ≤ 4 * L)
    nlinarith [mul_pos hW (by positivity : (0 : ℝ) < d)]
  refine this.trans (le_of_eq ?_)
  field_simp; ring

end Basic

section Budget

lemma max_rpow_le {a b e s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (a + b + e) ^ s ≤ a ^ s + b ^ s + e ^ s := by
  calc (a + b + e) ^ s ≤ (a + b) ^ s + e ^ s := Real.rpow_add_le_add_rpow (by positivity) he hs hs1
    _ ≤ a ^ s + b ^ s + e ^ s := by
        have := Real.rpow_add_le_add_rpow ha hb hs hs1; linarith

lemma pow_le_one_add {x r q : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) (hrq : r ≤ q) : x ^ r ≤ 1 + x ^ q := by
  rcases le_total x 1 with h | h
  · have : x ^ r ≤ 1 := Real.rpow_le_one hx h hr
    have : 0 ≤ x ^ q := by positivity
    linarith
  · have : x ^ r ≤ x ^ q := Real.rpow_le_rpow_of_exponent_le h hrq
    linarith

variable (hd : 0 < d) (hL : 0 < L) (hσ : 0 ≤ σ) (hp1 : 1 < p) (hp2 : p ≤ 2) (hε : 0 < ε)
include hσ hp1 hp2 hε

omit hσ hε in
lemma kbound {x : ℝ} (hx0 : 0 < x) :
    (256 * x + 64 + 2 * x * (33 * x) ^ (1 / (p - 1))) ^ (2 - p) * x ^ p ≤
      330 * 33 ^ (p / (p - 1)) / 1089 * (1 + x ^ (p / (p - 1))) := by
  set q := p / (p - 1) with hq
  have hp0 : 0 < p - 1 := by linarith
  have hq2 : 2 ≤ q := by rw [hq, le_div_iff₀ hp0]; linarith
  have hqm : 1 / (p - 1) * (2 - p) = q - 2 := by rw [hq]; field_simp; ring
  have hs0 : 0 ≤ 2 - p := by linarith
  have hs1 : 2 - p ≤ 1 := by linarith
  have hsum := max_rpow_le (a := 256 * x) (b := 64) (e := 2 * x * (33 * x) ^ (1 / (p - 1)))
    (by positivity) (by norm_num) (by positivity) hs0 hs1
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx0 p
  have t1 : (256 * x) ^ (2 - p) * x ^ p ≤ 256 * x ^ (2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hx0.le, mul_assoc, ← Real.rpow_add hx0, sub_add_cancel]
    have h256 : (256 : ℝ) ^ (2 - p) ≤ 256 := by
      calc (256 : ℝ) ^ (2 - p) ≤ 256 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
        _ = 256 := Real.rpow_one _
    exact mul_le_mul_of_nonneg_right h256 (by positivity)
  have t2 : (64 : ℝ) ^ (2 - p) * x ^ p ≤ 64 * x ^ p := by
    have h64 : (64 : ℝ) ^ (2 - p) ≤ 64 := by
      calc (64 : ℝ) ^ (2 - p) ≤ 64 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
        _ = 64 := Real.rpow_one _
    exact mul_le_mul_of_nonneg_right h64 hxp.le
  have t3 : (2 * x * (33 * x) ^ (1 / (p - 1))) ^ (2 - p) * x ^ p ≤ 2 * 33 ^ (q - 2) * x ^ q := by
    have hA : (2 * x * (33 * x) ^ (1 / (p - 1))) ^ (2 - p) =
        2 ^ (2 - p) * x ^ (2 - p) * (33 ^ (q - 2) * x ^ (q - 2)) := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hx0.le,
        ← Real.rpow_mul (by positivity), hqm, Real.mul_rpow (by norm_num) hx0.le]
    have hxq : x ^ (2 - p) * x ^ (q - 2) * x ^ p = x ^ q := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    have key : 2 ^ (2 - p) * x ^ (2 - p) * (33 ^ (q - 2) * x ^ (q - 2)) * x ^ p =
        2 ^ (2 - p) * 33 ^ (q - 2) * x ^ q := by
      rw [← hxq]; ring
    rw [hA, key]
    have h2 : (2 : ℝ) ^ (2 - p) ≤ 2 := by
      calc (2 : ℝ) ^ (2 - p) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
        _ = 2 := Real.rpow_one _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
  have hx2 := pow_le_one_add (x := x) (q := q) hx0.le (by norm_num : (0 : ℝ) ≤ 2) hq2
  have hxp' := pow_le_one_add (x := x) (q := q) hx0.le (by linarith : (0 : ℝ) ≤ p) (by linarith)
  have h33 : (33 : ℝ) ^ (q - 2) = 33 ^ q / 1089 := by
    rw [Real.rpow_sub (by norm_num)]; norm_num
  have h33q : (1089 : ℝ) ≤ 33 ^ q := by
    calc (1089 : ℝ) = 33 ^ (2 : ℝ) := by norm_num
      _ ≤ 33 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
  have hA : 0 ≤ 1 + x ^ q := by positivity
  have hxqn : 0 ≤ x ^ q := by positivity
  calc (256 * x + 64 + 2 * x * (33 * x) ^ (1 / (p - 1))) ^ (2 - p) * x ^ p
      ≤ ((256 * x) ^ (2 - p) + (64 : ℝ) ^ (2 - p) +
          (2 * x * (33 * x) ^ (1 / (p - 1))) ^ (2 - p)) * x ^ p :=
        mul_le_mul_of_nonneg_right hsum hxp.le
    _ = (256 * x) ^ (2 - p) * x ^ p + (64 : ℝ) ^ (2 - p) * x ^ p +
          (2 * x * (33 * x) ^ (1 / (p - 1))) ^ (2 - p) * x ^ p := by ring
    _ ≤ 256 * x ^ (2 : ℝ) + 64 * x ^ p + 2 * 33 ^ (q - 2) * x ^ q := by linarith
    _ ≤ 330 * 33 ^ q / 1089 * (1 + x ^ q) := by
        rw [h33]
        have hk : (1 : ℝ) ≤ 33 ^ q / 1089 := by rw [le_div_iff₀ (by norm_num)]; linarith
        have hK0 : (0 : ℝ) ≤ 33 ^ q / 1089 := by linarith
        have hKY : 1 + x ^ q ≤ 33 ^ q / 1089 * (1 + x ^ q) := by
          have := mul_le_mul_of_nonneg_right hk hA; linarith
        have hKx : 33 ^ q / 1089 * x ^ q ≤ 33 ^ q / 1089 * (1 + x ^ q) :=
          mul_le_mul_of_nonneg_left (by linarith) hK0
        have e1 : 330 * 33 ^ q / 1089 * (1 + x ^ q) = 330 * (33 ^ q / 1089 * (1 + x ^ q)) := by ring
        have e2 : 2 * (33 ^ q / 1089) * x ^ q = 2 * (33 ^ q / 1089 * x ^ q) := by ring
        rw [e1, e2]
        linarith

lemma W_le :
    clipLevel σ p ε ^ (2 - p) * scaleS σ ε ^ p ≤
      ε ^ 2 * (330 * 33 ^ (p / (p - 1)) / 1089) * (1 + (scaleS σ ε / ε) ^ (p / (p - 1))) := by
  have hS := scaleS_pos (ε := ε) hε hσ
  have hc : clipLevel σ p ε = 256 * scaleS σ ε + 64 * ε +
      2 * scaleS σ ε * (33 * scaleS σ ε / ε) ^ (1 / (p - 1)) := rfl
  rw [hc]
  generalize scaleS σ ε = S at hS ⊢
  obtain ⟨x, hx⟩ : ∃ x, x = S / ε := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; positivity
  have hSx : S = ε * x := by rw [hx]; field_simp
  subst hSx
  have h33 : 33 * (ε * x) / ε = 33 * x := by field_simp
  have hxe : ε * x / ε = x := by field_simp
  rw [h33, hxe]
  have hfac : 256 * (ε * x) + 64 * ε + 2 * (ε * x) * (33 * x) ^ (1 / (p - 1)) =
      ε * (256 * x + 64 + 2 * x * (33 * x) ^ (1 / (p - 1))) := by ring
  rw [hfac, Real.mul_rpow hε.le (by positivity), Real.mul_rpow hε.le hx0.le]
  have he : ε ^ (2 - p) * ε ^ p = ε ^ 2 := by
    rw [← Real.rpow_add hε, sub_add_cancel]; norm_cast
  have hk := kbound hp1 hp2 hx0
  have e : ε ^ (2 - p) * (256 * x + 64 + 2 * x * (33 * x) ^ (1 / (p - 1))) ^ (2 - p) *
      (ε ^ p * x ^ p) = (ε ^ (2 - p) * ε ^ p) *
        ((256 * x + 64 + 2 * x * (33 * x) ^ (1 / (p - 1))) ^ (2 - p) * x ^ p) := by ring
  rw [e, he]
  have : ε ^ 2 * ((256 * x + 64 + 2 * x * (33 * x) ^ (1 / (p - 1))) ^ (2 - p) * x ^ p) ≤
      ε ^ 2 * (330 * 33 ^ (p / (p - 1)) / 1089 * (1 + x ^ (p / (p - 1)))) :=
    mul_le_mul_of_nonneg_left hk (by positivity)
  linarith [show ε ^ 2 * (330 * 33 ^ (p / (p - 1)) / 1089 * (1 + x ^ (p / (p - 1)))) =
    ε ^ 2 * (330 * 33 ^ (p / (p - 1)) / 1089) * (1 + x ^ (p / (p - 1))) by ring]

omit hp2 in
lemma x_pow_le :
    1 + (scaleS σ ε / ε) ^ (p / (p - 1)) ≤ 4 ^ (p / (p - 1)) * (1 + (σ / ε) ^ (p / (p - 1))) := by
  set q := p / (p - 1) with hq
  have hp0 : 0 < p - 1 := by linarith
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ hp0]; linarith
  have hx : scaleS σ ε / ε = 2 * (σ / ε) + 1 / 28 := by unfold scaleS; field_simp; ring
  rw [hx]
  have h := add_rpow_le_two_mul (x := 2 * (σ / ε)) (y := 1 / 28) (by positivity) (by norm_num) hq1
  rw [Real.mul_rpow (by norm_num) (by positivity)] at h
  have h2q : (2 : ℝ) ^ (q - 1) * 2 ^ q ≤ 4 ^ q := by
    rw [← Real.rpow_add (by norm_num)]
    calc (2 : ℝ) ^ (q - 1 + q) ≤ 2 ^ (2 * q) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 ^ q := by rw [Real.rpow_mul (by norm_num)]; norm_num
  have hsmall : (2 : ℝ) ^ (q - 1) * (1 / 28) ^ q ≤ 1 := by
    have : (2 : ℝ) ^ (q - 1) ≤ 2 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    calc (2 : ℝ) ^ (q - 1) * (1 / 28) ^ q ≤ 2 ^ q * (1 / 28) ^ q :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = (1 / 14) ^ q := by rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
      _ ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
  have h4 : (4 : ℝ) ≤ 4 ^ q := by
    calc (4 : ℝ) = 4 ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ 4 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
  have hσq : 0 ≤ (σ / ε) ^ q := by positivity
  have h5 := mul_le_mul_of_nonneg_right h2q hσq
  have hexp : (2 : ℝ) ^ (q - 1) * (2 ^ q * (σ / ε) ^ q + (1 / 28) ^ q) =
      2 ^ (q - 1) * 2 ^ q * (σ / ε) ^ q + 2 ^ (q - 1) * (1 / 28) ^ q := by ring
  have e2 : (4 : ℝ) ^ q * (1 + (σ / ε) ^ q) = 4 ^ q + 4 ^ q * (σ / ε) ^ q := by ring
  rw [e2]
  linarith

include hd hL in
lemma horizon_suffices (hΔ : 0 ≤ Δ) :
    96 * Δ / (stepSize L σ p ε d * ε ^ 2) ≤ (horizon L Δ σ p ε d : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set q := p / (p - 1) with hq
  set W := clipLevel σ p ε ^ (2 - p) * scaleS σ ε ^ p
  have hc := clip_pos (p := p) hε hσ
  have hS := scaleS_pos (ε := ε) hε hσ
  have hW : 0 < W := by positivity
  have hη := step_pos (p := p) hd hL hε hσ
  have hWle := W_le hσ hp1 hp2 hε
  have hxp := x_pow_le hσ hp1 hε
  have h132 : (132 : ℝ) ^ q = 33 ^ q * 4 ^ q := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hq0 : 0 ≤ q := by rw [hq]; exact div_nonneg (by linarith) (by linarith)
  have h4 : (1 : ℝ) ≤ 4 ^ q := Real.one_le_rpow (by norm_num) hq0
  have h33 : (1 : ℝ) ≤ 33 ^ q := Real.one_le_rpow (by norm_num) hq0
  set M := 2 ^ 20 * 132 ^ q * L * d * Δ / ε ^ 2 * (1 + (σ / ε) ^ q) with hM
  have hceil : M ≤ (horizon L Δ σ p ε d : ℝ) := Nat.le_ceil M
  have hone : (1 : ℝ) ≤ 1 + (σ / ε) ^ q := le_add_of_nonneg_right (by positivity)
  rcases min_choice (1 / (8192 * L * d)) (ε ^ 2 / (96 * L * d * W)) with hmin | hmin
  · have hst : stepSize L σ p ε d = 1 / (8192 * L * d) := hmin
    rw [hst]
    have e : 96 * Δ / (1 / (8192 * L * d) * ε ^ 2) = 786432 * L * d * Δ / ε ^ 2 := by
      field_simp; ring
    rw [e]
    have : 786432 * L * d * Δ / ε ^ 2 ≤ M := by
      rw [hM]
      have hb : 786432 ≤ 2 ^ 20 * 132 ^ q * (1 + (σ / ε) ^ q) := by
        have : (1 : ℝ) ≤ 132 ^ q := Real.one_le_rpow (by norm_num) hq0
        nlinarith
      have hLdΔ : 0 ≤ L * d * Δ / ε ^ 2 := by positivity
      calc 786432 * L * d * Δ / ε ^ 2 = 786432 * (L * d * Δ / ε ^ 2) := by ring
        _ ≤ 2 ^ 20 * 132 ^ q * (1 + (σ / ε) ^ q) * (L * d * Δ / ε ^ 2) :=
            mul_le_mul_of_nonneg_right hb hLdΔ
        _ = 2 ^ 20 * 132 ^ q * L * d * Δ / ε ^ 2 * (1 + (σ / ε) ^ q) := by ring
    linarith
  · have hst : stepSize L σ p ε d = ε ^ 2 / (96 * L * d * W) := hmin
    rw [hst]
    have e : 96 * Δ / (ε ^ 2 / (96 * L * d * W) * ε ^ 2) = 9216 * L * d * Δ * W / ε ^ 4 := by
      field_simp; ring
    rw [e]
    have hWb : W ≤ ε ^ 2 * (330 * 33 ^ q / 1089) * (4 ^ q * (1 + (σ / ε) ^ q)) := by
      refine hWle.trans ?_
      apply mul_le_mul_of_nonneg_left hxp (by positivity)
    have : 9216 * L * d * Δ * W / ε ^ 4 ≤ M := by
      rw [hM, div_le_iff₀ (by positivity)]
      have hLdΔ : 0 ≤ 9216 * L * d * Δ := by positivity
      calc 9216 * L * d * Δ * W ≤ 9216 * L * d * Δ *
            (ε ^ 2 * (330 * 33 ^ q / 1089) * (4 ^ q * (1 + (σ / ε) ^ q))) :=
            mul_le_mul_of_nonneg_left hWb hLdΔ
        _ ≤ 2 ^ 20 * 132 ^ q * L * d * Δ / ε ^ 2 * (1 + (σ / ε) ^ q) * ε ^ 4 := by
            rw [h132]
            have e2 : 2 ^ 20 * (33 ^ q * 4 ^ q) * L * d * Δ / ε ^ 2 * (1 + (σ / ε) ^ q) * ε ^ 4 =
                (2 ^ 20 * ε ^ 2) * (L * d * Δ) * (33 ^ q * 4 ^ q * (1 + (σ / ε) ^ q)) := by
              field_simp
            rw [e2]
            have hpos : 0 ≤ (L * d * Δ) * (33 ^ q * 4 ^ q * (1 + (σ / ε) ^ q)) * ε ^ 2 := by
              positivity
            nlinarith
    linarith

end Budget

end LongTails.Proofs.SpsaTuning
