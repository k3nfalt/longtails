import LongTails.Proofs.CompositeAdaptiveCounting

namespace OracleTemplate.CompositeAdaptive

lemma initial_weight_inverse_bound {S M κ : ℝ} (hSM : S ≤ M * Real.exp κ) :
    1 / (1 / (8 * S * Real.exp (4 * κ))) ≤ 8 * M * Real.exp (5 * κ) := by
  have hm := mul_le_mul_of_nonneg_right hSM (by positivity : 0 ≤ 8 * Real.exp (4 * κ))
  have he : Real.exp κ * Real.exp (4 * κ) = Real.exp (5 * κ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [one_div_one_div]
  calc
    _ ≤ (M * Real.exp κ) * (8 * Real.exp (4 * κ)) := by nlinarith
    _ = 8 * M * Real.exp (5 * κ) := by rw [show M * Real.exp κ * (8 * Real.exp (4 * κ)) =
      8 * M * (Real.exp κ * Real.exp (4 * κ)) by ring, he]

lemma initialization_log_bound {A M κ : ℝ} (hA : 0 < A) (hM : 0 < M)
    (hinverse : 1 / A ≤ 8 * M * Real.exp (5 * κ)) :
    Real.log (1 / (256 * M * A)) ≤ 5 * κ := by
  have hb := div_le_div_of_nonneg_right hinverse (by positivity : 0 ≤ 256 * M)
  have he : 1 / (256 * M * A) = (1 / A) / (256 * M) := by ring
  have he' : (8 * M * Real.exp (5 * κ)) / (256 * M) = Real.exp (5 * κ) / 32 := by field_simp; norm_num
  rw [he'] at hb
  have hratio : 1 / (256 * M * A) ≤ Real.exp (5 * κ) := by
    rw [he]
    nlinarith [Real.exp_pos (5 * κ)]
  have hh := Real.log_le_log (by positivity : 0 < 1 / (256 * M * A)) hratio
  rwa [Real.log_exp] at hh

lemma endpoint_log_bound {A B M κ τ : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hτ : 0 < τ) (hinverse : 1 / A ≤ 8 * M * Real.exp (5 * κ))
    (hfinal : M * B ≤ 8 * τ) :
    Real.log B - Real.log A ≤ 5 * κ + Real.log (64 * τ) := by
  have hi := mul_le_mul_of_nonneg_left hinverse hB.le
  have hf := mul_le_mul_of_nonneg_right hfinal (by positivity : 0 ≤ 8 * Real.exp (5 * κ))
  have hratio : B / A ≤ 64 * τ * Real.exp (5 * κ) := by
    rw [show B / A = B * (1 / A) by ring]
    nlinarith
  have hh := Real.log_le_log (div_pos hB hA) hratio
  rw [Real.log_div hB.ne' hA.ne', Real.log_mul (by positivity : 64 * τ ≠ 0)
    (Real.exp_pos (5 * κ)).ne', Real.log_exp] at hh
  linarith

lemma log_scale_lower {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 ≤ τ) :
    4 ≤ Real.log (128 * (1 + κ + τ)) := by
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 128)
    (by linarith : 128 ≤ 128 * (1 + κ + τ))
  rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow] at hh
  norm_num at hh
  linarith [Real.log_two_gt_d9]

lemma search_log_factors {κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 ≤ τ) :
    ((1 + ⌈Real.log (1000 * (1 + 4 * κ)) / Real.log 2⌉₊ : ℕ) : ℝ) ≤
      4 * Real.log (128 * (1 + κ + τ)) ∧
    Real.log (128 * (1 + 4 * κ)) / Real.log 2 ≤ 2 * Real.log (128 * (1 + κ + τ)) := by
  let W := 128 * (1 + κ + τ)
  let ℓ := Real.log W
  have hW : 0 < W := by dsimp [W]; positivity
  have hℓ : 4 ≤ ℓ := log_scale_lower hκ hτ
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lower : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hD : 0 < 1000 * (1 + 4 * κ) := by positivity
  have hDle : 1000 * (1 + 4 * κ) ≤ W ^ 2 := by dsimp [W]; nlinarith [sq_nonneg (κ + τ)]
  have hDlog := Real.log_le_log hD hDle
  rw [Real.log_pow] at hDlog
  norm_num at hDlog
  have hdiv : Real.log (1000 * (1 + 4 * κ)) / Real.log 2 ≤ 3 * ℓ := by
    apply (div_le_iff₀ hlog2).mpr
    have hm := mul_le_mul_of_nonneg_left hlog2lower hℓ0
    change Real.log (1000 * (1 + 4 * κ)) ≤ 3 * ℓ * Real.log 2
    change Real.log (1000 * (1 + 4 * κ)) ≤ 2 * ℓ at hDlog
    nlinarith
  have hDnonneg : 0 ≤ Real.log (1000 * (1 + 4 * κ)) := Real.log_nonneg (by linarith)
  have hceil := Nat.ceil_lt_add_one (div_nonneg hDnonneg hlog2.le)
  have hQle : 128 * (1 + 4 * κ) ≤ 4 * W := by dsimp [W]; linarith
  have hQlog := Real.log_le_log (by positivity : 0 < 128 * (1 + 4 * κ)) hQle
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hW.ne',
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hQlog
  norm_num at hQlog
  have hℓdiv : ℓ / Real.log 2 ≤ (3 / 2) * ℓ := by
    apply (div_le_iff₀ hlog2).mpr
    have hm := mul_le_mul_of_nonneg_left hlog2lower hℓ0
    nlinarith
  have hQdiv := div_le_div_of_nonneg_right hQlog hlog2.le
  have he : (2 * Real.log 2 + Real.log W) / Real.log 2 = 2 + ℓ / Real.log 2 := by
    dsimp [ℓ]
    field_simp
  rw [he] at hQdiv
  constructor
  · push_cast
    change 1 + (⌈Real.log (1000 * (1 + 4 * κ)) / Real.log 2⌉₊ : ℝ) ≤ 4 * ℓ
    linarith
  · change Real.log (128 * (1 + 4 * κ)) / Real.log 2 ≤ 2 * ℓ
    linarith

lemma endpoint_log_scale_bound {H κ τ : ℝ} (hκ : 0 ≤ κ) (hτ : 0 < τ)
    (hbound : H ≤ 5 * κ + Real.log (64 * τ)) :
    H ≤ 5 * κ + Real.log (128 * (1 + κ + τ)) := by
  have hl := Real.log_le_log (by positivity : 0 < 64 * τ)
    (by linarith : 64 * τ ≤ 128 * (1 + κ + τ))
  linarith

lemma endpoint_start_log_bound {A B M κ τ : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hκ : 0 ≤ κ) (hτ : 0 < τ) (hinverse : 1 / A ≤ 8 * M * Real.exp (5 * κ))
    (hfinal : M * B ≤ 8 * τ) :
    Real.log (B / (A / 16)) / Real.log 2 ≤ 8 * κ + 3 * Real.log (128 * (1 + κ + τ)) := by
  let W := 128 * (1 + κ + τ)
  let ℓ := Real.log W
  have hW : 0 < W := by dsimp [W]; positivity
  have hℓ : 0 ≤ ℓ := le_trans (by norm_num : (0 : ℝ) ≤ 4) (log_scale_lower hκ hτ.le)
  have hH := endpoint_log_bound hA hB hτ hinverse hfinal
  have hlarge : 1024 * τ ≤ W ^ 2 := by dsimp [W]; nlinarith [sq_nonneg (κ + τ)]
  have hl := Real.log_le_log (by positivity : 0 < 1024 * τ) hlarge
  rw [Real.log_pow] at hl
  norm_num at hl
  have he : Real.log (64 * τ) + Real.log 16 = Real.log (1024 * τ) := by
    rw [← Real.log_mul (by positivity : 64 * τ ≠ 0) (by norm_num : (16 : ℝ) ≠ 0)]
    congr 1
    ring
  have hr : Real.log (B / (A / 16)) ≤ 5 * κ + 2 * ℓ := by
    rw [Real.log_div hB.ne' (div_pos hA (by norm_num)).ne',
      Real.log_div hA.ne' (by norm_num : (16 : ℝ) ≠ 0)]
    change Real.log (1024 * τ) ≤ 2 * ℓ at hl
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lower : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  apply (div_le_iff₀ hlog2).mpr
  have hm := mul_le_mul_of_nonneg_left hlog2lower (by positivity : 0 ≤ 8 * κ + 3 * ℓ)
  change Real.log (B / (A / 16)) ≤ (8 * κ + 3 * ℓ) * Real.log 2
  nlinarith

lemma final_call_budget {C N V κ ℓ : ℝ} (hκ : 0 ≤ κ) (hℓ : 1 ≤ ℓ)
    (hV : 1 + κ ≤ V) (hN : N ≤ 1024 * V * ℓ)
    (hcost : C ≤ 2 + 14 * N * ℓ + 16 * κ + 6 * ℓ) :
    C ≤ 32768 * V * ℓ ^ 2 := by
  have hV1 : 1 ≤ V := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hs : 1 ≤ ℓ ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs hV0
  have hl := mul_le_mul_of_nonneg_right hV1 (sq_nonneg ℓ)
  have hstep := mul_le_mul_of_nonneg_right hN (by positivity : 0 ≤ 14 * ℓ)
  nlinarith

end OracleTemplate.CompositeAdaptive
