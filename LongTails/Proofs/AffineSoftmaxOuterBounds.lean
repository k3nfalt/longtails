import LongTails.Proofs.AffineSoftmaxOuterMoments

namespace LongTails.Proofs.AffineSoftmaxOuterBounds

lemma weight_overshoot {μ A a M : ℝ} (hA : A ≤ M)
    (ha : 0 < a) (hM : 0 < M) (hscale : 1 ≤ μ * M)
    (hweight : μ * a ^ 2 = A + a) : A + a < 3 * M := by
  have hs : a ^ 2 ≤ M * (A + a) := by
    have he := congrArg (fun x : ℝ => M * x) hweight
    nlinarith only [mul_nonneg (sub_nonneg.mpr hscale) (sq_nonneg a), he]
  have ht : M * (A + a) ≤ M * (M + a) := by
    exact mul_le_mul_of_nonneg_left (show A + a ≤ M + a by linarith) hM.le
  have hb : a < 2 * M := by
    by_contra hn
    have hn' : 2 * M ≤ a := le_of_not_gt hn
    have hp := mul_nonneg (sub_nonneg.mpr hn') (show 0 ≤ a + M by positivity)
    nlinarith
  linarith

lemma small_weight_error {μ A a r H e : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (hr : 0 < r) (hH : 0 < H) (he : 0 < e)
    (hweight : μ * a ^ 2 = A + a)
    (hlinear : μ * r ^ 2 ≤ e * H ^ 3)
    (hcubic : μ ^ 3 * A * r ^ 4 ≤ 800 * e ^ 2 * H ^ 6) :
    μ ^ 2 * a * r ^ 2 / H ^ 3 < 31 * e := by
  let w := μ ^ 2 * a * r ^ 2 / H ^ 3
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hid : w ^ 2 = μ ^ 3 * A * r ^ 4 / H ^ 6 + (μ * r ^ 2 / H ^ 3) * w := by
    dsimp [w]
    field_simp
    nlinarith only [hweight]
  have hl : μ * r ^ 2 / H ^ 3 ≤ e := (div_le_iff₀ (by positivity)).2 hlinear
  have hc : μ ^ 3 * A * r ^ 4 / H ^ 6 ≤ 800 * e ^ 2 :=
    (div_le_iff₀ (by positivity)).2 hcubic
  have hb : w ^ 2 ≤ 800 * e ^ 2 + e * w := by
    have := mul_le_mul_of_nonneg_right hl hw
    linarith
  change w < 31 * e
  by_contra hn
  have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn))
    (show 0 ≤ w + 30 * e by positivity)
  nlinarith [sq_pos_of_pos he]

lemma floor_small_weight_error {μ A a r H e t D : ℝ} (hμ : 0 < μ)
    (hA : 0 ≤ A) (ha : 0 < a) (hr : 0 < r) (hH : 3 ≤ H) (he : 0 < e)
    (ht : 1 ≤ t) (hD : t ^ 3 * r ^ 2 = D ^ 2)
    (hweight : μ * a ^ 2 = A + a)
    (hfloor : μ ≤ 2 * (e * H ^ 2 / (t * r ^ 2))) (hcap : A ≤ 100 * D ^ 2 / e) :
    μ ^ 2 * a * r ^ 2 / H ^ 3 < 31 * e := by
  have htpos : 0 < t := by linarith
  have hHpos : 0 < H := by linarith
  apply small_weight_error hμ ha hr hHpos he hweight
  · have hm := mul_le_mul_of_nonneg_right hfloor (sq_nonneg r)
    have heq : 2 * (e * H ^ 2 / (t * r ^ 2)) * r ^ 2 = 2 * e * H ^ 2 / t := by
      field_simp
    rw [heq] at hm
    have hh : 2 ≤ H * t := by nlinarith
    have hb : 2 * e * H ^ 2 / t ≤ e * H ^ 3 := by
      apply (div_le_iff₀ htpos).2
      nlinarith only [mul_nonneg (show 0 ≤ H * t - 2 by linarith) (show 0 ≤ e * H ^ 2 by positivity)]
    exact hm.trans hb
  · have hc : μ ^ 3 * A * r ^ 4 ≤
        (2 * (e * H ^ 2 / (t * r ^ 2))) ^ 3 * (100 * D ^ 2 / e) * r ^ 4 := by
      gcongr
    have heq : (2 * (e * H ^ 2 / (t * r ^ 2))) ^ 3 * (100 * D ^ 2 / e) * r ^ 4 =
        800 * e ^ 2 * H ^ 6 := by
      rw [← hD]
      field_simp
      ring
    exact hc.trans_eq heq

lemma final_error_small {μ a r H e : ℝ} (ha : 0 < a)
    (he : 0 < e) (hw : μ ^ 2 * a * r ^ 2 / H ^ 3 < 31 * e) :
    (μ * a ^ 2) * (μ * r ^ 2 / (100000 * H ^ 3)) + a * e / 1000 +
      3 * a ^ 2 * (μ ^ 2 * r ^ 2 / (100000 * H ^ 3)) / 4 < a * e / 100 := by
  have h := mul_lt_mul_of_pos_left hw ha
  have hid : (μ * a ^ 2) * (μ * r ^ 2 / (100000 * H ^ 3)) + a * e / 1000 +
      3 * a ^ 2 * (μ ^ 2 * r ^ 2 / (100000 * H ^ 3)) / 4 =
      7 / 400000 * (a * (μ ^ 2 * a * r ^ 2 / H ^ 3)) + a * e / 1000 := by
    ring
  rw [hid]
  nlinarith [mul_pos ha he]

lemma final_error_large {μ a r H e d : ℝ} (ha : 0 ≤ a)
    (hr : 0 < r) (hH : 3 ≤ H) (he : 0 ≤ e) (hd : 3 * r / 4 ≤ d) :
    (μ * a ^ 2) * (μ * r ^ 2 / (100000 * H ^ 3)) + a * e / 1000 +
      3 * a ^ 2 * (μ ^ 2 * r ^ 2 / (100000 * H ^ 3)) / 4 ≤
      μ * (μ * a ^ 2) * d ^ 2 / 16 + a * e / 100 := by
  have hHpos : 0 < H := by linarith
  have hcube : 27 ≤ H ^ 3 := by nlinarith [sq_nonneg (H - 3)]
  have hdpos : 0 ≤ d := by linarith
  have hsq : 9 * r ^ 2 / 16 ≤ d ^ 2 := by nlinarith
  have hcoeff : 7 * r ^ 2 / (400000 * H ^ 3) ≤ d ^ 2 / 16 := by
    apply (div_le_iff₀ (by positivity)).2
    have hp := mul_nonneg (show 0 ≤ H ^ 3 - 27 by linarith) (sq_nonneg d)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hcoeff (show 0 ≤ μ ^ 2 * a ^ 2 by positivity)
  have hid : (μ * a ^ 2) * (μ * r ^ 2 / (100000 * H ^ 3)) +
      3 * a ^ 2 * (μ ^ 2 * r ^ 2 / (100000 * H ^ 3)) / 4 =
      (μ ^ 2 * a ^ 2) * (7 * r ^ 2 / (400000 * H ^ 3)) := by ring
  have hb := mul_nonneg ha he
  nlinarith only [hm, hid, hb]

lemma inverse_square_young {q b c : ℝ} (hq : 0 < q) (hc : 0 < c)
    (hbq : b * q ^ 2 = 1) : 3 ≤ c ^ 2 * b + 2 * q / c := by
  have hp := mul_nonneg (sq_nonneg (q - c)) (show 0 ≤ 2 * q + c by positivity)
  have he := congrArg (fun x : ℝ => c ^ 3 * x) hbq
  have hs : 0 ≤ q ^ 2 * (c ^ 3 * b + 2 * q - 3 * c) := by nlinarith only [hp, he]
  have ht : 0 ≤ c ^ 3 * b + 2 * q - 3 * c :=
    nonneg_of_mul_nonneg_right hs (sq_pos_of_pos hq)
  have hd : 3 * c ≤ c ^ 3 * b + 2 * q := by linarith
  have heq : c ^ 2 * b + 2 * q / c = (c ^ 3 * b + 2 * q) / c := by
    field_simp
  rw [heq]
  exact (le_div_iff₀ hc).2 hd

lemma inverse_square_count {ι : Type*} (s : Finset ι) (q b : ι → ℝ) {t H : ℝ}
    (ht : 0 < t) (hH : 3 ≤ H) (hq : ∀ i ∈ s, 0 < q i)
    (hbq : ∀ i ∈ s, b i * q i ^ 2 = 1)
    (hb : ∑ i ∈ s, b i ≤ (5120 / 3) * t ^ 3)
    (hs : ∑ i ∈ s, q i ≤ 6 * H) : (s.card : ℝ) < 30 * H * t := by
  have hi (i : ι) (h : i ∈ s) : 1 ≤ b i / (108 * t ^ 2) + 4 * t * q i := by
    have hh := inverse_square_young (hq i h) (show 0 < 1 / (6 * t) by positivity) (hbq i h)
    have heq : (1 / (6 * t)) ^ 2 * b i + 2 * q i / (1 / (6 * t)) =
        3 * (b i / (108 * t ^ 2) + 4 * t * q i) := by field_simp; ring
    rw [heq] at hh
    linarith
  have hsum := Finset.sum_le_sum hi
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.mul_sum] at hsum
  have hdiv : (∑ i ∈ s, b i) / (108 * t ^ 2) ≤ (1280 / 81) * t := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hb]
  have hqsum := mul_le_mul_of_nonneg_left hs (show 0 ≤ 4 * t by positivity)
  nlinarith only [hsum, hdiv, hqsum, mul_nonneg (sub_nonneg.mpr hH) ht.le, ht]

lemma weight_ratio_log {A a : ℝ} (hA : 0 < A) (ha : 0 ≤ a) :
    a / (A + a) ≤ Real.log (A + a) - Real.log A := by
  have hT : 0 < A + a := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hT hA)
  rw [Real.log_div hT.ne' hA.ne'] at h
  have heq : 1 - ((A + a) / A)⁻¹ = a / (A + a) := by field_simp; ring
  rwa [heq] at h

lemma sqrt_weight_progress {μ A a : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A) (ha : 0 < a)
    (hweight : μ * a ^ 2 = A + a) :
    1 ≤ 2 * Real.sqrt μ * (Real.sqrt (A + a) - Real.sqrt A) := by
  have hT : 0 < A + a := by positivity
  have hsT := Real.sq_sqrt hT.le
  have hsA := Real.sq_sqrt hA
  have hμs := Real.sqrt_nonneg μ
  have hTp := Real.sqrt_pos.2 hT
  have hAp := Real.sqrt_nonneg A
  have horder : Real.sqrt A ≤ Real.sqrt (A + a) := Real.sqrt_le_sqrt (by linarith)
  have hs : Real.sqrt μ * a = Real.sqrt (A + a) := by
    have hh : (Real.sqrt μ * a) ^ 2 = A + a := by
      rw [mul_pow, Real.sq_sqrt hμ.le, hweight]
    nlinarith [mul_nonneg hμs ha.le]
  have hd : (Real.sqrt (A + a) - Real.sqrt A) *
      (Real.sqrt (A + a) + Real.sqrt A) = a := by nlinarith only [hsT, hsA]
  have he := congrArg (fun x : ℝ => Real.sqrt μ * x) hd
  have hp := mul_nonneg (show 0 ≤ Real.sqrt μ * (Real.sqrt (A + a) - Real.sqrt A) by positivity)
    (sub_nonneg.mpr horder)
  nlinarith only [he, hs, hp, hTp]

lemma weight_ratio_sum (A : ℕ → ℝ) (hzero : A 0 = 0)
    (hpos : ∀ k, 0 < A (k + 1)) (hmono : ∀ k, A k ≤ A (k + 1)) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (A (k + 1) - A k) / A (k + 1)) ≤
      1 + Real.log (A (n + 1)) - Real.log (A 1) := by
  induction n with
  | zero => simp [hzero, (hpos 0).ne']
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := weight_ratio_log (hpos n) (sub_nonneg.mpr (hmono (n + 1)))
    have he : A (n + 1) + (A (n + 1 + 1) - A (n + 1)) = A (n + 1 + 1) := by ring
    rw [he] at h
    linarith

lemma small_sqrt_progress {μ A a floor : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A)
    (ha : 0 < a) (hweight : μ * a ^ 2 = A + a) (hfloor : μ ≤ 2 * floor) :
    1 ≤ 2 * Real.sqrt (2 * floor) * (Real.sqrt (A + a) - Real.sqrt A) := by
  have h := sqrt_weight_progress hμ hA ha hweight
  have hs := Real.sqrt_le_sqrt hfloor
  have hd : 0 ≤ Real.sqrt (A + a) - Real.sqrt A :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  nlinarith only [h, mul_nonneg (sub_nonneg.mpr hs) hd]

lemma final_error_bound {μ A a r H e t D d : ℝ} (hμ : 0 < μ)
    (hA : 0 ≤ A) (ha : 0 < a) (hr : 0 < r) (hH : 3 ≤ H) (he : 0 < e)
    (ht : 1 ≤ t) (hD : t ^ 3 * r ^ 2 = D ^ 2)
    (hweight : μ * a ^ 2 = A + a) (hcap : A ≤ 100 * D ^ 2 / e)
    (hvalid : μ ≤ 2 * (e * H ^ 2 / (t * r ^ 2)) ∨ 3 * r / 4 ≤ d) :
    (A + a) * (μ * r ^ 2 / (100000 * H ^ 3)) + a * e / 1000 +
      3 * a ^ 2 * (μ ^ 2 * r ^ 2 / (100000 * H ^ 3)) / 4 ≤
      μ * (A + a) * d ^ 2 / 16 + a * e / 100 := by
  rw [← hweight]
  rcases hvalid with hs | hl
  · have hw := floor_small_weight_error hμ hA ha hr hH he ht hD hweight hs hcap
    have he := final_error_small ha he hw
    have hn : 0 ≤ μ * (μ * a ^ 2) * d ^ 2 / 16 := by positivity
    linarith
  · exact final_error_large ha.le hr hH he.le hl

lemma log_weight_envelope {u H Q : ℝ} (hu : 0 < u) (hH : 3 ≤ H) (hQ : 1 ≤ Q)
    (hb : u ≤ 1200 * H ^ 2 * Q ^ 2) (hlog : Real.log Q ≤ H - 3) :
    1 + Real.log u ≤ 6 * H := by
  have hHp : 0 < H := by linarith
  have hQp : 0 < Q := by linarith
  have hnum : Real.log 1200 < 8 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 8 by norm_num) 9
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have h := Real.log_le_log hu hb
  rw [Real.log_mul (by positivity : (1200 : ℝ) * H ^ 2 ≠ 0) (pow_ne_zero _ hQp.ne'),
    Real.log_mul (by norm_num : (1200 : ℝ) ≠ 0) (pow_ne_zero _ hHp.ne'),
    Real.log_pow, Real.log_pow] at h
  have hh := Real.log_le_sub_one_of_pos hHp
  norm_num only [Nat.cast_ofNat] at h
  linarith

lemma sqrt_progress_count {ι : Type*} (s : Finset ι) (δ : ι → ℝ) {floor M H t : ℝ}
    (hf : 0 < floor) (hM : 0 < M) (hH : 0 < H) (ht : 0 < t)
    (hi : ∀ i ∈ s, 1 ≤ 2 * Real.sqrt (2 * floor) * δ i)
    (hs : ∑ i ∈ s, δ i ≤ Real.sqrt (3 * M))
    (hscale : floor * M ≤ 100 * H ^ 2 * t ^ 2) : (s.card : ℝ) < 49 * H * t := by
  have hsum := Finset.sum_le_sum hi
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum] at hsum
  have hbound := hsum.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have hsq : (2 * Real.sqrt (2 * floor) * Real.sqrt (3 * M)) ^ 2 = 24 * floor * M := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  have hnonneg : 0 ≤ 2 * Real.sqrt (2 * floor) * Real.sqrt (3 * M) := by positivity
  have hc : 0 ≤ (s.card : ℝ) := by positivity
  have hsqbound := mul_nonneg (sub_nonneg.mpr hbound)
    (show 0 ≤ 2 * Real.sqrt (2 * floor) * Real.sqrt (3 * M) + (s.card : ℝ) by positivity)
  by_contra hn
  have hn' : 49 * H * t ≤ (s.card : ℝ) := le_of_not_gt hn
  have hp := mul_nonneg (sub_nonneg.mpr hn') (show 0 ≤ (s.card : ℝ) + 49 * H * t by positivity)
  have hstrict : 0 < H ^ 2 * t ^ 2 := by positivity
  nlinarith only [hsqbound, hp, hsq, hscale, hstrict]

end LongTails.Proofs.AffineSoftmaxOuterBounds
