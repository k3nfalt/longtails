import LongTails.Proofs.HomotopyNewtonSchedule

namespace LongTails.Proofs.PointwiseHessianCounting

lemma capped_growth_formula {L q : ℝ} (hL : 0 ≤ L) (hq : 1 ≤ q)
    (b : ℕ → ℝ) (hb : b 0 ≤ L) (n : ℕ) (hs : ∀ k < n, b (k + 1) = min L (b k * q)) :
    b n = min L (b 0 * q ^ n) := by
  induction n with
  | zero => simp [min_eq_right hb]
  | succ n ih =>
    rw [hs n (by omega), ih (fun k hk => hs k (by omega)), min_mul_of_nonneg _ _ (by linarith : 0 ≤ q), ← min_assoc]
    have hh : L ≤ L * q := by nlinarith
    rw [min_eq_left hh, pow_succ]
    congr 1
    ring

lemma capped_growth_count {L q : ℝ} (hL : 0 < L) (hq : 1 < q)
    (b : ℕ → ℝ) (hb : 0 < b 0) (hbL : b 0 ≤ L)
    {n : ℕ} (hs : ∀ k < n, b (k + 1) = min L (b k * q)) (hn : b n < L) :
    (n : ℝ) < Real.log (L / b 0) / Real.log q := by
  have he := capped_growth_formula hL.le hq.le b hbL n hs
  have hp : b 0 * q ^ n < L := by
    rw [he] at hn
    exact (min_lt_iff.mp hn).resolve_left (lt_irrefl _)
  have hpow : q ^ n < L / b 0 := (lt_div_iff₀ hb).mpr (by nlinarith)
  have hl := Real.log_lt_log (pow_pos (by linarith : 0 < q) n) hpow
  rw [Real.log_pow] at hl
  exact (lt_div_iff₀ (Real.log_pos hq)).mpr hl

lemma continuation_growth_count {L a : ℝ} (hL : 0 < L) (ha : 0 < a) (ha1 : a ≤ 1)
    (b : ℕ → ℝ) (hb : 0 < b 0) (hbL : b 0 ≤ L)
    {n : ℕ} (hs : ∀ k < n, b (k + 1) = min L (b k * (1 + a / 8)))
    (hn : b n < L) : (n : ℝ) < (16 / a) * Real.log (L / b 0) := by
  have hh := capped_growth_count hL (by linarith : 1 < 1 + a / 8) b hb hbL hs hn
  have hlog : a / 16 ≤ Real.log (1 + a / 8) := by
    have hl := HomotopyNewtonSchedule.log_one_add_ge
      (show 0 ≤ a / 8 by positivity) (show a / 8 ≤ 1 by linarith)
    linarith
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_left hlog hn0
  have hh' := (lt_div_iff₀ (Real.log_pos (show 1 < 1 + a / 8 by linarith))).mp hh
  have ht : (n : ℝ) * a < 16 * Real.log (L / b 0) := by linarith
  have he : (16 / a) * Real.log (L / b 0) = (16 * Real.log (L / b 0)) / a := by ring
  rw [he]
  exact (lt_div_iff₀ ha).mpr ht

lemma contraction_formula (e : ℕ → ℝ) (n : ℕ) (hs : ∀ k < n, e (k + 1) ≤ e k / 4) :
    e n ≤ e 0 / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      e (n + 1) ≤ e n / 4 := hs n (by omega)
      _ ≤ (e 0 / 4 ^ n) / 4 := div_le_div_of_nonneg_right (ih (fun k hk => hs k (by omega))) (by norm_num)
      _ = e 0 / 4 ^ (n + 1) := by rw [pow_succ]; ring

lemma contraction_count (e : ℕ → ℝ) {n : ℕ} (hs : ∀ k < n, e (k + 1) ≤ e k / 4)
    {t : ℝ} (ht : 0 < t) (hn : t < e n) :
    (n : ℝ) < Real.log (e 0 / t) / Real.log 4 := by
  have hh := hn.trans_le (contraction_formula e n hs)
  have hp : 0 < (4 : ℝ) ^ n := by positivity
  have hm := (lt_div_iff₀ hp).mp hh
  have he : (4 : ℝ) ^ n < e 0 / t :=
    (lt_div_iff₀ ht).mpr (by nlinarith)
  have hl := Real.log_lt_log hp he
  rw [Real.log_pow] at hl
  exact (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 4))).mpr hl

lemma selected_log_count (A : ℕ → ℝ) (S : Finset ℕ) (N : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hS : S ⊆ Finset.range N)
    (hpos : ∀ i ≤ N, 0 < A i) (hmono : ∀ i < N, A i ≤ A (i + 1))
    (hstep : ∀ i ∈ S, 1 ≤ C * (Real.log (A (i + 1)) - Real.log (A i))) :
    (S.card : ℝ) ≤ C * (Real.log (A N) - Real.log (A 0)) := by
  have hn (i : ℕ) (hi : i ∈ Finset.range N) :
      0 ≤ Real.log (A (i + 1)) - Real.log (A i) := by
    have hl : i < N := Finset.mem_range.mp hi
    exact sub_nonneg.mpr (Real.log_le_log (hpos i (by omega)) (hmono i hl))
  calc
    (S.card : ℝ) = ∑ _i ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ S, C * (Real.log (A (i + 1)) - Real.log (A i)) := Finset.sum_le_sum hstep
    _ ≤ ∑ i ∈ Finset.range N, C * (Real.log (A (i + 1)) - Real.log (A i)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun i hi _ => mul_nonneg hC (hn i hi))
    _ = C * (Real.log (A N) - Real.log (A 0)) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => Real.log (A i)) N]

lemma shift_potential {x x' c d : ℝ}
    (hstep : |x' - x| ≤ c + d) : |x'| - |x| ≤ c + d := by
  have hh := abs_add_le (x' - x) x
  rw [sub_add_cancel] at hh
  linarith

lemma downward_potential {x x' c d : ℝ} (hd : 0 ≤ d) (hx : c ≤ x)
    (hstep : x' = x - c + d) : |x'| - |x| ≤ -c + d := by
  have hh := abs_add_le (x - c) d
  rw [abs_of_nonneg (sub_nonneg.mpr hx), abs_of_nonneg hd, ← hstep] at hh
  linarith [le_abs_self x]

lemma upward_potential {x x' c d : ℝ} (hd : 0 ≤ d) (hx : x ≤ -c)
    (hstep : x' = x + c + d) : |x'| - |x| ≤ -c + d := by
  have hh := abs_add_le (x + c) d
  rw [abs_of_nonpos (by linarith : x + c ≤ 0), abs_of_nonneg hd, ← hstep] at hh
  linarith [neg_le_abs x]

lemma potential_count (P D : ℕ → ℝ) (good : ℕ → Bool) {c : ℝ} (N : ℕ)
    (hP : 0 ≤ P N)
    (hstep : ∀ i < N, P (i + 1) - P i ≤
      (if good i then c else -c) + (D i - D (i + 1))) :
    (N : ℝ) * c ≤ 2 * c * (∑ i ∈ Finset.range N, if good i then (1 : ℝ) else 0) +
      P 0 + D 0 - D N := by
  have haux (n : ℕ) (hn : n ≤ N) :
      P n + (n : ℝ) * c ≤ 2 * c * (∑ i ∈ Finset.range n, if good i then (1 : ℝ) else 0) +
        P 0 + D 0 - D n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hi := ih (by omega)
      have hs := hstep n (by omega)
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      cases hg : good n <;> simp only [hg, Bool.false_eq_true, ↓reduceIte] at hs ⊢ <;> linarith
  have hh := haux N le_rfl
  linarith

noncomputable def level (D A : ℝ) : ℝ := max 1 ((D * A) ^ (2 / 7 : ℝ))

noncomputable def threshold (D A : ℝ) : ℝ := level D A ^ 2 / A

lemma level_pos (D A : ℝ) : 0 < level D A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

lemma level_mono {D A B : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) (hAB : A ≤ B) :
    level D A ≤ level D B := by
  apply max_le_max le_rfl
  exact Real.rpow_le_rpow (mul_nonneg hD hA) (mul_le_mul_of_nonneg_left hAB hD) (by norm_num)

lemma level_seventh {D A : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) : (D * A) ^ 2 ≤ level D A ^ 7 := by
  have he : ((D * A) ^ (2 / 7 : ℝ)) ^ (7 : ℕ) = (D * A) ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast (mul_nonneg hD hA)]
    norm_num
  rw [← he]
  exact pow_le_pow_left₀ (Real.rpow_nonneg (mul_nonneg hD hA) _)
    (le_max_right _ _) 7

lemma threshold_pos {D A : ℝ} (hA : 0 < A) : 0 < threshold D A :=
  div_pos (sq_pos_of_pos (level_pos D A)) hA

lemma rejection_charge {D A F η : ℝ} (hD : 0 ≤ D) (hA : 0 < A)
    (hF : level D A ≤ F) (hη : threshold D A / 2 ≤ η) : D ^ 2 ≤ 8 * F * A * η ^ 3 := by
  have hFp : 0 < F := (level_pos D A).trans_le hF
  have hηp : 0 < η := (half_pos (threshold_pos hA)).trans_le hη
  have hsq : level D A ^ 2 ≤ 2 * A * η := by
    unfold threshold at hη
    have hh := (div_le_iff₀ hA).mp (show level D A ^ 2 / A ≤ 2 * η by linarith)
    nlinarith
  have hc := pow_le_pow_left₀ (sq_nonneg (level D A)) hsq 3
  have hm := mul_le_mul_of_nonneg_left hc hFp.le
  have h7 := level_seventh hD hA.le
  have hlevel := mul_le_mul_of_nonneg_right hF (pow_nonneg (level_pos D A).le 6)
  have hh : A ^ 2 * D ^ 2 ≤ A ^ 2 * (8 * F * A * η ^ 3) := by
    nlinarith only [hm, h7, hlevel]
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hA)).mp hh

lemma level_square {D A : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) :
    level D A ^ 2 = max 1 ((D * A) ^ (4 / 7 : ℝ)) := by
  unfold level
  rw [← Real.rpow_two, Real.rpow_max zero_le_one
    (Real.rpow_nonneg (mul_nonneg hD hA) _) (by norm_num), Real.one_rpow,
    ← Real.rpow_mul (mul_nonneg hD hA)]
  norm_num

lemma threshold_formula {D A : ℝ} (hD : 0 ≤ D) (hA : 0 < A) :
    threshold D A = max (1 / A) (D ^ (4 / 7 : ℝ) / A ^ (3 / 7 : ℝ)) := by
  unfold threshold
  rw [level_square hD hA.le, ← max_div_div_right hA.le]
  congr 1
  rw [Real.mul_rpow hD hA.le, mul_div_assoc, ← Real.rpow_sub_one hA.ne']
  norm_num
  rw [Real.rpow_neg hA.le]
  rfl

lemma threshold_antitone {D A B : ℝ} (hD : 0 ≤ D) (hA : 0 < A) (hAB : A ≤ B) :
    threshold D B ≤ threshold D A := by
  have hB := hA.trans_le hAB
  rw [threshold_formula hD hA, threshold_formula hD hB]
  apply max_le_max
  · exact one_div_le_one_div_of_le hA hAB
  · exact div_le_div_of_nonneg_left (Real.rpow_nonneg hD _)
      (Real.rpow_pos_of_pos hA _) (Real.rpow_le_rpow hA.le hAB (by norm_num))

lemma threshold_log_variation {D A B : ℝ} (hD : 0 ≤ D) (hA : 0 < A) (hAB : A ≤ B) :
    0 ≤ Real.log (threshold D A) - Real.log (threshold D B) ∧
      Real.log (threshold D A) - Real.log (threshold D B) ≤ Real.log B - Real.log A := by
  have hB := hA.trans_le hAB
  have htA : 0 < threshold D A := threshold_pos hA
  have htB : 0 < threshold D B := threshold_pos hB
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log htB (threshold_antitone hD hA hAB))
  · have hh : A * threshold D A ≤ B * threshold D B := by
      have hm := pow_le_pow_left₀ (level_pos D A).le (level_mono hD hA.le hAB) 2
      simpa only [threshold, mul_div_cancel₀ _ hA.ne', mul_div_cancel₀ _ hB.ne'] using hm
    have hl := Real.log_le_log (mul_pos hA htA) hh
    rw [Real.log_mul hA.ne' htA.ne', Real.log_mul hB.ne' htB.ne'] at hl
    linarith

lemma full_log_potential {D A B η : ℝ} (hD : 0 ≤ D) (hA : 0 < A)
    (hAB : A ≤ B) (hη : 0 < η) :
    |Real.log (η / 2) - Real.log (threshold D B)| -
      |Real.log η - Real.log (threshold D A)| ≤
      (if η ≤ 2 * threshold D A then Real.log 2 else -Real.log 2) +
        (Real.log (threshold D A) - Real.log (threshold D B)) := by
  have hd := (threshold_log_variation hD hA hAB).1
  have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : Real.log (η / 2) - Real.log (threshold D B) =
      (Real.log η - Real.log (threshold D A)) - Real.log 2 +
        (Real.log (threshold D A) - Real.log (threshold D B)) := by
    rw [Real.log_div hη.ne' (by norm_num)]
    ring
  split_ifs with hg
  · apply shift_potential
    rw [he]
    apply abs_le.mpr
    constructor <;> linarith
  · apply downward_potential hd _ he
    have hh := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 2) (threshold_pos hA))
      (le_of_not_ge hg)
    rw [Real.log_mul (by norm_num) (threshold_pos hA).ne'] at hh
    linarith

lemma damped_log_potential {D A B η : ℝ} (hD : 0 ≤ D) (hA : 0 < A)
    (hAB : A ≤ B) (hη : 0 < η) :
    |Real.log (2 * η) - Real.log (threshold D B)| -
      |Real.log η - Real.log (threshold D A)| ≤
      (if threshold D A / 2 ≤ η then Real.log 2 else -Real.log 2) +
        (Real.log (threshold D A) - Real.log (threshold D B)) := by
  have hd := (threshold_log_variation hD hA hAB).1
  have hc : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : Real.log (2 * η) - Real.log (threshold D B) =
      (Real.log η - Real.log (threshold D A)) + Real.log 2 +
        (Real.log (threshold D A) - Real.log (threshold D B)) := by
    rw [Real.log_mul (by norm_num) hη.ne']
    ring
  split_ifs with hg
  · apply shift_potential
    rw [he]
    apply abs_le.mpr
    constructor <;> linarith
  · apply upward_potential hd _ he
    have hh := Real.log_le_log hη (le_of_not_ge hg)
    rw [Real.log_div (threshold_pos hA).ne' (by norm_num)] at hh
    linarith

lemma initial_log_potential {D A : ℝ} (hD : 0 ≤ D) (hA : 0 < A) :
    |Real.log (1 / A) - Real.log (threshold D A)| ≤ (4 / 7 : ℝ) * Real.log (1 + D * A) := by
  have hDA : 0 ≤ D * A := mul_nonneg hD hA.le
  have hL : 0 < level D A := level_pos D A
  have hL1 : 1 ≤ level D A := le_max_left _ _
  have hlogL : 0 ≤ Real.log (level D A) := Real.log_nonneg hL1
  have he : Real.log (1 / A) - Real.log (threshold D A) = -2 * Real.log (level D A) := by
    unfold threshold
    rw [Real.log_div one_ne_zero hA.ne', Real.log_one,
      Real.log_div (pow_ne_zero 2 hL.ne') hA.ne', Real.log_pow]
    ring
  rw [he, abs_of_nonpos (by nlinarith)]
  have hb : level D A ≤ (1 + D * A) ^ (2 / 7 : ℝ) := by
    apply max_le
    · exact Real.one_le_rpow (by linarith) (by norm_num)
    · exact Real.rpow_le_rpow hDA (by linarith) (by norm_num)
  have hl := Real.log_le_log hL hb
  rw [Real.log_rpow (by positivity)] at hl
  linarith

lemma doubled_radius_ledger {S r : ℝ} (hS : S ≤ (4 / 3 : ℝ) * r ^ 2) :
    S + (2 * r) ^ 2 ≤ (4 / 3 : ℝ) * (2 * r) ^ 2 := by nlinarith

lemma clipped_radius_ledger {S r cap : ℝ} (hr : 0 ≤ r) (hrc : r ≤ cap)
    (hS : S ≤ (4 / 3 : ℝ) * r ^ 2) : S + cap ^ 2 ≤ 3 * cap ^ 2 := by
  have hh := pow_le_pow_left₀ hr hrc 2
  nlinarith [sq_nonneg cap]

lemma completed_radius_ledger {r cap d S : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ cap)
    (hrd : r ≤ 6 * d) (hcd : cap ≤ 6 * d) (hS : S ≤ 3 * r ^ 2 + 4 * cap ^ 2) :
    S ≤ 252 * d ^ 2 := by
  have hh := pow_le_pow_left₀ hr hrd 2
  have hh' := pow_le_pow_left₀ hc hcd 2
  nlinarith

lemma open_radius_ledger {S cap R : ℝ} (hc : 0 ≤ cap) (hcR : cap ≤ 16 * R)
    (hS : S ≤ 7 * cap ^ 2) : S ≤ 1792 * R ^ 2 := by
  have hh := pow_le_pow_left₀ hc hcR 2
  nlinarith

end LongTails.Proofs.PointwiseHessianCounting
