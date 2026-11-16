import LongTails.Proofs.QuasarHardProfiles
import LongTails.Proofs.FiniteSumNondualLowerGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace LongTails.Proofs.QuasarHardChain

open QuasarHardProfiles FiniteSumNondualLowerGeometry

noncomputable def linkEnergy (δ : ℝ) (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, deadZone δ (y j - y (j + 1)) ^ 2

noncomputable def chainValue (δ : ℝ) (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  ((y 0 - 1) ^ 2 + linkEnergy δ y k) / 4

noncomputable def bumpSum (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), bump (y i)

noncomputable def bumpPairing (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (y i - 1) * bumpSlope (y i)

noncomputable def chainPairing (δ : ℝ) (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  (y 0 - 1) ^ 2 / 2 +
    (∑ j ∈ Finset.range k, softThreshold δ (y j - y (j + 1)) * (y j - y (j + 1))) / 2

lemma deadZone_sq_le_soft_mul (δ t : ℝ) (hδ : 0 ≤ δ) :
    deadZone δ t ^ 2 ≤ softThreshold δ t * t := by
  simp only [deadZone, softThreshold, abs, max_def]
  split_ifs <;> nlinarith

lemma linkEnergy_nonneg (δ : ℝ) (y : ℕ → ℝ) (k : ℕ) : 0 ≤ linkEnergy δ y k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma chainValue_nonneg (δ : ℝ) (y : ℕ → ℝ) (k : ℕ) : 0 ≤ chainValue δ y k := by
  unfold chainValue
  have := linkEnergy_nonneg δ y k
  positivity

lemma chainPairing_ge (δ : ℝ) (hδ : 0 ≤ δ) (y : ℕ → ℝ) (k : ℕ) :
    2 * chainValue δ y k ≤ chainPairing δ y k := by
  have h : linkEnergy δ y k ≤
      ∑ j ∈ Finset.range k, softThreshold δ (y j - y (j + 1)) * (y j - y (j + 1)) :=
    Finset.sum_le_sum (fun j _ => deadZone_sq_le_soft_mul δ _ hδ)
  unfold chainValue chainPairing
  linarith

lemma bumpPairing_nonneg (y : ℕ → ℝ) (k : ℕ) : 0 ≤ bumpPairing y k :=
  Finset.sum_nonneg (fun i _ => bump_slope_sign (y i))

lemma bump_le_pairing (θ : ℝ) : bump θ ≤ 10 + 40 * ((θ - 1) * bumpSlope θ) := by
  have hs := bump_slope_sign θ
  by_cases h : 1 / 10 ≤ |θ|
  · have := bump_quasar h
    linarith
  · push Not at h
    have hl := neg_abs_le θ
    rcases le_or_gt θ (9 / 10) with h9 | h9
    · have := bump_le_ten (by linarith) h9
      linarith
    · have : 1 / 10 ≤ |θ| := by
        rw [abs_of_pos (by linarith)]; linarith
      linarith

lemma bumpSum_le (y : ℕ → ℝ) (k : ℕ) :
    bumpSum y k ≤ 10 * ((k : ℝ) + 1) + 40 * bumpPairing y k := by
  unfold bumpSum bumpPairing
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (k + 1)) => bump_le_pairing (y i))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  linarith

lemma bumpSum_le_of_far (y : ℕ → ℝ) (k : ℕ) (h : ∀ i ≤ k, 1 / 10 ≤ |y i|) :
    bumpSum y k ≤ 40 * bumpPairing y k := by
  unfold bumpSum bumpPairing
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have := bump_quasar (h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
  linarith

lemma telescope_deadZone (δ : ℝ) (y : ℕ → ℝ) (j m : ℕ) :
    y j - y (j + m) - (m : ℝ) * δ ≤
      ∑ i ∈ Finset.range m, deadZone δ (y (j + i) - y (j + i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have h₁ := abs_le_deadZone_add δ (y (j + m) - y (j + m + 1))
    have h₂ := le_abs_self (y (j + m) - y (j + m + 1))
    have he : j + (m + 1) = j + m + 1 := by ring
    rw [he]
    linarith

lemma window_energy (δ : ℝ) (y : ℕ → ℝ) (j m k : ℕ) (hjm : j + m ≤ k)
    (h : 0 ≤ y j - y (j + m) - (m : ℝ) * δ) :
    (y j - y (j + m) - (m : ℝ) * δ) ^ 2 ≤ (m : ℝ) * linkEnergy δ y k := by
  have ht := telescope_deadZone δ y j m
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m) (fun _ => (1 : ℝ))
    (fun i => deadZone δ (y (j + i) - y (j + i + 1)))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hc
  have hsub : (∑ i ∈ Finset.range m, deadZone δ (y (j + i) - y (j + i + 1)) ^ 2) ≤
      linkEnergy δ y k := by
    unfold linkEnergy
    have he : (∑ i ∈ Finset.range m, deadZone δ (y (j + i) - y (j + i + 1)) ^ 2) =
        ∑ i ∈ Finset.Ico j (j + m), deadZone δ (y i - y (i + 1)) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [add_tsub_cancel_left]
    rw [he]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      exact Finset.mem_range.mpr (by omega)
    · intro _ _ _; exact sq_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc _ ≤ (∑ i ∈ Finset.range m, deadZone δ (y (j + i) - y (j + i + 1))) ^ 2 :=
        pow_le_pow_left₀ h ht 2
    _ ≤ _ := hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hsub hm

lemma between_pairing (y : ℕ → ℝ) (k j m : ℕ) (hjm : j + m ≤ k)
    (h : ∀ i, j < i → i < j + m → 1 / 10 ≤ y i ∧ y i ≤ 9 / 10) :
    (m : ℝ) - 1 ≤ bumpPairing y k := by
  unfold bumpPairing
  have hs : (∑ i ∈ Finset.Ioo j (j + m), (1 : ℝ)) ≤
      ∑ i ∈ Finset.Ioo j (j + m), (y i - 1) * bumpSlope (y i) :=
    Finset.sum_le_sum (fun i hi => by
      simp only [Finset.mem_Ioo] at hi
      obtain ⟨a, b⟩ := h i hi.1 hi.2
      exact bump_middle_progress a b)
  have hsub : (∑ i ∈ Finset.Ioo j (j + m), (y i - 1) * bumpSlope (y i)) ≤
      ∑ i ∈ Finset.range (k + 1), (y i - 1) * bumpSlope (y i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_Ioo] at hi
      exact Finset.mem_range.mpr (by omega)
    · intro i _ _; exact bump_slope_sign (y i)
  simp only [Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul, mul_one] at hs
  have hc : (m : ℝ) - 1 ≤ ((j + m - j - 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp
    · have : j + m - j - 1 = m - 1 := by omega
      rw [this, Nat.cast_sub (by omega)]
      simp
  linarith

lemma transition_bound (δ s : ℝ) (y : ℕ → ℝ) (k : ℕ)
    (hδk : ((k : ℝ) + 1) * δ ≤ 1 / 100) (hs : 0 < s) (hs1 : s ≤ 1 / 100)
    (h0 : 9 / 10 ≤ y 0) (hex : ∃ i ≤ k, y i < 1 / 10) :
    s / 10 ≤ 199 / 100 * chainValue δ y k + 3 / 5 * s ^ 2 * bumpPairing y k := by
  classical
  have hexN : ∃ i, i ≤ k ∧ y i < 1 / 10 := hex
  set K := Nat.find hexN with hKdef
  have hK : K ≤ k ∧ y K < 1 / 10 := Nat.find_spec hexN
  have hKmin : ∀ i < K, ¬ (i ≤ k ∧ y i < 1 / 10) := fun i hi => Nat.find_min hexN hi
  have hKpos : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · have h2 := hK.2
      rw [h] at h2
      linarith
    · exact h
  set J := Nat.findGreatest (fun i => 9 / 10 ≤ y i) (K - 1) with hJdef
  have hJle : J ≤ K - 1 := Nat.findGreatest_le _
  have hJ : 9 / 10 ≤ y J := by
    have := Nat.findGreatest_spec (P := fun i => 9 / 10 ≤ y i) (Nat.zero_le (K - 1)) h0
    exact this
  set m := K - J with hmdef
  have hm1 : 1 ≤ m := by omega
  have hJm : J + m = K := by omega
  have hmk : J + m ≤ k := by omega
  have hyK : y (J + m) < 1 / 10 := by rw [hJm]; exact hK.2
  have hbetween : ∀ i, J < i → i < J + m → 1 / 10 ≤ y i ∧ y i ≤ 9 / 10 := by
    intro i hi1 hi2
    constructor
    · by_contra hc
      push Not at hc
      exact hKmin i (by omega) ⟨by omega, hc⟩
    · by_contra hc
      push Not at hc
      have := Nat.le_findGreatest (P := fun i => 9 / 10 ≤ y i) (show i ≤ K - 1 by omega) hc.le
      omega
  have hP := between_pairing y k J m hmk hbetween
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmδ : (m : ℝ) * δ ≤ 1 / 100 := by
    have : (m : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast (show m ≤ k + 1 by omega)
    nlinarith
  have hdiff : 79 / 100 ≤ y J - y (J + m) - (m : ℝ) * δ := by linarith
  have hE := window_energy δ y J m k hmk (by linarith)
  have hsq : (79 / 100 : ℝ) ^ 2 ≤ (y J - y (J + m) - (m : ℝ) * δ) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hdiff 2
  have hQ : (79 / 100 : ℝ) ^ 2 / 4 ≤ (m : ℝ) * chainValue δ y k := by
    unfold chainValue
    nlinarith [sq_nonneg (y 0 - 1)]
  have hPn := bumpPairing_nonneg y k
  have hCn := chainValue_nonneg δ y k
  have key : s * m / 10 ≤ 199 / 100 * (m * chainValue δ y k) +
      3 / 5 * s ^ 2 * m * ((m : ℝ) - 1) := by
    nlinarith [sq_nonneg (s * m - 1 / 10), mul_pos hs (by linarith : (0 : ℝ) < m)]
  have hmpos : (0 : ℝ) < m := by linarith
  have h2 : 3 / 5 * s ^ 2 * m * ((m : ℝ) - 1) ≤ 3 / 5 * s ^ 2 * m * bumpPairing y k := by
    apply mul_le_mul_of_nonneg_left hP; positivity
  have h3 : m * (s / 10) ≤ m * (199 / 100 * chainValue δ y k + 3 / 5 * s ^ 2 * bumpPairing y k) := by
    nlinarith
  exact le_of_mul_le_mul_left h3 hmpos

lemma quasar_normalized (δ s : ℝ) (y : ℕ → ℝ) (k : ℕ) (hδ : 0 ≤ δ)
    (hδk : ((k : ℝ) + 1) * δ ≤ 1 / 100) (hs : 0 < s) (hs1 : s ≤ 1 / 100)
    (hT : 1 ≤ ((k : ℝ) + 1) * s) :
    (chainValue δ y k + s ^ 2 * bumpSum y k) / (100 * (((k : ℝ) + 1) * s)) ≤
      chainPairing δ y k + s ^ 2 * bumpPairing y k := by
  have hTs : 0 < ((k : ℝ) + 1) * s := by linarith
  have hD := mul_pos (by norm_num : (0 : ℝ) < 100) hTs
  have hpair := chainPairing_ge δ hδ y k
  have hQ := chainValue_nonneg δ y k
  have hP := bumpPairing_nonneg y k
  rw [div_le_iff₀ hD]
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  by_cases hfar : ∀ i ≤ k, 1 / 10 ≤ |y i|
  · have hB := bumpSum_le_of_far y k hfar
    nlinarith [mul_le_mul_of_nonneg_left hB hs2, mul_nonneg hs2 hP]
  · push Not at hfar
    obtain ⟨i, hik, hi⟩ := hfar
    have hB := bumpSum_le y k
    have hBs := mul_le_mul_of_nonneg_left hB hs2
    have hsT : s ^ 2 * (10 * ((k : ℝ) + 1)) * 100 = 1000 * s * (((k : ℝ) + 1) * s) := by ring
    by_cases hy0 : |y 0 - 1| < 1 / 10
    · have h0 : 9 / 10 ≤ y 0 := by
        have := neg_abs_le (y 0 - 1); linarith
      have hex : ∃ i ≤ k, y i < 1 / 10 := ⟨i, hik, by
        have := le_abs_self (y i); linarith⟩
      have ht := transition_bound δ s y k hδk hs hs1 h0 hex
      nlinarith [mul_nonneg hs2 hP, mul_le_mul_of_nonneg_right ht hTs.le]
    · push Not at hy0
      have hq : 1 / 400 ≤ chainValue δ y k := by
        unfold chainValue
        have := linkEnergy_nonneg δ y k
        have hsq : (1 / 10 : ℝ) ^ 2 ≤ (y 0 - 1) ^ 2 := by
          have h2 := pow_le_pow_left₀ (by norm_num) hy0 2
          rwa [sq_abs] at h2
        linarith
      nlinarith [mul_nonneg hs2 hP, mul_le_mul_of_nonneg_right hq hTs.le]

lemma convex_normalized (δ : ℝ) (y : ℕ → ℝ) (k : ℕ) (hδ : 0 ≤ δ) :
    chainValue δ y k ≤ chainPairing δ y k := by
  have := chainPairing_ge δ hδ y k
  have := chainValue_nonneg δ y k
  linarith

lemma chainValue_gap (δ : ℝ) (y : ℕ → ℝ) (k K : ℕ) (hK : K ≤ k)
    (h : 0 ≤ 1 - |y K| - (K : ℝ) * δ) :
    (1 - |y K| - (K : ℝ) * δ) ^ 2 ≤ 4 * ((K : ℝ) + 1) * chainValue δ y k := by
  have he := chain_energy δ 1 y K h
  have hsub : (∑ j ∈ Finset.range K, deadZone δ (y j - y (j + 1)) ^ 2) ≤ linkEnergy δ y k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hK) (fun _ _ _ => sq_nonneg _)
  have hz : (1 - y 0) ^ 2 = (y 0 - 1) ^ 2 := by ring
  rw [hz] at he
  unfold chainValue
  have hK0 : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsub hK0]

lemma bumpSum_gap (y : ℕ → ℝ) (k K : ℕ)
    (h : ∀ i, K ≤ i → i ≤ k → |y i| ≤ 1 / 20) :
    ((k : ℝ) + 1 - K) * (35 / 4) ≤ bumpSum y k := by
  unfold bumpSum
  have hs : (∑ i ∈ Finset.Ico K (k + 1), (35 / 4 : ℝ)) ≤
      ∑ i ∈ Finset.range (k + 1), bump (y i) := by
    calc _ = ∑ i ∈ Finset.Ico K (k + 1), bump (y i) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_Ico] at hi
          rw [bump_flat_value (h i hi.1 (by omega))]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (fun i hi => Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
          (fun i _ _ => bump_nonneg (y i))
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hs
  rcases le_or_gt K (k + 1) with hK | hK
  · rw [Nat.cast_sub hK] at hs
    push_cast at hs
    linarith
  · have : ((k : ℝ) + 1 - K) ≤ 0 := by
      have : ((k + 1 : ℕ) : ℝ) < K := by exact_mod_cast hK
      push_cast at this; linarith
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (k + 1)) => bump_nonneg (y i))
    nlinarith

end LongTails.Proofs.QuasarHardChain
