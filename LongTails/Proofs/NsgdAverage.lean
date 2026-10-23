import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

namespace LongTails.Proofs.NsgdAverage

lemma quartic_le {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 / a - u ^ 4 / (4 * a ^ 3) ≤ u := by
  rw [div_sub_div _ _ ha.ne' (by positivity), div_le_iff₀ (by positivity)]
  have key : 0 ≤ u * (u * (u - a) ^ 2 + a * (2 * (u - 5 * a / 4) ^ 2 + 7 * a ^ 2 / 8)) :=
    mul_nonneg hu (add_nonneg (mul_nonneg hu (sq_nonneg _)) (mul_nonneg ha.le (by positivity)))
  nlinarith [mul_nonneg ha.le key]

lemma abs_ge_quartic {a : ℝ} (ha : 0 < a) (M : ℝ) :
    M ^ 2 / a - M ^ 4 / (4 * a ^ 3) ≤ |M| := by
  have h2 : M ^ 2 = |M| ^ 2 := (sq_abs M).symm
  have h4 : M ^ 4 = |M| ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [h2, h4]
  exact quartic_le ha (abs_nonneg M)

lemma shifted_le {m : ℕ → ℝ} (hm : ∀ j, 0 ≤ m j) {n i N : ℕ} (h : i + n ≤ N) :
    ∑ t ∈ Finset.range n, m (t + i) ≤ ∑ j ∈ Finset.range N, m j := by
  have he : ∑ t ∈ Finset.range n, m (t + i) = ∑ j ∈ Finset.Ico i (i + n), m j := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    exact Finset.sum_congr rfl fun t _ => by rw [add_comm]
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
    omega
  · intro j _ _
    exact hm j

lemma window_average {m : ℕ → ℝ} (hm : ∀ j, 0 ≤ m j) {T k : ℕ} (hk : k ≤ T) {A q : ℝ}
    (hq : 0 ≤ q)
    (h : ∀ t, t + k ≤ T → A - q * ∑ i ∈ Finset.range k, m (t + i) ≤ m t + m (t + k)) :
    ((T + 1 - k : ℕ) : ℝ) * A ≤ (2 + q * k) * ∑ j ∈ Finset.range (T + 1), m j := by
  set S := ∑ j ∈ Finset.range (T + 1), m j
  have hsum := Finset.sum_le_sum (s := Finset.range (T + 1 - k))
    (fun t ht => h t (by simp only [Finset.mem_range] at ht; omega))
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have h1 : ∑ t ∈ Finset.range (T + 1 - k), m t ≤ S := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro j _ _
      exact hm j
  have h2 : ∑ t ∈ Finset.range (T + 1 - k), m (t + k) ≤ S := shifted_le hm (by omega)
  have h3 : ∑ t ∈ Finset.range (T + 1 - k), ∑ i ∈ Finset.range k, m (t + i) ≤ k * S := by
    rw [Finset.sum_comm]
    calc ∑ i ∈ Finset.range k, ∑ t ∈ Finset.range (T + 1 - k), m (t + i) ≤
          ∑ _i ∈ Finset.range k, S := by
            apply Finset.sum_le_sum
            intro i hi
            simp only [Finset.mem_range] at hi
            exact shifted_le hm (by omega)
      _ = k * S := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h4 := mul_le_mul_of_nonneg_left h3 hq
  nlinarith

lemma floor_half {x : ℝ} (hx : 1 ≤ x) : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  linarith

lemma regime_time {ℓ c σ η θ ε Λ μ : ℝ} {T : ℕ} (hℓ : 0 < ℓ) (hc : 0 < c) (hσ : 0 < σ)
    (hη : 0 < η) (hθ : 0 < θ) (hε : 0 < ε) (hΛ : 0 < Λ) (hμ : 0 ≤ μ)
    (htr : θ / 2 ≤ T * (η * c * (Λ / σ))) (hst : ℓ * μ ≤ ε) (hkick : 1 ≤ T → 7 / 50 * η ≤ μ)
    (hwin : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ T + 1 →
      η * Real.sqrt k / 120 ≤ μ * (2 + 6 / 7 * (η * ℓ / σ) * k))
    (hF3 : 4 * c * Λ ≤ θ * ℓ) :
    θ * ℓ * σ ^ 2 ≤ 490000 * ε ^ 2 * c * Λ * T := by
  have htr' : θ * σ ≤ 2 * T * η * c * Λ := by
    rw [mul_div_assoc', mul_div_assoc', le_div_iff₀ hσ] at htr
    nlinarith
  have hT : 1 ≤ T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · subst h
      simp at htr'
      nlinarith [mul_pos hθ hσ]
    · exact h
  have hηℓ : 7 * (η * ℓ) ≤ 50 * ε := by nlinarith [hkick hT]
  have hbase : θ * ℓ * σ ^ 2 ≤ 2 * T * c * Λ * σ * (η * ℓ) := by
    have := mul_le_mul_of_nonneg_left htr' (mul_nonneg hℓ.le hσ.le)
    nlinarith
  have hTcΛ : 0 ≤ (T : ℝ) * c * Λ := by positivity
  by_cases hmid : σ ≤ 30 * ε
  · have : σ * (η * ℓ) ≤ 30 * ε * (50 * ε / 7) :=
      mul_le_mul hmid (by linarith) (by positivity) (by positivity)
    nlinarith
  push Not at hmid
  set κ := η * ℓ / σ with hκ
  have hκpos : 0 < κ := by positivity
  have hκ1 : κ < 1 := by
    rw [hκ, div_lt_one hσ]
    nlinarith
  set K := ⌊1 / κ⌋₊ with hK
  have hKκ : (K : ℝ) * κ ≤ 1 := by
    have := Nat.floor_le (show 0 ≤ 1 / κ by positivity)
    rw [← hK] at this
    rw [le_div_iff₀ hκpos] at this
    linarith
  have hgain (k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2 * k ≤ T + 1) (hkK : k ≤ K) :
      49 * η ^ 2 * k ≤ 2400 ^ 2 * μ ^ 2 := by
    have hw := hwin k hk1 hk2
    have hkκ : (k : ℝ) * κ ≤ 1 := by
      have : (k : ℝ) ≤ K := by exact_mod_cast hkK
      nlinarith
    have hfac : μ * (2 + 6 / 7 * κ * k) ≤ μ * (20 / 7) := by
      apply mul_le_mul_of_nonneg_left _ hμ
      nlinarith
    have hroot : 7 * η * Real.sqrt k ≤ 2400 * μ := by
      linarith
    have hsq := mul_self_le_mul_self (by positivity) hroot
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hs : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk0
    nlinarith
  have hε2 : ℓ ^ 2 * μ ^ 2 ≤ ε ^ 2 := by
    have := mul_self_le_mul_self (mul_nonneg hℓ.le hμ) hst
    nlinarith
  by_cases hbranch : 2 * K ≤ T + 1
  · have hK1 : 1 ≤ K := by
      apply Nat.le_floor
      rw [Nat.cast_one, le_div_iff₀ hκpos]
      linarith
    have hg := hgain K hK1 hbranch le_rfl
    have hhalf : 1 / κ ≤ 2 * (K : ℝ) := floor_half (by rw [le_div_iff₀ hκpos]; linarith)
    have hKσ : σ ≤ 2 * K * (η * ℓ) := by
      rw [div_le_iff₀ hκpos, hκ] at hhalf
      rw [mul_div_assoc'] at hhalf
      rw [le_div_iff₀ hσ] at hhalf
      nlinarith
    have hprod : 49 * (η * ℓ) * σ ≤ 2 * 2400 ^ 2 * ε ^ 2 := by
      have h1 : 49 * η ^ 2 * K * ℓ ^ 2 ≤ 2400 ^ 2 * ε ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hKσ (by positivity : (0 : ℝ) ≤ 49 * η * ℓ)]
    nlinarith
  · push Not at hbranch
    set k := (T + 1) / 2 with hkdef
    have hk1 : 1 ≤ k := by omega
    have hk2 : 2 * k ≤ T + 1 := by omega
    have hkK : k ≤ K := by omega
    have hg := hgain k hk1 hk2 hkK
    have hkT : (T : ℝ) ≤ 2 * k := by
      have : T ≤ 2 * k := by omega
      exact_mod_cast this
    have hηT : 49 * ℓ ^ 2 * η ^ 2 * T ≤ 2 * 2400 ^ 2 * ε ^ 2 := by
      have a1 : 49 * ℓ ^ 2 * η ^ 2 * T ≤ 49 * ℓ ^ 2 * η ^ 2 * (2 * k) :=
        mul_le_mul_of_nonneg_left hkT (by positivity)
      have a2 : ℓ ^ 2 * (49 * η ^ 2 * k) ≤ ℓ ^ 2 * (2400 ^ 2 * μ ^ 2) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      linarith [a1, a2, hε2]
    have hθη : (θ * σ) ^ 2 ≤ (2 * T * c * Λ) ^ 2 * η ^ 2 := by
      have := mul_self_le_mul_self (by positivity) htr'
      calc (θ * σ) ^ 2 = (θ * σ) * (θ * σ) := by ring
        _ ≤ (2 * T * η * c * Λ) * (2 * T * η * c * Λ) := this
        _ = (2 * T * c * Λ) ^ 2 * η ^ 2 := by ring
    have hfin : 49 * (θ * ℓ) ^ 2 * σ ^ 2 ≤ 8 * 2400 ^ 2 * ε ^ 2 * c ^ 2 * Λ ^ 2 * T := by
      have h1 : 49 * ℓ ^ 2 * (θ * σ) ^ 2 ≤ 49 * ℓ ^ 2 * ((2 * T * c * Λ) ^ 2 * η ^ 2) :=
        mul_le_mul_of_nonneg_left hθη (by positivity)
      have h2 := mul_le_mul_of_nonneg_left hηT (by positivity : (0 : ℝ) ≤ 4 * T * c ^ 2 * Λ ^ 2)
      calc 49 * (θ * ℓ) ^ 2 * σ ^ 2 = 49 * ℓ ^ 2 * (θ * σ) ^ 2 := by ring
        _ ≤ 49 * ℓ ^ 2 * ((2 * T * c * Λ) ^ 2 * η ^ 2) := h1
        _ = 4 * T * c ^ 2 * Λ ^ 2 * (49 * ℓ ^ 2 * η ^ 2 * T) := by ring
        _ ≤ 4 * T * c ^ 2 * Λ ^ 2 * (2 * 2400 ^ 2 * ε ^ 2) := h2
        _ = 8 * 2400 ^ 2 * ε ^ 2 * c ^ 2 * Λ ^ 2 * T := by ring
    have hθℓ : 0 < θ * ℓ := by positivity
    by_contra hcon
    push Not at hcon
    have h3 : 490000 * ε ^ 2 * c * Λ * T * (4 * c * Λ) ≤ 490000 * ε ^ 2 * c * Λ * T * (θ * ℓ) :=
      mul_le_mul_of_nonneg_left hF3 (by positivity)
    have h4 : 490000 * ε ^ 2 * c * Λ * T * (θ * ℓ) < θ * ℓ * σ ^ 2 * (θ * ℓ) :=
      mul_lt_mul_of_pos_right hcon hθℓ
    have hM : 0 ≤ ε ^ 2 * c ^ 2 * Λ ^ 2 * T := by positivity
    linarith

end LongTails.Proofs.NsgdAverage
