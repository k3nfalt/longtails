import LongTails.Proofs.ComponentEnvelopeWarmup
open scoped BigOperators
namespace OracleTemplate.ComponentEnvelope

lemma epoch_accumulated (G D : ℕ → ℝ) (a b c δ : ℝ) (K : ℕ)
    (hstep : ∀ j < K, G (j + 1) + c * D (j + 1) ≤ a * G j + b + c * D j + δ) :
    (1 - a) * (∑ j ∈ Finset.range K, G (j + 1)) + a * G K + c * D K ≤
      a * G 0 + K * (b + δ) + c * D 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hprev := ih (fun j hj => hstep j (by omega))
      have hnext := hstep K (by omega)
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      nlinarith

lemma epoch_output_last_le (G : ℕ → ℝ) (K : ℕ) (hK : 0 < K)
    (hG : ∀ j, 0 ≤ G j) : G K ≤ ∑ j ∈ Finset.range K, G (j + 1) := by
  have hh := Finset.single_le_sum (f := fun j => G (j + 1))
    (fun j _ => hG (j + 1)) (Finset.mem_range.mpr (show K - 1 < K by omega))
  simpa [Nat.sub_add_cancel hK] using hh

lemma epoch_potential_bounds {τ μ sum last D P : ℝ} (hτ : 0 < τ) (hτu : τ ≤ 1 / 2)
    (hμ : 0 ≤ μ) (hlast : 0 ≤ last) (hsum : last ≤ sum) (hD : 0 ≤ D)
    (hP : ((τ + 1 / 2) * sum + (1 / 2 - τ) * last) / τ ^ 2 + 3 * μ * D ≤ P) :
    sum ≤ 2 * τ ^ 2 * P ∧ last ≤ τ ^ 2 * P := by
  have hscale := mul_le_mul_of_nonneg_left hP (sq_nonneg τ)
  have hid : τ ^ 2 * (((τ + 1 / 2) * sum + (1 / 2 - τ) * last) / τ ^ 2) =
      (τ + 1 / 2) * sum + (1 / 2 - τ) * last := by field_simp
  rw [mul_add, hid] at hscale
  have hnonneg : 0 ≤ τ ^ 2 * (3 * μ * D) := by positivity
  have hterm : 0 ≤ (1 / 2 - τ) * last := mul_nonneg (by linarith) hlast
  have hdiff := mul_nonneg (show 0 ≤ τ + 1 / 2 by linarith) (sub_nonneg.mpr hsum)
  have hsum0 : 0 ≤ sum := hlast.trans hsum
  constructor <;> nlinarith [mul_nonneg hτ.le hsum0]

lemma epoch_coefficient_comparison {t : ℝ} (ht : 1 ≤ t) :
    let τ := 2 / (t + 1)
    let prev := 2 / t
    (1 - τ) / τ ^ 2 ≤ 1 / prev ^ 2 ∧
      (1 / 2 : ℝ) / τ ^ 2 ≤ (prev + 1 / 2) / prev ^ 2 := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t + 1 := by linarith
  dsimp only
  constructor
  · field_simp
    nlinarith
  · field_simp
    nlinarith

lemma epoch_coefficients_bound {τ prev last sum : ℝ}
    (hlast : 0 ≤ last) (hsum : last ≤ sum)
    (hfirst : (1 - τ) / τ ^ 2 ≤ 1 / prev ^ 2)
    (hmiddle : (1 / 2 : ℝ) / τ ^ 2 ≤ (prev + 1 / 2) / prev ^ 2) :
    ((1 / 2 - τ) * last + (1 / 2 : ℝ) * sum) / τ ^ 2 ≤
      ((prev + 1 / 2) * sum + (1 / 2 - prev) * last) / prev ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_right hfirst hlast
  have h2 := mul_le_mul_of_nonneg_right hmiddle (sub_nonneg.mpr hsum)
  calc
    _ = ((1 - τ) / τ ^ 2) * last + ((1 / 2 : ℝ) / τ ^ 2) * (sum - last) := by ring
    _ ≤ (1 / prev ^ 2) * last + ((prev + 1 / 2) / prev ^ 2) * (sum - last) := add_le_add h1 h2
    _ = _ := by ring

lemma epoch_error_sum {S : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ s ∈ Finset.range S, δ / (2 / ((s : ℝ) + 4)) ^ 2) ≤
      δ * ((S : ℝ) + 4) ^ 3 / 4 := by
  have hterm (s : ℕ) (hs : s ∈ Finset.range S) :
      δ / (2 / ((s : ℝ) + 4)) ^ 2 ≤ δ * ((S : ℝ) + 4) ^ 2 / 4 := by
    have hs' : (s : ℝ) ≤ (S : ℝ) := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hs))
    have hid : δ / (2 / ((s : ℝ) + 4)) ^ 2 = δ * ((s : ℝ) + 4) ^ 2 / 4 := by field_simp; ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left (show ((s : ℝ) + 4) ^ 2 ≤ ((S : ℝ) + 4) ^ 2 by nlinarith) hδ
    linarith
  have h := Finset.sum_le_sum hterm
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  have hn : 0 ≤ δ * ((S : ℝ) + 4) ^ 2 := by positivity
  nlinarith

lemma epoch_tau_square_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, ((2 : ℝ) / (j + 5)) ^ 2) ≤ 1 - 4 / ((k : ℝ) + 4) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have h4 : 0 < (k : ℝ) + 4 := by positivity
      have h5 : 0 < (k : ℝ) + 5 := by positivity
      have hstep : ((2 : ℝ) / (k + 5)) ^ 2 ≤ 4 / (k + 4) - 4 / (k + 5) := by
        field_simp
        nlinarith
      push_cast
      rw [show (k : ℝ) + 1 + 4 = k + 5 by ring]
      linarith

noncomputable def costWeight (d : ℕ → ℝ) (s : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => d s + costWeight d (s + 1) k
noncomputable def costOffset (d h e : ℕ → ℝ) (s : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => h s + costOffset d h e (s + 1) k + costWeight d (s + 1) k * e s
lemma costWeight_nonneg {d : ℕ → ℝ} (hd : ∀ s, 0 ≤ d s) (s k : ℕ) :
    0 ≤ costWeight d s k := by
  induction k generalizing s with
  | zero => simp [costWeight]
  | succ k ih => exact add_nonneg (hd s) (ih (s + 1))
lemma costWeight_sum (d : ℕ → ℝ) (s k : ℕ) :
    costWeight d s k = ∑ j ∈ Finset.range k, d (s + j) := by
  induction k generalizing s with
  | zero => simp [costWeight]
  | succ k ih =>
      rw [costWeight, ih, Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      omega
lemma costOffset_bound (d h e : ℕ → ℝ) (D : ℝ)
    (he : ∀ s, 0 ≤ e s) (hD : ∀ s k, costWeight d s k ≤ D) (s k : ℕ) :
    costOffset d h e s k ≤ (∑ j ∈ Finset.range k, h (s + j)) +
      D * ∑ j ∈ Finset.range k, e (s + j) := by
  induction k generalizing s with
  | zero => simp [costOffset]
  | succ k ih =>
      rw [costOffset, Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [Nat.add_zero]
      have hh := ih (s + 1)
      have hm := mul_le_mul_of_nonneg_right (hD (s + 1) k) (he s)
      have heq (f : ℕ → ℝ) : (∑ j ∈ Finset.range k, f (s + (j + 1))) =
          ∑ j ∈ Finset.range k, f (s + 1 + j) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        omega
      rw [heq h, heq e]
      linarith

lemma epoch_weight_prefix (k : ℕ) :
    (∑ j ∈ Finset.range k, if j = 0 then (0 : ℝ) else ((2 : ℝ) / (j + 4)) ^ 2) ≤ 1 := by
  cases k with
  | zero => simp
  | succ k =>
      rw [Finset.sum_range_succ']
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]
      have heq (j : ℕ) : ((j + 1 : ℕ) : ℝ) + 4 = (j : ℝ) + 5 := by push_cast; ring
      simp_rw [heq]
      have h := epoch_tau_square_sum k
      have hp : 0 ≤ (4 : ℝ) / ((k : ℝ) + 4) := by positivity
      linarith
lemma epoch_weight_segment (s k : ℕ) :
    (∑ j ∈ Finset.range k, if s + j = 0 then (0 : ℝ) else ((2 : ℝ) / ((s + j : ℕ) + 4)) ^ 2) ≤ 1 := by
  let d := fun j : ℕ => if j = 0 then (0 : ℝ) else ((2 : ℝ) / (j + 4)) ^ 2
  have h := epoch_weight_prefix (s + k)
  change (∑ j ∈ Finset.range (s + k), d j) ≤ 1 at h
  rw [Finset.sum_range_add] at h
  have hn : 0 ≤ ∑ j ∈ Finset.range s, d j := by
    apply Finset.sum_nonneg
    intro j _
    dsimp [d]
    split_ifs <;> positivity
  change (∑ j ∈ Finset.range k, d (s + j)) ≤ 1
  linarith

lemma costWeight_epoch_bound (D : ℝ) (hD : 0 ≤ D) (s k : ℕ) :
    costWeight (fun j => D * (if j = 0 then 0 else ((2 : ℝ) / (j + 4)) ^ 2)) s k ≤ D := by
  rw [costWeight_sum, ← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (epoch_weight_segment s k) hD).trans_eq (mul_one D)
lemma epoch_overhead_sum (a b c d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) (k : ℕ) :
    (∑ j ∈ Finset.range k,
      (a + b * (if j = 0 then 0 else ((2 : ℝ) / (j + 4)) ^ 2) + c + (if j = 0 then d else 0))) ≤
        k * (a + c) + b + d := by
  have hw := mul_le_mul_of_nonneg_left (epoch_weight_prefix k) hb
  have hi : (∑ j ∈ Finset.range k, if j = 0 then d else 0) ≤ d := by
    classical
    simp only [Finset.sum_ite_eq', Finset.mem_range]
    split_ifs <;> linarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  linarith

end OracleTemplate.ComponentEnvelope
