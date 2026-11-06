import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace LongTails.Proofs.GdNegativeSpectrum

lemma log_increment {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) :
    a / (1 + s + a) ≤ Real.log (1 + s + a) - Real.log (1 + s) := by
  have h0 : 0 < 1 + s := by positivity
  have h1 : 0 < 1 + s + a := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (div_pos h1 h0)
  rw [Real.log_div h1.ne' h0.ne'] at h
  have he : 1 - ((1 + s + a) / (1 + s))⁻¹ = a / (1 + s + a) := by
    field_simp
    ring
  rwa [he] at h

lemma cumulative_weights_le_log (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    ∑ i ∈ Finset.range n, a i / (1 + ∑ j ∈ Finset.range (i + 1), a j) ≤
      Real.log (1 + ∑ i ∈ Finset.range n, a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : 0 ≤ ∑ i ∈ Finset.range n, a i := Finset.sum_nonneg (fun i _ => ha i)
    have h := log_increment hs (ha n)
    simp only [Finset.sum_range_succ] at ih ⊢
    simp only [add_assoc] at ih h ⊢
    linarith

lemma product_ge_one_add_sum (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    1 + ∑ i ∈ Finset.range n, a i ≤ ∏ i ∈ Finset.range n, (1 + a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : 0 ≤ ∑ i ∈ Finset.range n, a i := Finset.sum_nonneg (fun i _ => ha i)
    have hn := ha n
    simp only [Finset.sum_range_succ, Finset.prod_range_succ]
    nlinarith

lemma reciprocal_product_weights (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (n : ℕ) :
    ∑ i ∈ Finset.range n, a i / (∏ j ∈ Finset.range (i + 1), (1 + a j)) =
      1 - 1 / (∏ i ∈ Finset.range n, (1 + a i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 < ∏ i ∈ Finset.range n, (1 + a i) :=
      Finset.prod_pos (fun i _ => by have := ha i; positivity)
    have hn : 0 < 1 + a n := by have := ha n; positivity
    rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]
    field_simp
    ring

lemma spectral_weight_le {L l : ℝ} (hL : 0 ≤ L) (hl : 0 ≤ l) (hlL : l ≤ L)
    (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ℕ) :
    a i * l / (∏ j ∈ Finset.range (i + 1), (1 + a j * l)) ≤
      L * a i / (1 + L * ∑ j ∈ Finset.range (i + 1), a j) := by
  have hs : 0 ≤ ∑ j ∈ Finset.range (i + 1), a j := Finset.sum_nonneg (fun j _ => ha j)
  have hp := product_ge_one_add_sum (fun j => a j * l) (fun j => mul_nonneg (ha j) hl) (i + 1)
  rw [← Finset.sum_mul] at hp
  have hd : 0 < 1 + (∑ j ∈ Finset.range (i + 1), a j) * l := by positivity
  have hD : 0 < 1 + L * ∑ j ∈ Finset.range (i + 1), a j := by positivity
  calc
    a i * l / (∏ j ∈ Finset.range (i + 1), (1 + a j * l)) ≤
        a i * l / (1 + (∑ j ∈ Finset.range (i + 1), a j) * l) :=
      div_le_div_of_nonneg_left (mul_nonneg (ha i) hl) hd hp
    _ ≤ L * a i / (1 + L * ∑ j ∈ Finset.range (i + 1), a j) := by
      rw [div_le_div_iff₀ hd hD]
      nlinarith [mul_le_mul_of_nonneg_left hlL (ha i)]

lemma weighted_square_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → κ → ℝ) (m : ι → ℝ) (v : ι → κ → ℝ) (r : ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hm0 : ∀ i, 0 ≤ m i)
    (hm : ∀ i j, w i j ≤ m i)
    (hcolumn : ∀ j, ∑ i, w i j ≤ 1)
    (hv : ∀ i, ∑ j, v i j ^ 2 ≤ r ^ 2) :
    ∑ j, (∑ i, w i j * v i j) ^ 2 ≤ r ^ 2 * ∑ i, m i := by
  have hpoint (j : κ) :
      (∑ i, w i j * v i j) ^ 2 ≤ ∑ i, w i j * v i j ^ 2 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (s := Finset.univ) (f := fun i => w i j)
      (g := fun i => w i j * v i j ^ 2) (r := fun i => w i j * v i j)
      (fun i _ => hw i j) (fun i _ => mul_nonneg (hw i j) (sq_nonneg _))
      (fun i _ => le_of_eq (by ring))
    have hn : 0 ≤ ∑ i, w i j * v i j ^ 2 :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hw i j) (sq_nonneg _))
    exact hcs.trans (by simpa using mul_le_mul_of_nonneg_right (hcolumn j) hn)
  calc
    ∑ j, (∑ i, w i j * v i j) ^ 2 ≤ ∑ j, ∑ i, w i j * v i j ^ 2 :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = ∑ i, ∑ j, w i j * v i j ^ 2 := Finset.sum_comm
    _ ≤ ∑ i, m i * r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ∑ j, w i j * v i j ^ 2 ≤ ∑ j, m i * v i j ^ 2 :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hm i j) (sq_nonneg _))
        _ = m i * ∑ j, v i j ^ 2 := (Finset.mul_sum _ _ _).symm
        _ ≤ m i * r ^ 2 := mul_le_mul_of_nonneg_left (hv i) (hm0 i)
    _ = r ^ 2 * ∑ i, m i := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma spectral_noise_square_sum {κ : Type*} [Fintype κ]
    (L : ℝ) (hL : 0 ≤ L) (l : κ → ℝ) (hl : ∀ j, 0 ≤ l j) (hlL : ∀ j, l j ≤ L)
    (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (n : ℕ) (v : Fin n → κ → ℝ) (r : ℝ)
    (hv : ∀ i, ∑ j, v i j ^ 2 ≤ r ^ 2) :
    ∑ j, (∑ i : Fin n, (a i * l j /
      (∏ k ∈ Finset.range (i.val + 1), (1 + a k * l j))) * v i j) ^ 2 ≤
      r ^ 2 * Real.log (1 + L * ∑ i ∈ Finset.range n, a i) := by
  let w (i : Fin n) (j : κ) := a i * l j /
    (∏ k ∈ Finset.range (i.val + 1), (1 + a k * l j))
  let m (i : Fin n) := L * a i / (1 + L * ∑ k ∈ Finset.range (i.val + 1), a k)
  have hw (i : Fin n) (j : κ) : 0 ≤ w i j := by
    dsimp [w]
    apply div_nonneg (mul_nonneg (ha i) (hl j))
    exact Finset.prod_nonneg (fun k _ => by have := ha k; have := hl j; positivity)
  have hm (i : Fin n) : 0 ≤ m i := by
    dsimp [m]
    have := ha i
    have hs : 0 ≤ ∑ k ∈ Finset.range (i.val + 1), a k :=
      Finset.sum_nonneg (fun k _ => ha k)
    positivity
  have hwm (i : Fin n) (j : κ) : w i j ≤ m i :=
    spectral_weight_le hL (hl j) (hlL j) a ha i
  have hc (j : κ) : ∑ i : Fin n, w i j ≤ 1 := by
    dsimp [w]
    rw [Fin.sum_univ_eq_sum_range (fun i => a i * l j /
      (∏ k ∈ Finset.range (i + 1), (1 + a k * l j)))]
    rw [reciprocal_product_weights (fun i => a i * l j)
      (fun i => mul_nonneg (ha i) (hl j))]
    have hp : 0 ≤ 1 / (∏ i ∈ Finset.range n, (1 + a i * l j)) := by
      apply div_nonneg zero_le_one
      exact Finset.prod_nonneg (fun i _ => by have := ha i; have := hl j; positivity)
    linarith
  have hsum : ∑ i : Fin n, m i ≤ Real.log (1 + L * ∑ i ∈ Finset.range n, a i) := by
    dsimp [m]
    rw [Fin.sum_univ_eq_sum_range (fun i => L * a i /
      (1 + L * ∑ k ∈ Finset.range (i + 1), a k))]
    have h := cumulative_weights_le_log (fun i => L * a i)
      (fun i => mul_nonneg hL (ha i)) n
    simpa only [Finset.mul_sum] using h
  exact (weighted_square_sum w m v r hw hm hwm hc hv).trans
    (mul_le_mul_of_nonneg_left hsum (sq_nonneg r))

lemma backward_transport (a u v : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (n : ℕ)
    (hu : ∀ i < n, u (i + 1) = (1 + a i) * u i - a i * v i) :
    u 0 = u n / (∏ i ∈ Finset.range n, (1 + a i)) +
      ∑ i ∈ Finset.range n,
        (a i / (∏ k ∈ Finset.range (i + 1), (1 + a k))) * v i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 < ∏ i ∈ Finset.range n, (1 + a i) :=
      Finset.prod_pos (fun i _ => by have := ha i; positivity)
    have hn : 0 < 1 + a n := by have := ha n; positivity
    rw [Finset.sum_range_succ, hu n (by omega), Finset.prod_range_succ]
    rw [ih (fun i hi => hu i (by omega))]
    field_simp
    ring

lemma backward_transport_square_error {κ : Type*} [Fintype κ]
    (L : ℝ) (hL : 0 ≤ L) (l : κ → ℝ) (hl : ∀ j, 0 ≤ l j) (hlL : ∀ j, l j ≤ L)
    (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (u e : ℕ → κ → ℝ)
    (n : ℕ)
    (hu : ∀ i < n, ∀ j, u (i + 1) j = (1 + a i * l j) * u i j - a i * l j * e i j)
    (r : ℝ) (he : ∀ i < n, ∑ j, e i j ^ 2 ≤ r ^ 2) :
    ∑ j, (u 0 j - u n j / (∏ i ∈ Finset.range n, (1 + a i * l j))) ^ 2 ≤
      r ^ 2 * Real.log (1 + L * ∑ i ∈ Finset.range n, a i) := by
  have hidentity (j : κ) := backward_transport (fun i => a i * l j)
    (fun i => u i j) (fun i => e i j) (fun i => mul_nonneg (ha i) (hl j))
    n (fun i hi => hu i hi j)
  have hrewrite (j : κ) :
      u 0 j - u n j / (∏ i ∈ Finset.range n, (1 + a i * l j)) =
        ∑ i : Fin n, (a i * l j /
          (∏ k ∈ Finset.range (i.val + 1), (1 + a k * l j))) * e i j := by
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      (a i * l j / (∏ k ∈ Finset.range (i + 1), (1 + a k * l j))) * e i j)]
    linarith [hidentity j]
  simp_rw [hrewrite]
  exact spectral_noise_square_sum L hL l hl hlL a ha n (fun i j => e i j) r
    (fun i => he i i.isLt)

lemma backward_transport_square_persistence {κ : Type*} [Fintype κ]
    (L : ℝ) (hL : 0 ≤ L) (l : κ → ℝ) (hl : ∀ j, 0 ≤ l j) (hlL : ∀ j, l j ≤ L)
    (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (u e : ℕ → κ → ℝ)
    (n : ℕ)
    (hu : ∀ i < n, ∀ j, u (i + 1) j = (1 + a i * l j) * u i j - a i * l j * e i j)
    (r : ℝ) (he : ∀ i < n, ∑ j, e i j ^ 2 ≤ r ^ 2) :
    (∑ j, u 0 j ^ 2) / 2 - r ^ 2 * Real.log (1 + L * ∑ i ∈ Finset.range n, a i) ≤
      ∑ j, u n j ^ 2 := by
  have herr := backward_transport_square_error L hL l hl hlL a ha u e n hu r he
  have hp (j : κ) : 1 ≤ ∏ i ∈ Finset.range n, (1 + a i * l j) := by
    have h := product_ge_one_add_sum (fun i => a i * l j)
      (fun i => mul_nonneg (ha i) (hl j)) n
    have hs : 0 ≤ ∑ i ∈ Finset.range n, a i * l j :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (hl j))
    linarith
  have hpoint (j : κ) : u 0 j ^ 2 ≤
      2 * (u 0 j - u n j / (∏ i ∈ Finset.range n, (1 + a i * l j))) ^ 2 + 2 * u n j ^ 2 := by
    have hd : 0 < ∏ i ∈ Finset.range n, (1 + a i * l j) := by linarith [hp j]
    have hab : |u n j / (∏ i ∈ Finset.range n, (1 + a i * l j))| ≤ |u n j| := by
      rw [abs_div, abs_of_pos hd]
      exact div_le_self (abs_nonneg _) (hp j)
    have hs := pow_le_pow_left₀ (abs_nonneg _) hab 2
    simp only [sq_abs] at hs
    nlinarith [sq_nonneg (u 0 j - 2 * (u n j /
      (∏ i ∈ Finset.range n, (1 + a i * l j))))]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  linarith

end LongTails.Proofs.GdNegativeSpectrum
