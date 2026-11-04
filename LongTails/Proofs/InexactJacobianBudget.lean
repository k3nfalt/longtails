import LongTails.Proofs.InexactJacobianOuter
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace LongTails.Proofs.InexactJacobianBudget

open LongTails.Setups.InexactJacobianMonotone
open LongTails.Algorithms.NestedAnchoredInexactJacobian
open InexactJacobianModel InexactJacobianInner InexactJacobianOuter

noncomputable section

variable {p : Params}

lemma guess_succ (k j : ℕ) : guess p k (j + 1) = 2 * guess p k j := by
  unfold guess; rw [pow_succ]; ring

lemma sum_guess (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (k j : ℕ) : ∑ l ∈ Finset.range (j + 1), guess p k l ≤ 2 * guess p k j := by
  induction j with
  | zero => simp only [zero_add, Finset.sum_range_one]; linarith [guess_pos hM hδ hR hε k 0]
  | succ j ih => rw [Finset.sum_range_succ, guess_succ]; linarith

lemma scaled_guess (hM : 0 < p.M) (hR : 0 < p.R) (hε : 0 < p.ε) (k j : ℕ) :
    outerStep p k * p.M * guess p k j = (1 + outerStep p k * p.δ) * 2 ^ j := by
  have ha := outerStep_pos hR hε k
  unfold guess
  field_simp

lemma scaled_guess_lower (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (k j : ℕ) : 1 + outerStep p k * p.δ ≤ outerStep p k * p.M * guess p k j := by
  rw [scaled_guess hM hR hε]
  have ha := outerStep_pos hR hε k
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  nlinarith [mul_nonneg ha.le hδ]

lemma innerCount_le (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (k j : ℕ) : (innerCount p k j : ℝ) ≤ 5122 * (outerStep p k * p.M * guess p k j) := by
  have ha := outerStep_pos hR hε k
  have ht := innerStep_pos hM hδ hR hε k j
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 8 * outerStep p k / innerStep p k j by positivity)
  have hlow := scaled_guess_lower hM hδ hR hε k j
  have hδa := mul_nonneg ha.le hδ
  have he : 8 * outerStep p k / innerStep p k j =
      1024 * (outerStep p k * p.δ) + 4096 * (outerStep p k * p.M * guess p k j) := by
    unfold innerStep
    simp only [one_div, div_inv_eq_mul]
    ring
  unfold innerCount
  push_cast
  rw [he] at hc ⊢
  linarith

lemma outerTicks_le_sum (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    {base k : ℕ} {z Fz : p.E} (hs : Succeeds F J base k z Fz) :
    outerTicks F J base k z Fz ≤
      ∑ j ∈ Finset.range (firstAttempt F J base k z Fz + 1), 2 * innerCount p k j := by
  have hi := (first_spec F J hs).1
  unfold outerTicks attemptOffset
  rw [Finset.sum_range_succ]
  omega

lemma firstAttempt_guess (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (base k : ℕ) (z Fz : p.E) :
    guess p k (firstAttempt F J base k z Fz) ≤ guess p k 0 +
      2 * ‖center p k z Fz - resolvent F k z‖ := by
  have hs := succeeds F hreg J hJ hM hδ hR hε base k z Fz
  obtain ⟨_, _, hfail, _⟩ := first_spec F J hs
  cases he : firstAttempt F J base k z Fz with
  | zero => nlinarith [norm_nonneg (center p k z Fz - resolvent F k z)]
  | succ j =>
    have hj : guess p k j < ‖center p k z Fz - resolvent F k z‖ := by
      by_contra h
      obtain ⟨i, hi, hacc⟩ := attempt_success F hreg J hJ hM hδ hR hε base k z Fz
        (resolvent F k z) j (resolvent_spec F hreg hM hR hε k z) (le_of_not_gt h)
      exact hfail j (by omega) i hi hacc
    rw [guess_succ]
    linarith [guess_pos hM hδ hR hε k 0]

lemma outerTicks_bound (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (base k : ℕ) (z Fz : p.E) :
    (outerTicks F J base k z Fz : ℝ) ≤
      65536 * (1 + p.δ * outerStep p k +
        p.M * outerStep p k * ‖center p k z Fz - resolvent F k z‖) := by
  have hs := succeeds F hreg J hJ hM hδ hR hε base k z Fz
  have hticks : (outerTicks F J base k z Fz : ℝ) ≤
      ∑ j ∈ Finset.range (firstAttempt F J base k z Fz + 1), 2 * (innerCount p k j : ℝ) := by
    exact_mod_cast outerTicks_le_sum F J hs
  have hsum : (∑ j ∈ Finset.range (firstAttempt F J base k z Fz + 1), 2 * (innerCount p k j : ℝ)) ≤
      10244 * outerStep p k * p.M *
        (∑ j ∈ Finset.range (firstAttempt F J base k z Fz + 1), guess p k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := innerCount_le hM hδ hR hε k j
    nlinarith
  have ha := outerStep_pos hR hε k
  have hcoef : 0 ≤ 10244 * outerStep p k * p.M := by positivity
  have hgeos := mul_le_mul_of_nonneg_left
    (sum_guess hM hδ hR hε k (firstAttempt F J base k z Fz)) hcoef
  have hlast := mul_le_mul_of_nonneg_left
    (firstAttempt_guess F hreg J hJ hM hδ hR hε base k z Fz) hcoef
  have hbase := scaled_guess hM hR hε k 0
  norm_num only [pow_zero, mul_one] at hbase
  have hδa := mul_nonneg hδ ha.le
  have hr := mul_nonneg (mul_nonneg hM.le ha.le) (norm_nonneg (center p k z Fz - resolvent F k z))
  nlinarith

lemma weighted_radius_sum {a w s r : ℕ → ℝ} {ℓ R : ℝ} (n : ℕ)
    (hℓ : 0 ≤ ℓ) (hR : 0 ≤ R)
    (ha : ∀ k < n, 0 ≤ a k) (hs : ∀ k < n, 0 ≤ s k)
    (hr : ∀ k < n, r k ≤ 3 / 2 * s k)
    (hw : ∀ k < n, a k ≤ 2 * ℓ * w k)
    (henergy : ∑ k ∈ Finset.range n, w k ^ 2 * s k ^ 2 ≤ 4 / 3 * R ^ 2) :
    ∑ k ∈ Finset.range n, a k * r k ≤ 4 * ℓ * R * Real.sqrt n := by
  let W := ∑ k ∈ Finset.range n, w k * s k
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) (fun _ => (1 : ℝ)) (fun k => w k * s k)
  have hc' : W ^ 2 ≤ (n : ℝ) * (∑ k ∈ Finset.range n, w k ^ 2 * s k ^ 2) := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, mul_pow] using hc
  have he := mul_le_mul_of_nonneg_left henergy (show (0 : ℝ) ≤ n by positivity)
  have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt (by positivity)
  have hW : W ≤ 4 / 3 * R * Real.sqrt n := by
    have heq : (4 / 3 * R * Real.sqrt n) ^ 2 = 16 / 9 * R ^ 2 * n := by
      rw [mul_pow, hsqrt]; ring
    have hnn : 0 ≤ R ^ 2 * n := by positivity
    have hsq : W ^ 2 ≤ (4 / 3 * R * Real.sqrt n) ^ 2 := by rw [heq]; nlinarith
    have hpos : 0 ≤ 4 / 3 * R * Real.sqrt n := by positivity
    nlinarith
  have hsum : (∑ k ∈ Finset.range n, a k * r k) ≤ 3 * ℓ * W := by
    dsimp only [W]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkn := Finset.mem_range.mp hk
    have h₁ := mul_le_mul_of_nonneg_left (hr k hkn) (ha k hkn)
    have h₂ := mul_le_mul_of_nonneg_right (hw k hkn) (hs k hkn)
    nlinarith
  have h := mul_le_mul_of_nonneg_left hW (show 0 ≤ 3 * ℓ by positivity)
  nlinarith

lemma cumulative_ratio (hR : 0 < p.R) (hε : 0 < p.ε) (k : ℕ) :
    cumulative p (k + 1) / outerStep p k = ((k : ℝ) + 2) / 2 := by
  have hℓ := scale_pos hR hε
  unfold cumulative outerStep
  push_cast
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma radius_sum_bound (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (xs : p.E) (hzero : F xs = 0) (hx : ‖p.x0 - xs‖ ≤ p.R) (n : ℕ) :
    ∑ k ∈ Finset.range n, outerStep p k * radius F J k ≤ 4 * scale p * p.R * Real.sqrt n := by
  apply weighted_radius_sum (w := fun k => cumulative p (k + 1) / outerStep p k)
    n (scale_pos hR hε).le hR.le
    (fun k _ => (outerStep_pos hR hε k).le) (fun k _ => norm_nonneg _)
    (fun k _ => radius_le_gap F hreg J hJ hM hδ hR hε k)
  · intro k _
    rw [cumulative_ratio hR hε]
    unfold outerStep
    have hℓ := scale_pos hR hε
    nlinarith
  · exact outer_energy_sum F hreg J hJ hM hδ hR hε xs hzero hx n

lemma totalTicks_bound (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε) (n : ℕ) :
    ((outerSeq F J n).1 : ℝ) ≤ 65536 * ((n : ℝ) + p.δ * cumulative p n +
      p.M * ∑ k ∈ Finset.range n, outerStep p k * radius F J k) := by
  induction n with
  | zero => simp [outerSeq, cumulative]
  | succ n ih =>
    have h := outerTicks_bound F hreg J hJ hM hδ hR hε (outerSeq F J n).1 n
      (outerSeq F J n).2.1 (outerSeq F J n).2.2
    have he : ((outerSeq F J (n + 1)).1 : ℝ) = ((outerSeq F J n).1 : ℝ) +
        (outerTicks F J (outerSeq F J n).1 n (outerSeq F J n).2.1 (outerSeq F J n).2.2 : ℝ) := by
      simp only [outerSeq, Nat.cast_add]
    rw [he, cumulative_succ, Finset.sum_range_succ]
    push_cast
    change (outerTicks F J (outerSeq F J n).1 n (outerSeq F J n).2.1 (outerSeq F J n).2.2 : ℝ) ≤
      65536 * (1 + p.δ * outerStep p n + p.M * outerStep p n * radius F J n) at h
    nlinarith

lemma count_curvature (hM : 0 < p.M) (hR : 0 < p.R) (hε : 0 < p.ε) :
    p.M * p.R ^ 2 / p.ε ≤ (outerCount p : ℝ) ^ 2 * Real.sqrt (outerCount p) := by
  let Q := p.M * p.R ^ 2 / p.ε
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hK : (0 : ℝ) < outerCount p := by unfold outerCount; positivity
  have hbase : Q ^ (2 / 5 : ℝ) ≤ (outerCount p : ℝ) := by
    have h := Nat.le_ceil (Q ^ (2 / 5 : ℝ))
    unfold outerCount
    change Q ^ (2 / 5 : ℝ) ≤ (⌈Q ^ (2 / 5 : ℝ)⌉₊ + 1 : ℕ)
    push_cast
    linarith
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hQ.le _) hbase (show (0 : ℝ) ≤ 5 / 2 by norm_num)
  have heq : (Q ^ (2 / 5 : ℝ)) ^ (5 / 2 : ℝ) = Q := by
    rw [← Real.rpow_mul hQ.le]
    norm_num
  rw [heq] at hp
  have heqK : (outerCount p : ℝ) ^ (5 / 2 : ℝ) = (outerCount p : ℝ) ^ 2 * Real.sqrt (outerCount p) := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hK,
      Real.rpow_two, ← Real.sqrt_eq_rpow]
  rwa [heqK] at hp

lemma scaled_curvature (hM : 0 < p.M) (hR : 0 < p.R) (hε : 0 < p.ε) :
    4 * p.M * scale p * p.R * Real.sqrt (outerCount p) ≤ 16 * (outerCount p : ℝ) := by
  let K : ℝ := outerCount p
  have hK : 0 < K := by dsimp only [K]; unfold outerCount; positivity
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hs2 : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK.le
  have hQ := count_curvature hM hR hε
  change p.M * p.R ^ 2 / p.ε ≤ K ^ 2 * Real.sqrt K at hQ
  have hden : 0 < Real.sqrt K * (K + 1) := by positivity
  have he : 4 * p.M * scale p * p.R * Real.sqrt K =
      16 * (p.M * p.R ^ 2 / p.ε) / (Real.sqrt K * (K + 1)) := by
    unfold scale
    change 4 * p.M * (4 * p.R / (p.ε * K * (K + 1))) * p.R * Real.sqrt K = _
    field_simp
    nlinarith
  change 4 * p.M * scale p * p.R * Real.sqrt K ≤ 16 * K
  rw [he, div_le_iff₀ hden]
  nlinarith [mul_nonneg hK.le hs.le]

lemma public_budget_sufficient (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (xs : p.E) (hzero : F xs = 0) (hx : ‖p.x0 - xs‖ ≤ p.R) :
    (outerSeq F J (outerCount p)).1 ≤
      ⌈4194304 * (1 + (p.M * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ) + p.δ * p.R / p.ε)⌉₊ := by
  have ht := totalTicks_bound F hreg J hJ hM hδ hR hε (outerCount p)
  have hr := radius_sum_bound F hreg J hJ hM hδ hR hε xs hzero hx (outerCount p)
  have hmr := mul_le_mul_of_nonneg_left hr hM.le
  have hcurv := scaled_curvature hM hR hε
  rw [cumulative_final hR hε] at ht
  have heδ : p.δ * (2 * p.R / p.ε) = 2 * (p.δ * p.R / p.ε) := by ring
  rw [heδ] at ht
  have hbound : ((outerSeq F J (outerCount p)).1 : ℝ) ≤
      65536 * (17 * (outerCount p : ℝ) + 2 * (p.δ * p.R / p.ε)) := by nlinarith
  have hQ : 0 ≤ (p.M * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hN : (outerCount p : ℝ) ≤ (p.M * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ) + 2 := by
    have h := Nat.ceil_lt_add_one hQ
    unfold outerCount
    push_cast
    linarith
  have hδR : 0 ≤ p.δ * p.R / p.ε := by positivity
  have hfinal : ((outerSeq F J (outerCount p)).1 : ℝ) ≤
      4194304 * (1 + (p.M * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ) + p.δ * p.R / p.ε) := by nlinarith
  exact_mod_cast hfinal.trans (Nat.le_ceil _)

end

end LongTails.Proofs.InexactJacobianBudget
