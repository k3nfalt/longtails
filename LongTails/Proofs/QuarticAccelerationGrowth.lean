import LongTails.Proofs.QuarticAcceleration
import LongTails.Proofs.GeneralizedMixedRate

namespace LongTails.Proofs.QuarticAccelerationGrowth

open Finset

lemma weighted_fifth {ι : Type*} (s : Finset ι) (x y z : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 < y i)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hxyz : ∀ i ∈ s, z i ^ 5 ≤ x i * y i ^ 4) :
    (∑ i ∈ s, z i) ^ 5 ≤ (∑ i ∈ s, x i) * (∑ i ∈ s, y i) ^ 4 := by
  let v := fun i => z i ^ 3 / y i ^ 2
  have hv : ∀ i ∈ s, 0 ≤ v i := fun i hi => div_nonneg (pow_nonneg (hz i hi) _) (sq_nonneg _)
  have hfirst := OracleTemplate.GeneralizedAccelerated.weighted_holder_cube s v y z hv hy hz (by
    intro i hi
    simp only [v, div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos (hy i hi))), le_refl])
  have hsecond : (∑ i ∈ s, v i) ^ 2 ≤ (∑ i ∈ s, x i) * (∑ i ∈ s, z i) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul s hx hz
    intro i hi
    dsimp [v]
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos (sq_pos_of_pos (hy i hi)))).mpr
    have hh := mul_le_mul_of_nonneg_right (hxyz i hi) (hz i hi)
    nlinarith only [hh]
  have hsum : 0 ≤ ∑ i ∈ s, z i := sum_nonneg hz
  have hsquare := pow_le_pow_left₀ (pow_nonneg hsum 3) hfirst 2
  have hmul := mul_le_mul_of_nonneg_right hsecond (by positivity : 0 ≤ (∑ i ∈ s, y i) ^ 4)
  by_cases hzero : ∑ i ∈ s, z i = 0
  · rw [hzero]
    simpa only [zero_pow (by decide : 5 ≠ 0)] using
      mul_nonneg (sum_nonneg hx) (by positivity : 0 ≤ (∑ i ∈ s, y i) ^ 4)
  · have hpos : 0 < ∑ i ∈ s, z i := lt_of_le_of_ne hsum (Ne.symm hzero)
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith only [hsquare, hmul]

lemma fifth_root_pow {a : ℝ} (ha : 0 ≤ a) : (a ^ (1 / 5 : ℝ)) ^ 5 = a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  norm_num

lemma weighted_curvature_fifth {ι : Type*} (s : Finset ι) (A μ : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hμ : ∀ i ∈ s, 0 < μ i) :
    (∑ i ∈ s, A i ^ (1 / 5 : ℝ)) ^ 5 ≤
      (∑ i ∈ s, A i * μ i ^ 2) * (∑ i ∈ s, 1 / Real.sqrt (μ i)) ^ 4 := by
  apply weighted_fifth s (fun i => A i * μ i ^ 2) (fun i => 1 / Real.sqrt (μ i))
    (fun i => A i ^ (1 / 5 : ℝ))
    (fun i hi => mul_nonneg (hA i hi) (sq_nonneg _))
    (fun i hi => one_div_pos.mpr (Real.sqrt_pos.mpr (hμ i hi)))
    (fun i hi => Real.rpow_nonneg (hA i hi) _)
  intro i hi
  rw [fifth_root_pow (hA i hi)]
  have hs : (Real.sqrt (μ i)) ^ 4 = μ i ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (hμ i hi).le]
  rw [div_pow, one_pow, hs]
  simp only [mul_one_div, mul_div_cancel_right₀ _ (ne_of_gt (sq_pos_of_pos (hμ i hi))), le_refl]

lemma weighted_growth {ι : Type*} (s : Finset ι) (A μ : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hμ : ∀ i ∈ s, 0 < μ i)
    {H C c Afinal : ℝ} (hH : 0 ≤ H) (hc : 0 ≤ c) (hAf : 0 ≤ Afinal)
    (henergy : (∑ i ∈ s, A i * μ i ^ 2) ≤ H)
    (hweights : (∑ i ∈ s, 1 / Real.sqrt (μ i)) ≤ C * Real.sqrt Afinal)
    (htune : c ^ 5 * H * C ^ 4 ≤ 1) :
    c * (∑ i ∈ s, A i ^ (1 / 5 : ℝ)) ≤ (Afinal ^ (1 / 5 : ℝ)) ^ 2 := by
  have hw0 : 0 ≤ ∑ i ∈ s, 1 / Real.sqrt (μ i) :=
    sum_nonneg (fun i hi => (one_div_pos.mpr (Real.sqrt_pos.mpr (hμ i hi))).le)
  have hh := weighted_curvature_fifth s A μ hA hμ
  have hprod := mul_le_mul henergy (pow_le_pow_left₀ hw0 hweights 4)
    (by positivity : 0 ≤ (∑ i ∈ s, 1 / Real.sqrt (μ i)) ^ 4) hH
  have hp := mul_le_mul_of_nonneg_left (hh.trans hprod) (pow_nonneg hc 5)
  have hs : Real.sqrt Afinal ^ 4 = Afinal ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hAf]
  rw [mul_pow, hs] at hp
  have ht := mul_le_mul_of_nonneg_right htune (sq_nonneg Afinal)
  apply (pow_le_pow_iff_left₀ (mul_nonneg hc (sum_nonneg (fun i hi => Real.rpow_nonneg (hA i hi) _)))
    (sq_nonneg _) (by norm_num : (5 : ℕ) ≠ 0)).mp
  rw [mul_pow, ← pow_mul, Nat.mul_comm 2 5, pow_mul, fifth_root_pow hAf]
  nlinarith only [hp, ht]


lemma normalized_growth {ι : Type*} (s : Finset ι) (A μ : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hμ : ∀ i ∈ s, 0 < μ i)
    {Γ Afinal : ℝ} (hΓ : 0 < Γ) (hAf : 0 ≤ Afinal)
    (henergy : (∑ i ∈ s, A i * μ i ^ 2) ≤ 2 * Γ)
    (hweights : (∑ i ∈ s, 1 / Real.sqrt (μ i)) ≤ 8 * Real.sqrt Afinal) :
    (1 / (8 * Γ ^ (1 / 5 : ℝ))) * (∑ i ∈ s, A i ^ (1 / 5 : ℝ)) ≤
      (Afinal ^ (1 / 5 : ℝ)) ^ 2 := by
  apply weighted_growth s A μ hA hμ (by positivity : 0 ≤ 2 * Γ)
    (by positivity) hAf henergy hweights
  rw [div_pow, mul_pow, fifth_root_pow hΓ.le]
  field_simp
  nlinarith only [hΓ]


lemma sequence_growth (b : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hb : ∀ k, 0 ≤ b k) (hbpos : ∀ k, 0 < k → 0 < b k)
    (hrec : ∀ k, c * (∑ i ∈ range (k + 1), b i) ≤ b k ^ 2) :
    ∀ k, c * k / 2 ≤ b k := by
  have hsumformula (j : ℕ) : (∑ i ∈ range j, (i : ℝ)) = (j : ℝ) * (j - 1 : ℝ) / 2 := by
    induction j with
    | zero => simp
    | succ j hj => rw [sum_range_succ, hj]; push_cast; ring
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · simpa [hk] using hb 0
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hself : c ≤ b k := by
      have hsum : b k ≤ ∑ i ∈ range (k + 1), b i :=
        single_le_sum (fun i _ => hb i) (mem_range.mpr (Nat.lt_succ_self k))
      have hm := mul_le_mul_of_nonneg_left hsum hc.le
      have hp := hbpos k hkpos
      nlinarith [hrec k]
    have hprevious : (∑ i ∈ range k, c * (i : ℝ) / 2) ≤ ∑ i ∈ range k, b i :=
      sum_le_sum (fun i hi => ih i (mem_range.mp hi))
    have hsumid : (∑ i ∈ range k, c * (i : ℝ) / 2) = c * k * (k - 1 : ℝ) / 4 := by
      rw [← sum_div, ← mul_sum]
      rw [hsumformula k]
      ring
    rw [hsumid] at hprevious
    have htotal := hrec k
    rw [sum_range_succ] at htotal
    have hprev := mul_le_mul_of_nonneg_left hprevious hc.le
    by_contra hnot
    have hlt : b k < c * k / 2 := lt_of_not_ge hnot
    have hprod := mul_pos (sub_pos.mpr hlt)
      (show 0 < c * k / 2 + b k - c by linarith)
    have hkc : 0 < c ^ 2 * (k : ℝ) := mul_pos (sq_pos_of_pos hc) (by exact_mod_cast hkpos)
    nlinarith only [htotal, hprev, hprod, hkc]

lemma step_weight_sum (b t : ℕ → ℝ) (up : ℕ → Prop) [DecidablePred up]
    (hstep : ∀ k, b (k + 1) = if up k then b k / 2 else 2 * b k)
    (ht0 : 0 ≤ t 0) (hmono : Monotone t)
    (hdown : ∀ k, ¬up k → b k ≤ 2 * (t (k + 1) - t k))
    (N : ℕ) (hbN : 0 ≤ b N) (hinit : b 0 ≤ t N) :
    (∑ k ∈ range N, b k) ≤ 8 * t N := by
  have hid (j : ℕ) : (∑ k ∈ range j, b k) + 2 * b j =
      3 * (∑ k ∈ range j, if up k then 0 else b k) + 2 * b 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [sum_range_succ, sum_range_succ, hstep j]
      split_ifs <;> nlinarith only [ih]
  have hdsum : (∑ k ∈ range N, if up k then (0 : ℝ) else b k) ≤
      ∑ k ∈ range N, 2 * (t (k + 1) - t k) := by
    apply sum_le_sum
    intro k _
    split_ifs with hu
    · exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hmono (Nat.le_succ k)))
    · exact hdown k hu
  rw [← mul_sum, sum_range_sub] at hdsum
  nlinarith only [hid N, hdsum, hbN, hinit, ht0]

end LongTails.Proofs.QuarticAccelerationGrowth
