import LongTails.Proofs.CenteredLogisticExpansion
import LongTails.Proofs.CenteredLogisticGeometry

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticSlowDrift

open CenteredLogisticExpansion

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma background_force {μ C q : ℝ} {A r : ι → ℝ} (hμ : 0 < μ) (hsmall : μ ≤ 1 / 64)
    (hC : |C| ≤ 17 / 16) (hq : |q| ≤ 4 * μ) (hA : ∀ i, |A i| ≤ 9 / 8)
    (hr : ∀ i, |r i| ≤ μ / 32) (hmean : (𝔼 i, A i) = -μ / 2) :
    let k := 𝔼 i, A i * Real.sigmoid (-(A i * C * q + r i))
    |k + μ / 4 + (C * q / 4) * (𝔼 i, A i ^ 2)| ≤ μ / 16 := by
  let s := fun i => A i * C * q + r i
  let rem := fun i => Real.sigmoid (-s i) - 1 / 2 + s i / 4
  have hs (i : ι) : |s i| ≤ 6 * μ := by
    calc |s i| ≤ |A i * C * q| + |r i| := abs_add_le _ _
         _ = |A i| * |C| * |q| + |r i| := by simp only [abs_mul]
         _ ≤ 9 / 8 * (17 / 16) * (4 * μ) + μ / 32 := by
           exact add_le_add (mul_le_mul (mul_le_mul (hA i) hC (abs_nonneg _) (by norm_num))
             hq (abs_nonneg _) (by norm_num)) (hr i)
         _ ≤ _ := by linarith
  have hrem (i : ι) : |rem i| ≤ μ / 64 := by
    have h := sigmoid_cubic (-s i)
    rw [abs_neg, neg_div, sub_neg_eq_add] at h
    have hsq := mul_self_le_mul_self hμ.le hsmall
    have hc := mul_le_mul_of_nonneg_right hsq hμ.le
    have hpower := pow_le_pow_left₀ (abs_nonneg _) (hs i) 3
    change |Real.sigmoid (-s i) - 1 / 2 + s i / 4| ≤ _
    nlinarith
  let err := fun i => A i * (rem i - r i / 4)
  have he (i : ι) : |err i| ≤ μ / 16 := by
    have hbr : |rem i - r i / 4| ≤ μ / 64 + μ / 32 / 4 := by
      calc _ ≤ |rem i| + |r i / 4| := abs_sub _ _
           _ ≤ _ := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
                       exact add_le_add (hrem i) (div_le_div_of_nonneg_right (hr i) (by norm_num))
    calc |err i| = |A i| * |rem i - r i / 4| := abs_mul _ _
         _ ≤ 9 / 8 * (μ / 64 + μ / 32 / 4) :=
           mul_le_mul (hA i) hbr (abs_nonneg _) (by norm_num)
         _ ≤ _ := by linarith
  have hid (i : ι) : A i * Real.sigmoid (-s i) =
      A i / 2 - C * q / 4 * (A i ^ 2) + err i := by dsimp [err, rem, s]; ring
  change |(𝔼 i, A i * Real.sigmoid (-s i)) + μ / 4 + _| ≤ _
  simp_rw [hid, Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.expect_div,
    ← Finset.mul_expect, hmean]
  convert (Finset.abs_expect_le (s := Finset.univ) (f := err)).trans
    (Finset.expect_le Finset.univ_nonempty (fun i _ => he i)) using 1
  congr 1
  ring

lemma trapping {μ C η q A k : ℝ} (hμ : 0 < μ) (hC : 15 / 16 ≤ C) (hC' : C ≤ 17 / 16)
    (hη : 1 ≤ η) (hη' : η ≤ 2) (hA : 3 / 4 ≤ A) (hA' : A ≤ 3 / 2)
    (hlo : -4 * μ ≤ q) (hhi : q ≤ 0)
    (herr : |k + μ / 4 + (C * q / 4) * A| ≤ μ / 16) :
    -4 * μ ≤ q + η * C * k ∧ q + η * C * k ≤ -μ / 8 ∧ |k| ≤ 4 * μ := by
  let f := k + (C * q / 4) * A
  have hfl : -(5 / 16) * μ ≤ f := by dsimp [f]; linarith [(abs_le.mp herr).1]
  have hfu : f ≤ -(3 / 16) * μ := by dsimp [f]; linarith [(abs_le.mp herr).2]
  have hC0 : 0 ≤ C := by linarith
  have hη0 : 0 ≤ η := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hp := mul_le_mul hη' hC' hC0 (by norm_num : (0 : ℝ) ≤ 2)
  have hp0 := mul_nonneg hη0 hC0
  have hprod := mul_le_mul hC' hA' hA0 (by norm_num : (0 : ℝ) ≤ 17 / 16)
  have hlprod := mul_le_mul hC hA (by norm_num : (0 : ℝ) ≤ 3 / 4) hC0
  have hcoef : 0 ≤ 1 - η * C * (C * A) / 4 := by
    nlinarith [mul_le_mul hp hprod (mul_nonneg hC0 hA0) (by norm_num : 0 ≤ 2 * (17 / 16 : ℝ))]
  have hfpos : 0 ≤ (C * A) * μ + f := by
    linarith [mul_le_mul_of_nonneg_right hlprod hμ.le]
  have hpmin := mul_le_mul hη hC (by norm_num : (0 : ℝ) ≤ 15 / 16) hη0
  have hupper := mul_le_mul_of_nonneg_left hfu hp0
  have := mul_le_mul_of_nonneg_right hpmin hμ.le
  have hqlo := mul_le_mul_of_nonneg_left hlo hcoef
  have hqhi := mul_nonpos_of_nonneg_of_nonpos hcoef hhi
  have hbounded := mul_le_mul_of_nonneg_right hprod hμ.le
  have hboundq := mul_le_mul_of_nonneg_left hlo (mul_nonneg hC0 hA0)
  dsimp [f] at *
  refine ⟨?_, ?_, abs_le.mpr ⟨?_, ?_⟩⟩
  · nlinarith [mul_nonneg hp0 hfpos]
  · nlinarith
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hC0 hA0) hhi]
  · nlinarith

end LongTails.Proofs.CenteredLogisticSlowDrift
