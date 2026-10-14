import LongTails.Proofs.DiscreteRittResolvent
import LongTails.Proofs.MarkovRenewalTransfer
import LongTails.Proofs.CensoredBlockEnergy
import LongTails.Proofs.MarkovCovarianceEstimates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace OracleTemplate.MarkovProduct

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

noncomputable def renewalKernel (Φ : ℕ → B →L[ℂ] B) (α q : ℝ) (z : ℂ) : B →L[ℂ] B :=
  ((α : ℂ) * z) • operatorSeries (fun k => Φ (k + 1)) ((q : ℂ) * z)

noncomputable def renewalScalar (α q : ℝ) (z : ℂ) : ℂ := (α : ℂ) * z / (1 - (q : ℂ) * z)

omit [CompleteSpace B] in
lemma renewalKernel_zero (Φ : ℕ → B →L[ℂ] B) (α q : ℝ) : renewalKernel Φ α q 0 = 0 := by
  simp [renewalKernel]

omit [CompleteSpace B] in
lemma norm_renewalKernel_le (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    {α q : ℝ} (hα : 0 ≤ α) (hq : 0 ≤ q) (z : ℂ) (hz : q * ‖z‖ < 1) :
    ‖renewalKernel Φ α q z‖ ≤ α * ‖z‖ / (1 - q * ‖z‖) := by
  have hn : ‖(q : ℂ) * z‖ = q * ‖z‖ := by simp [abs_of_nonneg hq]
  have hc := norm_operatorSeries_le (fun k => Φ (k + 1)) (fun k => hΦ (k + 1)) (by rwa [hn])
  rw [renewalKernel, norm_smul, norm_mul]
  have ha : ‖(α : ℂ)‖ = α := by simp [abs_of_nonneg hα]
  rw [ha]
  calc
    _ ≤ α * ‖z‖ * (1 / (1 - q * ‖z‖)) := by rw [hn] at hc; gcongr
    _ = _ := by ring

omit [CompleteSpace B] in
lemma renewalKernel_eq_series (Φ : ℕ → B →L[ℂ] B) (α q : ℝ) (z : ℂ) :
    renewalKernel Φ α q z =
      z • operatorSeries (fun k => ((α : ℂ) * (q : ℂ) ^ k) • Φ (k + 1)) z := by
  unfold renewalKernel operatorSeries
  rw [← tsum_const_smul'', ← tsum_const_smul'']
  apply tsum_congr
  intro k
  simp only [smul_smul, mul_pow]
  congr 1
  ring

omit [CompleteSpace B] in
lemma renewalKernel_one (Φ : ℕ → B →L[ℂ] B) (q : ℝ) :
    renewalKernel Φ (1 - q) q 1 = geometricMean q Φ := by
  unfold renewalKernel operatorSeries geometricMean
  simp only [mul_one]
  change ((1 - q : ℝ) : ℂ) • (∑' k : ℕ, (q : ℂ) ^ k • Φ (k + 1)) =
    ((1 - q : ℝ) : ℂ) • (∑' k : ℕ, ((q ^ k : ℝ) : ℂ) • Φ (k + 1))
  simp only [Complex.ofReal_pow]

lemma isUnit_one_sub_renewalKernel (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    IsUnit (1 - renewalKernel Φ (1 - q) q z) := by
  have hqz : q * ‖z‖ < 1 := by nlinarith [norm_nonneg z]
  apply isUnit_one_sub_of_norm_lt_one
  apply (norm_renewalKernel_le Φ hΦ (by linarith) hq z hqz).trans_lt
  apply (div_lt_one (by linarith : 0 < 1 - q * ‖z‖)).mpr
  nlinarith

omit [CompleteSpace B] in
lemma norm_renewalScaling_le_one (V : ℕ → B →L[ℂ] B) (hV : ∀ k, ‖V k‖ ≤ 1)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) : ‖renewalScaling (α : ℂ) V n‖ ≤ 1 := by
  by_cases hn : n = 0
  · rw [hn, renewalScaling_zero]
    exact ContinuousLinearMap.norm_id_le
  · rw [renewalScaling, ite_eq_right hn, norm_smul]
    have ha : ‖(α : ℂ)‖ = α := by simp [abs_of_nonneg hα]
    rw [ha]
    nlinarith [hV n, norm_nonneg (V n)]

omit [CompleteSpace B] in
lemma norm_renewal_coefficient_le (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    {α q : ℝ} (hα : 0 ≤ α) (hq : 0 ≤ q) (hq1 : q ≤ 1) (k : ℕ) :
    ‖((α : ℂ) * (q : ℂ) ^ k) • Φ (k + 1)‖ ≤ α := by
  rw [norm_smul, norm_mul, norm_pow]
  have ha : ‖(α : ℂ)‖ = α := by simp [abs_of_nonneg hα]
  have hqn : ‖(q : ℂ)‖ = q := by simp [abs_of_nonneg hq]
  rw [ha, hqn]
  have hpow : q ^ k ≤ 1 := pow_le_one₀ hq hq1
  have hpow0 := pow_nonneg hq k
  calc
    _ ≤ α * 1 * 1 := by gcongr; exact hΦ (k + 1)
    _ = α := by ring

lemma renewalSeries_inverse (Φ V : ℕ → B →L[ℂ] B)
    (hΦ : ∀ k, ‖Φ k‖ ≤ 1) (hV : ∀ k, ‖V k‖ ≤ 1)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hrec : ∀ n, V (n + 1) = (q : ℂ) ^ n • Φ (n + 1) + ∑ k ∈ Finset.range n,
      (((1 - q : ℝ) : ℂ) * (q : ℂ) ^ k) • (Φ (k + 1) * V (n - k)))
    {z : ℂ} (hz : ‖z‖ < 1) :
    operatorSeries (renewalScaling ((1 - q : ℝ) : ℂ) V) z =
      Ring.inverse (1 - renewalKernel Φ (1 - q) q z) := by
  have hα : 0 ≤ 1 - q := by linarith
  have hα1 : 1 - q ≤ 1 := by linarith
  have hu := norm_renewalScaling_le_one V hV hα hα1
  have hc := norm_renewal_coefficient_le Φ hΦ hα hq hq1.le
  have hr := renewalScaling_recurrence Φ V (q : ℂ) ((1 - q : ℝ) : ℂ) hrec
  have he := operatorSeries_renewal_identity _ _ hc hu (renewalScaling_zero _ V)
    (fun n => by simpa only [smul_mul_assoc] using hr n) hz
  rw [← renewalKernel_eq_series] at he
  have hi := isUnit_one_sub_renewalKernel Φ hΦ hq hq1 hz
  have hh := congrArg (fun X => Ring.inverse (1 - renewalKernel Φ (1 - q) q z) * X) he
  rw [← mul_assoc, Ring.inverse_mul_cancel _ hi, one_mul, mul_one] at hh
  exact hh

lemma renewal_source_series (Φ V : ℕ → B →L[ℂ] B)
    (hΦ : ∀ k, ‖Φ k‖ ≤ 1) (hV : ∀ k, ‖V k‖ ≤ 1)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hrec : ∀ n, V (n + 1) = (q : ℂ) ^ n • Φ (n + 1) + ∑ k ∈ Finset.range n,
      (((1 - q : ℝ) : ℂ) * (q : ℂ) ^ k) • (Φ (k + 1) * V (n - k)))
    (A : B →L[ℂ] B) {z : ℂ} (hz : ‖z‖ < 1) :
    operatorSeries (fun n => renewalScaling ((1 - q : ℝ) : ℂ) V n * A) z =
      Ring.inverse (1 - renewalKernel Φ (1 - q) q z) * A := by
  have hu := norm_renewalScaling_le_one V hV (by linarith : 0 ≤ 1 - q) (by linarith)
  have hh := ((summable_operatorSeries _ hu hz).hasSum.mul_right A).tsum_eq
  have hi := renewalSeries_inverse Φ V hΦ hV hq hq1 hrec hz
  simp only [operatorSeries, smul_mul_assoc] at hh ⊢
  rw [← hi]
  exact hh

lemma operatorSeries_forward_difference (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) • operatorSeries (fun k => Φ (k + 1)) z =
      Φ 0 + operatorSeries (fun k => Φ (k + 1) - Φ k) z := by
  have hd : operatorSeries (fun k => Φ (k + 1) - Φ k) z =
      operatorSeries (fun k => Φ (k + 1)) z - operatorSeries Φ z := by
    unfold operatorSeries
    simp only [smul_sub]
    exact ((summable_operatorSeries _ (fun k => hΦ (k + 1)) hz).tsum_sub
      (summable_operatorSeries Φ hΦ hz))
  rw [hd, operatorSeries_shift Φ hΦ hz]
  module

lemma operatorSeries_forward_second (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - z) ^ 2 • operatorSeries (fun k => Φ (k + 1)) z =
      (1 - z) • Φ 0 + (Φ 1 - Φ 0) +
        z • operatorSeries (fun k => Φ (k + 2) - 2 • Φ (k + 1) + Φ k) z := by
  have hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ 2 := fun k =>
    (norm_sub_le _ _).trans (by linarith [hΦ (k + 1), hΦ k])
  rw [pow_two, mul_smul, operatorSeries_forward_difference Φ hΦ hz, smul_add,
    operatorSeries_abel_first _ hd hz]
  have he : (fun k => Φ (k + 1 + 1) - Φ (k + 1) - (Φ (k + 1) - Φ k)) =
      (fun k => Φ (k + 2) - 2 • Φ (k + 1) + Φ k) := by funext k; abel
  rw [he]
  abel

lemma renewalKernel_abel_second (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) (α q : ℝ) (z : ℂ) (hz : ‖(q : ℂ) * z‖ < 1) :
    (1 - (q : ℂ) * z) ^ 2 • renewalKernel Φ α q z =
      ((α : ℂ) * z * (1 - (q : ℂ) * z)) • (1 : B →L[ℂ] B) +
        ((α : ℂ) * z) • (Φ 1 - 1) +
        ((α : ℂ) * (q : ℂ) * z ^ 2) •
          operatorSeries (fun k => Φ (k + 2) - 2 • Φ (k + 1) + Φ k) ((q : ℂ) * z) := by
  rw [renewalKernel, smul_comm, operatorSeries_forward_second Φ hΦ hz, hzero]
  simp only [smul_add, smul_smul]
  congr 1
  congr 1
  ring

lemma renewalKernel_abel_difference (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) (α q : ℝ) (z : ℂ) (hz : ‖(q : ℂ) * z‖ < 1) :
    (1 - (q : ℂ) * z) ^ 2 • (renewalKernel Φ α q z - renewalScalar α q z • 1) =
      ((α : ℂ) * z) • (Φ 1 - 1) + ((α : ℂ) * (q : ℂ) * z ^ 2) •
        operatorSeries (fun k => Φ (k + 2) - 2 • Φ (k + 1) + Φ k) ((q : ℂ) * z) := by
  have hd : 1 - (q : ℂ) * z ≠ 0 := by
    intro he
    have hh := sub_eq_zero.mp he
    rw [← hh, norm_one] at hz
    linarith
  have hs : (1 - (q : ℂ) * z) ^ 2 * renewalScalar α q z =
      (α : ℂ) * z * (1 - (q : ℂ) * z) := by
    unfold renewalScalar
    field_simp
  rw [smul_sub, smul_smul, hs, renewalKernel_abel_second Φ hΦ hzero α q z hz]
  abel

lemma norm_renewalKernel_abel_difference (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α q b : ℝ} (hα : 0 ≤ α) (hq : 0 ≤ q)
    (hfirst : ‖Φ 1 - 1‖ ≤ b)
    (hsecond : ∀ k, ‖Φ (k + 2) - 2 • Φ (k + 1) + Φ k‖ ≤ b ^ 2)
    (z : ℂ) (hz : q * ‖z‖ < 1) :
    ‖1 - (q : ℂ) * z‖ ^ 2 * ‖renewalKernel Φ α q z - renewalScalar α q z • 1‖ ≤
      α * ‖z‖ * b + α * q * ‖z‖ ^ 2 * (b ^ 2 / (1 - q * ‖z‖)) := by
  have hn : ‖(q : ℂ) * z‖ = q * ‖z‖ := by simp [abs_of_nonneg hq]
  have hseries := norm_operatorSeries_le _ hsecond (by rwa [hn])
  rw [hn] at hseries
  have ha : ‖(α : ℂ)‖ = α := by simp [abs_of_nonneg hα]
  have hqn : ‖(q : ℂ)‖ = q := by simp [abs_of_nonneg hq]
  calc
    _ = ‖(1 - (q : ℂ) * z) ^ 2 • (renewalKernel Φ α q z - renewalScalar α q z • 1)‖ := by
      rw [norm_smul, norm_pow]
    _ = ‖((α : ℂ) * z) • (Φ 1 - 1) + ((α : ℂ) * (q : ℂ) * z ^ 2) •
        operatorSeries (fun k => Φ (k + 2) - 2 • Φ (k + 1) + Φ k) ((q : ℂ) * z)‖ :=
      congrArg norm (renewalKernel_abel_difference Φ hΦ hzero α q z (by rwa [hn]))
    _ ≤ ‖((α : ℂ) * z) • (Φ 1 - 1)‖ + ‖((α : ℂ) * (q : ℂ) * z ^ 2) •
        operatorSeries (fun k => Φ (k + 2) - 2 • Φ (k + 1) + Φ k) ((q : ℂ) * z)‖ := norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_smul, norm_mul, norm_pow, ha, hqn]
      gcongr

lemma ritt_scaled_resolvent (Ψ : B →L[ℂ] B) (hΨ : ‖Ψ‖ ≤ 1)
    (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - Ψ) * Ψ ^ n‖ ≤ 5)
    (r : ℂ) (hr : r ≠ 0) (hr1 : r ≠ 1)
    (hsector : -(|((1 - r) / r).im| / 128) ≤ ((1 - r) / r).re) :
    IsUnit (1 - r • Ψ) ∧ ‖Ring.inverse (1 - r • Ψ)‖ ≤ 128 / ‖1 - r‖ := by
  let ζ := (1 - r) / r
  have hζ : ζ ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hr1)) hr
  obtain ⟨hC, hCn⟩ := ritt_resolvent_sector Ψ hΨ hR ζ hζ hsector
  have hfac : r • (ζ • (1 : B →L[ℂ] B) + (1 - Ψ)) = 1 - r • Ψ := by
    rw [smul_add, smul_sub, smul_smul]
    have he : r * ζ = 1 - r := by dsimp [ζ]; field_simp
    rw [he, sub_smul, one_smul]
    abel
  have hunit : IsUnit (1 - r • Ψ) := by
    rw [← hfac]
    exact IsUnit.smul (Units.mk0 r hr) hC
  have hmul : (r⁻¹ • Ring.inverse (ζ • 1 + (1 - Ψ))) * (1 - r • Ψ) = 1 := by
    rw [← hfac, smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hr, one_smul,
      Ring.inverse_mul_cancel _ hC]
  have hinv : Ring.inverse (1 - r • Ψ) = r⁻¹ • Ring.inverse (ζ • 1 + (1 - Ψ)) := by
    symm
    simpa only [one_mul] using (Ring.eq_mul_inverse_iff_mul_eq _ 1 _ hunit).mpr hmul
  refine ⟨hunit, ?_⟩
  rw [hinv, norm_smul, norm_inv]
  calc
    _ ≤ ‖r‖⁻¹ * (128 / ‖ζ‖) := mul_le_mul_of_nonneg_left hCn (by positivity)
    _ = 128 / ‖1 - r‖ := by
      dsimp [ζ]
      rw [norm_div]
      have hn : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
      field_simp

omit [CompleteSpace B] in
lemma norm_resolvent_source_le (Ψ : B →L[ℂ] B) (r : ℂ) (hr : r ≠ 0)
    (hu : IsUnit (1 - r • Ψ))
    (hn : ‖Ring.inverse (1 - r • Ψ)‖ ≤ 128 / ‖1 - r‖) (hr1 : r ≠ 1) :
    ‖Ring.inverse (1 - r • Ψ) * (1 - Ψ)‖ ≤ 129 / ‖r‖ := by
  let R := Ring.inverse (1 - r • Ψ)
  have he : r • (R * (1 - Ψ)) = 1 - (1 - r) • R := by
    have hh := Ring.inverse_mul_cancel (1 - r • Ψ) hu
    change R * (1 - r • Ψ) = 1 at hh
    rw [mul_sub, mul_one, mul_smul_comm] at hh
    rw [sub_smul, one_smul, mul_sub, mul_one, smul_sub]
    rw [← hh]
    abel
  have hdn : 0 < ‖1 - r‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hr1))
  have hd : ‖1 - r‖ * ‖R‖ ≤ 128 := by
    have h := (le_div_iff₀ hdn).mp hn
    dsimp [R]
    nlinarith
  have hi : ‖(1 : B →L[ℂ] B)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hbound : ‖r‖ * ‖R * (1 - Ψ)‖ ≤ 129 := by
    calc
      _ = ‖r • (R * (1 - Ψ))‖ := (norm_smul _ _).symm
      _ = ‖1 - (1 - r) • R‖ := congrArg norm he
      _ ≤ ‖(1 : B →L[ℂ] B)‖ + ‖1 - r‖ * ‖R‖ := by simpa only [norm_smul] using norm_sub_le (1 : B →L[ℂ] B) ((1 - r) • R)
      _ ≤ 129 := by linarith
  apply (le_div_iff₀ (norm_pos_iff.mpr hr)).mpr
  dsimp [R] at hbound
  nlinarith

omit [CompleteSpace B] in
lemma norm_sequence_sub_initial_le (Φ : ℕ → B →L[ℂ] B) {b : ℝ}
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ b) (n : ℕ) : ‖Φ n - Φ 0‖ ≤ n * b := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : Φ (n + 1) - Φ 0 = (Φ (n + 1) - Φ n) + (Φ n - Φ 0) := by abel
    rw [he]
    calc
      _ ≤ ‖Φ (n + 1) - Φ n‖ + ‖Φ n - Φ 0‖ := norm_add_le _ _
      _ ≤ b + n * b := add_le_add (hd n) ih
      _ = _ := by push_cast; ring

lemma norm_complex_pow_sub_one_le (z : ℂ) {t : ℝ} (ht : 1 ≤ t) (hz : ‖z‖ ≤ t) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ n * ‖z - 1‖ * t ^ n := by
  have ht0 : 0 ≤ t := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z ^ (n + 1) - 1 = z ^ n * (z - 1) + (z ^ n - 1) := by ring
    rw [he]
    calc
      _ ≤ ‖z ^ n * (z - 1)‖ + ‖z ^ n - 1‖ := norm_add_le _ _
      _ ≤ t ^ n * ‖z - 1‖ + n * ‖z - 1‖ * t ^ n := by
        rw [norm_mul, norm_pow]
        gcongr
      _ = (n + 1 : ℝ) * ‖z - 1‖ * t ^ n := by ring
      _ ≤ (n + 1 : ℝ) * ‖z - 1‖ * t ^ (n + 1) := by
        rw [pow_succ]
        have hn : 0 ≤ (n + 1 : ℝ) * ‖z - 1‖ * t ^ n := by positivity
        nlinarith
      _ = _ := by push_cast; rfl

lemma hasSum_succ_sq_geometric {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * x ^ n) ((1 + x) / (1 - x) ^ 3) := by
  have hn : ‖x‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hx]
  have hs := ((hasSum_sq_mul_geometric_of_norm_lt_one hn).add
    ((hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left 2)).add
    (hasSum_geometric_of_lt_one hx hx1)
  convert hs using 1
  · ext n
    ring
  · have hne : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
    field_simp
    ring

lemma ritt_renewal_perturbation (Ψ K : B →L[ℂ] B) (hΨ : ‖Ψ‖ ≤ 1)
    (hR : ∀ n : ℕ, ((n : ℝ) + 1) * ‖(1 - Ψ) * Ψ ^ n‖ ≤ 5)
    (r : ℂ) (hr : 9 / 10 ≤ ‖r‖) (hr1 : r ≠ 1)
    (hsector : -(|((1 - r) / r).im| / 128) ≤ ((1 - r) / r).re)
    (hE : ‖K - r • Ψ‖ ≤ ‖1 - r‖ / 500) :
    IsUnit (1 - K) ∧ ‖Ring.inverse (1 - K) * (1 - Ψ)‖ ≤ 300 := by
  have hrpos : 0 < ‖r‖ := by linarith
  have hr0 : r ≠ 0 := norm_pos_iff.mp hrpos
  have hd : 0 < ‖1 - r‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hr1))
  obtain ⟨hu, hn⟩ := ritt_scaled_resolvent Ψ hΨ hR r hr0 hr1 hsector
  have hs := norm_resolvent_source_le Ψ r hr0 hu hn hr1
  have hsmall : ‖Ring.inverse (1 - r • Ψ) * (-(K - r • Ψ))‖ ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ ‖Ring.inverse (1 - r • Ψ)‖ * ‖-(K - r • Ψ)‖ := norm_mul_le _ _
      _ ≤ (128 / ‖1 - r‖) * (‖1 - r‖ / 500) := by rw [norm_neg]; gcongr
      _ ≤ 1 / 2 := by field_simp; norm_num
  have hp := inverse_add_source_bound (1 - r • Ψ) (-(K - r • Ψ)) (1 - Ψ) hu
    (by norm_num : (1 / 2 : ℝ) < 1) hsmall
  have he : (1 - r • Ψ) + -(K - r • Ψ) = 1 - K := by abel
  rw [he] at hp
  norm_num at hp
  refine ⟨hp.1, hp.2.trans ?_⟩
  calc
    _ ≤ 2 * (129 / ‖r‖) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ 300 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hrpos).mpr
      linarith

lemma renewal_disk_geometry {α : ℝ} (hα1 : α ≤ 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1 + α / 8) :
    7 * α / 8 ≤ 1 - (1 - α) * ‖z‖ ∧
      1 - (1 - α) * ‖z‖ ≤ ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ∧ ‖z‖ ≤ 9 / 8 := by
  have hq : 0 ≤ 1 - α := by linarith
  have hmul := mul_le_mul_of_nonneg_left hz hq
  have hgeom : 7 * α / 8 ≤ 1 - (1 - α) * ‖z‖ := by nlinarith [sq_nonneg α]
  have hnorm := norm_sub_norm_le (1 : ℂ) (((1 - α : ℝ) : ℂ) * z)
  have hn : ‖((1 - α : ℝ) : ℂ) * z‖ = (1 - α) * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  rw [norm_one, hn] at hnorm
  exact ⟨hgeom, hnorm, by linarith⟩

lemma renewal_global_abel_arithmetic {α q t d e N : ℝ}
    (hα : 0 < α) (hq1 : q ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 8)
    (hd : 7 * α / 8 ≤ d) (he : 7 * α / 8 ≤ e)
    (hN : d ^ 2 * N ≤ α * t * (α / 5000) +
      α * q * t ^ 2 * ((α / 5000) ^ 2 / e)) : N ≤ 3 / 10000 := by
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hdsq : 49 * α ^ 2 / 64 ≤ d ^ 2 := by nlinarith [sq_nonneg (d - 7 * α / 8)]
  have hde : 343 * α ^ 3 / 512 ≤ d ^ 2 * e := by
    have hh := mul_le_mul hdsq he (by positivity : 0 ≤ 7 * α / 8) (sq_nonneg d)
    nlinarith [hh]
  have hfirst : α * t * (α / 5000) ≤ (299 / 1000000) * d ^ 2 := by
    have h := mul_le_mul_of_nonneg_left ht1 (sq_nonneg α)
    nlinarith [h]
  have hsecond : α * q * t ^ 2 * ((α / 5000) ^ 2 / e) ≤ (1 / 1000000) * d ^ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ he0).mpr
    calc
      _ ≤ α * 1 * (9 / 8) ^ 2 * (α / 5000) ^ 2 := by gcongr
      _ ≤ (1 / 1000000) * d ^ 2 * e := by nlinarith [hde, pow_pos hα 3]
  have hh : d ^ 2 * N ≤ d ^ 2 * (3 / 10000) := by linarith
  exact le_of_mul_le_mul_left hh (sq_pos_of_pos hd0)

lemma norm_renewalKernel_global (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hfirst : ‖Φ 1 - 1‖ ≤ α / 5000)
    (hsecond : ∀ k, ‖Φ (k + 2) - 2 • Φ (k + 1) + Φ k‖ ≤ (α / 5000) ^ 2)
    (z : ℂ) (hz : ‖z‖ ≤ 1 + α / 8) :
    ‖renewalKernel Φ α (1 - α) z - renewalScalar α (1 - α) z • 1‖ ≤ 3 / 10000 := by
  obtain ⟨he, hd, ht⟩ := renewal_disk_geometry hα1 z hz
  have hq : 0 ≤ 1 - α := by linarith
  have hq1 : 1 - α ≤ 1 := by linarith
  have hqz : (1 - α) * ‖z‖ < 1 := by linarith
  exact renewal_global_abel_arithmetic hα hq1 (norm_nonneg z) ht
    (he.trans hd) he (norm_renewalKernel_abel_difference Φ hΦ hzero hα.le hq hfirst hsecond z hqz)

omit [CompleteSpace B] in
lemma operatorSeries_constant (X : B →L[ℂ] B) {z : ℂ} (hz : ‖z‖ < 1) :
    operatorSeries (fun _ => X) z = (1 - z)⁻¹ • X := by
  exact ((hasSum_geometric_of_norm_lt_one hz).smul_const X).tsum_eq

lemma renewalKernel_sub_scalar (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (α q : ℝ) (z : ℂ) (hz : ‖(q : ℂ) * z‖ < 1) :
    renewalKernel Φ α q z - renewalScalar α q z • 1 =
      ((α : ℂ) * z) • operatorSeries (fun k => Φ (k + 1) - 1) ((q : ℂ) * z) := by
  have hi : ‖(1 : B →L[ℂ] B)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hs : operatorSeries (fun k => Φ (k + 1) - 1) ((q : ℂ) * z) =
      operatorSeries (fun k => Φ (k + 1)) ((q : ℂ) * z) -
        operatorSeries (fun _ => (1 : B →L[ℂ] B)) ((q : ℂ) * z) := by
    unfold operatorSeries
    simp only [smul_sub]
    exact (summable_operatorSeries _ (fun k => hΦ (k + 1)) hz).tsum_sub
      (summable_operatorSeries _ (fun _ => hi) hz)
  rw [hs, smul_sub, operatorSeries_constant _ hz]
  simp only [renewalKernel, renewalScalar, div_eq_mul_inv, smul_smul]

lemma renewalKernel_centered_difference (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    {α q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (z : ℂ) (hz : ‖(q : ℂ) * z‖ < 1) :
    (renewalKernel Φ α q z - renewalScalar α q z • 1) -
      (renewalKernel Φ α q 1 - renewalScalar α q 1 • 1) =
      ∑' k : ℕ, ((α : ℂ) * (q : ℂ) ^ k * (z ^ (k + 1) - 1)) • (Φ (k + 1) - 1) := by
  have hqn : ‖(q : ℂ) * 1‖ < 1 := by simpa [abs_of_nonneg hq] using hq1
  have hd : ∀ k, ‖Φ (k + 1) - 1‖ ≤ 2 := by
    intro k
    have hi : ‖(1 : B →L[ℂ] B)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    exact (norm_sub_le _ _).trans (by linarith [hΦ (k + 1)])
  rw [renewalKernel_sub_scalar Φ hΦ α q z hz, renewalKernel_sub_scalar Φ hΦ α q 1 hqn]
  have hzsum := (summable_operatorSeries _ hd hz).const_smul ((α : ℂ) * z)
  have hqsum := (summable_operatorSeries _ hd hqn).const_smul ((α : ℂ) * 1)
  unfold operatorSeries
  rw [← tsum_const_smul'', ← tsum_const_smul'', ← hzsum.tsum_sub hqsum]
  apply tsum_congr
  intro k
  simp only [smul_smul, ← sub_smul, mul_pow, mul_one]
  congr 1
  rw [pow_succ]
  ring

lemma norm_renewalKernel_centered_difference (Φ : ℕ → B →L[ℂ] B)
    (hΦ : ∀ k, ‖Φ k‖ ≤ 1) (hzero : Φ 0 = 1) {α q b t : ℝ}
    (hα : 0 ≤ α) (hq : 0 ≤ q) (ht : 1 ≤ t)
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ b) (z : ℂ) (hz : ‖z‖ ≤ t) (hqt : q * t < 1) :
    ‖(renewalKernel Φ α q z - renewalScalar α q z • 1) -
      (renewalKernel Φ α q 1 - renewalScalar α q 1 • 1)‖ ≤
      (α * b * ‖z - 1‖ * t) * ((1 + q * t) / (1 - q * t) ^ 3) := by
  have ht0 : 0 ≤ t := by linarith
  have hq1 : q < 1 := by nlinarith
  have hqz : ‖(q : ℂ) * z‖ < 1 := by
    have hn : ‖(q : ℂ) * z‖ = q * ‖z‖ := by simp [abs_of_nonneg hq]
    rw [hn]
    exact (mul_le_mul_of_nonneg_left hz hq).trans_lt hqt
  rw [renewalKernel_centered_difference Φ hΦ hq hq1 z hqz]
  have hs := (hasSum_succ_sq_geometric (mul_nonneg hq ht0) hqt).mul_left (α * b * ‖z - 1‖ * t)
  apply tsum_of_norm_bounded hs
  intro k
  have hp := norm_complex_pow_sub_one_le z ht hz (k + 1)
  have hdiff := norm_sequence_sub_initial_le Φ hd (k + 1)
  rw [hzero] at hdiff
  have ha : ‖(α : ℂ)‖ = α := by simp [abs_of_nonneg hα]
  have hqn : ‖(q : ℂ)‖ = q := by simp [abs_of_nonneg hq]
  rw [norm_smul, norm_mul, norm_mul, norm_pow, ha, hqn]
  calc
    _ ≤ α * q ^ k * ((k + 1 : ℕ) * ‖z - 1‖ * t ^ (k + 1)) * ((k + 1 : ℕ) * b) := by
      gcongr
    _ = _ := by push_cast; rw [mul_pow, pow_succ]; ring

lemma renewalScalar_one_sub {α : ℝ} (z : ℂ)
    (hd : 1 - ((1 - α : ℝ) : ℂ) * z ≠ 0) :
    1 - renewalScalar α (1 - α) z = (1 - z) / (1 - ((1 - α : ℝ) : ℂ) * z) := by
  unfold renewalScalar
  apply (eq_div_iff hd).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hd]
  push_cast
  ring

lemma renewalScalar_quotient {α : ℝ} (hα : α ≠ 0) {z : ℂ} (hz : z ≠ 0)
    (hd : 1 - ((1 - α : ℝ) : ℂ) * z ≠ 0) :
    (1 - renewalScalar α (1 - α) z) / renewalScalar α (1 - α) z =
      (1 - z) / ((α : ℂ) * z) := by
  rw [renewalScalar_one_sub z hd]
  unfold renewalScalar
  have hd' : 1 - z * ((1 - α : ℝ) : ℂ) ≠ 0 := by simpa only [mul_comm] using hd
  field_simp [hd, hd', hz, hα]

lemma shifted_reciprocal_sector {α : ℝ} (hα : 0 < α) {z : ℂ} (hz : z ≠ 0)
    (hgeo : (z - 1).re + ‖z - 1‖ ^ 2 ≤ |(z - 1).im| / 128) :
    -(|((1 - z) / ((α : ℂ) * z)).im| / 128) ≤ ((1 - z) / ((α : ℂ) * z)).re := by
  let d : ℝ := α * ‖z‖ ^ 2
  have hd : 0 < d := mul_pos hα (sq_pos_of_pos (norm_pos_iff.mpr hz))
  have hn : Complex.normSq z ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hn' : z.re ^ 2 + z.im ^ 2 ≠ 0 := by simpa only [Complex.normSq_apply, pow_two] using hn
  have ha : α ≠ 0 := ne_of_gt hα
  have hre : ((1 - z) / ((α : ℂ) * z)).re * d = z.re - ‖z‖ ^ 2 := by
    dsimp [d]
    simp only [Complex.div_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero, zero_sub, map_mul, Complex.normSq_ofReal,
      ← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    field_simp [ha, hn, hn']; ring
  have him : ((1 - z) / ((α : ℂ) * z)).im * d = -z.im := by
    dsimp [d]
    simp only [Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero, zero_sub, map_mul, Complex.normSq_ofReal,
      ← Complex.normSq_eq_norm_sq]
    field_simp [ha, hn, hn']; ring
  have habs : |((1 - z) / ((α : ℂ) * z)).im| * d = |z.im| := by
    have h := congrArg abs him
    simpa only [abs_mul, abs_of_pos hd, abs_neg] using h
  have hsq : (z - 1).re + ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - z.re := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
    ring
  rw [hsq] at hgeo
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at hgeo
  have hscaled : (-(|((1 - z) / ((α : ℂ) * z)).im| / 128)) * d ≤
      ((1 - z) / ((α : ℂ) * z)).re * d := by nlinarith
  exact le_of_mul_le_mul_right hscaled hd

lemma renewal_centered_moment_arithmetic {α t x e s : ℝ} (hα : 0 < α)
    (ht : 0 ≤ t) (ht1 : t ≤ 9 / 8) (hx1 : x ≤ 1)
    (he : 7 * α / 8 ≤ e) (hs : 0 ≤ s) :
    (α * (α / 5000) * s * t) * ((1 + x) / e ^ 3) ≤ s / (1000 * α) := by
  have he0 : 0 < e := by linarith
  have he3 : 343 * α ^ 3 / 512 ≤ e ^ 3 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 7 * α / 8) he 3
    nlinarith [hh]
  have htx : t * (1 + x) ≤ 9 / 4 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left htx (pow_nonneg hα.le 3)
  have hprod' := mul_le_mul_of_nonneg_left hprod hs
  have he3' := mul_le_mul_of_nonneg_left he3 hs
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos he0 3) (by positivity : 0 < 1000 * α)).mpr
  nlinarith [mul_nonneg hs (pow_nonneg hα.le 3)]

lemma norm_renewalKernel_centered_small (Φ : ℕ → B →L[ℂ] B)
    (hΦ : ∀ k, ‖Φ k‖ ≤ 1) (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ α / 5000) (z : ℂ) (hz : ‖z‖ ≤ 1 + α / 8) :
    ‖(renewalKernel Φ α (1 - α) z - renewalScalar α (1 - α) z • 1) -
      (renewalKernel Φ α (1 - α) 1 - renewalScalar α (1 - α) 1 • 1)‖ ≤
      ‖z - 1‖ / (1000 * α) := by
  let t : ℝ := max 1 ‖z‖
  have ht : 1 ≤ t := le_max_left _ _
  have hzt : ‖z‖ ≤ t := le_max_right _ _
  have ht0 : 0 ≤ t := by linarith
  have htupper : t ≤ 1 + α / 8 := max_le (by linarith) hz
  have ht1 : t ≤ 9 / 8 := by linarith
  have hq : 0 ≤ 1 - α := by linarith
  have he : 7 * α / 8 ≤ 1 - (1 - α) * t := by
    have hh := mul_le_mul_of_nonneg_left htupper hq
    nlinarith [sq_nonneg α]
  have hqt : (1 - α) * t < 1 := by linarith
  have hn := norm_renewalKernel_centered_difference Φ hΦ hzero hα.le hq ht hd z hzt hqt
  exact hn.trans (renewal_centered_moment_arithmetic hα ht0 ht1 hqt.le he (norm_nonneg _))

lemma renewal_local_scalar_bounds {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (z : ℂ) (hz : ‖z - 1‖ ≤ α / 512) :
    ‖((1 - α : ℝ) : ℂ) * z‖ < 1 ∧ z ≠ 0 ∧
      ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ≤ 3 * α / 2 ∧
      9 / 10 ≤ ‖renewalScalar α (1 - α) z‖ ∧
      ‖1 - renewalScalar α (1 - α) z‖ = ‖z - 1‖ / ‖1 - ((1 - α : ℝ) : ℂ) * z‖ := by
  have hq : 0 ≤ 1 - α := by linarith
  have hq1 : 1 - α ≤ 1 := by linarith
  have hupper := norm_sub_norm_le z (1 : ℂ)
  have hlower := norm_sub_norm_le (1 : ℂ) z
  rw [norm_one] at hupper hlower
  rw [norm_sub_rev (1 : ℂ) z] at hlower
  have hzupper : ‖z‖ ≤ 1 + α / 8 := by linarith
  obtain ⟨he, hden, ht⟩ := renewal_disk_geometry hα1 z hzupper
  have hnorm : ‖((1 - α : ℝ) : ℂ) * z‖ = (1 - α) * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  have hqz : ‖((1 - α : ℝ) : ℂ) * z‖ < 1 := by rw [hnorm]; linarith
  have hzpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hdpos : 0 < ‖1 - ((1 - α : ℝ) : ℂ) * z‖ := by linarith
  have hd0 : 1 - ((1 - α : ℝ) : ℂ) * z ≠ 0 := norm_pos_iff.mp hdpos
  have ha : ‖(α : ℂ)‖ = α := by simp [abs_of_pos hα]
  have hdub : ‖1 - ((1 - α : ℝ) : ℂ) * z‖ ≤ α + ‖z - 1‖ := by
    have heq : 1 - ((1 - α : ℝ) : ℂ) * z = (α : ℂ) + ((1 - α : ℝ) : ℂ) * (1 - z) := by push_cast; ring
    rw [heq]
    calc
      _ ≤ ‖(α : ℂ)‖ + ‖((1 - α : ℝ) : ℂ) * (1 - z)‖ := norm_add_le _ _
      _ = α + (1 - α) * ‖z - 1‖ := by
        rw [ha, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq, norm_sub_rev (1 : ℂ) z]
      _ ≤ α + ‖z - 1‖ := by nlinarith [norm_nonneg (z - 1)]
  have hrnorm : 9 / 10 ≤ ‖renewalScalar α (1 - α) z‖ := by
    rw [renewalScalar, norm_div, norm_mul, ha]
    apply (le_div_iff₀ hdpos).mpr
    have hs : ‖z - 1‖ ≤ 1 / 512 := by linarith
    have hp := mul_le_mul_of_nonneg_left hs hα.le
    have hl := mul_le_mul_of_nonneg_left hlower hα.le
    nlinarith
  refine ⟨hqz, hz0, by linarith, hrnorm, ?_⟩
  rw [renewalScalar_one_sub z hd0, norm_div, norm_sub_rev (1 : ℂ) z]

lemma renewalScalar_at_one {α : ℝ} (hα : α ≠ 0) : renewalScalar α (1 - α) 1 = 1 := by
  unfold renewalScalar
  simp only [mul_one, Complex.ofReal_sub, Complex.ofReal_one, sub_sub_cancel]
  exact div_self (by exact_mod_cast hα)

lemma norm_renewalKernel_one_sub_one (Φ : ℕ → B →L[ℂ] B)
    (hΦ : ∀ k, ‖Φ k‖ ≤ 1) (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ α / 5000) :
    ‖renewalKernel Φ α (1 - α) 1 - 1‖ ≤ 1 / 5000 := by
  have he : renewalKernel Φ α (1 - α) 1 = geometricMean (1 - α) Φ := by
    simpa only [sub_sub_cancel] using renewalKernel_one Φ (1 - α)
  have h := norm_geometricMean_sub_initial_le Φ (by positivity : 0 ≤ α / 5000)
    (by linarith : 0 ≤ 1 - α) (by linarith : 1 - α < 1) hΦ hd
  rw [hzero, sub_sub_cancel] at h
  rw [he]
  convert h using 1
  field_simp

lemma norm_renewalKernel_local_error (Φ : ℕ → B →L[ℂ] B)
    (hΦ : ∀ k, ‖Φ k‖ ≤ 1) (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ α / 5000) (z : ℂ) (hz : ‖z - 1‖ ≤ α / 512) :
    ‖renewalKernel Φ α (1 - α) z - renewalScalar α (1 - α) z • renewalKernel Φ α (1 - α) 1‖ ≤
      ‖1 - renewalScalar α (1 - α) z‖ / 500 := by
  obtain ⟨hqw, hz0, hden, hr, hratio⟩ := renewal_local_scalar_bounds hα hα1 z hz
  have hdpos : 0 < ‖1 - ((1 - α : ℝ) : ℂ) * z‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (((1 - α : ℝ) : ℂ) * z)
    rw [norm_one] at hh
    linarith
  have hs := norm_sub_norm_le z (1 : ℂ)
  rw [norm_one] at hs
  have hzbig : ‖z‖ ≤ 1 + α / 8 := by linarith
  have hc := norm_renewalKernel_centered_small Φ hΦ hzero hα hα1 hd z hzbig
  rw [renewalScalar_at_one (ne_of_gt hα), one_smul] at hc
  have hp := norm_renewalKernel_one_sub_one Φ hΦ hzero hα hα1 hd
  have he : renewalKernel Φ α (1 - α) z - renewalScalar α (1 - α) z • renewalKernel Φ α (1 - α) 1 =
      ((renewalKernel Φ α (1 - α) z - renewalScalar α (1 - α) z • 1) -
        (renewalKernel Φ α (1 - α) 1 - 1)) +
      (1 - renewalScalar α (1 - α) z) • (renewalKernel Φ α (1 - α) 1 - 1) := by module
  have hfirst : ‖z - 1‖ / (1000 * α) ≤ (3 / 2000) * ‖1 - renewalScalar α (1 - α) z‖ := by
    have hid := (eq_div_iff (ne_of_gt hdpos)).mp hratio
    rw [← hid]
    calc
      _ ≤ (‖1 - renewalScalar α (1 - α) z‖ * (3 * α / 2)) / (1000 * α) := by gcongr
      _ = _ := by field_simp; ring
  rw [he]
  calc
    _ ≤ ‖(renewalKernel Φ α (1 - α) z - renewalScalar α (1 - α) z • 1) -
        (renewalKernel Φ α (1 - α) 1 - 1)‖ +
        ‖(1 - renewalScalar α (1 - α) z) • (renewalKernel Φ α (1 - α) 1 - 1)‖ := norm_add_le _ _
    _ ≤ ‖z - 1‖ / (1000 * α) + ‖1 - renewalScalar α (1 - α) z‖ * (1 / 5000) := by
      rw [norm_smul]
      gcongr
    _ ≤ _ := by nlinarith [norm_nonneg (1 - renewalScalar α (1 - α) z)]

lemma renewal_local_resolvent (Φ : ℕ → B →L[ℂ] B) (hΦ : ∀ k, ‖Φ k‖ ≤ 1)
    (hzero : Φ 0 = 1) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ α / 5000)
    (hR : ∀ n : ℕ, ((n : ℝ) + 1) *
      ‖(1 - renewalKernel Φ α (1 - α) 1) * renewalKernel Φ α (1 - α) 1 ^ n‖ ≤ 5)
    (z : ℂ) (hz : ‖z - 1‖ ≤ α / 512) (hz1 : z ≠ 1)
    (hgeo : (z - 1).re + ‖z - 1‖ ^ 2 ≤ |(z - 1).im| / 128) :
    IsUnit (1 - renewalKernel Φ α (1 - α) z) ∧
      ‖Ring.inverse (1 - renewalKernel Φ α (1 - α) z) *
        (1 - renewalKernel Φ α (1 - α) 1)‖ ≤ 300 := by
  obtain ⟨hqw, hz0, hden, hr, hratio⟩ := renewal_local_scalar_bounds hα hα1 z hz
  have hd0 : 1 - ((1 - α : ℝ) : ℂ) * z ≠ 0 := by
    intro he
    have hh := sub_eq_zero.mp he
    rw [← hh, norm_one] at hqw
    linarith
  have hr1 : renewalScalar α (1 - α) z ≠ 1 := by
    have h : 1 - renewalScalar α (1 - α) z ≠ 0 := by
      rw [renewalScalar_one_sub z hd0]
      exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hz1)) hd0
    exact Ne.symm (sub_ne_zero.mp h)
  have hΨ : ‖renewalKernel Φ α (1 - α) 1‖ ≤ 1 := by
    have h := norm_renewalKernel_le Φ hΦ hα.le (by linarith : 0 ≤ 1 - α) 1
      (by simpa using (show 1 - α < 1 by linarith))
    simpa only [norm_one, mul_one, sub_sub_cancel, div_self (ne_of_gt hα)] using h
  apply ritt_renewal_perturbation _ _ hΨ hR _ hr hr1
  · rw [renewalScalar_quotient (ne_of_gt hα) hz0 hd0]
    exact shifted_reciprocal_sector hα hz0 hgeo
  · exact norm_renewalKernel_local_error Φ hΦ hzero hα hα1 hd z hz

end OracleTemplate.MarkovProduct
