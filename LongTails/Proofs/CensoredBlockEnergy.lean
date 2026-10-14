import LongTails.Proofs.GeometricBlockSector
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators

namespace OracleTemplate.MarkovProduct

noncomputable def censoredMean {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℝ) (n : ℕ) (f : ℕ → V) : V :=
  (1 - q) • (∑ k ∈ Finset.range n, q ^ k • f (k + 1)) + q ^ n • f n

lemma censoredMean_telescope {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℝ) (n : ℕ) (f : ℕ → V) :
    censoredMean q n f = f 0 + ∑ k ∈ Finset.range n, q ^ k • (f (k + 1) - f k) :=
  censored_geometric_telescope q f n

@[simp] lemma censoredMean_const {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℝ) (n : ℕ) (c : V) : censoredMean q n (fun _ => c) = c := by
  simp [censoredMean_telescope]

lemma censoredMean_add {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℝ) (n : ℕ) (f g : ℕ → V) :
    censoredMean q n (fun k => f k + g k) = censoredMean q n f + censoredMean q n g := by
  simp only [censoredMean, smul_add, Finset.sum_add_distrib]
  abel

lemma censoredMean_sub {V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℝ) (n : ℕ) (f g : ℕ → V) :
    censoredMean q n (fun k => f k - g k) = censoredMean q n f - censoredMean q n g := by
  simp only [censoredMean, smul_sub, Finset.sum_sub_distrib]
  abel

lemma censoredMean_mul (q c : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    censoredMean q n (fun k => c * f k) = c * censoredMean q n f := by
  simp only [censoredMean, smul_eq_mul]
  rw [show (∑ k ∈ Finset.range n, q ^ k * (c * f (k + 1))) =
      c * ∑ k ∈ Finset.range n, q ^ k * f (k + 1) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring]
  ring

lemma censoredMean_mono {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ)
    {f g : ℕ → ℝ} (hfg : ∀ k, f k ≤ g k) : censoredMean q n f ≤ censoredMean q n g := by
  unfold censoredMean
  simp only [smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk =>
    mul_le_mul_of_nonneg_left (hfg (k + 1)) (pow_nonneg hq _)) (sub_nonneg.mpr hq1))
    (mul_le_mul_of_nonneg_left (hfg n) (pow_nonneg hq _))

lemma censoredMean_nonneg {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ)
    {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) : 0 ≤ censoredMean q n f := by
  simpa using censoredMean_mono hq hq1 n hf

lemma re_censoredMean (q : ℝ) (n : ℕ) (f : ℕ → ℂ) :
    (censoredMean q n f).re = censoredMean q n (fun k => (f k).re) := by
  change Complex.reCLM (censoredMean q n f) = _
  simp only [censoredMean, map_add, map_smul, map_sum, Complex.reCLM_apply]

lemma im_censoredMean (q : ℝ) (n : ℕ) (f : ℕ → ℂ) :
    (censoredMean q n f).im = censoredMean q n (fun k => (f k).im) := by
  change Complex.imCLM (censoredMean q n f) = _
  simp only [censoredMean, map_add, map_smul, map_sum, Complex.imCLM_apply]

lemma censoredMean_complex_mul (q : ℝ) (z : ℂ) (n : ℕ) (f : ℕ → ℂ) :
    censoredMean q n (fun k => z * f k) = z * censoredMean q n f := by
  simp only [censoredMean, mul_add, Finset.mul_sum, mul_smul_comm]

section Limits

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

noncomputable def geometricMean (q : ℝ) (f : ℕ → V) : V :=
  (1 - q) • ∑' k : ℕ, q ^ k • f (k + 1)

lemma summable_geometric_vector {q C : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (f : ℕ → V) (hf : ∀ k, ‖f k‖ ≤ C) : Summable (fun k : ℕ => q ^ k • f (k + 1)) := by
  have hs : Summable (fun k : ℕ => q ^ k * C) :=
    (summable_geometric_of_lt_one hq hq1).mul_right C
  apply hs.of_norm_bounded
  intro k
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq _)]
  exact mul_le_mul_of_nonneg_left (hf (k + 1)) (pow_nonneg hq k)

lemma tendsto_censoredMean {q C : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (f : ℕ → V) (hf : ∀ k, ‖f k‖ ≤ C) :
    Filter.Tendsto (fun n : ℕ => censoredMean q n f) Filter.atTop (nhds (geometricMean q f)) := by
  have htail : Filter.Tendsto (fun n : ℕ => q ^ n • f n) Filter.atTop (nhds (0 : V)) := by
    apply squeeze_zero_norm (a := fun n : ℕ => q ^ n * C)
    · intro n
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq _)]
      exact mul_le_mul_of_nonneg_left (hf n) (pow_nonneg hq n)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const C
  have hsum := (summable_geometric_vector hq hq1 f hf).hasSum.tendsto_sum_nat
  simpa only [censoredMean, geometricMean, add_zero] using
    (hsum.const_smul (1 - q)).add htail

end Limits

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma censored_displacement_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (x : ℕ → E) (n : ℕ) :
    (1 - r ^ 2) * censoredMean (r ^ 2) n (fun k => ‖x 0 - x k‖ ^ 2) ≤
      5 * ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2 := by
  rw [censoredMean_telescope]
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add, smul_eq_mul, ← pow_mul]
  exact geometric_displacement_variation r hr hr1 x n

omit [InnerProductSpace ℂ E] in
lemma censored_loss_identity (q : ℝ) (x : ℕ → E) (n : ℕ) :
    ‖x 0‖ ^ 2 - censoredMean q n (fun k => ‖x k‖ ^ 2) =
      ∑ k ∈ Finset.range n, q ^ k * (‖x k‖ ^ 2 - ‖x (k + 1)‖ ^ 2) := by
  rw [censoredMean_telescope]
  simp only [smul_eq_mul]
  rw [show ‖x 0‖ ^ 2 - (‖x 0‖ ^ 2 + ∑ k ∈ Finset.range n,
      q ^ k * (‖x (k + 1)‖ ^ 2 - ‖x k‖ ^ 2)) =
      -(∑ k ∈ Finset.range n, q ^ k * (‖x (k + 1)‖ ^ 2 - ‖x k‖ ^ 2)) by ring]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

omit [InnerProductSpace ℂ E] in
lemma censored_increment_bound {q β : ℝ} (hq : 0 ≤ q) (x : ℕ → E)
    (hstep : ∀ k, ‖x (k + 1) - x k‖ ^ 2 ≤ β * (‖x k‖ ^ 2 - ‖x (k + 1)‖ ^ 2))
    (n : ℕ) :
    (∑ k ∈ Finset.range n, q ^ k * ‖x (k + 1) - x k‖ ^ 2) ≤
      β * (‖x 0‖ ^ 2 - censoredMean q n (fun k => ‖x k‖ ^ 2)) := by
  rw [censored_loss_identity, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  convert mul_le_mul_of_nonneg_left (hstep k) (pow_nonneg hq k) using 1
  ring

lemma censored_cross_re (q : ℝ) (x : ℕ → E) (n : ℕ) :
    (censoredMean q n (fun k => inner ℂ (x k) (x 0 - x k))).re =
      (‖x 0‖ ^ 2 - censoredMean q n (fun k => ‖x k‖ ^ 2) -
        censoredMean q n (fun k => ‖x 0 - x k‖ ^ 2)) / 2 := by
  have hp (k : ℕ) : 2 * (inner ℂ (x k) (x 0 - x k)).re =
      ‖x 0‖ ^ 2 - ‖x k‖ ^ 2 - ‖x 0 - x k‖ ^ 2 := by
    have h := norm_add_sq (𝕜 := ℂ) (x k) (x 0 - x k)
    rw [show x k + (x 0 - x k) = x 0 by abel] at h
    change ‖x 0‖ ^ 2 = ‖x k‖ ^ 2 +
      2 * (inner ℂ (x k) (x 0 - x k)).re + ‖x 0 - x k‖ ^ 2 at h
    linarith
  have h := congrArg (censoredMean q n) (funext hp)
  rw [censoredMean_mul, censoredMean_sub, censoredMean_sub, censoredMean_const] at h
  rw [re_censoredMean]
  linarith

lemma censored_cross_im (q : ℝ) (x : ℕ → E)
    (hreal : ∀ k, (inner ℂ (x k) (x k - x (k + 1))).im = 0) (n : ℕ) :
    (censoredMean q n (fun k => inner ℂ (x k) (x 0 - x k))).im =
      ∑ k ∈ Finset.range n, q ^ k *
        (inner ℂ (x 0 - x k) (x k - x (k + 1))).im := by
  have hc (k : ℕ) : (inner ℂ (x k) (x 0 - x k)).im =
      (inner ℂ (x 0) (x 0 - x k)).im := by
    have hd := inner_self_im (𝕜 := ℂ) (x 0 - x k)
    change (inner ℂ (x 0 - x k) (x 0 - x k)).im = 0 at hd
    rw [inner_sub_left, Complex.sub_im] at hd
    linarith
  rw [im_censoredMean]
  simp_rw [hc]
  rw [censoredMean_telescope]
  simp only [sub_self, inner_zero_right, Complex.zero_im, zero_add, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [imaginary_area_telescope x hreal (k + 1), imaginary_area_telescope x hreal k,
    Finset.sum_range_succ]
  ring

lemma censored_cross_im_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (x : ℕ → E) (hreal : ∀ k, (inner ℂ (x k) (x k - x (k + 1))).im = 0) (n : ℕ) :
    (1 - r ^ 2) * |(censoredMean (r ^ 2) n (fun k => inner ℂ (x k) (x 0 - x k))).im| ≤
      2 * ∑ k ∈ Finset.range n, r ^ (2 * k) * ‖x (k + 1) - x k‖ ^ 2 := by
  rw [censored_cross_im _ x hreal]
  simp only [← pow_mul]
  exact geometric_projection_area_bound Complex.im Complex.abs_im_le_norm r hr hr1 x n

lemma censored_block_gap {r β : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hsmall : 8 * β ≤ 1 - r ^ 2) (x : ℕ → E)
    (hstep : ∀ k, ‖x (k + 1) - x k‖ ^ 2 ≤ β * (‖x k‖ ^ 2 - ‖x (k + 1)‖ ^ 2))
    (hcontract : ∀ k, ‖x (k + 1)‖ ≤ ‖x k‖) (n : ℕ) :
    censoredMean (r ^ 2) n (fun k => ‖x 0 - x k‖ ^ 2) ≤
      ‖x 0‖ ^ 2 - censoredMean (r ^ 2) n (fun k => ‖x k‖ ^ 2) := by
  let D := ‖x 0‖ ^ 2 - censoredMean (r ^ 2) n (fun k => ‖x k‖ ^ 2)
  let J := censoredMean (r ^ 2) n (fun k => ‖x 0 - x k‖ ^ 2)
  have hD : 0 ≤ D := by
    dsimp [D]
    rw [censored_loss_identity]
    apply Finset.sum_nonneg
    intro k hk
    have h := hcontract k
    exact mul_nonneg (pow_nonneg (sq_nonneg r) k) (by nlinarith [norm_nonneg (x k), norm_nonneg (x (k + 1))])
  have ha : 0 < 1 - r ^ 2 := by nlinarith
  have hJ := censored_displacement_bound hr hr1.le x n
  have hE := censored_increment_bound (sq_nonneg r) x hstep n
  simp only [← pow_mul] at hE
  change (1 - r ^ 2) * J ≤ _ at hJ
  change _ ≤ β * D at hE
  have hscale := mul_le_mul_of_nonneg_right (show 5 * β ≤ 1 - r ^ 2 by linarith) hD
  change J ≤ D
  nlinarith

lemma censored_perturbation_identity (q : ℝ) (x : ℕ → E) (n : ℕ) (z : ℂ) :
    censoredMean q n (fun k => ‖x k + z • (x 0 - x k)‖ ^ 2) =
      censoredMean q n (fun k => ‖x k‖ ^ 2) +
      2 * (z * censoredMean q n (fun k => inner ℂ (x k) (x 0 - x k))).re +
      ‖z‖ ^ 2 * censoredMean q n (fun k => ‖x 0 - x k‖ ^ 2) := by
  have hp (k : ℕ) : ‖x k + z • (x 0 - x k)‖ ^ 2 =
      ‖x k‖ ^ 2 + 2 * (z * inner ℂ (x k) (x 0 - x k)).re +
        ‖z‖ ^ 2 * ‖x 0 - x k‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, mul_pow]
    rfl
  simp_rw [hp]
  rw [censoredMean_add, censoredMean_add, censoredMean_mul, censoredMean_mul,
    ← re_censoredMean, censoredMean_complex_mul]

lemma censored_block_disk {r β : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hsmall : 8 * β ≤ 1 - r ^ 2) (x : ℕ → E)
    (hstep : ∀ k, ‖x (k + 1) - x k‖ ^ 2 ≤ β * (‖x k‖ ^ 2 - ‖x (k + 1)‖ ^ 2))
    (hcontract : ∀ k, ‖x (k + 1)‖ ≤ ‖x k‖)
    (hreal : ∀ k, (inner ℂ (x k) (x k - x (k + 1))).im = 0)
    (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    censoredMean (r ^ 2) n (fun k => ‖x k + z • (x 0 - x k)‖ ^ 2) ≤ ‖x 0‖ ^ 2 := by
  let D := ‖x 0‖ ^ 2 - censoredMean (r ^ 2) n (fun k => ‖x k‖ ^ 2)
  let J := censoredMean (r ^ 2) n (fun k => ‖x 0 - x k‖ ^ 2)
  let c := censoredMean (r ^ 2) n (fun k => inner ℂ (x k) (x 0 - x k))
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have ha : 0 < 1 - r ^ 2 := by nlinarith
  have hJ : 0 ≤ J := censoredMean_nonneg (sq_nonneg r) hr2 n (fun k => sq_nonneg _)
  have hJD : J ≤ D := censored_block_gap hr hr1 hsmall x hstep hcontract n
  have hD : 0 ≤ D := hJ.trans hJD
  have hIm : |c.im| ≤ D / 4 := by
    have harea := censored_cross_im_bound hr hr1.le x hreal n
    have hinc := censored_increment_bound (sq_nonneg r) x hstep n
    simp only [← pow_mul] at hinc
    change (1 - r ^ 2) * |c.im| ≤ _ at harea
    change _ ≤ β * D at hinc
    have hm := mul_le_mul_of_nonneg_right hsmall hD
    nlinarith
  have hscalar := disk_scalar_bound hJ hJD c z (censored_cross_re (r ^ 2) x n) hIm hz
  rw [censored_perturbation_identity]
  change censoredMean (r ^ 2) n (fun k => ‖x k‖ ^ 2) + 2 * (z * c).re + ‖z‖ ^ 2 * J ≤ _
  dsimp [D] at hscalar
  linarith

end OracleTemplate.MarkovProduct
