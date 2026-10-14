import LongTails.Proofs.TemporalNonlinearResponse

namespace OracleTemplate.TemporalDiscrepancy

open LongTails.Setups.QuadraticTemporalDiscrepancy

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompleteSpace E] in
lemma split_forced_rec (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (v noise : ℕ → V) (e r : ℕ → E)
    (hv : ∀ k, v (k + 1) = T (v k) + B (e k + r k))
    (hn : ∀ k, noise (k + 1) = T (noise k) + B (e k)) (k : ℕ) :
    v (k + 1) - noise (k + 1) = T (v k - noise k) + B (r k) := by
  rw [hv, hn, map_add, map_sub]
  abel

omit [CompleteSpace E] in
lemma projection_split_bound (P : V →L[ℝ] E) (p : Seminorm ℝ V)
    {χ B : ℝ} (hχ : 0 < χ) (hP : ∀ v, χ * ‖P v‖ ≤ p v)
    (v noise : V) (hn : ‖P noise‖ ≤ B) :
    ‖P v‖ ≤ p (v - noise) / χ + B := by
  have hh : ‖P v‖ ≤ ‖P (v - noise)‖ + ‖P noise‖ := by
    rw [map_sub]
    have hh := norm_add_le (P v - P noise) (P noise)
    simpa only [sub_add_cancel] using hh
  have hp : ‖P (v - noise)‖ ≤ p (v - noise) / χ := by
    apply (le_div_iff₀ hχ).mpr
    simpa only [mul_comm] using hP (v - noise)
  exact hh.trans (add_le_add hp hn)

omit [CompleteSpace E] in
lemma nonlinear_split_envelope (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (Q : V →L[ℝ] E) (p : Seminorm ℝ V)
    (v noise : ℕ → V) (e r : ℕ → E)
    {ρ β χ D M : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hβ : 0 ≤ β)
    (hχ : 0 < χ) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hT : ∀ v, p (T v) ≤ ρ * p v) (hB : ∀ e, p (B e) ≤ β * ‖e‖)
    (hQ : ∀ v, χ * ‖Q v‖ ≤ p v)
    (hv : ∀ k, v (k + 1) = T (v k) + B (e k + r k))
    (hn : ∀ k, noise (k + 1) = T (noise k) + B (e k)) (hn0 : noise 0 = 0)
    (hnoise : ∀ k, ‖Q (noise k)‖ ≤ D)
    (hr : ∀ k, ‖r k‖ ≤ M * ‖Q (v k)‖ ^ 2)
    (hsmall : (β * M / χ) * (p (v 0) / χ + 2 * D) ≤ (1 - ρ) / 2) (n : ℕ) :
    p (v n - noise n) / χ + D ≤
      (p (v 0) / χ) * ((1 + ρ) / 2) ^ n + 2 * D := by
  let z := fun k => p (v k - noise k) / χ + D
  have hz (k : ℕ) : 0 ≤ z k := add_nonneg
    (div_nonneg (apply_nonneg p _) hχ.le) hD
  have hq (k : ℕ) : ‖Q (v k)‖ ≤ z k :=
    projection_split_bound Q p hχ hQ (v k) (noise k) (hnoise k)
  have herr (k : ℕ) : ‖r k‖ ≤ M * z k ^ 2 := (hr k).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hq k) 2) hM)
  have hrec (k : ℕ) : z k ≤ (p (v 0) / χ) * ρ ^ k + D +
      (β * M / χ) * causalSum ρ (fun i => z i ^ 2) k := by
    have hh := seminorm_forcing_bound T B p hρ hT hB
      (fun i => v i - noise i) r (split_forced_rec T B v noise e r hv hn) k
    simp only [hn0, sub_zero] at hh
    have hc := causalSum_mono hρ herr k
    rw [causalSum_mul] at hc
    have hh' := hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc hβ))
    have hd := add_le_add (div_le_div_of_nonneg_right hh' hχ.le) (le_refl D)
    change z k ≤ _
    convert hd using 1; ring
  exact nonlinear_convolution_bootstrap z hρ hρ1
    (div_nonneg (apply_nonneg p _) hχ.le) hD (by positivity) hz hrec hsmall n

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma quadratic_remainder_envelope {q A D M : ℝ}
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hq1 : q ≤ 1) (x r : E) (n : ℕ)
    (hx : ‖x‖ ≤ A * q ^ n + 2 * D) (hr : ‖r‖ ≤ M * ‖x‖ ^ 2) :
    ‖r‖ ≤ 2 * M * A ^ 2 * q ^ n + 8 * M * D ^ 2 := by
  have hp0 : 0 ≤ q ^ n := pow_nonneg hq n
  have hp1 : q ^ n ≤ 1 := pow_le_one₀ hq hq1
  have hp2 : (q ^ n) ^ 2 ≤ q ^ n := by nlinarith
  have hs := pow_le_pow_left₀ (norm_nonneg x) hx 2
  have ha := mul_le_mul_of_nonneg_left hp2 (sq_nonneg A)
  have ht : ‖x‖ ^ 2 ≤ 2 * A ^ 2 * q ^ n + 8 * D ^ 2 := by
    nlinarith [sq_nonneg (A * q ^ n - 2 * D)]
  have hm := mul_le_mul_of_nonneg_left ht hM
  nlinarith

omit [CompleteSpace E] in
lemma remainder_energy_envelope (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (Q : V →L[ℝ] E) (p : Seminorm ℝ V) (v noise : ℕ → V) (e r : ℕ → E)
    {ρ q β A D M : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hρq : ρ < q) (hq1 : q ≤ 1)
    (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hT : ∀ v, p (T v) ≤ ρ * p v) (hB : ∀ e, p (B e) ≤ β * ‖e‖)
    (hv : ∀ k, v (k + 1) = T (v k) + B (e k + r k))
    (hn : ∀ k, noise (k + 1) = T (noise k) + B (e k)) (hn0 : noise 0 = 0)
    (hq : ∀ k, ‖Q (v k)‖ ≤ A * q ^ k + 2 * D)
    (hr : ∀ k, ‖r k‖ ≤ M * ‖Q (v k)‖ ^ 2) (n : ℕ) :
    p (v n - noise n) ≤ ρ ^ n * p (v 0) +
      (2 * β * M * A ^ 2) * q ^ n / (q - ρ) + (8 * β * M * D ^ 2) / (1 - ρ) := by
  have hstep (k : ℕ) : p (v (k + 1) - noise (k + 1)) ≤
      ρ * p (v k - noise k) + (2 * β * M * A ^ 2) * q ^ k + 8 * β * M * D ^ 2 := by
    rw [split_forced_rec T B v noise e r hv hn]
    have hh := (map_add_le_add p (T (v k - noise k)) (B (r k))).trans
      (add_le_add (hT (v k - noise k)) (hB (r k)))
    have hrem := quadratic_remainder_envelope hM (hρ.trans hρq.le) hq1
      (Q (v k)) (r k) k (hq k) (hr k)
    have hm := mul_le_mul_of_nonneg_left hrem hβ
    nlinarith
  have hh := scalar_forcing_envelope (fun k => p (v k - noise k)) hρ hρ1 hρq
    (show 0 ≤ 2 * β * M * A ^ 2 by positivity)
    (show 0 ≤ 8 * β * M * D ^ 2 by positivity) hstep n
  simpa only [hn0, sub_zero] using hh

lemma seminorm_tail_envelope (p : Seminorm ℝ V) (v : ℕ → V)
    {q C F : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (hv : ∀ k, p (v k) ≤ C * q ^ k + F) (start count : ℕ) (hc : 0 < count) :
    p (tailAverage v start count) ≤ C * q ^ start + F := by
  have hn : (0 : ℝ) < count := by exact_mod_cast hc
  have hs : (∑ k ∈ Finset.range count, p (v (start + k + 1))) ≤
      (count : ℝ) * (C * q ^ start + F) := by
    calc
      _ ≤ ∑ _k ∈ Finset.range count, (C * q ^ start + F) := by
        apply Finset.sum_le_sum
        intro k _
        exact (hv _).trans (add_le_add (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hq hq1 (by omega)) hC) le_rfl)
      _ = _ := by simp; ring
  rw [tailAverage, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  have hh := (seminorm_sum_range_le p (fun k => v (start + k + 1)) count).trans hs
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hn.le)).trans_eq
  field_simp

lemma tailAverage_split (v noise : ℕ → V) (start count : ℕ) :
    tailAverage v start count =
      tailAverage (fun k => v k - noise k) start count + tailAverage noise start count := by
  simp only [tailAverage, Finset.sum_sub_distrib, smul_sub]
  abel

omit [CompleteSpace E] in
lemma split_tail_bound (T : V →L[ℝ] V) (B : E →L[ℝ] V)
    (Q : V →L[ℝ] E) (p : Seminorm ℝ V)
    (v noise : ℕ → V) (e r : ℕ → E)
    {ρ β χ D S M : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hβ : 0 ≤ β)
    (hχ : 0 < χ) (hD : 0 ≤ D) (hS : 0 ≤ S) (hM : 0 ≤ M)
    (hT : ∀ v, p (T v) ≤ ρ * p v) (hB : ∀ e, p (B e) ≤ β * ‖e‖)
    (hQ : ∀ v, χ * ‖Q v‖ ≤ p v)
    (hv : ∀ k, v (k + 1) = T (v k) + B (e k + r k))
    (hn : ∀ k, noise (k + 1) = T (noise k) + B (e k)) (hn0 : noise 0 = 0)
    (hnoise : ∀ k, ‖Q (noise k)‖ ≤ D)
    (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ S)
    (hr : ∀ k, ‖r k‖ ≤ M * ‖Q (v k)‖ ^ 2)
    (hsmall : (β * M / χ) * (p (v 0) / χ + 2 * D) ≤ (1 - ρ) / 2)
    (start count : ℕ) (hc : 0 < count) :
    let q := (1 + ρ) / 2
    let a := p (v 0) / χ
    p (tailAverage v start count) ≤
      (p (v 0) + 2 * β * M * a ^ 2 / (q - ρ)) * q ^ start +
        8 * β * M * D ^ 2 / (1 - ρ) + 2 * β * S / ((1 - ρ) * count) := by
  let q := (1 + ρ) / 2
  let a := p (v 0) / χ
  have ha : 0 ≤ a := div_nonneg (apply_nonneg p _) hχ.le
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hρq : ρ < q := by dsimp [q]; linarith
  have henv (k : ℕ) : ‖Q (v k)‖ ≤ a * q ^ k + 2 * D :=
    (projection_split_bound Q p hχ hQ (v k) (noise k) (hnoise k)).trans
      (nonlinear_split_envelope T B Q p v noise e r hρ hρ1 hβ hχ hD hM hT hB hQ
        hv hn hn0 hnoise hr hsmall k)
  have hw (k : ℕ) : p (v k - noise k) ≤
      (p (v 0) + 2 * β * M * a ^ 2 / (q - ρ)) * q ^ k +
        8 * β * M * D ^ 2 / (1 - ρ) := by
    have hh := remainder_energy_envelope T B Q p v noise e r hρ hρ1 hρq hq1
      hβ hM hT hB hv hn hn0 henv hr k
    have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ hρq.le k)
      (apply_nonneg p (v 0))
    calc
      _ ≤ ρ ^ k * p (v 0) + 2 * β * M * a ^ 2 * q ^ k / (q - ρ) +
          8 * β * M * D ^ 2 / (1 - ρ) := hh
      _ ≤ q ^ k * p (v 0) + 2 * β * M * a ^ 2 * q ^ k / (q - ρ) +
          8 * β * M * D ^ 2 / (1 - ρ) := add_le_add (add_le_add hp le_rfl) le_rfl
      _ = _ := by ring
  have hwavg := seminorm_tail_envelope p (fun k => v k - noise k) hq hq1
    (show 0 ≤ p (v 0) + 2 * β * M * a ^ 2 / (q - ρ) by
      exact add_nonneg (apply_nonneg p _) (div_nonneg (by positivity) (sub_pos.mpr hρq).le))
    hw start count hc
  have hnavg := tail_average_bound T B p noise e hn hρ hρ1 hβ hS hT hB he start count hc
  simp only [hn0, map_zero, mul_zero, zero_add] at hnavg
  rw [tailAverage_split v noise start count]
  exact (map_add_le_add p _ _).trans (add_le_add hwavg hnavg)

end OracleTemplate.TemporalDiscrepancy
