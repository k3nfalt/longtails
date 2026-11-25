import LongTails.Proofs.CyclicLogisticDynamics

open scoped RealInnerProductSpace
open LongTails.Proofs.CyclicLogisticGroups
open LongTails.Proofs.CyclicLogisticDynamics
open LongTails.Proofs.BilinearLogisticDescent
open LongTails.Proofs.SoftQuadraticDynamics (weight weight_pos weight_le_one weight_ge_half)

namespace LongTails.Proofs.CyclicLogisticSignal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

lemma mean_norm (hn : 0 < n) (m : Fin n → ℝ) (r : Fin n → E) {μ : ℝ}
    (hr : ∀ i, ‖r i‖ ≤ μ) : ‖mean m r‖ ≤ μ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [mean, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn'.le),
    ← div_eq_inv_mul, div_le_iff₀ hn']
  calc
    _ ≤ ∑ i, ‖weight (m i) • r i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, μ := Finset.sum_le_sum fun i _ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_pos _).le]
      simpa using mul_le_mul (weight_le_one _) (hr i) (norm_nonneg _) zero_le_one
    _ = _ := by simp [mul_comm]

lemma risk_nonneg (z r : Fin n → E) (s : Point E) : 0 ≤ risk z r s :=
  div_nonneg (Finset.sum_nonneg fun _ _ => loss_nonneg _) (Nat.cast_nonneg _)

lemma nuisance_bound (z r : Fin n → E) (s : Point E) {μ ρ : ℝ} (hμ : 0 ≤ μ)
    (hr : ∀ i, ‖r i‖ ≤ μ) (hρ : 0 < ρ)
    (hh : ∃ i, ⟪z i, s.fst.fst • s.fst.snd⟫ ≤ -ρ * ‖s.fst.fst • s.fst.snd‖)
    (hF : risk z r s ≤ 1) (hn : 0 < n) (hb : |imbalance s.fst| ≤ 1) :
    ‖s.fst‖ ^ 2 ≤ 1 + (2 * n + μ * ‖s‖ ^ 2) / ρ := by
  obtain ⟨i, hi⟩ := hh
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum := (div_le_iff₀ hn').mp hF
  have hl := Finset.single_le_sum (f := fun j => loss (scores z r s j))
    (fun j _ => loss_nonneg _) (Finset.mem_univ i)
  have hm : -(scores z r s i) ≤ n := by linarith [neg_margin_le_loss (scores z r s i)]
  have hw : value (r i) s.snd ≤ μ * ‖s.snd‖ ^ 2 / 2 := by
    have hinner := (abs_real_inner_le_norm (r i) s.snd.snd).trans
      (mul_le_mul_of_nonneg_right (hr i) (norm_nonneg _))
    have ham := mul_le_mul_of_nonneg_left hinner (abs_nonneg s.snd.fst)
    have hb' := le_abs_self (value (r i) s.snd)
    rw [value, abs_mul] at hb'
    rw [group_norm, value]
    have hh : 2 * |s.snd.fst| * ‖s.snd.snd‖ ≤ s.snd.fst ^ 2 + ‖s.snd.snd‖ ^ 2 := by
      nlinarith [sq_nonneg (|s.snd.fst| - ‖s.snd.snd‖), sq_abs s.snd.fst]
    linarith [mul_le_mul_of_nonneg_left hh hμ]
  rw [real_inner_smul_right] at hi
  change - (value (z i) s.fst + value (r i) s.snd) ≤ _ at hm
  change value (z i) s.fst ≤ _ at hi
  have hprod : 2 * ‖s.fst.fst • s.fst.snd‖ ≤ (2 * n + μ * ‖s‖ ^ 2) / ρ := by
    apply (le_div_iff₀ hρ).mpr
    rw [WithLp.prod_norm_sq_eq_of_L2]
    linarith [mul_nonneg hμ (sq_nonneg ‖s.fst‖)]
  linarith [group_energy_from_product s.fst]

lemma filter_positive (z r : Fin n → E) (s : Point E) {μ η : ℝ} (hn : 0 < n)
    (hr : ∀ i, ‖r i‖ ≤ μ) (hμ : μ ≤ 1) (hη : 0 ≤ η) (hη' : η ≤ 1)
    (hpos : 0 < s.snd.fst) (hb : 0 < imbalance s.snd) :
    0 < (update z r η s).snd.fst := by
  let R := mean (scores z r s) r
  have ha : ‖s.snd.snd‖ < s.snd.fst := by
    unfold imbalance at hb
    nlinarith [sq_nonneg (‖s.snd.snd‖ - s.snd.fst), norm_nonneg s.snd.snd]
  have hR : ‖R‖ ≤ 1 := (mean_norm hn _ _ hr).trans hμ
  have hlt : |⟪R, s.snd.snd⟫| < s.snd.fst := (abs_real_inner_le_norm ..).trans_lt
    ((show ‖R‖ * ‖s.snd.snd‖ ≤ ‖s.snd.snd‖ by
      simpa using mul_le_mul_of_nonneg_right hR (norm_nonneg s.snd.snd)).trans_lt ha)
  change 0 < s.snd.fst + η * ⟪R, s.snd.snd⟫
  have hle := mul_le_mul_of_nonneg_right hη' (abs_nonneg ⟪R, s.snd.snd⟫)
  rw [one_mul] at hle
  nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs ⟪R, s.snd.snd⟫) hη,
    mul_nonneg hη (sub_nonneg.mpr hη'), mul_nonneg (sub_nonneg.mpr hη') (abs_nonneg ⟪R, s.snd.snd⟫)]

lemma signal_growth (z r : Fin n → E) (s : Point E) (u : E) {γ η : ℝ}
    (hn : 0 < n) (hu : ‖u‖ = 1) (hγ : 0 < γ) (hη : 0 ≤ η)
    (hsep : ∀ i, γ ≤ ⟪r i, u⟫) (hfail : ∃ i, scores z r s i ≤ 0)
    (hpos : 0 < s.snd.fst) (hb : 1 / 4 ≤ imbalance s.snd) :
    (1 + η * γ / (8 * n)) * (1 + ⟪s.snd.snd, u⟫) ≤
    1 + ⟪(update z r η s).snd.snd, u⟫ := by
  obtain ⟨i, hi⟩ := hfail
  let m := scores z r s
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm := mul_le_mul (weight_ge_half hi) (hsep i) hγ.le (weight_pos _).le
  have hsum := Finset.single_le_sum (f := fun j => weight (m j) * ⟪r j, u⟫)
    (fun j _ => mul_nonneg (weight_pos _).le (hγ.le.trans (hsep j))) (Finset.mem_univ i)
  have hmean : γ / (2 * n) ≤ ⟪mean m r, u⟫ := by
    rw [mean, real_inner_smul_left, sum_inner, ← div_eq_inv_mul]
    simp only [real_inner_smul_left]
    rw [div_le_div_iff₀ (by positivity) hn']
    change 1 / 2 * γ ≤ weight (m i) * ⟪r i, u⟫ at hterm
    nlinarith [mul_le_mul_of_nonneg_right (hterm.trans hsum) hn'.le]
  have hy := abs_real_inner_le_norm s.snd.snd u
  rw [hu, mul_one] at hy
  unfold imbalance at hb
  have ht : ‖s.snd.snd‖ ≤ s.snd.fst := by
    nlinarith [norm_nonneg s.snd.snd, sq_nonneg (‖s.snd.snd‖ - s.snd.fst)]
  have hhalf : 1 / 2 ≤ s.snd.fst := by nlinarith [sq_nonneg ‖s.snd.snd‖]
  have hcoeff : 1 + ⟪s.snd.snd, u⟫ ≤ 4 * s.snd.fst := by
    linarith [le_abs_self ⟪s.snd.snd, u⟫]
  change _ ≤ 1 + ⟪s.snd.snd + η • (s.snd.fst • mean m r), u⟫
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h1 := mul_le_mul_of_nonneg_left hmean hpos.le
  have h2 := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ γ / (8 * n) by positivity)
  have hid : γ / (2 * n) = 4 * (γ / (8 * n)) := by ring
  rw [hid] at h1
  have h3 : γ / (8 * n) * (1 + ⟪s.snd.snd, u⟫) ≤
      s.snd.fst * ⟪mean m r, u⟫ := by linarith
  rw [mul_div_assoc]
  linarith [mul_le_mul_of_nonneg_left h3 hη]

end LongTails.Proofs.CyclicLogisticSignal
