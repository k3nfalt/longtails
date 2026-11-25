import LongTails.Proofs.SoftQuadraticDynamics

namespace LongTails.Proofs.BilinearLogisticDescent

open SoftQuadraticDynamics

noncomputable def loss (m : ℝ) := Real.log (1 + Real.exp (-m))

lemma loss_nonneg (m : ℝ) : 0 ≤ loss m :=
  Real.log_nonneg (by linarith [Real.exp_pos (-m)])

lemma neg_margin_le_loss (m : ℝ) : -m ≤ loss m := by
  rw [← Real.log_exp (-m)]
  exact Real.log_le_log (Real.exp_pos _) (by linarith)

private lemma weight_eq (m : ℝ) : weight m = Real.exp (-m) / (1 + Real.exp (-m)) := by
  unfold weight
  rw [Real.exp_neg]
  field_simp
  ring

lemma loss_increment {m d : ℝ} (hd : |d| ≤ 1) :
    loss (m + d) ≤ loss m - weight m * d + d ^ 2 := by
  have h1 : 0 < 1 + Real.exp (-m) := by positivity
  have h2 : 0 < 1 + Real.exp (-(m + d)) := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos h2 h1)
  rw [Real.log_div h2.ne' h1.ne'] at hlog
  have he := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
    (x := -d) (by simpa using hd))).2
  have hid : (1 + Real.exp (-(m + d))) / (1 + Real.exp (-m)) - 1 =
      weight m * (Real.exp (-d) - 1) := by
    rw [neg_add, Real.exp_add, weight_eq]
    field_simp
    ring
  rw [hid] at hlog
  unfold loss
  nlinarith [mul_le_mul_of_nonneg_left he (weight_pos m).le,
    mul_le_mul_of_nonneg_right (weight_le_one m) (sq_nonneg d)]

lemma loss_quadratic_step {m l q η M D : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hDM : D ≤ M)
    (hl : l ^ 2 ≤ M * D) (hq : |q| ≤ D / 2)
    (hsmall : η * (1 + M) ≤ 1 / 8) :
    loss (m + (η * l + η ^ 2 * q)) ≤
      loss m - η * weight m * l + η / 2 * D := by
  have habsl : |l| ≤ M := by
    have := mul_le_mul_of_nonneg_left hDM hM
    nlinarith [sq_abs l, abs_nonneg l, sq_nonneg (|l| - M)]
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp hq
  have habs : |η * l + η ^ 2 * q| ≤ 1 := by
    calc
      _ ≤ |η * l| + |η ^ 2 * q| := abs_add_le _ _
      _ = η * |l| + η ^ 2 * |q| := by rw [abs_mul, abs_mul, abs_of_nonneg hη,
        abs_of_nonneg (sq_nonneg η)]
      _ ≤ η * M + η * M := by
        apply add_le_add (mul_le_mul_of_nonneg_left habsl hη)
        exact mul_le_mul (by nlinarith [mul_nonneg hη (sub_nonneg.mpr hη')])
          (by linarith) (abs_nonneg _) hη
      _ ≤ 1 := by linarith
  have hsquare : q ^ 2 ≤ M * D := by
    have he := mul_self_le_mul_self (abs_nonneg q) (hq.trans (by linarith : D / 2 ≤ D))
    nlinarith [sq_abs q, mul_le_mul_of_nonneg_right hDM hD]
  have hqd : (η * q) ^ 2 ≤ M * D := by
    rw [mul_pow]
    have hsq : η ^ 2 ≤ 1 := by nlinarith [mul_nonneg hη (sub_nonneg.mpr hη')]
    exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg q)).trans
      (by simpa using hsquare)
  have hd : (η * l + η ^ 2 * q) ^ 2 ≤ η ^ 2 * (4 * M * D) := by
    have h := mul_le_mul_of_nonneg_left (show (l + η * q) ^ 2 ≤ 4 * M * D by
      nlinarith [sq_nonneg (l - η * q)]) (sq_nonneg η)
    nlinarith only [h]
  have hweight : -(weight m * q) ≤ D / 2 := by
    calc
      _ ≤ |weight m * q| := neg_le_abs _
      _ = weight m * |q| := by rw [abs_mul, abs_of_nonneg (weight_pos _).le]
      _ ≤ 1 * |q| := mul_le_mul_of_nonneg_right (weight_le_one _) (abs_nonneg _)
      _ ≤ _ := by simpa using hq
  have hcost : η * (1 / 2 + 4 * M) ≤ 1 / 2 := by linarith
  nlinarith only [loss_increment (m := m) habs, hd,
    mul_le_mul_of_nonneg_left hweight (sq_nonneg η),
    mul_le_mul_of_nonneg_right hcost (mul_nonneg hη hD)]

open scoped RealInnerProductSpace

section Batch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

noncomputable def direction (m : Fin n → ℝ) (g : Fin n → E) : E :=
  (n : ℝ)⁻¹ • ∑ i, weight (m i) • g i

private lemma direction_pairing (m : Fin n → ℝ) (g : Fin n → E) (w : E) :
    ⟪direction m g, w⟫ = (n : ℝ)⁻¹ * ∑ i, weight (m i) * ⟪g i, w⟫ := by
  simp [direction, sum_inner, real_inner_smul_left]

lemma energy_step (hn : 0 < n) (m : Fin n → ℝ) (g : Fin n → E) (w : E)
    (hEuler : ∀ i, ⟪g i, w⟫ = 2 * m i) {η : ℝ} (hη : 0 ≤ η) :
    ‖w + η • direction m g‖ ^ 2 ≤ ‖w‖ ^ 2 + 4 * η + η ^ 2 * ‖direction m g‖ ^ 2 := by
  have hmass : ∑ i, weight (m i) * ⟪g i, w⟫ ≤ (n : ℝ) * 2 := by
    calc
      _ ≤ ∑ _i : Fin n, (2 : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [hEuler]; linarith [weighted_score_le_one (m i)]
      _ = _ := by simp
  have hpair : ⟪direction m g, w⟫ ≤ 2 := by
    rw [direction_pairing, ← div_eq_inv_mul]
    exact (div_le_iff₀ (by exact_mod_cast hn)).2 (by linarith)
  rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm (direction m g) w, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  linarith [mul_le_mul_of_nonneg_left hpair hη]

lemma batch_descent (hn : 0 < n) (m q : Fin n → ℝ) (g : Fin n → E) {η R : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1) (hg : ∀ i, ‖g i‖ ≤ R)
    (hq : ∀ i, |q i| ≤ ‖direction m g‖ ^ 2 / 2)
    (hsmall : η * (1 + R ^ 2) ≤ 1 / 8) :
    (∑ i, loss (m i + (η * ⟪g i, direction m g⟫ + η ^ 2 * q i))) / n ≤
      (∑ i, loss (m i)) / n - η / 2 * ‖direction m g‖ ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let d := direction m g
  have hsize : ‖d‖ ≤ R := by
    change ‖(n : ℝ)⁻¹ • ∑ i, weight (m i) • g i‖ ≤ R
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn'.le),
      ← div_eq_inv_mul, div_le_iff₀ hn']
    calc
      _ ≤ ∑ i, ‖weight (m i) • g i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, R := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_pos _).le]
        simpa using mul_le_mul (weight_le_one _) (hg i) (norm_nonneg _) zero_le_one
      _ = _ := by simp [mul_comm]
  have hpoint (i : Fin n) : loss (m i + (η * ⟪g i, d⟫ + η ^ 2 * q i)) ≤
      loss (m i) - η * (weight (m i) * ⟪g i, d⟫) + η / 2 * ‖d‖ ^ 2 := by
    rw [← mul_assoc]
    apply loss_quadratic_step hη hη' (M := R ^ 2) (sq_nonneg _) (sq_nonneg _)
      (pow_le_pow_left₀ (norm_nonneg d) hsize 2) _ (hq i) hsmall
    have habs := (abs_real_inner_le_norm (g i) d).trans
      (mul_le_mul_of_nonneg_right (hg i) (norm_nonneg _))
    simpa [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hpair := direction_pairing m g d
  change ⟪d, d⟫ = _ at hpair
  rw [real_inner_self_eq_norm_sq, ← div_eq_inv_mul, eq_div_iff hn'.ne'] at hpair
  rw [div_le_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
  change (∑ i, loss (m i + (η * ⟪g i, d⟫ + η ^ 2 * q i))) ≤ _
  rw [← hpair] at hsum
  linarith

end Batch

end LongTails.Proofs.BilinearLogisticDescent
