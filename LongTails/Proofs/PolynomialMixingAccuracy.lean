import LongTails.Proofs.PolynomialMixingTraining

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.PolynomialMixingAccuracy

open LongTails.Setups.PolynomialMixingSubgradient LongTails.Algorithms.PolynomialMixingSelection
open LongTails.Proofs.PolynomialMixingTraining PolynomialMixingValidation PolynomialMixingScore

lemma sample_tuning {B ε p : ℝ} (hB : 0 < B) (he : 0 < ε) (hp : 1 < p) {n : ℕ}
    (hn : (32768 * B / ε) ^ (p / (p - 1)) ≤ n) :
    0 < n ∧ 32768 * B * (n : ℝ) ^ (1 / p) ≤ n * ε := by
  have hn' := lt_of_lt_of_le (Real.rpow_pos_of_pos (by positivity) _) hn
  have hp0 : 0 < p := by linarith
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hn
    (show 0 ≤ (p - 1) / p by positivity)
  rw [← Real.rpow_mul (by positivity), show p / (p - 1) * ((p - 1) / p) = 1 by field_simp [ne_of_gt (sub_pos.mpr hp)],
    Real.rpow_one] at hpow
  have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ he).mp hpow)
    (Real.rpow_nonneg hn'.le (1 / p))
  rw [mul_right_comm _ ε, ← Real.rpow_add hn', show (p - 1) / p + 1 / p = 1 by field_simp; ring,
    Real.rpow_one] at hh
  exact ⟨by exact_mod_cast hn', hh⟩

lemma root_scale {p B C : ℝ} {n : ℕ} (hp : 1 ≤ p) (hB : 0 ≤ B) (hC : 1 ≤ C) :
    C * n * B ^ p ≤ (C * (n : ℝ) ^ (1 / p) * B) ^ p := by
  have hC0 : 0 ≤ C := by linarith
  rw [Real.mul_rpow (mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hB,
    Real.mul_rpow hC0 (Real.rpow_nonneg (Nat.cast_nonneg n) _), ← Real.rpow_mul (Nat.cast_nonneg n),
    one_div_mul_cancel (by linarith : p ≠ 0), Real.rpow_one]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.self_le_rpow_of_one_le hC hp)
    (Nat.cast_nonneg n)) (Real.rpow_nonneg hB _)

lemma markov_power {W : Type*} [MeasurableSpace W] (P : Measure W) [IsProbabilityMeasure P]
    {F : W → ℝ} {p a c : ℝ} (hp : 0 < p) (ha : 0 < a) (hF : ∀ w, 0 ≤ F w)
    (hi : Integrable (fun w => F w ^ p) P) (hm : (∫ w, F w ^ p ∂P) ≤ a ^ p * c) :
    P.real {w | a < F w} ≤ c := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun w => Real.rpow_nonneg (hF w) p) hi (a ^ p)
  have hsub : {w | a < F w} ⊆ {w | a ^ p ≤ F w ^ p} := fun w hw =>
    Real.rpow_le_rpow ha.le (le_of_lt hw) hp.le
  apply (measureReal_mono hsub).trans
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos ha p)).mp (h.trans hm)

variable {q : Params} {f : Space q → ℝ} {g : Point q → ℝ → Space q} {π : Measure ℝ}
  [IsProbabilityMeasure π]

lemma iid_train (h : SubgradientOracle q f g π) (hc : ConvexOn ℝ (Domain q) f)
    (hR : 0 < q.R) (hG : 0 < q.G) (hp : 1 < q.p) (hp2 : q.p ≤ 2) (he : 0 < q.ε)
    (u : Point q) (n : ℕ) (hn : (32768 * (q.G * q.R) / q.ε) ^ (q.p / (q.p - 1)) ≤ n) :
    (Measure.infinitePi (fun _ : ℕ => π)).real {ξ | q.ε / 2 < f (average g n ξ).val - f u.val} ≤ 1 / 32 := by
  let P := Measure.infinitePi (fun _ : ℕ => π)
  obtain ⟨hn', ht⟩ := sample_tuning (mul_pos hG hR) he hp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'
  let r := (n : ℝ) ^ (1 / q.p)
  have hr : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast hn') (by positivity)
  let A := 64 * r * q.G
  let B := 1536 * r * (q.G * (2 * q.R))
  let energy := fun ξ => Real.sqrt (∑ i ∈ Finset.range n, ‖g (state g i ξ).x (ξ i)‖ ^ 2)
  have hE (ξ) : energy ξ ^ q.p ≤ energySum g n ξ :=
    sqrt_sum_power (by linarith) hp2 _ (fun _ => norm_nonneg _) n
  have hA := root_scale (n := n) hp.le hG.le (by norm_num : (1 : ℝ) ≤ 64)
  have hB := root_scale (n := n) hp.le (mul_nonneg hG.le (by positivity : 0 ≤ 2 * q.R))
    (by norm_num : (1 : ℝ) ≤ 1536)
  have hAp : 0 < A := by dsimp [A, r]; positivity
  have hBp : 0 < B := by dsimp [B, r]; positivity
  have hne (ξ) : 0 ≤ energySum g n ξ := Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨hi, hm⟩ := energy_moment h n
  have hEA : P.real {ξ | A < energy ξ} ≤ 1 / 64 := by
    have hh := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hne) hi (A ^ q.p)
    apply (measureReal_mono (show {ξ | A < energy ξ} ⊆ {ξ | A ^ q.p ≤ energySum g n ξ} from
      fun ξ hξ => (Real.rpow_le_rpow hAp.le (le_of_lt hξ) (by linarith)).trans (hE ξ))).trans
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hAp q.p)).mp
    apply hh.trans (hm.trans ?_)
    change _ ≤ A ^ q.p * (1 / 64)
    change 64 * n * q.G ^ q.p ≤ A ^ q.p at hA
    linarith
  obtain ⟨hdi, hdm⟩ := deviation_moment h hp hp2 hG.le u n
  have hDB : P.real {ξ | B < ‖deviation g π u n ξ‖} ≤ 1 / 64 := by
    apply markov_power P (by linarith : 0 < q.p) hBp (fun _ => norm_nonneg _) hdi (hdm.trans ?_)
    change 1536 * n * (q.G * (2 * q.R)) ^ q.p ≤ B ^ q.p at hB
    linarith
  apply (measureReal_mono (show _ ⊆ {ξ | A < energy ξ} ∪ {ξ | B < ‖deviation g π u n ξ‖} from ?_)).trans
    ((measureReal_union_le _ _).trans (by linarith))
  intro ξ hξ
  by_contra! hh
  have h₁ : energy ξ ≤ A := le_of_not_gt (fun h' => hh (Or.inl h'))
  have h₂ : ‖deviation g π u n ξ‖ ≤ B := le_of_not_gt (fun h' => hh (Or.inr h'))
  change energy ξ ≤ A at h₁
  change ‖deviation g π u n ξ‖ ≤ B at h₂
  have hg := path_gap h hc hR hG u hn' ξ
  change _ ≤ 3 * q.R * q.G + 3 * q.R * energy ξ + _ at hg
  change q.ε / 2 < f (average g n ξ).val - f u.val at hξ
  have ht' := mul_lt_mul_of_pos_left hξ hn0
  have hh₁ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 3 * q.R by positivity)
  have hh₂ := mul_le_mul_of_nonneg_left hr (mul_nonneg hG.le hR.le)
  change 32768 * (q.G * q.R) * r ≤ _ at ht
  dsimp only [A, B] at hh₁ h₂
  nlinarith only [ht, ht', hg, hh₁, h₂, hh₂, mul_pos (mul_pos hG hR) (by linarith : 0 < r)]

noncomputable def score (g : Point q → ℝ → Space q) (x : Point q) (n : ℕ) (ξ : Path) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ⟪g (chordPoint q x n i) (ξ i), x.val⟫

lemma iid_score (h : SubgradientOracle q f g π) (hR : 0 < q.R) (hG : 0 < q.G)
    (hp : 1 < q.p) (hp2 : q.p ≤ 2) (he : 0 < q.ε) (x : Point q) (n : ℕ)
    (hn : (32768 * (q.G * q.R) / q.ε) ^ (q.p / (q.p - 1)) ≤ n) :
    (Measure.infinitePi (fun _ : ℕ => π)).real {ξ | q.ε / 12 < |score g x n ξ - (f x.val - f 0)|} ≤ 1 / 64 := by
  obtain ⟨hn', ht⟩ := sample_tuning (mul_pos hG hR) he hp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn'
  let r := (n : ℝ) ^ (1 / q.p)
  have hr : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast hn') (by positivity)
  let D := fun (i : ℕ) (z : ℝ) => ⟪g (chordPoint q x n i) z, x.val⟫
  let F := fun ξ : Path => ∑ i ∈ Finset.range n, (D i (ξ i) - ∫ z, D i z ∂π)
  let A := 1536 * r * (q.G * q.R)
  have hA : 0 < A := by dsimp [A, r]; positivity
  have hb := root_scale (n := n) hp.le (mul_nonneg hG.le hR.le) (by norm_num : (1 : ℝ) ≤ 1536)
  change 1536 * n * (q.G * q.R) ^ q.p ≤ A ^ q.p at hb
  obtain ⟨hi, hm⟩ := chord_score_moment h hp hp2 hG.le x n
  have hprob := markov_power (Measure.infinitePi fun _ : ℕ => π) (by linarith : 0 < q.p) hA
    (fun ξ => norm_nonneg (F ξ)) hi (c := 1 / 64) (hm.trans (by linarith))
  apply (measureReal_mono (show _ ⊆ {ξ | A < ‖F ξ‖} from ?_)).trans hprob
  intro ξ hξ
  by_contra! hbad
  change ¬ A < ‖F ξ‖ at hbad
  have hsmall := le_of_not_gt hbad
  have hmean (i : ℕ) : (∫ z, D i z ∂π) = ⟪∫ z, g (chordPoint q x n i) z ∂π, x.val⟫ := by
    change (∫ z, ⟪_, _⟫ ∂π) = _
    have he (z : ℝ) : ⟪g (chordPoint q x n i) z, x.val⟫ = ⟪x.val, g (chordPoint q x n i) z⟫ := real_inner_comm _ _
    simp_rw [he]; rw [integral_inner (h.integrable _)]; exact real_inner_comm _ _
  let m := (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∫ z, D i z ∂π
  have hquad : |f x.val - f 0 - m| ≤ 2 * (q.G * q.R) / n := by
    simpa only [m, hmean] using chord_oracle_bias h hp hG.le x hn'
  have hdiff : score g x n ξ - m = (n : ℝ)⁻¹ * F ξ := by
    simp [score, m, F, D, Finset.sum_sub_distrib, mul_sub]
  have hnoise : |score g x n ξ - m| ≤ (n : ℝ)⁻¹ * A := by
    rw [hdiff, abs_mul, abs_of_nonneg (inv_nonneg.mpr hn0.le)]
    exact mul_le_mul_of_nonneg_left hsmall (inv_nonneg.mpr hn0.le)
  change q.ε / 12 < |score g x n ξ - (f x.val - f 0)| at hξ
  have htri := abs_sub_le (score g x n ξ) m (f x.val - f 0)
  rw [abs_sub_comm m] at htri
  have hlt : q.ε / 12 < (A + 2 * (q.G * q.R)) / n := by
    rw [add_div, div_eq_inv_mul A]; linarith
  have hh := (lt_div_iff₀ hn0).mp hlt
  have hscale := mul_le_mul_of_nonneg_left hr (mul_nonneg hG.le hR.le)
  change 32768 * (q.G * q.R) * r ≤ _ at ht
  dsimp only [A] at hh
  nlinarith only [hh, ht, hscale, mul_pos (mul_pos hG hR) (by linarith : 0 < r)]

end LongTails.Proofs.PolynomialMixingAccuracy
