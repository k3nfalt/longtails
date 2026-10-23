import LongTails.Proofs.GdConvex
import LongTails.Proofs.AdamLogGeometry

open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamAuxiliaryDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma perturbed_smooth_step {f : E → ℝ} {u : E → E} {A K α : ℝ}
    (hA : 0 ≤ A) (hα : 0 ≤ α)
    (hf : ∀ x, HasGradientAt f (u x) x)
    (hlip : ∀ x y, ‖u x - u y‖ ≤ A * ‖x - y‖)
    (hvalue : ∀ x y, |f x - f y| ≤ K * ‖x - y‖)
    (x z q r : E) :
    f (z - α • q + r) ≤ f z - α * ⟪u x, q⟫ +
      A / 2 * ‖z - x‖ ^ 2 + A * α ^ 2 * ‖q‖ ^ 2 + K * ‖r‖ := by
  have hs := OracleTemplate.Gradient.smooth_upper_bound hf hlip z (z - α • q)
  have he : z - α • q - z = -α • q := by module
  rw [he, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg hα] at hs
  have hv := (abs_le.mp (hvalue (z - α • q + r) (z - α • q))).2
  have he' : (z - α • q + r) - (z - α • q) = r := by abel
  rw [he'] at hv
  have hi := abs_real_inner_le_norm (u z - u x) q
  rw [inner_sub_left] at hi
  have hd := mul_le_mul_of_nonneg_right (hlip z x) (norm_nonneg q)
  have hb := mul_le_mul_of_nonneg_left ((abs_le.mp hi).1) hα
  have hd' := mul_le_mul_of_nonneg_left hd hα
  have hy := mul_nonneg hA (sq_nonneg (‖z - x‖ - α * ‖q‖))
  nlinarith

lemma centered_log_step {f : E → ℝ} {u : E → E} {A K α B : ℝ}
    (hA : 0 ≤ A) (hα : 0 ≤ α)
    (hf : ∀ x, HasGradientAt f (u x) x)
    (hlip : ∀ x y, ‖u x - u y‖ ≤ A * ‖x - y‖)
    (hvalue : ∀ x y, |f x - f y| ≤ K * ‖x - y‖)
    (x z q Q signal r : E) (hu : ‖u x‖ ≤ K)
    (hsignal : 0 ≤ ⟪u x, signal⟫) (hbias : ‖Q - signal‖ ≤ B) :
    f (z - α • q + r) ≤ f z - α * ⟪u x, q - Q⟫ + α * K * B +
      A / 2 * ‖z - x‖ ^ 2 + A * α ^ 2 * ‖q‖ ^ 2 + K * ‖r‖ := by
  have hs := perturbed_smooth_step hA hα hf hlip hvalue x z q r
  have hK : 0 ≤ K := (norm_nonneg _).trans hu
  have hi := (abs_real_inner_le_norm (u x) (Q - signal)).trans
    (mul_le_mul hu hbias (norm_nonneg _) hK)
  rw [inner_sub_right] at hi
  have hb := mul_le_mul_of_nonneg_left (abs_le.mp hi).1 hα
  have hp := mul_nonneg hα hsignal
  rw [inner_sub_right]
  linarith

lemma centered_log_path {f : E → ℝ} {u : E → E} {A K α B : ℝ}
    (hA : 0 ≤ A) (hα : 0 ≤ α)
    (hf : ∀ x, HasGradientAt f (u x) x)
    (hlip : ∀ x y, ‖u x - u y‖ ≤ A * ‖x - y‖)
    (hvalue : ∀ x y, |f x - f y| ≤ K * ‖x - y‖)
    (x z q Q signal r : ℕ → E) (n : ℕ) (hzero : z 0 = x 0)
    (hrec : ∀ t < n, z (t + 1) = z t - α • q t + r t)
    (hu : ∀ t < n, ‖u (x t)‖ ≤ K)
    (hsignal : ∀ t < n, 0 ≤ ⟪u (x t), signal t⟫)
    (hbias : ∀ t < n, ‖Q t - signal t‖ ≤ B) :
    f (x n) ≤ f (x 0) +
      (∑ t ∈ Finset.range n, -α * ⟪u (x t), q t - Q t⟫) + n * α * K * B +
      A / 2 * (∑ t ∈ Finset.range n, ‖z t - x t‖ ^ 2) +
      A * α ^ 2 * (∑ t ∈ Finset.range n, ‖q t‖ ^ 2) +
      K * (∑ t ∈ Finset.range n, ‖r t‖) + K * ‖x n - z n‖ := by
  let D := fun t => -α * ⟪u (x t), q t - Q t⟫ + α * K * B +
    A / 2 * ‖z t - x t‖ ^ 2 + A * α ^ 2 * ‖q t‖ ^ 2 + K * ‖r t‖
  have hstep (t : ℕ) (ht : t < n) : f (z (t + 1)) ≤ f (z t) + D t := by
    have hh := centered_log_step hA hα hf hlip hvalue (x t) (z t) (q t) (Q t)
      (signal t) (r t) (hu t ht) (hsignal t ht) (hbias t ht)
    rw [← hrec t ht] at hh
    dsimp [D]
    linarith
  have hsum (k : ℕ) (hk : k ≤ n) : f (z k) ≤ f (z 0) + ∑ t ∈ Finset.range k, D t := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
        have hp := ih (Nat.le_of_lt hk')
        have hs := hstep k hk'
        rw [Finset.sum_range_succ]
        linarith
  have hs := hsum n le_rfl
  rw [hzero] at hs
  have hv := (abs_le.mp (hvalue (x n) (z n))).2
  dsimp [D] at hs
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hs
  simp only [← Finset.mul_sum]
  nlinarith

omit [CompleteSpace E] in
lemma perturbed_local_centered_step {f : E → ℝ} {A G α B : ℝ}
    (hA : 0 ≤ A) (hα : 0 ≤ α) (x z q Q signal r ux uz : E)
    (hbase : f (z - α • q) ≤ f z - α * ⟪uz, q⟫ + A / 2 * α ^ 2 * ‖q‖ ^ 2)
    (hgrad : ‖uz - ux‖ ≤ A * ‖z - x‖)
    (hresid : f (z - α • q + r) ≤ f (z - α • q) + G * ‖r‖)
    (hu : ‖ux‖ ≤ G) (hbias : ‖Q - signal‖ ≤ B) :
    f (z - α • q + r) ≤ f z - α * ⟪ux, signal⟫ - α * ⟪ux, q - Q⟫ +
      α * G * B + A / 2 * ‖z - x‖ ^ 2 + A * α ^ 2 * ‖q‖ ^ 2 + G * ‖r‖ := by
  have hG : 0 ≤ G := (norm_nonneg _).trans hu
  have hi := abs_real_inner_le_norm (uz - ux) q
  rw [inner_sub_left] at hi
  have hd := mul_le_mul_of_nonneg_right hgrad (norm_nonneg q)
  have hb := mul_le_mul_of_nonneg_left ((abs_le.mp hi).1) hα
  have hd' := mul_le_mul_of_nonneg_left hd hα
  have hy := mul_nonneg hA (sq_nonneg (‖z - x‖ - α * ‖q‖))
  have he := (abs_real_inner_le_norm ux (Q - signal)).trans
    (mul_le_mul hu hbias (norm_nonneg _) hG)
  rw [inner_sub_right] at he
  have he' := mul_le_mul_of_nonneg_left (abs_le.mp he).1 hα
  rw [inner_sub_right]
  nlinarith

lemma original_local_step {f : E → ℝ} {g : E → E} {L0 L1 lower K M R α B : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K) (hLK : L1 ≤ K) (hM : 1 ≤ M)
    (hcurv : L0 + 2 * L1 * K ≤ K ^ 2) (hα : 0 ≤ α)
    (hf : ∀ x, HasGradientAt f (g x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 → ‖g y - g x‖ ≤ (L0 + L1 * ‖g x‖) * ‖y - x‖)
    (hbound : ∀ x, ‖g x‖ ≤ K * (1 + f x - lower))
    (x z q Q signal r : E) (hheight : 1 + f x - lower ≤ M)
    (hR : K * R ≤ 1 / 2) (hz : ‖z - x‖ ≤ R)
    (hw : ‖z - α • q - x‖ ≤ R) (hwr : ‖z - α • q + r - x‖ ≤ R)
    (hbias : ‖Q - signal‖ ≤ B) :
    f (z - α • q + r) ≤ f z - α * ⟪g x, signal⟫ - α * ⟪g x, q - Q⟫ +
      α * (2 * K * M) * B + (K ^ 2 * M) / 2 * ‖z - x‖ ^ 2 +
      (K ^ 2 * M) * α ^ 2 * ‖q‖ ^ 2 + (2 * K * M) * ‖r‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hz
  have hM0 : 0 ≤ M := by linarith
  have hnear : K * ‖z - x‖ ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hz hK).trans hR
  have hgx : ‖g x‖ ≤ K * M := (hbound x).trans (mul_le_mul_of_nonneg_left hheight hK)
  have hgz : ‖g z‖ ≤ 2 * K * M := by
    have hh := (AdamLogGeometry.close_value_bound hf hlower hbound x z hnear).trans
      (mul_le_mul_of_nonneg_left hheight (by norm_num : (0 : ℝ) ≤ 2))
    exact (hbound z).trans (by nlinarith [mul_le_mul_of_nonneg_left hh hK])
  have hcurvz : L0 + L1 * ‖g z‖ ≤ K ^ 2 * M := by
    have hh := mul_le_mul_of_nonneg_left hgz hL1
    have hc := mul_le_mul_of_nonneg_right hcurv hM0
    nlinarith [mul_nonneg hL0 (sub_nonneg.2 hM)]
  have hcurvx : L0 + L1 * ‖g x‖ ≤ K ^ 2 * M := by
    have hh := mul_le_mul_of_nonneg_left hgx hL1
    have hc := mul_le_mul_of_nonneg_right hcurv hM0
    nlinarith [mul_nonneg hL0 (sub_nonneg.2 hM), mul_nonneg (mul_nonneg hL1 hK) hM0]
  have hzx : L1 * ‖z - x‖ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hLK (norm_nonneg (z - x))
    linarith
  have hdist : ‖(z - α • q) - z‖ ≤ 2 * R := by
    calc
      _ = ‖((z - α • q) - x) - (z - x)‖ := by congr 1; abel
      _ ≤ ‖(z - α • q) - x‖ + ‖z - x‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hwz : L1 * ‖(z - α • q) - z‖ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdist hL1
    have hh' := mul_le_mul_of_nonneg_right hLK hR0
    linarith
  apply perturbed_local_centered_step (by positivity) hα x z q Q signal r (g x) (g z)
  · have hh := AdamLogGeometry.local_upper hL1 hf hs z (z - α • q) hwz
    have he : z - α • q - z = -α • q := by module
    rw [he, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hα] at hh
    have hc := mul_le_mul_of_nonneg_right hcurvz (sq_nonneg (α * ‖q‖))
    nlinarith
  · exact (hs x z hzx).trans (mul_le_mul_of_nonneg_right hcurvx (norm_nonneg _))
  · have hh := (abs_le.mp (AdamLogGeometry.local_value_lipschitz hK hf hlower hbound
      x (z - α • q + r) (z - α • q) hR hwr hw)).2
    have he : (z - α • q + r) - (z - α • q) = r := by abel
    rw [he] at hh
    have hc := mul_le_mul_of_nonneg_right hheight (by positivity : 0 ≤ 2 * K * ‖r‖)
    nlinarith
  · nlinarith [mul_nonneg hK hM0]
  · exact hbias

lemma local_signal_path {f : E → ℝ} {g : E → E} {L0 L1 lower K M R α B : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K) (hLK : L1 ≤ K) (hM : 1 ≤ M)
    (hcurv : L0 + 2 * L1 * K ≤ K ^ 2) (hα : 0 ≤ α)
    (hf : ∀ x, HasGradientAt f (g x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 → ‖g y - g x‖ ≤ (L0 + L1 * ‖g x‖) * ‖y - x‖)
    (hbound : ∀ x, ‖g x‖ ≤ K * (1 + f x - lower))
    (x z q Q signal r : ℕ → E) (n : ℕ) (hz0 : z 0 = x 0)
    (hrec : ∀ t < n, z (t + 1) = z t - α • q t + r t)
    (hheight : ∀ t < n, 1 + f (x t) - lower ≤ M) (hR : K * R ≤ 1 / 2)
    (hz : ∀ t < n, ‖z t - x t‖ ≤ R)
    (hw : ∀ t < n, ‖z t - α • q t - x t‖ ≤ R)
    (hwr : ∀ t < n, ‖z t - α • q t + r t - x t‖ ≤ R)
    (hbias : ∀ t < n, ‖Q t - signal t‖ ≤ B) :
    α * (∑ t ∈ Finset.range n, ⟪g (x t), signal t⟫) ≤ f (x 0) - lower +
      (∑ t ∈ Finset.range n, -α * ⟪g (x t), q t - Q t⟫) + n * α * (2 * K * M) * B +
      (K ^ 2 * M) / 2 * (∑ t ∈ Finset.range n, ‖z t - x t‖ ^ 2) +
      (K ^ 2 * M) * α ^ 2 * (∑ t ∈ Finset.range n, ‖q t‖ ^ 2) +
      (2 * K * M) * (∑ t ∈ Finset.range n, ‖r t‖) := by
  let D := fun t => -α * ⟪g (x t), signal t⟫ - α * ⟪g (x t), q t - Q t⟫ +
    α * (2 * K * M) * B + (K ^ 2 * M) / 2 * ‖z t - x t‖ ^ 2 +
    (K ^ 2 * M) * α ^ 2 * ‖q t‖ ^ 2 + (2 * K * M) * ‖r t‖
  have hstep (t : ℕ) (ht : t < n) : f (z (t + 1)) ≤ f (z t) + D t := by
    have hh := original_local_step hL0 hL1 hK hLK hM hcurv hα hf hlower hs hbound
      (x t) (z t) (q t) (Q t) (signal t) (r t) (hheight t ht) hR (hz t ht)
      (hw t ht) (hwr t ht) (hbias t ht)
    rw [← hrec t ht] at hh
    dsimp [D]
    linarith
  have hsum (k : ℕ) (hk : k ≤ n) : f (z k) ≤ f (z 0) + ∑ t ∈ Finset.range k, D t := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k < n := by omega
        have hh := hstep k hk'
        have hp := ih (by omega)
        rw [Finset.sum_range_succ]
        linarith
  have hh := hsum n le_rfl
  rw [hz0] at hh
  dsimp [D] at hh
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
  have hn := hlower (z n)
  have he : (∑ t ∈ Finset.range n, -α * ⟪g (x t), q t - Q t⟫) =
      -α * ∑ t ∈ Finset.range n, ⟪g (x t), q t - Q t⟫ := by rw [Finset.mul_sum]
  rw [he]
  nlinarith

end LongTails.Proofs.AdamAuxiliaryDescent
