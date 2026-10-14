import LongTails.Proofs.ComplexifiedHilbert
import LongTails.Proofs.QuadraticContractions
import LongTails.Proofs.CensoredBlockEnergy
import LongTails.Proofs.FiniteCovarianceRitt

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.MarkovProduct

def censorTime (n : ℕ) : Fin n ⊕ Unit → ℕ
  | .inl k => k.val + 1
  | .inr _ => n

noncomputable def censorWeight (q : ℝ) (n : ℕ) : Fin n ⊕ Unit → ℝ
  | .inl k => (1 - q) * q ^ k.val
  | .inr _ => q ^ n

lemma censorWeight_nonneg {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ)
    (i : Fin n ⊕ Unit) : 0 ≤ censorWeight q n i := by
  cases i with
  | inl k => exact mul_nonneg (sub_nonneg.mpr hq1) (pow_nonneg hq _)
  | inr u => exact pow_nonneg hq n

lemma sum_censorWeight (q : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    ∑ i : Fin n ⊕ Unit, censorWeight q n i * f (censorTime n i) = censoredMean q n f := by
  rw [Fintype.sum_sum_type]
  simp only [censorWeight, censorTime, Fintype.sum_unique]
  unfold censoredMean
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k => (1 - q) * q ^ k * f (k + 1))]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma censorWeight_total (q : ℝ) (n : ℕ) : ∑ i, censorWeight q n i = 1 := by
  simpa using sum_censorWeight q n (fun _ => 1)

lemma sum_censored_product_weights {Ω : Type*} [Fintype Ω] (v : Ω → ℝ)
    (q : ℝ) (n : ℕ) (f : Ω → ℕ → ℝ) :
    (∑ i : Ω × (Fin n ⊕ Unit), v i.1 * censorWeight q n i.2 * f i.1 (censorTime n i.2)) =
      ∑ ω, v ω * censoredMean q n (f ω) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω hω
  simp only [mul_assoc, ← Finset.mul_sum, sum_censorWeight]

end OracleTemplate.MarkovProduct

namespace OracleTemplate.MarkovQuadratic

open MarkovProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def liftedStep (η : ℝ) (H : E →L[ℝ] E) :
    Complexified E →L[ℂ] Complexified E :=
  Complexified.lift (ContinuousLinearMap.id ℝ E - η • H)

lemma norm_liftedStep_le_one (H : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η) (hηL : η * L ≤ 2) :
    ‖liftedStep η H‖ ≤ 1 := by
  apply (Complexified.norm_lift_le _).trans
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [sub_apply, ContinuousLinearMap.id_apply, smul_apply, one_mul] using
    quadratic_step_contract H hL hs hp hb hη hηL x

lemma liftedStep_small_increment (H : E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : H.adjoint = H) (hp : ∀ x, 0 ≤ ⟪x, H x⟫)
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (x : Complexified E) :
    ‖liftedStep η H x - x‖ ^ 2 ≤ η * L * (‖x‖ ^ 2 - ‖liftedStep η H x‖ ^ 2) := by
  have hr := quadratic_step_small_increment H hL hs hp hb hη hηL (Complexified.realPart x)
  have hi := quadratic_step_small_increment H hL hs hp hb hη hηL (Complexified.imagPart x)
  simp only [Complexified.norm_sq, Complexified.real_sub, Complexified.imag_sub,
    liftedStep, Complexified.lift_apply, Complexified.real_pair, Complexified.imag_pair,
    sub_apply, ContinuousLinearMap.id_apply, smul_apply, sub_sub_cancel_left, norm_neg]
  linarith

lemma liftedStep_real_increment (H : E →L[ℝ] E) (η : ℝ)
    (hs : H.adjoint = H) (x : Complexified E) :
    (inner ℂ x (x - liftedStep η H x)).im = 0 := by
  have hself : IsSelfAdjoint (Complexified.lift H) := by
    change star (Complexified.lift H) = Complexified.lift H
    rw [ContinuousLinearMap.star_eq_adjoint, Complexified.lift_adjoint H hs]
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself
  have him := hsym.im_inner_self_apply x
  change (inner ℂ x (Complexified.lift H x)).im = 0 at him
  rw [liftedStep, Complexified.lift_gradient_step]
  simp only [sub_apply, ContinuousLinearMap.id_apply, smul_apply, sub_sub_cancel,
    inner_smul_right, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, him,
    mul_zero, zero_mul, add_zero]

noncomputable def liftedProduct (η : ℝ) (H : ℕ → E →L[ℝ] E) :
    ℕ → Complexified E →L[ℂ] Complexified E
  | 0 => 1
  | n + 1 => liftedStep η (H n) * liftedProduct η H n

lemma liftedProduct_norm_le_one (H : ℕ → E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : ∀ k, (H k).adjoint = H k) (hp : ∀ k x, 0 ≤ ⟪x, H k x⟫)
    (hb : ∀ k x, ⟪x, H k x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η) (hηL : η * L ≤ 2) :
    ∀ n, ‖liftedProduct η H n‖ ≤ 1 := by
  intro n
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    change ‖liftedStep η (H n) * liftedProduct η H n‖ ≤ 1
    have hb' := norm_liftedStep_le_one (H n) hL (hs n) (hp n) (hb n) hη hηL
    apply (norm_mul_le _ _).trans
    nlinarith [norm_nonneg (liftedStep η (H n)), norm_nonneg (liftedProduct η H n)]

lemma liftedProduct_path_contract (H : ℕ → E →L[ℝ] E) {L η : ℝ} (hL : 0 < L)
    (hs : ∀ k, (H k).adjoint = H k) (hp : ∀ k x, 0 ≤ ⟪x, H k x⟫)
    (hb : ∀ k x, ⟪x, H k x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η) (hηL : η * L ≤ 2)
    (x : Complexified E) (k : ℕ) : ‖liftedProduct η H (k + 1) x‖ ≤ ‖liftedProduct η H k x‖ := by
  change ‖liftedStep η (H k) (liftedProduct η H k x)‖ ≤ _
  apply ((liftedStep η (H k)).le_opNorm _).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (norm_liftedStep_le_one (H k) hL (hs k) (hp k) (hb k) hη hηL)
    (norm_nonneg (liftedProduct η H k x))

lemma censored_liftedProduct_gap (H : ℕ → E →L[ℝ] E) {L η r : ℝ} (hL : 0 < L)
    (hs : ∀ k, (H k).adjoint = H k) (hp : ∀ k x, 0 ≤ ⟪x, H k x⟫)
    (hb : ∀ k x, ⟪x, H k x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η)
    (hr : 0 ≤ r) (hr1 : r < 1) (hsmall : 8 * (η * L) ≤ 1 - r ^ 2)
    (x : Complexified E) (n : ℕ) :
    censoredMean (r ^ 2) n (fun k => ‖x - liftedProduct η H k x‖ ^ 2) +
      censoredMean (r ^ 2) n (fun k => ‖liftedProduct η H k x‖ ^ 2) ≤ ‖x‖ ^ 2 := by
  have hηL : η * L ≤ 1 := by nlinarith [sq_nonneg r]
  have hg := censored_block_gap hr hr1 hsmall (fun k => liftedProduct η H k x)
    (fun k => liftedStep_small_increment (H k) hL (hs k) (hp k) (hb k) hη hηL _)
    (liftedProduct_path_contract H hL hs hp hb hη (by linarith) x) n
  simp only [liftedProduct, one_apply_eq_self] at hg
  linarith

lemma censored_liftedProduct_disk (H : ℕ → E →L[ℝ] E) {L η r : ℝ} (hL : 0 < L)
    (hs : ∀ k, (H k).adjoint = H k) (hp : ∀ k x, 0 ≤ ⟪x, H k x⟫)
    (hb : ∀ k x, ⟪x, H k x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η)
    (hr : 0 ≤ r) (hr1 : r < 1) (hsmall : 8 * (η * L) ≤ 1 - r ^ 2)
    (x : Complexified E) (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    censoredMean (r ^ 2) n (fun k =>
      ‖liftedProduct η H k x + z • (x - liftedProduct η H k x)‖ ^ 2) ≤ ‖x‖ ^ 2 := by
  have hηL : η * L ≤ 1 := by nlinarith [sq_nonneg r]
  simpa only [liftedProduct, one_apply_eq_self] using
    censored_block_disk hr hr1 hsmall (fun k => liftedProduct η H k x)
      (fun k => liftedStep_small_increment (H k) hL (hs k) (hp k) (hb k) hη hηL _)
      (liftedProduct_path_contract H hL hs hp hb hη (by linarith) x)
      (fun k => liftedStep_real_increment (H k) η (hs k) _) n z hz

noncomputable def censoredCovariance {Ω : Type*} [Fintype Ω] (v : Ω → ℝ)
    (H : Ω → ℕ → E →L[ℝ] E) (η q : ℝ) (N : ℕ) :
    (Complexified E →L[ℂ] Complexified E) →L[ℂ] (Complexified E →L[ℂ] Complexified E) :=
  finiteCovariance (fun i : Ω × (Fin N ⊕ Unit) => v i.1 * censorWeight q N i.2)
    (fun i => liftedProduct η (H i.1) (censorTime N i.2))

lemma censoredCovariance_ritt {Ω : Type*} [Fintype Ω] (v : Ω → ℝ)
    (hv : ∀ ω, 0 ≤ v ω) (hvs : ∑ ω, v ω = 1)
    (H : Ω → ℕ → E →L[ℝ] E) {L η r : ℝ} (hL : 0 < L)
    (hs : ∀ ω k, (H ω k).adjoint = H ω k) (hp : ∀ ω k x, 0 ≤ ⟪x, H ω k x⟫)
    (hb : ∀ ω k x, ⟪x, H ω k x⟫ ≤ L * ‖x‖ ^ 2) (hη : 0 ≤ η)
    (hr : 0 ≤ r) (hr1 : r < 1) (hsmall : 8 * (η * L) ≤ 1 - r ^ 2) (N n : ℕ) :
    (n + 1 : ℝ) * ‖censoredCovariance v H η (r ^ 2) N ^ n -
      censoredCovariance v H η (r ^ 2) N ^ (n + 1)‖ ≤ 4 := by
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  unfold censoredCovariance
  apply finite_covariance_ritt
  · intro i
    exact mul_nonneg (hv i.1) (censorWeight_nonneg (sq_nonneg r) hr2 N i.2)
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, censorWeight_total, mul_one]
    exact hvs
  · intro x
    simp only [sub_apply, one_apply_eq_self]
    rw [sum_censored_product_weights v (r ^ 2) N (fun ω k => ‖x - liftedProduct η (H ω) k x‖ ^ 2),
      sum_censored_product_weights v (r ^ 2) N (fun ω k => ‖liftedProduct η (H ω) k x‖ ^ 2),
      ← Finset.sum_add_distrib]
    calc
      _ ≤ ∑ ω, v ω * ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ω hω
        have h := mul_le_mul_of_nonneg_left
          (censored_liftedProduct_gap (H ω) hL (hs ω) (hp ω) (hb ω) hη hr hr1 hsmall x N) (hv ω)
        simpa only [mul_add] using h
      _ = ‖x‖ ^ 2 := by rw [← Finset.sum_mul, hvs, one_mul]
  · intro z hz x
    simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self]
    rw [sum_censored_product_weights v (r ^ 2) N (fun ω k =>
      ‖liftedProduct η (H ω) k x + z • (x - liftedProduct η (H ω) k x)‖ ^ 2)]
    calc
      _ ≤ ∑ ω, v ω * ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro ω hω
        exact mul_le_mul_of_nonneg_left
          (censored_liftedProduct_disk (H ω) hL (hs ω) (hp ω) (hb ω) hη hr hr1 hsmall x N z hz) (hv ω)
      _ = ‖x‖ ^ 2 := by rw [← Finset.sum_mul, hvs, one_mul]

end OracleTemplate.MarkovQuadratic
