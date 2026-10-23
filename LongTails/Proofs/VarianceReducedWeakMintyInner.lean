import LongTails.Proofs.VarianceReducedWeakMintySampling
import LongTails.Proofs.VarianceReducedWeakMintyExecution
import LongTails.Proofs.ScalarMomentConcentration
import LongTails.Proofs.VarianceReducedWeakMintyAlgebra

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.VarianceReducedWeakMinty

open LongTails.Setups.FiniteSumWeakMintyInclusion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n b : ℕ} [NeZero n]

lemma picard_step_mean_bound (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (z w y t : E) {η L ν : ℝ} (hν : 0 ≤ ν)
    (hJ : ∀ a c, ‖J η a - J η c‖ ≤ ‖a - c‖)
    (ht : J η (z - η • operator F t) = t)
    (hF : ‖operator F y - operator F t‖ ≤ L * ‖y - t‖)
    (hm : ∑ ξ : Fin b → Fin n, (estimatorValue exact F w y ξ - operator F y) = 0)
    (hv : (𝔼 ξ : Fin b → Fin n, ‖estimatorValue exact F w y ξ - operator F y‖ ^ 2) ≤
      ν * ‖y - w‖ ^ 2) :
    (𝔼 ξ : Fin b → Fin n,
      ‖(QueryPlan.eval (answer F J) (picardStepPlan exact η z w (operator F w) y ξ)).1 - t‖ ^ 2) ≤
      (η ^ 2 * L ^ 2 + 2 * η ^ 2 * ν) * ‖y - t‖ ^ 2 +
        2 * η ^ 2 * ν * ‖t - w‖ ^ 2 := by
  have hh := mean_picard_error (J η) (operator F) z y t
    (fun ξ : Fin b → Fin n => estimatorValue exact F w y ξ - operator F y) hJ ht hF hm hv
  have he (ξ : Fin b → Fin n) :
      operator F y + (estimatorValue exact F w y ξ - operator F y) =
        estimatorValue exact F w y ξ := by abel
  simp only [he] at hh
  simp only [eval_picardStepPlan]
  have hn := FiniteSum.norm_sub_sq_le (y - t) (w - t)
  have hid : (y - t) - (w - t) = y - w := by abel
  rw [hid, norm_sub_rev w t] at hn
  have hm' := mul_le_mul_of_nonneg_left hn (mul_nonneg (sq_nonneg η) hν)
  nlinarith

omit [NeZero n] in
lemma scaled_residual_error_bound (F : E → E) (u y t g : E) {η L : ℝ}
    (hF : ‖F u - F y‖ ≤ L * ‖u - y‖) :
    ‖η • (F u - g)‖ ^ 2 ≤
      4 * η ^ 2 * L ^ 2 * (‖u - t‖ ^ 2 + ‖y - t‖ ^ 2) +
        2 * η ^ 2 * ‖g - F y‖ ^ 2 := by
  have hh := FiniteSum.norm_sub_sq_le (F u - F y) (g - F y)
  have he : (F u - F y) - (g - F y) = F u - g := by abel
  rw [he] at hh
  have hf := pow_le_pow_left₀ (norm_nonneg _) hF 2
  simp only [mul_pow] at hf
  have hn := FiniteSum.norm_sub_sq_le (u - t) (y - t)
  have he' : (u - t) - (y - t) = u - y := by abel
  rw [he'] at hn
  have hmul := mul_le_mul_of_nonneg_left hn (sq_nonneg L)
  have hb : ‖F u - g‖ ^ 2 ≤
      4 * L ^ 2 * (‖u - t‖ ^ 2 + ‖y - t‖ ^ 2) + 2 * ‖g - F y‖ ^ 2 := by
    nlinarith
  have hh' := mul_le_mul_of_nonneg_left hb (sq_nonneg η)
  simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using
    (show η ^ 2 * ‖F u - g‖ ^ 2 ≤
      4 * η ^ 2 * L ^ 2 * (‖u - t‖ ^ 2 + ‖y - t‖ ^ 2) +
        2 * η ^ 2 * ‖g - F y‖ ^ 2 by nlinarith)

noncomputable def scaledError (F : E → E) (η : ℝ) (z : E) (yv : E × E) : ℝ :=
  ‖η • (F yv.1 + yv.2) - (z - yv.1)‖ ^ 2

omit [NeZero n] in
lemma scaledError_prox_pair (F : E → E) {η : ℝ} (hη : η ≠ 0) (z y g : E) :
    scaledError F η z (y, η⁻¹ • (z - y) - g) = ‖η • (F y - g)‖ ^ 2 := by
  unfold scaledError
  dsimp only
  congr 2
  simp only [smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hη, one_smul]
  module

lemma picard_step_error_bound (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (z w y t : E) {η L ν : ℝ} (hη : 0 < η) (hν : 0 ≤ ν)
    (hcontract : η ^ 2 * L ^ 2 + 2 * η ^ 2 * ν ≤ 1)
    (hnoise : η ^ 2 * ν ≤ 1 / 4)
    (hJ : ∀ a c, ‖J η a - J η c‖ ≤ ‖a - c‖)
    (ht : J η (z - η • operator F t) = t)
    (hF : ∀ u v, ‖operator F u - operator F v‖ ≤ L * ‖u - v‖)
    (hm : ∑ ξ : Fin b → Fin n, (estimatorValue exact F w y ξ - operator F y) = 0)
    (hv : (𝔼 ξ : Fin b → Fin n, ‖estimatorValue exact F w y ξ - operator F y‖ ^ 2) ≤
      ν * ‖y - w‖ ^ 2) :
    (𝔼 ξ : Fin b → Fin n, scaledError (operator F) η z
      (QueryPlan.eval (answer F J) (picardStepPlan exact η z w (operator F w) y ξ))) ≤
        9 * ‖y - t‖ ^ 2 + 12 * η ^ 2 * ν * ‖t - w‖ ^ 2 := by
  let Y := fun ξ : Fin b → Fin n =>
    J η (z - η • estimatorValue exact F w y ξ)
  have hp := picard_step_mean_bound exact F J z w y t hν hJ ht (hF y t) hm hv
  simp only [eval_picardStepPlan] at hp
  have hp' : (𝔼 ξ, ‖Y ξ - t‖ ^ 2) ≤ ‖y - t‖ ^ 2 +
      2 * η ^ 2 * ν * ‖t - w‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hcontract (sq_nonneg ‖y - t‖)
    dsimp only [Y]
    nlinarith
  have hb := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ =>
    scaled_residual_error_bound (operator F) (Y ξ) y t (estimatorValue exact F w y ξ)
      (η := η) (hF (Y ξ) y))
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] at hb
  have h1 := mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ 4 * η ^ 2 * L ^ 2)
  have h2 := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * η ^ 2)
  have hn := FiniteSum.norm_sub_sq_le (y - t) (w - t)
  rw [show (y - t) - (w - t) = y - w by abel, norm_sub_rev w t] at hn
  have h3 := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2 * η ^ 2 * ν)
  have ha : η ^ 2 * L ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg η) hν]
  have h4 := mul_le_mul_of_nonneg_right ha (by positivity : 0 ≤ 8 * ‖y - t‖ ^ 2)
  have h5 := mul_le_mul_of_nonneg_right ha
    (by positivity : 0 ≤ 8 * η ^ 2 * ν * ‖t - w‖ ^ 2)
  have h6 := mul_le_mul_of_nonneg_right hnoise (by positivity : 0 ≤ 4 * ‖y - t‖ ^ 2)
  simp only [eval_picardStepPlan, scaledError_prox_pair _ hη.ne']
  change (𝔼 ξ, ‖η • (operator F (Y ξ) - estimatorValue exact F w y ξ)‖ ^ 2) ≤ _
  nlinarith

lemma picard_iterate_bound (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (z w t : E) (η Q C : ℝ) (hQ : 0 ≤ Q)
    (hstep : ∀ y, (𝔼 ξ : Fin b → Fin n,
      ‖(QueryPlan.eval (answer F J) (picardStepPlan exact η z w (operator F w) y ξ)).1 - t‖ ^ 2) ≤
        Q * ‖y - t‖ ^ 2 + C) (k : ℕ) (state : E × E) :
    (𝔼 ξ : Fin k → Fin b → Fin n,
      ‖(QueryPlan.eval (answer F J) (picardPlan exact η z w (operator F w) k ξ state)).1 - t‖ ^ 2) ≤
        Q ^ k * ‖state.1 - t‖ ^ 2 + C * ∑ j ∈ Finset.range k, Q ^ j := by
  induction k generalizing state with
  | zero => simp [picardPlan, QueryPlan.eval]
  | succ k ih =>
    rw [expect_fin_succ]
    simp only [picardPlan, QueryPlan.eval_bind, Fin.cons_zero, Fin.cons_succ]
    calc
      _ ≤ (𝔼 a : Fin b → Fin n,
          (Q ^ k * ‖(QueryPlan.eval (answer F J)
            (picardStepPlan exact η z w (operator F w) state.1 a)).1 - t‖ ^ 2 +
              C * ∑ j ∈ Finset.range k, Q ^ j)) :=
        Finset.expect_le_expect (fun a _ => ih _)
      _ = Q ^ k * (𝔼 a : Fin b → Fin n,
          ‖(QueryPlan.eval (answer F J)
            (picardStepPlan exact η z w (operator F w) state.1 a)).1 - t‖ ^ 2) +
              C * ∑ j ∈ Finset.range k, Q ^ j := by
        simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
      _ ≤ Q ^ k * (Q * ‖state.1 - t‖ ^ 2 + C) + C * ∑ j ∈ Finset.range k, Q ^ j :=
        add_le_add (mul_le_mul_of_nonneg_left (hstep state.1) (pow_nonneg hQ k)) le_rfl
      _ = _ := by rw [Finset.sum_range_succ, pow_succ]; ring

lemma picard_terminal_bound (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (z w t : E) (η Q C A B : ℝ) (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (V : E × E → ℝ)
    (hstep : ∀ y, (𝔼 ξ : Fin b → Fin n,
      ‖(QueryPlan.eval (answer F J) (picardStepPlan exact η z w (operator F w) y ξ)).1 - t‖ ^ 2) ≤
        Q * ‖y - t‖ ^ 2 + C)
    (hterminal : ∀ y, (𝔼 ξ : Fin b → Fin n,
      V (QueryPlan.eval (answer F J) (picardStepPlan exact η z w (operator F w) y ξ))) ≤
        A * ‖y - t‖ ^ 2 + B) (k : ℕ) (state : E × E) :
    (𝔼 ξ : Fin (k + 1) → Fin b → Fin n,
      V (QueryPlan.eval (answer F J) (picardPlan exact η z w (operator F w) (k + 1) ξ state))) ≤
        A * Q ^ k * ‖state.1 - t‖ ^ 2 + A * C * (∑ j ∈ Finset.range k, Q ^ j) + B := by
  induction k generalizing state with
  | zero =>
    rw [expect_fin_succ]
    simpa only [picardPlan, QueryPlan.eval_bind, QueryPlan.eval, Fin.cons_zero,
      Fintype.expect_const, pow_zero, mul_one, Finset.range_zero, Finset.sum_empty,
      mul_zero, add_zero] using hterminal state.1
  | succ k ih =>
    rw [expect_fin_succ]
    have hrec (a : Fin b → Fin n) (ξ : Fin (k + 1) → Fin b → Fin n) :
        QueryPlan.eval (answer F J)
          (picardPlan exact η z w (operator F w) (k + 1 + 1) (Fin.cons a ξ) state) =
        QueryPlan.eval (answer F J)
          (picardPlan exact η z w (operator F w) (k + 1) ξ
            (QueryPlan.eval (answer F J) (picardStepPlan exact η z w (operator F w) state.1 a))) := by
      rw [picardPlan, QueryPlan.eval_bind]
      rfl
    simp only [hrec]
    calc
      _ ≤ (𝔼 a : Fin b → Fin n,
          (A * Q ^ k * ‖(QueryPlan.eval (answer F J)
            (picardStepPlan exact η z w (operator F w) state.1 a)).1 - t‖ ^ 2 +
              A * C * (∑ j ∈ Finset.range k, Q ^ j) + B)) :=
        Finset.expect_le_expect (fun a _ => ih _)
      _ = A * Q ^ k * (𝔼 a : Fin b → Fin n,
          ‖(QueryPlan.eval (answer F J)
            (picardStepPlan exact η z w (operator F w) state.1 a)).1 - t‖ ^ 2) +
              A * C * (∑ j ∈ Finset.range k, Q ^ j) + B := by
        simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
      _ ≤ A * Q ^ k * (Q * ‖state.1 - t‖ ^ 2 + C) +
          A * C * (∑ j ∈ Finset.range k, Q ^ j) + B :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (hstep state.1) (mul_nonneg hA (pow_nonneg hQ k))) le_rfl) le_rfl
      _ = _ := by rw [Finset.sum_range_succ, pow_succ]; ring

lemma picard_geometric_bounds (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (z w t : E) {η L ν h : ℝ} (hη : 0 < η) (hν : 0 ≤ ν)
    (hh : 0 < h) (hhdef : h = 1 - η ^ 2 * L ^ 2) (hnoise : η ^ 2 * ν ≤ h / 8)
    (hJ : ∀ a c, ‖J η a - J η c‖ ≤ ‖a - c‖)
    (ht : J η (z - η • operator F t) = t)
    (hF : ∀ u v, ‖operator F u - operator F v‖ ≤ L * ‖u - v‖)
    (hm : ∀ y, ∑ ξ : Fin b → Fin n, (estimatorValue exact F w y ξ - operator F y) = 0)
    (hv : ∀ y, (𝔼 ξ : Fin b → Fin n, ‖estimatorValue exact F w y ξ - operator F y‖ ^ 2) ≤
      ν * ‖y - w‖ ^ 2) (k : ℕ) :
    let Q := 1 - h / 2
    let Y := fun ξ : Fin (k + 1) → Fin b → Fin n =>
      QueryPlan.eval (answer F J) (picardPlan exact η z w (operator F w) (k + 1) ξ (z, 0))
    (𝔼 ξ, ‖(Y ξ).1 - t‖ ^ 2) ≤ Q ^ (k + 1) * ‖z - t‖ ^ 2 +
      4 * η ^ 2 * ν / h * ‖t - w‖ ^ 2 ∧
    (𝔼 ξ, scaledError (operator F) η z (Y ξ)) ≤
      9 * Q ^ k * ‖z - t‖ ^ 2 + 48 * η ^ 2 * ν / h * ‖t - w‖ ^ 2 := by
  dsimp only
  have ha0 : 0 ≤ η ^ 2 * L ^ 2 := mul_nonneg (sq_nonneg η) (sq_nonneg L)
  have hh1 : h ≤ 1 := by linarith
  have hQ : 0 ≤ 1 - h / 2 := by linarith
  have hQ1 : 1 - h / 2 < 1 := by linarith
  have hc : η ^ 2 * L ^ 2 + 2 * η ^ 2 * ν ≤ 1 - h / 2 := by linarith
  have hstep (y : E) : (𝔼 ξ : Fin b → Fin n,
      ‖(QueryPlan.eval (answer F J) (picardStepPlan exact η z w (operator F w) y ξ)).1 - t‖ ^ 2) ≤
      (1 - h / 2) * ‖y - t‖ ^ 2 + 2 * η ^ 2 * ν * ‖t - w‖ ^ 2 := by
    have hb := picard_step_mean_bound exact F J z w y t hν hJ ht (hF y t) (hm y) (hv y)
    have hm' := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖y - t‖)
    linarith
  have hsum (i : ℕ) : (∑ j ∈ Finset.range i, (1 - h / 2) ^ j) ≤ 2 / h := by
    have hb := LongTails.Proofs.ScalarMomentConcentration.finite_geometric_bound hQ hQ1 i
    convert hb using 1
    field_simp [hh.ne']
    ring
  constructor
  · have hb := picard_iterate_bound exact F J z w t η (1 - h / 2)
      (2 * η ^ 2 * ν * ‖t - w‖ ^ 2) hQ hstep (k + 1) (z, 0)
    have hm' := mul_le_mul_of_nonneg_left (hsum (k + 1))
      (by positivity : 0 ≤ 2 * η ^ 2 * ν * ‖t - w‖ ^ 2)
    dsimp only at hb
    simp only [div_eq_mul_inv] at hb hm' ⊢
    nlinarith
  · have hterminal (y : E) := picard_step_error_bound exact F J z w y t hη hν
      (hc.trans hQ1.le) (show η ^ 2 * ν ≤ 1 / 4 by linarith) hJ ht hF (hm y) (hv y)
    have hb := picard_terminal_bound exact F J z w t η (1 - h / 2)
      (2 * η ^ 2 * ν * ‖t - w‖ ^ 2) 9 (12 * η ^ 2 * ν * ‖t - w‖ ^ 2)
      hQ (by norm_num) (scaledError (operator F) η z) hstep hterminal k (z, 0)
    have hm' := mul_le_mul_of_nonneg_left (hsum k)
      (by positivity : 0 ≤ 18 * η ^ 2 * ν * ‖t - w‖ ^ 2)
    have hh' := mul_le_mul_of_nonneg_left hh1
      (by positivity : 0 ≤ 12 * η ^ 2 * ν / h * ‖t - w‖ ^ 2)
    have hid : (12 * η ^ 2 * ν / h * ‖t - w‖ ^ 2) * h =
        12 * η ^ 2 * ν * ‖t - w‖ ^ 2 := by field_simp
    rw [hid] at hh'
    dsimp only at hb
    simp only [div_eq_mul_inv] at hb hm' hh' ⊢
    nlinarith

lemma picard_relative_error (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (z w t : E) {η L ν h s : ℝ} (hη : 0 < η) (hν : 0 ≤ ν)
    (hh : 0 < h) (hhdef : h = 1 - η ^ 2 * L ^ 2) (hnoise : η ^ 2 * ν ≤ h / 8)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hsmall : η ^ 2 * ν / h ≤ s ^ 2 / 65536)
    (hJ : ∀ a c, ‖J η a - J η c‖ ≤ ‖a - c‖)
    (ht : J η (z - η • operator F t) = t)
    (hF : ∀ u v, ‖operator F u - operator F v‖ ≤ L * ‖u - v‖)
    (hm : ∀ y, ∑ ξ : Fin b → Fin n, (estimatorValue exact F w y ξ - operator F y) = 0)
    (hv : ∀ y, (𝔼 ξ : Fin b → Fin n, ‖estimatorValue exact F w y ξ - operator F y‖ ^ 2) ≤
      ν * ‖y - w‖ ^ 2) (k : ℕ) (hpower : (1 - h / 2) ^ k ≤ s ^ 2 / 8192) :
    let Y := fun ξ : Fin (k + 1) → Fin b → Fin n =>
      QueryPlan.eval (answer F J) (picardPlan exact η z w (operator F w) (k + 1) ξ (z, 0))
    (𝔼 ξ, scaledError (operator F) η z (Y ξ)) ≤
      s ^ 2 / 32 * (𝔼 ξ, ‖z - (Y ξ).1‖ ^ 2) + 256 * (η ^ 2 * ν / h) * ‖z - w‖ ^ 2 := by
  let Y := fun ξ : Fin (k + 1) → Fin b → Fin n =>
    QueryPlan.eval (answer F J) (picardPlan exact η z w (operator F w) (k + 1) ξ (z, 0))
  obtain ⟨hdist, herr⟩ := picard_geometric_bounds exact F J z w t hη hν hh hhdef hnoise
    hJ ht hF hm hv k
  change (𝔼 ξ, scaledError (operator F) η z (Y ξ)) ≤ _
  have hh1 : h ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg η) (sq_nonneg L)]
  have hQ : 0 ≤ 1 - h / 2 := by linarith
  have hv0 : 0 ≤ η ^ 2 * ν / h := by positivity
  have htw : ‖t - w‖ ^ 2 ≤ 2 * ‖z - t‖ ^ 2 + 2 * ‖z - w‖ ^ 2 := by
    have hn := FiniteSum.norm_sub_sq_le (z - w) (z - t)
    rw [show (z - w) - (z - t) = t - w by abel] at hn
    linarith
  have htri : ‖z - t‖ ^ 2 ≤ 2 * (𝔼 ξ, ‖z - (Y ξ).1‖ ^ 2) +
      2 * (𝔼 ξ, ‖(Y ξ).1 - t‖ ^ 2) := by
    have hp (ξ : Fin (k + 1) → Fin b → Fin n) :=
      FiniteSum.norm_sub_sq_le (z - (Y ξ).1) (t - (Y ξ).1)
    have hi (ξ : Fin (k + 1) → Fin b → Fin n) :
        (z - (Y ξ).1) - (t - (Y ξ).1) = z - t := by abel
    simp only [hi, norm_sub_rev t] at hp
    have hm' := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ => hp ξ)
    simpa only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] using hm'
  have hp : (1 - h / 2) ^ (k + 1) ≤ (1 - h / 2) ^ k := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hQ k) (by linarith)
  have hp' := mul_le_mul_of_nonneg_right hp (sq_nonneg ‖z - t‖)
  have hw := mul_le_mul_of_nonneg_left htw hv0
  have hr : (𝔼 ξ, ‖(Y ξ).1 - t‖ ^ 2) ≤
      (1 - h / 2) ^ k * ‖z - t‖ ^ 2 + 8 * (η ^ 2 * ν / h) * (‖z - t‖ ^ 2 + ‖z - w‖ ^ 2) := by
    dsimp only [Y]
    simp only [div_eq_mul_inv] at hdist hp' hw ⊢
    nlinarith
  have he : (𝔼 ξ, scaledError (operator F) η z (Y ξ)) ≤
      16 * (1 - h / 2) ^ k * ‖z - t‖ ^ 2 +
        136 * (η ^ 2 * ν / h) * (‖z - t‖ ^ 2 + ‖z - w‖ ^ 2) := by
    have hqA := mul_nonneg (pow_nonneg hQ k) (sq_nonneg ‖z - t‖)
    have hvA := mul_nonneg hv0 (sq_nonneg ‖z - t‖)
    have hvB := mul_nonneg hv0 (sq_nonneg ‖z - w‖)
    dsimp only [Y]
    simp only [div_eq_mul_inv] at herr hw hqA hvA hvB ⊢
    nlinarith
  exact (relative_error_transfer hs hs1 (pow_nonneg hQ k) hv0 (sq_nonneg _) (sq_nonneg _)
    (Finset.expect_nonneg (fun _ _ => sq_nonneg _)) hpower hsmall hr htri he).2

end OracleTemplate.VarianceReducedWeakMinty
