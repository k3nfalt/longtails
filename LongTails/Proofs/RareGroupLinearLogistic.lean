import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import LongTails.Setups.RareGroupLinearLogistic
import LongTails.Proofs.TrajectoryExecution
import Mathlib.Tactic

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.RareGroupLinearLogistic

open LongTails.Setups.RareGroupLinearLogistic
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

lemma logit_derivative (m : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp (-t))) (-Real.sigmoid (-m)) m := by
  have h := (((hasDerivAt_id m).neg.exp).const_add 1).log
    (by change 1 + Real.exp (-m) ≠ 0; positivity)
  change HasDerivAt _ (Real.exp (-m)*(-1) / (1+Real.exp (-m))) m at h
  rw [← Real.sigmoid_mul_rexp_neg m, Real.sigmoid_def]
  convert h using 1 <;> simp [div_eq_mul_inv, mul_comm]

lemma row_derivative {d : ℕ} (x w : Features d) :
    HasFDerivAt (fun u : Features d => Real.log (1 + Real.exp (-⟪u,x⟫)))
      ((-Real.sigmoid (-⟪w,x⟫)) • innerSL ℝ x) w := by
  have h := (logit_derivative ⟪x,w⟫).comp_hasFDerivAt w (innerSL ℝ x).hasFDerivAt
  convert h using 1
  · ext u
    simp [real_inner_comm u x]
  · rw [real_inner_comm w x]

lemma meanLoss_derivative {d n : ℕ} (x : Fin n → Features d) (w : Features d) :
    HasGradientAt (meanLoss x) (-meanVote x w) w := by
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => row_derivative (x i) w)).const_mul
    ((n : ℝ)⁻¹)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · rfl
  · ext y
    simp only [meanVote, InnerProductSpace.toDual_apply_apply, inner_neg_left, real_inner_smul_left,
    sum_inner, smul_apply, FunLike.coe_sum, Finset.sum_apply,
    innerSL_apply_apply, smul_eq_mul, neg_mul, Finset.sum_neg_distrib, mul_neg]

lemma loss_derivative {P : Public} (D : Data P) (w : Features P.d) :
    HasGradientAt (loss D) (-vote D w) w := by
  have h := ((meanLoss_derivative D.core w).hasFDerivAt.const_mul (1-P.p)).add
    ((meanLoss_derivative D.rare w).hasFDerivAt.const_mul P.p)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · rfl
  · simp [vote, map_add, map_smul, smul_neg, add_comm]

lemma meanVote_inner {d n : ℕ} (x : Fin n → Features d) (v w : Features d) :
    ⟪v, meanVote x w⟫ = (n : ℝ)⁻¹ * ∑ i, Real.sigmoid (-⟪w, x i⟫) * ⟪v, x i⟫ := by
  simp [meanVote, real_inner_smul_right, inner_sum]

lemma meanVote_price {d n : ℕ} (x : Fin n → Features d) (v w : Features d) :
    ⟪v, meanVote x w⟫ ≤ (n : ℝ)⁻¹ * ∑ i, max ⟪v, x i⟫ 0 := by
  rw [meanVote_inner]
  gcongr with i
  rcases le_total ⟪v, x i⟫ 0 with h | h
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.sigmoid_nonneg _) h).trans (le_max_right _ _)
  · exact (mul_le_of_le_one_left h (Real.sigmoid_le_one _)).trans (le_max_left _ _)

lemma inner_vote {p : Params} (H : Obstruction p)
    (hp : 0 ≤ p.p) (hp' : p.p ≤ 1) (w : Features p.d) :
    ⟪p.v, vote p.data w⟫ ≤ p.p * capacity p := by
  have core : ⟪p.v, meanVote p.data.core w⟫ ≤ 0 := by
    rw [meanVote_inner]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (Real.sigmoid_nonneg _) (H.2.2 i))
  rw [vote, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  exact add_le_of_nonpos_of_le (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp') core)
    (mul_le_mul_of_nonneg_left (meanVote_price _ _ _) hp)

noncomputable def oracle {P : Public} (D : Data P) :
    Oracle (Features P.d) (Bool × Features P.d) where
  answer _ q _ := answer D q.2

lemma fails_within {p : Params} (H : Obstruction p)
    (hp : 0 < p.p) (hp' : p.p < 1) (hc : 0 < capacity p)
    (A : Algorithm (Features p.d) (Bool × Features p.d) (Features p.d))
    (ha : family p.toPublic A) (b : Fin 1 → ℕ)
    (hb : b 0 ≠ 0 → ((b 0 : ℝ)-1) * (p.p*capacity p) ≤ -⟪p.v, vote p.data p.start⟫) (seed : A.Seed) (ξ : ℕ → Unit) :
    ¬ Fits p.data (execute (oracle p.data) A b seed ξ) := by
  classical
  obtain ⟨point, h, hh, initial, query, update, output⟩ := ha
  let R := fun (q : Fin 1 × Features p.d) => answer p.data q.2
  let step := fun s => A.update s (R (A.query s))
  let s := fun t : ℕ => step^[t] (A.initial seed)
  have first : ¬ Fits p.data p.start := fun hf => (not_lt_of_ge H.2.1) (H.1 _ hf)
  have one : point (s 1) = p.start + h • vote p.data p.start := by
    change point (A.update (A.initial seed) (R (A.query (A.initial seed)))) = _
    rw [update, query, initial]
    simp [R, answer, first]
  have inc (u : A.State) :
      ⟪p.v, point (step u)⟫ ≤ ⟪p.v, point u⟫ + h * (p.p*capacity p) := by
    change ⟪p.v, point (A.update u (R (A.query u)))⟫ ≤ _
    rw [update, query]
    by_cases hf : Fits p.data (point u)
    · simp [R, answer, hf]
      exact (mul_pos hh (mul_pos hp hc)).le
    · simp only [R, answer, decide_eq_false hf, Bool.false_eq_true, ite_false]
      rw [inner_add_right, real_inner_smul_right]
      linarith [mul_le_mul_of_nonneg_left (inner_vote H hp.le hp'.le (point u)) hh.le]
  have bound (t : ℕ) :
      ⟪p.v, point (s (t+1))⟫ ≤ h * ((t:ℝ)*(p.p*capacity p) + ⟪p.v, vote p.data p.start⟫) := by
    induction t with
    | zero =>
      rw [one, inner_add_right, real_inner_smul_right]
      simpa only [Nat.cast_zero, zero_mul, zero_add, add_le_iff_nonpos_left] using H.2.1
    | succ t ih =>
      have hs : s (t+1+1) = step (s (t+1)) := Function.iterate_succ_apply' _ _ _
      rw [hs, Nat.cast_succ]
      linarith [inc (s (t+1))]
  obtain ⟨t, ht, he⟩ := execute_eq_trajectory (oracle p.data) A b seed ξ R (by intros; rfl)
  simp only [Fin.sum_univ_one] at ht
  rw [he, output]
  change ¬ Fits p.data (point (s t))
  cases t with
  | zero =>
    change ¬ Fits p.data (point (A.initial seed))
    rwa [initial]
  | succ t =>
    intro hf
    have ht' : (t : ℝ)+1 ≤ b 0 := by exact_mod_cast ht
    have htime := (mul_le_mul_of_nonneg_right (show (t:ℝ) ≤ (b 0:ℝ)-1 by linarith)
      (mul_pos hp hc).le).trans (hb (by omega))
    exact (not_lt_of_ge ((bound t).trans
      (mul_nonpos_of_nonneg_of_nonpos hh.le (by linarith)))) (H.1 _ hf)

end LongTails.Proofs.RareGroupLinearLogistic
