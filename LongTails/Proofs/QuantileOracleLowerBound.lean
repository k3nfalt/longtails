import LongTails.Proofs.ExecutionHistory
import LongTails.Proofs.NearZeroSumCalculus
import LongTails.Proofs.SgdExecution
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation

open MeasureTheory

namespace LongTails.Proofs.QuantileOracleLowerBound

lemma chi_square_eq {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hQ : ∀ i, Q i ≠ 0) (hPsum : ∑ i, P i = 1) (hQsum : ∑ i, Q i = 1) :
    (∑ i, (P i - Q i) ^ 2 / Q i) = (∑ i, P i ^ 2 / Q i) - 1 := by
  have he (i : ι) : (P i - Q i) ^ 2 / Q i = P i ^ 2 / Q i - 2 * P i + Q i := by
    field_simp [hQ i]
    ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hPsum, hQsum]
  ring

lemma product_weight_sum {ι : Type*} [Fintype ι] (P : ι → ℝ) (N : ℕ) :
    (∑ x : Fin N → ι, ∏ i, P (x i)) = (∑ i, P i) ^ N := by
  rw [← Fintype.prod_sum]
  simp

lemma product_chi_square_eq {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hQ : ∀ i, Q i ≠ 0) (hPsum : ∑ i, P i = 1) (hQsum : ∑ i, Q i = 1) (N : ℕ) :
    (∑ x : Fin N → ι, ((∏ i, P (x i)) - (∏ i, Q (x i))) ^ 2 / (∏ i, Q (x i))) =
      (1 + ∑ i, (P i - Q i) ^ 2 / Q i) ^ N - 1 := by
  rw [chi_square_eq (fun x : Fin N → ι => ∏ i, P (x i))
    (fun x : Fin N → ι => ∏ i, Q (x i))
    (fun x => Finset.prod_ne_zero_iff.mpr fun i _ => hQ (x i))
    (by rw [product_weight_sum, hPsum, one_pow])
    (by rw [product_weight_sum, hQsum, one_pow])]
  simp_rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
  rw [show (∑ x : Fin N → ι, ∏ i, P (x i) ^ 2 / Q (x i)) =
      (∑ i, P i ^ 2 / Q i) ^ N from product_weight_sum (fun i => P i ^ 2 / Q i) N,
    chi_square_eq P Q hQ hPsum hQsum]
  congr 2
  ring

lemma one_add_pow_le_linear {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (hNx : N * x ≤ 1 / 2) :
    (1 + x) ^ N ≤ 1 + 2 * N * x := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : (N : ℝ) * x ≤ 1 / 2 := by push_cast at hNx; nlinarith
    have hi := ih hN
    rw [pow_succ]
    have hm := mul_le_mul_of_nonneg_right hi (by linarith : 0 ≤ 1 + x)
    push_cast
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hN)]

lemma finite_testing_bound {ι : Type*} [Fintype ι] (P Q a : ι → ℝ)
    (hQ : ∀ i, 0 < Q i) (hPsum : ∑ i, P i = 1) (hQsum : ∑ i, Q i = 1)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hχ : ∑ i, (P i - Q i) ^ 2 / Q i ≤ 1 / 4) :
    1 / 2 ≤ ∑ i, (P i * (1 - a i) + Q i * a i) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => |P i - Q i|) (f := Q) (g := fun i => (P i - Q i) ^ 2 / Q i)
    (fun i _ => (hQ i).le) (fun i _ => div_nonneg (sq_nonneg _) (hQ i).le)
    (fun i _ => by rw [sq_abs]; rw [mul_div_cancel₀ _ (ne_of_gt (hQ i))])
  rw [hQsum, one_mul] at hcs
  have habs : 0 ≤ ∑ i, |P i - Q i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have htv : (∑ i, |P i - Q i|) ≤ 1 / 2 := by nlinarith
  have hpoint (i : ι) : P i - |P i - Q i| ≤ P i * (1 - a i) + Q i * a i := by
    have h1 := neg_abs_le (P i - Q i)
    have h2 := le_abs_self (P i - Q i)
    have h3 := mul_nonneg (ha0 i) (sub_nonneg.mpr h2)
    have h4 := mul_nonneg (abs_nonneg (P i - Q i)) (sub_nonneg.mpr (ha1 i))
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  rw [Finset.sum_sub_distrib, hPsum] at hsum
  linarith

lemma repeated_testing_bound {ι : Type*} [Fintype ι] (P Q : ι → ℝ)
    (hQ : ∀ i, 0 < Q i) (hPsum : ∑ i, P i = 1) (hQsum : ∑ i, Q i = 1)
    (N : ℕ) (a : (Fin N → ι) → ℝ) (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1)
    (hN : N * (∑ i, (P i - Q i) ^ 2 / Q i) ≤ 1 / 8) :
    1 / 2 ≤ ∑ x : Fin N → ι,
      ((∏ i, P (x i)) * (1 - a x) + (∏ i, Q (x i)) * a x) := by
  apply finite_testing_bound _ _ a
    (fun x => Finset.prod_pos fun i _ => hQ (x i))
    (by rw [product_weight_sum, hPsum, one_pow])
    (by rw [product_weight_sum, hQsum, one_pow]) ha0 ha1
  rw [product_chi_square_eq P Q (fun i => (hQ i).ne') hPsum hQsum N]
  have hχ0 : 0 ≤ ∑ i, (P i - Q i) ^ 2 / Q i :=
    Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hQ i).le
  have hp := one_add_pow_le_linear hχ0 N (by linarith)
  nlinarith

lemma three_tag_chi_bound {w a : ℝ} (hw : 0 < w) (ha : |a| ≤ w / 4) :
    4 * a ^ 2 / (w / 2 - a) + 4 * a ^ 2 / (w / 2 + a) ≤ 32 * a ^ 2 / w := by
  have ha' := abs_le.mp ha
  have hm : 0 < w / 2 - a := by linarith
  have hp : 0 < w / 2 + a := by linarith
  have hleft : 4 * a ^ 2 / (w / 2 - a) ≤ 16 * a ^ 2 / w := by
    apply (div_le_div_iff₀ hm hw).mpr
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr ha'.2)]
  have hright : 4 * a ^ 2 / (w / 2 + a) ≤ 16 * a ^ 2 / w := by
    apply (div_le_div_iff₀ hp hw).mpr
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr ha'.1)]
  calc
    _ ≤ 16 * a ^ 2 / w + 16 * a ^ 2 / w := add_le_add hleft hright
    _ = _ := by ring

noncomputable def threeTagWeights (w a : ℝ) : Fin 3 → ℝ := ![1 - w, w / 2 + a, w / 2 - a]

lemma threeTagWeights_sum (w a : ℝ) : ∑ i, threeTagWeights w a i = 1 := by
  simp [threeTagWeights, Fin.sum_univ_succ]

lemma threeTagWeights_pos {w a : ℝ} (hw : 0 < w) (hw1 : w < 1) (ha : |a| ≤ w / 4)
    (i : Fin 3) : 0 < threeTagWeights w a i := by
  have ha' := abs_le.mp ha
  fin_cases i <;> simp [threeTagWeights] <;> linarith

lemma threeTagWeights_chi {w a : ℝ} (hw : 0 < w) (ha : |a| ≤ w / 4) :
    (∑ i, (threeTagWeights w a i - threeTagWeights w (-a) i) ^ 2 /
      threeTagWeights w (-a) i) ≤ 32 * a ^ 2 / w := by
  have he : (∑ i, (threeTagWeights w a i - threeTagWeights w (-a) i) ^ 2 /
      threeTagWeights w (-a) i) =
      4 * a ^ 2 / (w / 2 - a) + 4 * a ^ 2 / (w / 2 + a) := by
    simp [threeTagWeights, Fin.sum_univ_succ]
    ring
  rw [he]
  exact three_tag_chi_bound hw ha

lemma advance_prefix_congr {State : Type*} {f g : ℕ → State → State}
    (N call : ℕ) (s : State) (h : ∀ k, call ≤ k → k < call + N → f k = g k) :
    OracleTemplate.StochasticGradient.advance f N call s =
      OracleTemplate.StochasticGradient.advance g N call s := by
  induction N generalizing call s with
  | zero => rfl
  | succ N ih =>
    rw [OracleTemplate.StochasticGradient.advance, OracleTemplate.StochasticGradient.advance,
      h call le_rfl (by omega)]
    apply ih
    intro k hk hk'
    exact h k (by omega) (by omega)

lemma execute_prefix_congr {Query Reply Output : Type*}
    (O : OracleTemplate.Oracle Query Reply) (A : OracleTemplate.Algorithm Query Reply Output)
    (N : ℕ) (seed : A.Seed) (ξ ζ : (k : ℕ) → O.Seed k)
    (h : ∀ k, k < N → ξ k = ζ k) :
    OracleTemplate.execute O A (fun _ => N) seed ξ =
      OracleTemplate.execute O A (fun _ => N) seed ζ := by
  have hist : ∀ k, k ≤ N →
      OracleTemplate.executeIndexedState O A seed ξ k =
        OracleTemplate.executeIndexedState O A seed ζ k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      simp only [OracleTemplate.executeIndexedState]
      rw [congrArg Prod.fst hprev, congrArg Prod.snd hprev]
      have hlen := OracleTemplate.executeIndexedState_length O A seed ζ k
      have hseed : ξ (OracleTemplate.executeIndexedState O A seed ζ k).2.length =
          ζ (OracleTemplate.executeIndexedState O A seed ζ k).2.length :=
        h _ (by rw [hlen]; omega)
      rw [hseed]
  unfold OracleTemplate.execute
  rw [OracleTemplate.executeWithTrace_eq_executeIndexedState,
    OracleTemplate.executeWithTrace_eq_executeIndexedState, hist N le_rfl]

section Quadratic

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def centeredQuadratic (lam : ℝ) (c x : E) : ℝ := lam / 2 * ‖x - c‖ ^ 2

lemma centeredQuadratic_gradient (lam : ℝ) (c x : E) :
    HasGradientAt (centeredQuadratic lam c) (lam • (x - c)) x :=
  hasGradientWithinAt_univ.mp (OracleTemplate.NearZeroSum.gradient_translated_quadratic lam c x Set.univ)

omit [CompleteSpace E] in
lemma centeredQuadratic_convex {lam : ℝ} (hlam : 0 ≤ lam) (c : E) :
    ConvexOn ℝ Set.univ (centeredQuadratic lam c) := by
  have h0 : StrongConvexOn (Set.univ : Set E) 0 (fun _ => (0 : ℝ)) := by
    simpa using (convexOn_const (c := (0 : ℝ)) convex_univ)
  have hs := OracleTemplate.NearZeroSum.strong_convex_add_quadratic (β := lam) (k := 0) h0 c
  have hs' : StrongConvexOn Set.univ lam (centeredQuadratic lam c) := by
    change StrongConvexOn Set.univ lam (fun x : E => lam / 2 * ‖x - c‖ ^ 2)
    simpa only [zero_add, add_zero] using hs
  simpa using hs'.mono hlam

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma centeredQuadratic_min {lam : ℝ} (hlam : 0 ≤ lam) (c : E) :
    IsMinOn (centeredQuadratic lam c) Set.univ c := by
  change ∀ x ∈ Set.univ, lam / 2 * ‖c - c‖ ^ 2 ≤ lam / 2 * ‖x - c‖ ^ 2
  intro x _
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
  exact mul_nonneg (div_nonneg hlam (by norm_num)) (sq_nonneg _)

lemma centeredQuadratic_lipschitz {lam L : ℝ} (hlam : 0 ≤ lam) (hL : lam ≤ L) (c x y : E) :
    ‖gradient (centeredQuadratic lam c) x - gradient (centeredQuadratic lam c) y‖ ≤ L * ‖x - y‖ := by
  rw [(centeredQuadratic_gradient lam c x).gradient, (centeredQuadratic_gradient lam c y).gradient,
    ← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
  exact mul_le_mul_of_nonneg_right hL (norm_nonneg _)

omit [CompleteSpace E] in
lemma centeredQuadratic_wrong_sign {lam : ℝ} (hlam : 0 ≤ lam) {c x : E}
    (hc : ⟪x, c⟫ ≤ 0) : lam / 2 * ‖c‖ ^ 2 ≤ centeredQuadratic lam c x := by
  have hn : ‖c‖ ^ 2 ≤ ‖x - c‖ ^ 2 := by
    rw [norm_sub_sq_real]
    nlinarith [sq_nonneg ‖x‖]
  exact mul_le_mul_of_nonneg_left hn (by positivity)

noncomputable def signDecoder (c x : E) : ℝ := if 0 ≤ ⟪x, c⟫ then 1 else 0

omit [CompleteSpace E] in
lemma signDecoder_bounds (c x : E) : 0 ≤ signDecoder c x ∧ signDecoder c x ≤ 1 := by
  unfold signDecoder
  split <;> norm_num

omit [CompleteSpace E] in
lemma centeredQuadratic_testing {lam : ℝ} (hlam : 0 ≤ lam) (c x : E) :
    lam / 2 * ‖c‖ ^ 2 * (1 - signDecoder c x) ≤ centeredQuadratic lam c x ∧
    lam / 2 * ‖c‖ ^ 2 * signDecoder c x ≤ centeredQuadratic lam (-c) x := by
  by_cases hx : 0 ≤ ⟪x, c⟫
  · simp only [signDecoder, ite_eq_left hx, sub_self, mul_zero, mul_one]
    refine ⟨by unfold centeredQuadratic; positivity, ?_⟩
    have hh := centeredQuadratic_wrong_sign hlam
      (c := -c) (x := x) (by simpa using neg_nonpos.mpr hx)
    simpa only [norm_neg] using hh
  · simp only [signDecoder, ite_eq_right hx, sub_zero, mul_one, mul_zero]
    exact ⟨centeredQuadratic_wrong_sign hlam (le_of_lt (lt_of_not_ge hx)),
      by unfold centeredQuadratic; positivity⟩

omit [CompleteSpace E] in
lemma measurable_signDecoder [MeasurableSpace E] [BorelSpace E] (c : E) :
    Measurable (signDecoder c) := by
  unfold signDecoder
  exact Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const measurable_const

omit [CompleteSpace E] in
lemma randomized_quadratic_testing {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E] {ρ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure ρ]
    (P Q : ι → ℝ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ i, 0 < Q i)
    (hPsum : ∑ i, P i = 1) (hQsum : ∑ i, Q i = 1)
    (hχ : ∑ i, (P i - Q i) ^ 2 / Q i ≤ 1 / 4)
    {lam : ℝ} (hlam : 0 ≤ lam) (c : E) (out : ι → Ω → E)
    (hm : ∀ i, Measurable (out i))
    (hp : ∀ i, MeasureTheory.Integrable (fun ω => centeredQuadratic lam c (out i ω)) ρ)
    (hn : ∀ i, MeasureTheory.Integrable (fun ω => centeredQuadratic lam (-c) (out i ω)) ρ) :
    lam * ‖c‖ ^ 2 / 4 ≤ ∑ i,
      (P i * (∫ ω, centeredQuadratic lam c (out i ω) ∂ρ) +
       Q i * (∫ ω, centeredQuadratic lam (-c) (out i ω) ∂ρ)) := by
  let C := lam / 2 * ‖c‖ ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let a := fun i => ∫ ω, signDecoder c (out i ω) ∂ρ
  have hi (i : ι) : MeasureTheory.Integrable (fun ω => signDecoder c (out i ω)) ρ := by
    apply MeasureTheory.Integrable.of_bound ((measurable_signDecoder c).comp (hm i)).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (signDecoder_bounds c (out i ω)).1]
    exact (signDecoder_bounds c (out i ω)).2
  have ha0 (i : ι) : 0 ≤ a i := MeasureTheory.integral_nonneg fun ω => (signDecoder_bounds c (out i ω)).1
  have ha1 (i : ι) : a i ≤ 1 := by
    have hb := MeasureTheory.integral_mono (hi i) (MeasureTheory.integrable_const (1 : ℝ))
      (fun ω => (signDecoder_bounds c (out i ω)).2)
    simpa using hb
  have ht := finite_testing_bound P Q a hQ hPsum hQsum ha0 ha1 hχ
  have hplus (i : ι) : C * (1 - a i) ≤ ∫ ω, centeredQuadratic lam c (out i ω) ∂ρ := by
    have hb := MeasureTheory.integral_mono
      (((MeasureTheory.integrable_const (1 : ℝ)).sub (hi i)).const_mul C) (hp i)
      (fun ω => (centeredQuadratic_testing hlam c (out i ω)).1)
    simp only [Pi.sub_apply] at hb
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub (MeasureTheory.integrable_const 1) (hi i)] at hb
    simpa [a] using hb
  have hminus (i : ι) : C * a i ≤ ∫ ω, centeredQuadratic lam (-c) (out i ω) ∂ρ := by
    have hb := MeasureTheory.integral_mono ((hi i).const_mul C) (hn i)
      (fun ω => (centeredQuadratic_testing hlam c (out i ω)).2)
    rw [MeasureTheory.integral_const_mul] at hb
    exact hb
  calc
    _ = C * (1 / 2) := by dsimp [C]; ring
    _ ≤ C * ∑ i, (P i * (1 - a i) + Q i * a i) := mul_le_mul_of_nonneg_left ht hC
    _ = ∑ i, (P i * (C * (1 - a i)) + Q i * (C * a i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => add_le_add
      (mul_le_mul_of_nonneg_left (hplus i) (hP i))
      (mul_le_mul_of_nonneg_left (hminus i) (hQ i).le)

end Quadratic

end LongTails.Proofs.QuantileOracleLowerBound
