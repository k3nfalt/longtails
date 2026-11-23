import LongTails.Proofs.DistributedContaminationConcentration
import LongTails.Algorithms.ContaminatedParallelDescent

namespace LongTails.Proofs.ContaminatedTreeProbability

open MeasureTheory
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonTuning (iterations)

noncomputable def weight (p : Params) (l : ℕ) := min 1 ((16 : ℝ)^l / iterations (network p))

lemma weight_nonneg (p : Params) (l : ℕ) : 0 ≤ weight p l := le_min zero_le_one (by positivity)

lemma precision_gain (p : Params) (l : ℕ) :
    let q := (confidence p : ℝ)
    (Real.exp (2*q*weight p l)-1) * (2 * Real.exp (-(levelConfidence p l : ℝ))) ≤
      q / (4 * iterations (network p)) := by
  let q := (confidence p : ℝ)
  let K := (iterations (network p) : ℝ)
  let a := 2*q*weight p l
  have hK : 0 < K := by dsimp [K, iterations]; positivity
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have ha : 0 ≤ a := mul_nonneg (by positivity) (weight_nonneg _ _)
  have hprec : 8*(1+(l:ℝ))+a ≤ levelConfidence p l := by
    unfold levelConfidence
    push_cast
    dsimp only [a, weight, q]
    linarith only [Nat.le_ceil ((confidence p : ℝ) * min 1 ((16:ℝ)^l / iterations (network p)))]
  have hcancel : (Real.exp a - 1) * Real.exp (-a) ≤ a := by
    rw [sub_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    linarith [Real.add_one_le_exp (-a)]
  have hfactor : 2 * Real.exp (-(8*(1+(l:ℝ)))) ≤ (8*(16:ℝ)^l)⁻¹ := by
    have h8 : (16:ℝ) ≤ Real.exp 8 := by
      have hth := Real.exp_one_gt_d9
      have he := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
        (show 2 ≤ Real.exp 1 by linarith) 8
      norm_num [← Real.exp_nat_mul] at he
      linarith
    rw [show -(8*(1+(l:ℝ))) = -8 + l*(-8) by ring, Real.exp_add, Real.exp_nat_mul, Real.exp_neg]
    have hi := inv_anti₀ (by norm_num : (0:ℝ) < 16) h8
    have hpow := pow_le_pow_left₀ (inv_nonneg.mpr (Real.exp_pos _).le) hi l
    apply (mul_le_mul_of_nonneg_left (mul_le_mul hi hpow (by positivity) (by positivity))
      (by norm_num : (0:ℝ) ≤ 2)).trans_eq
    rw [inv_pow, mul_inv_rev]
    ring
  have hlevel : Real.exp (-(levelConfidence p l : ℝ)) ≤ Real.exp (-a) * Real.exp (-(8*(1+(l:ℝ)))) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  change (Real.exp a - 1) * _ ≤ _
  have he0 : 0 ≤ Real.exp a - 1 := by linarith [Real.add_one_le_exp a]
  calc
    _ ≤ (Real.exp a - 1) * (2 * (Real.exp (-a) * Real.exp (-(8*(1+(l:ℝ)))))) := by gcongr
    _ = ((Real.exp a - 1) * Real.exp (-a)) * (2 * Real.exp (-(8*(1+(l:ℝ))))) := by ring
    _ ≤ a * (8*(16:ℝ)^l)⁻¹ := (mul_le_mul_of_nonneg_right hcancel (by positivity)).trans
      (mul_le_mul_of_nonneg_left hfactor ha)
    _ ≤ (2*q*((16:ℝ)^l/K)) * (8*(16:ℝ)^l)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ = _ := by change _ = q / (4*K); field_simp; ring

open scoped Classical

noncomputable def mass {Ω : Type*} (w : ℕ → ℝ) (bad : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, if ω ∈ bad i then w i else 0

lemma mass_measurable {Ω : Type*} [MeasurableSpace Ω] (w : ℕ → ℝ) (bad : ℕ → Set Ω)
    (n : ℕ) (hb : ∀ i < n, MeasurableSet (bad i)) : Measurable (mass w bad n) := by
  apply Finset.measurable_fun_sum
  intro i hi
  exact Measurable.ite (hb i (Finset.mem_range.mp hi)) measurable_const measurable_const

lemma mass_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (bad : ℕ → Set Ω) (r : ℕ → ℝ) (N : ℕ) {θ c : ℝ}
    (hθ : 0 < θ) (hw : ∀ i < N, 0 ≤ w i) (hb : ∀ i < N, MeasurableSet (bad i))
    (hgain : ∀ i < N, (Real.exp (θ*w i)-1) * r i ≤ c)
    (hcond : ∀ i < N, (∫ ω, (if ω ∈ bad i then Real.exp (θ * mass w bad i ω) else 0) ∂P) ≤
      (∫ ω, Real.exp (θ * mass w bad i ω) ∂P) * r i) :
    P.real {ω | 1 ≤ mass w bad N ω} ≤ Real.exp (N*c - θ) := by
  let W (n : ℕ) (ω : Ω) := Real.exp (θ * mass w bad n ω)
  have hi (n : ℕ) (hn : n ≤ N) : Integrable (W n) P := by
    have hm := mass_measurable w bad n (fun i h => hb i (h.trans_le hn))
    apply Integrable.of_bound ((hm.const_mul θ).exp.aestronglyMeasurable) (Real.exp (θ * ∑ i ∈ Finset.range n, w i))
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hθ.le
    apply Finset.sum_le_sum
    intro i hi
    split <;> first | exact le_rfl | exact hw i ((Finset.mem_range.mp hi).trans_le hn)
  have hmgf (n : ℕ) (hn : n ≤ N) : (∫ ω, W n ω ∂P) ≤ Real.exp (n*c) := by
    induction n with
    | zero => simp [W,mass]
    | succ n ih =>
      have hlt : n < N := by omega
      let a := Real.exp (θ*w n) - 1
      have ha : 0 ≤ a := by dsimp [a]; linarith [Real.add_one_le_exp (θ*w n),mul_nonneg hθ.le (hw n hlt)]
      have hW : W (n+1) = fun ω => W n ω + a * (bad n).indicator (W n) ω := by
        funext ω
        dsimp only [W,mass,a]
        rw [Finset.sum_range_succ, mul_add, Real.exp_add]
        by_cases h : ω ∈ bad n <;> simp [h]
        ring
      rw [hW, integral_add (hi n hlt.le) (((hi n hlt.le).indicator (hb n hlt)).const_mul a),
        integral_const_mul]
      have ht := mul_le_mul_of_nonneg_left (hcond n hlt) ha
      change a * (∫ ω, (bad n).indicator (W n) ω ∂P) ≤ a * ((∫ ω, W n ω ∂P) * r n) at ht
      have hn0 : 0 ≤ ∫ ω, W n ω ∂P := integral_nonneg (fun ω => (Real.exp_pos _).le)
      have he := (hgain n hlt).trans (by linarith [Real.add_one_le_exp c] : c ≤ Real.exp c - 1)
      change a*r n ≤ _ at he
      have hmul := mul_le_mul_of_nonneg_left he hn0
      calc
        _ ≤ (∫ ω, W n ω ∂P) * Real.exp c := by linarith only [ht,hmul]
        _ ≤ Real.exp (n*c) * Real.exp c := mul_le_mul_of_nonneg_right (ih hlt.le) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add, Nat.cast_succ]; congr 1; ring
  exact (StoppedVectorConcentration.exponential_tail_of_bound hθ.le (hi N le_rfl)
    (hmgf N le_rfl) 1).trans_eq (by rw [mul_one])

end LongTails.Proofs.ContaminatedTreeProbability
