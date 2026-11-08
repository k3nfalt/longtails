import LongTails.Proofs.BirchResourceChainScaling
import Mathlib.Probability.Distributions.Bernoulli

namespace LongTails.Proofs.BirchResourceChain

open Finset MeasureTheory ProbabilityTheory Set
open OracleTemplate.Rennala (Point Instance)
open LongTails.Proofs.BirchResourceGeometry
open LongTails.Setups.BirchNonEuclidean
open LongTails.Setups.UscgConstant (dualNorm)

lemma progress_iff {D : ℕ} (x : Point D) (k : ℕ) : progress x ≤ k ↔ Supported x k := by
  constructor
  · intro h i hi
    exact progress_spec x i (h.trans hi)
  · exact progress_le x

lemma support_closed {D : ℕ} (k : ℕ) : IsClosed {x : Point D | Supported x k} := by
  have he : {x : Point D | Supported x k} =
      ⋂ i : Fin D, ⋂ _h : k ≤ i.val, {x : Point D | x i = 0} := by
    ext x
    simp [Supported]
  rw [he]
  exact isClosed_iInter fun i => isClosed_iInter fun _ =>
    isClosed_eq (EuclideanSpace.proj i : Point D →L[ℝ] ℝ).continuous continuous_const

lemma progress_measurable (D : ℕ) : Measurable (progress : Point D → ℕ) := by
  apply measurable_to_countable'
  intro n
  cases n with
  | zero =>
    change MeasurableSet {x : Point D | progress x = 0}
    have he : {x : Point D | progress x = 0} = {x : Point D | Supported x 0} := by
      ext x
      simp only [mem_ofPred_eq, ← progress_iff, Nat.le_zero]
    rw [he]
    exact (support_closed 0).measurableSet
  | succ n =>
    change MeasurableSet {x : Point D | progress x = n + 1}
    have he : {x : Point D | progress x = n + 1} =
        {x : Point D | Supported x (n + 1)} \ {x : Point D | Supported x n} := by
      ext x
      simp only [mem_ofPred_eq, mem_sdiff, ← progress_iff]
      omega
    rw [he]
    exact (support_closed (n + 1)).measurableSet.diff (support_closed n).measurableSet

lemma grad_measurable (D : ℕ) : Measurable (gradient objective : Point D → Point D) := by
  have hl : LipschitzWith 30 (gradient objective : Point D → Point D) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    exact objective_smooth x y
  exact hl.continuous.measurable

lemma masked_formula {D : ℕ} (x : Point D) :
    maskedCoordinate x = ∑ i : Fin D,
      if progress x = i.val then (gradient objective x i) • basis i else 0 := by
  classical
  by_cases h : progress x < D
  · let i : Fin D := ⟨progress x, h⟩
    rw [maskedCoordinate, dite_eq_left h, sum_eq_single_of_mem i (mem_univ _)]
    · simp only [show progress x = i.val from rfl, ite_true]
      ext j
      simp [basis]
    · intro j _ hj
      have hj' : progress x ≠ j.val := fun he => hj (Fin.ext he.symm)
      simp [hj']
  · rw [maskedCoordinate, dite_eq_right h]
    symm
    exact sum_eq_zero (fun i _ => ite_eq_right (fun (he : progress x = i.val) => h (he.symm ▸ i.isLt)))

lemma masked_measurable (D : ℕ) : Measurable (maskedCoordinate : Point D → Point D) := by
  have he : (maskedCoordinate : Point D → Point D) = fun x => ∑ i : Fin D,
      if progress x = i.val then (gradient objective x i) • basis i else 0 :=
    funext masked_formula
  rw [he]
  apply Finset.measurable_fun_sum
  intro i _
  have hgrad : Measurable (fun x : Point D => gradient objective x i) :=
    (EuclideanSpace.proj i : Point D →L[ℝ] ℝ).continuous.measurable.comp (grad_measurable D)
  exact (hgrad.smul measurable_const).ite
    (measurableSet_eq_fun (progress_measurable D) measurable_const) measurable_const

lemma noisy_measurable (D : ℕ) (q : ℝ) :
    Measurable (Function.uncurry (noisyGradient q : Point D → Bool → Point D)) := by
  have hcoin : Measurable (fun b : Bool => (if b then q⁻¹ else 0) - 1) := measurable_of_countable _
  exact ((grad_measurable D).comp measurable_fst).add
    ((hcoin.comp measurable_snd).smul ((masked_measurable D).comp measurable_fst))

noncomputable def bernoulliLaw (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1) : ProbabilityMeasure Bool :=
  ⟨bernoulliMeasure true false ⟨q, hq, hq'⟩, inferInstance⟩

lemma scaled_oracle_measurable (D : ℕ) (a s q : ℝ) :
    Measurable (Function.uncurry (scaledOracle a s q : Point D → Bool → Point D)) := by
  have ha : Measurable (fun z : Point D × Bool => a⁻¹ • z.1) :=
    (measurable_const (a := a⁻¹)).smul measurable_fst
  have h : Measurable (fun z : Point D × Bool => (a⁻¹ • z.1, z.2)) := ha.prodMk measurable_snd
  have hm := ((measurable_const (a := s)) : Measurable (fun _ : Point D × Bool => s)).smul
    ((noisy_measurable D q).comp h)
  exact hm

lemma hard_oracle {p : Params}
    (hdual : ∀ v, ‖v‖ / 2 ≤ dualNorm p.N v ∧ dualNorm p.N v ≤ ‖v‖)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    let q := s ^ 2 / (s ^ 2 + p.σ ^ 2)
    let hq : 0 < q := div_pos (sq_pos_of_pos hs) (by positivity)
    let hq' : q ≤ 1 := (div_le_one (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg _))
    StochasticGradient p (bernoulliLaw q hq.le hq' : Measure Bool)
      (scaledObjective a s) (scaledOracle a s q) := by
  let q := s ^ 2 / (s ^ 2 + p.σ ^ 2)
  have hq : 0 < q := div_pos (sq_pos_of_pos hs) (by positivity)
  have hq' : q ≤ 1 := (div_le_one (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg _))
  refine ⟨scaled_oracle_measurable p.d a s q, ?_, ?_, ?_, ?_⟩
  · intro x
    exact integrable_bernoulliMeasure true false _ _
  · intro x
    change (∫ b, scaledOracle a s q x b ∂bernoulliMeasure true false ⟨q, hq.le, hq'⟩) = _
    rw [integral_bernoulliMeasure, add_comm]
    exact scaled_mean ha hq s x
  · intro x
    exact integrable_bernoulliMeasure true false _ _
  · intro x
    change (∫ b, dualNorm p.N (scaledOracle a s q x b - gradient (scaledObjective a s) x) ^ 2
      ∂bernoulliMeasure true false ⟨q, hq.le, hq'⟩) ≤ _
    rw [integral_bernoulliMeasure, smul_eq_mul, smul_eq_mul, add_comm]
    change (1 - q) * dualNorm p.N (scaledOracle a s q x false - gradient (scaledObjective a s) x) ^ 2 +
      q * dualNorm p.N (scaledOracle a s q x true - gradient (scaledObjective a s) x) ^ 2 ≤ p.σ ^ 2
    have hd (v : Point p.d) : dualNorm p.N v ^ 2 ≤ ‖v‖ ^ 2 := by
      have ht := hdual v
      exact (sq_le_sq₀ ((div_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans ht.1)
        (norm_nonneg _)).2 ht.2
    refine (add_le_add (mul_le_mul_of_nonneg_left (hd _) (sub_nonneg.mpr hq'))
      (mul_le_mul_of_nonneg_left (hd _) hq.le)).trans ?_
    refine (scaled_variance ha hq hq' x).trans_eq ?_
    have hs' : s ≠ 0 := hs.ne'
    dsimp only [q]
    field_simp
    ring

end LongTails.Proofs.BirchResourceChain
