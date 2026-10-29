import LongTails.Proofs.CovarianceSoftCutDensity

open MeasureTheory

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutTrajectory

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Proofs.CovarianceSoftCutDensity

@[fun_prop] lemma continuous_batchMean (q : Params) (b t : ℕ) :
    Continuous (batchMean q b t) := by
  unfold batchMean
  fun_prop

lemma generatorCuts_list_succ (q : Params) (α η : ℝ) (b n : ℕ)
    (replies : ℕ → Space q) :
    List.ofFn (generatorCuts q α η b (n + 1) replies) =
      List.ofFn (generatorCuts q α η b n replies) ++
        [(batchMean q b n replies, generatorPoint q α η b n replies)] := by
  simp only [generatorCuts]
  rw [List.ofFn_fin_append]
  rfl

lemma continuous_generatorCuts (q : Params) (hR : 0 < q.R) (α η : ℝ) (b n : ℕ) :
    Continuous (generatorCuts q α η b n) := by
  induction n with
  | zero => exact continuous_pi (fun i => Fin.elim0 i)
  | succ n ih =>
      have hp := (continuous_centroid_ofFn q hR α η n).comp ih
      have hn := (continuous_batchMean q b n).prodMk hp
      apply continuous_pi
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [generatorCuts, Fin.append_left, Function.comp_def] using
          (continuous_apply j).comp ih
      · simpa only [generatorCuts, Fin.append_right, Function.comp_def] using hn

lemma continuous_generatorPoint (q : Params) (hR : 0 < q.R) (α η : ℝ) (b n : ℕ) :
    Continuous (generatorPoint q α η b n) := by
  unfold generatorPoint
  simpa only [Function.comp_def] using
    (continuous_centroid_ofFn q hR α η n).comp (continuous_generatorCuts q hR α η b n)

lemma generatorCuts_eq_of_prefix (q : Params) (α η : ℝ) (b n : ℕ)
    (r s : ℕ → Space q) (h : ∀ i, i < n * b → r i = s i) :
    generatorCuts q α η b n r = generatorCuts q α η b n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn : n * b ≤ (n + 1) * b := Nat.mul_le_mul_right b (Nat.le_succ n)
      have hp := ih (fun i hi => h i (lt_of_lt_of_le hi hn))
      have hb : batchMean q b n r = batchMean q b n s := by
        unfold batchMean
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply h
        have hi := i.isLt
        rw [Nat.add_mul, one_mul]
        omega
      simp only [generatorCuts, hp, hb]

lemma generatorPoint_eq_of_prefix (q : Params) (α η : ℝ) (b n : ℕ)
    (r s : ℕ → Space q) (h : ∀ i, i < n * b → r i = s i) :
    generatorPoint q α η b n r = generatorPoint q α η b n s := by
  unfold generatorPoint
  rw [generatorCuts_eq_of_prefix q α η b n r s h]

lemma generator_mass_bound (q : Params) (hd : 0 < q.d) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (b n : ℕ) (replies : ℕ → Space q) :
    mass q α (2 / α) (List.ofFn (generatorCuts q α (2 / α) b n replies)) ≤
      (5 / 6 : ℝ) ^ n * mass q α (2 / α) [] := by
  induction n with
  | zero => simp [generatorCuts]
  | succ n ih =>
      rw [generatorCuts_list_succ]
      apply (mass_append_centroid_contracts q hd hR α hα _ (batchMean q b n replies)).trans
      calc
        (5 / 6 : ℝ) * mass q α (2 / α) (List.ofFn (generatorCuts q α (2 / α) b n replies)) ≤
            (5 / 6 : ℝ) * ((5 / 6 : ℝ) ^ n * mass q α (2 / α) []) := by gcongr
        _ = (5 / 6 : ℝ) ^ (n + 1) * mass q α (2 / α) [] := by ring

lemma generator_mass_exp_bound (q : Params) (hd : 0 < q.d) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (b n : ℕ) (replies : ℕ → Space q) :
    mass q α (2 / α) (List.ofFn (generatorCuts q α (2 / α) b n replies)) ≤
      Real.exp (-(n : ℝ) / 6) * mass q α (2 / α) [] := by
  apply (generator_mass_bound q hd hR α hα b n replies).trans
  have he : (5 / 6 : ℝ) ≤ Real.exp (-1 / 6) := by
    have h := Real.add_one_le_exp (-1 / 6)
    linarith
  have hp : (5 / 6 : ℝ) ^ n ≤ Real.exp (-(n : ℝ) / 6) := by
    calc
      (5 / 6 : ℝ) ^ n ≤ (Real.exp (-1 / 6)) ^ n := by gcongr
      _ = Real.exp (-(n : ℝ) / 6) := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact mul_le_mul_of_nonneg_right hp (le_of_lt (mass_pos q hR α (2 / α) []))

end LongTails.Proofs.CovarianceSoftCutTrajectory
