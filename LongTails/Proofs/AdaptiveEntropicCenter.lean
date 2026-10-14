import LongTails.Proofs.AdaptiveEntropicGeometry
import Mathlib.Data.List.GetD

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma sorted_middle_interval (l : List ℝ) (hs : l.SortedLE) (a b : ℝ)
    (hg : l.length < 2 * l.countP (fun x => decide (a ≤ x ∧ x ≤ b))) :
    a ≤ l.getD (l.length / 2) 0 ∧ l.getD (l.length / 2) 0 ≤ b := by
  classical
  let k := l.length / 2
  let good : ℝ → Bool := fun x => decide (a ≤ x ∧ x ≤ b)
  have hk : k < l.length := by
    have hc := List.countP_le_length (p := good) (l := l)
    dsimp [k, good] at *
    omega
  rw [List.getD_eq_getElem _ _ hk]
  change a ≤ l[k] ∧ l[k] ≤ b
  constructor
  · by_contra h
    have hz : (l.take (k + 1)).countP good = 0 := by
      apply List.countP_eq_zero.mpr
      intro x hx
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
      have hil : i < l.length := by
        exact lt_of_lt_of_le hi (by simpa only [List.length_take] using Nat.min_le_right (k + 1) l.length)
      have hik : i ≤ k := by
        have hh := lt_of_lt_of_le hi (by simpa only [List.length_take] using Nat.min_le_left (k + 1) l.length)
        omega
      have hv := hs.getElem_le_getElem_of_le (hi := hil) (hj := hk) hik
      have he' : l[i] = x := by simpa using he
      rw [he'] at hv
      simp only [good, decide_eq_true_eq]
      intro hgx
      exact h (hgx.1.trans hv)
    have hc := List.countP_le_length (p := good) (l := l.drop (k + 1))
    have he := List.countP_append (p := good) (l₁ := l.take (k + 1)) (l₂ := l.drop (k + 1))
    rw [List.take_append_drop, hz, zero_add] at he
    rw [← he, List.length_drop] at hc
    dsimp [good, k] at *
    omega
  · by_contra h
    have hz : (l.drop k).countP good = 0 := by
      apply List.countP_eq_zero.mpr
      intro x hx
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
      have hil : k + i < l.length := by simp only [List.length_drop] at hi; omega
      have hv := hs.getElem_le_getElem_of_le (hi := hk) (hj := hil) (Nat.le_add_right k i)
      have he' : l[k + i] = x := by simpa using he
      rw [he'] at hv
      simp only [good, decide_eq_true_eq]
      intro hgx
      exact h (hv.trans hgx.2)
    have hc := List.countP_le_length (p := good) (l := l.take k)
    have he := List.countP_append (p := good) (l₁ := l.take k) (l₂ := l.drop k)
    rw [List.take_append_drop, hz, add_zero] at he
    rw [← he, List.length_take] at hc
    have hm := Nat.min_le_left k l.length
    dsimp [good, k] at *
    omega

lemma medianCenter_accuracy {d : ℕ} (history : List (Vector d)) (μ : Vector d) (R : ℝ)
    (hR : 0 ≤ R)
    (hg : history.length < 2 * history.countP (fun v => decide (dualNorm (v - μ) ≤ R))) :
    dualNorm (medianCenter history - μ) ≤ R := by
  classical
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  let values := history.map (fun v => v i)
  let sorted := values.mergeSort (· ≤ ·)
  have hc : history.countP (fun v => decide (dualNorm (v - μ) ≤ R)) ≤
      values.countP (fun x => decide (μ i - R ≤ x ∧ x ≤ μ i + R)) := by
    rw [List.countP_map]
    apply List.countP_mono_left
    intro v hv hgood
    simp only [decide_eq_true_eq] at *
    have hcoord := norm_le_pi_norm (fun j => (v - μ) j) i
    change |v i - μ i| ≤ dualNorm (v - μ) at hcoord
    have hab := abs_le.mp (hcoord.trans hgood)
    dsimp only [Function.comp_def]
    simp only [decide_eq_true_eq]
    constructor <;> linarith
  have hp : sorted.Perm values := List.mergeSort_perm _ _
  have hlen : sorted.length = history.length := by simp [sorted, values]
  have hcount := hp.countP_eq (fun x => decide (μ i - R ≤ x ∧ x ≤ μ i + R))
  have hs : sorted.length < 2 * sorted.countP
      (fun x => decide (μ i - R ≤ x ∧ x ≤ μ i + R)) := by
    rw [hlen, hcount]
    omega
  have hm := sorted_middle_interval sorted List.sortedLE_mergeSort (μ i - R) (μ i + R) hs
  rw [hlen] at hm
  change |((history.map (fun v => v i)).mergeSort (· ≤ ·)).getD (history.length / 2) 0 - μ i| ≤ R
  apply abs_le.mpr
  change μ i - R ≤ ((history.map (fun v => v i)).mergeSort (· ≤ ·)).getD (history.length / 2) 0 ∧
    ((history.map (fun v => v i)).mergeSort (· ≤ ·)).getD (history.length / 2) 0 ≤ μ i + R at hm
  constructor <;> linarith [hm.1, hm.2]

lemma trajectory_distance {d : ℕ} (x : ℕ → simplex d)
    (hstep : ∀ n, oneNorm ((x (n + 1)).val - (x n).val) ≤ 8 / (n + 1))
    (i n : ℕ) : oneNorm ((x (i + n)).val - (x i).val) ≤ 8 * n / (i + 1) := by
  induction n with
  | zero => simp [oneNorm]
  | succ n ih =>
    have ht := oneNorm_add ((x (i + n + 1)).val - (x (i + n)).val)
      ((x (i + n)).val - (x i).val)
    rw [sub_add_sub_cancel] at ht
    have hf : (8 : ℝ) / ((i + n : ℕ) + 1) ≤ 8 / (i + 1) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      push_cast
      linarith
    have hh := add_le_add ((hstep (i + n)).trans hf) ih
    calc
      _ ≤ _ := ht
      _ ≤ 8 / (i + 1) + 8 * n / (i + 1) := hh
      _ = _ := by push_cast; ring

lemma window_trajectory_distance {d : ℕ} (x : ℕ → simplex d)
    (hstep : ∀ n, oneNorm ((x (n + 1)).val - (x n).val) ≤ 8 / (n + 1))
    {i t k : ℕ} (ht : 0 < t) (hi : i ≤ t) (hik : t - k ≤ i) :
    oneNorm ((x t).val - (x i).val) ≤ 24 * k / t := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  by_cases hsmall : t ≤ 2 * k
  · apply (simplex_diameter (x t) (x i)).trans
    apply (le_div_iff₀ htR).mpr
    have hcast : (t : ℝ) ≤ 2 * k := by exact_mod_cast hsmall
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hdist := trajectory_distance x hstep i (t - i)
  rw [Nat.add_sub_of_le hi] at hdist
  have hdiff : t - i ≤ k := by omega
  have hden : (t : ℝ) ≤ 2 * ((i : ℝ) + 1) := by
    have hh : t ≤ 2 * (i + 1) := by omega
    exact_mod_cast hh
  have hnum : (t - i : ℕ) ≤ k := hdiff
  have hnumR : ((t - i : ℕ) : ℝ) ≤ k := by exact_mod_cast hnum
  apply hdist.trans
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < i + 1) htR).mpr
  have ha := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ 8 * (t - i : ℕ))
  have hb := mul_le_mul_of_nonneg_right hnumR (by positivity : (0 : ℝ) ≤ 16 * ((i : ℝ) + 1))
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

lemma window_failure_bound (q : Public) (hH : 0 ≤ confidence q) {t : ℕ} (ht : 0 < t) :
    Real.exp (-(window q t : ℝ) / 8) ≤
      Real.exp (-confidence q) / ((t : ℝ) * (t + 1)) := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (0 : ℝ) < t + 1 := by positivity
  have hk : 16 * (confidence q + Real.log ((t : ℝ) + 1)) ≤ (window q t : ℝ) :=
    Nat.le_ceil _
  have he := Real.exp_le_exp.mpr (show -(window q t : ℝ) / 8 ≤
      -2 * confidence q - 2 * Real.log ((t : ℝ) + 1) by linarith)
  have hlog : 2 * Real.log ((t : ℝ) + 1) = Real.log (((t : ℝ) + 1) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [Real.exp_sub, hlog, Real.exp_log (sq_pos_of_pos ht1)] at he
  have hnum : Real.exp (-2 * confidence q) ≤ Real.exp (-confidence q) :=
    Real.exp_le_exp.mpr (by linarith)
  have hden : (t : ℝ) * (t + 1) ≤ ((t : ℝ) + 1) ^ 2 := by nlinarith
  exact he.trans ((div_le_div_of_nonneg_right hnum (sq_nonneg _)).trans
    (div_le_div_of_nonneg_left (Real.exp_nonneg _) (mul_pos htR ht1) hden))

lemma countP_ofFn_real {α : Type*} (P : α → Bool) (n : ℕ) (f : Fin n → α) :
    ((List.ofFn f).countP P : ℝ) = ∑ i, if P (f i) then (1 : ℝ) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    by_cases h : P (f 0)
    · rw [List.countP_cons_of_pos h, Nat.cast_add, ih]
      simp [h, add_comm]
    · rw [List.countP_cons_of_neg h, ih]
      simp [h]

lemma sum_reverse_window (f : ℕ → ℝ) {n k : ℕ} (hk : k ≤ n) :
    (∑ i ∈ Finset.range k, f (n - 1 - i)) = ∑ j ∈ Finset.Ico (n - k) n, f j := by
  apply Finset.sum_bij (fun i _ => n - 1 - i)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Ico]
    omega
  · intro i hi j hj he
    simp only [Finset.mem_range] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_Ico] at hj
    refine ⟨n - 1 - j, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

lemma medianCenter_of_bad_count {d k : ℕ} (v : Fin k → Vector d) (bad : Fin k → Bool)
    (μ : Vector d) (R : ℝ) (hR : 0 ≤ R)
    (hgood : ∀ i, ¬ bad i → dualNorm (v i - μ) ≤ R)
    (hbad : (∑ i, if bad i then (1 : ℝ) else 0) < (k : ℝ) / 2) :
    dualNorm (medianCenter (List.ofFn v) - μ) ≤ R := by
  classical
  have hsum : (∑ i, if bad i then (0 : ℝ) else 1) ≤
      ((List.ofFn v).countP (fun x => decide (dualNorm (x - μ) ≤ R)) : ℝ) := by
    rw [countP_ofFn_real]
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : bad i
    · simp only [ite_eq_left h]
      split_ifs <;> norm_num
    · simp [h, hgood i h]
  have he : (∑ i, if bad i then (0 : ℝ) else 1) =
      (k : ℝ) - ∑ i, if bad i then (1 : ℝ) else 0 := by
    calc
      _ = ∑ i, ((1 : ℝ) - if bad i then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> norm_num
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  rw [he] at hsum
  have hcard : (k : ℝ) < 2 * ((List.ofFn v).countP
      (fun x => decide (dualNorm (x - μ) ≤ R)) : ℝ) := by linarith
  have hnat : k < 2 * (List.ofFn v).countP (fun x => decide (dualNorm (x - μ) ≤ R)) := by
    exact_mod_cast hcard
  exact medianCenter_accuracy (List.ofFn v) μ R hR (by simpa using hnat)

end OracleTemplate.AdaptiveHeavyTailSimplex
