import Mathlib

namespace LongTails.Proofs.BernoulliCountCrossing

open MeasureTheory
open ProbabilityTheory

noncomputable def cutoff (T k : ℕ) (c : ℝ) : ℕ := min T ⌊(k : ℝ) / c⌋₊

lemma crossing_witness {N : ℕ → ℕ} {T n : ℕ} {c : ℝ}
    (hc : 0 < c) (hmono : Monotone N) (hbound : ∀ t, N t ≤ t)
    (hn : 0 < n) (hnT : n ≤ T) (hcross : c * n ≤ N n) :
    ∃ k ∈ Finset.Icc 1 T, k ≤ N (cutoff T k c) ∧ c * cutoff T k c ≤ k := by
  have hk : 0 < N n := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    by_contra hh
    have hz : N n = 0 := by omega
    simp only [hz, Nat.cast_zero] at hcross
    nlinarith
  have hnf : n ≤ ⌊(N n : ℝ) / c⌋₊ := by
    apply Nat.le_floor
    exact (le_div_iff₀ hc).mpr (by nlinarith)
  have hfloor : (⌊(N n : ℝ) / c⌋₊ : ℝ) ≤ (N n : ℝ) / c :=
    Nat.floor_le (by positivity)
  refine ⟨N n, Finset.mem_Icc.mpr ⟨hk, (hbound n).trans hnT⟩,
    hmono (le_min hnT hnf), ?_⟩
  have hh : (cutoff T (N n) c : ℝ) ≤ ⌊(N n : ℝ) / c⌋₊ := by
    exact_mod_cast min_le_right T ⌊(N n : ℝ) / c⌋₊
  exact (mul_le_mul_of_nonneg_left (hh.trans hfloor) hc.le).trans_eq
    (by field_simp)

lemma geometric_sum_bound {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (T : ℕ) :
    ∑ k ∈ Finset.range T, q ^ (k + 1) ≤ q / (1 - q) := by
  have hid : (1 - q) * (∑ k ∈ Finset.range T, q ^ (k + 1)) = q - q ^ (T + 1) := by
    induction T with
    | zero => simp
    | succ T ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  apply (le_div_iff₀ (by linarith : 0 < 1 - q)).mpr
  nlinarith [pow_nonneg hq (T + 1)]

lemma crossing_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {N : ℕ → Ω → ℕ} {T : ℕ} {c q : ℝ}
    (hc : 0 < c) (hq : 0 ≤ q) (hq1 : q < 1)
    (hmono : ∀ ω, Monotone (fun n => N n ω))
    (hbound : ∀ n ω, N n ω ≤ n)
    (htail : ∀ k ∈ Finset.Icc 1 T,
      P.real {ω | k ≤ N (cutoff T k c) ω} ≤ q ^ k) :
    P.real {ω | ∃ n, 0 < n ∧ n ≤ T ∧ c * n ≤ N n ω} ≤ q / (1 - q) := by
  let E : ℕ → Set Ω := fun j => {ω | j + 1 ≤ N (cutoff T (j + 1) c) ω}
  have hsub : {ω | ∃ n, 0 < n ∧ n ≤ T ∧ c * n ≤ N n ω} ⊆
      ⋃ j ∈ Finset.range T, E j := by
    intro ω hω
    obtain ⟨n, hn, hnT, hh⟩ := hω
    obtain ⟨k, hk, hkn, _⟩ := crossing_witness hc (hmono ω) (fun t => hbound t ω) hn hnT hh
    have hk' := Finset.mem_Icc.mp hk
    have he : k - 1 + 1 = k := by omega
    apply Set.mem_iUnion.mpr ⟨k - 1, ?_⟩
    apply Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    change k - 1 + 1 ≤ N (cutoff T (k - 1 + 1) c) ω
    rwa [he]
  calc
    _ ≤ P.real (⋃ j ∈ Finset.range T, E j) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ j ∈ Finset.range T, P.real (E j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range T, q ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact htail (j + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hj; omega⟩)
    _ ≤ _ := geometric_sum_bound hq hq1 T

lemma fixed_count_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {N : ℕ → Ω → ℕ} {n k : ℕ} {c lam : ℝ}
    (hlam : 0 ≤ lam) (hn : c * n ≤ k)
    (hi : Integrable (fun ω => Real.exp (lam * (N n ω : ℝ))) P)
    (hmgf : mgf (fun ω => (N n ω : ℝ)) P lam ≤ Real.exp (c * n)) :
    P.real {ω | k ≤ N n ω} ≤ Real.exp (1 - lam) ^ k := by
  have ht := measure_ge_le_exp_mul_mgf (X := fun ω => (N n ω : ℝ)) (k : ℝ) hlam hi
  have he : {ω | (k : ℝ) ≤ (N n ω : ℝ)} = {ω | k ≤ N n ω} := by
    ext ω
    simp
  rw [he] at ht
  calc
    _ ≤ Real.exp (-lam * k) * mgf (fun ω => (N n ω : ℝ)) P lam := ht
    _ ≤ Real.exp (-lam * k) * Real.exp (c * n) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ ≤ Real.exp (-lam * k) * Real.exp (k : ℝ) := by
      gcongr
    _ = Real.exp (1 - lam) ^ k := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring

lemma bernoulli_exp_identity {X : ℕ} (hX : X ≤ 1) (lam : ℝ) :
    Real.exp (lam * (X : ℝ)) = 1 + (Real.exp lam - 1) * (X : ℝ) := by
  interval_cases X <;> simp

lemma bernoulli_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℕ}
    (hm : Measurable (fun ω => (X ω : ℝ))) (hb : ∀ ω, X ω ≤ 1) :
    Integrable (fun ω => (X ω : ℝ)) P := by
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hb ω)

lemma bernoulli_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℕ} {p lam : ℝ}
    (hm : Measurable (fun ω => (X ω : ℝ))) (hb : ∀ ω, X ω ≤ 1)
    (hmean : (∫ ω, (X ω : ℝ) ∂P) = p) :
    mgf (fun ω => (X ω : ℝ)) P lam = 1 + (Real.exp lam - 1) * p := by
  unfold mgf
  simp_rw [bernoulli_exp_identity (hb _) lam]
  rw [integral_add (integrable_const _) ((bernoulli_integrable hm hb).const_mul _),
    integral_const_mul, hmean]
  simp

lemma bernoulli_sum_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℕ} {p lam : ℝ}
    (hm : ∀ i, Measurable (fun ω => (X i ω : ℝ)))
    (hind : iIndepFun (fun i ω => (X i ω : ℝ)) P)
    (hb : ∀ i ω, X i ω ≤ 1)
    (hmean : ∀ i, (∫ ω, (X i ω : ℝ) ∂P) = p) (n : ℕ) :
    mgf (fun ω => ((∑ i ∈ Finset.range n, X i ω : ℕ) : ℝ)) P lam =
      (1 + (Real.exp lam - 1) * p) ^ n := by
  have he : (fun ω => ((∑ i ∈ Finset.range n, X i ω : ℕ) : ℝ)) =
      ∑ i ∈ Finset.range n, (fun ω => (X i ω : ℝ)) := by
    funext ω
    simp
  rw [he, hind.mgf_sum hm]
  simp_rw [bernoulli_mgf (hm _) (hb _) (hmean _)]
  simp

lemma bernoulli_sum_exp_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℕ} (lam : ℝ)
    (hm : ∀ i, Measurable (fun ω => (X i ω : ℝ)))
    (hind : iIndepFun (fun i ω => (X i ω : ℝ)) P)
    (hb : ∀ i ω, X i ω ≤ 1) (n : ℕ) :
    Integrable (fun ω => Real.exp (lam * ((∑ i ∈ Finset.range n, X i ω : ℕ) : ℝ))) P := by
  have hi : ∀ i ∈ Finset.range n, Integrable (fun ω => Real.exp (lam * (X i ω : ℝ))) P := by
    intro i _
    simp_rw [bernoulli_exp_identity (hb i _) lam]
    exact (integrable_const _).add ((bernoulli_integrable (hm i) (hb i)).const_mul _)
  simpa using hind.integrable_exp_mul_sum hm hi

lemma iid_bernoulli_crossing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℕ} {p c lam : ℝ}
    (hm : ∀ i, Measurable (fun ω => (X i ω : ℝ)))
    (hind : iIndepFun (fun i ω => (X i ω : ℝ)) P)
    (hb : ∀ i ω, X i ω ≤ 1)
    (hmean : ∀ i, (∫ ω, (X i ω : ℝ) ∂P) = p)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hc : 0 < c) (hlam : 1 < lam)
    (hscale : p * Real.exp lam = c) (T : ℕ) :
    P.real {ω | ∃ n, 0 < n ∧ n ≤ T ∧
      c * n ≤ ((∑ i ∈ Finset.range n, X i ω : ℕ) : ℝ)} ≤
      Real.exp (1 - lam) / (1 - Real.exp (1 - lam)) := by
  let N : ℕ → Ω → ℕ := fun n ω => ∑ i ∈ Finset.range n, X i ω
  have hmono : ∀ ω, Monotone (fun n => N n ω) := by
    intro ω n m hnm
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hnm)
  have hbound : ∀ n ω, N n ω ≤ n := by
    intro n ω
    calc
      _ ≤ ∑ i ∈ Finset.range n, 1 := Finset.sum_le_sum (fun i _ => hb i ω)
      _ = n := by simp
  have hmgf : ∀ n, mgf (fun ω => (N n ω : ℝ)) P lam ≤ Real.exp (c * n) := by
    intro n
    rw [bernoulli_sum_mgf hm hind hb hmean]
    have hbase : 1 + (Real.exp lam - 1) * p ≤ Real.exp c := by
      have hex := Real.add_one_le_exp c
      nlinarith
    have hbase0 : 0 ≤ 1 + (Real.exp lam - 1) * p := by
      nlinarith [Real.exp_pos lam]
    calc
      _ ≤ (Real.exp c) ^ n := pow_le_pow_left₀ hbase0 hbase n
      _ = Real.exp (c * n) := by rw [← Real.exp_nat_mul]; congr 1; ring
  apply crossing_bound hc (Real.exp_pos _).le
    (by rw [Real.exp_lt_one_iff]; linarith) hmono hbound
  intro k hk
  have hkn : c * cutoff T k c ≤ k := by
    have hf := Nat.floor_le (show 0 ≤ (k : ℝ) / c by positivity)
    have hm' : (cutoff T k c : ℝ) ≤ (⌊(k : ℝ) / c⌋₊ : ℝ) := by
      exact_mod_cast min_le_right T ⌊(k : ℝ) / c⌋₊
    exact (mul_le_mul_of_nonneg_left (hm'.trans hf) hc.le).trans_eq (by field_simp)
  exact fixed_count_tail (by linarith) hkn
    (bernoulli_sum_exp_integrable lam hm hind hb _) (hmgf _)

lemma iid_bernoulli_crossing_log {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℕ} {p c : ℝ}
    (hm : ∀ i, Measurable (fun ω => (X i ω : ℝ)))
    (hind : iIndepFun (fun i ω => (X i ω : ℝ)) P)
    (hb : ∀ i ω, X i ω ≤ 1)
    (hmean : ∀ i, (∫ ω, (X i ω : ℝ) ∂P) = p)
    (hp : 0 < p) (hp1 : p ≤ 1) (hc : 0 < c)
    (hlog : 1 < Real.log (c / p)) (T : ℕ) :
    P.real {ω | ∃ n, 0 < n ∧ n ≤ T ∧
      c * n ≤ ((∑ i ∈ Finset.range n, X i ω : ℕ) : ℝ)} ≤
      (Real.exp 1 * p / c) / (1 - Real.exp 1 * p / c) := by
  have he : Real.exp (Real.log (c / p)) = c / p := Real.exp_log (by positivity)
  have hscale : p * Real.exp (Real.log (c / p)) = c := by rw [he]; field_simp
  have hq : Real.exp (1 - Real.log (c / p)) = Real.exp 1 * p / c := by
    rw [Real.exp_sub, he]
    field_simp
  simpa only [hq] using iid_bernoulli_crossing hm hind hb hmean hp.le hp1 hc hlog hscale T

end LongTails.Proofs.BernoulliCountCrossing
