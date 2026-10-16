import LongTails.Proofs.ScalarMomentConcentration
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.AdaptiveOracleConcentration

lemma iid_history_independent {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) (n : ℕ) :
    IndepFun (fun ω (i : Fin n) => ξ i ω) (ξ n) P := by
  have hdis : Disjoint (Finset.range n) {n} := by simp
  have hh := hind.indepFun_finset (Finset.range n) {n} hdis hξ
  have hleft : Measurable (fun z : (i : ↥(Finset.range n)) → Z =>
      fun i : Fin n => z ⟨i, Finset.mem_range.mpr i.isLt⟩) := by fun_prop
  have hright : Measurable (fun z : (i : ↥({n} : Finset ℕ)) → Z => z ⟨n, by simp⟩) := by fun_prop
  exact hh.comp hleft hright

lemma independent_nonnegative_fiber_bound {Ω A Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {history : Ω → A} {sample : Ω → Z} {p : Measure Z} [IsProbabilityMeasure p]
    (hH : Measurable history) (hS : Measurable sample)
    (hind : IndepFun history sample P) (hlaw : P.map sample = p)
    {f : A × Z → ℝ} {bound : A → ℝ}
    (hf : Measurable f) (hn : ∀ z, 0 ≤ f z)
    (hfi : ∀ a, Integrable (fun z => f (a, z)) p)
    (hb : Integrable bound (P.map history))
    (hbound : ∀ a, (∫ z, f (a, z) ∂p) ≤ bound a) :
    Integrable (fun ω => f (history ω, sample ω)) P ∧
      (∫ ω, f (history ω, sample ω) ∂P) ≤ ∫ a, bound a ∂P.map history := by
  have heq : P.map (fun ω => (history ω, sample ω)) = (P.map history).prod p := by
    rw [hind.map_prod_eq_prod_map_map hH.aemeasurable hS.aemeasurable, hlaw]
  have hi := WeakGradientConvolution.nonnegative_fiber_integral_bound
    hf.stronglyMeasurable hn (Filter.Eventually.of_forall hfi) hb (Filter.Eventually.of_forall hbound)
  have hmap : Measurable (fun ω => (history ω, sample ω)) := hH.prodMk hS
  have him : Integrable f (P.map (fun ω => (history ω, sample ω))) := by
    rw [heq]
    exact hi.1
  refine ⟨him.comp_measurable hmap, ?_⟩
  rw [← integral_map hmap.aemeasurable hf.aestronglyMeasurable, heq]
  exact hi.2

lemma independent_exponential_step {Ω A Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {history : Ω → A} {sample : Ω → Z} {p : Measure Z} [IsProbabilityMeasure p]
    (hH : Measurable history) (hS : Measurable sample)
    (hind : IndepFun history sample P) (hlaw : P.map sample = p)
    {increment : A × Z → ℝ} {weight : A → ℝ} {c : ℝ}
    (hinc : Measurable increment) (hw : Measurable weight)
    (hwn : ∀ a, 0 ≤ weight a) (hwi : Integrable weight (P.map history))
    (hei : ∀ a, Integrable (fun z => Real.exp (increment (a, z))) p)
    (heb : ∀ a, (∫ z, Real.exp (increment (a, z)) ∂p) ≤ Real.exp c) :
    Integrable (fun ω => weight (history ω) * Real.exp (increment (history ω, sample ω))) P ∧
      (∫ ω, weight (history ω) * Real.exp (increment (history ω, sample ω)) ∂P) ≤
        Real.exp c * (∫ a, weight a ∂P.map history) := by
  have hm : Measurable (fun az : A × Z => weight az.1 * Real.exp (increment az)) :=
    (hw.comp measurable_fst).mul hinc.exp
  have hh := independent_nonnegative_fiber_bound hH hS hind hlaw hm
    (fun az => mul_nonneg (hwn az.1) (Real.exp_pos _).le)
    (fun a => (hei a).const_mul (weight a)) (hwi.mul_const (Real.exp c))
    (fun a => by
      dsimp only
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (heb a) (hwn a))
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  rw [integral_mul_const, mul_comm]


lemma iid_exponential_recursion {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    {state : (n : ℕ) → (Fin n → Z) → ℝ}
    {increment : (n : ℕ) → (Fin n → Z) × Z → ℝ} {c : ℝ}
    (hstate : ∀ n, Measurable (state n)) (hinc : ∀ n, Measurable (increment n))
    (hzero : ∀ ω, state 0 (fun i => ξ i ω) = 0)
    (hstep : ∀ n ω, state (n + 1) (fun i => ξ i ω) =
      state n (fun i => ξ i ω) + increment n ((fun i => ξ i ω), ξ n ω))
    (hei : ∀ n a, Integrable (fun z => Real.exp (increment n (a, z))) p)
    (heb : ∀ n a, (∫ z, Real.exp (increment n (a, z)) ∂p) ≤ Real.exp c)
    (n : ℕ) :
    Integrable (fun ω => Real.exp (state n (fun i => ξ i ω))) P ∧
      (∫ ω, Real.exp (state n (fun i => ξ i ω)) ∂P) ≤ Real.exp ((n : ℝ) * c) := by
  induction n with
  | zero =>
    simp only [hzero, Real.exp_zero, Nat.cast_zero, zero_mul]
    exact ⟨integrable_const 1, by simp⟩
  | succ n ih =>
    have hh : Measurable (fun ω (i : Fin n) => ξ i ω) := by fun_prop
    have hweight : Integrable (fun a => Real.exp (state n a))
        (P.map (fun ω (i : Fin n) => ξ i ω)) := by
      exact (integrable_map_measure (hstate n).exp.aestronglyMeasurable hh.aemeasurable).mpr ih.1
    have he := independent_exponential_step hh (hξ n)
      (iid_history_independent hξ hind n) (hlaw n) (hinc n) (hstate n).exp
      (fun a => (Real.exp_pos _).le) hweight (hei n) (heb n)
    have heq : (fun ω => Real.exp (state (n + 1) (fun i => ξ i ω))) =
        fun ω => Real.exp (state n (fun i => ξ i ω)) *
          Real.exp (increment n ((fun i => ξ i ω), ξ n ω)) := by
      funext ω
      rw [hstep, Real.exp_add]
    rw [heq]
    refine ⟨he.1, he.2.trans ?_⟩
    rw [integral_map hh.aemeasurable (hstate n).exp.aestronglyMeasurable]
    calc
      Real.exp c * (∫ ω, Real.exp (state n (fun i => ξ i ω)) ∂P) ≤
          Real.exp c * Real.exp ((n : ℝ) * c) :=
        mul_le_mul_of_nonneg_left ih.2 (Real.exp_pos _).le
      _ = Real.exp ((↑(n + 1) : ℝ) * c) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring


lemma iid_additive_exponential_bound {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    {state : (n : ℕ) → (Fin n → Z) → ℝ}
    {increment : (n : ℕ) → (Fin n → Z) × Z → ℝ} (cost : ℕ → ℝ) (θ : ℝ)
    (hstate : ∀ n, Measurable (state n)) (hinc : ∀ n, Measurable (increment n))
    (hzero : ∀ ω, state 0 (fun i => ξ i ω) = 0)
    (hstep : ∀ n ω, state (n + 1) (fun i => ξ i ω) =
      state n (fun i => ξ i ω) + increment n ((fun i => ξ i ω), ξ n ω))
    (hei : ∀ n a, Integrable (fun z => Real.exp (θ * increment n (a, z))) p)
    (heb : ∀ n a, (∫ z, Real.exp (θ * increment n (a, z)) ∂p) ≤ Real.exp (cost n))
    (n : ℕ) :
    Integrable (fun ω => Real.exp (θ * state n (fun i => ξ i ω))) P ∧
      (∫ ω, Real.exp (θ * state n (fun i => ξ i ω)) ∂P) ≤
        Real.exp (∑ i ∈ Finset.range n, cost i) := by
  let S := fun n a => θ * state n a - ∑ i ∈ Finset.range n, cost i
  let I := fun n az => θ * increment n az - cost n
  have hs : ∀ n, Measurable (S n) := fun n => ((hstate n).const_mul θ).sub_const _
  have hi : ∀ n, Measurable (I n) := fun n => ((hinc n).const_mul θ).sub_const _
  have hz : ∀ ω, S 0 (fun i => ξ i ω) = 0 := by intro ω; simp [S, hzero]
  have hrec : ∀ n ω, S (n + 1) (fun i => ξ i ω) =
      S n (fun i => ξ i ω) + I n ((fun i => ξ i ω), ξ n ω) := by
    intro n ω
    dsimp [S, I]
    rw [hstep, Finset.sum_range_succ]
    ring
  have heq (n : ℕ) (a : Fin n → Z) : (fun z => Real.exp (I n (a, z))) =
      fun z => Real.exp (θ * increment n (a, z)) * Real.exp (-cost n) := by
    funext z
    simp only [I, sub_eq_add_neg, Real.exp_add]
  have hEi : ∀ n a, Integrable (fun z => Real.exp (I n (a, z))) p := by
    intro n a
    rw [heq]
    exact (hei n a).mul_const _
  have hEb : ∀ n a, (∫ z, Real.exp (I n (a, z)) ∂p) ≤ Real.exp 0 := by
    intro n a
    rw [heq, integral_mul_const]
    calc
      (∫ z, Real.exp (θ * increment n (a, z)) ∂p) * Real.exp (-cost n) ≤
          Real.exp (cost n) * Real.exp (-cost n) :=
        mul_le_mul_of_nonneg_right (heb n a) (Real.exp_pos _).le
      _ = Real.exp 0 := by rw [← Real.exp_add]; simp
  have hh := iid_exponential_recursion hξ hind hlaw hs hi hz hrec hEi hEb n
  have hout : (fun ω => Real.exp (θ * state n (fun i => ξ i ω))) =
      fun ω => Real.exp (S n (fun i => ξ i ω)) * Real.exp (∑ i ∈ Finset.range n, cost i) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    dsimp [S]
    ring
  rw [hout]
  refine ⟨hh.1.mul_const _, ?_⟩
  rw [integral_mul_const]
  simpa only [mul_zero, Real.exp_zero, one_mul] using
    mul_le_mul_of_nonneg_right hh.2 (Real.exp_pos (∑ i ∈ Finset.range n, cost i)).le


noncomputable def historySum {Z : Type*}
    (increment : (n : ℕ) → (Fin n → Z) × Z → ℝ) : (n : ℕ) → (Fin n → Z) → ℝ
  | 0, _ => 0
  | n + 1, a => historySum increment n (Fin.init a) + increment n (Fin.init a, a (Fin.last n))

lemma history_sum_measurable {Z : Type*} [MeasurableSpace Z]
    {increment : (n : ℕ) → (Fin n → Z) × Z → ℝ}
    (hi : ∀ n, Measurable (increment n)) (n : ℕ) : Measurable (historySum increment n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hinit : Measurable (Fin.init : (Fin (n + 1) → Z) → Fin n → Z) := by
      apply Measurable.of_eval
      intro i
      exact measurable_pi_apply i.castSucc
    exact (ih.comp hinit).add ((hi n).comp (hinit.prodMk (measurable_pi_apply (Fin.last n))))

lemma history_sum_eq {Ω Z : Type*} (ξ : ℕ → Ω → Z)
    (increment : (n : ℕ) → (Fin n → Z) × Z → ℝ) (n : ℕ) (ω : Ω) :
    historySum increment n (fun i => ξ i ω) =
      ∑ i ∈ Finset.range n, increment i ((fun j => ξ j ω), ξ i ω) := by
  induction n with
  | zero => simp [historySum]
  | succ n ih =>
    simp only [historySum, Fin.init_def, Fin.val_castSucc, Fin.val_last, ih, Finset.sum_range_succ]

lemma iid_predictable_sum_exponential_bound {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    {increment : (n : ℕ) → (Fin n → Z) × Z → ℝ} (cost : ℕ → ℝ) (θ : ℝ)
    (hinc : ∀ n, Measurable (increment n))
    (hei : ∀ n a, Integrable (fun z => Real.exp (θ * increment n (a, z))) p)
    (heb : ∀ n a, (∫ z, Real.exp (θ * increment n (a, z)) ∂p) ≤ Real.exp (cost n))
    (n : ℕ) :
    Integrable (fun ω => Real.exp (θ * ∑ i ∈ Finset.range n,
      increment i ((fun j => ξ j ω), ξ i ω))) P ∧
      (∫ ω, Real.exp (θ * ∑ i ∈ Finset.range n,
        increment i ((fun j => ξ j ω), ξ i ω)) ∂P) ≤ Real.exp (∑ i ∈ Finset.range n, cost i) := by
  have hzero : ∀ ω, historySum increment 0 (fun i => ξ i ω) = 0 := fun _ => rfl
  have hstep : ∀ n ω, historySum increment (n + 1) (fun i => ξ i ω) =
      historySum increment n (fun i => ξ i ω) + increment n ((fun i => ξ i ω), ξ n ω) := by
    intro n ω
    simp only [historySum, Fin.init_def, Fin.val_castSucc, Fin.val_last]
  have hh := iid_additive_exponential_bound hξ hind hlaw cost θ
    (history_sum_measurable hinc) hinc hzero hstep hei heb n
  simpa only [history_sum_eq] using hh

end LongTails.Proofs.AdaptiveOracleConcentration
