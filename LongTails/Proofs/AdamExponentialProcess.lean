import LongTails.Proofs.AdamExponentialMax

open MeasureTheory

namespace LongTails.Proofs.AdamExponentialProcess

open AdamHeavyTailedProcess AdamExponentialMax

noncomputable def nextState {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S × ℝ × ℝ) (ω : Ω) : S × ℝ × ℝ :=
  (next s.1 ω, s.2.1 * Real.exp (U s.1 ω), max s.2.2 (s.2.1 * Real.exp (U s.1 ω)))

noncomputable def trace {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ξ : ℕ → Ω) (n : ℕ) : S × ℝ × ℝ := stateAt (nextState next U) (s, 1, 1) ξ n

lemma trace_succ {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ξ : ℕ → Ω) (n : ℕ) :
    trace next U s ξ (n + 1) = nextState next U (trace next U s ξ n) (ξ n) :=
  stateAt_succ _ _ _ _

lemma trace_base {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ξ : ℕ → Ω) (n : ℕ) : (trace next U s ξ n).1 = stateAt next s ξ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [trace_succ, stateAt_succ]; exact congrArg (fun s => next s (ξ n)) ih

lemma measurable_nextState {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hU : Measurable (Function.uncurry U)) :
    Measurable (Function.uncurry (nextState next U)) := by
  have hm : Measurable (fun z : (S × ℝ × ℝ) × Ω => (z.1.1, z.2)) := by fun_prop
  have he := Real.measurable_exp.comp (hU.comp hm)
  exact (hn.comp hm).prodMk (((by fun_prop : Measurable
    (fun z : (S × ℝ × ℝ) × Ω => z.1.2.1)).mul he).prodMk
      ((by fun_prop : Measurable (fun z : (S × ℝ × ℝ) × Ω => z.1.2.2)).max
        ((by fun_prop : Measurable (fun z : (S × ℝ × ℝ) × Ω => z.1.2.1)).mul he)))

lemma measurable_trace {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hU : Measurable (Function.uncurry U))
    (s : S) (n : ℕ) : Measurable (fun ξ => trace next U s ξ n) :=
  measurable_stateAt (measurable_nextState hn hU) (s, 1, 1) n

lemma trace_bounds {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hU : ∀ s ω, U s ω ≤ B) (s : S) (ξ : ℕ → Ω) (n : ℕ) :
    0 ≤ (trace next U s ξ n).2.1 ∧ 1 ≤ (trace next U s ξ n).2.2 ∧
      (trace next U s ξ n).2.1 ≤ (trace next U s ξ n).2.2 ∧
      (trace next U s ξ n).2.2 ≤ Real.exp (n * B) := by
  induction n with
  | zero => norm_num [trace, stateAt_zero]
  | succ n ih =>
      have he : Real.exp (n * B) ≤ Real.exp ((n + 1 : ℕ) * B) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith
      have hx : (trace next U s ξ n).2.1 * Real.exp (U (trace next U s ξ n).1 (ξ n)) ≤
          Real.exp ((n + 1 : ℕ) * B) := by
        have hh := mul_le_mul (ih.2.2.1.trans ih.2.2.2) (Real.exp_le_exp.mpr (hU (trace next U s ξ n).1 (ξ n)))
          (Real.exp_pos _).le (Real.exp_pos _).le
        have heq : Real.exp (n * B) * Real.exp B = Real.exp ((n + 1 : ℕ) * B) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
        exact hh.trans_eq heq
      rw [trace_succ]
      change 0 ≤ _ ∧ 1 ≤ max _ _ ∧ _ ≤ max _ _ ∧ max _ _ ≤ _
      exact ⟨mul_nonneg ih.1 (Real.exp_pos _).le, ih.2.1.trans (le_max_left _ _),
        le_max_right _ _, max_le (ih.2.2.2.trans he) hx⟩

lemma potential_trace_bound {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hU : ∀ s ω, U s ω ≤ B) (s : S) (ξ : ℕ → Ω) (n : ℕ) :
    0 ≤ potential (trace next U s ξ n).2.1 (trace next U s ξ n).2.2 ∧
      potential (trace next U s ξ n).2.1 (trace next U s ξ n).2.2 ≤ 2 * Real.exp (n * B) := by
  have hh := trace_bounds next U hB hU s ξ n
  have hm : 0 ≤ (trace next U s ξ n).2.2 := by linarith [hh.2.1]
  have hs : 1 ≤ Real.sqrt (trace next U s ξ n).2.2 := by
    nlinarith [Real.sq_sqrt hm, Real.sqrt_nonneg (trace next U s ξ n).2.2, hh.2.1]
  have hs' : Real.sqrt (trace next U s ξ n).2.2 ≤ (trace next U s ξ n).2.2 := by
    nlinarith [Real.sq_sqrt hm, Real.sqrt_nonneg (trace next U s ξ n).2.2]
  have hd : (trace next U s ξ n).2.1 / Real.sqrt (trace next U s ξ n).2.2 ≤
      (trace next U s ξ n).2.1 := div_le_self hh.1 hs
  refine ⟨(Real.sqrt_nonneg _).trans (potential_lower hh.1), ?_⟩
  dsimp [potential]
  linarith [hh.2.2.1, hh.2.2.2]

lemma integrable_potential_trace {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hUm : Measurable (Function.uncurry U))
    {B : ℝ} (hB : 0 ≤ B) (hU : ∀ s ω, U s ω ≤ B) (s : S) (n : ℕ) :
    Integrable (fun ξ => potential (trace next U s ξ n).2.1 (trace next U s ξ n).2.2)
      (Measure.infinitePi (fun _ : ℕ => P)) := by
  have ht := measurable_trace hn hUm s n
  have hm : Measurable (fun ξ => potential (trace next U s ξ n).2.1 (trace next U s ξ n).2.2) := by
    dsimp [potential]
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (2 * Real.exp (n * B))
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (potential_trace_bound next U hB hU s ξ n).1]
  exact (potential_trace_bound next U hB hU s ξ n).2

lemma expected_potential_trace {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hUm : Measurable (Function.uncurry U))
    {B : ℝ} (hB : 0 ≤ B) (hU : ∀ s ω, U s ω ≤ B)
    (hUi : ∀ s, Integrable (fun ω => Real.exp (U s ω)) P)
    (hUe : ∀ s, (∫ ω, Real.exp (U s ω) ∂P) ≤ 1) (s : S) (ω0 : Ω) (n : ℕ) :
    (∫ ξ, potential (trace next U s ξ n).2.1 (trace next U s ξ n).2.2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 2 := by
  have hi := integrable_potential_trace P hn hUm hB hU s
  have hstep (z : S × ℝ × ℝ) (hx : 0 ≤ z.2.1) (hm : 1 ≤ z.2.2) :
      Integrable (fun ω => potential (nextState next U z ω).2.1 (nextState next U z ω).2.2) P ∧
      (∫ ω, potential (nextState next U z ω).2.1 (nextState next U z ω).2.2 ∂P) ≤
        potential z.2.1 z.2.2 := by
    have hY : Measurable (fun ω => z.2.1 * Real.exp (U z.1 ω)) :=
      (Real.measurable_exp.comp (hUm.comp measurable_prodMk_left)).const_mul _
    apply potential_expected_step P hY ((hUi z.1).const_mul _)
      (fun ω => mul_nonneg hx (Real.exp_pos _).le) (by linarith)
    rw [integral_const_mul]
    exact mul_le_of_le_one_right hx (hUe z.1)
  induction n with
  | zero => norm_num [trace, stateAt_zero, potential]
  | succ n ih =>
      let F := fun z : S × ℝ × ℝ => fun ω =>
        potential (nextState next U z ω).2.1 (nextState next U z ω).2.2
      let V := fun z : S × ℝ × ℝ => potential z.2.1 z.2.2
      have hpref (b : Fin n → Ω) :
          0 ≤ (prefixState (nextState next U) (s, 1, 1) ω0 n b).2.1 ∧
          1 ≤ (prefixState (nextState next U) (s, 1, 1) ω0 n b).2.2 := by
        have hh := trace_bounds next U hB hU s
          (fun k => if hk : k < n then b ⟨k, hk⟩ else ω0) n
        exact ⟨hh.1, hh.2.1⟩
      have hiF : Integrable (fun ξ => F (stateAt (nextState next U) (s, 1, 1) ξ n) (ξ n))
          (Measure.infinitePi (fun _ : ℕ => P)) := by
        simpa only [trace, stateAt_succ, F] using hi (n + 1)
      have hh := stateAt_sample_integral_le P (nextState next U) (s, 1, 1) ω0 n F V hiF (hi n)
        (fun b => (hstep _ (hpref b).1 (hpref b).2).1)
        (fun b => (hstep _ (hpref b).1 (hpref b).2).2)
      have hh' : (∫ ξ, potential (trace next U s ξ (n + 1)).2.1 (trace next U s ξ (n + 1)).2.2
          ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
          ∫ ξ, potential (trace next U s ξ n).2.1 (trace next U s ξ n).2.2
            ∂Measure.infinitePi (fun _ : ℕ => P) := by
        simpa only [trace, stateAt_succ, F, V] using hh
      exact hh'.trans ih

lemma expected_sqrt_max {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hUm : Measurable (Function.uncurry U))
    {B : ℝ} (hB : 0 ≤ B) (hU : ∀ s ω, U s ω ≤ B)
    (hUi : ∀ s, Integrable (fun ω => Real.exp (U s ω)) P)
    (hUe : ∀ s, (∫ ω, Real.exp (U s ω) ∂P) ≤ 1) (s : S) (ω0 : Ω) (n : ℕ) :
    Integrable (fun ξ => Real.sqrt (trace next U s ξ n).2.2) (Measure.infinitePi (fun _ : ℕ => P)) ∧
      (∫ ξ, Real.sqrt (trace next U s ξ n).2.2 ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 2 := by
  have hi := integrable_potential_trace P hn hUm hB hU s n
  have hm := (measurable_trace hn hUm s n).snd.snd
  have hb (ξ) : Real.sqrt (trace next U s ξ n).2.2 ≤
      potential (trace next U s ξ n).2.1 (trace next U s ξ n).2.2 :=
    potential_lower (trace_bounds next U hB hU s ξ n).1
  have hint := hi.mono' (Real.continuous_sqrt.measurable.comp hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => by
      simp only [Function.comp_def]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hb ξ)
  exact ⟨hint, (integral_mono hint hi hb).trans
    (expected_potential_trace P hn hUm hB hU hUi hUe s ω0 n)⟩

noncomputable def partialSum {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ξ : ℕ → Ω) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, U (stateAt next s ξ k) (ξ k)

noncomputable def partialMax {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ξ : ℕ → Ω) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (partialMax next U s ξ n) (partialSum next U s ξ (n + 1))

lemma measurable_partialSum {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hU : Measurable (Function.uncurry U))
    (s : S) (n : ℕ) : Measurable (partialSum next U s · n) := by
  apply Finset.measurable_sum
  intro k hk
  exact hU.comp ((measurable_stateAt hn s k).prodMk (measurable_pi_apply k))

lemma measurable_partialMax {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hU : Measurable (Function.uncurry U))
    (s : S) (n : ℕ) : Measurable (partialMax next U s · n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (measurable_partialSum hn hU s (n + 1))

lemma trace_exponential {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ξ : ℕ → Ω) (n : ℕ) :
    (trace next U s ξ n).2.1 = Real.exp (partialSum next U s ξ n) := by
  induction n with
  | zero => simp [trace, stateAt_zero, partialSum]
  | succ n ih =>
      rw [trace_succ]
      change (trace next U s ξ n).2.1 * Real.exp (U (trace next U s ξ n).1 (ξ n)) = _
      rw [ih, trace_base, ← Real.exp_add]
      congr 1
      simp [partialSum, Finset.sum_range_succ]

lemma partialSum_compensated {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (θ v : ℝ) (s : S) (ξ : ℕ → Ω) (n : ℕ) :
    partialSum next (fun s ω => θ * U s ω - θ ^ 2 * v) s ξ n =
      θ * partialSum next U s ξ n - θ ^ 2 * n * v := by
  simp [partialSum, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

lemma partialMax_exp_bound {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    {θ v : ℝ} (hv : 0 ≤ v) (s : S) (ξ : ℕ → Ω) (n : ℕ) :
    Real.exp (θ * partialMax next U s ξ n) ≤ Real.exp (θ ^ 2 * n * v) *
      (trace next (fun s ω => θ * U s ω - θ ^ 2 * v) s ξ n).2.2 := by
  let V := fun s ω => θ * U s ω - θ ^ 2 * v
  have hpos (k) : 0 < (trace next V s ξ k).2.1 := by
    rw [trace_exponential]
    exact Real.exp_pos _
  have hm (k) : 0 ≤ (trace next V s ξ k).2.2 := by
    induction k with
    | zero => norm_num [trace, stateAt_zero]
    | succ k ih =>
        rw [trace_succ]
        exact ih.trans (le_max_left _ _)
  induction n with
  | zero => simp [partialMax, trace, stateAt_zero]
  | succ n ih =>
      have he : Real.exp (θ ^ 2 * n * v) ≤ Real.exp (θ ^ 2 * (n + 1 : ℕ) * v) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [mul_nonneg (sq_nonneg θ) hv]
      have hleft : Real.exp (θ * partialMax next U s ξ n) ≤
          Real.exp (θ ^ 2 * (n + 1 : ℕ) * v) * (trace next V s ξ (n + 1)).2.2 := by
        apply ih.trans
        apply mul_le_mul he _ (hm n) (Real.exp_pos _).le
        rw [trace_succ]
        exact le_max_left _ _
      have hright : Real.exp (θ * partialSum next U s ξ (n + 1)) ≤
          Real.exp (θ ^ 2 * (n + 1 : ℕ) * v) * (trace next V s ξ (n + 1)).2.2 := by
        have hh : (trace next V s ξ (n + 1)).2.1 ≤ (trace next V s ξ (n + 1)).2.2 := by
          rw [trace_succ]
          exact le_max_right _ _
        have heq : Real.exp (θ * partialSum next U s ξ (n + 1)) =
            Real.exp (θ ^ 2 * (n + 1 : ℕ) * v) * (trace next V s ξ (n + 1)).2.1 := by
          rw [trace_exponential, partialSum_compensated, ← Real.exp_add]
          congr 1
          ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
      change Real.exp (θ * max _ _) ≤ _
      rcases le_total (partialMax next U s ξ n) (partialSum next U s ξ (n + 1)) with h | h
      · rw [max_eq_right h]; exact hright
      · rw [max_eq_left h]; exact hleft

lemma exponential_partialMax {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {next : S → Ω → S} {U : S → Ω → ℝ}
    (hn : Measurable (Function.uncurry next)) (hUm : Measurable (Function.uncurry U))
    {θ v : ℝ} (hv : 0 ≤ v)
    (hUi : ∀ s, Integrable (U s) P) (hU2 : ∀ s, Integrable (fun ω => (U s ω) ^ 2) P)
    (hmean : ∀ s, (∫ ω, U s ω ∂P) = 0) (hvar : ∀ s, (∫ ω, (U s ω) ^ 2 ∂P) ≤ v)
    (hbound : ∀ s ω, |θ * U s ω| ≤ 1) (s : S) (ω0 : Ω) (n : ℕ) :
    Integrable (fun ξ => Real.exp (θ / 2 * partialMax next U s ξ n))
        (Measure.infinitePi (fun _ : ℕ => P)) ∧
      (∫ ξ, Real.exp (θ / 2 * partialMax next U s ξ n) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
        2 * Real.exp (θ ^ 2 * n * v / 2) := by
  let V := fun s ω => θ * U s ω - θ ^ 2 * v
  have hVm : Measurable (Function.uncurry V) := (hUm.const_mul θ).sub_const _
  have hV (s) (ω) : V s ω ≤ 1 := by
    have hh := (abs_le.mp (hbound s ω)).2
    dsimp [V]
    nlinarith [mul_nonneg (sq_nonneg θ) hv]
  have hexp (s) := exp_centered_bound P (hUm.comp measurable_prodMk_left) (hUi s) (hU2 s)
    (hmean s) (hvar s) (hbound s)
  have hm := expected_sqrt_max P hn hVm (by norm_num : (0 : ℝ) ≤ 1) hV
    (fun s => (hexp s).1) (fun s => (hexp s).2) s ω0 n
  have hp (ξ) : Real.exp (θ / 2 * partialMax next U s ξ n) ≤
      Real.exp (θ ^ 2 * n * v / 2) * Real.sqrt (trace next V s ξ n).2.2 := by
    have hh := partialMax_exp_bound next U (θ := θ) hv s ξ n
    have hnonneg : 0 ≤ (trace next V s ξ n).2.2 :=
      (by norm_num : (0 : ℝ) ≤ 1).trans
        (trace_bounds next V (by norm_num : (0 : ℝ) ≤ 1) hV s ξ n).2.1
    have he1 : (Real.exp (θ / 2 * partialMax next U s ξ n)) ^ 2 =
        Real.exp (θ * partialMax next U s ξ n) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have he2 : (Real.exp (θ ^ 2 * n * v / 2) * Real.sqrt (trace next V s ξ n).2.2) ^ 2 =
        Real.exp (θ ^ 2 * n * v) * (trace next V s ξ n).2.2 := by
      rw [mul_pow, Real.sq_sqrt hnonneg, pow_two, ← Real.exp_add]
      congr 2
      ring
    have hright : 0 ≤ Real.exp (θ ^ 2 * n * v / 2) * Real.sqrt (trace next V s ξ n).2.2 :=
      mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
    nlinarith [Real.exp_pos (θ / 2 * partialMax next U s ξ n)]
  have hright := hm.1.const_mul (Real.exp (θ ^ 2 * n * v / 2))
  have hleft : Integrable (fun ξ => Real.exp (θ / 2 * partialMax next U s ξ n))
      (Measure.infinitePi (fun _ : ℕ => P)) := hright.mono'
    (Real.measurable_exp.comp ((measurable_partialMax hn hUm s n).const_mul _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hp ξ)
  refine ⟨hleft, (integral_mono hleft hright hp).trans ?_⟩
  rw [integral_const_mul]
  nlinarith [mul_le_mul_of_nonneg_left hm.2 (Real.exp_pos (θ ^ 2 * n * v / 2)).le]

lemma partialSum_le_partialMax {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ξ : ℕ → Ω) (n : ℕ) : partialSum next U s ξ n ≤ partialMax next U s ξ n := by
  cases n with
  | zero => simp [partialSum, partialMax]
  | succ n => exact le_max_right _ _

lemma partialMax_mono {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ξ : ℕ → Ω) {k n : ℕ} (hkn : k ≤ n) :
    partialMax next U s ξ k ≤ partialMax next U s ξ n := by
  induction n, hkn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih.trans (le_max_left _ _)

lemma partialMax_nonneg {S Ω : Type*} (next : S → Ω → S) (U : S → Ω → ℝ)
    (s : S) (ξ : ℕ → Ω) (n : ℕ) : 0 ≤ partialMax next U s ξ n :=
  partialMax_mono next U s ξ (Nat.zero_le n)

end LongTails.Proofs.AdamExponentialProcess
