import LongTails.Proofs.AffineSoftmaxSearch
import LongTails.Proofs.TwoSidedPLSampling

namespace LongTails.Proofs.AffineSoftmaxSearchTrace

abbrev State := ℕ × (ℝ × ℝ)

def scan (previous : ℝ) : State := (0, previous, previous)
def bracket (lower upper : ℝ) : State := (1, lower, upper)
def done (answer : ℝ) : State := (2, answer, answer)

noncomputable def step (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H index : ℕ)
    (state : State) : State :=
  if state.1 = 0 then
    if index ≤ H then
      let current := max floor (cap / 2 ^ index)
      let value := observe index current
      if 7 * r / 8 ≤ value then
        if index = 0 then done cap else bracket current state.2.1
      else if index = H then done floor else scan current
    else done floor
  else if state.1 = 1 then
    if index ≤ H then state
    else
      let mid := (state.2.1 + state.2.2) / 2
      let value := observe index mid
      if 2 * H + 8 ≤ index then done mid
      else if value < 13 * r / 16 then bracket state.2.1 mid
      else if 15 * r / 16 < value then bracket mid state.2.2
      else done mid
  else state

noncomputable def trajectory (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H : ℕ) : ℕ → State
  | 0 => scan cap
  | n + 1 => step observe r floor cap H n (trajectory observe r floor cap H n)

noncomputable def run (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H : ℕ) : ℕ → ℕ → State → State
  | 0, _, state => state
  | n + 1, index, state => run observe r floor cap H n (index + 1)
      (step observe r floor cap H index state)

lemma step_done (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H index : ℕ) (answer : ℝ) :
    step observe r floor cap H index (done answer) = done answer := by
  simp [step, done]

lemma run_done (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H n index : ℕ) (answer : ℝ) :
    run observe r floor cap H n index (done answer) = done answer := by
  induction n generalizing index with
  | zero => rfl
  | succ n ih => simpa only [run, step_done] using ih (index + 1)

lemma run_append (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H n m index : ℕ) (state : State) :
    run observe r floor cap H (n + m) index state =
      run observe r floor cap H m (index + n) (run observe r floor cap H n index state) := by
  induction n generalizing index state with
  | zero => simp only [zero_add, run, Nat.add_zero]
  | succ n ih =>
    simp only [Nat.succ_add, run]
    rw [ih]
    congr 1
    omega

lemma run_succ_end (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H n index : ℕ) (state : State) :
    run observe r floor cap H (n + 1) index state =
      step observe r floor cap H (index + n) (run observe r floor cap H n index state) := by
  simpa only [run] using run_append observe r floor cap H n 1 index state

lemma trajectory_eq_run (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H n : ℕ) :
    trajectory observe r floor cap H n = run observe r floor cap H n 0 (scan cap) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [trajectory, ih, run_succ_end, zero_add]

lemma step_observation_congr (observe other : ℕ → ℝ → ℝ) (r floor cap : ℝ)
    (H index : ℕ) (state : State) (h : ∀ x, observe index x = other index x) :
    step observe r floor cap H index state = step other r floor cap H index state := by
  unfold step
  simp only [h]

lemma trajectory_prefix (observe other : ℕ → ℝ → ℝ) (r floor cap : ℝ)
    (H n : ℕ) (h : ∀ k, k < n → ∀ x, observe k x = other k x) :
    trajectory observe r floor cap H n = trajectory other r floor cap H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [trajectory, ih (fun k hk => h k (by omega))]
    exact step_observation_congr observe other r floor cap H n _ (h n (by omega))

lemma step_range (observe : ℕ → ℝ → ℝ) (r : ℝ) {floor cap : ℝ}
    (hc : 0 ≤ cap) (hfc : floor ≤ cap) (H index : ℕ) (state : State)
    (hl : state.2.1 ∈ Set.Icc floor cap) (hu : state.2.2 ∈ Set.Icc floor cap) :
    (step observe r floor cap H index state).2.1 ∈ Set.Icc floor cap ∧
      (step observe r floor cap H index state).2.2 ∈ Set.Icc floor cap := by
  have hcurrent : max floor (cap / 2 ^ index) ∈ Set.Icc floor cap :=
    ⟨le_max_left _ _, max_le hfc (div_le_self hc (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))⟩
  have hmid : (state.2.1 + state.2.2) / 2 ∈ Set.Icc floor cap := by
    constructor <;> linarith [hl.1, hl.2, hu.1, hu.2]
  unfold step
  dsimp only
  split_ifs <;> try simp only [scan, bracket, done]
  all_goals
    first
    | exact ⟨⟨hfc, le_rfl⟩, ⟨hfc, le_rfl⟩⟩
    | exact ⟨⟨le_rfl, hfc⟩, ⟨le_rfl, hfc⟩⟩
    | exact ⟨hcurrent, hl⟩
    | exact ⟨hcurrent, hcurrent⟩
    | exact ⟨hl, hu⟩
    | exact ⟨hmid, hmid⟩
    | exact ⟨hl, hmid⟩
    | exact ⟨hmid, hu⟩

lemma trajectory_range (observe : ℕ → ℝ → ℝ) (r : ℝ) {floor cap : ℝ}
    (hc : 0 ≤ cap) (hfc : floor ≤ cap) (H n : ℕ) :
    (trajectory observe r floor cap H n).2.1 ∈ Set.Icc floor cap ∧
      (trajectory observe r floor cap H n).2.2 ∈ Set.Icc floor cap := by
  induction n with
  | zero => exact ⟨⟨hfc, le_rfl⟩, ⟨hfc, le_rfl⟩⟩
  | succ n ih => exact step_range observe r hc hfc H n _ ih.1 ih.2

lemma step_measurable {Z : Type*} [MeasurableSpace Z]
    (observe : Z → ℕ → ℝ → ℝ) (r floor cap : ℝ) (H index : ℕ)
    (state : Z → State) (hs : Measurable state)
    (ho : Measurable (fun z : Z × ℝ => observe z.1 index z.2)) :
    Measurable (fun z => step (observe z) r floor cap H index (state z)) := by
  have hgrid : Measurable (fun z => observe z index (max floor (cap / 2 ^ index))) :=
    ho.comp (measurable_id.prodMk measurable_const)
  have hmid : Measurable (fun z => ((state z).2.1 + (state z).2.2) / 2) :=
    (hs.snd.fst.add hs.snd.snd).div_const 2
  have hbisect : Measurable (fun z => observe z index (((state z).2.1 + (state z).2.2) / 2)) :=
    ho.comp (measurable_id.prodMk hmid)
  unfold step
  dsimp only
  apply Measurable.ite (measurableSet_eq_fun hs.fst measurable_const)
  · by_cases hi : index ≤ H
    · simp only [hi, ite_true]
      apply Measurable.ite (measurableSet_le measurable_const hgrid)
      · by_cases hz : index = 0
        · simp only [hz, ite_true]; exact measurable_const
        · simp only [hz, ite_false, bracket]
          exact measurable_const.prodMk (measurable_const.prodMk hs.snd.fst)
      · exact measurable_const
    · simp only [hi, ite_false]; exact measurable_const
  · apply Measurable.ite (measurableSet_eq_fun hs.fst measurable_const)
    · by_cases hi : index ≤ H
      · simpa only [hi, ite_true] using hs
      · simp only [hi, ite_false]
        by_cases hend : 2 * H + 8 ≤ index
        · simp only [hend, ite_true, done]
          exact measurable_const.prodMk (hmid.prodMk hmid)
        · simp only [hend, ite_false]
          apply Measurable.ite (measurableSet_lt hbisect measurable_const)
          · exact measurable_const.prodMk (hs.snd.fst.prodMk hmid)
          · apply Measurable.ite (measurableSet_lt measurable_const hbisect)
            · exact measurable_const.prodMk (hmid.prodMk hs.snd.snd)
            · exact measurable_const.prodMk (hmid.prodMk hmid)
    · exact hs

lemma trajectory_measurable {Z : Type*} [MeasurableSpace Z]
    (observe : Z → ℕ → ℝ → ℝ) (r floor cap : ℝ) (H n : ℕ)
    (ho : ∀ k, Measurable (fun z : Z × ℝ => observe z.1 k z.2)) :
    Measurable (fun z => trajectory (observe z) r floor cap H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact step_measurable observe r floor cap H n _ ih (ho n)

lemma seeded_trajectory_prefix {Ω : Type*} (observe : ℕ → Ω → ℝ → ℝ)
    (r floor cap : ℝ) (H n : ℕ) (seeds other : ℕ → Ω)
    (h : ∀ k, k < n → seeds k = other k) :
    trajectory (fun k => observe k (seeds k)) r floor cap H n =
      trajectory (fun k => observe k (other k)) r floor cap H n := by
  apply trajectory_prefix
  intro k hk x
  rw [h k hk]

lemma seeded_trajectory_measurable {Ω : Type*} [MeasurableSpace Ω]
    (observe : ℕ → Ω → ℝ → ℝ)
    (ho : ∀ k, Measurable (Function.uncurry (observe k))) (r floor cap : ℝ) (H n : ℕ) :
    Measurable (fun seeds : ℕ → Ω => trajectory (fun k => observe k (seeds k)) r floor cap H n) := by
  apply trajectory_measurable
  intro k
  have hp : Measurable (fun z : (ℕ → Ω) × ℝ => (z.1 k, z.2)) :=
    ((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd
  exact (ho k).comp hp

lemma run_bracket_idle (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ)
    (H n index : ℕ) (lower upper : ℝ) (h : index + n ≤ H + 1) :
    run observe r floor cap H n index (bracket lower upper) = bracket lower upper := by
  induction n generalizing index with
  | zero => rfl
  | succ n ih =>
    have hi : index ≤ H := by omega
    rw [run]
    have hs : step observe r floor cap H index (bracket lower upper) = bracket lower upper := by
      simp [step, bracket, hi]
    rw [hs]
    exact ih (index + 1) (by omega)

open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxSearch

lemma run_bisect_eq (Q R : Type*) (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r floor cap : ℝ) (H fuel index : ℕ)
    (lower upper : ℝ) (hi : H < index) (hend : index + fuel = 2 * H + 8) :
    run (fun j t => Program.eval reply (probe j t)) r floor cap H (fuel + 1) index (bracket lower upper) =
      done (Program.eval reply (bisectPlan probe r fuel index lower upper)) := by
  induction fuel generalizing index lower upper with
  | zero =>
    have hn : ¬ index ≤ H := by omega
    have hf : 2 * H + 8 ≤ index := by omega
    simp [run, step, bracket, hn, hf, bisectPlan, Program.eval_bind, Program.eval, done]
  | succ n ih =>
    have hn : ¬ index ≤ H := by omega
    have hf : ¬ 2 * H + 8 ≤ index := by omega
    rw [run]
    simp +instances only [step, bracket, show ¬ (1 : ℕ) = 0 by decide, ite_false,
      ite_true, hn, hf, bisectPlan, Program.eval_bind]
    by_cases hlo : Program.eval reply (probe index ((lower + upper) / 2)) < 13 * r / 16
    · simp +instances only [hlo, ite_true]
      exact ih (index + 1) lower ((lower + upper) / 2) (by omega) (by omega)
    · simp +instances only [hlo, ite_false]
      by_cases hhi : 15 * r / 16 < Program.eval reply (probe index ((lower + upper) / 2))
      · simp +instances only [hhi, ite_true]
        exact ih (index + 1) ((lower + upper) / 2) upper (by omega) (by omega)
      · simp +instances only [hhi, ite_false, Program.eval]
        exact run_done _ r floor cap H (n + 1) (index + 1) ((lower + upper) / 2)

lemma run_bracket_wait_bisect (Q R : Type*) (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r floor cap : ℝ) (H index : ℕ)
    (lower upper : ℝ) (hi : index ≤ H + 1) :
    run (fun j t => Program.eval reply (probe j t)) r floor cap H (2 * H + 9 - index) index
      (bracket lower upper) = done (Program.eval reply (bisectPlan probe r (H + 7) (H + 1) lower upper)) := by
  have hlength : 2 * H + 9 - index = (H + 1 - index) + (H + 8) := by omega
  rw [hlength, run_append, run_bracket_idle _ r floor cap H (H + 1 - index) index lower upper (by omega)]
  have hstart : index + (H + 1 - index) = H + 1 := by omega
  rw [hstart]
  exact run_bisect_eq Q R probe reply r floor cap H (H + 7) (H + 1) lower upper (by omega) (by omega)

lemma run_grid_eq (Q R : Type*) (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r floor cap : ℝ) (H fuel index : ℕ)
    (previous : ℝ) (hend : index + fuel = H) :
    run (fun j t => Program.eval reply (probe j t)) r floor cap H (fuel + H + 9) index (scan previous) =
      done (Program.eval reply (gridPlan probe r floor cap H fuel index previous)) := by
  induction fuel generalizing index previous with
  | zero =>
    have hi : index = H := by omega
    rw [show 0 + H + 9 = (H + 8) + 1 by omega, run]
    simp +instances only [step, scan, ite_true, hi, Nat.le_refl, gridPlan, Program.eval_bind]
    by_cases hcross : 7 * r / 8 ≤ Program.eval reply (probe H (max floor (cap / 2 ^ H)))
    · simp +instances only [hcross, ite_true]
      by_cases hz : H = 0
      · simp only [hz, ite_true, Program.eval]
        exact run_done _ r floor cap 0 8 1 cap
      · simp only [hz, ite_false]
        rw [show H + 8 = (H + 7) + 1 by omega]
        exact run_bisect_eq Q R probe reply r floor cap H (H + 7) (H + 1)
          (max floor (cap / 2 ^ H)) previous (by omega) (by omega)
    · simp +instances only [hcross, ite_false, Program.eval]
      exact run_done _ r floor cap H (H + 8) (H + 1) floor
  | succ n ih =>
    have hi : index ≤ H := by omega
    have hne : index ≠ H := by omega
    rw [show n + 1 + H + 9 = (n + H + 9) + 1 by omega, run]
    simp +instances only [step, scan, ite_true, hi, hne, ite_false, gridPlan, Program.eval_bind]
    by_cases hcross : 7 * r / 8 ≤ Program.eval reply (probe index (max floor (cap / 2 ^ index)))
    · simp +instances only [hcross, ite_true]
      by_cases hz : index = 0
      · simp only [hz, ite_true, Program.eval]
        exact run_done _ r floor cap H (n + H + 9) 1 cap
      · simp only [hz, ite_false]
        have hlength : n + H + 9 = 2 * H + 9 - (index + 1) := by omega
        rw [hlength]
        exact run_bracket_wait_bisect Q R probe reply r floor cap H (index + 1)
          (max floor (cap / 2 ^ index)) previous (by omega)
    · simp +instances only [hcross, ite_false]
      exact ih (index + 1) (max floor (cap / 2 ^ index)) (by omega)

lemma trajectory_search_eq (Q R : Type*) (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r floor cap : ℝ) (H : ℕ) :
    trajectory (fun j t => Program.eval reply (probe j t)) r floor cap H (2 * H + 9) =
      done (Program.eval reply (searchPlan probe r floor cap H)) := by
  rw [trajectory_eq_run]
  rw [show 2 * H + 9 = H + H + 9 by omega]
  exact run_grid_eq Q R probe reply r floor cap H H 0 cap (by omega)

lemma searchPlan_measurable {Q R Z : Type*} [MeasurableSpace Z]
    (probe : Z → ℕ → ℝ → Program Q R ℝ) (reply : Q → R)
    (r floor cap : ℝ) (H : ℕ)
    (hm : ∀ j, Measurable (fun z : Z × ℝ => Program.eval reply (probe z.1 j z.2))) :
    Measurable (fun z => Program.eval reply (searchPlan (probe z) r floor cap H)) := by
  have ht := trajectory_measurable (fun z j t => Program.eval reply (probe z j t))
    r floor cap H (2 * H + 9) hm
  have hs : Measurable (fun z => (trajectory
      (fun j t => Program.eval reply (probe z j t)) r floor cap H (2 * H + 9)).2.1) := ht.snd.fst
  have heq : (fun z => (trajectory
      (fun j t => Program.eval reply (probe z j t)) r floor cap H (2 * H + 9)).2.1) =
      (fun z => Program.eval reply (searchPlan (probe z) r floor cap H)) := by
    funext z
    rw [trajectory_search_eq]
    rfl
  rw [heq] at hs
  exact hs

open MeasureTheory

lemma prefix_failure_sum_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (X : ℕ → (ℕ → Ω) → S)
    (hX : ∀ k, Measurable (X k))
    (hdep : ∀ k ξ ξ', (∀ i, i < k → ξ i = ξ' i) → X k ξ = X k ξ')
    (Φ : ℕ → S → Ω → ℝ) (hΦ : ∀ k, Measurable (Function.uncurry (Φ k)))
    (hn : ∀ k x ω, 0 ≤ Φ k x ω)
    (hi : ∀ k x, Integrable (Φ k x) (Q : Measure Ω))
    {p : ℝ} (hb : ∀ k x, (∫ ω, Φ k x ω ∂(Q : Measure Ω)) ≤ p) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)))
      {ξ | 1 ≤ ∑ k ∈ Finset.range n, Φ k (X k ξ) (ξ k)} ≤ ENNReal.ofReal ((n : ℝ) * p) := by
  have hh k := OracleTemplate.TwoSidedPL.integrable_prefix_dep (Q : Measure Ω) k
    (X k) (hX k) (hdep k) (Φ k) (hΦ k) (hn k) (hi k) (hb k)
  have hsum := integrable_finsetSum (Finset.range n) (fun k _ => (hh k).1)
  have he : (∫ ξ, ∑ k ∈ Finset.range n, Φ k (X k ξ) (ξ k)
      ∂(Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)))) ≤ (n : ℝ) * p := by
    rw [integral_finsetSum _ (fun k _ => (hh k).1)]
    calc
      _ ≤ ∑ _k ∈ Finset.range n, p := Finset.sum_le_sum (fun k _ => (hh k).2)
      _ = (n : ℝ) * p := by simp
  exact (hsum.measure_le_integral
    (Filter.Eventually.of_forall (fun ξ => Finset.sum_nonneg (fun k _ => hn k (X k ξ) (ξ k))))
    (fun _ h => h)).trans (ENNReal.ofReal_le_ofReal he)

end LongTails.Proofs.AffineSoftmaxSearchTrace
