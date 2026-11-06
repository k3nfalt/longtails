import LongTails.Proofs.SparseGroupChoices
import LongTails.Proofs.SparseGroupGeometry
import LongTails.Proofs.SparseGroupEmpirical
import LongTails.Proofs.ExecutionHistory

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SparseGroupExecution

open OracleTemplate LongTails.Setups.OptimumGapGroupDro
open LongTails.Algorithms.SparseGroupSampling SparseGroupChoices

noncomputable def process (q : Public) (ξ : ℕ → Reservoir q) :
    ℕ → State q × (Fin q.K → ℕ)
  | 0 => ((fun _ => 0, fun _ _ => 0, none), fun _ => 0)
  | n + 1 =>
      let old := process q ξ n
      let i := ((algorithm q).query old.1).2
      (step q old.1 (ξ n (old.2 i) i), Function.update old.2 i (old.2 i + 1))

lemma groupCount_append (q : Public) (history : List ((Fin 1 × Fin q.K) × q.Z))
    (query : Fin 1 × Fin q.K) (reply : q.Z) :
    groupCount q (history ++ [(query, reply)]) =
      Function.update (groupCount q history) query.2 (groupCount q history query.2 + 1) := by
  classical
  funext i
  by_cases hi : i = query.2
  · subst i
    simp [groupCount, List.countP_append]
  · simp [groupCount, List.countP_append, Function.update_of_ne hi, Ne.symm hi]

lemma process_eq_indexed (q : Public) (P : ProbabilityMeasure (Reservoir q))
    (ξ : ℕ → Reservoir q) (n : ℕ) :
    process q ξ n =
      ((executeIndexedState (reservoirOracle q P) (algorithm q) () ξ n).1,
       groupCount q (executeIndexedState (reservoirOracle q P) (algorithm q) () ξ n).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [process, ih]
    simp only [executeIndexedState]
    simp only [groupCount_append, reservoirOracle, algorithm]
    rw [executeIndexedState_length]

lemma execute_eq_process (q : Public) (P : ProbabilityMeasure (Reservoir q))
    (ξ : ℕ → Reservoir q) (n : ℕ) :
    execute (reservoirOracle q P) (algorithm q) (fun _ => n) () ξ =
      output q (process q ξ n).1 := by
  unfold execute
  erw [executeWithTrace_eq_executeIndexedState]
  rw [process_eq_indexed q P]
  rfl

lemma output_feasible (q : Public) (hε : 0 < q.ε) (hG : 0 ≤ q.G)
    (hx0 : q.x0 ∈ q.domain) (hb : ∀ x ∈ q.domain, ‖x - q.x0‖ ≤ q.R)
    (s : State q) : output q s ∈ q.domain := by
  have hm := SparseGroupGeometry.primalMesh_valid q hε hG hx0 hb
  unfold output
  split
  · exact hm.2.2.1 _ (Subtype.property _)
  · exact hm.2.2.1 _ (Subtype.property _)

lemma measurable_process (q : Public) (hloss : Measurable (Function.uncurry q.loss))
    (n : ℕ) : Measurable (fun ξ : ℕ → Reservoir q => process q ξ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    let asked : State q → Fin q.K := fun s => ((algorithm q).query s).2
    have ha : Measurable asked := by
      have hc : Measurable (fun p : State q × Option (PrimalIndex q) =>
          match p.2 with | some _ => (0 : Fin q.K) | none => selectedGroup q p.1) := by
        apply measurable_from_prod_countable_left
        intro o
        cases o with
        | none => exact measurable_selectedGroup q
        | some _ => exact measurable_const
      exact hc.comp (measurable_id.prodMk (measurable_snd.comp measurable_snd))
    have hi : Measurable (fun ξ : ℕ → Reservoir q => asked (process q ξ n).1) :=
      ha.comp (measurable_fst.comp ih)
    have hcount : Measurable (fun ξ : ℕ → Reservoir q => (process q ξ n).2 (asked (process q ξ n).1)) :=
      measurable_selected_score (fun i ξ => (process q ξ n).2 i)
        (fun i => (measurable_pi_apply i).comp (measurable_snd.comp ih)) hi
    have hreply : Measurable (fun ξ : ℕ → Reservoir q =>
        ξ n ((process q ξ n).2 (asked (process q ξ n).1)) (asked (process q ξ n).1)) := by
      apply measurable_selected_score (fun i ξ => ξ n ((process q ξ n).2 (asked (process q ξ n).1)) i) _ hi
      intro i
      apply measurable_selected_score (fun k ξ => ξ n k i) _ hcount
      intro k
      fun_prop
    have hcounts : Measurable (fun ξ : ℕ → Reservoir q =>
        Function.update (process q ξ n).2 (asked (process q ξ n).1)
          ((process q ξ n).2 (asked (process q ξ n).1) + 1)) := by
      apply measurable_selected_score (fun i ξ =>
        Function.update (process q ξ n).2 i ((process q ξ n).2 i + 1)) _ hi
      intro i
      exact measurable_update'.comp ((measurable_snd.comp ih).prodMk
        (((measurable_pi_apply i).comp (measurable_snd.comp ih)).add_const 1))
    exact ((measurable_step q hloss).comp ((measurable_fst.comp ih).prodMk hreply)).prodMk hcounts

lemma step_frozen (q : Public) (s : State q) (z : q.Z) (h : PrimalIndex q)
    (hs : s.2.2 = some h) : step q s z = s := by
  simp [step, hs]

lemma step_counts (q : Public) (s : State q) (z : q.Z) (hs : s.2.2 = none) :
    (step q s z).1 = Function.update s.1 (selectedGroup q s) (s.1 (selectedGroup q s) + 1) := by
  classical
  simp only [step, hs]
  split_ifs <;> rfl

lemma step_totals (q : Public) (s : State q) (z : q.Z) (hs : s.2.2 = none) :
    (step q s z).2.1 = Function.update s.2.1 (selectedGroup q s)
      (fun h => s.2.1 (selectedGroup q s) h + q.loss h.val z) := by
  classical
  simp only [step, hs]
  split_ifs <;> rfl

lemma step_none_previous (q : Public) (s : State q) (z : q.Z)
    (hs : (step q s z).2.2 = none) : s.2.2 = none := by
  cases ho : s.2.2 with
  | none => rfl
  | some h => rw [step_frozen q s z h ho, ho] at hs; contradiction

lemma process_active_counts (q : Public) (ξ : ℕ → Reservoir q) (n : ℕ)
    (hs : (process q ξ n).1.2.2 = none) : (process q ξ n).1.1 = (process q ξ n).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : (process q ξ n).1.2.2 = none := step_none_previous q _ _ hs
    have he := ih hprev
    change (step q (process q ξ n).1 _).1 = _
    rw [step_counts q _ _ hprev, he]
    change Function.update (process q ξ n).2 (selectedGroup q (process q ξ n).1)
      ((process q ξ n).2 (selectedGroup q (process q ξ n).1) + 1) = _
    simp only [process, algorithm, hprev]

lemma sum_update_increment {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (i : ι) :
    (∑ j, Function.update c i (c i + 1) j) = (∑ j, c j) + 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have h := Finset.sum_erase_add Finset.univ c (Finset.mem_univ i)
  omega

lemma process_oracle_count_sum (q : Public) (ξ : ℕ → Reservoir q) (n : ℕ) :
    (∑ i, (process q ξ n).2 i) = n := by
  induction n with
  | zero => simp [process]
  | succ n ih =>
    change (∑ i, Function.update (process q ξ n).2 _ _ i) = n + 1
    rw [sum_update_increment, ih]

lemma process_active_count_sum (q : Public) (ξ : ℕ → Reservoir q) (n : ℕ)
    (hs : (process q ξ n).1.2.2 = none) : (∑ i, (process q ξ n).1.1 i) = n := by
  rw [process_active_counts q ξ n hs]
  exact process_oracle_count_sum q ξ n

lemma process_totals (q : Public) (ω : Reservoir q) (n : ℕ) :
    ∀ i h, (process q (fun _ => ω) n).1.2.1 i h =
      ∑ k ∈ Finset.range ((process q (fun _ => ω) n).1.1 i), q.loss h.val (ω k i) := by
  classical
  induction n with
  | zero => simp [process]
  | succ n ih =>
    let old := process q (fun _ => ω) n
    cases ho : old.1.2.2 with
    | some h =>
      have he : (process q (fun _ => ω) (n + 1)).1 = old.1 :=
        step_frozen q old.1 _ h ho
      rw [he]
      exact ih
    | none =>
      have hc : old.1.1 = old.2 := process_active_counts q _ n ho
      have hi : ((algorithm q).query old.1).2 = selectedGroup q old.1 := by
        simp [algorithm, ho]
      intro i h
      change (step q old.1 _).2.1 i h = ∑ k ∈ Finset.range ((step q old.1 _).1 i), _
      rw [step_counts q _ _ ho, step_totals q _ _ ho]
      by_cases he : i = selectedGroup q old.1
      · subst i
        simp only [Function.update_self]
        rw [Finset.sum_range_succ, ih]
        congr 1
        change q.loss h.val (ω (old.2 (((algorithm q).query old.1).2))
          (((algorithm q).query old.1).2)) = _
        rw [hi, ← hc]
      · simp only [Function.update_of_ne he]
        exact ih i h

lemma step_none_uncertified (q : Public) (s : State q) (z : q.Z)
    (hs : (step q s z).2.2 = none) : ¬ certified q (step q s z) := by
  classical
  have hprev := step_none_previous q s z hs
  simp only [step, hprev] at hs ⊢
  split_ifs at hs ⊢ with hc
  assumption

lemma initial_uncertified (q : Public) (ξ : ℕ → Reservoir q) (hε : 0 < q.ε) (hε1 : q.ε ≤ 1) :
    ¬ certified q (process q ξ 0).1 := by
  classical
  let s : State q := (fun _ => 0, fun _ _ => 0, none)
  let w := (dualChoice q s).val
  have hw := (SparseGroupGeometry.dualMesh_valid q hε).2.1 w (dualChoice q s).property
  obtain ⟨S, hcard, hsupp⟩ := hw.2.2
  intro hc
  change uncertainty q s (selectedGroup q s) ≤ q.ε / (4 * (q.d + 1 : ℝ)) at hc
  have hsum : ∑ j ∈ S, w j = 1 := by
    rw [← hw.2.1]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j _ hj
    exact hsupp j hj
  have hmax (j : Fin q.K) : w j ≤ q.ε / (4 * (q.d + 1 : ℝ)) := by
    have h := (le_finiteMaximizer (uncertainty q s) j).trans hc
    simpa only [uncertainty, radius, s, ite_true, mul_one] using h
  have hbound := Finset.sum_le_sum (s := S) (fun j _ => hmax j)
  rw [hsum] at hbound
  simp only [Finset.sum_const, nsmul_eq_mul] at hbound
  have hcard' : (S.card : ℝ) ≤ q.d + 1 := by exact_mod_cast hcard
  have hspos : (0 : ℝ) < q.d + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcard'
    (div_nonneg hε.le (by positivity : 0 ≤ 4 * (q.d + 1 : ℝ)))
  have he : (q.d + 1 : ℝ) * (q.ε / (4 * (q.d + 1 : ℝ))) = q.ε / 4 := by field_simp
  rw [he] at hmul
  linarith

lemma process_frozen_correct (q : Public) (ξ : ℕ → Reservoir q) (n : ℕ) :
    ∀ h, (process q ξ n).1.2.2 = some h →
      certified q (process q ξ n).1 ∧ h = primalChoice q (process q ξ n).1 := by
  classical
  induction n with
  | zero => simp [process]
  | succ n ih =>
    let old := process q ξ n
    cases ho : old.1.2.2 with
    | some h =>
      have he : (process q ξ (n + 1)).1 = old.1 := step_frozen q old.1 _ h ho
      rw [he]
      exact ih
    | none =>
      intro h
      let z := ξ n (old.2 (((algorithm q).query old.1).2)) (((algorithm q).query old.1).2)
      change (step q old.1 z).2.2 = some h →
        certified q (step q old.1 z) ∧ h = primalChoice q (step q old.1 z)
      simp only [step, ho]
      split_ifs with hc
      · intro he
        have hh := Option.some.inj he
        subst h
        exact ⟨hc, rfl⟩
      · intro he
        contradiction

lemma process_output_primal (q : Public) (ξ : ℕ → Reservoir q) (n : ℕ) :
    output q (process q ξ n).1 = (primalChoice q (process q ξ n).1).val := by
  cases ho : (process q ξ n).1.2.2 with
  | none => simp only [output, ho]
  | some h =>
    simp only [output, ho]
    exact congrArg Subtype.val (process_frozen_correct q ξ n h ho).2

lemma process_none_uncertified (q : Public) (ξ : ℕ → Reservoir q) (n : ℕ)
    (hε : 0 < q.ε) (hε1 : q.ε ≤ 1) (hn : (process q ξ n).1.2.2 = none) :
    ¬ certified q (process q ξ n).1 := by
  cases n with
  | zero => exact initial_uncertified q ξ hε hε1
  | succ n => exact step_none_uncertified q (process q ξ n).1 _ hn

lemma process_state_count_sum_le (q : Public) (ξ : ℕ → Reservoir q) (n : ℕ) :
    (∑ i, (process q ξ n).1.1 i) ≤ n := by
  induction n with
  | zero => simp [process]
  | succ n ih =>
    let old := process q ξ n
    cases ho : old.1.2.2 with
    | some h =>
      have he : (process q ξ (n + 1)).1 = old.1 := step_frozen q old.1 _ h ho
      rw [he]
      exact ih.trans (Nat.le_succ n)
    | none =>
      change (∑ i, (step q old.1 _).1 i) ≤ n + 1
      rw [step_counts q _ _ ho, sum_update_increment]
      exact Nat.add_le_add_right ih 1

lemma process_count_le_clock (q : Public) (ξ : ℕ → Reservoir q) (n : ℕ) (i : Fin q.K) :
    (process q ξ n).1.1 i ≤ n :=
  (Finset.single_le_sum (fun j _ => Nat.zero_le ((process q ξ n).1.1 j))
    (Finset.mem_univ i)).trans (process_state_count_sum_le q ξ n)

lemma process_count_caps (q : Public) (ξ : ℕ → Reservoir q) (M : Fin q.K → ℝ)
    (hM : ∀ i, 0 ≤ M i) (n : ℕ)
    (hcap : ∀ k < n, (process q ξ k).1.2.2 = none →
      ((process q ξ k).1.1 (selectedGroup q (process q ξ k).1) : ℝ) ≤
        M (selectedGroup q (process q ξ k).1)) :
    ∀ i, ((process q ξ n).1.1 i : ℝ) ≤ M i + 1 := by
  induction n with
  | zero => intro i; simp only [process, Nat.cast_zero]; linarith [hM i]
  | succ n ih =>
    have hprev := ih (fun k hk => hcap k (by omega))
    let old := process q ξ n
    cases ho : old.1.2.2 with
    | some h =>
      have he : (process q ξ (n + 1)).1 = old.1 := step_frozen q old.1 _ h ho
      rw [he]
      exact hprev
    | none =>
      have hc := hcap n (by omega) ho
      intro i
      change ((step q old.1 _).1 i : ℝ) ≤ _
      rw [step_counts q _ _ ho]
      by_cases hi : i = selectedGroup q old.1
      · subst i
        simp only [Function.update_self, Nat.cast_add, Nat.cast_one]
        change (old.1.1 (selectedGroup q old.1) : ℝ) ≤ M (selectedGroup q old.1) at hc
        linarith
      · rw [Function.update_of_ne hi]
        exact hprev i

lemma process_certified_of_budget (q : Public) (ξ : ℕ → Reservoir q)
    (M : Fin q.K → ℝ) (hM : ∀ i, 0 ≤ M i) (n : ℕ)
    (hcap : ∀ k < n, (process q ξ k).1.2.2 = none →
      ((process q ξ k).1.1 (selectedGroup q (process q ξ k).1) : ℝ) ≤
        M (selectedGroup q (process q ξ k).1))
    (hn : (∑ i, (M i + 1)) < n) : certified q (process q ξ n).1 := by
  have hcaps := process_count_caps q ξ M hM n hcap
  cases ho : (process q ξ n).1.2.2 with
  | some h => exact (process_frozen_correct q ξ n h ho).1
  | none =>
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcaps i)
    have he := process_active_count_sum q ξ n ho
    have he' : (∑ i, ((process q ξ n).1.1 i : ℝ)) = n := by exact_mod_cast he
    rw [he'] at hsum
    linarith

end LongTails.Proofs.SparseGroupExecution
