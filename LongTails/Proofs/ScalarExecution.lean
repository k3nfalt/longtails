import LongTails.Setups.BoundedScalarConvex
import LongTails.Proofs.ScalarInterval
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.ExecutionHistory
import Mathlib.Data.List.GetD

open MeasureTheory

namespace OracleTemplate.BoundedScalarConvex

open LongTails.Setups.BoundedScalarConvex

lemma past_le (O : Oracle ℝ ℝ) (n : ℕ) :
    past O n ≤ (inferInstance : MeasurableSpace (Samples O)) := by
  unfold past
  apply iSup_le
  intro k
  exact (measurable_pi_apply (k : ℕ)).comap_le

lemma past_mono (O : Oracle ℝ ℝ) : Monotone (past O) := by
  intro n r hnr
  unfold past
  apply iSup_le
  intro k
  exact le_iSup_of_le (⟨k, lt_of_lt_of_le k.isLt hnr⟩ : Fin r) le_rfl

lemma measurable_seed_past (O : Oracle ℝ ℝ) {n k : ℕ} (hk : k < n) :
    Measurable[past O n] (fun ξ : Samples O => ξ k) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le (⟨k, hk⟩ : Fin n) le_rfl

lemma measurable_history_append {O : Oracle ℝ ℝ} {n : ℕ} {m : MeasurableSpace (Samples O)}
    (history : Samples O → HistoryAt n) (entry : Samples O → HistoryEntry)
    (hh : Measurable[m] history) (he : Measurable[m] entry) :
    Measurable[m] (fun ω =>
      (⟨(history ω).val ++ [entry ω], by simp [(history ω).property]⟩ : HistoryAt (n+1))) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (fun ω =>
      (⟨(history ω).val ++ [entry ω], by simp [(history ω).property]⟩ : HistoryAt (n+1)))
      (MeasurableSpace.comap (historyCoordinates (n+1)) inferInstance) ≤ m
  rw [MeasurableSpace.comap_comp]
  have hcoord : Measurable (fun ω => historyCoordinates (n+1)
      ⟨(history ω).val ++ [entry ω], by simp [(history ω).property]⟩) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i.val < n
    · have hcoord_i : Measurable (fun ω => historyCoordinates n (history ω) ⟨i.val, hi⟩) := by
        convert (measurable_pi_apply (⟨i.val, hi⟩ : Fin n)).comp
          ((comap_measurable (historyCoordinates n)).comp hh) using 1
        funext ω
        rfl
      have heq : (fun ω => historyCoordinates (n+1)
          ⟨(history ω).val ++ [entry ω], by simp [(history ω).property]⟩ i) =
          fun ω => historyCoordinates n (history ω) ⟨i.val, hi⟩ := by
        funext ω
        have hlt : i.val < (history ω).val.length := by simpa [(history ω).property] using hi
        simp only [historyCoordinates]
        rw [List.getD_append _ _ _ _ hlt]
      simpa only [heq] using hcoord_i
    · have hieq : i.val = n := by omega
      have hentry : Measurable entry := he
      have heq : (fun ω => historyCoordinates (n+1)
          ⟨(history ω).val ++ [entry ω], by simp [(history ω).property]⟩ i) = entry := by
        funext ω
        have hlen : (history ω).val.length ≤ i.val := by simpa [(history ω).property] using (show n ≤ i.val by omega)
        simp only [historyCoordinates]
        rw [List.getD_append_right _ _ _ _ hlen]
        have hlen_eq : (history ω).val.length = n := (history ω).property
        have hzero : i.val - (history ω).val.length = 0 := by rw [hlen_eq, hieq]; omega
        simp [hzero]
      simpa only [heq] using hentry
  exact hcoord.comap_le

lemma scalarRun_length (O : Oracle ℝ ℝ) (l u η x0 : ℝ) (n : ℕ) (ξ : Samples O) :
    (scalarRun O l u η x0 n ξ).2.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [scalarRun, ih]

lemma cast_seed_eq (O : Oracle ℝ ℝ) (ξ : Samples O) {i j : ℕ} (h : i = j) :
    cast (congrArg O.Seed h) (ξ i) = ξ j := by
  cases h
  rfl

noncomputable def scalarHistoryAt (O : Oracle ℝ ℝ) (l u η x0 : ℝ) (n : ℕ) (ξ : Samples O) : HistoryAt n :=
  ⟨scalarHistory O l u η x0 n ξ, scalarRun_length O l u η x0 n ξ⟩

lemma answerAt_scalarRun (O : Oracle ℝ ℝ) (l u η x0 : ℝ) (n : ℕ) (ξ : Samples O) :
    answerAt O n (scalarHistoryAt O l u η x0 n ξ)
      (0, scalarIterate O l u η x0 n ξ) (ξ n) =
      O.answer (scalarHistory O l u η x0 n ξ)
        (0, scalarIterate O l u η x0 n ξ)
        (ξ (scalarHistory O l u η x0 n ξ).length) := by
  unfold answerAt scalarHistoryAt scalarHistory
  have h := scalarRun_length O l u η x0 n ξ
  have hseed : cast (congrArg O.Seed h.symm) (ξ n) = ξ (scalarRun O l u η x0 n ξ).2.length := by
    exact cast_seed_eq O ξ h.symm
  rw [hseed]

lemma scalarIterate_mem (O : Oracle ℝ ℝ) {l u η x0 : ℝ} (hl : l ≤ u)
    (hx0 : x0 ∈ Set.Icc l u) (n : ℕ) (ξ : Samples O) :
    scalarIterate O l u η x0 n ξ ∈ Set.Icc l u := by
  cases n with
  | zero => exact hx0
  | succ n => exact project_mem hl _

lemma scalarRun_adapted (O : Oracle ℝ ℝ) (l u η x0 : ℝ)
    (hJoint : ∀ n, Measurable (fun z : (HistoryAt n × (Fin 1 × ℝ)) × O.Seed n =>
      answerAt O n z.1.1 z.1.2 z.2)) (n : ℕ) :
    Measurable[past O n] (scalarIterate O l u η x0 n) ∧
      Measurable[past O n] (scalarHistoryAt O l u η x0 n) := by
  induction n with
  | zero =>
    constructor
    · exact measurable_const
    · change Measurable[past O 0] (fun _ : Samples O => (⟨[], rfl⟩ : HistoryAt 0))
      exact measurable_const
  | succ n ih =>
    have hp : Measurable[past O (n+1)] (scalarIterate O l u η x0 n) :=
      ih.1.mono (past_mono O (Nat.le_succ n)) le_rfl
    have hh : Measurable[past O (n+1)] (scalarHistoryAt O l u η x0 n) :=
      ih.2.mono (past_mono O (Nat.le_succ n)) le_rfl
    have hx : Measurable[past O (n+1)] (fun ξ : Samples O => ξ n) :=
      measurable_seed_past O (Nat.lt_succ_self n)
    have hr : Measurable[past O (n+1)]
        (fun ξ => answerAt O n (scalarHistoryAt O l u η x0 n ξ)
          (0, scalarIterate O l u η x0 n ξ) (ξ n)) := by
      have hjoint := hJoint n
      let z : Samples O → ((HistoryAt n × (Fin 1 × ℝ)) × O.Seed n) := fun ξ =>
        ((scalarHistoryAt O l u η x0 n ξ, (0, scalarIterate O l u η x0 n ξ)), ξ n)
      have hz : Measurable[past O (n+1)] z := by
        convert (hh.prodMk (measurable_const.prodMk hp)).prodMk hx using 1
      exact hjoint.comp hz
    have hr' : Measurable[past O (n+1)]
        (fun ξ => O.answer (scalarHistory O l u η x0 n ξ)
          (0, scalarIterate O l u η x0 n ξ)
          (ξ (scalarHistory O l u η x0 n ξ).length)) := by
      convert hr using 1
      funext ξ
      exact (answerAt_scalarRun O l u η x0 n ξ).symm
    have hstate : Measurable[past O (n+1)] (scalarIterate O l u η x0 (n+1)) := by
      change Measurable[past O (n+1)] (fun ξ => project l u
        (scalarIterate O l u η x0 n ξ - η * O.answer _ _ _))
      exact (continuous_project l u).measurable.comp (hp.sub (hr'.const_mul η))
    have hhistory : Measurable[past O (n+1)] (scalarHistoryAt O l u η x0 (n+1)) := by
      change Measurable[past O (n+1)] (fun ξ =>
        (⟨(scalarHistoryAt O l u η x0 n ξ).val ++
          [((0, scalarIterate O l u η x0 n ξ),
            O.answer (scalarHistory O l u η x0 n ξ) (0, scalarIterate O l u η x0 n ξ)
              (ξ (scalarHistory O l u η x0 n ξ).length))], by
              exact scalarRun_length O l u η x0 (n+1) ξ⟩ : HistoryAt (n+1)))
      apply measurable_history_append
      · exact hh
      · exact ((measurable_const.prodMk hp).prodMk hr')
    exact ⟨hstate, hhistory⟩

lemma scalarIterate_measurable (O : Oracle ℝ ℝ) (l u η x0 : ℝ)
    (hJoint : ∀ n, Measurable (fun z : (HistoryAt n × (Fin 1 × ℝ)) × O.Seed n =>
      answerAt O n z.1.1 z.1.2 z.2)) (n : ℕ) :
    Measurable (scalarIterate O l u η x0 n) :=
  (scalarRun_adapted O l u η x0 hJoint n).1.mono (past_le O n) le_rfl

lemma advance_trajectory {S : Type*} (step : ℕ → S → S) (x : ℕ → S)
    (hx : ∀ n, x (n+1) = step n (x n)) (K call : ℕ) :
    StochasticGradient.advance step K call (x call) = x (call+K) := by
  induction K generalizing call with
  | zero => simp [StochasticGradient.advance]
  | succ K ih =>
    rw [StochasticGradient.advance, ← hx call, ih]
    congr 1
    omega

lemma execute_scalarSgd (O : Oracle ℝ ℝ) (l u η x0 : ℝ) (K : ℕ) (ξ : Samples O)
    : execute O (scalarSgd l u η x0) (fun _ => K)
        (by unfold scalarSgd; exact ()) ξ = scalarIterate O l u η x0 K ξ := by
  let seed : (scalarSgd l u η x0).Seed := by
    unfold scalarSgd
    exact ()
  change execute O (scalarSgd l u η x0) (fun _ => K) seed ξ = _
  rw [show execute O (scalarSgd l u η x0) (fun _ => K) seed ξ =
      (executeWithTrace O (scalarSgd l u η x0) (fun _ => K) seed ξ).1 by rfl,
    executeWithTrace_eq_executeIndexedState]
  change (executeIndexedState O (scalarSgd l u η x0) () ξ K).1 = _
  have hrun : executeIndexedState O (scalarSgd l u η x0) () ξ K =
      scalarRun O l u η x0 K ξ := by
    induction K with
    | zero => rfl
    | succ K ih =>
        simp only [executeIndexedState, scalarRun]
        rw [ih]
        simp [scalarSgd]
  rw [hrun]
  rfl

end OracleTemplate.BoundedScalarConvex
