import LongTails.Setups.BoundedScalarConvex
import LongTails.Proofs.ScalarInterval
import LongTails.Proofs.SgdExecution

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

lemma scalarIterate_mem (O : Oracle ℝ ℝ) {l u η x0 : ℝ} (hl : l ≤ u)
    (hx0 : x0 ∈ Set.Icc l u) (n : ℕ) (ξ : Samples O) :
    scalarIterate O l u η x0 n ξ ∈ Set.Icc l u := by
  cases n with
  | zero => exact hx0
  | succ n => exact project_mem hl _

lemma scalarIterate_adapted (O : Oracle ℝ ℝ) (l u η x0 : ℝ)
    (hO : ∀ n, Measurable (Function.uncurry (fun x seed => O.answer n (0, x) seed))) (n : ℕ) :
    Measurable[past O n] (scalarIterate O l u η x0 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hp : Measurable[past O (n+1)] (scalarIterate O l u η x0 n) :=
      ih.mono (past_mono O (Nat.le_succ n)) le_rfl
    have hr : Measurable[past O (n+1)]
        (fun ξ => O.answer n (0, (scalarIterate O l u η x0 n ξ)) (ξ n)) :=
      (hO n).comp (hp.prodMk (measurable_seed_past O (Nat.lt_succ_self n)))
    exact (continuous_project l u).measurable.comp (hp.sub (hr.const_mul η))

lemma scalarIterate_measurable (O : Oracle ℝ ℝ) (l u η x0 : ℝ)
    (hO : ∀ n, Measurable (Function.uncurry (fun x seed => O.answer n (0, x) seed))) (n : ℕ) :
    Measurable (scalarIterate O l u η x0 n) :=
  (scalarIterate_adapted O l u η x0 hO n).mono (past_le O n) le_rfl

lemma advance_trajectory {S : Type*} (step : ℕ → S → S) (x : ℕ → S)
    (hx : ∀ n, x (n+1) = step n (x n)) (K call : ℕ) :
    StochasticGradient.advance step K call (x call) = x (call+K) := by
  induction K generalizing call with
  | zero => simp [StochasticGradient.advance]
  | succ K ih =>
    rw [StochasticGradient.advance, ← hx call, ih]
    congr 1
    omega

lemma execute_scalarSgd (O : Oracle ℝ ℝ) (l u η x0 : ℝ) (K : ℕ) (ξ : Samples O) :
    execute O (scalarSgd l u η x0) (fun _ => K) () ξ = scalarIterate O l u η x0 K ξ := by
  erw [StochasticGradient.execute_advance]
  change StochasticGradient.advance
    (fun n x => project l u (x-η*O.answer n (0, x) (ξ n))) K 0 x0 = _
  have h := advance_trajectory
    (fun n x => project l u (x-η*O.answer n (0, x) (ξ n)))
    (fun n => scalarIterate O l u η x0 n ξ) (fun _ => rfl) K 0
  simpa [scalarIterate] using h

end OracleTemplate.BoundedScalarConvex
