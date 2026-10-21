import LongTailsOnline.Proofs.TaskAllocationConfidence
import LongTailsOnline.Proofs.TaskAllocationExecution

open MeasureTheory ProbabilityTheory

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

def ValidIntervals {k : ℕ} (μ : Worker k → ℝ) (ci : Intervals k) : Prop :=
  ∀ i, 0 ≤ ci.1 i ∧ ci.1 i ≤ μ i ∧ μ i ≤ ci.2 i ∧ ci.2 i ≤ 1

lemma start_intervals (p : Public) (s : Statistics p.k) (ci : Intervals p.k) (h : ℕ) :
    (start p s ci h).2.1 = ci := by
  unfold start
  split_ifs <;> rfl

lemma prepare_interval_cases (p : Public) (s : State p) :
    (prepare p s).2.1 = s.2.1 ∨
      (prepare p s).2.1 = refineIntervals p s.1 s.2.1 := by
  unfold prepare
  split_ifs <;> (try dsimp only)
  all_goals (try split_ifs) <;> simp only [start_intervals, true_or, or_true]

lemma refine_intervals_valid {p : Params} {w : Sample p.config.k}
    (hB : 0 < p.config.B) (hT : 0 < p.config.T) (hw : w ∉ confidenceFailure p)
    (s : Statistics p.config.k) (ci : Intervals p.config.k) (hci : ValidIntervals p.μ ci)
    (hcounts : ∀ i, s.1 i ≤ p.config.B * p.config.T)
    (hstats : ∀ i, s.2 i / s.1 i = empirical (clipLevel p.config) w i (s.1 i)) :
    ValidIntervals p.μ (refineIntervals p.config s ci) := by
  intro i
  by_cases hzero : s.1 i = 0
  · simpa only [refineIntervals, hzero, ite_true] using hci i
  · have hN : 0 < s.1 i := Nat.pos_of_ne_zero hzero
    have hc := (prefix_confident hw i hN (hcounts i)).trans
      (radius_mono (hci i).2.2.1 (s.1 i) hB hT)
    rw [← hstats i] at hc
    have hcenter := abs_le.mp hc
    have hμ0 : 0 ≤ p.μ i := (hci i).1.trans (hci i).2.1
    have hμ1 : p.μ i ≤ 1 := (hci i).2.2.1.trans (hci i).2.2.2
    simp only [refineIntervals, hzero, ite_false]
    refine ⟨(le_max_left 0 _).trans (le_max_right _ _), ?_, ?_, ?_⟩
    · exact max_le (hci i).2.1 (max_le hμ0 (by linarith [hcenter.2]))
    · exact le_min (hci i).2.2.1 (le_min hμ1 (by linarith [hcenter.1]))
    · exact (min_le_right _ _).trans (min_le_left _ _)

lemma prepare_intervals_valid {p : Params} {w : Sample p.config.k}
    (hB : 0 < p.config.B) (hT : 0 < p.config.T) (hw : w ∉ confidenceFailure p)
    (s : State p.config) (hci : ValidIntervals p.μ s.2.1)
    (hcounts : ∀ i, s.1.1 i ≤ p.config.B * p.config.T)
    (hstats : ∀ i, s.1.2 i / s.1.1 i = empirical (clipLevel p.config) w i (s.1.1 i)) :
    ValidIntervals p.μ (prepare p.config s).2.1 := by
  rcases prepare_interval_cases p.config s with hsame | hrefined
  · exact hsame.symm ▸ hci
  · rw [hrefined]
    exact refine_intervals_valid hB hT hw s.1 s.2.1 hci hcounts hstats

lemma trajectory_intervals_valid {p : Params} {w : Sample p.config.k}
    (hB : 0 < p.config.B) (hT : 0 < p.config.T)
    (hμ : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1) (hw : w ∉ confidenceFailure p)
    {t : ℕ} (ht : t ≤ p.config.T) :
    ValidIntervals p.μ (trajectory p.config w t).2.1 := by
  induction t with
  | zero =>
    intro i
    exact ⟨le_rfl, (hμ i).1, (hμ i).2, le_rfl⟩
  | succ t ih =>
    have hprev := ih (by omega)
    have hc (i) : (trajectory p.config w t).1.1 i ≤ p.config.B * p.config.T := by
      calc
        _ ≤ t * p.config.B := counts_le p.config w t i
        _ ≤ p.config.T * p.config.B := Nat.mul_le_mul_right _ (by omega)
        _ = _ := Nat.mul_comm _ _
    have hprepared := prepare_intervals_valid hB hT hw (trajectory p.config w t)
      hprev hc (statistics_empirical p.config w t)
    exact hprepared

lemma prepared_intervals_valid {p : Params} {w : Sample p.config.k}
    (hB : 0 < p.config.B) (hT : 0 < p.config.T)
    (hμ : ∀ i, p.μ i ∈ Set.Icc (0 : ℝ) 1) (hw : w ∉ confidenceFailure p)
    {t : ℕ} (ht : t ≤ p.config.T) :
    ValidIntervals p.μ (prepare p.config (trajectory p.config w t)).2.1 := by
  apply prepare_intervals_valid hB hT hw (trajectory p.config w t)
    (trajectory_intervals_valid hB hT hμ hw ht)
  · intro i
    calc
      _ ≤ t * p.config.B := counts_le p.config w t i
      _ ≤ p.config.T * p.config.B := Nat.mul_le_mul_right _ ht
      _ = _ := Nat.mul_comm _ _
  · exact statistics_empirical p.config w t

end LongTailsOnline.Proofs.TaskAllocation
