import LongTails.Proofs.OptimumHeterogeneityAllocation
import LongTails.Proofs.DistributedBatchedExecution
import LongTails.Proofs.DistributedReplySimulation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.OptimumHeterogeneityExecution

open MeasureTheory DistributedTemplate LongTails.Setups.DistributedOptimumHeterogeneity
open LongTails.Algorithms.OptimumHeterogeneitySgd

variable {p : Params}

def tagged (s : Samples p) : LongTails.Setups.DistributedSmoothNonconvex.Samples (tagParams p) :=
  fun i k => (k,s i k)

noncomputable def transformed (g : LocalOracle p) (i : Fin p.n) (x : Point p) (z : ℕ × p.Ω) :=
  multiplier p i (z.1 / batch p i) • g i x z.2

lemma batch_identity (T : Time) (g : LocalOracle p) (s : Samples p) (x : Point p)
    (k : ℕ) (i : Fin p.n) :
    Algorithms.DistributedBatchedSgd.batchMean (tagParams p) (tagConfig p T) (transformed g) x k (tagged s) i =
      Algorithms.DistributedBatchedSgd.batchMean (transport p) (config p T) (scaled p g k) x k s i := by
  unfold Algorithms.DistributedBatchedSgd.batchMean
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < batch p i := Finset.mem_range.mp hj
  change multiplier p i ((k * batch p i + j) / batch p i) • _ = _
  rw [Nat.mul_comm k, Nat.mul_add_div (OptimumHeterogeneityAllocation.batch_pos p i), Nat.div_eq_of_lt hj', Nat.add_zero]
  rfl

lemma trajectory_identity (T : Time) (g : LocalOracle p) (s : Samples p) (k : ℕ) :
    Algorithms.DistributedBatchedSgd.trajectory (tagParams p) (tagConfig p T) (transformed g) (tagged s) k =
      iterate p T g s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Algorithms.DistributedBatchedSgd.trajectory, iterate, ih]
    change _ - (1 / (1 : ℝ)) • _ = _
    rw [div_one, one_smul]
    unfold Algorithms.DistributedBatchedSgd.estimate
    simp_rw [batch_identity]
    rfl

lemma executed (T : Time) (g : LocalOracle p) (P : ProbabilityMeasure (Samples p))
    (s : Samples p) (ht : Algorithms.DistributedBatchedSgd.timeBudget (tagParams p) (tagConfig p T) = T) :
    FiniteEvents (LongTails.Setups.DistributedWeakInterpolation.system p.toParams g P) (algorithm p T) T ((),s) ∧
      execute (LongTails.Setups.DistributedWeakInterpolation.system p.toParams g P) (algorithm p T) T () s = output p T g s := by
  let q := tagParams p
  let cfg := tagConfig p T
  let A := Algorithms.DistributedBatchedSgd.algorithm q cfg
  let j : Fin cfg.iterations := ⟨2 * phase p, by change 2 * phase p < 2 * phase p + 1; omega⟩
  let P' : ProbabilityMeasure (LongTails.Setups.DistributedSmoothNonconvex.Samples q) :=
    ⟨Measure.dirac (tagged s), inferInstance⟩
  have ha : (Algorithms.DistributedBatchedSgd.active q cfg).Nonempty := by
    let i : Fin p.n := 0
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, OptimumHeterogeneityAllocation.batch_pos p i⟩⟩
  have hf := DistributedBatchedExecution.finiteEvents cfg (transformed g) P' ha j (tagged s)
  have ho := DistributedBatchedExecution.execute_output cfg (transformed g) P' (tagged s) j ha
  rw [ht] at hf ho
  let tr : Fin (p.n+1) → ℕ → Point p → Point p → Point p := fun v k _ y =>
    Fin.cases 0 (fun i => multiplier p i (k / batch p i) • y) v
  have sim := DistributedReplySimulation.execution_transfer
    ⟨p.h, p.l, p.b⟩ (fun i x (r : Samples p) k => g i x (r i k)) P
    (fun i x (r : LongTails.Setups.DistributedSmoothNonconvex.Samples q) k => transformed g i x (r i k))
    P' tagged A j tr (fun _ _ _ _ => rfl) T s hf
  exact ⟨sim.1, sim.2.trans (ho.trans (trajectory_identity T g s _))⟩

end LongTails.Proofs.OptimumHeterogeneityExecution
