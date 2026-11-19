import LongTails.Proofs.MultiscaleAggregateTrajectory
import LongTails.Proofs.DistributedBatchedSgd

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MultiscaleAggregateHistory

open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate
open MultiscaleAggregateTrajectory

local instance historyListMeasurableSpace {α : Type*} : MeasurableSpace (List α) := ⊤
local instance historyListDiscreteMeasurableSpace {α : Type*} : DiscreteMeasurableSpace (List α) := ⟨fun _ => trivial⟩

abbrev History (p : Params) := List (ℕ × Code p)

noncomputable def replay (p : Params) : History p → Model p
  | [] => initialModel p
  | (k, z) :: tail => advance p (replay p tail) k z

noncomputable def history (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) : ℕ → History p
  | 0 => []
  | k + 1 => (k, readPacket p k (rootMessage p g s k (point g s k))) :: history p g s k

lemma replay_history (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (k : ℕ) :
    replay p (history p g s k) = trajectory p g s k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [history, replay, trajectory, ih, point]

lemma finite_codes (p : Params) (k : ℕ) :
    (Set.range (readPacket p k)).Finite := by
  let values : (Fin p.d → Fin (2 ^ width p k)) → Code p := fun z j => (z j).val
  apply (Set.finite_range values).subset
  rintro _ ⟨b, rfl⟩
  exact ⟨_, rfl⟩

lemma finite_history (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ) :
    (Set.range fun s => history p g s k).Finite := by
  induction k with
  | zero => simpa only [history] using (Set.finite_range_const : (Set.range (fun _ : Samples p => ([] : History p))).Finite)
  | succ k ih =>
    apply (((finite_codes p k).prod ih).image (fun zh => (k, zh.1) :: zh.2)).subset
    rintro _ ⟨s, rfl⟩
    exact ⟨(readPacket p k (rootMessage p g s k (point g s k)), history p g s k),
      ⟨⟨_, rfl⟩, ⟨s, rfl⟩⟩, rfl⟩

lemma finite_trajectory_image (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (k : ℕ) {α : Type*} (φ : Model p → α) :
    (Set.range fun s => φ (trajectory p g s k)).Finite := by
  apply ((finite_history p g k).image (fun h => φ (replay p h))).subset
  rintro _ ⟨s, rfl⟩
  exact ⟨_, ⟨s, rfl⟩, congrArg φ (replay_history p g s k)⟩

lemma coordinates_measurable (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (K : ℕ)
    (m : MeasurableSpace (Samples p))
    (hm : ∀ i j, j < K * batch p i → @Measurable _ _ m _ (fun s : Samples p => s i j)) :
    @Measurable _ _ m _ (fun s => history p g s K) := by
  let : MeasurableSpace (Samples p) := m
  induction K with
  | zero => exact measurable_const
  | succ k ih =>
    have hhist := ih (fun i j h => hm i j (h.trans_le (Nat.mul_le_mul_right _ (Nat.le_succ k))))
    have hx : Measurable (fun s => point g s k) := by
      have hh := (measurable_of_countable (f := fun h : History p => (replay p h).point)).comp hhist
      simpa only [Function.comp_def, replay_history, point] using hh
    have hmean (i : Fin p.n) : Measurable (fun s => batchMean p g s k i (point g s k)) := by
      unfold batchMean
      apply Measurable.fun_const_smul
      apply Finset.measurable_sum
      intro j hj
      have ht : k * batch p i + j < (k + 1) * batch p i := by
        simpa only [Nat.add_mul, Nat.one_mul] using Nat.add_lt_add_left (Finset.mem_range.mp hj) (k * batch p i)
      exact (hg i).comp (hx.prodMk (hm i _ ht))
    have hcode (i : Fin p.n) : Measurable (fun s => localCode p (batchMean p g s k i (point g s k))) :=
      (DashaQuantization.measurable_indices p.d false (spacing p)).comp ((hmean i).prodMk measurable_const)
    let f := fun z : Fin p.n → Code p => readPacket p k (packet p k (∑ i, readPacket p k (packet p k (z i))))
    have hz := (measurable_of_countable (f := f)).comp (Measurable.of_eval hcode)
    exact (measurable_of_countable (f := fun zh : Code p × History p => (k, zh.1) :: zh.2)).comp
      (hz.prodMk hhist)

lemma measurable_trajectory_image (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) {α : Type*} [MeasurableSpace α]
    (φ : Model p → α) :
    Measurable (fun s => φ (trajectory p g s k)) := by
  have hh := coordinates_measurable p g hg k inferInstance
    (fun i j _ => (measurable_pi_apply j).comp (measurable_pi_apply i))
  simpa only [Function.comp_def, replay_history] using
    (measurable_of_countable (f := fun h => φ (replay p h))).comp hh

end LongTails.Proofs.MultiscaleAggregateHistory
