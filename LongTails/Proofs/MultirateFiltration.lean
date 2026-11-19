import LongTails.Proofs.MultirateDrift
import LongTails.Proofs.MultiscaleAggregateSampling

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MultirateFiltration

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateAllocation LongTails.Algorithms.MultirateTrajectory
open LongTails.Algorithms.MultirateCalendar
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

variable {p : Params}

local instance packetMeasurableSpace : MeasurableSpace (List Bool) := ⊤
local instance packetDiscreteSpace : DiscreteMeasurableSpace (List Bool) := ⟨fun _ => trivial⟩

lemma measurable_query (p : Params) : Measurable (queryPacket p) := by
  let f := fun z : Code p => pack p (∑ _i : Fin p.n, z)
  apply (measurable_of_countable (f := f)).comp
  exact (DashaQuantization.measurable_indices p.d false (Algorithms.MultiscaleAggregate.spacing (aggregate p))).comp
    (((measurable_id.sub_const p.x0).const_smul (aggregate p).L).prodMk (measurable_const (a := fun _ : Fin p.d => (0 : ℝ))))

lemma measurable_mean {m : MeasurableSpace (Samples p)} (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (i : Fin p.n) (a : ℕ)
    (x : Samples p → Point p) (hx : @Measurable _ _ m _ x)
    (hm : ∀ j < batch p i, @Measurable _ _ m _ (fun s : Samples p => s i (a * batch p i + j))) :
    @Measurable _ _ m _ (fun s => batchMean p g s i a (x s)) := by
  let : MeasurableSpace (Samples p) := m
  apply Measurable.fun_const_smul
  exact Finset.measurable_sum _ (fun j hj => (hg i).comp (hx.prodMk (hm j (Finset.mem_range.mp hj))))

lemma measurable_state (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (K : ℕ) (m : MeasurableSpace (Samples p))
    (hm : ∀ k < K, ∀ i, ∀ j < batch p i, @Measurable _ _ m _
      (fun s : Samples p => s i (epoch p i k * batch p i + j))) (a : ℕ) :
    @Measurable _ _ m _ (fun s => (trajectory p g s K).points a) ∧
    @Measurable _ _ m _ (fun s => (trajectory p g s K).estimates a) := by
  let : MeasurableSpace (Samples p) := m
  induction K generalizing a with
  | zero => exact ⟨measurable_const, measurable_const⟩
  | succ k ih =>
    have hprev := ih (fun t ht => hm t (Nat.lt_succ_of_lt ht))
    have hinput (i : Fin p.n) : Measurable (fun s => input p k i (trajectory p g s k)) :=
      (measurable_of_countable (f := queryPoint p)).comp ((measurable_query p).comp ((hprev _).1))
    have hmean (i : Fin p.n) := measurable_mean g hg i (epoch p i k) _ (hinput i) (hm k (by omega) i)
    have hr (i : Fin p.n) : Measurable (fun s => read p (message p g s k i (trajectory p g s k))) := by
      let f := fun z : Code p => read p (pack p z)
      apply (measurable_of_countable (f := f)).comp
      exact (DashaQuantization.measurable_indices p.d false
        (Algorithms.MultiscaleAggregate.spacing (aggregate p))).comp ((hmean i).prodMk measurable_const)
    have hv := (measurable_of_countable (f := liftCode p)).comp (Finset.measurable_sum Finset.univ (fun i _ => hr i))
    constructor
    · by_cases ha : a = k+1
      · subst a
        simp only [trajectory, advance, Function.update_self, OracleTemplate.NormalizedStorm.stormStep]
        exact (hprev k).1.sub ((measurable_const.div hv.norm).smul hv)
      · simpa only [trajectory, advance, Function.update_of_ne ha] using (hprev a).1
    · by_cases ha : a = k
      · subst a
        simp only [trajectory, advance, Function.update_self]
        exact hv
      · simpa only [trajectory, advance, Function.update_of_ne ha] using (hprev a).2

def prior (p : Params) (i : Fin p.n) (b : ℕ) : Set (Fin p.n × ℕ) :=
  {v | v.1 ≠ i ∨ v.2 < b * batch p i}

noncomputable abbrev priorSpace (p : Params) (i : Fin p.n) (a : ℕ) : MeasurableSpace (Samples p) :=
  ⨆ v ∈ prior p i a, MeasurableSpace.comap (fun s : Samples p => s v.1 v.2) p.measurableΩ

noncomputable def block (p : Params) (i : Fin p.n) (a : ℕ) (s : Samples p) (j : Fin (batch p i)) : p.Ω :=
  s i (a * batch p i + j.val)

lemma prior_coordinate {i w : Fin p.n} {a j : ℕ} (h : (w,j) ∈ prior p i a) :
    @Measurable _ _ (priorSpace p i a) _ (fun s : Samples p => s w j) :=
  Measurable.of_comap_le (le_iSup_of_le (w,j) (le_iSup_of_le h le_rfl))

lemma sample_coordinate (p : Params) (i : Fin p.n) (k : ℕ) : Measurable (fun s : Samples p => s i k) :=
  (measurable_pi_apply (X := fun _ : ℕ => p.Ω) k).comp (measurable_pi_apply (X := fun _ : Fin p.n => ℕ → p.Ω) i)

lemma prior_le (i : Fin p.n) (a : ℕ) : priorSpace p i a ≤ (inferInstance : MeasurableSpace (Samples p)) :=
  iSup_le (fun v => iSup_le (fun _ => (sample_coordinate p v.1 v.2).comap_le))

lemma block_law (P : Measure (Samples p)) (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hIID : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure p.Ω) P)
    (i : Fin p.n) (a : ℕ) :
    HasLaw (block p i a) (Measure.pi (fun _ : Fin (batch p i) => (μ i : Measure p.Ω))) P :=
  DistributedSampling.worker_batch_law (MultiscaleAggregateSampling.streamParams (aggregate p))
    ⟨1, batch p, 1, 0⟩ P μ hIID a i

lemma independent_block (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure p.Ω) P)
    (i : Fin p.n) (a : ℕ) {Y : Type*} [MeasurableSpace Y] (H : Samples p → Y)
    (hH : @Measurable _ _ (priorSpace p i a) _ H) : IndepFun H (block p i a) P := by
  let m := fun v : Fin p.n × ℕ => MeasurableSpace.comap (fun s : Samples p => s v.1 v.2) p.measurableΩ
  let V : Set (Fin p.n × ℕ) := {v | v.1 = i ∧ a * batch p i ≤ v.2}
  have hd : Disjoint (prior p i a) V := Set.disjoint_left.mpr (by
    intro v hv hw
    rcases hv with h | h
    · exact h hw.1
    · exact (not_lt_of_ge hw.2) h)
  have hm (v) : m v ≤ (inferInstance : MeasurableSpace (Samples p)) :=
    (sample_coordinate p v.1 v.2).comap_le
  have hI := DistributedSampling.independent_coordinates (MultiscaleAggregateSampling.streamParams (aggregate p))
    P μ hw hIID
  apply indep_of_indep_of_le (indep_iSup_of_disjoint hm hI hd) hH.comap_le
  apply Measurable.comap_le
  let : MeasurableSpace (Samples p) := ⨆ v ∈ V, m v
  apply Measurable.of_eval
  intro j
  exact Measurable.of_comap_le (le_iSup_of_le (i, a * batch p i + j.val)
    (le_iSup_of_le (show (i, a * batch p i + j.val) ∈ V from ⟨rfl, by omega⟩) le_rfl))

noncomputable abbrev release (p : Params) (i : Fin p.n) (k : ℕ) := epoch p i k * period p i

lemma origin_le_release (i : Fin p.n) (k : ℕ) : origin p i k ≤ release p i k :=
  Nat.mul_le_mul_right _ (Nat.sub_le _ _)

lemma prior_point (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (i : Fin p.n) (k : ℕ) {t : ℕ}
    (ht : t ≤ release p i k) :
    @Measurable _ _ (priorSpace p i (epoch p i k)) _ (fun s => MultirateDrift.point g s t) := by
  apply (measurable_state g hg t _ ?_ t).1
  intro b hb w j hj
  apply prior_coordinate
  by_cases h : w = i
  · subst w
    right
    have he : epoch p i b < epoch p i k := (Nat.div_lt_iff_lt_mul (MultirateCalendar.period_pos p i)).mpr
      (Nat.lt_of_lt_of_le hb ht)
    exact (Nat.add_lt_add_left hj _).trans_le (by simpa [Nat.succ_mul] using Nat.mul_le_mul_right (batch p i) he)
  · exact Or.inl h

noncomputable abbrev query (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ) (i : Fin p.n)
    (s : Samples p) := input p k i (trajectory p g s k)

lemma prior_query (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (i j : Fin p.n) (k : ℕ)
    (h : release p i k ≤ release p j k) :
    @Measurable _ _ (priorSpace p j (epoch p j k)) _ (query g k i) := by
  change @Measurable _ _ (priorSpace p j (epoch p j k)) _ (fun s => queryPoint p (queryPacket p ((trajectory p g s k).points (origin p i k))))
  simp only [MultirateDrift.past_point g _ (MultirateCalendar.origin_le p i k)]
  exact (measurable_of_countable (f := queryPoint p)).comp ((measurable_query p).comp
    (prior_point g hg j k ((origin_le_release i k).trans h)))

end LongTails.Proofs.MultirateFiltration
