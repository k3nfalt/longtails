import LongTails.Proofs.BirchResourceHardRun

namespace LongTails.Proofs.BirchResourceHardLower

open Finset MeasureTheory Set
open LongTails.Proofs.BirchResourceHardRun
open LongTails.Proofs.BirchResourceAdaptiveLower
open LongTails.Proofs.BirchResourceLowerWindow
open LongTails.Proofs.BirchResourceLower
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

noncomputable def delay {Packet : Type*} (run : Scheduler Packet) (N m : ℕ) (ℓ : ℝ)
    (ξ : ℕ → Bool) : ℝ :=
  if m + 1 ≤ level run ξ N then reachTime run ξ N (m + 1) - reachTime run ξ N m else ℓ + 1

noncomputable def cost {Packet : Type*} (run : Scheduler Packet) (N m : ℕ)
    (size : Packet → ℕ) (ξ : ℕ → Bool) : ℝ :=
  ((reachSlot run ξ N (m + 1)).map (fun s => size s.packet)).getD 0

lemma delay_nonneg {Packet : Type*} {run : Scheduler Packet} {N : ℕ}
    (hc : Causal run N) (m : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (ξ : ℕ → Bool) :
    0 ≤ delay run N m ℓ ξ := by
  unfold delay
  split
  · exact sub_nonneg.mpr (reach_ordered hc ξ (Nat.le_succ _) ‹_›)
  · positivity

lemma delay_measurable {Packet : Type*} (run : Scheduler Packet) (N m : ℕ) (ℓ : ℝ) :
    Measurable (delay run N m ℓ) := by
  have hm (k : ℕ) : Measurable (fun ξ => reachTime run ξ N k) :=
    reach_observable run N k (fun z => (z.map Slot.finish).getD 0)
  exact ((hm (m + 1)).sub (hm m)).ite
    (measurableSet_le measurable_const (level_measurable run N)) measurable_const

lemma cost_measurable {Packet : Type*} (run : Scheduler Packet) (N m : ℕ) (size : Packet → ℕ) :
    Measurable (cost run N m size) := by
  unfold cost
  exact reach_observable (X := ℝ) run N (m + 1)
    (fun z : Option (Slot Packet) => (((z.map (fun s => size s.packet)).getD 0 : ℕ) : ℝ))

lemma observed_cost {Packet : Type*} {run : Scheduler Packet} {N m : ℕ} (ξ : ℕ → Bool)
    (size : Packet → ℕ) (hr : m + 1 ≤ level run ξ N) (s : Slot Packet)
    (hs : observed run ξ (witness run ξ N (m + 1) (Nat.succ_pos _) hr) = some s) :
    cost run N m size ξ = size s.packet := by
  unfold cost reachSlot
  rw [dite_eq_left (And.intro (Nat.succ_pos _) hr), hs]
  rfl

lemma sum_delay {Packet : Type*} (run : Scheduler Packet) (N D : ℕ) (ℓ : ℝ)
    (ξ : ℕ → Bool) (hr : D ≤ level run ξ N) :
    ∑ i : Fin D, delay run N i ℓ ξ = reachTime run ξ N D := by
  rw [Fin.sum_univ_eq_sum_range (fun i => delay run N i ℓ ξ)]
  induction D with
  | zero => simp [reachTime_zero]
  | succ D ih =>
    rw [sum_range_succ, ih ((Nat.le_succ _).trans hr), delay, ite_eq_left hr]
    ring

lemma sum_cost_le {Packet : Type*} [DecidableEq Packet] {run : Scheduler Packet} {N D : ℕ}
    (hc : Causal run N) (size : Packet → ℕ) (launched : Finset Packet)
    (ξ : ℕ → Bool) (hr : D ≤ level run ξ N)
    (hlaunch : ∀ n < N, ∀ s, observed run ξ n = some s → s.packet ∈ launched) :
    ∑ i : Fin D, cost run N i size ξ ≤ ∑ p ∈ launched, (size p : ℝ) := by
  classical
  have hreach (i : Fin D) : i.val + 1 ≤ level run ξ N := i.isLt.trans_le hr
  let pick : Fin D → Slot Packet := fun i => Classical.choose
    (reached_slot hc ξ (Nat.succ_pos i.val) (hreach i))
  have hpick (i : Fin D) := Classical.choose_spec
    (reached_slot hc ξ (Nat.succ_pos i.val) (hreach i))
  have hobs (i : Fin D) :
      observed run ξ (witness run ξ N (i.val + 1) (Nat.succ_pos _) (hreach i)) = some (pick i) :=
    (hpick i).1
  have hinj : Function.Injective (fun i : Fin D => (pick i).packet) := by
    intro i j he
    have hi := (witness_spec hc ξ (Nat.succ_pos _) (hreach i)).1
    have hj := (witness_spec hc ξ (Nat.succ_pos _) (hreach j)).1
    have hs := hc.atomic ξ _ _ _ _ hi hj (hobs i) (hobs j) he
    apply Fin.ext
    have h₁ : (pick i).source + 1 = i.val + 1 := (hpick i).2.1
    have h₂ : (pick j).source + 1 = j.val + 1 := (hpick j).2.1
    omega
  have hsub : ((Finset.univ : Finset (Fin D)).image (fun i : Fin D => (pick i).packet)) ⊆ launched := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact hlaunch _ (witness_spec hc ξ (Nat.succ_pos _) (hreach i)).1 _ (hobs i)
  calc
    _ = ∑ i : Fin D, (size (pick i).packet : ℝ) := by
      apply sum_congr rfl
      intro i _
      exact observed_cost ξ size (hreach i) _ (hobs i)
    _ = ∑ p ∈ (Finset.univ : Finset (Fin D)).image (fun i : Fin D => (pick i).packet), (size p : ℝ) := by
      rw [sum_image (fun _ _ _ _ he => hinj he)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)

lemma fast_probability {Packet : Type*} {run : Scheduler Packet} {N : ℕ}
    (hc : Causal run N) (μ : ProbabilityMeasure Bool) (P : ProbabilityMeasure (ℕ → Bool))
    (hiid : IID (fun i (ξ : ℕ → Bool) => ξ i) (μ : Measure Bool) (P : Measure (ℕ → Bool)))
    (hq : 0 < (μ : Measure Bool).real ({true} : Set Bool)) (m : ℕ)
    (size : Packet → ℕ) {ℓ U : ℝ}
    (hcount : ∀ ξ, ∑ i ∈ range N,
      (past i ⁻¹' eligibility run (fun s => (size s.packet : ℝ) ≤ U) m ℓ i).indicator
        (fun _ => (1 : ℝ)) ξ ≤ 1 / (8 * (μ : Measure Bool).real ({true} : Set Bool))) :
    (P : Measure (ℕ → Bool)).real {ξ | delay run N m ℓ ξ ≤ ℓ ∧ cost run N m size ξ ≤ U} ≤ 1 / 8 := by
  let keep := fun s : Slot Packet => (size s.packet : ℝ) ≤ U
  let fast := {ξ | delay run N m ℓ ξ ≤ ℓ ∧ cost run N m size ξ ≤ U}
  have hf : MeasurableSet fast := (measurableSet_le (delay_measurable run N m ℓ) measurable_const).inter
    (measurableSet_le (cost_measurable run N m size) measurable_const)
  apply adaptive_count_bound μ P hiid N (eligibility run keep m ℓ) {true} fast
    (fun _ => Set.to_countable _ |>.measurableSet) (measurableSet_singleton true) hf hq hcount
  intro ξ hξ
  obtain ⟨ht, hw⟩ : delay run N m ℓ ξ ≤ ℓ ∧ cost run N m size ξ ≤ U := hξ
  have hr : m + 1 ≤ level run ξ N := by
    unfold delay at ht
    split at ht
    · assumption
    · linarith only [ht]
  have hd : reachTime run ξ N (m + 1) - reachTime run ξ N m ≤ ℓ := by simpa [delay, hr] using ht
  obtain ⟨i, hi, helig, hbit⟩ := witness_eligible hc ξ hr keep ℓ hd (fun s hs => by
    change (size s.packet : ℝ) ≤ U
    rw [← observed_cost ξ size hr s hs]
    exact hw)
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨mem_range.mpr hi, helig, hbit⟩⟩

lemma clock_lower {Packet : Type*} {run : Scheduler Packet} {N D : ℕ} (hc : Causal run N)
    (hD : 0 < D) (μ : ProbabilityMeasure Bool) (P : ProbabilityMeasure (ℕ → Bool))
    (hiid : IID (fun i (ξ : ℕ → Bool) => ξ i) (μ : Measure Bool) (P : Measure (ℕ → Bool)))
    (hq : 0 < (μ : Measure Bool).real ({true} : Set Bool))
    (size : Packet → ℕ) {ℓ U ε : ℝ} (hℓ : 0 < ℓ) (hU : 0 < U) (hε : 0 < ε)
    (elapsed error : (ℕ → Bool) → ℝ) (htm : Measurable elapsed)
    (htI : Integrable elapsed (P : Measure (ℕ → Bool)))
    (heI : Integrable error (P : Measure (ℕ → Bool)))
    (ht₀ : ∀ ξ, 0 ≤ elapsed ξ) (he₀ : ∀ ξ, 0 ≤ error ξ)
    (htime : ∀ ξ, ∀ i < N, ∀ s, observed run ξ i = some s → s.finish ≤ elapsed ξ)
    (hwork : ∀ ξ, D ≤ level run ξ N → ∑ i : Fin D, cost run N i size ξ ≤ D * U / 4)
    (hmiss : ∀ ξ, level run ξ N < D → 4 * ε ≤ error ξ)
    (hacc : (∫ ξ, error ξ ∂(P : Measure (ℕ → Bool))) ≤ ε)
    (hcount : ∀ m < D, ∀ ξ, ∑ i ∈ range N,
      (past i ⁻¹' eligibility run (fun s => (size s.packet : ℝ) ≤ U) m ℓ i).indicator
        (fun _ => (1 : ℝ)) ξ ≤ 1 / (8 * (μ : Measure Bool).real ({true} : Set Bool))) :
    (D : ℝ) * ℓ / 8 ≤ ∫ ξ, elapsed ξ ∂(P : Measure (ℕ → Bool)) := by
  let reached := {ξ | D ≤ level run ξ N}
  let quick := reached ∩ {ξ | elapsed ξ ≤ D * ℓ / 4}
  have hr : MeasurableSet reached := measurableSet_le measurable_const (level_measurable run N)
  have hs : MeasurableSet quick := hr.inter (measurableSet_le htm measurable_const)
  have hp (i : Fin D) := fast_probability hc μ P hiid hq i.val size (hcount i i.isLt)
  have hfast : (P : Measure (ℕ → Bool)).real quick ≤ 1 / 4 := by
    apply short_run_bound (P : Measure (ℕ → Bool)) hD
      (fun i => delay run N i.val ℓ) (fun i => cost run N i.val size) hℓ hU
      (fun _ => delay_measurable run N _ ℓ) (fun _ => cost_measurable run N _ size)
      (fun i ξ => delay_nonneg hc i hℓ.le ξ) (fun _ _ => Nat.cast_nonneg _) quick hs hp
    · intro ξ hx
      obtain ⟨hreach, hquick⟩ : D ≤ level run ξ N ∧ elapsed ξ ≤ D * ℓ / 4 := hx
      rw [sum_delay run N D ℓ ξ hreach]
      obtain ⟨s, hobs, _, _, hfinish⟩ := reached_slot hc ξ hD hreach
      rw [hfinish]
      exact (htime ξ _ (witness_spec hc ξ hD hreach).1 s hobs).trans hquick
    · intro ξ hx
      exact hwork ξ hx.1
  have h := expected_time (P : Measure (ℕ → Bool)) elapsed error reached hr htI heI ht₀ he₀
    hε (by positivity : 0 ≤ (D : ℝ) * ℓ / 4) (fun ξ hξ => hmiss ξ (lt_of_not_ge hξ)) hacc hfast htm
  linarith only [h]

end LongTails.Proofs.BirchResourceHardLower
