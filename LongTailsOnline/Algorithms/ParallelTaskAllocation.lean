import LongTailsOnline.Setups.StationaryTaskAllocation
import Mathlib.MeasureTheory.Function.Floor

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LongTailsOnline.Algorithms.ParallelTaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation

noncomputable def noise (p : Public) : ℝ := max 1 p.σ

noncomputable def confidenceLog (p : Public) : ℝ :=
  Real.log (64 * (p.k + 1 : ℝ) * (p.B : ℝ) ^ 2 * (p.T : ℝ) ^ 3 * (1 + noise p))

noncomputable def clipLevel (p : Public) : ℝ :=
  1 + noise p * Real.sqrt (2 * confidenceLog p)

noncomputable def scale (p : Public) : ℝ := clipLevel p * confidenceLog p

noncomputable def bias (p : Public) : ℝ :=
  (1 + noise p) * Real.exp (-confidenceLog p)

noncomputable def imbalance (p : Public) : ℝ :=
  (p.B : ℝ) / (p.k + 1) + (p.k + 1 : ℝ) / p.B

noncomputable def accuracy (p : Public) : ℝ := Real.sqrt (imbalance p / p.T)

noncomputable def precision (p : Public) (h : ℕ) : ℝ := p.B / (2 : ℝ) ^ h

noncomputable def radius (p : Public) (u : ℝ) (N : ℕ) : ℝ :=
  2 * Real.sqrt (u * scale p / N) + 2 * scale p / N + bias p

noncomputable def capacity {k : ℕ} (B : ℕ) (L : ℝ) (s : Worker k → ℝ)
    (i : Worker k) : ℕ := if 0 < s i then min B ⌊L / s i⌋₊ else B

noncomputable def uncertainty {k : ℕ} (B : ℕ) (L : ℝ)
    (s u : Worker k → ℝ) (i : Worker k) : ℝ :=
  capacity B L s i * (u i - s i)

noncomputable def quota (p : Public) (θ u : ℝ) (C : ℕ) : ℕ :=
  if C = 0 then 0 else ⌈256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 +
    32 * scale p * C / θ⌉₊ + 1

noncomputable def clipped {k : ℕ} (H : ℝ) (w : Sample k) (i : Worker k) (j : ℕ) : ℝ :=
  min (w (i, j)) H

noncomputable def empirical {k : ℕ} (H : ℝ) (w : Sample k) (i : Worker k) (N : ℕ) : ℝ :=
  (∑ j ∈ Finset.range N, clipped H w i j) / N

@[fun_prop]
lemma measurable_empirical (k : ℕ) (H : ℝ) (i : Worker k) (N : ℕ) :
    Measurable (fun w : Sample k => empirical H w i N) := by
  unfold empirical clipped
  fun_prop

noncomputable def allocationOfNat (k B j : ℕ) : Allocation k B :=
  if h : j < Fintype.card (Allocation k B) then
    (Fintype.equivFin (Allocation k B)).symm ⟨j, h⟩ else concentrated 0

lemma allocationOfNat_surjective (k B : ℕ) : Function.Surjective (allocationOfNat k B) := by
  intro a
  let j := Fintype.equivFin (Allocation k B) a
  exact ⟨j.val, by simp [allocationOfNat, j.isLt, j]⟩

lemma minimum_exists {k B : ℕ} (u : Worker k → ℝ) :
    ∃ j, ∀ a : Allocation k B, loss u (allocationOfNat k B j) ≤ loss u a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image (Finset.univ : Finset (Allocation k B))
    (loss u) Finset.univ_nonempty
  obtain ⟨j, rfl⟩ := allocationOfNat_surjective k B a
  exact ⟨j, fun a => ha a (Finset.mem_univ a)⟩

noncomputable def upperOracle {k B : ℕ} (u : Worker k → ℝ) : Allocation k B :=
  allocationOfNat k B (Nat.find (minimum_exists (B := B) u))

lemma upperOracle_le {k B : ℕ} (u : Worker k → ℝ) (a : Allocation k B) :
    loss u (upperOracle (B := B) u) ≤ loss u a :=
  Nat.find_spec (minimum_exists (B := B) u) a

@[fun_prop]
lemma measurable_loss_weights {k B : ℕ} (a : Allocation k B) :
    Measurable (fun u : Worker k → ℝ => loss u a) := by
  unfold loss
  have hm := Finset.measurable_sup' Finset.univ_nonempty
    (f := fun i : Worker k => fun u : Worker k → ℝ => ((a.val i).val : ℝ) * u i)
    (fun i _ => by fun_prop)
  have heq : (Finset.univ.sup' Finset.univ_nonempty
      (fun i : Worker k => fun u : Worker k → ℝ => ((a.val i).val : ℝ) * u i)) =
      fun u => Finset.univ.sup' Finset.univ_nonempty
        (fun i => ((a.val i).val : ℝ) * u i) := by
    ext u
    simp only [Finset.sup'_apply]
  exact heq ▸ hm

@[fun_prop]
lemma measurable_upperOracle (k B : ℕ) :
    Measurable (upperOracle : (Worker k → ℝ) → Allocation k B) := by
  apply (measurable_of_countable (allocationOfNat k B)).comp
  apply measurable_find (minimum_exists (k := k) (B := B))
  intro j
  have hm (a : Allocation k B) : MeasurableSet
      {u : Worker k → ℝ | loss u (allocationOfNat k B j) ≤ loss u a} :=
    measurableSet_le (measurable_loss_weights _) (measurable_loss_weights _)
  have he : {u : Worker k → ℝ | ∀ a : Allocation k B,
      loss u (allocationOfNat k B j) ≤ loss u a} =
      ⋂ a : Allocation k B, {u | loss u (allocationOfNat k B j) ≤ loss u a} := by
    ext u
    simp
  exact he.symm ▸ MeasurableSet.iInter hm

abbrev Statistics (k : ℕ) := Counts k × (Worker k → ℝ)

abbrev Intervals (k : ℕ) := (Worker k → ℝ) × (Worker k → ℝ)

noncomputable def refineIntervals (p : Public) (s : Statistics p.k) (ci : Intervals p.k) :
    Intervals p.k :=
  (fun i => if s.1 i = 0 then ci.1 i else
    max (ci.1 i) (max 0 (s.2 i / s.1 i - radius p (ci.2 i) (s.1 i))),
   fun i => if s.1 i = 0 then ci.2 i else
    min (ci.2 i) (min 1 (s.2 i / s.1 i + radius p (ci.2 i) (s.1 i))))

@[fun_prop]
lemma measurable_refineIntervals (p : Public) :
    Measurable (fun v : Statistics p.k × Intervals p.k => refineIntervals p v.1 v.2) := by
  unfold refineIntervals radius
  apply Measurable.prodMk
  all_goals
    apply Measurable.of_eval
    intro i
    apply Measurable.ite
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · fun_prop
    · fun_prop

noncomputable def record {k B : ℕ} (H : ℝ) (s : Statistics k)
    (a : Allocation k B) (f : Feedback k B) : Statistics k :=
  (increment s.1 a, fun i => s.2 i + ∑ j : Fin B,
    if j.val < (a.val i).val then min (f i j) H else 0)

@[fun_prop]
lemma measurable_record (k B : ℕ) (H : ℝ) :
    Measurable (fun p : Statistics k × Allocation k B × Feedback k B =>
      record H p.1 p.2.1 p.2.2) := by
  apply Measurable.prodMk
  · exact (measurable_increment k B).comp
      (measurable_fst.fst.prodMk measurable_snd.fst)
  · apply Measurable.of_eval
    intro i
    apply Measurable.add (by fun_prop)
    apply Finset.measurable_sum
    intro j _
    apply Measurable.ite
    · exact measurableSet_lt measurable_const
        ((measurable_of_countable (fun a : Allocation k B => (a.val i).val)).comp
          measurable_snd.fst)
    · fun_prop
    · fun_prop

noncomputable def level {k B : ℕ} (u : Worker k → ℝ) : ℝ :=
  loss u (upperOracle (B := B) u)

@[fun_prop]
lemma measurable_level (k B : ℕ) : Measurable (level (B := B) : (Worker k → ℝ) → ℝ) := by
  have hf : Measurable (fun u : Worker k → ℝ => fun a : Allocation k B => loss u a) :=
    Measurable.of_eval (fun a => measurable_loss_weights a)
  exact LongTailsOnline.Setups.StochasticBandit.measurable_eval_countable
    (f := fun u : Worker k → ℝ => fun a : Allocation k B => loss u a)
    (i := upperOracle (B := B)) hf (measurable_upperOracle k B)

@[fun_prop]
lemma measurable_capacity (k B : ℕ) :
    Measurable (fun v : ℝ × (Worker k → ℝ) => capacity B v.1 v.2) := by
  apply Measurable.of_eval
  intro i
  unfold capacity
  apply Measurable.ite
  · exact measurableSet_lt measurable_const (by fun_prop)
  · fun_prop
  · fun_prop

@[fun_prop]
lemma measurable_uncertainty (k B : ℕ) :
    Measurable (fun v : ℝ × Intervals k => uncertainty B v.1 v.2.1 v.2.2) := by
  apply Measurable.of_eval
  intro i
  unfold uncertainty
  have hc := (measurable_capacity k B).comp
    (show Measurable (fun v : ℝ × Intervals k => (v.1, v.2.1)) by fun_prop)
  have hci := (measurable_pi_apply i).comp hc
  fun_prop

@[fun_prop]
lemma measurable_quota (p : Public) :
    Measurable (fun v : ℝ × ℝ × ℕ => quota p v.1 v.2.1 v.2.2) := by
  unfold quota
  apply Measurable.ite
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · fun_prop
  · fun_prop

abbrev Plan (k : ℕ) := List (Counts k)

instance (k : ℕ) : MeasurableSpace (Plan k) := ⊤

instance (k : ℕ) : MeasurableSingletonClass (Plan k) where
  measurableSet_singleton _ := trivial

noncomputable def bucketSchedule {k : ℕ} (B : ℕ) (q C : Counts k) (h : ℕ) :
    List (Counts k) :=
  let workers := (List.finRange (k + 1)).filter (fun i => 0 < q i ∧ Nat.log2 (q i) = h)
  let m := workers.length
  let base := 2 ^ h
  let cmin := workers.foldl (fun c i => min c (C i)) B
  let d := max 1 (min cmin (min (2 * base) (max 1 (B / m))))
  let chunk := max 1 (B / d)
  if m = 0 then [] else
    (List.range ((2 * base + d - 1) / d)).flatMap (fun cycle =>
      (List.range ((m + chunk - 1) / chunk)).map (fun j =>
        fun i => if i ∈ (workers.drop (j * chunk)).take chunk then
          min d (2 * base - cycle * d) else 0))

noncomputable def schedule {k : ℕ} (B : ℕ) (q C : Counts k) : List (Counts k) :=
  (List.range (1 + Finset.univ.sup (fun i => Nat.log2 (q i)))).flatMap
    (bucketSchedule B q C)

noncomputable def fill {k B : ℕ} (b : Allocation k B) (C e : Counts k) : Allocation k B :=
  if h : ∃ a : Allocation k B, ∀ i, e i ≤ (a.val i).val ∧
      (a.val i).val ≤ C i ∧ (a.val i).val - e i ≤ (b.val i).val then
    Classical.choose h else concentrated 0

abbrev State (p : Public) :=
  Statistics p.k × Intervals p.k × ℕ × List (Counts p.k) × Fin 4

def initialState (p : Public) : State p :=
  ((fun _ => 0, fun _ => 0), (fun _ => 0, fun _ => 1), 0, [], 0)

noncomputable def start (p : Public) (s : Statistics p.k) (ci : Intervals p.k)
    (h : ℕ) : State p :=
  if ∀ i, ci.1 i ≤ ci.2 i then
    if precision p h ≤ accuracy p ∨ level (B := p.B) ci.2 ≤ accuracy p then
      (s, ci, h, [], 2) else
      let L := level (B := p.B) ci.2
      let C := capacity p.B L ci.1
      let q := fun i => quota p (precision p h) (ci.2 i) (C i)
      (s, ci, h, schedule p.B q C, 1)
  else (s, ci, h, [], 3)

noncomputable def prepare (p : Public) (s : State p) : State p :=
  if s.2.2.2.2 = 0 then start p s.1 s.2.1 s.2.2.1 else
    if s.2.2.2.2 = 1 ∧ s.2.2.2.1 = [] then
      let ci := refineIntervals p s.1 s.2.1
      if ∀ i, uncertainty p.B (level (B := p.B) ci.2) ci.1 ci.2 i ≤
          precision p s.2.2.1 / 2 then
        start p s.1 ci (s.2.2.1 + 1)
      else (s.1, s.2.1, s.2.2.1, [], 3)
    else s

noncomputable def select (p : Public) (s : State p) : Allocation p.k p.B :=
  if s.2.2.2.2 = 2 then upperOracle s.2.1.2 else
    if s.2.2.2.2 = 1 then
      let C := capacity p.B (level (B := p.B) s.2.1.2) s.2.1.1
      fill (upperOracle s.2.1.2) C (s.2.2.2.1.headD (fun _ => 0))
    else concentrated 0

noncomputable def update (p : Public) (s : State p) (a : Allocation p.k p.B)
    (f : Feedback p.k p.B) : State p :=
  (record (clipLevel p) s.1 a f, s.2.1, s.2.2.1,
    (if s.2.2.2.2 = 1 then s.2.2.2.1.tail else s.2.2.2.1), s.2.2.2.2)

@[fun_prop]
lemma measurable_precision (p : Public) : Measurable (precision p) := measurable_of_countable _

@[fun_prop]
lemma measurable_schedule (k B : ℕ) :
    Measurable (fun v : Counts k × Counts k => schedule B v.1 v.2) :=
  measurable_of_countable _

@[fun_prop]
lemma measurable_fill (k B : ℕ) :
    Measurable (fun v : Allocation k B × Counts k × Counts k => fill v.1 v.2.1 v.2.2) :=
  measurable_of_countable _

@[fun_prop]
lemma measurable_head (k : ℕ) : Measurable (fun l : Plan k => l.headD (fun _ => 0)) :=
  measurable_of_countable _

@[fun_prop]
lemma measurable_tail (k : ℕ) : Measurable (List.tail : Plan k → Plan k) :=
  measurable_of_countable _

lemma measurableSet_forall_le {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {f g : α → ι → ℝ} (hf : ∀ i, Measurable (fun x => f x i))
    (hg : ∀ i, Measurable (fun x => g x i)) : MeasurableSet {x | ∀ i, f x i ≤ g x i} := by
  have he : {x | ∀ i, f x i ≤ g x i} = ⋂ i, {x | f x i ≤ g x i} := by ext x; simp
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_le (hf i) (hg i))

@[fun_prop]
lemma measurable_start (p : Public) :
    Measurable (fun v : Statistics p.k × Intervals p.k × ℕ => start p v.1 v.2.1 v.2.2) := by
  unfold start
  apply Measurable.ite
  · exact measurableSet_forall_le (fun i => by fun_prop) (fun i => by fun_prop)
  · apply Measurable.ite
    · have h1 : MeasurableSet {v : Statistics p.k × Intervals p.k × ℕ |
          precision p v.2.2 ≤ accuracy p} :=
        measurableSet_le ((measurable_precision p).comp measurable_snd.snd) measurable_const
      have h2 : MeasurableSet {v : Statistics p.k × Intervals p.k × ℕ |
          level (B := p.B) v.2.1.2 ≤ accuracy p} :=
        measurableSet_le ((measurable_level p.k p.B).comp measurable_snd.fst.snd)
          measurable_const
      exact h1.union h2
    · fun_prop
    · fun_prop
  · fun_prop

set_option maxHeartbeats 2000000 in
@[fun_prop]
lemma measurable_prepare (p : Public) : Measurable (prepare p) := by
  have hci : Measurable (fun s : State p => refineIntervals p s.1 s.2.1) :=
    (measurable_refineIntervals p).comp (measurable_fst.prodMk measurable_snd.fst)
  have hD : Measurable (fun s : State p => uncertainty p.B
      (level (B := p.B) (refineIntervals p s.1 s.2.1).2)
      (refineIntervals p s.1 s.2.1).1 (refineIntervals p s.1 s.2.1).2) :=
    (measurable_uncertainty p.k p.B).comp
      (((measurable_level p.k p.B).comp hci.snd).prodMk hci)
  unfold prepare
  apply Measurable.ite
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · exact (measurable_start p).comp
      (show Measurable (fun s : State p => (s.1, s.2.1, s.2.2.1)) by fun_prop)
  · apply Measurable.ite
    · exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
        (measurableSet_eq_fun (by fun_prop) measurable_const)
    · apply Measurable.ite
      · exact measurableSet_forall_le (fun i => (measurable_pi_apply i).comp hD)
          (fun i => by fun_prop)
      · exact (measurable_start p).comp
          (measurable_fst.prodMk (hci.prodMk
            (show Measurable (fun s : State p => s.2.2.1 + 1) by fun_prop)))
      · fun_prop
    · exact measurable_id

set_option maxHeartbeats 2000000 in
@[fun_prop]
lemma measurable_select (p : Public) : Measurable (select p) := by
  have hb : Measurable (fun s : State p => upperOracle (B := p.B) s.2.1.2) :=
    (measurable_upperOracle p.k p.B).comp measurable_snd.fst.snd
  have hC : Measurable (fun s : State p =>
      capacity p.B (level (B := p.B) s.2.1.2) s.2.1.1) :=
    (measurable_capacity p.k p.B).comp
      (((measurable_level p.k p.B).comp measurable_snd.fst.snd).prodMk
        measurable_snd.fst.fst)
  have he : Measurable (fun s : State p => s.2.2.2.1.headD (fun _ => 0)) :=
    (measurable_head p.k).comp measurable_snd.snd.snd.fst
  unfold select
  apply Measurable.ite
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · exact hb
  · apply Measurable.ite
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · exact (measurable_fill p.k p.B).comp (hb.prodMk (hC.prodMk he))
    · exact measurable_const

@[fun_prop]
lemma measurable_update (p : Public) :
    Measurable (fun v : State p × Allocation p.k p.B × Feedback p.k p.B =>
      update p v.1 v.2.1 v.2.2) := by
  unfold update
  apply Measurable.prodMk
  · exact (measurable_record p.k p.B (clipLevel p)).comp
      (measurable_fst.fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))
  · apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk
    · apply Measurable.ite
      · exact measurableSet_eq_fun (by fun_prop) measurable_const
      · exact (measurable_tail p.k).comp (by fun_prop)
      · fun_prop
    · fun_prop

noncomputable abbrev algorithm (p : Public) :
    OnlineTemplate.Algorithm Unit (Allocation p.k p.B) (Feedback p.k p.B) where
  State := State p
  initial := ⟨Measure.dirac (initialState p), inferInstance⟩
  choose _ := Kernel.deterministic
    (fun s => (select p (prepare p s.1), prepare p s.1)) (by fun_prop)
  update _ := Kernel.deterministic
    (fun s => update p s.1 s.2.2.1 s.2.2.2) (by fun_prop)

end LongTailsOnline.Algorithms.ParallelTaskAllocation
