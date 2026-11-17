import LongTails.Algorithms.DashaDistributed
import LongTails.Proofs.DistributedExecution
import LongTails.Proofs.DashaPackets
import LongTails.Proofs.DashaQuantization
import LongTails.Proofs.DashaModular

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedExecution

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling

variable {p : Params}

def workerProgress (v : Fin (p.n + 1)) (s : State p) : ℕ :=
  Fin.cases ((2 * p.n + 1) * s.iteration + s.arrived.card + (p.n - s.targets.length))
    (fun _ => 4 * s.iteration + s.pending.toNat + 2 * s.outbox.isSome.toNat + 3 * s.sent.toNat) v

lemma query_progress (cfg : Config p) (v : Fin (p.n + 1)) (s : State p) (clock : ClockReading) :
    workerProgress v s ≤ workerProgress v ((algorithm p cfg).query v s clock).2 := by
  classical
  induction v using Fin.cases with
  | zero =>
    cases h : s.outbox <;> cases ht : s.targets <;> simp [algorithm, h, ht, workerProgress]
    omega
  | succ i =>
    simp only [algorithm, Fin.cases_succ]
    split_ifs with hready
    · have hp : s.pending = false := by simpa using hready.2.1
      have hs : s.sent = false := by simpa using hready.2.2
      cases ho : s.outbox <;> simp [workerProgress, ho, hp, hs]
    · exact le_rfl

lemma computed_progress (cfg : Config p) (i : Fin p.n) (s : State p) (h : Point p)
    (hp : s.pending = true) (ho : s.outbox = none) (hs : s.sent = false) :
    workerProgress i.succ s < workerProgress i.succ (computed p cfg i s h) := by
  simp [workerProgress, computed, hp, ho, hs]

lemma advance_progress (cfg : Config p) (i : Fin p.n) (s : State p) (total : Fin p.d → ℤ)
    (hp : s.pending = false) (ho : s.outbox = none) (hs : s.sent = true) :
    workerProgress i.succ s < workerProgress i.succ (advance p cfg s total) := by
  simp only [workerProgress, Fin.cases_succ, advance, hp, hs, ho, Option.isSome_none,
    Bool.toNat_false, Bool.toNat_true]
  omega

lemma accept_progress (cfg : Config p) (s : State p) (i : Fin p.n) (bits : List Bool)
    (hi : i ∉ s.arrived) :
    workerProgress 0 s < workerProgress 0 (accept p cfg s i.succ bits) := by
  classical
  have hc : s.arrived.card ≤ p.n := by simpa using Finset.card_le_univ s.arrived
  have htargets := Nat.sub_le p.n s.targets.length
  unfold accept
  simp only [Fin.cases_succ, ite_eq_left hi]
  split_ifs <;> simp only [workerProgress, Fin.cases_zero, advance, Finset.card_empty,
    Finset.card_insert_of_notMem hi, List.length_finRange, Nat.sub_self, Nat.mul_add, Nat.mul_one] <;> omega

lemma uplinkMessage_length (cfg : Config p) (i : Fin p.n) (s : State p) (h : Point p) :
    (uplinkMessage p cfg i s h).length = if s.iteration = 0 then initialBits p cfg else roundBits p cfg := by
  by_cases hk : s.iteration = 0
  · cases hi : cfg.initializer <;> cases hm : cfg.modularInitialization <;>
      simp_all [uplinkMessage, initialBits, LongTails.Algorithms.DashaQuantization.message,
        DashaQuantization.encode_length, DashaPackets.message_length, DashaModular.encode_length]
  · simp only [uplinkMessage, ite_eq_right hk, roundBits]
    exact DashaPackets.message_length _ _ _ _ _ _

lemma roundStart_succ (cfg : Config p) (k : ℕ) :
    roundStart p cfg (k + 1) = roundStart p cfg k + computationTime p + uploadTime p cfg k := by
  cases k with
  | zero => simp [roundStart, uploadTime, add_assoc]
  | succ k =>
    simp only [roundStart, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one, uploadTime]
    push_cast
    ring

structure Points (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p) (selected : ℕ) (s : State p) : Prop where
  point : s.point = (idealTrajectory p cfg f seed s.iteration).point
  index : s.outputIndex = selected
  selected_point : s.selected = if selected ≤ s.iteration then (idealTrajectory p cfg f seed selected).point else p.x0

lemma initial_points (cfg : Config p) (f : Functions p)
    (seed : Fin cfg.iterations × (ℕ → Sample p)) (v : Fin (p.n + 1)) :
    Points cfg f seed.2 seed.1.val ((algorithm p cfg).initial v seed) := by
  have hx : (idealTrajectory p cfg f seed.2 0).point = p.x0 := by
    cases hi : cfg.initializer <;> simp [idealTrajectory, idealInitial, hi, initialIterate, sparseInitialIterate]
  constructor
  · exact hx.symm
  · rfl
  · change p.x0 = if seed.1.val ≤ 0 then (idealTrajectory p cfg f seed.2 seed.1.val).point else p.x0
    split_ifs with hi
    · have he : seed.1.val = 0 := by omega
      rw [he, hx]
    · rfl

lemma advance_points (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p) (selected : ℕ)
    (s : State p) (h : Points cfg f seed selected s) :
    Points cfg f seed selected (advance p cfg s (fun j => ∑ i, (idealTrajectory p cfg f seed s.iteration).localCode i j)) := by
  have hp : (advance p cfg s (fun j => ∑ i, (idealTrajectory p cfg f seed s.iteration).localCode i j)).point =
      (idealTrajectory p cfg f seed (s.iteration + 1)).point := by
    change s.point - stepSize p cfg.choice • estimate p cfg.choice (idealTrajectory p cfg f seed s.iteration) = _
    rw [h.point]
    rfl
  constructor
  · exact hp
  · exact h.index
  · change (if s.iteration + 1 = s.outputIndex then
        (advance p cfg s (fun j => ∑ i, (idealTrajectory p cfg f seed s.iteration).localCode i j)).point else s.selected) =
      if selected ≤ s.iteration + 1 then (idealTrajectory p cfg f seed selected).point else p.x0
    rw [hp, h.index, h.selected_point]
    split_ifs with he hle hle' hle' <;> try omega
    · rw [he]
    · rfl
    · rfl

lemma computationTime_le (i : Fin p.n) : p.h i ≤ computationTime p :=
  Finset.le_sup (Finset.mem_univ i)

lemma computationTime_attained : ∃ i : Fin p.n, computationTime p = p.h i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty p.h
  exact ⟨i, hi⟩

lemma ideal_gradient (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (k : ℕ) (i : Fin p.n) :
    (idealTrajectory p cfg f seed k).localGradient i = gradient (f i) (idealTrajectory p cfg f seed k).point := by
  cases k with
  | zero => cases hi : cfg.initializer <;> simp [idealTrajectory, idealInitial, hi, initialIterate, sparseInitialIterate]
  | succ k => rfl

noncomputable def previousCode (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p) :
    ℕ → Fin p.n → Fin p.d → ℤ
  | 0, _ => 0
  | k + 1, i => (idealTrajectory p cfg f seed k).localCode i

noncomputable def previousGradient (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p) :
    ℕ → Fin p.n → Point p
  | 0, _ => 0
  | k + 1, i => (idealTrajectory p cfg f seed k).localGradient i

noncomputable def increment (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (k : ℕ) (i : Fin p.n) : Fin p.d → ℤ :=
  (idealTrajectory p cfg f seed k).localCode i - previousCode cfg f seed k i

noncomputable def wireIncrement (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (k : ℕ) (i : Fin p.n) : Fin p.d → ℤ :=
  if modularAt p cfg k then fun j => increment cfg f seed k i j % LongTails.Algorithms.DashaModular.modulus cfg.initialWidth
  else increment cfg f seed k i

noncomputable def workerMessage (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (k : ℕ) (i : Fin p.n) : List Bool :=
  uplinkMessage p cfg i
    { point := (idealTrajectory p cfg f seed k).point
      selected := p.x0
      outputIndex := 0
      randomness := seed
      iteration := k
      localGradient := previousGradient cfg f seed k i
      code := previousCode cfg f seed k i }
    (gradient (f i) (idealTrajectory p cfg f seed k).point)

noncomputable def broadcastMessage (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (k : ℕ) : List Bool :=
  LongTails.Algorithms.DashaQuantization.encode p.d cfg.broadcastWidth
    (fun j => ∑ i, (idealTrajectory p cfg f seed k).localCode i j)

structure TransportExact (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p) : Prop where
  worker : ∀ k < (cfg.iterations : ℕ), ∀ i suffix,
    uplinkReceive p cfg seed k i (workerMessage cfg f seed k i ++ suffix) = wireIncrement cfg f seed k i
  retained : ∀ k < (cfg.iterations : ℕ), ∀ i s, s.iteration = k → s.randomness = seed →
    localIncrement p cfg i s (gradient (f i) (idealTrajectory p cfg f seed k).point)
      (workerMessage cfg f seed k i) = increment cfg f seed k i
  total : ∀ k < (cfg.iterations : ℕ),
    finishTotal p cfg k ((fun j => ∑ i, previousCode cfg f seed k i j) +
      (fun j => ∑ i, wireIncrement cfg f seed k i j)) =
      fun j => ∑ i, (idealTrajectory p cfg f seed k).localCode i j
  broadcast : ∀ k < (cfg.iterations : ℕ), ∀ suffix,
    LongTails.Algorithms.DashaQuantization.decode p.d cfg.broadcastWidth
      (broadcastMessage cfg f seed k ++ suffix) =
      (fun j => ∑ i, (idealTrajectory p cfg f seed k).localCode i j)

lemma transportExact_of_nonmodular (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (hmod : cfg.modularInitialization = false)
    (hw : ∀ k < (cfg.iterations : ℕ), ∀ i suffix,
      uplinkReceive p cfg seed k i (workerMessage cfg f seed k i ++ suffix) = increment cfg f seed k i)
    (hb : ∀ k < (cfg.iterations : ℕ), ∀ suffix,
      LongTails.Algorithms.DashaQuantization.decode p.d cfg.broadcastWidth
        (broadcastMessage cfg f seed k ++ suffix) =
        (fun j => ∑ i, (idealTrajectory p cfg f seed k).localCode i j)) :
    TransportExact cfg f seed := by
  refine ⟨?_, ?_, ?_, hb⟩
  · simpa only [wireIncrement, modularAt, hmod, Bool.false_and, Bool.false_eq_true, ite_false] using hw
  · intro k hk i s hiter hseed
    simpa only [localIncrement, modularAt, hmod, Bool.false_and, Bool.false_eq_true, ite_false,
      hiter, hseed, List.append_nil] using hw k hk i []
  · intro k hk
    simp only [finishTotal, wireIncrement, modularAt, hmod, Bool.false_and, Bool.false_eq_true, ite_false]
    funext j
    simp only [Pi.add_apply, increment, Pi.sub_apply, Finset.sum_sub_distrib]
    ring

lemma workerMessage_length (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p) (k : ℕ) (i : Fin p.n) :
    (workerMessage cfg f seed k i).length = if k = 0 then initialBits p cfg else roundBits p cfg :=
  uplinkMessage_length cfg i _ _

lemma broadcastMessage_length (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p) (k : ℕ) :
    (broadcastMessage cfg f seed k).length = p.d * cfg.broadcastWidth :=
  DashaQuantization.encode_length _ _ _

lemma computed_values (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (hexact : TransportExact cfg f seed) (k : ℕ) (hk : k < (cfg.iterations : ℕ))
    (i : Fin p.n) (s : State p) (hiter : s.iteration = k) (hseed : s.randomness = seed)
    (hcode : s.code = previousCode cfg f seed k i) (hgrad : s.localGradient = previousGradient cfg f seed k i) :
    let next := computed p cfg i s (gradient (f i) (idealTrajectory p cfg f seed k).point)
    next.code = (idealTrajectory p cfg f seed k).localCode i ∧
      next.localGradient = gradient (f i) (idealTrajectory p cfg f seed k).point ∧
      next.outbox = some (workerMessage cfg f seed k i) := by
  have hmessage : uplinkMessage p cfg i s (gradient (f i) (idealTrajectory p cfg f seed k).point) =
      workerMessage cfg f seed k i := by
    unfold workerMessage uplinkMessage
    simp only [hiter, hseed, hcode, hgrad]
  have hw := hexact.retained k hk i s hiter hseed
  dsimp only [computed]
  rw [hmessage, hw, hcode]
  refine ⟨?_, rfl, rfl⟩
  unfold increment
  abel

structure WorkerData (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (i : Fin p.n) (s : State p)
    (oracle : LongTails.Setups.StarNetwork.ComputationState (Point p) Unit) : Prop where
  points : Points cfg f seed selected.val s
  randomness : s.randomness = seed
  code : s.code = if s.sent then (idealTrajectory p cfg f seed s.iteration).localCode i else previousCode cfg f seed s.iteration i
  gradient : s.localGradient = if s.sent then (idealTrajectory p cfg f seed s.iteration).localGradient i else
    previousGradient cfg f seed s.iteration i
  used : oracle.used = s.iteration + s.sent.toNat
  outbox : s.outbox = none

structure RootData (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (s : State p) : Prop where
  points : Points cfg f seed selected.val s
  randomness : s.randomness = seed
  code : s.code = fun j => ∑ i, previousCode cfg f seed s.iteration i j
  accumulator : s.accumulator = fun j => ∑ i ∈ s.arrived, wireIncrement cfg f seed s.iteration i j

lemma initial_worker_data (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (i : Fin p.n) :
    WorkerData cfg f seed selected i ((algorithm p cfg).initial i.succ (selected, seed))
      ((system p f).computation.initial i.succ ()) := by
  refine ⟨initial_points cfg f (selected, seed) i.succ, ?_, ?_, ?_, ?_, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl

lemma initial_root_data (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) :
    RootData cfg f seed selected ((algorithm p cfg).initial 0 (selected, seed)) := by
  refine ⟨initial_points cfg f (selected, seed) 0, rfl, ?_, ?_⟩
  · funext j
    simp [algorithm, previousCode]
  · funext j
    simp [algorithm]

lemma accumulated_insert (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (s : State p) (h : RootData cfg f seed selected s)
    (i : Fin p.n) (hi : i ∉ s.arrived) :
    s.accumulator + wireIncrement cfg f seed s.iteration i =
      fun j => ∑ a ∈ insert i s.arrived, wireIncrement cfg f seed s.iteration a j := by
  funext j
  rw [Finset.sum_insert hi]
  have he := congrFun h.accumulator j
  change s.accumulator j + wireIncrement cfg f seed s.iteration i j = _
  rw [he]
  ring

lemma total_insert (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (s : State p) (h : RootData cfg f seed selected s)
    (hexact : TransportExact cfg f seed) (hk : s.iteration < (cfg.iterations : ℕ))
    (i : Fin p.n) (hi : i ∉ s.arrived) (hall : insert i s.arrived = Finset.univ) :
    finishTotal p cfg s.iteration (s.code + (s.accumulator + wireIncrement cfg f seed s.iteration i)) =
      fun j => ∑ a, (idealTrajectory p cfg f seed s.iteration).localCode a j := by
  rw [accumulated_insert cfg f seed selected s h i hi, hall, h.code]
  exact hexact.total s.iteration hk

lemma accept_root_data (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (hexact : TransportExact cfg f seed)
    (s : State p) (h : RootData cfg f seed selected s)
    (hk : s.iteration < (cfg.iterations : ℕ)) (i : Fin p.n) (hi : i ∉ s.arrived) :
    RootData cfg f seed selected (accept p cfg s i.succ
      (workerMessage cfg f seed s.iteration i ++ List.replicate clockBits false)) := by
  have hw := hexact.worker s.iteration hk i (List.replicate clockBits false)
  have hb := hexact.broadcast s.iteration hk []
  simp only [List.append_nil] at hb
  unfold accept
  simp only [Fin.cases_succ, ite_eq_left hi, h.randomness, hw]
  split_ifs with hall
  · have ht := total_insert cfg f seed selected s h hexact hk i hi hall
    rw [ht]
    change RootData cfg f seed selected
      { advance p cfg s (LongTails.Algorithms.DashaQuantization.decode p.d cfg.broadcastWidth
          (broadcastMessage cfg f seed s.iteration)) with
        code := fun j => ∑ a, (idealTrajectory p cfg f seed s.iteration).localCode a j
        outbox := some (broadcastMessage cfg f seed s.iteration)
        targets := List.finRange p.n }
    rw [hb]
    have hp := advance_points cfg f seed selected.val s h.points
    refine ⟨⟨hp.point, hp.index, hp.selected_point⟩, h.randomness, ?_, ?_⟩
    · rfl
    · funext j
      simp [advance]
  · refine ⟨⟨h.points.point, h.points.index, h.points.selected_point⟩, rfl, h.code, ?_⟩
    exact accumulated_insert cfg f seed selected s h i hi

lemma computed_query (cfg : Config p) (i : Fin p.n) (s : State p) (h : Point p) (clock : ClockReading)
    (hk : s.iteration < (cfg.iterations : ℕ)) (hs : s.sent = false) :
    (algorithm p cfg).query i.succ (computed p cfg i s h) clock =
      (.communicate (0, ((computed p cfg i s h).outbox.getD [])),
        { computed p cfg i s h with outbox := none, sent := true }) := by
  simp [algorithm, computed, hk, hs]

lemma computed_worker_data (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (hexact : TransportExact cfg f seed)
    (i : Fin p.n) (s : State p) (oracle : LongTails.Setups.StarNetwork.ComputationState (Point p) Unit)
    (h : WorkerData cfg f seed selected i s oracle)
    (hk : s.iteration < (cfg.iterations : ℕ)) (hs : s.sent = false) :
    WorkerData cfg f seed selected i
      { computed p cfg i s (gradient (f i) s.point) with outbox := none, sent := true }
      { oracle with pending := none, used := oracle.used + 1 } := by
  have hc := h.code
  have hg := h.gradient
  simp only [hs, Bool.false_eq_true, ite_eq_right, not_false_eq_true] at hc hg
  have hv := computed_values cfg f seed hexact s.iteration hk i s rfl h.randomness hc hg
  rw [h.points.point]
  refine ⟨⟨h.points.point, h.points.index, h.points.selected_point⟩, h.randomness, ?_, ?_, ?_, rfl⟩
  · exact hv.1
  · exact ideal_gradient cfg f seed s.iteration i |>.symm
  · have hu := h.used
    simp only [hs, Bool.toNat_false, add_zero] at hu
    simp only [computed, Bool.toNat_true]
    omega

lemma advance_worker_data (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (selected : Fin cfg.iterations) (i : Fin p.n) (s : State p)
    (oracle : LongTails.Setups.StarNetwork.ComputationState (Point p) Unit)
    (h : WorkerData cfg f seed selected i s oracle) (hs : s.sent = true) :
    WorkerData cfg f seed selected i
      (advance p cfg s (fun j => ∑ a, (idealTrajectory p cfg f seed s.iteration).localCode a j)) oracle := by
  have hp := advance_points cfg f seed selected.val s h.points
  refine ⟨hp, h.randomness, ?_, ?_, ?_, rfl⟩
  · simpa only [advance, Bool.false_eq_true, ite_false, previousCode, hs, ite_true] using h.code
  · simpa only [advance, Bool.false_eq_true, ite_false, previousGradient, hs, ite_true] using h.gradient
  · simpa only [advance, Bool.toNat_false, add_zero, hs, Bool.toNat_true] using h.used

lemma roundStart_mono (cfg : Config p) : Monotone (roundStart p cfg) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [roundStart_succ]
  exact (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (by positivity))

lemma final_round_budget (cfg : Config p) : roundStart p cfg (cfg.iterations : ℕ) + cfg.slack = timeBudget p cfg := by
  simp only [roundStart, cfg.iterations.ne_zero, ite_false, timeBudget]

lemma roundStart_le_budget (cfg : Config p) (k : ℕ) (hk : k ≤ cfg.iterations) :
    roundStart p cfg k ≤ timeBudget p cfg := by
  rw [← final_round_budget]
  exact (roundStart_mono cfg hk).trans (le_add_of_nonneg_right (by positivity))

lemma worker_finish_le_budget (cfg : Config p) (i : Fin p.n) (k : ℕ) (hk : k < cfg.iterations) :
    roundStart p cfg k + p.h i + uploadTime p cfg k ≤ timeBudget p cfg := by
  calc
    _ ≤ roundStart p cfg k + computationTime p + uploadTime p cfg k :=
      add_le_add (add_le_add le_rfl (computationTime_le (p := p) i)) le_rfl
    _ = roundStart p cfg (k + 1) := (roundStart_succ cfg k).symm
    _ ≤ _ := roundStart_le_budget cfg (k + 1) (Nat.succ_le_of_lt hk)

end LongTails.Proofs.DashaDistributedExecution
