import LongTails.Proofs.BirchNonEuclideanEventMeaning

namespace LongTails.Proofs.BirchNonEuclideanEventHistory

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Algorithms.BirchNonEuclideanTrajectories
open LongTails.Proofs.BirchNonEuclideanScheduling

def Captured {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H : ℕ)
    (s : EventState m × Values p.d m) : Prop :=
  ∀ w ∈ s.1.live,
    s.2.launchPoint w = s.2.points (s.1.schedule.source w) ∧
    s.2.launchMomentum w = s.2.momenta (s.1.schedule.source w) ∧
    (s.2.point w, s.2.momentum w) =
      localValues p lmo (fun h => response (Sum.inr (w, s.1.schedule.serial w, h)))
        η B H (s.2.launchPoint w, s.2.launchMomentum w) (s.1.progress w)

lemma captured_query {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H K R : ℕ)
    (s : EventState m × Values p.d m) (w : Fin m)
    (hc : Captured p lmo response η B H s) :
    Captured p lmo response η B H (eventValues p lmo response η B H K R (.query w) s) := by
  intro i hi
  have hh := hc i hi
  by_cases he : i = w
  · subst i
    refine ⟨hh.1, hh.2.1, ?_⟩
    simp only [eventValues, eventStep, Function.update_self, localValues, ← hh.2.2]
  · simpa only [eventValues, eventStep, Function.update_of_ne he] using hh

lemma captured_complete {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H K R : ℕ)
    (s : EventState m × Values p.d m) (w : Fin m)
    (hsrc : ∀ i, s.1.schedule.source i ≤ s.1.schedule.accepted.length)
    (hc : Captured p lmo response η B H s) :
    Captured p lmo response η B H (eventValues p lmo response η B H K R (.complete w) s) := by
  intro i hi
  by_cases ha : s.1.schedule.accepted.length < K
  · by_cases hg : s.1.schedule.accepted.length - s.1.schedule.source w ≤ R
    · by_cases hn : s.1.schedule.accepted.length + 1 < K
      · have hmem : i ∈ s.1.live := by simpa [eventValues, eventStep, scheduleStep, ha, hg, hn] using hi
        have hh := hc i hmem
        by_cases he : i = w
        · subst i
          simp [eventValues, eventStep, scheduleStep, ha, hg, hn, localValues]
        · have hne : s.1.schedule.source i ≠ s.1.schedule.accepted.length + 1 := by have := hsrc i; omega
          simpa [eventValues, eventStep, scheduleStep, ha, hg, hn, he, hne] using hh
      · have hmem : i ∈ s.1.live ∧ i ≠ w := by
          simpa [eventValues, eventStep, scheduleStep, ha, hg, hn, Finset.mem_erase, and_comm] using hi
        have hh := hc i hmem.1
        have hne : s.1.schedule.source i ≠ s.1.schedule.accepted.length + 1 := by have := hsrc i; omega
        simpa [eventValues, eventStep, scheduleStep, ha, hg, hn, hmem.2, hne] using hh
    · have hmem : i ∈ s.1.live := by simpa [eventValues, eventStep, scheduleStep, ha, hg] using hi
      have hh := hc i hmem
      by_cases he : i = w
      · subst i
        simp [eventValues, eventStep, scheduleStep, ha, hg, localValues]
      · simpa [eventValues, eventStep, scheduleStep, ha, hg, he] using hh
  · have hmem : i ∈ s.1.live := by
      have hh : i ∈ s.1.live.erase w := by simpa [eventValues, eventStep, ha] using hi
      exact Finset.mem_of_mem_erase hh
    simpa [eventValues, eventStep, ha] using hc i hmem

structure History (d : ℕ) where
  count : ℕ
  points : ℕ → Point d
  momenta : ℕ → Point d

noncomputable def historyStep {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H : ℕ)
    (old : History p.d) (job : Packet m) : History p.d :=
  let packet := localValues p lmo (fun h => response (Sum.inr (job.worker, job.serial, h)))
    η B H (old.points job.source, old.momenta job.source) H
  { count := old.count + 1
    points := Function.update old.points (old.count + 1)
      (old.points old.count + (packet.1 - old.points job.source))
    momenta := Function.update old.momenta (old.count + 1)
      (old.momenta old.count + (packet.2 - old.momenta job.source)) }

noncomputable def packetHistory {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H : ℕ)
    (initial : Point p.d) (jobs : List (Packet m)) : History p.d :=
  jobs.foldl (historyStep p lmo response η B H)
    { count := 0, points := fun _ => p.x0, momenta := fun _ => initial }

lemma packetHistory_append {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H : ℕ)
    (initial : Point p.d) (jobs : List (Packet m)) (job : Packet m) :
    packetHistory p lmo response η B H initial (jobs ++ [job]) =
      historyStep p lmo response η B H (packetHistory p lmo response η B H initial jobs) job := by
  simp only [packetHistory, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma packetHistory_count {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H : ℕ)
    (initial : Point p.d) (jobs : List (Packet m)) :
    (packetHistory p lmo response η B H initial jobs).count = jobs.length := by
  induction jobs using List.reverseRecOn with
  | nil => rfl
  | append_singleton jobs job ih =>
      rw [packetHistory_append]
      simpa only [historyStep, List.length_append, List.length_singleton] using congrArg (· + 1) ih

def HistoryMatches {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H : ℕ)
    (initial : Point p.d) (s : EventState m × Values p.d m) : Prop :=
  let hist := packetHistory p lmo response η B H initial s.1.schedule.accepted
  s.2.points = hist.points ∧ s.2.momenta = hist.momenta

lemma historyMatches_step {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H K R : ℕ)
    (initial : Point p.d) (s : EventState m × Values p.d m) (e : Event m)
    (word : ℕ → Fin m) (he : e.Enabled H K word s.1)
    (hc : Captured p lmo response η B H s)
    (hh : HistoryMatches p lmo response η B H initial s) :
    HistoryMatches p lmo response η B H initial (eventValues p lmo response η B H K R e s) := by
  cases e with
  | query w => exact hh
  | complete w =>
      have hcap := hc w he.1
      have hp : (s.2.point w, s.2.momentum w) =
          localValues p lmo (fun h => response (Sum.inr (w, s.1.schedule.serial w, h)))
            η B H (s.2.points (s.1.schedule.source w), s.2.momenta (s.1.schedule.source w)) H := by
        simpa only [he.2.1, hcap.1, hcap.2.1] using hcap.2.2
      have hx := congrArg Prod.fst hp
      have hv := congrArg Prod.snd hp
      dsimp only at hx hv
      dsimp only [HistoryMatches] at hh ⊢
      by_cases ha : s.1.schedule.accepted.length < K
      · by_cases hg : s.1.schedule.accepted.length - s.1.schedule.source w ≤ R
        · by_cases hn : s.1.schedule.accepted.length + 1 < K
          all_goals
            simp only [eventValues, eventStep, scheduleStep, ha, hg, and_self, ite_true,
              List.length_append, List.length_singleton, hn, and_false, ite_false,
              packetHistory_append, historyStep, packetHistory_count]
            exact ⟨by rw [hx, hcap.1, hh.1, hh.2], by rw [hv, hcap.2.1, hh.1, hh.2]⟩
        · simpa [eventValues, eventStep, scheduleStep, ha, hg] using hh
      · simpa [eventValues, eventStep, scheduleStep, ha] using hh

lemma eventValues_public {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H K R : ℕ)
    (s : EventState m × Values p.d m) (e : Event m) :
    (eventValues p lmo response η B H K R e s).1 = eventStep K R s.1 e := by
  cases e <;> rfl

def ReplayInvariant {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H K R : ℕ)
    (initial : Point p.d) (s : EventState m × Values p.d m) : Prop :=
  ScheduleInvariant K R s.1.schedule ∧ Captured p lmo response η B H s ∧
    HistoryMatches p lmo response η B H initial s

lemma replayInvariant_step {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H K R : ℕ)
    (initial : Point p.d) (s : EventState m × Values p.d m) (e : Event m)
    (word : ℕ → Fin m) (he : e.Enabled H K word s.1)
    (hi : ReplayInvariant p lmo response η B H K R initial s) :
    ReplayInvariant p lmo response η B H K R initial (eventValues p lmo response η B H K R e s) := by
  refine ⟨?_, ?_, historyMatches_step p lmo response η B H K R initial s e word he hi.2.1 hi.2.2⟩
  · rw [eventValues_public]
    cases e with
    | query w => exact hi.1
    | complete w =>
        by_cases ha : s.1.schedule.accepted.length < K
        · simpa only [eventStep, ite_eq_left ha] using scheduleStep_invariant K R w s.1.schedule hi.1
        · simpa only [eventStep, ite_eq_right ha] using hi.1
  · cases e with
    | query w => exact captured_query p lmo response η B H K R s w hi.2.1
    | complete w => exact captured_complete p lmo response η B H K R s w hi.1.2.1 hi.2.1

lemma replayInvariant_fold {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H K R : ℕ)
    (initial : Point p.d) (s : EventState m × Values p.d m) (events : List (Event m))
    (word : ℕ → Fin m) (he : LegalFrom H K R word s.1 events)
    (hi : ReplayInvariant p lmo response η B H K R initial s) :
    ReplayInvariant p lmo response η B H K R initial
      (events.foldl (fun state e => eventValues p lmo response η B H K R e state) s) := by
  induction events generalizing s with
  | nil => exact hi
  | cons e rest ih =>
      apply ih
      · simpa only [eventValues_public] using he.2
      · exact replayInvariant_step p lmo response η B H K R initial s e word he.1 hi

def initialValues {m : ℕ} (p : Params) (initial : Point p.d) : Values p.d m where
  points := fun _ => p.x0
  momenta := fun _ => initial
  launchPoint := fun _ => p.x0
  launchMomentum := fun _ => initial
  point := fun _ => p.x0
  momentum := fun _ => initial

lemma replayInvariant_initial {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H K R : ℕ)
    (initial : Point p.d) :
    ReplayInvariant p lmo response η B H K R initial ({}, initialValues p initial) := by
  simp [ReplayInvariant, ScheduleInvariant, agePotential, Captured, HistoryMatches,
    initialValues, packetHistory, localValues]

noncomputable def packetResponse {m : ℕ} (response : QueryLabel m → Point d → Point d)
    (jobs : List (Packet m)) (k h : ℕ) (x : Point d) : Point d :=
  match jobs[k]? with
  | some job => response (Sum.inr (job.worker, job.serial, h)) x
  | none => 0

lemma pairedValues_congr (p : Params) (lmo : Point p.d → Point p.d)
    (response response' : ℕ → ℕ → Point p.d → Point p.d) (η : ℝ) (B H : ℕ)
    (dispatch dispatch' : ℕ → ℕ) (initial : Point p.d) (K : ℕ)
    (hr : ∀ k < K, response k = response' k) (hd : ∀ k < K, dispatch k = dispatch' k) :
    pairedValues p lmo response η B H dispatch initial K =
      pairedValues p lmo response' η B H dispatch' initial K := by
  induction K with
  | zero => rfl
  | succ K ih =>
      simp only [pairedValues, ih (fun k hk => hr k (by omega)) (fun k hk => hd k (by omega)),
        hr K (by omega), hd K (by omega)]

lemma packetHistory_pairedValues {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : QueryLabel m → Point p.d → Point p.d) (η : ℝ) (B H : ℕ)
    (initial : Point p.d) (jobs : List (Packet m)) :
    let hist := packetHistory p lmo response η B H initial jobs
    (hist.points, hist.momenta) =
      pairedValues p lmo (packetResponse response jobs) η B H (packetSource jobs) initial jobs.length := by
  induction jobs using List.reverseRecOn with
  | nil => rfl
  | append_singleton jobs job ih =>
      have hc := pairedValues_congr p lmo (packetResponse response (jobs ++ [job]))
        (packetResponse response jobs) η B H (packetSource (jobs ++ [job])) (packetSource jobs)
        initial jobs.length (by
          intro k hk
          funext h x
          simp [packetResponse, List.getElem?_eq_getElem hk,
            List.getElem?_eq_getElem (by simp; omega : k < (jobs ++ [job]).length),
            List.getElem_append_left hk]) (by
          intro k hk
          simp [packetSource, List.getElem?_eq_getElem hk,
            List.getElem?_eq_getElem (by simp; omega : k < (jobs ++ [job]).length),
            List.getElem_append_left hk])
      dsimp only at ih ⊢
      rw [packetHistory_append]
      simp only [List.length_append, List.length_singleton, pairedValues, hc, ← ih,
        historyStep, packetHistory_count]
      have hr : packetResponse response (jobs ++ [job]) jobs.length =
          fun h => response (Sum.inr (job.worker, job.serial, h)) := by
        funext h x
        simp [packetResponse]
      rw [hr]
      simp [packetSource]

end LongTails.Proofs.BirchNonEuclideanEventHistory
