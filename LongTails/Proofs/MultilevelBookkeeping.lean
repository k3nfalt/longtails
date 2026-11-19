import LongTails.Proofs.MultilevelDeadline

namespace LongTails.Proofs.MultilevelBookkeeping

open DistributedTemplate MeasureTheory LongTails.Setups
open DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport
open MultilevelTransportState MultilevelTimetable MultilevelWireState MultilevelWireTransitions MultilevelDeadline

variable {p : Params}

structure Local (u : Context p) (b : Book p) (now : Time) : Prop where
  valid : Valid u.t b
  memory : Memory u b
  forecast : Forecast u b
  frontier : b.issued < u.t.count → now ≤ u.t.start b.issued

lemma Good.local {u : Context p} {b : Book p} {c : u.Exec} (h : Good u b c) :
    Local u b c.time := ⟨h.valid,h.memory,h.forecast,h.frontier⟩

lemma valid_launch (u : Context p) (b : Book p) (now : Time) (hl : Local u b now)
    (sc : Timetable p u.t u.T) (hr : ready u.t (root b u.seed u.out)) :
    let τ := now + wire p (payload u.t u.out b.issued)
    Local u (launch u.t b τ) now := by
  intro τ
  have hv := launch_valid _ b τ hl.valid hr.1 hr.2.1
  have hs := sc.service b.issued hr.1
    (fun j => if j < b.issued ∧ u.t.finish j ≤ u.t.start b.issued then u.out j else [])
    (let z := u.t.decode (payload u.t u.out b.issued)
     let i := u.t.worker b.issued
     let sample := u.xs i (ordinal u.t b.issued)
     (u.g i z.1 sample, u.g i z.2 sample))
  have hdata := reply_eq u.t u.g u.xs b.issued
  dsimp only at hs hdata
  change u.t.start b.issued + wire p (payload u.t u.out b.issued) + _ + wire p _ ≤ _ at hs
  have hprice : u.t.start b.issued + wire p (payload u.t u.out b.issued) + 2*p.h (u.t.worker b.issued) +
      wire p (u.out b.issued) ≤ u.t.finish b.issued :=
    (congrArg (fun bs => u.t.start b.issued + wire p (payload u.t u.out b.issued) +
      2*p.h (u.t.worker b.issued) + wire p bs) hdata).le.trans hs
  refine ⟨hv, ?_, ?_, ?_⟩
  · intro i j t h
    by_cases hi : i = u.t.worker b.issued
    · simp [launch,hi] at h
    · exact hl.memory i j t (by simpa [launch,hi] using h)
  · intro i
    by_cases hi : i = u.t.worker b.issued
    · subst i
      simp only [launch,Function.update_self,MultilevelWireState.Phase.within]
      exact (add_le_add_left (add_le_add_left (add_le_add_left (hl.frontier hr.1) _) _) _).trans hprice
    · simpa [launch,hi] using hl.forecast i
  · intro hn
    exact (hl.frontier hr.1).trans (sc.ordered _ _ (Nat.le_succ _) hn)

lemma valid_work (u : Context p) (b : Book p) (now : Time) (hl : Local u b now)
    (i : Fin p.n) (j : ℕ) (h : b.pending i = .down j now) :
    Local u (startWork b i j (now+2*p.h i) (payload u.t u.out j)) now := by
  refine ⟨same_jobs_valid _ _ _ hl.valid rfl rfl ?_, ?_, ?_, hl.frontier⟩
  · intro a
    by_cases ha : a = i <;> simp [startWork,ha,h,Phase.job]
  · intro a k τ hk
    by_cases ha : a = i
    · subst a
      simp [startWork] at hk ⊢
      rw [hk.1]
    · simpa [startWork,ha] using hl.memory a k τ (by simpa [startWork,ha] using hk)
  · intro a
    by_cases ha : a = i
    · subst a; simpa [startWork,h,MultilevelWireState.Phase.within] using hl.forecast i
    · simpa [startWork,ha] using hl.forecast a

lemma valid_reply (u : Context p) (b : Book p) (now : Time) (hl : Local u b now)
    (i : Fin p.n) (j : ℕ) (h : b.pending i = .work j now) :
    Local u (startReply b i j (now+wire p (u.out j))) now := by
  refine ⟨same_jobs_valid _ _ _ hl.valid rfl rfl ?_, ?_, ?_, hl.frontier⟩
  · intro a
    by_cases ha : a = i <;> simp [startReply,ha,h,Phase.job]
  · intro a k τ hk
    by_cases ha : a = i
    · simp [startReply,ha] at hk
    · exact hl.memory a k τ (by simpa [startReply,ha] using hk)
  · intro a
    by_cases ha : a = i
    · subst a; simpa [startReply,h,MultilevelWireState.Phase.within] using hl.forecast i
    · simpa [startReply,ha] using hl.forecast a

lemma valid_collect (u : Context p) (b : Book p) (now : Time) (hl : Local u b now)
    (i : Fin p.n) (j : ℕ) (h : b.pending i = .up j now) :
    Local u (collect b i j) now := by
  refine ⟨collect_valid _ b i j hl.valid (by simp [h,Phase.job]), ?_, ?_, hl.frontier⟩
  · intro a k τ hk
    by_cases ha : a = i
    · simp [collect,ha] at hk
    · exact hl.memory a k τ (by simpa [collect,ha] using hk)
  · intro a
    by_cases ha : a = i
    · simp [collect,ha,MultilevelWireState.Phase.within]
    · simpa [collect,ha] using hl.forecast a

lemma phase_decreases (t : Script p) (b c : Book p) (i : Fin p.n) (v : Phase)
    (hn : c.issued = b.issued) (hp : c.pending = Function.update b.pending i v)
    (hv : v.remaining < (b.pending i).remaining) : workLeft t c < workLeft t b := by
  have h := remaining_update b i v
  simp only [workLeft,hn,hp]
  omega

lemma jump_good (u : Context p) (b : Book p) (c : u.Exec) (hg : Good u b c)
    (sc : Timetable p u.t u.T) (hh : ∀ i, 0 < p.h i) (hc : c.time ≤ c.deadline)
    (hquiet : event u.O u.A c c.time = none) :
    Good u b {c with time := nextTime (event u.O u.A c) c.time c.deadline} := by
  have hnot : ¬ready u.t (root b u.seed u.out) := by
    intro h
    have hev := (DistributedExecution.event_ready u.O u.A c c.time).mpr (Or.inr ⟨0,hg.runnable h⟩)
    simp [hquiet] at hev
  refine ⟨hg.valid,hg.memory,hg.forecast,hg.workers,hg.oracle,
    MultilevelClock.jump_timely _ _ _ _ c hc hg.timely, ?_, fun h => (hnot h).elim⟩
  intro hn
  obtain ⟨i,j,hj,hf⟩ := pending_due u b hg.valid sc hh hn hnot
  obtain ⟨τ,hτ,hnow,hev⟩ := pending_threshold u b c hg i j hj
  have hex := DistributedExecution.star_nextTime_exists (Network p) (evalPair u.g) u.P u.A c hc
  exact (DistributedExecution.nextTime_le_ready _ _ _ _ hex hnow hev).trans (hτ.trans hf)

lemma terminal_done (u : Context p) (b : Book p) (c : u.Exec) (hg : Good u b c)
    (sc : Timetable p u.t u.T) (hc : c.deadline = u.T) (hd : c.time = c.deadline)
    (hquiet : event u.O u.A c c.time = none) (j : ℕ) (hj : j < u.t.count)
    (hh : ∀ i, 0 < p.h i) : j ∈ b.done := by
  have noPending (i : Fin p.n) (k : ℕ) (hk : (b.pending i).job = some k) : False := by
    obtain ⟨τ,hτ,hnow,hev⟩ := pending_threshold u b c hg i k hk
    have hk' := (hg.valid.2.2.1 i k hk).1.trans_le hg.valid.1
    have ht := hτ.trans (sc.deadline k hk')
    have he : τ = c.time := le_antisymm (by simpa only [hd,hc] using ht) hnow
    simp [he,hquiet] at hev
  have hall : b.issued = u.t.count := by
    apply le_antisymm hg.valid.1
    by_contra! h
    have hr : ¬ready u.t (root b u.seed u.out) := by
      intro h
      have hev := (DistributedExecution.event_ready _ _ _ _).mpr (Or.inr ⟨0,hg.runnable h⟩)
      simp [hquiet] at hev
    obtain ⟨i,k,hk,_⟩ := pending_due u b hg.valid sc hh h hr
    exact noPending i k hk
  rcases hg.valid.2.2.2 j (hall ▸ hj) with h | h
  · exact h
  · exact (noPending _ _ h).elim

end LongTails.Proofs.MultilevelBookkeeping
