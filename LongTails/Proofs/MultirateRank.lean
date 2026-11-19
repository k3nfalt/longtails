import LongTails.Proofs.MultirateInvariants

open MeasureTheory

namespace LongTails.Proofs.MultirateRank

open DistributedTemplate LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateProtocol LongTails.Algorithms.MultirateAllocation
open MultirateReservations MultirateMachine MultirateEvents MultirateInteraction MultirateProgress MultirateInvariants

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
    {s : Samples p} {D u : Time} {x y : Config p} {n : ℕ} {out : Point p}

noncomputable def effort (b : Table p) := ∑ i, busy p i (b i)
noncomputable def capacity (p : Params) := (∑ i, (2 * batch p i + 3)) + 1
noncomputable def awake (D : Time) (w : Fin (p.n+1) → Time) := ∑ v, if w v ≤ D then 1 else 0
noncomputable def rank (D : Time) (x : Config p) (n : ℕ) :=
  (n * capacity p + effort x.table) * (p.n + 2 : ℕ) + awake D x.wakes

lemma effort_lt (b : Table p) : effort b < capacity p := by
  apply Nat.lt_succ_of_le
  apply Finset.sum_le_sum
  intro i _
  cases b i <;> simp only [busy] <;> omega

lemma awake_lt (w : Fin (p.n+1) → Time) : awake D w < (p.n+2 : ℕ) := by
  change (∑ v, if w v ≤ D then 1 else 0) < _
  have he : (∑ v : Fin (p.n+1), 1 : ℕ) = p.n+1 := by simp
  apply Nat.lt_succ_of_le
  apply le_trans _ he.le
  apply Finset.sum_le_sum
  intro v _
  split <;> omega

lemma radix {a b c d B : ℕ} (h : a < c) (hb : b < B) : a*B+b < c*B+d := by
  have h' := Nat.mul_le_mul_right B h
  rw [Nat.succ_mul] at h'
  omega

lemma lower_step {m : ℕ} (h : m < n) : rank D y m < rank D x n :=
  radix (radix h (effort_lt _)) (awake_lt _)

lemma lower_work (h : effort y.table < effort x.table) : rank D y n < rank D x n :=
  radix (Nat.add_lt_add_left h _) (awake_lt _)

lemma sum_decreases {ι α : Type*} [Fintype ι] [DecidableEq ι] (f : ι → α → ℕ)
    (b : ι → α) (i : ι) (z : α) (h : f i z < f i (b i)) :
    (∑ j, f j (Function.update b i z j)) < ∑ j, f j (b j) := by
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j = i
    · subst j; simpa using h.le
    · rw [Function.update_of_ne hj]
  · exact ⟨i,Finset.mem_univ i,by simpa using h⟩

lemma lower_sleep (i : Fin (p.n+1)) (h : x.wakes i ≤ D) :
    rank D (tick x i (D+1) x.table x.program) n < rank D x n := by
  apply Nat.add_lt_add_left
  exact sum_decreases (fun _ (t : Time) => if t ≤ D then 1 else 0) x.wakes i (D+1) (by simp [h])

lemma lower_cell {i : Fin p.n} {v : Fin (p.n+1)} {w : Time} {cell : Cell p}
    (h : busy p i cell < busy p i (x.table i)) :
    rank D (tick x v w (revised x i cell) x.program) n < rank D x n :=
  lower_work (sum_decreases (busy p) x.table i cell h)

lemma book_same {i : Fin p.n} {cell : Cell p} (h : booking cell = booking (x.table i)) :
    (fun j => booking (revised x i cell j)) = fun j => booking (x.table j) := by
  funext j
  by_cases hj : j = i <;> simp [revised,hj,h]

lemma preserved {v e os} (hm : Move g P s D u x v e os y) (h : Valid g s out D x n u) :
    ∃ m t, Valid g s out D y m t ∧ rank D y m < rank D x n := by
  have hr := responsive_next hm h.responsive
  have hsafe := safe_next hm h
  have cp := h.cert
  have same (m t b prog v w) (hc : Certified g s out D m prog (fun j => booking (b j)) t)
      (hnow : 0 < m → x.now ≤ t) (he : y = tick x v w b prog) :
      Valid g s out D y m t := by
    subst y
    exact ⟨hc,h.time,h.deadline,hnow,hsafe,hr⟩
  cases hm with
  | sleep i hw _ =>
    exact ⟨n,u,same n u _ _ _ _ cp h.current rfl,lower_sleep _ (hw.trans (h.time.trans h.deadline))⟩
  | post i bits next e hp hf hw hb =>
    rw [hp] at cp
    cases cp with
    | @post m _ _ _ _ _ t e' hfree _ htime hc =>
      have he : e = e' := by simpa only [hf,booking,Reservation.free.injEq] using hfree
      subst e'
      have hb' : (fun j => booking (revised x i (.down ⟨e,bits,u⟩ (x.now+packetDelay p)) j)) =
          Function.update (fun j => booking (x.table j)) i (.pending ⟨e,bits,u⟩) :=
        map_update (fun _ => booking) _ _ _
      rw [← hb'] at hc
      exact ⟨m,t,same m t _ _ _ _ hc (fun _ => (h.current (by omega)).trans htime) rfl,lower_step (by omega)⟩
  | take i job next hp hf hw =>
    rw [hp] at cp
    cases cp with
    | @collect m _ _ _ _ t job' hjob _ htime hc =>
      have he : job = job' := by simpa only [hf,booking,Reservation.pending.injEq] using hjob
      subst job'
      have hb' : (fun j => booking (revised x i (.free (job.number+1)) j)) =
          Function.update (fun j => booking (x.table j)) i (.free (job.number+1)) :=
        map_update (fun _ => booking) _ _ _
      rw [← hb'] at hc
      exact ⟨m,t,same m t _ _ _ _ hc (fun _ => (h.current (by omega)).trans htime) rfl,lower_step (by omega)⟩
  | evaluate i job j t hc hw hj | reply i job t hc hw | down i job t hc ht | up i job t hc ht | computed i job j t hc ht =>
    refine ⟨n,u,same n u _ _ _ _ ?_ h.current rfl,lower_cell ?_⟩
    · rw [book_same (by rw [hc]; rfl)]
      exact cp
    · simp only [hc,busy]
      first | omega | have hj := (h.safe i).1; rw [hc] at hj; obtain ⟨hj,_⟩ := hj; omega

end LongTails.Proofs.MultirateRank
