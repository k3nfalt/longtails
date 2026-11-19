import LongTails.Proofs.MultirateReservations

namespace LongTails.Proofs.MultirateSchedule

open DistributedTemplate
open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateTrajectory LongTails.Algorithms.MultirateProtocol
open LongTails.Algorithms.MultirateCalendar
open MultirateReservations MultirateDrift

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {s : Samples p} {out : Point p} {T : Time}

def Can (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (out : Point p) (T : Time)
    (prog : Program p) (book : Book p) (t : Time) :=
  ∃ n t', t ≤ t' ∧ Certified g s out T n prog book t'

lemma can_earlier {prog : Program p} {book : Book p} {t u : Time}
    (h : t ≤ u) (hc : Can g s out T prog book u) : Can g s out T prog book t := by
  obtain ⟨n, t', hu, hc⟩ := hc
  exact ⟨n, t', h.trans hu, hc⟩

def replace {ι α : Type*} [DecidableEq ι] (ls : List ι) (vals base : ι → α) :=
  fun i => if i ∈ ls then vals i else base i

lemma replace_nil {ι α : Type*} [DecidableEq ι] (v b : ι → α) : replace [] v b = b := by
  funext j
  simp [replace]

lemma replace_tail {ι α : Type*} [DecidableEq ι] (v : ι → α) (b : ι → α) (i : ι) (rest : List ι) :
    replace rest v (Function.update b i (v i)) = replace (i::rest) v b := by
  funext j
  by_cases h : j = i <;> by_cases hj : j ∈ rest <;> simp [replace, h, hj]

lemma sends (ls : List (Fin p.n)) (nd : ls.Nodup) (bits : List Bool)
    (hl : bits.length = payload p) (e : Fin p.n → ℕ) (t : Time) (next : Program p) (book : Book p)
    (hb : ∀ i ∈ ls, book i = .free (e i))
    (hc : Can g s out T next (replace ls (fun i => .pending ⟨e i,bits,t⟩) book) t) :
    Can g s out T (sendAll bits next ls) book t := by
  induction ls generalizing book with
  | nil => simpa [replace_nil,sendAll] using hc
  | cons i rest ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp nd
    let v := fun j => Reservation.pending (p := p) ⟨e j, bits, t⟩
    have hp : ∀ j ∈ rest, Function.update book i (v i) j = .free (e j) := by
      intro j hj
      have hn : j ≠ i := fun h => hnot (h ▸ hj)
      rw [Function.update_of_ne hn]
      exact hb _ (List.mem_cons_of_mem _ hj)
    have hnext := ih hnd _ hp (by change Can g s out T next (replace rest v (Function.update book i (v i))) t; rw [replace_tail]; exact hc)
    obtain ⟨n,u,htu,hs⟩ := hnext
    exact ⟨n+1,t,le_rfl,Certified.post (hb _ (by simp)) hl htu hs⟩

lemma collects (ls : List (Fin p.n)) (nd : ls.Nodup) (j : Fin p.n → Job p)
    (t : Time) (next : (Fin p.n → Code p) → Program p) (book : Book p) (cache : Fin p.n → Code p)
    (hb : ∀ i ∈ ls, book i = .pending (j i))
    (ht : ∀ i ∈ ls, (j i).posted + span p i ≤ t)
    (hc : Can g s out T (next (replace ls (fun i => Algorithms.MultirateTrajectory.read p (jobReply g s i (j i))) cache))
      (replace ls (fun i => .free ((j i).number+1)) book) t) :
    Can g s out T (collectAll next ls cache) book t := by
  induction ls generalizing book cache with
  | nil => simpa [replace_nil,collectAll] using hc
  | cons i rest ih =>
    obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp nd
    let v := fun w => Reservation.free (p := p) ((j w).number+1)
    let r := fun w => Algorithms.MultirateTrajectory.read p (jobReply g s w (j w))
    have hp : ∀ w ∈ rest, Function.update book i (v i) w = .pending (j w) := by
      intro w hw
      rw [Function.update_of_ne (show w ≠ i from fun h => hnot (h ▸ hw))]
      exact hb _ (List.mem_cons_of_mem _ hw)
    have hnext := ih hnd _ (Function.update cache i (r i)) hp (fun w hw => ht _ (List.mem_cons_of_mem _ hw))
      (by change Can g s out T (next (replace rest r (Function.update cache i (r i)))) (replace rest v (Function.update book i (v i))) t; rw [replace_tail, replace_tail]; exact hc)
    obtain ⟨n,u,htu,hs⟩ := hnext
    exact ⟨n+1,t,le_rfl,Certified.collect (hb _ (by simp)) (ht _ (by simp)) htu hs⟩

noncomputable def ticket (p : Params) (i : Fin p.n) : ℕ → ℕ
  | 0 => 0
  | k+1 => epoch p i k + 1

lemma ticket_eq (i : Fin p.n) (k : ℕ) :
    ticket p i k = if k % period p i = 0 then epoch p i k else epoch p i k + 1 := by
  cases k with
  | zero => simp [ticket, epoch]
  | succ k =>
    by_cases h : (k+1) % period p i = 0
    · simp [ticket, epoch, h, Nat.succ_div_of_mod_eq_zero h]
    · simp [ticket, epoch, h, Nat.succ_div_of_mod_ne_zero h]

noncomputable def jobAt (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (i : Fin p.n) (e : ℕ) : Job p :=
  ⟨e, queryPacket p (point g s ((e-1) * period p i)), if e = 0 then 0 else frame p ((e-1) * period p i)⟩

noncomputable def before (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (k : ℕ) : Book p :=
  fun i => if ticket p i k * period p i < steps p then .pending (jobAt g s i (ticket p i k)) else .free (ticket p i k)

noncomputable def code (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (k : ℕ) (i : Fin p.n) :=
  Algorithms.MultirateTrajectory.read p (message p g s k i (trajectory p g s k))

lemma code_epoch (k : ℕ) (i : Fin p.n) :
    Algorithms.MultirateTrajectory.read p (jobReply g s i (jobAt g s i (epoch p i k))) = code g s k i := by
  unfold code message input jobAt
  rw [read_reply, past_point g s (MultirateCalendar.origin_le p i k)]
  rfl

lemma due_iff (k : ℕ) (i : Fin p.n) : i ∈ due p k ↔ k % period p i = 0 := by simp [due]
lemma due_nodup (p : Params) (k : ℕ) : (due p k).Nodup := (List.nodup_finRange _).filter _

lemma exact_epoch {k : ℕ} {i : Fin p.n} (h : i ∈ due p k) : epoch p i k * period p i = k := by
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ((due_iff k i).mp h))

lemma job_timely (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) {k : ℕ} {i : Fin p.n} (h : i ∈ due p k) :
    (jobAt g s i (epoch p i k)).posted + span p i ≤ frame p k := by
  have he := exact_epoch h
  generalize hn : epoch p i k = e at *
  cases e with
  | zero => simp only [Nat.zero_mul] at he; subst k; simpa [jobAt] using first_ready p i
  | succ e =>
    simp only [jobAt, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one]
    simpa only [← he, Nat.succ_mul] using frame_ready hh hL i (e * period p i)

noncomputable def again (p : Params) (k : ℕ) := (due p k).filter fun i => k + period p i < steps p

lemma cache_next (k : ℕ) {i : Fin p.n} (h : i ∉ due p (k+1)) : code g s k i = code g s (k+1) i := by
  have hm : (k+1) % period p i ≠ 0 := fun he => h ((due_iff _ _).mpr he)
  rw [← code_epoch, ← code_epoch]
  simp only [epoch, Nat.succ_div_of_mod_ne_zero hm]

noncomputable def afterCollect (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (k : ℕ) :=
  replace (due p k) (fun i => Reservation.free (epoch p i k + 1)) (before g s k)

lemma after_posts (k : ℕ) :
    replace (again p k) (fun i => Reservation.pending ⟨epoch p i k+1, queryPacket p (point g s k), frame p k⟩)
      (afterCollect g s k) = before g s (k+1) := by
  funext i
  by_cases h : i ∈ due p k
  · have he := exact_epoch h
    by_cases hc : k + period p i < steps p
    · simp [replace, again, h, hc, before, ticket, jobAt, Nat.add_mul, he]
    · simp [replace, again, h, hc, afterCollect, before, ticket, Nat.add_mul, he]
  · have hm : k % period p i ≠ 0 := fun he => h ((due_iff k i).mpr he)
    have ht : ticket p i k = epoch p i k + 1 := by rw [ticket_eq, ite_eq_right hm]
    simp [replace, again, h, afterCollect, before, ht, show ticket p i (k+1) = epoch p i k + 1 from rfl]

lemma schedule_can (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) (a b k m : ℕ)
    (hs : k+m = steps p) (cache : Fin p.n → Code p) (hc : ∀ i ∉ due p k, cache i = code g s k i) :
    Can g s (output p (trajectory p g s (steps p)) a b) (finishTime p)
      (schedule p a b (List.range' k m) (trajectory p g s k) cache) (before g s k) (frame p k) := by
  induction m generalizing k cache with
  | zero =>
    have he : k = steps p := by omega
    subst k
    exact ⟨0,finishTime p,le_rfl,Certified.done _ _ le_rfl⟩
  | succ m ih =>
    have hk : k < steps p := by omega
    have hnext := ih (k+1) (by omega) (code g s k) (fun _ hn => cache_next k hn)
    simp only [List.range'_succ, schedule]
    apply collects (due p k) (due_nodup p k) (fun i => jobAt g s i (epoch p i k))
    · intro i hi
      simp only [before, ticket_eq i k, (due_iff k i).mp hi, ite_true, exact_epoch hi, ite_eq_left hk]
    · exact fun _ hi => job_timely hh hL hi
    · have he : replace (due p k) (fun i => Algorithms.MultirateTrajectory.read p
          (jobReply g s i (jobAt g s i (epoch p i k)))) cache = code g s k := by
        funext i
        by_cases hi : i ∈ due p k <;> simp [replace, hi, code_epoch, hc i]
      rw [he]
      apply sends (again p k) ((due_nodup p k).filter _) _ (query_length _) (fun i => epoch p i k + 1)
      · intro i hi
        have hd : i ∈ due p k := (List.mem_filter.mp hi).1
        simp [replace, hd, jobAt]
      · change Can _ _ _ _ _ (replace (again p k) _ (afterCollect g s k)) _
        rw [after_posts]
        exact can_earlier (frame_mono p (Nat.le_succ k)) hnext

lemma start_can (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) (a b : ℕ) :
    Can g s (output p (trajectory p g s (steps p)) a b) (finishTime p)
      (start p a b) (fun _ => .free 0) 0 := by
  unfold start
  apply sends _ (List.nodup_finRange _) _ (query_length _) (fun _ => 0)
  · exact fun _ _ => rfl
  · have h := schedule_can (g := g) (s := s) hh hL a b 0 (steps p) (by omega) (fun _ => 0)
      (by intro i hi; exact (hi ((due_iff 0 i).mpr (Nat.zero_mod _))).elim)
    rw [List.range_eq_range']
    have hb : replace (List.finRange p.n) (fun _ => Reservation.pending (p := p) ⟨0,queryPacket p p.x0,0⟩)
        (fun _ => .free 0) = before g s 0 := by
      funext i
      simp [replace, before, ticket, jobAt, MultirateCalendar.steps_pos, point, trajectory, Algorithms.MultirateTrajectory.initial]
    rw [hb]
    exact can_earlier zero_le h

end LongTails.Proofs.MultirateSchedule
