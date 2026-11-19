import LongTails.Proofs.MultirateFrames
import LongTails.Proofs.LocalReservations

namespace LongTails.Proofs.MultirateLedger

open DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Algorithms.MultirateSchedule
open MultirateCalendar MultirateFrames
open LeonReservations (Frame posted consumed usedCount sends receives used)
open LeonExchangeReservations (sendFrame sent_list)

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)

lemma post_used (i : Fin p.n) (u : ℕ) (ids : List (Fin p.n)) :
    usedCount (posts g s i u ids) i = 0 := by
  induction ids <;> simp_all [posts,usedCount,used,sendFrame]

lemma post_consumed (i j : Fin p.n) (u : ℕ) (ids : List (Fin p.n)) :
    consumed (posts g s i u ids) j i = [] := by
  induction ids <;> simp_all [posts,consumed,receives,sendFrame]

lemma post_sent (i j : Fin p.n) (u : ℕ) (ids : List (Fin p.n)) (hn : ids.Nodup) :
    posted (posts g s i u ids) i j = if j ∈ ids then [record g s i u] else [] :=
  sent_list _ _ _ _ hn _ _

lemma recv_effect (i j : Fin p.n) (k : ℕ) (ids : List (Fin p.n)) (hn : ids.Nodup) :
    let a := ids.map (recvFrame g s i k)
    usedCount a i = 0 ∧ posted a i j = [] ∧
      consumed a j i = if j ∈ ids then [record g s j (block p j k)] else [] := by
  induction ids with
  | nil => simp [usedCount,posted,consumed]
  | cons l ls ih =>
    obtain ⟨hl,hn'⟩ := List.nodup_cons.mp hn
    obtain ⟨h₁,h₂,h₃⟩ := ih hn'
    let tail := ls.map (recvFrame g s i k)
    change 0 + usedCount tail i = 0 ∧ [] ++ posted tail i j = [] ∧
      (if l = j then [((record g s l (block p l k)).1,(record g s l (block p l k)).2)] else []) ++
        consumed tail j i = _
    rw [h₁,h₂,h₃]
    by_cases he : j = l
    · subst l; simp [hl]
    · simp [he,Ne.symm he]

lemma job_effect (i j : Fin p.n) (u : ℕ) :
    usedCount (job g s i u) i = batch p i ∧ posted (job g s i u) i j = [record g s i u] ∧
      consumed (job g s i u) j i = [] := by
  have hx := post_sent g s i j u (List.finRange p.n) (List.nodup_finRange _)
  simp only [List.mem_finRange,ite_true] at hx
  have hu := post_used g s i u (List.finRange p.n)
  have hc := post_consumed g s i j u (List.finRange p.n)
  change (batch p i : ℕ) + usedCount (posts g s i u (List.finRange p.n)) i = _ ∧
    [] ++ posted (posts g s i u (List.finRange p.n)) i j = _ ∧
    [] ++ consumed (posts g s i u (List.finRange p.n)) j i = _
  simp only [hx,hu,hc,Nat.add_zero,List.nil_append,and_self]

lemma due_nodup (k : ℕ) : (due p k).Nodup := (List.nodup_finRange _).filter _

lemma counters (i j : Fin p.n) (k : ℕ) :
    usedCount (workerRows g s i k) i = issued p i k * (batch p i : ℕ) ∧
      posted (workerRows g s i k) i j = (List.range (issued p i k)).map (record g s i) ∧
      consumed (workerRows g s i k) j i = (List.range (countBefore p j k)).map (record g s j) := by
  induction k with
  | zero =>
    simpa [workerRows,issued_zero,countBefore] using job_effect g s i j 0
  | succ k ih =>
    rcases ih with ⟨hc,hs,hr⟩
    have hrec := recv_effect g s i j k (due p k) (due_nodup k)
    dsimp only at hrec
    rw [prefix_succ,cycle]
    simp only [usedCount,List.map_append,List.sum_append,posted,consumed,List.flatMap_append] at *
    simp only [hrec.1,hrec.2.1,hrec.2.2,List.append_nil,Nat.add_zero, hc,hs,hr,next_issued,next_count]
    have hj : (List.range (countBefore p j k)).map (record g s j) ++
        (if j ∈ due p k then [record g s j (block p j k)] else []) =
      (List.range (countBefore p j k + if k % (period p j : ℕ) = 0 then 1 else 0)).map (record g s j) := by
      by_cases he : k % (period p j : ℕ) = 0
      · simp [due,he,List.range_succ,before_eq j k]
      · simp [due,he]
    by_cases he : k % (period p i : ℕ) = 0 ∧ k + period p i < K p
    · have hjb := job_effect g s i j (block p i k + 1)
      simp only [usedCount,posted,consumed] at hjb
      simp [requests,he,hjb.1,hjb.2.1,hjb.2.2, List.range_succ, Nat.add_one_mul, issued_launch i k he,hj]
    · simp [requests,he,hj]

end LongTails.Proofs.MultirateLedger
