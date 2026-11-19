import LongTails.Proofs.MultirateLedger

namespace LongTails.Proofs.MultirateDeliveries

open DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Algorithms.MultirateSchedule
open MultirateCalendar MultirateFrames MultirateLedger
open LeonReservations (Frame posted consumed usedCount)

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)

def Witness (all : List (Frame (network p))) (i j : Fin p.n) (u : ℕ) : Prop :=
  ∃ pre row rem, all = pre ++ row :: rem ∧ row.finish ≤ stamp p (u * (period p i : ℕ)) ∧
    (List.range (u+1)).map (record g s i) <+: posted (pre ++ [row]) i j

lemma job_witness (i j : Fin p.n) (u : ℕ) (prior all : List (Frame (network p)))
    (hp : prior ++ job g s i u <+: all)
    (hs : posted prior i j = (List.range u).map (record g s i)) : Witness g s all i j u := by
  let work := job g s i u
  have hn : work ≠ [] := by simp [work,job]
  let last := work.getLast hn
  have he : work.dropLast ++ [last] = work := List.dropLast_append_getLast hn
  have hh : last ∈ work := List.getLast_mem hn
  have hl : last.finish ≤ stamp p (u * (period p i : ℕ)) := by
    change last ∈ sampleFrame g s i u :: posts g s i u (List.finRange p.n) at hh
    rcases List.mem_cons.mp hh with hl | hm
    · rw [hl]; exact tsub_le_self
    · obtain ⟨id,_,hx⟩ := List.mem_map.mp hm
      rw [← hx]
      exact tsub_le_self
  obtain ⟨rest,hrest⟩ := hp
  refine ⟨prior ++ work.dropLast,last,rest,?_,hl,?_⟩
  · calc
      all = (prior ++ work) ++ rest := hrest.symm
      _ = (prior ++ (work.dropLast ++ [last])) ++ rest := by rw [he]
      _ = _ := by simp [List.append_assoc]
  · rw [List.append_assoc,he]
    change _ <+: posted (prior ++ job g s i u) i j
    rw [show posted (prior ++ job g s i u) i j = posted prior i j ++ posted (job g s i u) i j from List.flatMap_append,hs,(job_effect g s i j u).2.1,List.range_succ,List.map_append]
    rfl

lemma issued_witness (i j : Fin p.n) (k : ℕ) (hk : k ≤ K p) (u : ℕ) (hu : u < issued p i k) :
    Witness g s (workerRows g s i (K p)) i j u := by
  induction k generalizing u with
  | zero =>
    rw [issued_zero] at hu
    obtain rfl : u = 0 := by omega
    apply job_witness g s i j 0 []
    · simp [workerRows]
    · rfl
  | succ k ih =>
    by_cases hl : k % (period p i : ℕ) = 0 ∧ k + period p i < K p
    · rw [next_issued,ite_eq_left hl] at hu
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hu) with he | he
      · exact ih (by omega) _ he
      · subst u
        have hi := issued_launch i k hl
        rw [hi]
        apply job_witness g s i j _ (workerRows g s i k)
        · apply List.IsPrefix.trans _ (prefix_le g s i hk)
          rw [prefix_succ,cycle,requests,ite_eq_left hl,← List.append_assoc]
          exact List.prefix_append _ _
        · rw [(counters g s i j k).2.1,hi]
    · rw [next_issued,ite_eq_right hl,Nat.add_zero] at hu
      exact ih (by omega) _ hu

lemma received_witness (i j : Fin p.n) (k : ℕ) (hk : k < K p) (hdue : k % (period p j : ℕ) = 0)
    (ht : 0 < tick p) :
    let msg := record g s j (block p j k)
    msg.1 ≤ enter p i (k+1) ∧ ∃ pre row rem, workerRows g s j (K p) = pre ++ row :: rem ∧
      row.finish < enter p i (k+1) ∧ (List.range (countBefore p j k)).map (record g s j) ++ [msg] <+:
        posted (pre ++ [row]) j i := by
  have hb := before_mono (p := p) j (show k+1 ≤ K p by omega)
  rw [before_succ] at hb
  have hu : block p j k < issued p j (K p) := by unfold issued; omega
  obtain ⟨pre,row,rem,he,htime,hpre⟩ := issued_witness g s j i (K p) le_rfl _ hu
  have hd := due_mul (p := p) j k hdue
  rw [hd] at htime
  have hcap : stamp p k < enter p i (k+1) := by
    apply stamp_strict ht
    exact lt_min hk (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (before_bounds i (k+1)).1)
  refine ⟨?_,pre,row,rem,he,htime.trans_lt hcap,?_⟩
  · change stamp p (block p j k * (period p j : ℕ)) ≤ _
    rw [hd]; exact hcap.le
  · simpa only [before_eq j k,ite_eq_left hdue,Nat.add_zero,List.range_succ,List.map_append,
      List.map_cons,List.map_nil] using hpre

end LongTails.Proofs.MultirateDeliveries
