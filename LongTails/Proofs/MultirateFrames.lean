import LongTails.Proofs.MultirateCalendar
import LongTails.Proofs.MultiratePackets

namespace LongTails.Proofs.MultirateFrames

open DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Algorithms
open MultirateSchedule MultirateTrajectory MultirateCalendar
open LeonReservations (Frame posted consumed usedCount sends receives used)
open LeonTranscript (Op Trace)
open LeonExchangeReservations (sendFrame sent_list)

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)

noncomputable abbrev jobValues (i : Fin p.n) (u : ℕ) :=
  values p g s i u (x g s (anchor p i u))

noncomputable abbrev bits (i : Fin p.n) (u : ℕ) := packet p (jobValues g s i u)

noncomputable def record (i : Fin p.n) (u : ℕ) : LeonLinkLedger.Packet :=
  (stamp p (u * (period p i : ℕ)), LeonTranscript.wire (bits g s i u))

noncomputable def sampleFrame (i : Fin p.n) (u : ℕ) : Frame (network p) :=
  let beginTime := if u = 0 then 0 else stamp p (anchor p i u)
  let delivery := stamp p (u * (period p i : ℕ))
  ⟨fun _ => .sample (x g s (anchor p i u),batch p i) (jobValues g s i u),beginTime,delivery - transmission p,delivery⟩

noncomputable def posts (i : Fin p.n) (u : ℕ) (ids : List (Fin p.n)) : List (Frame (network p)) :=
  let row := sampleFrame g s i u
  ids.map (sendFrame row.finish row.delivery (fun _ _ => bits g s i u))

noncomputable def job (i : Fin p.n) (u : ℕ) :=
  sampleFrame g s i u :: posts g s i u (List.finRange p.n)

noncomputable def recvFrame (i : Fin p.n) (k : ℕ) (j : Fin p.n) : Frame (network p) :=
  let msg := record g s j (block p j k)
  ⟨fun _ => .receive j msg.2,enter p i (k+1),enter p i (k+1),msg.1⟩

noncomputable def requests (i : Fin p.n) (k : ℕ) : List (Frame (network p)) :=
  if k % (period p i : ℕ) = 0 ∧ k + period p i < K p then job g s i (block p i k + 1) else []

noncomputable def cycle (i : Fin p.n) (k : ℕ) : List (Frame (network p)) :=
  requests g s i k ++ (due p k).map (recvFrame g s i k)

noncomputable def workerRows (i : Fin p.n) (k : ℕ) :=
  job g s i 0 ++ (List.range k).flatMap (cycle g s i)

lemma prefix_succ (i : Fin p.n) (k : ℕ) : workerRows g s i (k+1) = workerRows g s i k ++ cycle g s i k := by
  simp [workerRows,List.range_succ,List.append_assoc]

lemma prefix_le (i : Fin p.n) {k m : ℕ} (h : k ≤ m) : workerRows g s i k <+: workerRows g s i m := by
  induction h with
  | refl => rfl
  | step h ih => rw [prefix_succ]; exact ih.trans (List.prefix_append _ _)

lemma record_eq (j : Fin p.n) (k : ℕ) : (record g s j (block p j k)).2 = packets g s k j :=
  (MultiratePackets.packet_eq g s k j).symm

lemma same_packet {k : ℕ} {i : Fin p.n} (hk : i ∉ due p (k+1)) : packets g s k i = packets g s (k+1) i := by
  have hm : (k+1) % (period p i : ℕ) ≠ 0 := by simpa [due] using hk
  rw [← record_eq,← record_eq]
  unfold block
  rw [Nat.succ_div_of_mod_ne_zero hm]

lemma launch_anchor (i : Fin p.n) (k : ℕ) (h : k % (period p i : ℕ) = 0) :
    anchor p i (block p i k + 1) = k := by
  simpa [anchor] using due_mul (p := p) i k h

lemma job_trace (i : Fin p.n) (u : ℕ) {next : LeonProtocol.Program (network p)} {os z}
    (h : Trace next os z) :
    Trace (publish p i (x g s (anchor p i u)) next) ((job g s i u).map (fun c => c.op i) ++ os) z := by
  apply Trace.sample
  simpa [posts,List.map_map,Function.comp_def,sendFrame] using
    LeonTranscript.post_trace (fun _ => bits g s i u) h (List.finRange p.n)

lemma cycle_trace (i : Fin p.n) (a b k : ℕ) (ks : List ℕ) (old : Table p)
    {os : List (Op (network p))} {z : Point p}
    (hold : ∀ j, j ∉ due p k → old j = packets g s k j)
    (h : Trace (program p i a b ks (modelAt g s (k+1)) (packets g s k)) os z) :
    Trace (program p i a b (k::ks) (modelAt g s k) old)
      ((cycle g s i k).map (fun c => c.op i) ++ os) z := by
  let next := fun data => program p i a b ks (update p (modelAt g s k) data) data
  have hn : Trace (next (packets g s k)) os z := h
  have hr := LeonTranscript.collect_trace (p := network p) (packets g s k)
    (next := next) hn (due p k) old hold
  have he : ((due p k).map (recvFrame g s i k)).map (fun c => c.op i) =
      (due p k).map (fun j => Op.receive j (packets g s k j)) := by
    simp [List.map_map,Function.comp_def,recvFrame,record_eq]
  simp only [program,cycle,List.map_append,List.append_assoc,he,requests]
  split_ifs with hl
  · have hj := job_trace g s i (block p i k + 1) hr
    rw [launch_anchor i k hl.1] at hj
    exact hj
  · exact hr

lemma full_trace (i : Fin p.n) (ab : Fin (K p) × Fin (K p)) (hL : smoothness p ≠ 0) :
    Trace (initialProgram p i ab.1 ab.2) ((workerRows g s i (K p)).map (fun c => c.op i))
      (output p (modelAt g s (K p)) ab) := by
  have tail (r k : ℕ) (old : Table p) (hkr : k+r = K p)
      (hold : ∀ j, j ∉ due p k → old j = packets g s k j) :
      let ks := List.range' k r
      Trace (program p i ab.1 ab.2 ks (modelAt g s k) old)
        ((ks.flatMap (cycle g s i)).map (fun c => c.op i)) (output p (modelAt g s (K p)) ab) := by
    induction r generalizing k old with
    | zero => simp only [Nat.add_zero] at hkr; subst k; exact Trace.done _
    | succ r ih =>
      have hh := ih (k+1) (packets g s k) (by omega) (fun _ hh => same_packet g s hh)
      simpa only [List.range'_succ, Nat.add_one, List.flatMap_cons, List.map_append] using
        cycle_trace g s i ab.1 ab.2 k _ old hold hh
  have h := tail (K p) 0 (fun _ => []) (by omega) (fun j hj => False.elim (hj (by simp [due])))
  rw [initialProgram,ite_eq_right hL,workerRows,List.map_append, List.range_eq_range']
  simpa only [anchor,Nat.zero_sub,Nat.zero_mul,x,modelAt,trajectory,LeonTrajectory.initial] using job_trace g s i 0 h

end LongTails.Proofs.MultirateFrames
