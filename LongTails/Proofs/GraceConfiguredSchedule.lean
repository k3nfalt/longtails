import LongTails.Proofs.GraceSampleSchedule

namespace LongTails.Proofs.GraceConfiguredSchedule

open DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms
open GraceRouting GraceBatch GracePacket GraceSgd
open DistributedBatchedSgd (trajectory encode decode batchMean estimate spacing)
open DistributedQuantization (reconstruct)
open GraceRoundSchedule (localPoint nextPoint combined code)
open GraceSampleSchedule (reply mean roundRows time)
open LeonReservations (Frame usedCount)
open LeonTranscript (Trace)
open GraceScheduleBlocks (Block shift)

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n}
variable (A : Routes p S r)

noncomputable abbrev X (S : Finset (Fin p.n)) (g : Point p → p.Ω → Point p) (s : Samples p) :=
  trajectory (statistical p) (tuning p S) (fun _ => g) s

lemma mean_active (g : Point p → p.Ω → Point p) (s : Samples p) (x : Point p)
    (k : ℕ) (i : Fin p.n) (hi : i ∈ S) :
    mean S g s x k i = batchMean (statistical p) (tuning p S) (fun _ => g) x k s i := by
  simp only [mean,LeonTrajectory.mean,reply,List.length_map,List.length_range,localPoint,ite_eq_left hi,
    ← List.sum_toFinset _ List.nodup_range,List.toFinset_range]
  rfl

lemma decode_grid (x m : Point p) : decode (statistical p) (tuning p S) x
    (encode (statistical p) (tuning p S) x m) =
    reconstruct (spacing (statistical p) (tuning p S) x) (grid p (tuning p S) x m) := by
  rw [DistributedBatchedSgd.decode_encode]
  unfold encode
  rw [DistributedQuantization.receive_message]
  rfl

lemma next_eq (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i) (g : Point p → p.Ω → Point p)
    (s : Samples p) (k : ℕ) :
    nextPoint S (X S g s k) (mean S g s (X S g s k) k) = X S g s (k+1) := by
  let x := X S g s k
  let cfg := tuning p S
  let m := mean S g s x k
  have hpos : 0 < B p := Nat.zero_lt_one.trans_le (le_max_left 1 _)
  have hs := (GraceBatchTuning.batches_spec hS hh).2
  have hB := (GraceBatchTuning.total_and_worker_time hS hh).1
  have he : combined S x m = ∑ i, ((cfg.batch i : ℝ) / (DistributedBatchedSgd.totalBatch (statistical p) cfg)) •
      decode (statistical p) cfg x (encode (statistical p) cfg x (batchMean (statistical p) cfg (fun _ => g) x k s i)) := by
    rw [combined,GracePacket.reconstruct_mean _ _ _ _ hpos hs.2,hB]
    refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ S) ?_ ?_
    · intro i hi
      change ((batches p S i : ℝ) / _) • _ = 0
      simp [hs.1 i (Finset.mem_sdiff.mp hi).2]
    · intro i hi
      simp only [cfg,code,localPoint,ite_eq_left hi,m,mean_active g s x k i hi,decode_grid]
      rfl
  change nextPoint S x m = x - (1 / (statistical p).L) • estimate (statistical p) cfg (fun _ => g) x k s
  unfold nextPoint estimate
  rw [he,decode_grid]

noncomputable def plan (g : Point p → p.Ω → Point p) (s : Samples p) (k n : ℕ) :=
  (List.range' k n).flatMap fun l => roundRows A g s (X S g s l) l (l * time A)

lemma counts (g : Point p → p.Ω → Point p) (s : Samples p) (k n : ℕ) (i : Fin p.n) :
    usedCount (plan A g s k n) i = n * batches p S i := by
  induction n generalizing k with
  | zero => simp [plan,usedCount]
  | succ n ih =>
    change usedCount (roundRows A g s _ k _ ++ plan A g s (k+1) n) i = _
    rw [GraceScheduleBlocks.used_append,GraceSampleSchedule.round_count,ih,Nat.succ_mul,Nat.add_comm]

lemma certified (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i)
    (hs : ∀ i j, p.G.Adj i j → p.b i j = p.b j i)
    (g : Point p → p.Ω → Point p) (s : Samples p) (k n : ℕ) :
    Block g (shift s (fun i => k * batches p S i)) (k * time A) ((k+n : ℕ) * time A)
      (plan A g s k n) := by
  induction n generalizing k with
  | zero => simpa [plan] using GracePhaseSchedule.empty_block g (shift s (fun i => k * batches p S i)) (k * time A)
  | succ n ih =>
    let f := roundRows A g s (X S g s k) k (k * time A)
    have hb := GraceSampleSchedule.round_block A hS hh hs g s (X S g s k) k (k * time A)
    have ht : (k : Time) * time A + time A = (k+1 : ℕ) * time A := by push_cast; ring
    rw [ht] at hb
    have hstreams : shift (shift s (fun i => k * batches p S i)) (usedCount f) =
        shift s (fun i => (k+1) * batches p S i) := by
      funext i j
      simp [shift,f,GraceSampleSchedule.round_count,Nat.succ_mul,Nat.add_assoc]
    have hn := ih (k+1)
    rw [← hstreams] at hn
    simpa [plan,List.range'_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,f] using
      GraceScheduleBlocks.append hb hn

lemma trace (hS : S.Nonempty) (hr : r ∈ S) (hh : ∀ i, 0 < p.h i)
    (g : Point p → p.Ω → Point p) (s : Samples p) (k n : ℕ) (i : Fin p.n) :
    Trace (program A i n (localPoint S (X S g s k) i))
      ((plan A g s k n).map fun c => c.op i) (localPoint S (X S g s (k+n)) i) := by
  induction n generalizing k with
  | zero => exact .done _
  | succ n ih =>
    have hn := ih (k+1)
    rw [← next_eq hS hh g s k] at hn
    have ht := GraceSampleSchedule.round_trace A hS hr hh g s (X S g s k) k n (k * time A) i hn
    simpa [plan,List.range'_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

lemma round_query (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i)
    (g : Point p → p.Ω → Point p) (s : Samples p) (x : Point p) (l : ℕ) (a : Time)
    (pre : List (Frame p.base)) (c : Frame p.base) (rest : List (Frame p.base))
    (he : roundRows A g s x l a = pre ++ c::rest) (i : Fin p.n) (query vals)
    (ho : c.op i = .sample query vals) :
    usedCount pre i = 0 ∧ query.1 = x ∧ (query.2 : ℕ) = batches p S i := by
  cases pre with
  | nil =>
    have hc := (List.cons.inj he).1
    rw [← hc] at ho
    by_cases h : 0 < batches p S i
    · have hi : i ∈ S := by by_contra hn; simp [(GraceBatchTuning.batches_spec hS hh).2.1 i hn] at h
      simp [GraceSampleSchedule.sampleRow,h,localPoint,hi] at ho
      obtain ⟨rfl,rfl⟩ := ho
      exact ⟨rfl,rfl,rfl⟩
    · simp [GraceSampleSchedule.sampleRow,h] at ho
  | cons f pre =>
    have hx := (List.cons.inj he).2
    have hz := GraceRoundSchedule.exchange_samples A (a + batchTime p S) x (mean S g s x l) i
    rw [hx] at hz
    change usedCount (pre ++ c::rest) i = 0 at hz
    rw [GraceScheduleBlocks.used_append] at hz
    change _ + (LeonReservations.used c i + _) = 0 at hz
    simp [LeonReservations.used,ho] at hz

lemma sample_position (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i)
    (g : Point p → p.Ω → Point p) (s : Samples p) (k n : ℕ) (pre : List (Frame p.base))
    (c : Frame p.base) (rest : List (Frame p.base)) (he : plan A g s k n = pre ++ c::rest)
    (i : Fin p.n) (query vals) (ho : c.op i = .sample query vals) :
    ∃ l < n, usedCount pre i = l * batches p S i ∧ query.1 = X S g s (k+l) ∧
      (query.2 : ℕ) = batches p S i := by
  induction n generalizing k pre with
  | zero => simp [plan] at he
  | succ n ih =>
    change roundRows A g s _ k _ ++ plan A g s (k+1) n = pre ++ c::rest at he
    obtain ⟨tail,hf,_⟩ | ⟨mid,hm,rfl⟩ := GraceScheduleBlocks.locate _ _ _ _ _ he
    · obtain ⟨hu,hq,hb⟩ := round_query A hS hh g s _ k _ pre c tail hf i query vals ho
      exact ⟨0,Nat.zero_lt_succ _,by simpa using hu,by simpa using hq,hb⟩
    · obtain ⟨l,hl,hu,hq,hb⟩ := ih (k+1) mid hm
      exact ⟨l+1,by omega,by rw [GraceScheduleBlocks.used_append,GraceSampleSchedule.round_count,hu,
        Nat.succ_mul,Nat.add_comm],by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq,hb⟩

end LongTails.Proofs.GraceConfiguredSchedule
