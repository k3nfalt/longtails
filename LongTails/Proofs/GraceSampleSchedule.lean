import LongTails.Proofs.GraceRoundSchedule

namespace LongTails.Proofs.GraceSampleSchedule

open DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms
open GraceSgd GraceBatch GraceRouting
open LeonReservations (Frame sends receives used usedCount posted consumed due)
open GraceScheduleBlocks (Block shift)
open GraceRoundSchedule (localPoint nextPoint exchanges)
open LeonTranscript (Trace Op)

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n}
variable (A : Routes p S r)

noncomputable def reply (S : Finset (Fin p.n)) (g : Point p → p.Ω → Point p) (s : Samples p)
    (x : Point p) (k : ℕ) (i : Fin p.n) := (List.range (batches p S i)).map fun j =>
  g (localPoint S x i) (s i (k * batches p S i + j))

noncomputable def mean (S : Finset (Fin p.n)) (g : Point p → p.Ω → Point p) (s : Samples p)
    (x : Point p) (k : ℕ) (i : Fin p.n) := LeonTrajectory.mean p.base (reply S g s x k i)

noncomputable def sampleRow (S : Finset (Fin p.n)) (g : Point p → p.Ω → Point p) (s : Samples p)
    (x : Point p) (k : ℕ) (a : Time) : Frame p.base :=
  ⟨fun i => if h : 0 < batches p S i then
    .sample (localPoint S x i, ⟨batches p S i,h⟩) (reply S g s x k i) else .send i [],
    a, a + batchTime p S, a + batchTime p S⟩

lemma singleton_row {α : Type*} {f c : α} {pre rest : List α} (he : [f] = pre ++ c :: rest) :
    pre = [] ∧ c = f ∧ rest = [] := by
  cases pre with
  | nil => simpa [eq_comm] using he
  | cons i l =>
    have ht := congrArg List.length he
    simp at ht

lemma sample_block (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i) (g : Point p → p.Ω → Point p)
    (s : Samples p) (x : Point p) (k : ℕ) (a : Time) :
    Block g (shift s (fun i => k * batches p S i)) a (a + batchTime p S) [sampleRow S g s x k a] := by
  let f := sampleRow S g s x k a
  have loc {pre c rest} (he : [f] = pre ++ c :: rest) := singleton_row he
  constructor
  · constructor
    · intro pre c rest he
      obtain ⟨rfl,rfl,rfl⟩ := loc he
      exact ⟨le_self_add,le_rfl⟩
    · intro c hc
      obtain rfl : c = f := List.mem_singleton.mp hc
      rfl
    · intro pre c rest he i q vals ho
      obtain ⟨rfl,rfl,rfl⟩ := loc he
      by_cases h : 0 < batches p S i
      · simp [f,sampleRow,h] at ho
        obtain ⟨rfl,rfl⟩ := ho
        exact ⟨add_le_add_right ((GraceBatchTuning.total_and_worker_time hS hh).2 i) a,by simp [reply,shift,usedCount]⟩
      · simp [f,sampleRow,h] at ho
    · intro pre c rest he i j bits ho
      obtain ⟨rfl,rfl,rfl⟩ := loc he
      by_cases h : 0 < batches p S i
      · simp [f,sampleRow,h] at ho
      · simp [f,sampleRow,h] at ho
        obtain ⟨rfl,rfl⟩ := ho
        exact ⟨Or.inl rfl,by simp [f,sampleRow,GraceReservations.duration], by simp [posted]⟩
    · intro pre c rest he j i bits ho
      obtain ⟨rfl,rfl,rfl⟩ := loc he
      by_cases h : 0 < batches p S j <;> simp [f,sampleRow,h] at ho
  · exact le_self_add
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    rfl
  · intro c hc
    obtain rfl := List.mem_singleton.mp hc
    rfl
  · intro c hc i bits ho
    obtain rfl := List.mem_singleton.mp hc
    by_cases h : 0 < batches p S i <;> simp [sampleRow,h] at ho
  · intro i j hne
    by_cases h : 0 < batches p S i <;> by_cases h' : 0 < batches p S j <;>
      simp [sampleRow,posted,consumed,sends,receives,h,h',hne]

lemma sample_count (g : Point p → p.Ω → Point p) (s : Samples p) (x : Point p)
    (k : ℕ) (a : Time) (i : Fin p.n) :
    used (sampleRow S g s x k a) i = batches p S i := by
  by_cases h : 0 < batches p S i
  · simp [used,sampleRow,h]
  · simp [used,sampleRow,Nat.eq_zero_of_not_pos h]

noncomputable def time (A : Routes p S r) := batchTime p S + GraceRoundSchedule.halfTime A + GraceRoundSchedule.halfTime A

noncomputable def roundRows (g : Point p → p.Ω → Point p) (s : Samples p) (x : Point p)
    (k : ℕ) (a : Time) :=
  sampleRow S g s x k a :: exchanges A (a + batchTime p S) x (mean S g s x k)

lemma round_block (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i)
    (hs : ∀ i j, p.G.Adj i j → p.b i j = p.b j i)
    (g : Point p → p.Ω → Point p) (s : Samples p) (x : Point p) (k : ℕ) (a : Time) :
    Block g (shift s (fun i => k * batches p S i)) a (a + time A) (roundRows A g s x k a) := by
  simpa only [time,← add_assoc, List.singleton_append,roundRows] using
    GraceScheduleBlocks.append (sample_block hS hh g s x k a)
      (GraceRoundSchedule.exchange_block A g _ (a + batchTime p S) x (mean S g s x k) hs)

lemma round_count (g : Point p → p.Ω → Point p) (s : Samples p) (x : Point p)
    (k : ℕ) (a : Time) (i : Fin p.n) : usedCount (roundRows A g s x k a) i = batches p S i := by
  change used (sampleRow S g s x k a) i + usedCount (exchanges A _ x _) i = _
  rw [sample_count,GraceRoundSchedule.exchange_samples,add_zero]

lemma round_trace (hS : S.Nonempty) (hr : r ∈ S) (hh : ∀ i, 0 < p.h i)
    (g : Point p → p.Ω → Point p) (s : Samples p) (x : Point p) (k n : ℕ) (a : Time)
    (i : Fin p.n) {ops out} (h : Trace (program A i n (localPoint S (nextPoint S x (mean S g s x k)) i)) ops out) :
    Trace (program A i (n+1) (localPoint S x i)) (((roundRows A g s x k a).map fun c => c.op i) ++ ops) out := by
  have he := GraceRoundSchedule.exchange_trace A hS hr hh (a + batchTime p S) x
    (mean S g s x k) i (program A i n) h
  by_cases hb : 0 < batches p S i
  · simpa only [roundRows,List.map_cons,List.cons_append,sampleRow,program,dite_eq_left hb,mean] using
      (Trace.sample (q := (localPoint S x i,⟨batches p S i,hb⟩)) (values := reply S g s x k i)
        (f := fun vals => GraceSgd.round A i (localPoint S x i) (LeonTrajectory.mean p.base vals) (program A i n)) he)
  · have hm : mean S g s x k i = 0 := by
      simp [mean,reply,LeonTrajectory.mean,Nat.eq_zero_of_not_pos hb]
    rw [hm] at he
    simpa only [roundRows,List.map_cons,List.cons_append,sampleRow,program,dite_eq_right hb] using
      (Trace.send (i := i) (bits := []) he)

end LongTails.Proofs.GraceSampleSchedule
