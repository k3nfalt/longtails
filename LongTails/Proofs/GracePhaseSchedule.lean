import LongTails.Proofs.GraceRoutedValues

namespace LongTails.Proofs.GracePhaseSchedule

open DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.GraceRouting
open LongTails.Algorithms.LeonProtocol (Program)
open GraceScheduleBlocks (Block)
open GraceExchangeBlock (rows packets afterReads)
open LeonReservations (Frame usedCount)
open LeonTranscript (Trace)

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n} (A : Routes p S r)

noncomputable def stage (D q : ℕ) (phase : Phase) (v : ℕ → Fin p.n → Values) :
    Time → ℕ → ℕ → List (Frame p.base)
  | _,_,0 => []
  | a,k,n+1 =>
    rows (packets A D q phase k (v k)) a (a + A.frameTime q) ++
      stage D q phase v (a + A.frameTime q) (k+1) n

lemma empty_block (g : Point p → p.Ω → Point p) (s : Samples p) (a : Time) :
    Block g s a a [] := by
  constructor
  · constructor <;> simp
  · exact le_rfl
  · simp
  · simp
  · simp
  · intros; rfl

lemma stage_block (g : Point p → p.Ω → Point p) (s : Samples p) (D q : ℕ) (phase : Phase)
    (v : ℕ → Fin p.n → Values) (a : Time) (k n : ℕ)
    (hs : ∀ i j, p.G.Adj i j → p.b i j = p.b j i) :
    Block g s a (a + n * A.frameTime q) (stage A D q phase v a k n) := by
  induction n generalizing s a k with
  | zero => simpa [stage] using empty_block g s a
  | succ n ih =>
    have ht : a + ((n+1 : ℕ) : Time) * A.frameTime q =
        a + A.frameTime q + n * A.frameTime q := by push_cast; ring
    rw [ht,stage]
    exact GraceScheduleBlocks.append (GraceExchangeBlock.routed_block A g s a D q phase k (v k) hs)
      (ih _ _ _)

lemma stage_samples (D q : ℕ) (phase : Phase) (v : ℕ → Fin p.n → Values) (a : Time) (k n : ℕ)
    (i : Fin p.n) : usedCount (stage A D q phase v a k n) i = 0 := by
  induction n generalizing a k with
  | zero => rfl
  | succ n ih =>
    rw [stage,GraceScheduleBlocks.used_append,GraceExchangeBlock.zero_samples,ih,add_zero]

lemma stage_trace (D q : ℕ) (phase : Phase) (v : ℕ → Fin p.n → Values)
    (step : ∀ k i, afterReads A D q phase k (v k) i (List.finRange p.n) (v k i) = v (k+1) i)
    (i : Fin p.n) (next : Values → Program p.base) (a : Time) (k n : ℕ)
    {ops x} (h : Trace (next (v (k+n) i)) ops x) :
    Trace (A.frames D q phase i next (List.range' k n) (v k i))
      (((stage A D q phase v a k n).map fun c => c.op i) ++ ops) x := by
  induction n generalizing k a with
  | zero => exact h
  | succ n ih =>
    have ht := ih (a + A.frameTime q) (k+1) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)
    rw [← step k i] at ht
    have hr := GraceExchangeBlock.receive_trace A D q phase k (v k) (a + A.frameTime q) i
      (A.frames D q phase i next (List.range' (k+1) n)) _ _ ht
    have hp := GraceExchangeBlock.send_trace A D q phase k (v k) a (a + A.frameTime q) i _ (List.finRange p.n) hr
    simpa [stage,rows,List.range'_succ,Routes.frames,List.map_map,Function.comp_def,List.append_assoc] using hp

end LongTails.Proofs.GracePhaseSchedule
