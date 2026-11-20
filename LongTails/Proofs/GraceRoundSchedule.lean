import LongTails.Proofs.GracePhaseSchedule
import LongTails.Proofs.GraceSgdTrajectory

namespace LongTails.Proofs.GraceRoundSchedule

open DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms
open GraceRouting GraceSgd GraceBatch GracePacket
open DistributedBatchedSgd (spacing)
open DistributedQuantization (Grid reconstruct)
open LeonProtocol (Program)
open LeonReservations (Frame usedCount)
open LeonTranscript (Trace)
open GraceScheduleBlocks (Block)
open GracePhaseSchedule (stage)
open GraceRoutedValues (up down)

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n}
variable (A : Routes p S r)

noncomputable abbrev t (p : Params) := limbWidth (B p)
noncomputable abbrev q (p : Params) := wordWidth (t p) (B p)
noncomputable abbrev D (p : Params) (S : Finset (Fin p.n)) := p.d * limbCount (tuning p S).width (t p)

def localPoint (S : Finset (Fin p.n)) (x : Point p) (i : Fin p.n) :=
  if i ∈ S then x else p.x₀

noncomputable def code (S : Finset (Fin p.n)) (x : Point p) (m : Fin p.n → Point p) (i : Fin p.n) :=
  grid p (tuning p S) (localPoint S x i) (m i)

noncomputable def weighted (S : Finset (Fin p.n)) (x : Point p) (m : Fin p.n → Point p)
    (i : Fin p.n) (y : ℕ) := batches p S i * indices (t p) (code S x m i) y

noncomputable def combined (S : Finset (Fin p.n)) (x : Point p) (m : Fin p.n → Point p) :=
  meanFromIndices (tuning p S).width (B p) (spacing (statistical p) (tuning p S) x)
    (partialIndex S (batches p S) (code S x m))

noncomputable def digit (S : Finset (Fin p.n)) (x : Point p) (m : Fin p.n → Point p) :=
  indices (t p) (grid p (tuning p S) x (combined S x m))

noncomputable def nextPoint (S : Finset (Fin p.n)) (x : Point p) (m : Fin p.n → Point p) :=
  x - (1 / (2*p.L)) • reconstruct (spacing (statistical p) (tuning p S) x)
    (grid p (tuning p S) x (combined S x m))

noncomputable def halfTime (A : Routes p S r) : Time := A.slots (D p S) * A.frameTime (q p)

noncomputable def exchanges (a : Time) (x : Point p) (m : Fin p.n → Point p) :=
  stage A (D p S) (q p) .reduce (up A (D p S) (weighted S x m)) a 0 (A.slots (D p S)) ++
  stage A (D p S) (q p) .broadcast (down A (D p S) (digit S x m))
    (a + halfTime A) 0 (A.slots (D p S))

lemma exchange_block (g : Point p → p.Ω → Point p) (s : Samples p) (a : Time) (x : Point p)
    (m : Fin p.n → Point p) (hs : ∀ i j, p.G.Adj i j → p.b i j = p.b j i) :
    Block g s a (a + halfTime A + halfTime A) (exchanges A a x m) := by
  exact GraceScheduleBlocks.append (GracePhaseSchedule.stage_block g s _ _ _ _ _ _ _ hs (A := A))
    (GracePhaseSchedule.stage_block g _ _ _ _ _ _ _ _ hs (A := A))

lemma exchange_samples (a : Time) (x : Point p) (m : Fin p.n → Point p) (i : Fin p.n) :
    usedCount (exchanges A a x m) i = 0 := by
  rw [exchanges,GraceScheduleBlocks.used_append,GracePhaseSchedule.stage_samples,
    GracePhaseSchedule.stage_samples,add_zero]

lemma index_bound {d w : ℕ} (t : ℕ) (z : Grid d w) (y : ℕ) : indices t z y < 2^t := by
  unfold indices
  dsimp only
  split
  · exact Fin.isLt _
  · positivity

lemma weighted_bound (hS : S.Nonempty) (hh : ∀ i, 0 < p.h i) (x : Point p)
    (m : Fin p.n → Point p) (y : ℕ) : (∑ i ∈ S, weighted S x m i y) < 2 ^ q p := by
  have hle : (∑ i ∈ S, weighted S x m i y) ≤ B p * 2 ^ t p := by
    refine (Finset.sum_le_sum (s := S) (f := fun i => weighted S x m i y)
      (g := fun i => batches p S i * 2 ^ t p) (fun i _ =>
        Nat.mul_le_mul_left _ (index_bound _ _ _).le)).trans_eq ?_
    rw [← Finset.sum_mul,(GraceBatchTuning.batches_spec hS hh).2.2]
  rw [q, wordWidth, pow_add, Nat.mul_comm]
  exact hle.trans_lt (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity))

lemma assembled_congr {d w t : ℕ} (u v : Values) (h : ∀ y < d * limbCount w t, u y = v y)
    (j : Fin d) : assembled t w u j = assembled t w v j := by
  unfold assembled assemble
  apply Finset.sum_congr rfl
  intro l hl
  apply congrArg ((2 ^ t) ^ l * ·)
  apply h
  have he := Nat.mul_le_mul_right (limbCount w t) (Nat.succ_le_of_lt j.isLt)
  have hl' := Finset.mem_range.mp hl
  rw [Nat.succ_mul] at he
  omega

lemma root_assembled (x : Point p) (m : Fin p.n → Point p) :
    assembled (t p) (tuning p S).width
      (up A (D p S) (weighted S x m) (A.slots (D p S)) r) =
    partialIndex S (batches p S) (code S x m) := by
  funext j
  refine (assembled_congr _ _ (fun y hy => GraceRoutedValues.up_root A _ _ y hy) j).trans ?_
  exact GraceSgdTrajectory.assembled_total (t p) (by simp [t,limbWidth,clockBits]) _ _ _ _

lemma terminal_advance (x : Point p) (m : Fin p.n → Point p) (i : Fin p.n) (hi : i ∈ S) :
    advance p (tuning p S) (t p) x
      (down A (D p S) (digit S x m) (A.slots (D p S)) i) = nextPoint S x m := by
  have hid : (fun j : Fin p.d => Fin.ofNat (2 ^ ((tuning p S).width : ℕ))
      (assembled (t p) (tuning p S).width (down A (D p S) (digit S x m) (A.slots (D p S)) i) j)) =
      grid p (tuning p S) x (combined S x m) := by
    funext j
    apply Fin.ext
    have hh := (assembled_congr _ _ (fun y hy => GraceRoutedValues.down_terminal A (D p S) (digit S x m) i hi y hy) j).trans
      (GraceSgdTrajectory.assembled_indices (t p) (by simp [t,limbWidth,clockBits]) (grid p (tuning p S) x (combined S x m)) j)
    change _ % _ = _
    rw [hh, Nat.mod_eq_of_lt (Fin.isLt _)]
  rw [advance,hid]
  rfl

lemma exchange_trace (hS : S.Nonempty) (hr : r ∈ S) (hh : ∀ i, 0 < p.h i)
    (a : Time) (x : Point p) (m : Fin p.n → Point p) (i : Fin p.n) (next : Point p → Program p.base)
    {ops out} (h : Trace (next (localPoint S (nextPoint S x m) i)) ops out) :
    Trace (round A i (localPoint S x i) (m i) next) (((exchanges A a x m).map fun c => c.op i) ++ ops) out := by
  let N := A.slots (D p S)
  let u := up A (D p S) (weighted S x m)
  let v := down A (D p S) (digit S x m)
  let xi := localPoint S x i
  let nb := fun data => next (if i ∈ S then advance p (tuning p S) (t p) xi data else xi)
  let init := fun totals => if i = r then
    let mean := meanFromIndices (tuning p S).width (B p) (spacing (statistical p) (tuning p S) xi)
      (assembled (t p) (tuning p S).width totals)
    indices (t p) (grid p (tuning p S) xi mean)
    else fun _ => 0
  let nr := fun totals => A.frames (D p S) (q p) .broadcast i nb (List.range N) (init totals)
  have hu (k j) := GraceRoutedValues.up_step A (D p S) (q p) k (weighted S x m)
    (fun i hi y => by simp [weighted,(GraceBatchTuning.batches_spec hS hh).2.1 i hi])
    (fun y _ => weighted_bound hS hh x m y) j
  have hv (k j) := GraceRoutedValues.down_step A (D p S) (q p) k (digit S x m)
    (fun y _ => (index_bound _ _ y).trans_le (Nat.pow_le_pow_right (by decide)
      (Nat.le_add_right (t p) (Nat.size (B p)))) ) j
  have hend : Trace (nb (v (0+N) i)) ops out := by
    by_cases hi : i ∈ S
    · simpa [nb,v,N,xi,localPoint,hi,terminal_advance A x m i hi] using h
    · simpa [nb,xi,localPoint,hi] using h
  have hb := GracePhaseSchedule.stage_trace A _ _ _ _ hv i nb (a + halfTime A) 0 N hend
  have he : init (u N i) = v 0 i := by
    by_cases hi : i = r
    · subst i
      funext y
      simp [init,u,v,xi,localPoint,hr,N,root_assembled,digit,combined,down]
    · funext y
      simp [init,v,down,hi]
  have hr' : Trace (nr (u (0+N) i))
      (((stage A (D p S) (q p) .broadcast v (a + halfTime A) 0 N).map fun c => c.op i) ++ ops) out := by
    simpa only [nr,Nat.zero_add,he,List.range_eq_range'] using hb
  have hred := GracePhaseSchedule.stage_trace A _ _ _ _ hu i nr a 0 N hr'
  have hz : up A (D p S) (weighted S x m) 0 i = (fun y => (tuning p S).batch i *
      indices (t p) (grid p (tuning p S) (localPoint S x i) (m i)) y) := by
    funext y
    simp only [up,Nat.not_lt_zero,and_false,ite_false]
    rfl
  rw [hz] at hred
  simpa only [exchanges,List.map_append,List.append_assoc,GraceSgd.round,List.range_eq_range',
    xi,nr,init,nb,N,t,q,D,v] using hred

end LongTails.Proofs.GraceRoundSchedule
