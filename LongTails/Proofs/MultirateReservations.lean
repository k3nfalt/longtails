import LongTails.Algorithms.MultirateProtocol
import LongTails.Proofs.MultirateDrift

namespace LongTails.Proofs.MultirateReservations

open DistributedTemplate
open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateTrajectory LongTails.Algorithms.MultirateProtocol
open LongTails.Algorithms.MultirateCalendar LongTails.Algorithms.MultirateAllocation

variable {p : Params}

noncomputable def packetDelay (p : Params) : Time :=
  p.l + p.b * (p.d * Algorithms.MultiscaleAggregate.width (aggregate p) 0 + clockBits : ℕ)

noncomputable def span (p : Params) (i : Fin p.n) : Time :=
  packetDelay p + batch p i * p.h i + packetDelay p

noncomputable def firstFrame (p : Params) : Time := Finset.univ.sup (span p)

noncomputable def frame (p : Params) (k : ℕ) : Time :=
  firstFrame p + k * Real.toNNReal (slot p)

noncomputable def finishTime (p : Params) := frame p (steps p)

lemma frame_mono (p : Params) : Monotone (frame p) := by
  intro i j h
  unfold frame
  gcongr

lemma first_ready (p : Params) (i : Fin p.n) : span p i ≤ frame p 0 := by
  simpa [frame, firstFrame] using (Finset.le_sup (f := span p) (Finset.mem_univ i))

lemma frame_ready (hh : ∀ i, 0 < p.h i) (hLi : ∀ i, 0 ≤ p.L i) (i : Fin p.n) (k : ℕ) :
    frame p k + span p i ≤ frame p (k + period p i) := by
  have hspan : (span p i : ℝ) = trip p i := by
    simp only [span, trip, service, packetDelay, packetTime, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast]
    ring
  have h := MultirateCalendar.trip_le hh hLi i
  apply NNReal.coe_le_coe.mp
  simp only [frame, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add, hspan,
    Real.toNNReal_of_nonneg (MultirateCalendar.slot_pos hh hLi).le]
  change (firstFrame p : ℝ) + k * slot p + trip p i ≤ firstFrame p + ((k : ℝ) + period p i) * slot p
  linarith only [h]

def wire (bits : List Bool) : List Bool := bits ++ List.replicate clockBits false

structure Job (p : Params) where
  number : ℕ
  query : List Bool
  posted : Time

noncomputable def jobInput (p : Params) (job : Job p) : Point p := queryPoint p (wire job.query)

noncomputable def partialSum (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (i : Fin p.n) (job : Job p) (j : ℕ) : Point p :=
  ∑ k ∈ Finset.range j, g i (jobInput p job) (s i (job.number * batch p i + k))

noncomputable def jobReply (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (i : Fin p.n) (job : Job p) :=
  wire (replyPacket p ((batch p i : ℝ)⁻¹ • partialSum g s i job (batch p i)))

lemma query_wire (x : Point p) :
    queryPoint p (wire (queryPacket p x)) = queryPoint p (queryPacket p x) := by
  simp only [queryPoint, wire, queryPacket, MultirateEncoding.read_pack]

lemma read_reply (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (i : Fin p.n)
    (e : ℕ) (x : Point p) (t : Time) :
    Algorithms.MultirateTrajectory.read p (jobReply g s i ⟨e, queryPacket p x, t⟩) =
      Algorithms.MultirateTrajectory.read p (replyPacket p (batchMean p g s i e (queryPoint p (queryPacket p x)))) := by
  simp only [jobReply, replyPacket, wire, MultirateEncoding.read_pack, partialSum, jobInput,
    show ∀ y, queryPoint p (queryPacket p y ++ List.replicate clockBits false) = queryPoint p (queryPacket p y) from query_wire,
    batchMean]

inductive Reservation (p : Params)
  | free (next : ℕ)
  | pending (job : Job p)

abbrev Book (p : Params) := Fin p.n → Reservation p

noncomputable def payload (p : Params) := p.d * Algorithms.MultiscaleAggregate.width (aggregate p) 0

lemma query_length (x : Point p) : (queryPacket p x).length = payload p :=
  MultiscaleAggregateCodec.packet_length (aggregate p) 0 _

lemma reply_length (x : Point p) : (replyPacket p x).length = payload p :=
  MultiscaleAggregateCodec.packet_length (aggregate p) 0 _

inductive Certified (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (out : Point p) (limit : Time) :
    ℕ → Program p → Book p → Time → Prop
  | done (book) (t) (ht : t ≤ limit) : Certified g s out limit 0 (.done out) book t
  | post {n i bits next book t t' e} (hfree : book i = .free e)
      (hbits : bits.length = payload p) (ht : t ≤ t')
      (hnext : Certified g s out limit n next (Function.update book i (.pending ⟨e,bits,t⟩)) t') :
      Certified g s out limit (n+1) (.post i bits next) book t
  | collect {n i next book t t' job} (hjob : book i = .pending job)
      (hready : job.posted + span p i ≤ t) (ht : t ≤ t')
      (hnext : Certified g s out limit n (next (jobReply g s i job))
        (Function.update book i (.free (job.number+1))) t') :
      Certified g s out limit (n+1) (.collect i next) book t

lemma certified_limit {g : Fin p.n → Point p → p.Ω → Point p} {s : Samples p} {x : Point p} {T t : Time}
    {n : ℕ} {prog : Program p} {book : Book p} (h : Certified g s x T n prog book t) : t ≤ T := by
  induction h with
  | done _ _ ht => exact ht
  | post _ _ h _ ih => exact h.trans ih
  | collect _ _ h _ ih => exact h.trans ih

end LongTails.Proofs.MultirateReservations
